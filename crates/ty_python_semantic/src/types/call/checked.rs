use indexmap::map::Entry;
use itertools::Itertools;
use ruff_db::parsed::parsed_module;
use ruff_python_ast::{self as ast, name::Name};
use ruff_text_size::{Ranged, TextRange};
use rustc_hash::FxHashSet;
use ty_python_core::ProgramFile;
use ty_python_core::definition::{BindingsOwner, Definition, DefinitionKind};
use ty_python_core::scope::{ScopeId, ScopeKind};
use ty_python_core::semantic_index;

use super::arguments::{CallArgumentTypes, collect_keyword_items};
use super::{Binding, CallArguments};
use crate::place::{DefinedPlace, Definedness, Place, place_from_bindings_with_reachability_cache};
use crate::reachability::ReachabilityEvaluationCache;
use crate::types::class::DynamicClassAnchor;
use crate::types::infer::infer_definition_types;
use crate::types::typed_dict::{
    UnpackedTypedDict, UnpackedTypedDictKey, extract_unpacked_typed_dict_from_value_type,
};
use crate::types::{KnownClass, ProgramEnvironment, Type, UnionType};
use crate::{Db, FxIndexMap};

/// A named value or per-name residual restriction in a dictionary argument.
/// Optional entries in partial dictionaries can have unobserved values on other paths.
#[derive(Clone, Debug)]
pub struct DictionaryItem<'db> {
    pub name: Name,
    pub ty: Type<'db>,
    pub kind: DictionaryItemKind,
    /// The key's definition or unpacking expression in the call's file.
    pub source: TextRange,
}

/// A dictionary entry's presence and named-value evidence.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DictionaryItemKind {
    /// A named value is present on every path.
    Required,
    /// A named value may be present.
    Optional,
    /// A restriction on values supplied by unknown keys, not evidence of a named value.
    /// `Never` excludes this name from the residual.
    Residual,
}

impl DictionaryItemKind {
    pub(crate) fn from_required<'db>(db: &'db dyn Db, ty: Type<'db>, is_required: bool) -> Self {
        if is_required {
            Self::Required
        } else if ty.resolve_type_alias(db).is_never() {
            Self::Residual
        } else {
            Self::Optional
        }
    }

    pub(crate) const fn is_required(self) -> bool {
        matches!(self, Self::Required)
    }
}

impl DictionaryItem<'_> {
    pub const fn is_required(&self) -> bool {
        let Self {
            name: _,
            ty: _,
            kind,
            source: _,
        } = self;
        kind.is_required()
    }
}

/// Dictionary entries available at a call argument.
pub struct DictionaryItems<'db> {
    pub items: Box<[DictionaryItem<'db>]>,
    pub extra_items: DictionaryExtraItems<'db>,
}

/// Evidence about dictionary values beyond the named entries.
#[derive(Clone, Copy, Debug)]
pub enum DictionaryExtraItems<'db> {
    /// Every possible key has an entry, which records its own evidence.
    Closed,
    /// Values for additional keys. Every represented name is excluded; its entry records the
    /// applicable value restriction and whether a named value can supply it.
    Value(Type<'db>),
    /// Only individual writes were observed. The ordinary mapping type still applies to unseen
    /// keys and to optional observed keys on paths where their writes did not execute.
    /// These observations cannot establish an inventory for keyword argument matching.
    Unobserved,
}

impl<'db> DictionaryItems<'db> {
    /// Whether the named entries account for every possible key.
    pub const fn is_complete(&self) -> bool {
        matches!(self.extra_items, DictionaryExtraItems::Closed)
    }

    pub(crate) fn observed(
        db: &'db dyn Db,
        scope: ScopeId<'db>,
        expression: &ast::Expr,
        argument_type: Type<'db>,
        reachability: &ReachabilityEvaluationCache<'db>,
    ) -> Option<Self> {
        let file = scope.program_file(db);
        let env = ProgramEnvironment::from_file(file);
        let index = semantic_index(db, file);
        let use_def = index.use_def_map(scope.file_scope_id(db));
        let module = parsed_module(db, file.python_file(db)).load(db);

        let use_id = index.try_expression_use_id(expression.into())?;

        if !argument_type
            .as_nominal_instance()?
            .has_known_class(db, KnownClass::Dict)
        {
            return None;
        }

        let definition_key = |definition: Definition<'_>| {
            let key = match definition.kind(db) {
                DefinitionKind::DictKeyAssignment(assignment) => assignment.key(&module),
                DefinitionKind::Assignment(assignment) => {
                    let subscript = assignment.target(&module).as_subscript_expr()?;
                    subscript.slice.as_ref().into()
                }
                DefinitionKind::AnnotatedAssignment(assignment) => {
                    let subscript = assignment.target(&module).as_subscript_expr()?;
                    subscript.slice.as_ref().into()
                }
                _ => return None,
            };

            let name = match key {
                ast::AnyNodeRef::ExprStringLiteral(literal) => Name::new(literal.value.to_str()),
                ast::AnyNodeRef::Identifier(identifier) => identifier.id.clone(),
                _ => return None,
            };
            Some((name, key.range()))
        };

        // Collect the types of each distinct key.
        let mut elements = Vec::new();
        for bindings in use_def.multi_bindings_at_use(use_id) {
            let place = place_from_bindings_with_reachability_cache(
                db,
                &env,
                bindings.clone(),
                reachability,
            );
            let Some((name, source)) = place.first_definition.and_then(definition_key) else {
                continue;
            };

            if let Place::Defined(DefinedPlace {
                ty: field_ty,
                definedness,
                ..
            }) = place.place
            {
                elements.push(DictionaryItem {
                    name,
                    ty: field_ty,
                    kind: DictionaryItemKind::from_required(
                        db,
                        field_ty,
                        definedness == Definedness::AlwaysDefined,
                    ),
                    source,
                });
            }
        }

        let is_complete =
            Self::complete_initializer_keys(db, scope, expression).is_some_and(|mut keys| {
                for element in &elements {
                    keys.remove(&element.name);
                }
                keys.is_empty()
            });
        Some(DictionaryItems {
            items: elements.into_boxed_slice(),
            extra_items: if is_complete {
                DictionaryExtraItems::Closed
            } else {
                DictionaryExtraItems::Unobserved
            },
        })
    }

    /// Recover a fresh allocation whose key assignments are all tracked.
    ///
    /// The usage check covers the whole symbol, including other bindings and nested captures.
    /// This deliberately gives up precision after harmless reads, but also catches loop-carried
    /// aliases without an alias or heap-effect analysis.
    fn complete_initializer_keys(
        db: &'db dyn Db,
        scope: ScopeId<'db>,
        expression: &ast::Expr,
    ) -> Option<FxHashSet<Name>> {
        if scope.scope(db).kind() != ScopeKind::Function {
            return None;
        }
        let name = expression.as_name_expr()?;
        let file = scope.program_file(db);
        let index = semantic_index(db, file);
        let symbol = index
            .place_table(scope.file_scope_id(db))
            .symbol_by_name(&name.id)?;
        if !symbol.is_local() || symbol.is_declared() || !symbol.has_only_tracked_dictionary_uses()
        {
            return None;
        }
        let use_id = index.try_expression_use_id(expression.into())?;
        let binding = index
            .use_def_map(scope.file_scope_id(db))
            .bindings_at_use(use_id)
            .exactly_one()
            .ok()?;
        let definition = binding.binding.definition()?;
        let DefinitionKind::Assignment(assignment) = definition.kind(db) else {
            return None;
        };
        // In particular, `alias = values = {}` does not allocate an unaliased dictionary.
        if assignment.owner() != BindingsOwner::Definition {
            return None;
        }
        let inference = infer_definition_types(db, definition);
        if inference.discards_dict_key_assignments() {
            return None;
        }
        let module = parsed_module(db, file.python_file(db)).load(db);
        match assignment.value(&module) {
            ast::Expr::Dict(dictionary) => dictionary
                .items
                .iter()
                .map(|item| {
                    let key = item.key.as_ref()?.as_string_literal_expr()?;
                    Some(Name::new(key.value.to_str()))
                })
                .collect(),
            ast::Expr::Call(call) => {
                if !call.arguments.args.is_empty() {
                    return None;
                }
                let Type::ClassLiteral(class) = inference.expression_type(&*call.func) else {
                    return None;
                };
                if !class.is_known(db, KnownClass::Dict) {
                    return None;
                }
                call.arguments
                    .keywords
                    .iter()
                    .map(|keyword| Some(keyword.arg.as_ref()?.id.clone()))
                    .collect()
            }
            _ => None,
        }
    }

    pub(crate) fn expression(
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        expression: &ast::Expr,
        expression_type: &mut impl FnMut(&ast::Expr) -> Option<Type<'db>>,
    ) -> Option<Self> {
        match expression {
            ast::Expr::Dict(_) => Self::literal(db, env, expression, expression_type),
            ast::Expr::Call(call) => {
                let ast::ExprCall {
                    node_index: _,
                    range_start: _,
                    func,
                    arguments,
                } = call;
                let Type::ClassLiteral(class) = expression_type(func)? else {
                    return None;
                };
                if !class.is_known(db, KnownClass::Dict) {
                    return None;
                }
                let mut dictionary = DictionaryItemsBuilder::default();
                match arguments.args.as_ref() {
                    [] => {}
                    [source] => {
                        if source.is_starred_expr() {
                            return None;
                        }
                        let source = Self::unpacked_expression(db, env, source, expression_type)?;
                        dictionary.overlay(db, env, source)?;
                    }
                    _ => return None,
                }
                let keywords = collect_keyword_items(
                    db,
                    env,
                    arguments.keywords.iter().map(|keyword| {
                        let ast::Keyword {
                            node_index: _,
                            range: _,
                            arg,
                            value,
                        } = keyword;
                        if let Some(name) = arg {
                            let ty = expression_type(value)?;
                            Some(Self {
                                items: Box::new([DictionaryItem {
                                    name: name.id.clone(),
                                    ty,
                                    kind: DictionaryItemKind::Required,
                                    source: name.range(),
                                }]),
                                extra_items: DictionaryExtraItems::Closed,
                            })
                        } else {
                            Self::unpacked_expression(db, env, value, expression_type)
                        }
                    }),
                )?;
                dictionary.overlay(db, env, keywords)?;
                Some(dictionary.finish())
            }
            _ => None,
        }
    }

    fn unpacked_expression(
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        expression: &ast::Expr,
        expression_type: &mut impl FnMut(&ast::Expr) -> Option<Type<'db>>,
    ) -> Option<Self> {
        let observed = Self::expression(db, env, expression, expression_type);
        if expression.is_dict_expr() {
            // An unsupported nested literal invalidates the whole inventory. Its ordinary
            // inferred value type must not masquerade as a proven residual here.
            return observed;
        }
        observed.or_else(|| {
            // Other expressions, including unsupported constructor forms, retain their ordinary
            // mapping type. No partial constructor inventory escapes through this fallback.
            let ty = expression_type(expression)?;
            Self::unpacked(db, env, ty, expression.range())
        })
    }

    fn literal(
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        expression: &ast::Expr,
        expression_type: &mut impl FnMut(&ast::Expr) -> Option<Type<'db>>,
    ) -> Option<Self> {
        let ast::Expr::Dict(ast::ExprDict {
            node_index: _,
            range: _,
            items,
        }) = expression
        else {
            return None;
        };
        let mut dictionary = DictionaryItemsBuilder::default();
        for ast::DictItem { key, value } in items {
            let Some(key) = key else {
                let unpacked = Self::unpacked_expression(db, env, value, expression_type)?;
                dictionary.overlay(db, env, unpacked)?;
                continue;
            };
            let name = match key {
                ast::Expr::StringLiteral(literal) => Name::new(literal.value.to_str()),
                _ => {
                    let ty = expression_type(key)?;
                    let name = ty.string_literal_value(db)?;
                    Name::new(name)
                }
            };
            let ty = expression_type(value)?;
            let entry = DictionaryItem {
                name: name.clone(),
                ty,
                kind: DictionaryItemKind::Required,
                source: key.range(),
            };
            // Repeated keys replace their values without changing insertion order.
            dictionary.items.insert(name, entry);
        }
        Some(dictionary.finish())
    }

    /// Read an unpacked source's existing type without inferring its expression again.
    fn unpacked(
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        ty: Type<'db>,
        source: TextRange,
    ) -> Option<Self> {
        // An unreachable source is not evidence for an inhabited, empty mapping.
        if ty.resolve_type_alias(db).is_never() {
            return None;
        }
        if let Some(unpacked) = extract_unpacked_typed_dict_from_value_type(db, env, ty) {
            let UnpackedTypedDict {
                keys,
                openness,
                has_implicit_extra_items,
            } = unpacked;
            // Hidden TypedDict fields follow a different call policy from ordinary mapping
            // values. Preserve the existing literal inference until that provenance is retained.
            if has_implicit_extra_items {
                return None;
            }
            return Some(Self {
                items: keys
                    .into_iter()
                    .map(|(name, key)| {
                        let UnpackedTypedDictKey {
                            value_ty,
                            kind,
                            definition: _,
                        } = key;
                        DictionaryItem {
                            name,
                            ty: value_ty,
                            kind,
                            source,
                        }
                    })
                    .collect(),
                extra_items: openness
                    .effective_extra_items()
                    .map_or(DictionaryExtraItems::Closed, |extra| {
                        DictionaryExtraItems::Value(extra.declared_ty)
                    }),
            });
        }
        let (_, value_ty) = ty.unpack_keys_and_items(db, env)?;
        Some(Self {
            items: Box::default(),
            extra_items: if value_ty.resolve_type_alias(db).is_never() {
                DictionaryExtraItems::Closed
            } else {
                DictionaryExtraItems::Value(value_ty)
            },
        })
    }
}

/// An ordered overlay of mapping sources. The residual excludes every represented name.
#[derive(Default)]
struct DictionaryItemsBuilder<'db> {
    items: FxIndexMap<Name, DictionaryItem<'db>>,
    extra_items: Option<Type<'db>>,
}

impl<'db> DictionaryItemsBuilder<'db> {
    fn overlay(
        &mut self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        dictionary: DictionaryItems<'db>,
    ) -> Option<()> {
        let DictionaryItems { items, extra_items } = dictionary;
        let incoming_extra = match extra_items {
            DictionaryExtraItems::Closed => None,
            DictionaryExtraItems::Value(ty) => Some(ty),
            DictionaryExtraItems::Unobserved => return None,
        };
        if let Some(ty) = incoming_extra {
            let names: FxHashSet<_> = items.iter().map(|item| item.name.clone()).collect();
            for item in self.items.values_mut() {
                if !names.contains(&item.name) {
                    item.ty = UnionType::from_two_elements(db, env, item.ty, ty);
                }
            }
        }
        for mut item in items {
            match self.items.entry(item.name.clone()) {
                Entry::Occupied(mut entry) => {
                    if !item.is_required() {
                        let previous = entry.get();
                        item.ty = UnionType::from_two_elements(db, env, previous.ty, item.ty);
                        if item.kind == DictionaryItemKind::Residual {
                            item.source = previous.source;
                        }
                        item.kind = match previous.kind {
                            DictionaryItemKind::Required => DictionaryItemKind::Required,
                            DictionaryItemKind::Optional => DictionaryItemKind::Optional,
                            DictionaryItemKind::Residual => item.kind,
                        };
                    }
                    entry.insert(item);
                }
                Entry::Vacant(entry) => {
                    if !item.is_required()
                        && let Some(ty) = self.extra_items
                    {
                        item.ty = UnionType::from_two_elements(db, env, ty, item.ty);
                    }
                    entry.insert(item);
                }
            }
        }
        if let Some(ty) = incoming_extra {
            self.extra_items = Some(self.extra_items.map_or(ty, |previous| {
                UnionType::from_two_elements(db, env, previous, ty)
            }));
        }
        Some(())
    }

    fn finish(self) -> DictionaryItems<'db> {
        let Self { items, extra_items } = self;
        DictionaryItems {
            items: items.into_values().collect(),
            extra_items: extra_items
                .map_or(DictionaryExtraItems::Closed, DictionaryExtraItems::Value),
        }
    }
}

/// Whether a checked parameter was supplied by one definite argument.
pub enum CheckedArgument<'a, 'db> {
    /// No argument supplied this parameter.
    Omitted,
    /// A single value supplied this parameter. A synthetic receiver has no source expression.
    Value {
        ty: Type<'db>,
        expression: Option<&'a ast::Expr>,
    },
    /// Argument recovery or unpacking did not determine a single value.
    Indeterminate,
}

/// A call after ordinary argument matching and type checking.
///
/// Native refinements can update the return type through this view. Applications receive
/// read-only access. Child types come from the current inference result, so inspecting them
/// cannot recursively request the enclosing scope. Source nodes belong to the original call.
pub struct CheckedCall<'a, 'db> {
    pub(crate) binding: &'a mut Binding<'db>,
    pub(crate) arguments: &'a CallArguments<'a, 'db>,
    pub(crate) bound_receiver: bool,
    pub(crate) file: ProgramFile<'db>,
    pub(crate) call: &'a ast::ExprCall,
    pub(crate) expression_type: &'a dyn Fn(&ast::Expr) -> Option<Type<'db>>,
    pub(crate) dictionary_items: &'a dyn Fn(&ast::Expr, Type<'db>) -> Option<DictionaryItems<'db>>,
    pub(crate) class_anchor: &'a dyn Fn(Box<[Type<'db>]>) -> DynamicClassAnchor<'db>,
    pub(crate) has_binding_errors: bool,
}

impl<'a, 'db> CheckedCall<'a, 'db> {
    pub fn file(&self) -> ProgramFile<'db> {
        self.file
    }

    pub fn call(&self) -> &'a ast::ExprCall {
        self.call
    }

    pub fn declaration(&self) -> Option<Definition<'db>> {
        self.binding.signature.definition()
    }

    pub fn return_type(&self) -> Type<'db> {
        self.binding.return_ty
    }

    pub fn has_binding_errors(&self) -> bool {
        self.has_binding_errors
    }

    pub fn expression_type(&self, expression: &ast::Expr) -> Option<Type<'db>> {
        (self.expression_type)(expression)
    }

    pub fn argument(&self, name: &str) -> CheckedArgument<'a, 'db> {
        let Some(parameter) = self
            .binding
            .signature
            .parameters()
            .iter()
            .position(|parameter| parameter.name().map(Name::as_str) == Some(name))
        else {
            return CheckedArgument::Indeterminate;
        };
        self.argument_at(parameter)
    }

    /// Known entries of a definitely supplied dictionary argument.
    pub fn dictionary_argument(&self, name: &str) -> Option<DictionaryItems<'db>> {
        let CheckedArgument::Value { ty, expression } = self.argument(name) else {
            return None;
        };
        let expression = expression?;
        (self.dictionary_items)(expression, ty)
    }

    fn argument_at(&self, parameter: usize) -> CheckedArgument<'a, 'db> {
        let mut arguments = self.matched_arguments(parameter);
        let Some(source) = arguments.next() else {
            return CheckedArgument::Omitted;
        };
        if arguments.next().is_some() {
            return CheckedArgument::Indeterminate;
        }
        let Some(ty) = self.parameter_types()[parameter] else {
            return CheckedArgument::Indeterminate;
        };
        let expression = match source {
            Some((source, _)) => {
                let expression = match source {
                    ast::ArgOrKeyword::Arg(expression) => {
                        if expression.is_starred_expr() {
                            return CheckedArgument::Indeterminate;
                        }
                        expression
                    }
                    ast::ArgOrKeyword::Keyword(keyword) => {
                        if keyword.arg.is_none() {
                            return CheckedArgument::Indeterminate;
                        }
                        &keyword.value
                    }
                };
                Some(expression)
            }
            None => None,
        };
        CheckedArgument::Value { ty, expression }
    }

    /// Associates the matcher's receiver-prefixed arguments with original source arguments.
    /// Literal unpacking still occupies one source entry, even if it supplies several parameters.
    fn matched_arguments(
        &self,
        parameter: usize,
    ) -> impl Iterator<Item = Option<(ast::ArgOrKeyword<'a>, &CallArgumentTypes<'db>)>> {
        let matches = move |argument: &super::MatchedArgument<'db>| {
            argument
                .parameters
                .iter()
                .any(|matched| matched.index == parameter)
        };
        let receiver = self
            .binding
            .argument_matches()
            .first()
            .filter(|argument| self.bound_receiver && matches(argument))
            .map(|_| None);
        let sources = self
            .call
            .arguments
            .iter_source_order()
            .zip(self.arguments.iter_types())
            .enumerate()
            .filter_map(move |(index, (source, types))| {
                let argument = self
                    .binding
                    .matched_argument_for_call_argument(self.bound_receiver, index)?;
                matches(argument).then_some(Some((source, types)))
            });
        receiver.into_iter().chain(sources)
    }

    pub(crate) fn parameter_types(&self) -> &[Option<Type<'db>>] {
        self.binding.parameter_types()
    }

    pub(crate) fn arguments_for_parameter(
        &self,
        parameter: usize,
    ) -> impl Iterator<Item = Type<'db>> {
        self.matched_arguments(parameter)
            .filter_map(move |argument| match argument {
                Some((_, types)) => {
                    let declared = self.binding.signature.parameters()[parameter].annotated_type();
                    Some(types.get_for_declared_type(declared))
                }
                None => self.parameter_types()[parameter],
            })
    }

    /// Returns the complete source argument for diagnostics, including a keyword's name.
    pub(crate) fn argument_node(&self, parameter: usize) -> Option<ast::AnyNodeRef<'a>> {
        let mut arguments = self.matched_arguments(parameter);
        let (source, _) = arguments.next()??;
        if arguments.next().is_some() {
            return None;
        }
        Some(match source {
            ast::ArgOrKeyword::Arg(expression) => expression.into(),
            ast::ArgOrKeyword::Keyword(keyword) => keyword.into(),
        })
    }

    pub(crate) fn argument_expression(&self, parameter: usize) -> Option<&'a ast::Expr> {
        match self.argument_at(parameter) {
            CheckedArgument::Value { ty: _, expression } => expression,
            CheckedArgument::Omitted => None,
            CheckedArgument::Indeterminate => None,
        }
    }

    pub(crate) fn set_return_type(&mut self, ty: Type<'db>) {
        self.binding.set_return_type(ty);
    }

    pub(crate) fn class_anchor(&self, bases: Box<[Type<'db>]>) -> DynamicClassAnchor<'db> {
        (self.class_anchor)(bases)
    }
}

#[cfg(test)]
mod tests {
    use ruff_db::files::system_path_to_file;
    use ruff_text_size::{TextLen, TextRange, TextSize};

    use crate::Db as _;
    use crate::db::tests::TestDbBuilder;

    #[test]
    fn native_diagnostics_keep_the_complete_keyword() -> anyhow::Result<()> {
        let source = "from ty_extensions import static_assert\nstatic_assert(condition=False)\n";
        let db = TestDbBuilder::new()
            .with_file("/src/main.py", source)
            .build()?;
        let file = system_path_to_file(&db, "/src/main.py")?;
        let diagnostics = db.check_file(file);
        let [diagnostic] = diagnostics.as_slice() else {
            panic!("expected one static assertion diagnostic: {diagnostics:#?}");
        };
        assert_eq!(diagnostic.id().as_str(), "static-assert-error");
        let start = TextSize::try_from(source.find("condition=False").unwrap())?;
        let expected = TextRange::at(start, "condition=False".text_len());
        assert!(
            diagnostic
                .secondary_annotations()
                .any(|annotation| annotation.get_span().range() == Some(expected)),
            "{diagnostic:#?}"
        );
        Ok(())
    }
}
