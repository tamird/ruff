use std::collections::hash_map::Entry;

use itertools::Itertools;
use ruff_db::parsed::parsed_module;
use ruff_python_ast::{self as ast, name::Name};
use ruff_text_size::{Ranged, TextRange};
use rustc_hash::{FxHashMap, FxHashSet};
use ty_python_core::ProgramFile;
use ty_python_core::definition::{BindingsOwner, Definition, DefinitionKind};
use ty_python_core::scope::{ScopeId, ScopeKind};
use ty_python_core::semantic_index;

use super::arguments::CallArgumentTypes;
use super::{Binding, CallArguments};
use crate::Db;
use crate::place::{DefinedPlace, Definedness, Place, place_from_bindings_with_reachability_cache};
use crate::reachability::ReachabilityEvaluationCache;
use crate::types::class::DynamicClassAnchor;
use crate::types::infer::infer_definition_types;
use crate::types::{KnownClass, ProgramEnvironment, Type};

/// A known string key and its observed value in a dictionary argument.
pub struct DictionaryItem<'db> {
    pub name: Name,
    pub ty: Type<'db>,
    /// The key's definition in the call's file.
    pub source: TextRange,
}

/// Dictionary entries available at a call argument.
pub struct DictionaryItems<'db> {
    pub items: Box<[DictionaryItem<'db>]>,
    /// Whether these entries describe the entire string-key set.
    ///
    /// Immediate literals and fresh local dictionaries used exclusively through keyword
    /// unpacking can be complete. Other observations narrow known values while preserving
    /// the dictionary's ordinary value type for additional keys.
    pub is_complete: bool,
}

impl<'db> DictionaryItems<'db> {
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
                definedness: Definedness::AlwaysDefined,
                ..
            }) = place.place
            {
                elements.push(DictionaryItem {
                    name,
                    ty: field_ty,
                    source,
                });
            }
        }

        let is_complete =
            Self::complete_initializer_keys(db, scope, expression).is_some_and(|keys| {
                keys.len() == elements.len()
                    && elements.iter().all(|element| keys.contains(&element.name))
            });
        Some(DictionaryItems {
            items: elements.into_boxed_slice(),
            is_complete,
        })
    }

    /// Recover a fresh allocation only when no source-level use can expose or mutate it.
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
        if !symbol.is_local()
            || symbol.is_declared()
            || !symbol.is_used_only_for_keyword_unpacking()
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

    pub(crate) fn literal(
        db: &'db dyn Db,
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
        let mut entries = Vec::<DictionaryItem<'db>>::with_capacity(items.len());
        let mut indexes = FxHashMap::<Name, usize>::default();
        for ast::DictItem { key, value } in items {
            let key = key.as_ref()?;
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
                source: key.range(),
            };
            match indexes.entry(name) {
                Entry::Occupied(index) => {
                    // Repeated keys replace their values without changing insertion order.
                    entries[*index.get()] = entry;
                }
                Entry::Vacant(index) => {
                    index.insert(entries.len());
                    entries.push(entry);
                }
            }
        }
        Some(Self {
            items: entries.into_boxed_slice(),
            is_complete: true,
        })
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
