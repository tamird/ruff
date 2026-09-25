//! Mapping contents at a use, inferred from the ordinary reaching-definition graph.

use ruff_db::parsed::parsed_module;
use ruff_python_ast as ast;
use ruff_python_ast::name::Name;
use ruff_python_ast::visitor::{Visitor, walk_expr};
use ruff_text_size::{Ranged, TextRange};
use rustc_hash::FxHashSet;
use ty_python_core::definition::{
    Definition, DefinitionKind, DefinitionState, DictionaryContentsDefinitionKind,
    DictionaryContentsEffect, DictionaryContentsInferenceOwner, NestedBindingExecution,
};
use ty_python_core::place::ScopedPlaceId;
use ty_python_core::place::{PlaceExpr, PlaceTable};
use ty_python_core::scope::ScopeId;
use ty_python_core::{
    BindingWithConstraintsIterator, NarrowingEvaluator, ProgramFile, Statement, semantic_index,
};

use crate::place::loop_header_reachability;
use crate::reachability::{ReachabilityEvaluationCache, evaluate_reachability_with_cache};
use crate::types::infer::{StatementInference, infer_definition_types, infer_statement_types};
use crate::types::narrow::NarrowingEvaluatorExtension;
use crate::types::{KnownClass, ProgramEnvironment, Type, UnionType};
use crate::{Db, FxIndexMap};

use super::{
    DictionaryExtraItems, DictionaryFallback, DictionaryItem, DictionaryItemKind, DictionaryItems,
    DictionaryItemsBuilder, DictionaryObservation,
};

/// A cycle seed, unreachable control flow, missing history, and an inhabited mapping are
/// distinct. In particular, neither missing history nor a pending cycle proves an empty map.
#[derive(Clone, Debug, PartialEq, Eq, get_size2::GetSize, salsa::SalsaValue)]
enum ContentsValue<'db> {
    Pending,
    Unreachable,
    Unavailable,
    Mapping(MappingContents<'db>),
}

#[derive(Clone, Debug, PartialEq, Eq, get_size2::GetSize, salsa::SalsaValue)]
struct MappingContents<'db> {
    /// All ranges belong to this file. Copying from another file rebases them to the local use.
    file: ProgramFile<'db>,
    dictionary: DictionaryItems<'db>,
    /// Other code can retain this object. Later writes refine values but cannot prove presence.
    exposed: bool,
    /// The ordinary mapping value bound for declared or external/member bindings survives exposure.
    value_bound: Option<Type<'db>>,
}

impl<'db> MappingContents<'db> {
    fn value_at(&self, name: &Name) -> Type<'db> {
        self.dictionary
            .items
            .iter()
            .find(|item| &item.name == name)
            .map_or_else(|| self.extra_value(), |item| item.ty)
    }

    fn extra_value(&self) -> Type<'db> {
        match self.dictionary.extra_items {
            DictionaryExtraItems::Closed => Type::Never,
            DictionaryExtraItems::Value(ty) => ty,
        }
    }

    fn expose(&mut self, db: &'db dyn Db) {
        self.exposed = true;
        self.dictionary.items = std::mem::take(&mut self.dictionary.items)
            .into_vec()
            .into_iter()
            .filter(|item| !item.ty.resolve_type_alias(db).is_never())
            .collect();
        for item in &mut self.dictionary.items {
            item.kind = DictionaryItemKind::Residual;
        }
        self.dictionary.extra_items =
            DictionaryExtraItems::Value(self.value_bound.unwrap_or_else(Type::unknown));
    }

    fn set_item(
        &mut self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        key: Type<'db>,
        value: Type<'db>,
        source: TextRange,
    ) {
        if let Some(name) = key.string_literal_value(db) {
            let name = Name::new(name);
            let item = DictionaryItem {
                name: name.clone(),
                ty: value,
                kind: if self.exposed {
                    DictionaryItemKind::Residual
                } else {
                    DictionaryItemKind::Required
                },
                source,
            };
            if let Some(previous) = self
                .dictionary
                .items
                .iter_mut()
                .find(|item| item.name == name)
            {
                *previous = item;
            } else {
                let mut items = std::mem::take(&mut self.dictionary.items).into_vec();
                items.push(item);
                self.dictionary.items = items.into_boxed_slice();
            }
        } else {
            // A computed key can overwrite any named value as well as introduce another name.
            for item in &mut self.dictionary.items {
                item.ty = UnionType::from_two_elements(db, env, item.ty, value);
            }
            self.dictionary.extra_items = DictionaryExtraItems::Value(
                UnionType::from_two_elements(db, env, self.extra_value(), value),
            );
        }
    }

    fn delete_item(&mut self, db: &'db dyn Db, key: Type<'db>, source: TextRange) {
        if let Some(name) = key.string_literal_value(db) {
            let name = Name::new(name);
            let mut items = std::mem::take(&mut self.dictionary.items).into_vec();
            items.retain(|item| item.name != name);
            if !self.exposed {
                items.push(DictionaryItem {
                    name,
                    ty: Type::Never,
                    kind: DictionaryItemKind::Residual,
                    source,
                });
            }
            self.dictionary.items = items.into_boxed_slice();
        } else {
            for item in &mut self.dictionary.items {
                if item.kind == DictionaryItemKind::Required {
                    item.kind = DictionaryItemKind::Optional;
                }
            }
        }
    }

    fn localize(&mut self, file: ProgramFile<'db>, source: TextRange) {
        if self.file != file {
            for item in &mut self.dictionary.items {
                item.source = source;
            }
            self.file = file;
        }
    }

    fn join(&self, db: &'db dyn Db, env: &ProgramEnvironment<'db>, other: &Self) -> Self {
        let Self {
            file,
            dictionary,
            exposed,
            value_bound,
        } = self;
        let Self {
            file: _,
            dictionary: other_dictionary,
            exposed: other_exposed,
            value_bound: other_bound,
        } = other;
        let exposed = *exposed || *other_exposed;
        let value_bound = value_bound
            .zip(*other_bound)
            .map(|(left, right)| UnionType::from_two_elements(db, env, left, right));
        let extra_value =
            UnionType::from_two_elements(db, env, self.extra_value(), other.extra_value());
        let mut items: FxIndexMap<_, _> = dictionary
            .items
            .iter()
            .map(|item| (item.name.clone(), item.clone()))
            .collect();
        for item in &other_dictionary.items {
            items
                .entry(item.name.clone())
                .or_insert_with(|| item.clone());
        }
        for (name, item) in &mut items {
            let left = dictionary.items.iter().find(|item| &item.name == name);
            let right = other_dictionary
                .items
                .iter()
                .find(|item| &item.name == name);
            item.ty =
                UnionType::from_two_elements(db, env, self.value_at(name), other.value_at(name));
            item.kind = if exposed {
                DictionaryItemKind::Residual
            } else if left.is_some_and(DictionaryItem::is_required)
                && right.is_some_and(DictionaryItem::is_required)
            {
                DictionaryItemKind::Required
            } else if left
                .into_iter()
                .chain(right)
                .any(|item| item.kind != DictionaryItemKind::Residual)
            {
                DictionaryItemKind::Optional
            } else {
                DictionaryItemKind::Residual
            };
        }
        Self {
            file: *file,
            dictionary: DictionaryItems {
                items: items.into_values().collect(),
                extra_items: if extra_value.is_never() {
                    DictionaryExtraItems::Closed
                } else {
                    DictionaryExtraItems::Value(extra_value)
                },
            },
            exposed,
            value_bound,
        }
    }
}

impl<'db> ContentsValue<'db> {
    fn join(self, db: &'db dyn Db, env: &ProgramEnvironment<'db>, other: Self) -> Self {
        match self {
            Self::Pending => {
                if matches!(other, Self::Unreachable) {
                    self
                } else {
                    other
                }
            }
            Self::Unreachable => other,
            Self::Unavailable => self,
            Self::Mapping(mapping) => match other {
                Self::Pending => Self::Mapping(mapping),
                Self::Unreachable => Self::Mapping(mapping),
                Self::Unavailable => Self::Unavailable,
                Self::Mapping(other) => Self::Mapping(mapping.join(db, env, &other)),
            },
        }
    }

    fn cycle_normalized(
        self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        previous: &Self,
        cycle: &salsa::Cycle,
    ) -> Self {
        if cycle.iteration() <= crate::TAINTED_CYCLES {
            return self;
        }
        let mut result = previous.clone().join(db, env, self);
        if let Self::Mapping(mapping) = &mut result {
            for item in &mut mapping.dictionary.items {
                let previous_ty = match previous {
                    Self::Mapping(previous) => previous.value_at(&item.name),
                    _ => Type::Never,
                };
                item.ty = item.ty.cycle_normalized(db, env, previous_ty, cycle);
            }
            if let DictionaryExtraItems::Value(ty) = &mut mapping.dictionary.extra_items {
                let previous_ty = match previous {
                    Self::Mapping(previous) => previous.extra_value(),
                    _ => Type::Never,
                };
                *ty = ty.cycle_normalized(db, env, previous_ty, cycle);
            }
        }
        result
    }
}

#[derive(Clone, Debug, PartialEq, Eq, get_size2::GetSize, salsa::SalsaValue)]
struct Contents<'db> {
    value: ContentsValue<'db>,
    captured: bool,
}

impl<'db> Contents<'db> {
    fn new(value: ContentsValue<'db>) -> Self {
        Self {
            value,
            captured: false,
        }
    }

    fn join(self, db: &'db dyn Db, env: &ProgramEnvironment<'db>, other: Self) -> Self {
        let Self { value, captured } = self;
        let Self {
            value: other_value,
            captured: other_captured,
        } = other;
        let captured = captured || other_captured;
        let mut value = value.join(db, env, other_value);
        if captured && let ContentsValue::Mapping(mapping) = &mut value {
            mapping.expose(db);
        }
        Self { value, captured }
    }

    fn narrow(
        mut self,
        db: &'db dyn Db,
        scope: ScopeId<'db>,
        place: ScopedPlaceId,
        constraint: &NarrowingEvaluator<'_, 'db>,
    ) -> Self {
        let ContentsValue::Mapping(mapping) = &mut self.value else {
            return self;
        };
        let env = ProgramEnvironment::from_scope(scope);
        let index = semantic_index(db, scope.program_file(db));
        let table = index.place_table(scope.file_scope_id(db));
        for item in &mut mapping.dictionary.items {
            let Some(key) = table.contents_key(place, &item.name) else {
                continue;
            };
            item.ty = constraint.narrow(db, &env, item.ty, key);
            if item.is_required() && item.ty.resolve_type_alias(db).is_never() {
                self.value = ContentsValue::Unreachable;
                return self;
            }
        }
        self
    }
}

#[salsa::tracked(
    returns(clone),
    cycle_initial=|_, _, _| Contents::new(ContentsValue::Pending),
    cycle_fn=|db, cycle, previous: &Contents<'db>, result: Contents<'db>, definition: Definition<'db>| {
        let env = ProgramEnvironment::from_definition(definition);
        let Contents { value, captured } = result;
        let Contents { value: previous_value, captured: previous_captured } = previous;
        let value = value.cycle_normalized(db, &env, previous_value, cycle);
        let captured = if cycle.iteration() <= crate::TAINTED_CYCLES {
            captured
        } else { *previous_captured || captured };
        Contents { value, captured }
    },
    heap_size=get_size2::GetSize::get_heap_size,
)]
fn definition_contents<'db>(db: &'db dyn Db, definition: Definition<'db>) -> Contents<'db> {
    let scope = definition.scope(db);
    let env = ProgramEnvironment::from_scope(scope);
    let index = semantic_index(db, scope.program_file(db));
    let use_def = index.use_def_map(scope.file_scope_id(db));
    let reachability = ReachabilityEvaluationCache::new(scope, use_def.reachability_constraints());

    match definition.kind(db) {
        DefinitionKind::LoopHeader(_) => {
            if use_def.reachability_constraints().used_interiors().len()
                > crate::place::MAX_EXACT_LOOP_HEADER_INFERENCE_NODES
            {
                return Contents {
                    value: ContentsValue::Unavailable,
                    captured: true,
                };
            }
            let loop_header = loop_header_reachability(db, definition);
            let mut result = Contents::new(if loop_header.deleted_reachability.is_always_false() {
                ContentsValue::Unreachable
            } else {
                ContentsValue::Unavailable
            });
            for binding in &loop_header.reachable_bindings {
                let incoming = definition_contents(db, binding.definition).narrow(
                    db,
                    scope,
                    definition.place(db),
                    &use_def.narrowing_evaluator(binding.narrowing_constraint),
                );
                result = result.join(db, &env, incoming);
            }
            result
        }
        DefinitionKind::DictionaryContents(contents) => match contents.as_ref() {
            DictionaryContentsDefinitionKind::Initialize {
                definition,
                range: _,
            } => Contents::new(initial_contents(db, *definition)),
            DictionaryContentsDefinitionKind::LoopCapture { header, range: _ } => {
                let Contents { value, captured } = definition_contents(db, *header);
                match value {
                    ContentsValue::Pending => Contents::new(ContentsValue::Pending),
                    ContentsValue::Unavailable => Contents {
                        value: ContentsValue::Unreachable,
                        captured,
                    },
                    ContentsValue::Unreachable => Contents {
                        value: ContentsValue::Unreachable,
                        captured,
                    },
                    ContentsValue::Mapping(_) => Contents {
                        value: ContentsValue::Unreachable,
                        captured,
                    },
                }
            }
            DictionaryContentsDefinitionKind::Operation { receiver, effect } => {
                Contents::new(operation_contents(db, definition, receiver, effect))
            }
            DictionaryContentsDefinitionKind::Capture {
                nested_scope,
                name,
                range: _,
                execution,
                resolution,
            } => {
                let previous = || {
                    from_bindings(
                        db,
                        scope,
                        use_def.bindings_at_definition(definition),
                        &reachability,
                    )
                };
                if index.captured_binding_scope(*nested_scope, name, *resolution)
                    != Some(scope.file_scope_id(db))
                {
                    return match execution {
                        NestedBindingExecution::Lazy => Contents::new(ContentsValue::Unreachable),
                        NestedBindingExecution::Eager => previous(),
                    };
                }
                match execution {
                    NestedBindingExecution::Lazy => Contents {
                        value: ContentsValue::Unreachable,
                        captured: true,
                    },
                    NestedBindingExecution::Eager => {
                        let mut result = previous();
                        if let ContentsValue::Mapping(mapping) = &mut result.value {
                            mapping.expose(db);
                        }
                        result
                    }
                }
            }
        },
        _ => Contents::new(ContentsValue::Unavailable),
    }
}

/// Seed the contents graph from the same binding that owns ordinary value inference.
/// Parameter and member bindings carry value refinements without asserting a closed key set.
fn initial_contents<'db>(db: &'db dyn Db, definition: Definition<'db>) -> ContentsValue<'db> {
    if crate::types::infer::is_discarded_dict_key_assignment(db, definition) {
        return ContentsValue::Unavailable;
    }
    let scope = definition.scope(db);
    let env = ProgramEnvironment::from_scope(scope);
    let file = scope.program_file(db);
    let module = parsed_module(db, file.python_file(db)).load(db);
    let inference = infer_definition_types(db, definition);
    if StatementInference::Definition(definition, inference).is_provisional() {
        return ContentsValue::Pending;
    }
    let bound_type = inference.binding_type(definition);
    if !bound_type
        .as_nominal_instance()
        .is_some_and(|instance| instance.has_known_class(db, KnownClass::Dict))
    {
        return ContentsValue::Unavailable;
    }
    let index = semantic_index(db, file);
    let place = index
        .place_table(scope.file_scope_id(db))
        .place(definition.place(db));
    let (owner, value, shared) = match definition.kind(db) {
        DefinitionKind::DictKeyAssignment(assignment) => (
            assignment.assignment(),
            Some(assignment.value(&module)),
            true,
        ),
        DefinitionKind::NamedExpression(named) => {
            (definition, Some(named.node(&module).value.as_ref()), false)
        }
        DefinitionKind::Assignment(assignment) => (
            definition,
            Some(assignment.value(&module)),
            assignment.owner() != ty_python_core::definition::BindingsOwner::Definition,
        ),
        kind => (definition, kind.value(&module), false),
    };
    let owner_inference = infer_definition_types(db, owner);
    if StatementInference::Definition(owner, owner_inference).is_provisional() {
        return ContentsValue::Pending;
    }
    let bounded = !place.is_symbol() || place.is_declared() || value.is_none();
    let value_bound = if bounded {
        bound_type
            .unpack_keys_and_items(db, &env)
            .map(|(_, value)| value)
    } else {
        None
    };
    let Some(dictionary) = DictionaryItems::unpacked(
        db,
        &env,
        bound_type,
        definition.kind(db).target_range(&module),
    ) else {
        return ContentsValue::Unavailable;
    };
    let mut mapping = MappingContents {
        file,
        dictionary,
        exposed: bounded,
        value_bound,
    };
    if !owner_inference.discards_dict_key_assignments()
        && let Some(value) = value
    {
        match DictionaryItems::unpacked_expression(db, &env, scope, value, &mut |expression| {
            owner_inference.try_expression_type(expression)
        }) {
            Ok(dictionary) => mapping.dictionary = dictionary,
            Err(DictionaryFallback::Unreachable) => return ContentsValue::Unreachable,
            Err(DictionaryFallback::Unavailable) => {}
        }
    }
    if bounded || shared || value.is_some_and(|value| PlaceExpr::try_from_expr(value).is_some()) {
        mapping.expose(db);
    }
    ContentsValue::Mapping(mapping)
}

/// The semantic transfer is shared by contents inference and saved-key predicate validity.
/// The index records syntax only; exact builtin identity is resolved with the operand's owner.
enum MappingTransfer<'db> {
    Result(ContentsValue<'db>),
    Keep,
    Expose,
    Set {
        key: Type<'db>,
        value: Type<'db>,
        source: TextRange,
    },
    Delete {
        key: Type<'db>,
        source: TextRange,
    },
    Clear,
    Update {
        dictionary: DictionaryItems<'db>,
        retained: bool,
    },
}

impl<'db> MappingTransfer<'db> {
    fn preserves_key(&self, db: &'db dyn Db, name: &str) -> bool {
        match self {
            Self::Keep => true,
            Self::Expose => true,
            Self::Set {
                key,
                value: _,
                source: _,
            } => key.string_literal_value(db).is_some_and(|key| key != name),
            Self::Delete { key, source: _ } => {
                key.string_literal_value(db).is_some_and(|key| key != name)
            }
            Self::Update {
                dictionary,
                retained: _,
            } => {
                if let Some(item) = dictionary.items.iter().find(|item| item.name == name) {
                    item.ty.resolve_type_alias(db).is_never()
                } else {
                    matches!(dictionary.extra_items, DictionaryExtraItems::Closed)
                }
            }
            Self::Clear => false,
            Self::Result(_) => false,
        }
    }

    fn apply(
        self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        previous: impl FnOnce() -> ContentsValue<'db>,
    ) -> ContentsValue<'db> {
        let mut previous = match self {
            Self::Result(result) => return result,
            _ => previous(),
        };
        let ContentsValue::Mapping(mapping) = &mut previous else {
            return previous;
        };
        match self {
            Self::Result(result) => result,
            Self::Keep => previous,
            Self::Expose => {
                mapping.expose(db);
                previous
            }
            Self::Set { key, value, source } => {
                mapping.set_item(db, env, key, value, source);
                previous
            }
            Self::Delete { key, source } => {
                mapping.delete_item(db, key, source);
                previous
            }
            Self::Clear => {
                mapping.dictionary = DictionaryItems {
                    items: Box::default(),
                    extra_items: if mapping.exposed {
                        DictionaryExtraItems::Value(
                            mapping.value_bound.unwrap_or_else(Type::unknown),
                        )
                    } else {
                        DictionaryExtraItems::Closed
                    },
                };
                previous
            }
            Self::Update {
                dictionary,
                retained,
            } => {
                let mut result = DictionaryItemsBuilder::default();
                result.overlay(db, env, mapping.dictionary.clone());
                result.overlay(db, env, dictionary);
                mapping.dictionary = result.finish();
                if mapping.exposed || retained {
                    mapping.expose(db);
                }
                previous
            }
        }
    }
}

fn operation_contents<'db>(
    db: &'db dyn Db,
    definition: Definition<'db>,
    receiver: &ty_python_core::ast_node_ref::AstNodeRef<ast::Expr>,
    effect: &DictionaryContentsEffect<'db>,
) -> ContentsValue<'db> {
    let scope = definition.scope(db);
    let env = ProgramEnvironment::from_scope(scope);
    mapping_transfer(db, definition, receiver, effect).apply(db, &env, || {
        let index = semantic_index(db, scope.program_file(db));
        let use_def = index.use_def_map(scope.file_scope_id(db));
        let cache = ReachabilityEvaluationCache::new(scope, use_def.reachability_constraints());
        from_bindings(
            db,
            scope,
            use_def.bindings_at_definition(definition),
            &cache,
        )
        .value
    })
}

fn mapping_transfer<'db>(
    db: &'db dyn Db,
    definition: Definition<'db>,
    receiver: &ty_python_core::ast_node_ref::AstNodeRef<ast::Expr>,
    effect: &DictionaryContentsEffect<'db>,
) -> MappingTransfer<'db> {
    let scope = definition.scope(db);
    let env = ProgramEnvironment::from_scope(scope);
    let file = scope.program_file(db);
    let module = parsed_module(db, file.python_file(db)).load(db);
    let unavailable = || MappingTransfer::Result(ContentsValue::Unavailable);
    let pending = || MappingTransfer::Result(ContentsValue::Pending);
    match effect {
        DictionaryContentsEffect::Expose => MappingTransfer::Expose,
        DictionaryContentsEffect::UnknownMutation => unavailable(),
        DictionaryContentsEffect::AugmentItem(assignment) => {
            let DefinitionKind::AugmentedAssignment(node) = assignment.kind(db) else {
                return unavailable();
            };
            let Some(subscript) = node.node(&module).target.as_subscript_expr() else {
                return unavailable();
            };
            let inference = infer_definition_types(db, *assignment);
            if StatementInference::Definition(*assignment, inference).is_provisional() {
                return pending();
            }
            let Some(key) = inference.try_expression_type(&subscript.slice) else {
                return unavailable();
            };
            let value = inference.binding_type(*assignment);
            MappingTransfer::Set {
                key,
                value,
                source: subscript.slice.range(),
            }
        }
        DictionaryContentsEffect::SetItem { subscript, owner } => {
            let Some(inference) = operand_types(db, scope, owner.as_ref()) else {
                return unavailable();
            };
            if inference.is_provisional() {
                return pending();
            }
            let subscript = subscript.node(&module);
            let Some(key) = inference.try_expression_type(&subscript.slice) else {
                return unavailable();
            };
            let Some(value) = inference.try_expression_type(ast::ExprRef::from(subscript)) else {
                return unavailable();
            };
            MappingTransfer::Set {
                key,
                value,
                source: subscript.slice.range(),
            }
        }
        DictionaryContentsEffect::DeleteItem { subscript, owner } => {
            let Some(inference) = operand_types(db, scope, owner.as_ref()) else {
                return unavailable();
            };
            if inference.is_provisional() {
                return pending();
            }
            let subscript = subscript.node(&module);
            let Some(key) = inference.try_expression_type(&subscript.slice) else {
                return unavailable();
            };
            MappingTransfer::Delete {
                key,
                source: subscript.slice.range(),
            }
        }
        DictionaryContentsEffect::Call {
            call,
            owner,
            retained,
        } => {
            let Some(inference) = operand_types(db, scope, owner.as_ref()) else {
                return unavailable();
            };
            if inference.is_provisional() {
                return pending();
            }
            let call = call.node(&module);
            if let Some(Type::ClassLiteral(class)) = inference.try_expression_type(&call.func)
                && class.is_known(db, KnownClass::Dict)
            {
                return if *retained {
                    MappingTransfer::Expose
                } else {
                    MappingTransfer::Keep
                };
            }
            let receiver = receiver.node(&module);
            let method = call.func.as_attribute_expr().filter(|attribute| {
                PlaceExpr::try_from_expr(&*attribute.value) == PlaceExpr::try_from_expr(receiver)
                    && inference
                        .try_expression_type(receiver)
                        .and_then(Type::as_nominal_instance)
                        .is_some_and(|instance| instance.has_known_class(db, KnownClass::Dict))
            });
            let Some(method) = method else {
                return MappingTransfer::Expose;
            };
            match method.attr.as_str() {
                "copy" | "get" | "keys" | "items" | "values" | "__getitem__" | "__contains__" => {
                    // A read-only operation can return an argument, including this receiver
                    // supplied again as a default value.
                    if *retained
                        || call.arguments.args.iter().any(|argument| {
                            PlaceExpr::try_from_expr(argument) == PlaceExpr::try_from_expr(receiver)
                        })
                    {
                        MappingTransfer::Expose
                    } else {
                        MappingTransfer::Keep
                    }
                }
                "clear" => {
                    if call.arguments.is_empty() {
                        MappingTransfer::Clear
                    } else {
                        unavailable()
                    }
                }
                "pop" => {
                    let key = match call.arguments.args.as_ref() {
                        [key] => key,
                        [key, _default] => key,
                        _ => return unavailable(),
                    };
                    if !call.arguments.keywords.is_empty() {
                        return unavailable();
                    }
                    let Some(key_ty) = inference.try_expression_type(key) else {
                        return unavailable();
                    };
                    MappingTransfer::Delete {
                        key: key_ty,
                        source: key.range(),
                    }
                }
                "update" => {
                    let mut update = DictionaryItemsBuilder::default();
                    match call.arguments.args.as_ref() {
                        [] => {}
                        [source] => {
                            if source.is_starred_expr() {
                                return unavailable();
                            }
                            let source = match DictionaryItems::positional_source(
                                db,
                                &env,
                                scope,
                                call.into(),
                                source,
                                &mut |expression| inference.try_expression_type(expression),
                            ) {
                                Ok(source) => source,
                                Err(DictionaryFallback::Unavailable) => return unavailable(),
                                Err(DictionaryFallback::Unreachable) => {
                                    return MappingTransfer::Result(ContentsValue::Unreachable);
                                }
                            };
                            update.overlay(db, &env, source);
                        }
                        _ => return unavailable(),
                    }
                    let keywords = match DictionaryItems::keywords(
                        db,
                        &env,
                        scope,
                        &call.arguments.keywords,
                        &mut |expression| inference.try_expression_type(expression),
                    ) {
                        Ok(keywords) => keywords,
                        Err(DictionaryFallback::Unavailable) => return unavailable(),
                        Err(DictionaryFallback::Unreachable) => {
                            return MappingTransfer::Result(ContentsValue::Unreachable);
                        }
                    };
                    update.overlay(db, &env, keywords);
                    MappingTransfer::Update {
                        dictionary: update.finish(),
                        retained: *retained,
                    }
                }
                _ => MappingTransfer::Expose,
            }
        }
    }
}

fn operand_types<'db>(
    db: &'db dyn Db,
    scope: ScopeId<'db>,
    owner: Option<&DictionaryContentsInferenceOwner>,
) -> Option<StatementInference<'db>> {
    let file = scope.program_file(db);
    let module = parsed_module(db, file.python_file(db)).load(db);
    let index = semantic_index(db, file);
    let statement = match owner? {
        DictionaryContentsInferenceOwner::Expression(expression) => {
            Statement::Expression(index.try_expression(expression.node(&module))?)
        }
        DictionaryContentsInferenceOwner::Statement(statement) => {
            index.try_statement(statement.node(&module))?
        }
    };
    Some(infer_statement_types(db, statement))
}

pub(crate) enum KeyPreservation {
    Preserved,
    Changed,
    Pending,
}

/// Prove that all current contents paths preserve a key read by a saved predicate.
/// This follows the existing definition graph; it does not compare inferred values or source
/// ranges, which can coincide for different mutations and loop iterations.
pub(crate) fn alias_preserves_key<'db>(
    db: &'db dyn Db,
    scope: ScopeId<'db>,
    original: &ast::Expr,
    current: &ast::Expr,
    key_place: ScopedPlaceId,
    loop_carried: bool,
) -> Option<KeyPreservation> {
    struct KeyRead<'a, 'ast> {
        table: &'a PlaceTable,
        target: ScopedPlaceId,
        read: Option<&'ast ast::ExprSubscript>,
        multiple: bool,
    }
    impl<'ast> Visitor<'ast> for KeyRead<'_, 'ast> {
        fn visit_expr(&mut self, expression: &'ast ast::Expr) {
            if let ast::Expr::Subscript(subscript) = expression
                && let Some(place) = PlaceExpr::try_from_expr(expression)
                && self.table.place_id(&place) == Some(self.target)
            {
                self.multiple |= self.read.replace(subscript).is_some();
            }
            walk_expr(self, expression);
        }
    }
    let index = semantic_index(db, scope.program_file(db));
    let table = index.place_table(scope.file_scope_id(db));
    let mut reads = KeyRead {
        table,
        target: key_place,
        read: None,
        multiple: false,
    };
    reads.visit_expr(original);
    let read = reads.read?;
    let place = PlaceExpr::contents(&read.value)?;
    let place = table.place_id(&place)?;
    if reads.multiple || loop_carried {
        return Some(KeyPreservation::Changed);
    }
    let name = read.slice.as_string_literal_expr()?.value.to_str();
    let use_def = index.use_def_map(scope.file_scope_id(db));
    let Some(original_use) = index.try_expression_use_id(ast::ExprRef::from(read)) else {
        return Some(KeyPreservation::Changed);
    };
    let Some(current_use) = index.try_expression_use_id(current.into()) else {
        return Some(KeyPreservation::Changed);
    };
    let Some(original_bindings) = use_def.multi_bindings_at_use(original_use, place) else {
        return Some(KeyPreservation::Changed);
    };
    let Some(current_bindings) = use_def.multi_bindings_at_use(current_use, place) else {
        return Some(KeyPreservation::Changed);
    };
    let anchors: Vec<_> = original_bindings.map(|binding| binding.binding).collect();
    let mut pending: Vec<_> = current_bindings.map(|binding| binding.binding).collect();
    let mut visited = FxHashSet::default();
    let mut provisional = false;
    while let Some(binding) = pending.pop() {
        if anchors.contains(&binding) {
            continue;
        }
        let Some(definition) = binding.definition() else {
            return Some(KeyPreservation::Changed);
        };
        // Ordinary operation predecessors are source ordered. LoopHeader is the only back
        // edge and is rejected below; deduplication therefore only skips shared suffixes.
        if !visited.insert(definition) {
            continue;
        }
        let DefinitionKind::DictionaryContents(contents) = definition.kind(db) else {
            return Some(KeyPreservation::Changed);
        };
        match contents.as_ref() {
            DictionaryContentsDefinitionKind::Initialize {
                definition: _,
                range: _,
            } => return Some(KeyPreservation::Changed),
            DictionaryContentsDefinitionKind::Operation { receiver, effect } => {
                let transfer = mapping_transfer(db, definition, receiver, effect);
                if matches!(transfer, MappingTransfer::Result(ContentsValue::Pending)) {
                    provisional = true;
                    continue;
                }
                if !transfer.preserves_key(db, name) {
                    return Some(KeyPreservation::Changed);
                }
            }
            DictionaryContentsDefinitionKind::Capture {
                nested_scope: _,
                name: _,
                range: _,
                execution,
                resolution: _,
            } => {
                if *execution == NestedBindingExecution::Lazy {
                    continue;
                }
            }
            // Modifier-only bindings do not change a key's value, and do not stand in for
            // the ordinary loop header, which the traversal rejects above.
            DictionaryContentsDefinitionKind::LoopCapture {
                header: _,
                range: _,
            } => continue,
        }
        pending.extend(
            use_def
                .bindings_at_definition(definition)
                .map(|binding| binding.binding),
        );
    }
    Some(if provisional {
        KeyPreservation::Pending
    } else {
        KeyPreservation::Preserved
    })
}

fn from_bindings<'db>(
    db: &'db dyn Db,
    scope: ScopeId<'db>,
    bindings: BindingWithConstraintsIterator<'_, 'db>,
    reachability: &ReachabilityEvaluationCache<'db>,
) -> Contents<'db> {
    let env = ProgramEnvironment::from_scope(scope);
    let constraints = bindings.reachability_constraints();
    let predicates = bindings.predicates();
    let mut result = Contents::new(ContentsValue::Unreachable);
    for binding in bindings {
        if evaluate_reachability_with_cache(
            db,
            Some(reachability),
            constraints,
            predicates,
            binding.reachability_constraint,
        )
        .is_always_false()
        {
            continue;
        }
        let incoming = match binding.binding {
            DefinitionState::Defined(definition) => definition_contents(db, definition).narrow(
                db,
                scope,
                definition.place(db),
                &binding.narrowing_constraint,
            ),
            DefinitionState::Undefined => Contents::new(ContentsValue::Unavailable),
            DefinitionState::Deleted => Contents::new(ContentsValue::Unavailable),
        };
        result = result.join(db, &env, incoming);
    }
    result
}

pub(super) fn at_use<'db>(
    db: &'db dyn Db,
    scope: ScopeId<'db>,
    expression: &ast::Expr,
    argument_type: Type<'db>,
    reachability: &ReachabilityEvaluationCache<'db>,
) -> DictionaryObservation<'db> {
    at_snapshot(
        db,
        scope,
        expression,
        expression.into(),
        argument_type,
        reachability,
    )
}

pub(super) fn at_snapshot<'db>(
    db: &'db dyn Db,
    scope: ScopeId<'db>,
    expression: &ast::Expr,
    snapshot: ast::ExprRef<'_>,
    argument_type: Type<'db>,
    reachability: &ReachabilityEvaluationCache<'db>,
) -> DictionaryObservation<'db> {
    let observed = (|| {
        if !argument_type
            .as_nominal_instance()?
            .has_known_class(db, KnownClass::Dict)
        {
            return None;
        }
        let file = scope.program_file(db);
        let index = semantic_index(db, file);
        let place = PlaceExpr::contents(expression)?;
        let contents_place = index
            .place_table(scope.file_scope_id(db))
            .place_id(&place)?;
        let use_id = index.try_expression_use_id(snapshot)?;
        let use_def = index.use_def_map(scope.file_scope_id(db));
        let bindings = use_def.multi_bindings_at_use(use_id, contents_place)?;
        let Contents { value, captured: _ } = from_bindings(db, scope, bindings, reachability);
        Some(value)
    })();
    match observed {
        Some(ContentsValue::Mapping(mut mapping)) => {
            mapping.localize(scope.program_file(db), expression.range());
            let MappingContents {
                file: _,
                dictionary,
                exposed: _,
                value_bound: _,
            } = mapping;
            Ok(dictionary)
        }
        Some(ContentsValue::Unreachable) => Err(DictionaryFallback::Unreachable),
        Some(ContentsValue::Pending) => Err(DictionaryFallback::Unavailable),
        Some(ContentsValue::Unavailable) => Err(DictionaryFallback::Unavailable),
        None => Err(DictionaryFallback::Unavailable),
    }
}
