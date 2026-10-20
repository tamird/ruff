//! Mapping contents at a use, inferred from the ordinary reaching-definition graph.

use ruff_db::parsed::parsed_module;
use ruff_python_ast as ast;
use ruff_python_ast::HasNodeIndex;
use ruff_python_ast::helpers::any_over_expr;
use ruff_python_ast::name::Name;
use ruff_python_ast::visitor::{Visitor, walk_expr};
use ruff_text_size::{Ranged, TextRange};
use rustc_hash::FxHashSet;
use ty_python_core::definition::{
    Definition, DefinitionKind, DefinitionState, DictionaryContentsDefinitionKind,
    DictionaryContentsEffect, DictionaryContentsInferenceOwner, LambdaParameterDefinitionNodeKind,
    NestedBindingExecution, ParameterDefinitionNodeKind,
};
use ty_python_core::place::ScopedPlaceId;
use ty_python_core::place::{PlaceExpr, PlaceTable};
use ty_python_core::scope::{FileScopeId, NodeWithScopeKind, ScopeId};
use ty_python_core::symbol::Symbol;
use ty_python_core::{
    BindingWithConstraintsIterator, NarrowingEvaluator, ProgramFile, Statement, semantic_index,
};

use crate::Db;
use crate::place::loop_header_reachability;
use crate::provided::ProvidedBindingValue;
use crate::reachability::{ReachabilityEvaluationCache, evaluate_reachability_with_cache};
use crate::types::call::CallArguments;
use crate::types::infer::{
    DefinitionInference, FunctionBodyDomain, StatementInference, infer_definition_with_body_domain,
    infer_statement_with_body_domain,
};
use crate::types::narrow::NarrowingEvaluatorExtension;
use crate::types::{KnownClass, KnownFunction, ProgramEnvironment, Type, UnionBuilder, UnionType};

use super::{
    DictionaryExtraItems, DictionaryFallback, DictionaryFirstEntry, DictionaryItem,
    DictionaryItemKind, DictionaryItems, DictionaryItemsBuilder, DictionaryObservation,
    ParamSpecKeywords,
};

/// A cycle seed, unreachable control flow, missing history, and an inhabited mapping are
/// distinct. In particular, neither missing history nor a pending cycle proves an empty map.
#[derive(Clone, Debug, PartialEq, Eq, get_size2::GetSize, salsa::SalsaValue)]
pub(super) enum ContentsValue<'db> {
    Pending,
    Unreachable,
    Unavailable,
    Mapping(MappingContents<'db>),
}

#[derive(Clone, Debug, PartialEq, Eq, get_size2::GetSize, salsa::SalsaValue)]
pub(super) struct MappingContents<'db> {
    /// All ranges belong to this file. Copying from another file rebases them to the local use.
    pub(super) file: ProgramFile<'db>,
    pub(super) dictionary: DictionaryItems<'db>,
    /// Builtin construction or a checked final allocation class establishes builtin operations.
    /// Exposure changes contents while preserving this class identity.
    pub(super) builtin: bool,
    /// Opaque exposure leaves only value restrictions, rather than evidence of key presence.
    /// An explicitly described `TypedDict` retains its schema and can track subsequent mutations.
    pub(super) uses_residual_presence: bool,
    /// The original mapping bound and its local source survive exposure.
    pub(super) bound: Option<MappingBound<'db>>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, get_size2::GetSize, salsa::SalsaValue)]
pub(super) struct MappingBound<'db> {
    ty: Type<'db>,
    source: TextRange,
}

impl<'db> MappingContents<'db> {
    fn bound_value(&self, db: &'db dyn Db, env: &ProgramEnvironment<'db>) -> Type<'db> {
        self.bound
            .and_then(|MappingBound { ty, source: _ }| ty.unpack_keys_and_items(db, env))
            .map_or_else(Type::unknown, |(_, value)| value)
    }

    fn expose(&mut self, db: &'db dyn Db, env: &ProgramEnvironment<'db>) {
        self.dictionary.first_entry = DictionaryFirstEntry::Unknown;
        self.dictionary.items = Box::default();
        self.generalize_presence(db, env);
    }

    /// Retain observed values without treating ordinary dictionary entries as supplied keys.
    fn generalize_presence(&mut self, db: &'db dyn Db, env: &ProgramEnvironment<'db>) {
        if let Some(MappingBound { ty, source }) = self.bound
            && has_explicit_typed_dict_items(db, ty)
            && let Some(dictionary) = DictionaryItems::unpacked(db, env, ty, source)
        {
            self.dictionary = dictionary;
            self.uses_residual_presence = false;
            return;
        }
        self.uses_residual_presence = true;
        self.dictionary.items = std::mem::take(&mut self.dictionary.items)
            .into_vec()
            .into_iter()
            .filter(|item| !item.ty.resolve_type_alias(db).is_never())
            .collect();
        for item in &mut self.dictionary.items {
            item.kind = DictionaryItemKind::Residual;
        }
        self.dictionary.extra_items = DictionaryExtraItems::Value(self.bound_value(db, env));
    }

    fn set_item(
        &mut self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        key: Type<'db>,
        value: Type<'db>,
        source: TextRange,
    ) {
        self.dictionary
            .first_entry
            .set(db, env, key.string_literal_value(db), value);
        if let Some(name) = key.string_literal_value(db) {
            let name = Name::new(name);
            let item = DictionaryItem {
                name: name.clone(),
                ty: value,
                kind: if self.uses_residual_presence {
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
            let key = UnionBuilder::new(db, env).add(key).build();
            if let Some(keys) = key.string_literal_values(db) {
                let items = keys
                    .map(|name| DictionaryItem {
                        name: Name::new(name),
                        ty: value,
                        kind: if self.uses_residual_presence {
                            DictionaryItemKind::Residual
                        } else {
                            DictionaryItemKind::Optional
                        },
                        source,
                    })
                    .collect();
                let mut result = DictionaryItemsBuilder::default();
                result.overlay(db, env, self.dictionary.clone());
                result.overlay(
                    db,
                    env,
                    DictionaryItems {
                        items,
                        extra_items: DictionaryExtraItems::Closed,
                        first_entry: DictionaryFirstEntry::Unknown,
                    },
                );
                self.dictionary = result.finish();
                return;
            }
            // A computed key can overwrite any named value as well as introduce another name.
            for item in &mut self.dictionary.items {
                item.ty = UnionType::from_two_elements(db, env, item.ty, value);
            }
            self.dictionary.extra_items = DictionaryExtraItems::Value(
                UnionType::from_two_elements(db, env, self.dictionary.extra_value(), value),
            );
        }
    }

    fn set_default(
        &mut self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        key: Type<'db>,
        value: Type<'db>,
        source: TextRange,
    ) {
        let previous = std::mem::replace(
            &mut self.dictionary,
            DictionaryItems {
                items: Box::default(),
                extra_items: DictionaryExtraItems::Closed,
                first_entry: DictionaryFirstEntry::Empty,
            },
        );
        self.set_item(db, env, key, value, source);
        let first_entry = match &previous.first_entry {
            DictionaryFirstEntry::Empty => self.dictionary.first_entry.clone(),
            DictionaryFirstEntry::Entry { key: _, value: _ } => previous.first_entry.clone(),
            DictionaryFirstEntry::Unknown => DictionaryFirstEntry::Unknown,
        };
        // Existing required entries replace the candidate default, while optional entries
        // retain both possibilities. Runtime insertion order still starts with the old map.
        let mut result = DictionaryItemsBuilder::default();
        result.overlay(db, env, self.dictionary.clone());
        result.overlay(db, env, previous);
        self.dictionary = result.finish();
        self.dictionary.first_entry = first_entry;
    }

    fn delete_item(
        &mut self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        key: Type<'db>,
        source: TextRange,
    ) {
        if let DictionaryFirstEntry::Entry {
            key: first_key,
            value: _,
        } = &self.dictionary.first_entry
        {
            if first_key.as_ref().is_none_or(|first_key| {
                key.string_literal_value(db)
                    .is_none_or(|key| first_key == key)
            }) {
                // The named inventory does not establish which remaining entry comes next.
                self.dictionary.first_entry = DictionaryFirstEntry::Unknown;
            }
        }
        if let Some(name) = key.string_literal_value(db) {
            let name = Name::new(name);
            let mut items = std::mem::take(&mut self.dictionary.items).into_vec();
            items.retain(|item| item.name != name);
            // A closed inventory already excludes missing names. An open remainder needs an
            // explicit exclusion so it cannot supply the deleted key.
            if !self.uses_residual_presence && !self.dictionary.is_complete() {
                items.push(DictionaryItem {
                    name,
                    ty: Type::Never,
                    kind: DictionaryItemKind::Residual,
                    source,
                });
            }
            self.dictionary.items = items.into_boxed_slice();
        } else {
            let key = UnionBuilder::new(db, env).add(key).build();
            let names = key
                .string_literal_values(db)
                .map(Iterator::collect::<FxHashSet<_>>);
            for item in &mut self.dictionary.items {
                if item.kind == DictionaryItemKind::Required
                    && names
                        .as_ref()
                        .is_none_or(|names| names.contains(item.name.as_str()))
                {
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
            if let Some(bound) = &mut self.bound {
                bound.source = source;
            }
            self.file = file;
        }
    }

    pub(super) fn join(
        &self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        other: &Self,
    ) -> Self {
        let Self {
            file,
            dictionary,
            builtin,
            uses_residual_presence,
            bound,
        } = self;
        let Self {
            file: _,
            dictionary: other_dictionary,
            builtin: other_builtin,
            uses_residual_presence: other_uses_residual_presence,
            bound: other_bound,
        } = other;
        let uses_residual_presence = *uses_residual_presence || *other_uses_residual_presence;
        let bound = bound.zip(*other_bound).map(|(left, right)| MappingBound {
            ty: UnionType::from_two_elements(db, env, left.ty, right.ty),
            source: left.source,
        });
        Self {
            file: *file,
            dictionary: dictionary.join(db, env, other_dictionary, uses_residual_presence),
            uses_residual_presence,
            bound,
            builtin: *builtin && *other_builtin,
        }
    }
}

impl<'db> ContentsValue<'db> {
    pub(super) fn from_literal(
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        scope: ScopeId<'db>,
        value: &ast::Expr,
        inference: &StatementInference<'db>,
    ) -> Self {
        if inference.is_provisional() {
            return Self::Pending;
        }
        let ast::Expr::Dict(dictionary) = value else {
            return Self::Unavailable;
        };
        if dictionary.items.iter().any(|item| {
            !item
                .key
                .as_ref()
                .is_some_and(ast::Expr::is_string_literal_expr)
        }) {
            return Self::Unavailable;
        }
        let mut pending = false;
        let observed =
            DictionaryItems::expression(db, env, scope, value, None, &mut |expression| {
                let ty = inference.try_expression_type(expression)?;
                if crate::types::visitor::any_over_type_expanding_aliases(db, env, ty, |ty| {
                    matches!(ty, Type::Divergent(_))
                }) {
                    pending = true;
                    return None;
                }
                if matches!(ty.resolve_type_alias(db), Type::Never) {
                    return None;
                }
                Some(ty)
            });
        if pending {
            Self::Pending
        } else {
            match observed {
                Ok(dictionary) => Self::Mapping(MappingContents {
                    file: scope.program_file(db),
                    dictionary,
                    builtin: true,
                    uses_residual_presence: false,
                    bound: None,
                }),
                Err(_) => Self::Unavailable,
            }
        }
    }

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

    pub(super) fn cycle_normalized(
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
            if let DictionaryFirstEntry::Entry { key: _, value } =
                &mut mapping.dictionary.first_entry
            {
                let previous_ty = match previous {
                    Self::Mapping(previous) => match previous.dictionary.first_entry {
                        DictionaryFirstEntry::Entry { key: _, value } => value,
                        DictionaryFirstEntry::Unknown => Type::Never,
                        DictionaryFirstEntry::Empty => Type::Never,
                    },
                    _ => Type::Never,
                };
                *value = value.cycle_normalized(db, env, previous_ty, cycle);
            }
            for item in &mut mapping.dictionary.items {
                let previous_ty = match previous {
                    Self::Mapping(previous) => previous.dictionary.value_at(&item.name),
                    _ => Type::Never,
                };
                item.ty = item.ty.cycle_normalized(db, env, previous_ty, cycle);
            }
            if let DictionaryExtraItems::Value(ty) = &mut mapping.dictionary.extra_items {
                let previous_ty = match previous {
                    Self::Mapping(previous) => previous.dictionary.extra_value(),
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
    fn cycle_normalized(
        self,
        db: &'db dyn Db,
        previous: &Self,
        cycle: &salsa::Cycle,
        definition: Definition<'db>,
    ) -> Self {
        let env = ProgramEnvironment::from_definition(definition);
        let Self { value, captured } = self;
        let Self {
            value: previous_value,
            captured: previous_captured,
        } = previous;
        let value = value.cycle_normalized(db, &env, previous_value, cycle);
        let captured = if cycle.iteration() <= crate::TAINTED_CYCLES {
            captured
        } else {
            *previous_captured || captured
        };
        Self { value, captured }
    }

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
            mapping.expose(db, env);
        }
        Self { value, captured }
    }

    fn narrow(
        mut self,
        db: &'db dyn Db,
        scope: ScopeId<'db>,
        definition: Definition<'db>,
        constraint: &NarrowingEvaluator<'_, 'db>,
        domain: Option<FunctionBodyDomain<'db>>,
    ) -> Self {
        if matches!(self.value, ContentsValue::Pending) {
            return self;
        }
        let env = ProgramEnvironment::from_scope(scope);
        // Receiver guards can exclude an initializer or establish its mapping type. Later
        // history steps still obtain their contents through the recorded predecessors.
        if let DefinitionKind::DictionaryContents(contents) = definition.kind(db)
            && let DictionaryContentsDefinitionKind::Initialize {
                definition: receiver,
                range: _,
            } = contents.as_ref()
        {
            let inference = infer_definition_with_body_domain(db, *receiver, domain);
            let bound = inference.binding_type(*receiver);
            let narrowed = constraint.narrow_in_domain(db, &env, bound, receiver.place(db), domain);
            if narrowed.resolve_type_alias(db).is_never() {
                self.value = ContentsValue::Unreachable;
            } else if matches!(self.value, ContentsValue::Unavailable) && narrowed != bound {
                self.value = initial_contents(db, *receiver, narrowed, domain);
            }
        }
        let ContentsValue::Mapping(mapping) = &mut self.value else {
            return self;
        };
        let place = definition.place(db);
        let index = semantic_index(db, scope.program_file(db));
        let table = index.place_table(scope.file_scope_id(db));
        for item in &mut mapping.dictionary.items {
            let Some(key) = table.contents_key(place, &item.name) else {
                continue;
            };
            item.ty = constraint.narrow_in_domain(db, &env, item.ty, key, domain);
            if item.is_required() && item.ty.resolve_type_alias(db).is_never() {
                self.value = ContentsValue::Unreachable;
                return self;
            }
        }
        if let DictionaryFirstEntry::Entry {
            key: Some(name),
            value,
        } = &mut mapping.dictionary.first_entry
            && let Some(key) = table.contents_key(place, name)
        {
            *value = constraint.narrow_in_domain(db, &env, *value, key, domain);
            if value.resolve_type_alias(db).is_never() {
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
        result.cycle_normalized(db, previous, cycle, definition)
    },
    heap_size=get_size2::GetSize::get_heap_size,
)]
fn definition_contents<'db>(db: &'db dyn Db, definition: Definition<'db>) -> Contents<'db> {
    infer_definition_contents(db, definition, None)
}

#[salsa::tracked(
    returns(clone),
    cycle_initial=|_, _, _, _| Contents::new(ContentsValue::Pending),
    cycle_fn=|db, cycle, previous: &Contents<'db>, result: Contents<'db>, definition: Definition<'db>, _| {
        result.cycle_normalized(db, previous, cycle, definition)
    },
    heap_size=get_size2::GetSize::get_heap_size,
)]
fn body_definition_contents<'db>(
    db: &'db dyn Db,
    definition: Definition<'db>,
    domain: FunctionBodyDomain<'db>,
) -> Contents<'db> {
    infer_definition_contents(db, definition, Some(domain))
}

fn definition_contents_in_domain<'db>(
    db: &'db dyn Db,
    definition: Definition<'db>,
    domain: Option<FunctionBodyDomain<'db>>,
) -> Contents<'db> {
    domain
        .filter(|domain| domain.scope(db) == definition.scope(db))
        .map_or_else(
            || definition_contents(db, definition),
            |domain| body_definition_contents(db, definition, domain),
        )
}

fn infer_definition_contents<'db>(
    db: &'db dyn Db,
    definition: Definition<'db>,
    domain: Option<FunctionBodyDomain<'db>>,
) -> Contents<'db> {
    let scope = definition.scope(db);
    let env = ProgramEnvironment::from_scope(scope);
    let index = semantic_index(db, scope.program_file(db));
    let use_def = index.use_def_map(scope.file_scope_id(db));
    let reachability = ReachabilityEvaluationCache::new(scope, use_def.reachability_constraints())
        .with_body_domain(domain.filter(|domain| domain.scope(db) == scope));

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
                let incoming = definition_contents_in_domain(db, binding.definition, domain)
                    .narrow(
                        db,
                        scope,
                        binding.definition,
                        &use_def.narrowing_evaluator(binding.narrowing_constraint),
                        domain,
                    );
                result = result.join(db, &env, incoming);
            }
            result
        }
        DefinitionKind::DictionaryContents(contents) => match contents.as_ref() {
            DictionaryContentsDefinitionKind::Initialize {
                definition,
                range: _,
            } => {
                let inference = infer_definition_with_body_domain(db, *definition, domain);
                Contents::new(initial_contents(
                    db,
                    *definition,
                    inference.binding_type(*definition),
                    domain,
                ))
            }
            DictionaryContentsDefinitionKind::LoopCapture { header, range: _ } => {
                let Contents { value, captured } =
                    definition_contents_in_domain(db, *header, domain);
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
                Contents::new(operation_contents(db, definition, receiver, effect, domain))
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
                        if let ContentsValue::Mapping(mapping) = &mut result.value
                            && !capture_has_no_reachable_effects(db, definition, *nested_scope)
                        {
                            mapping.expose(db, &env);
                        }
                        result
                    }
                }
            }
        },
        _ => Contents::new(ContentsValue::Unavailable),
    }
}

fn capture_has_no_reachable_effects<'db>(
    db: &'db dyn Db,
    capture: Definition<'db>,
    nested_scope: FileScopeId,
) -> bool {
    let scope = capture.scope(db);
    let file = scope.program_file(db);
    let index = semantic_index(db, file);
    let place = index
        .place_table(scope.file_scope_id(db))
        .place(capture.place(db));
    let Some(place) = index.place_table(nested_scope).place_id(place) else {
        return false;
    };
    let scope = nested_scope.to_scope_id(db, file);
    let use_def = index.use_def_map(nested_scope);
    let reachability = ReachabilityEvaluationCache::new(scope, use_def.reachability_constraints());
    // This inventory retains earlier operations even when a later binding shadows them.
    let mut bindings = use_def.reachable_bindings(place);
    // A captured place has no local value at scope entry; this is not an inferred empty map.
    if bindings.next().map(|binding| binding.binding) != Some(DefinitionState::Undefined) {
        return false;
    }
    bindings.all(|binding| {
        evaluate_reachability_with_cache(
            db,
            Some(&reachability),
            use_def.reachability_constraints(),
            use_def.predicates(),
            binding.reachability_constraint,
        )
        .is_always_false()
    })
}

/// Seed the contents graph from the same binding that owns ordinary value inference.
/// Nominal dictionary parameters and members carry value refinements without a closed key set.
/// An explicitly described `TypedDict` retains its fields until a recorded mutation changes them.
fn initial_contents<'db>(
    db: &'db dyn Db,
    definition: Definition<'db>,
    bound_type: Type<'db>,
    domain: Option<FunctionBodyDomain<'db>>,
) -> ContentsValue<'db> {
    if crate::types::infer::is_discarded_dict_key_assignment(db, definition) {
        return ContentsValue::Unavailable;
    }
    let scope = definition.scope(db);
    let env = ProgramEnvironment::from_scope(scope);
    let file = scope.program_file(db);
    let module = parsed_module(db, file.python_file(db)).load(db);
    let inference = infer_definition_with_body_domain(db, definition, domain);
    if StatementInference::Definition(definition, inference).is_provisional() {
        return ContentsValue::Pending;
    }
    let explicit_typed_dict = has_explicit_typed_dict_items(db, bound_type);
    let paramspec = matches!(
        definition.kind(db),
        DefinitionKind::Parameter(ParameterDefinitionNodeKind::VariadicKeywordParameter(_))
    )
    .then(|| ParamSpecKeywords::from_type(db, bound_type))
    .flatten();
    if !explicit_typed_dict && paramspec.is_none() && !super::has_dict_type(db, &env, bound_type) {
        return ContentsValue::Unavailable;
    }
    if matches!(definition.kind(db), DefinitionKind::ProvidedBinding(_))
        && let ProvidedBindingValue::Export {
            file,
            name,
            value: None,
        } = db.provided_binding(definition).value
        && db.provided_exports_are_frozen(file)
        && let Some(mut contents) = frozen_export_contents(db, file, &name)
    {
        if let ContentsValue::Mapping(mapping) = &mut contents {
            mapping.localize(
                definition.program_file(db),
                definition.kind(db).target_range(&module),
            );
        }
        return contents;
    }
    let index = semantic_index(db, file);
    let place = index
        .place_table(scope.file_scope_id(db))
        .place(definition.place(db));
    if !place.is_declared() && matches!(definition.kind(db), DefinitionKind::For(_)) {
        match super::records::for_target(db, definition) {
            ContentsValue::Unavailable => {}
            contents => return contents,
        }
    }
    let (owner, value, shared) = match definition.kind(db) {
        DefinitionKind::DictKeyAssignment(assignment) => (
            assignment.assignment(),
            Some(assignment.value(&module)),
            false,
        ),
        DefinitionKind::NamedExpression(named) => {
            (definition, Some(named.node(&module).value.as_ref()), false)
        }
        DefinitionKind::Assignment(assignment) => (
            definition,
            Some(assignment.value(&module)),
            !assignment.is_single_target(&module),
        ),
        kind => (definition, kind.value(&module), false),
    };
    let owner_inference = infer_definition_with_body_domain(db, owner, domain);
    if StatementInference::Definition(owner, owner_inference).is_provisional() {
        return ContentsValue::Pending;
    }
    let builtin_allocation = !owner_inference.discards_dict_key_assignments()
        && value.is_some_and(|value| is_builtin_allocation(db, value, owner_inference));
    let observed = value
        .filter(|value| {
            !owner_inference.discards_dict_key_assignments()
                // A conditional can select an existing dictionary. Its contents describe the
                // expression at this point, but later mutation through an alias can invalidate
                // them. Only persist the observation when both arms allocate fresh dictionaries.
                && (!matches!(value, ast::Expr::If(_)) || builtin_allocation)
        })
        .map_or(Err(DictionaryFallback::Unavailable), |value| {
            DictionaryItems::expression(db, &env, scope, value, domain, &mut |expression| {
                owner_inference.try_expression_type(expression)
            })
        });
    let fresh_nested_allocation =
        matches!(definition.kind(db), DefinitionKind::DictKeyAssignment(_))
            && matches!(owner.kind(db), DefinitionKind::Assignment(assignment)
            if assignment.is_single_target(&module)
                && assignment.target(&module).is_name_expr()
                && assignment.value(&module).is_dict_expr())
            && matches!(value, Some(ast::Expr::Dict(_) | ast::Expr::BinOp(_)))
            && observed.is_ok();
    // A fresh allocation can prove its contents even when its inferred type is a union.
    // Unobserved union bounds retain their per-alternative key domains.
    if !explicit_typed_dict
        && paramspec.is_none()
        && bound_type.as_nominal_instance().is_none()
        && observed.is_err()
    {
        return ContentsValue::Unavailable;
    }
    let parent_preserved = if builtin_allocation && !shared && !place.is_symbol() {
        match parent_allows_seed(db, owner, domain) {
            KeyPreservation::Preserved => true,
            KeyPreservation::Changed => false,
            KeyPreservation::Pending => return ContentsValue::Pending,
        }
    } else {
        true
    };
    let bounded = !place.is_symbol() || place.is_declared() || value.is_none();
    let source = definition.kind(db).target_range(&module);
    let bound = (bounded || explicit_typed_dict).then_some(MappingBound {
        ty: bound_type,
        source,
    });
    let Some(mut dictionary) = DictionaryItems::unpacked(db, &env, bound_type, source) else {
        return ContentsValue::Unavailable;
    };
    if let Some(component) = paramspec {
        dictionary.extra_items = DictionaryExtraItems::ParamSpec(component);
    }
    let kwargs_parameters = match definition.kind(db) {
        DefinitionKind::Parameter(parameter) => match parameter {
            ParameterDefinitionNodeKind::VariadicKeywordParameter(_) => match scope.node(db) {
                NodeWithScopeKind::Function(function) => {
                    Some(function.node(&module).parameters.as_ref())
                }
                _ => None,
            },
            _ => None,
        },
        DefinitionKind::LambdaParameter(LambdaParameterDefinitionNodeKind {
            index: _,
            lambda,
            parameter,
        }) => match parameter {
            ParameterDefinitionNodeKind::VariadicKeywordParameter(_) => {
                lambda.node(&module).parameters.as_deref()
            }
            _ => None,
        },
        _ => None,
    };
    let provided_allocation = bound_type.as_nominal_instance().is_some_and(|instance| {
        KnownClass::Dict.provided_allocation_class(db, &env)
            == Some(instance.class_literal(db, &env))
    });
    let mut mapping = MappingContents {
        file,
        dictionary,
        builtin: explicit_typed_dict || provided_allocation || kwargs_parameters.is_some(),
        uses_residual_presence: false,
        bound,
    };
    if !owner_inference.discards_dict_key_assignments()
        && let Some(value) = value
    {
        // A constructor establishes allocation even when its keys cannot be enumerated.
        mapping.builtin |= builtin_allocation;
        if PlaceExpr::try_from_expr(value).is_some() {
            let use_def = index.use_def_map(scope.file_scope_id(db));
            let cache = ReachabilityEvaluationCache::new(scope, use_def.reachability_constraints())
                .with_body_domain(domain.filter(|domain| domain.scope(db) == scope));
            match snapshot_contents(db, scope, value, value.into(), bound_type, &cache) {
                ContentsValue::Mapping(source) => mapping.builtin |= source.builtin,
                ContentsValue::Pending => return ContentsValue::Pending,
                ContentsValue::Unreachable => return ContentsValue::Unreachable,
                ContentsValue::Unavailable => {}
            }
        }
        match observed {
            Ok(dictionary) => {
                mapping.dictionary = dictionary;
                mapping.builtin = true;
            }
            Err(DictionaryFallback::Unreachable) => return ContentsValue::Unreachable,
            Err(DictionaryFallback::Unavailable) => {
                if !value.is_dict_expr() {
                    match DictionaryItems::unpacked_value(
                        db,
                        &env,
                        scope,
                        value,
                        domain,
                        &mut |expression| owner_inference.try_expression_type(expression),
                    ) {
                        Ok(dictionary) => mapping.dictionary = dictionary,
                        Err(DictionaryFallback::Unreachable) => return ContentsValue::Unreachable,
                        Err(DictionaryFallback::Unavailable) => {}
                    }
                }
            }
        }
    }
    if matches!(
        mapping.dictionary.extra_items,
        DictionaryExtraItems::ParamSpec(_) | DictionaryExtraItems::KeywordTail(_)
    ) {
        // A copied parameter bundle loses its identity when exposed, but its ordinary value
        // type still constrains what can be forwarded afterward.
        mapping.bound.get_or_insert(MappingBound {
            ty: bound_type,
            source,
        });
    }
    if paramspec.is_none()
        && !fresh_nested_allocation
        && (bounded
            || shared
            || value.is_some_and(|value| PlaceExpr::try_from_expr(value).is_some()))
    {
        if builtin_allocation
            && !shared
            && parent_preserved
            && place.as_symbol().is_none_or(Symbol::is_local)
        {
            // Ordinary per-key values remain available without proving key presence.
            mapping.generalize_presence(db, &env);
        } else {
            mapping.expose(db, &env);
        }
    }
    if !explicit_typed_dict && let Some(parameters) = kwargs_parameters {
        // Binding consumes keyword-capable named parameters before allocating **kwargs.
        // These exclusions are local contents facts; mutation and exposure can remove them.
        mapping.dictionary.items = parameters
            .args
            .iter()
            .chain(&parameters.kwonlyargs)
            .map(|parameter| DictionaryItem {
                name: parameter.parameter.name.id.clone(),
                ty: Type::Never,
                kind: DictionaryItemKind::Residual,
                source: parameter.parameter.name.range(),
            })
            .collect();
    }
    if matches!(
        definition.kind(db),
        DefinitionKind::Parameter(ParameterDefinitionNodeKind::VariadicKeywordParameter(_))
    ) && let Some(entry) = domain.and_then(|domain| domain.parameter_type(db, definition))
        && let Some(mut dictionary) = DictionaryItems::unpacked(db, &env, entry, source)
    {
        // Parameter coverage proves these initial fields. Keep the source writable bound so
        // an escape restores its field types instead of perpetuating the narrowed entry row.
        if let Some(tail) = domain.and_then(|domain| domain.keyword_tail(db)) {
            dictionary.extra_items = DictionaryExtraItems::KeywordTail(tail);
            dictionary.first_entry = DictionaryFirstEntry::Unknown;
        } else if let Some(component) = ParamSpecKeywords::from_type(db, entry) {
            dictionary.extra_items = DictionaryExtraItems::ParamSpec(component);
        }
        mapping.dictionary = dictionary;
        mapping.uses_residual_presence = false;
    }
    ContentsValue::Mapping(mapping)
}

/// Observe completion through the same reaching definitions as local dictionary reads.
/// Missing indexed history declines; no initializer snapshot can stand in for later effects.
fn frozen_export_contents<'db>(
    db: &'db dyn Db,
    file: ProgramFile<'db>,
    name: &str,
) -> Option<ContentsValue<'db>> {
    let scope = ty_python_core::global_scope(db, file);
    let index = semantic_index(db, file);
    let table = index.place_table(scope.file_scope_id(db));
    let symbol = table.symbol_id(name)?;
    let contents = table.contents_place(symbol.into())?;
    let use_def = index.use_def_map(scope.file_scope_id(db));
    let reachability = ReachabilityEvaluationCache::new(scope, use_def.reachability_constraints());
    let Contents { value, captured: _ } = from_bindings(
        db,
        scope,
        use_def.end_of_scope_bindings(contents),
        &reachability,
    );
    Some(value)
}

/// Observe an exported field when the holder's assignment completes module evaluation. Within
/// the indexed evaluation model, the fresh dictionary cannot change: later argument evaluation
/// is inert, the checked factory retains it unchanged, and the holder's first binding replaces
/// no earlier value whose destructor could run during assignment.
#[salsa::tracked(
    returns(clone),
    cycle_initial=|_, _, _, _, _| ContentsValue::Pending,
    cycle_fn=|db, cycle, previous: &ContentsValue<'db>, result: ContentsValue<'db>, file: ProgramFile<'db>, _, _| {
        result.cycle_normalized(db, &ProgramEnvironment::from_file(file), previous, cycle)
    },
    heap_size=get_size2::GetSize::get_heap_size,
)]
fn frozen_exported_field_contents<'db>(
    db: &'db dyn Db,
    file: ProgramFile<'db>,
    name: Name,
    field: Name,
) -> ContentsValue<'db> {
    let observed = (|| {
        if !db.provided_exports_are_frozen(file) {
            return None;
        }
        let module = parsed_module(db, file.python_file(db)).load(db);
        let ast::Stmt::Assign(assignment) = module.suite().last()? else {
            return None;
        };
        let [ast::Expr::Name(holder)] = assignment.targets.as_slice() else {
            return None;
        };
        if holder.id != name {
            return None;
        }
        let ast::Expr::Call(call) = assignment.value.as_ref() else {
            return None;
        };
        let mut keywords = call.arguments.keywords.iter();
        let keyword =
            keywords.find(|keyword| keyword.arg.as_ref().is_some_and(|name| name.id == field))?;
        if !keyword.value.is_dict_expr()
            || std::iter::once(keyword)
                .chain(keywords)
                .any(|keyword| keyword.arg.is_none() || !inert_field_argument(&keyword.value))
        {
            return None;
        }
        let index = semantic_index(db, file);
        let definition = index.try_definition(holder)?;
        let scope = definition.scope(db);
        if index
            .place_table(scope.file_scope_id(db))
            .symbol(definition.place(db).as_symbol()?)
            .is_reassigned()
        {
            return None;
        }
        let inference = StatementInference::Definition(
            definition,
            infer_definition_with_body_domain(db, definition, None),
        );
        if inference.is_provisional() {
            return Some(ContentsValue::Pending);
        }
        checked_keyword_field_factory(db, scope, call, &inference)?;
        Some(ContentsValue::from_literal(
            db,
            &ProgramEnvironment::from_scope(scope),
            scope,
            &keyword.value,
            &inference,
        ))
    })();
    observed.unwrap_or(ContentsValue::Unavailable)
}

/// Expressions that cannot call user code while evaluating a factory argument. Dictionary keys
/// are limited to string literals because hashing other objects can execute user code.
fn inert_field_argument(expression: &ast::Expr) -> bool {
    !any_over_expr(expression, |expression| match expression {
        ast::Expr::Name(_) | ast::Expr::List(_) | ast::Expr::Tuple(_) => false,
        ast::Expr::Dict(dictionary) => dictionary.items.iter().any(|item| {
            !item
                .key
                .as_ref()
                .is_some_and(ast::Expr::is_string_literal_expr)
        }),
        expression => !expression.is_literal_expr(),
    })
}

fn is_builtin_allocation<'db>(
    db: &'db dyn Db,
    value: &ast::Expr,
    inference: &DefinitionInference<'db>,
) -> bool {
    match value {
        ast::Expr::Dict(_) => true,
        ast::Expr::DictComp(_) => true,
        ast::Expr::If(conditional) => {
            is_builtin_allocation(db, &conditional.body, inference)
                && is_builtin_allocation(db, &conditional.orelse, inference)
        }
        ast::Expr::Call(call) => inference
            .try_expression_type(&call.func)
            .and_then(Type::as_class_literal)
            .is_some_and(|class| class.is_known(db, KnownClass::Dict)),
        _ => false,
    }
}

fn fresh_allocation<'db>(
    db: &'db dyn Db,
    definition: Definition<'db>,
    domain: Option<FunctionBodyDomain<'db>>,
) -> KeyPreservation {
    let scope = definition.scope(db);
    let module = parsed_module(db, scope.program_file(db).python_file(db)).load(db);
    let (owner, value) = match definition.kind(db) {
        DefinitionKind::DictKeyAssignment(assignment) => {
            (assignment.assignment(), Some(assignment.value(&module)))
        }
        kind => (definition, kind.value(&module)),
    };
    if let DefinitionKind::Assignment(assignment) = owner.kind(db)
        && !assignment.is_single_target(&module)
    {
        return KeyPreservation::Changed;
    }
    let Some(value) = value else {
        return KeyPreservation::Changed;
    };
    let inference = infer_definition_with_body_domain(db, owner, domain);
    if StatementInference::Definition(owner, inference).is_provisional() {
        return KeyPreservation::Pending;
    }
    if !inference.discards_dict_key_assignments() && is_builtin_allocation(db, value, inference) {
        KeyPreservation::Preserved
    } else {
        KeyPreservation::Changed
    }
}

/// The semantic transfer is shared by contents inference and saved-key predicate validity.
/// The index records syntax only; exact builtin identity is resolved with the operand's owner.
enum MappingTransfer<'db> {
    Result(ContentsValue<'db>),
    UnknownMutation,
    Keep {
        exposes_descendants: bool,
    },
    Expose,
    Set {
        key: Type<'db>,
        value: Type<'db>,
        source: TextRange,
    },
    SetDefault {
        key: Type<'db>,
        value: Type<'db>,
        source: TextRange,
        exposes_descendants: bool,
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
            Self::Keep {
                exposes_descendants: _,
            } => true,
            Self::Expose | Self::UnknownMutation => false,
            Self::Set {
                key,
                value: _,
                source: _,
            } => key.string_literal_value(db).is_some_and(|key| key != name),
            Self::SetDefault {
                key: _,
                value: _,
                source: _,
                exposes_descendants: _,
            } => true,
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

    fn preserves_confinement(&self) -> bool {
        match self {
            Self::Keep {
                exposes_descendants: _,
            } => true,
            Self::Set {
                key: _,
                value: _,
                source: _,
            } => true,
            Self::SetDefault {
                key: _,
                value: _,
                source: _,
                exposes_descendants: _,
            } => true,
            Self::Delete { key: _, source: _ } => true,
            Self::Clear => true,
            Self::Update {
                dictionary: _,
                retained,
            } => !retained,
            Self::Expose | Self::UnknownMutation => false,
            Self::Result(_) => false,
        }
    }

    fn for_descendants(self) -> Self {
        match self {
            Self::Keep {
                exposes_descendants,
            } => {
                if exposes_descendants {
                    Self::Expose
                } else {
                    Self::Keep {
                        exposes_descendants: false,
                    }
                }
            }
            Self::Result(result) => match result {
                ContentsValue::Pending => Self::Result(ContentsValue::Pending),
                ContentsValue::Unreachable => Self::Result(ContentsValue::Unreachable),
                ContentsValue::Unavailable => Self::Expose,
                ContentsValue::Mapping(_) => Self::Expose,
            },
            Self::Expose | Self::UnknownMutation => Self::Expose,
            Self::Set {
                key: _,
                value: _,
                source: _,
            } => Self::Expose,
            Self::SetDefault {
                key: _,
                value: _,
                source: _,
                exposes_descendants,
            } => {
                if exposes_descendants {
                    Self::Expose
                } else {
                    Self::Keep {
                        exposes_descendants: false,
                    }
                }
            }
            Self::Delete { key: _, source: _ } => Self::Expose,
            Self::Clear => Self::Expose,
            Self::Update {
                dictionary: _,
                retained: _,
            } => Self::Expose,
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
            return if matches!(self, Self::UnknownMutation) {
                ContentsValue::Unavailable
            } else {
                previous
            };
        };
        let preserved_tail = match (&self, mapping.dictionary.extra_items) {
            (Self::Delete { key, source: _ }, DictionaryExtraItems::KeywordTail(tail))
                if key
                    .string_literal_value(db)
                    .is_some_and(|name| tail.fixed.items(db).contains_key(name)) =>
            {
                Some(tail)
            }
            _ => None,
        };
        if preserved_tail.is_none()
            && !matches!(
                self,
                Self::Keep {
                    exposes_descendants: _
                }
            )
        {
            mapping.dictionary.extra_items = mapping.dictionary.extra_items.forget_paramspec();
        }
        match self {
            Self::Result(result) => result,
            Self::UnknownMutation => {
                if mapping
                    .bound
                    .is_some_and(|bound| ParamSpecKeywords::from_type(db, bound.ty).is_some())
                {
                    // Falling back to the receiver's declared type would restore the
                    // original keyword arguments after an unmodeled mutation.
                    mapping.expose(db, env);
                    previous
                } else {
                    ContentsValue::Unavailable
                }
            }
            Self::Keep {
                exposes_descendants: _,
            } => previous,
            Self::Expose => {
                mapping.expose(db, env);
                previous
            }
            Self::Set { key, value, source } => {
                mapping.set_item(db, env, key, value, source);
                previous
            }
            Self::SetDefault {
                key,
                value,
                source,
                exposes_descendants: _,
            } => {
                mapping.set_default(db, env, key, value, source);
                previous
            }
            Self::Delete { key, source } => {
                mapping.delete_item(db, env, key, source);
                if let Some(tail) = preserved_tail
                    && !mapping.dictionary.items.iter().any(|item| {
                        item.kind != DictionaryItemKind::Residual
                            && tail.fixed.items(db).contains_key(&item.name)
                    })
                {
                    mapping.dictionary.extra_items =
                        DictionaryExtraItems::ParamSpec(tail.component);
                }
                previous
            }
            Self::Clear => {
                mapping.dictionary = DictionaryItems {
                    first_entry: DictionaryFirstEntry::Empty,
                    items: Box::default(),
                    extra_items: if mapping.uses_residual_presence {
                        DictionaryExtraItems::Value(mapping.bound_value(db, env))
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
                if retained {
                    mapping.expose(db, env);
                } else if mapping.uses_residual_presence {
                    mapping.generalize_presence(db, env);
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
    domain: Option<FunctionBodyDomain<'db>>,
) -> ContentsValue<'db> {
    let scope = definition.scope(db);
    let env = ProgramEnvironment::from_scope(scope);
    mapping_transfer(db, definition, receiver, effect, domain).apply(db, &env, || {
        let index = semantic_index(db, scope.program_file(db));
        let use_def = index.use_def_map(scope.file_scope_id(db));
        let cache = ReachabilityEvaluationCache::new(scope, use_def.reachability_constraints())
            .with_body_domain(domain.filter(|domain| domain.scope(db) == scope));
        from_bindings(
            db,
            scope,
            use_def.bindings_at_definition(definition),
            &cache,
        )
        .value
    })
}

/// Apply declaration effects only to direct arguments matched by the ordinary call binder.
/// Other occurrences can expose the same container, including a nested argument or callee.
fn call_preserves_contents<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    call: &ast::ExprCall,
    receiver: &ast::Expr,
    expression_type: &dyn Fn(&ast::Expr) -> Option<Type<'db>>,
) -> bool {
    let Some(receiver) = PlaceExpr::try_from_expr(receiver) else {
        return false;
    };
    let mentions_receiver = |expression: &ast::Expr| {
        any_over_expr(expression, |expression| {
            PlaceExpr::try_from_expr(expression).as_ref() == Some(&receiver)
        })
    };
    let Some(callee @ Type::FunctionLiteral(_)) = expression_type(&call.func) else {
        return false;
    };
    if mentions_receiver(&call.func)
        || call.arguments.args.iter().any(ast::Expr::is_starred_expr)
        || call
            .arguments
            .keywords
            .iter()
            .any(|keyword| keyword.arg.is_none())
    {
        return false;
    }
    let bindings = callee.bindings(db, env);
    let Some(callable) = bindings.single_element() else {
        return false;
    };
    if callable.bound_type.is_some() {
        return false;
    }
    let [binding] = callable.overloads() else {
        return false;
    };
    let Some(declaration) = binding.signature.definition() else {
        return false;
    };
    if !binding.signature.parameters().iter().any(|parameter| {
        parameter.name().is_some_and(|name| {
            db.provided_parameter_preserves_contents(declaration, name.as_str())
        })
    }) {
        return false;
    }
    let arguments = CallArguments::from_arguments_typed(&call.arguments, |expression| {
        expression_type(expression).unwrap_or(Type::unknown())
    });
    let bindings = bindings.match_parameters(db, env, &arguments);
    let Some(callable) = bindings.single_element() else {
        return false;
    };
    let [binding] = callable.overloads() else {
        return false;
    };
    if !binding.errors().is_empty() || binding.argument_matches().len() != call.arguments.len() {
        return false;
    }
    let mut found = false;
    for (argument, matched) in call
        .arguments
        .iter_source_order()
        .zip(binding.argument_matches())
    {
        let expression = match argument {
            ast::ArgOrKeyword::Arg(expression) => expression,
            ast::ArgOrKeyword::Keyword(keyword) => &keyword.value,
        };
        if PlaceExpr::try_from_expr(expression).as_ref() != Some(&receiver) {
            if mentions_receiver(expression) {
                return false;
            }
            continue;
        }
        let [parameter] = matched.parameters.as_slice() else {
            return false;
        };
        let Some(name) = binding.signature.parameters()[parameter.index].name() else {
            return false;
        };
        if !matched.matched || !db.provided_parameter_preserves_contents(declaration, name.as_str())
        {
            return false;
        }
        found = true;
    }
    found
}

/// Aliases, stored values, and raw returns transfer the whole value, rather than observing
/// its current fields. Body domains do not yet project these whole-row read contracts.
pub(crate) fn has_value_exposure(db: &dyn Db, parameter: Definition<'_>) -> bool {
    let scope = parameter.scope(db);
    let index = semantic_index(db, scope.program_file(db));
    let use_def = index.use_def_map(scope.file_scope_id(db));
    let place = use_def
        .definitions_with_usage()
        .find_map(|(_, definition, _)| {
            let DefinitionKind::DictionaryContents(kind) = definition.kind(db) else {
                return None;
            };
            if let DictionaryContentsDefinitionKind::Initialize {
                definition: source,
                range: _,
            } = kind.as_ref()
                && *source == parameter
            {
                Some(definition.place(db))
            } else {
                None
            }
        });
    place.is_some_and(|place| {
        use_def.definitions_with_usage().any(|(_, definition, _)| {
            if definition.place(db) != place {
                return false;
            }
            let DefinitionKind::DictionaryContents(kind) = definition.kind(db) else {
                return false;
            };
            let DictionaryContentsDefinitionKind::Operation {
                receiver: _,
                effect,
            } = kind.as_ref()
            else {
                return false;
            };
            matches!(effect, DictionaryContentsEffect::Expose)
        })
    })
}

fn mapping_transfer<'db>(
    db: &'db dyn Db,
    definition: Definition<'db>,
    receiver: &ty_python_core::ast_node_ref::AstNodeRef<ast::Expr>,
    effect: &DictionaryContentsEffect<'db>,
    domain: Option<FunctionBodyDomain<'db>>,
) -> MappingTransfer<'db> {
    let scope = definition.scope(db);
    let env = ProgramEnvironment::from_scope(scope);
    let file = scope.program_file(db);
    let module = parsed_module(db, file.python_file(db)).load(db);
    let unavailable = || MappingTransfer::Result(ContentsValue::Unavailable);
    let pending = || MappingTransfer::Result(ContentsValue::Pending);
    // Nominal dict annotations can hide overridden methods and item operations. Apply this
    // admission here because saved-key proofs also inspect the transfer before applying it.
    if !matches!(
        effect,
        DictionaryContentsEffect::Expose
            | DictionaryContentsEffect::UnknownMutation
            | DictionaryContentsEffect::ProjectedCall(_)
    ) {
        let index = semantic_index(db, file);
        let use_def = index.use_def_map(scope.file_scope_id(db));
        let cache = ReachabilityEvaluationCache::new(scope, use_def.reachability_constraints())
            .with_body_domain(domain.filter(|domain| domain.scope(db) == scope));
        match from_bindings(
            db,
            scope,
            use_def.bindings_at_definition(definition),
            &cache,
        )
        .value
        {
            ContentsValue::Mapping(mapping) => {
                if !mapping.builtin {
                    return unavailable();
                }
            }
            result => return MappingTransfer::Result(result),
        }
    }
    match effect {
        DictionaryContentsEffect::Expose => MappingTransfer::Expose,
        DictionaryContentsEffect::UnknownMutation => MappingTransfer::UnknownMutation,
        DictionaryContentsEffect::ProjectedCall(original) => {
            let DefinitionKind::DictionaryContents(kind) = original.kind(db) else {
                return unavailable();
            };
            let DictionaryContentsDefinitionKind::Operation { receiver, effect } = kind.as_ref()
            else {
                return unavailable();
            };
            if !matches!(
                effect,
                DictionaryContentsEffect::Call {
                    call: _,
                    owner: _,
                    retained: _,
                }
            ) {
                return unavailable();
            }
            let transfer = mapping_transfer(db, *original, receiver, effect, domain);
            let index = semantic_index(db, file);
            let table = index.place_table(scope.file_scope_id(db));
            let Some(source) = PlaceExpr::try_from_expr(receiver.node(&module))
                .and_then(|place| table.place_id(&place))
            else {
                return unavailable();
            };
            let descendant = table
                .parents(table.place(definition.place(db)))
                .any(|place| place == source);
            if !descendant && !matches!(transfer, MappingTransfer::Result(_)) {
                // Reading a member mentions its ancestors syntactically. Recognized child
                // mappings do not constitute an observed escape of those ancestors, even
                // when the actual child escapes. Every completed Call transfer passed
                // builtin receiver admission above.
                // Ordinary analysis tracks observed escapes; parameters can still alias
                // through hidden backreferences.
                MappingTransfer::Keep {
                    exposes_descendants: false,
                }
            } else {
                transfer.for_descendants()
            }
        }
        DictionaryContentsEffect::AugmentItem(assignment) => {
            let DefinitionKind::AugmentedAssignment(node) = assignment.kind(db) else {
                return unavailable();
            };
            let Some(subscript) = node.node(&module).target.as_subscript_expr() else {
                return unavailable();
            };
            let inference = infer_definition_with_body_domain(db, *assignment, domain);
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
            let Some(inference) = operand_types(db, scope, owner.as_ref(), domain) else {
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
            let Some(inference) = operand_types(db, scope, owner.as_ref(), domain) else {
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
            let Some(inference) = operand_types(db, scope, owner.as_ref(), domain) else {
                return unavailable();
            };
            if inference.is_provisional() {
                return pending();
            }
            let call = call.node(&module);
            let discarded = match owner {
                Some(DictionaryContentsInferenceOwner::Statement(statement)) => {
                    if let ast::Stmt::Expr(statement) = statement.node(&module) {
                        statement
                            .value
                            .as_call_expr()
                            .is_some_and(|expression| std::ptr::eq(expression, call))
                    } else {
                        false
                    }
                }
                Some(DictionaryContentsInferenceOwner::Expression(_)) => false,
                None => false,
            };
            if let Some(Type::ClassLiteral(class)) = inference.try_expression_type(&call.func)
                && class.is_known(db, KnownClass::Dict)
            {
                return if *retained {
                    MappingTransfer::Expose
                } else {
                    MappingTransfer::Keep {
                        exposes_descendants: !discarded,
                    }
                };
            }
            let receiver = receiver.node(&module);
            // Positional unpacking of captured keywords passes their string keys, not the
            // dictionary. Reject calls that also mention the dictionary elsewhere.
            if let [ast::Expr::Starred(starred)] = call.arguments.args.as_ref()
                && call.arguments.keywords.is_empty()
                && let Some(place) = PlaceExpr::try_from_expr(receiver)
                && PlaceExpr::try_from_expr(&starred.value).as_ref() == Some(&place)
                && !any_over_expr(&call.func, |expression| {
                    PlaceExpr::try_from_expr(expression).as_ref() == Some(&place)
                })
                && inference
                    .try_expression_type(receiver)
                    .is_some_and(|ty| ParamSpecKeywords::from_type(db, ty).is_some())
            {
                return MappingTransfer::Keep {
                    exposes_descendants: false,
                };
            }
            // `reveal_type` returns its argument, so a retained result may expose the mapping.
            if let Some(Type::FunctionLiteral(function)) = inference.try_expression_type(&call.func)
                && (function.known(db) == Some(KnownFunction::Len)
                    || discarded && function.known(db) == Some(KnownFunction::RevealType))
                && let [argument] = call.arguments.args.as_ref()
                && call.arguments.keywords.is_empty()
                && PlaceExpr::try_from_expr(argument) == PlaceExpr::try_from_expr(receiver)
            {
                return MappingTransfer::Keep {
                    exposes_descendants: false,
                };
            }
            if call_preserves_contents(db, &env, call, receiver, &|expression| {
                inference.try_expression_type(expression)
            }) {
                return MappingTransfer::Keep {
                    exposes_descendants: true,
                };
            }
            let method = call.func.as_attribute_expr().filter(|attribute| {
                PlaceExpr::try_from_expr(&*attribute.value) == PlaceExpr::try_from_expr(receiver)
                    && inference.try_expression_type(receiver).is_some_and(|ty| {
                        has_explicit_typed_dict_items(db, ty)
                            || ParamSpecKeywords::from_type(db, ty).is_some()
                            || (ty.as_nominal_instance().is_some()
                                && super::has_dict_type(db, &env, ty))
                    })
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
                        MappingTransfer::Keep {
                            exposes_descendants: !discarded
                                && method.attr.as_str() != "__contains__",
                        }
                    }
                }
                "setdefault" => {
                    let (key, default) = match call.arguments.args.as_ref() {
                        [key] => (key, None),
                        [key, default] => (key, Some(default)),
                        _ => return unavailable(),
                    };
                    if !call.arguments.keywords.is_empty()
                        || call.arguments.args.iter().any(ast::Expr::is_starred_expr)
                    {
                        return unavailable();
                    }
                    if *retained
                        || call.arguments.args.iter().any(|argument| {
                            PlaceExpr::try_from_expr(argument) == PlaceExpr::try_from_expr(receiver)
                        })
                    {
                        return MappingTransfer::Expose;
                    }
                    let Some(key_ty) = inference.try_expression_type(key) else {
                        return unavailable();
                    };
                    let value = match default {
                        Some(default) => {
                            let Some(value) = inference.try_expression_type(default) else {
                                return unavailable();
                            };
                            value
                        }
                        None => Type::none(db, &env),
                    };
                    MappingTransfer::SetDefault {
                        key: key_ty,
                        value,
                        source: key.range(),
                        exposes_descendants: !discarded,
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
                                domain,
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
                        domain,
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
    domain: Option<FunctionBodyDomain<'db>>,
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
    Some(infer_statement_with_body_domain(db, statement, domain))
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
    domain: Option<FunctionBodyDomain<'db>>,
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
    if reads.multiple || loop_carried {
        return Some(KeyPreservation::Changed);
    }
    let name = read.slice.as_string_literal_expr()?.value.to_str();
    Some(saved_read_preserved(
        db,
        scope,
        &read.value,
        read.into(),
        current,
        name,
        domain,
    ))
}

fn saved_read_preserved<'db>(
    db: &'db dyn Db,
    scope: ScopeId<'db>,
    receiver: &ast::Expr,
    original: ast::ExprRef<'_>,
    current: &ast::Expr,
    name: &str,
    domain: Option<FunctionBodyDomain<'db>>,
) -> KeyPreservation {
    let index = semantic_index(db, scope.program_file(db));
    let table = index.place_table(scope.file_scope_id(db));
    let Some(place) = PlaceExpr::contents(receiver).and_then(|place| table.place_id(&place)) else {
        return KeyPreservation::Changed;
    };
    let Some(original_use) = index.try_expression_use_id(original) else {
        return KeyPreservation::Changed;
    };
    let Some(current_use) = index.try_expression_use_id(current.into()) else {
        return KeyPreservation::Changed;
    };
    let use_def = index.use_def_map(scope.file_scope_id(db));
    let Some(original) = use_def.multi_bindings_at_use(original_use, place) else {
        return KeyPreservation::Changed;
    };
    let Some(current) = use_def.multi_bindings_at_use(current_use, place) else {
        return KeyPreservation::Changed;
    };
    let anchors: Vec<_> = original.map(|binding| binding.binding).collect();
    check_contents_history(
        db,
        scope,
        current.map(|binding| binding.binding).collect(),
        KeyHistoryOrigin::SavedRead {
            anchors: &anchors,
            name,
        },
        domain,
    )
}

#[derive(Clone, Copy)]
enum KeyHistoryOrigin<'a, 'db> {
    SavedRead {
        anchors: &'a [DefinitionState<'db>],
        name: &'a str,
    },
    /// Ordinary member seeds may start at a parameter, but not after a known escape.
    UnexposedParent,
    /// A retained source must originate in a fresh local allocation, never a parameter.
    FreshSource,
    /// All paths must reach this exact retaining call without changing the whole mapping.
    RetainedCall(ast::NodeIndex),
}

/// A member store does not create a new containing object. Read the receiver's snapshot before
/// the store, so a new child cannot hide an earlier escape of its parent.
fn parent_allows_seed<'db>(
    db: &'db dyn Db,
    owner: Definition<'db>,
    domain: Option<FunctionBodyDomain<'db>>,
) -> KeyPreservation {
    let owner = match owner.kind(db) {
        DefinitionKind::DictKeyAssignment(assignment) => assignment.assignment(),
        _ => owner,
    };
    let scope = owner.scope(db);
    let module = parsed_module(db, scope.program_file(db).python_file(db)).load(db);
    let target = match owner.kind(db) {
        DefinitionKind::Assignment(assignment) => assignment.target(&module),
        DefinitionKind::AnnotatedAssignment(assignment) => assignment.target(&module),
        _ => return KeyPreservation::Changed,
    };
    let receiver = match target {
        ast::Expr::Name(_) => return KeyPreservation::Preserved,
        ast::Expr::Attribute(attribute) => attribute.value.as_ref(),
        ast::Expr::Subscript(subscript) => subscript.value.as_ref(),
        _ => return KeyPreservation::Changed,
    };
    let index = semantic_index(db, scope.program_file(db));
    let table = index.place_table(scope.file_scope_id(db));
    let Some(place) = PlaceExpr::contents(receiver).and_then(|place| table.place_id(&place)) else {
        return KeyPreservation::Changed;
    };
    let Some(use_id) = index.try_expression_use_id(receiver.into()) else {
        return KeyPreservation::Changed;
    };
    let use_def = index.use_def_map(scope.file_scope_id(db));
    let Some(bindings) = use_def.multi_bindings_at_use(use_id, place) else {
        return KeyPreservation::Changed;
    };
    check_contents_history(
        db,
        scope,
        bindings.map(|binding| binding.binding).collect(),
        KeyHistoryOrigin::UnexposedParent,
        domain,
    )
}

fn check_contents_history<'db>(
    db: &'db dyn Db,
    scope: ScopeId<'db>,
    mut pending: Vec<DefinitionState<'db>>,
    origin: KeyHistoryOrigin<'_, 'db>,
    domain: Option<FunctionBodyDomain<'db>>,
) -> KeyPreservation {
    let index = semantic_index(db, scope.program_file(db));
    let use_def = index.use_def_map(scope.file_scope_id(db));
    let mut visited = FxHashSet::default();
    let mut provisional = false;
    while let Some(binding) = pending.pop() {
        if let KeyHistoryOrigin::SavedRead { anchors, name: _ } = origin
            && anchors.contains(&binding)
        {
            continue;
        }
        let Some(definition) = binding.definition() else {
            return KeyPreservation::Changed;
        };
        // Ordinary operation predecessors are source ordered. LoopHeader is the only back
        // edge and is rejected below; deduplication therefore only skips shared suffixes.
        if !visited.insert(definition) {
            continue;
        }
        let DefinitionKind::DictionaryContents(contents) = definition.kind(db) else {
            return KeyPreservation::Changed;
        };
        match contents.as_ref() {
            DictionaryContentsDefinitionKind::Initialize {
                definition,
                range: _,
            } => {
                let allocation = match origin {
                    KeyHistoryOrigin::SavedRead {
                        anchors: _,
                        name: _,
                    } => {
                        return KeyPreservation::Changed;
                    }
                    KeyHistoryOrigin::RetainedCall(_) => return KeyPreservation::Changed,
                    KeyHistoryOrigin::UnexposedParent | KeyHistoryOrigin::FreshSource => {
                        if matches!(origin, KeyHistoryOrigin::UnexposedParent)
                            && definition.kind(db).is_parameter_def()
                        {
                            continue;
                        }
                        match fresh_allocation(db, *definition, domain) {
                            KeyPreservation::Preserved => {
                                parent_allows_seed(db, *definition, domain)
                            }
                            result => result,
                        }
                    }
                };
                match allocation {
                    KeyPreservation::Preserved => {}
                    KeyPreservation::Pending => provisional = true,
                    KeyPreservation::Changed => return KeyPreservation::Changed,
                }
                continue;
            }
            DictionaryContentsDefinitionKind::Operation { receiver, effect } => {
                if let KeyHistoryOrigin::RetainedCall(anchor) = origin
                    && let DictionaryContentsEffect::Call {
                        call,
                        owner: _,
                        retained: _,
                    } = effect
                    && call.index() == anchor
                {
                    continue;
                }
                let transfer = mapping_transfer(db, definition, receiver, effect, domain);
                if matches!(transfer, MappingTransfer::Result(ContentsValue::Pending)) {
                    provisional = true;
                    continue;
                }
                let preserved = match origin {
                    KeyHistoryOrigin::SavedRead { anchors: _, name } => {
                        transfer.preserves_key(db, name)
                    }
                    KeyHistoryOrigin::UnexposedParent => transfer.preserves_confinement(),
                    KeyHistoryOrigin::FreshSource | KeyHistoryOrigin::RetainedCall(_) => {
                        matches!(transfer, MappingTransfer::Keep { .. })
                    }
                };
                if !preserved {
                    return KeyPreservation::Changed;
                }
            }
            DictionaryContentsDefinitionKind::Capture {
                nested_scope: _,
                name: _,
                range: _,
                execution,
                resolution: _,
            } => {
                if !matches!(
                    origin,
                    KeyHistoryOrigin::SavedRead {
                        anchors: _,
                        name: _
                    }
                ) {
                    return KeyPreservation::Changed;
                }
                if *execution == NestedBindingExecution::Lazy {
                    continue;
                }
            }
            // Modifier-only bindings do not change a key's value, and do not stand in for
            // the ordinary loop header, which the traversal rejects above.
            DictionaryContentsDefinitionKind::LoopCapture {
                header: _,
                range: _,
            } => {
                if !matches!(
                    origin,
                    KeyHistoryOrigin::SavedRead {
                        anchors: _,
                        name: _
                    }
                ) {
                    return KeyPreservation::Changed;
                }
                continue;
            }
        }
        pending.extend(
            use_def
                .bindings_at_definition(definition)
                .map(|binding| binding.binding),
        );
    }
    if provisional {
        KeyPreservation::Pending
    } else {
        KeyPreservation::Preserved
    }
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
            DefinitionState::Defined(definition) => {
                definition_contents_in_domain(db, definition, reachability.body_domain()).narrow(
                    db,
                    scope,
                    definition,
                    &binding.narrowing_constraint,
                    reachability.body_domain(),
                )
            }
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

pub(crate) fn at_snapshot<'db>(
    db: &'db dyn Db,
    scope: ScopeId<'db>,
    expression: &ast::Expr,
    snapshot: ast::ExprRef<'_>,
    argument_type: Type<'db>,
    reachability: &ReachabilityEvaluationCache<'db>,
) -> DictionaryObservation<'db> {
    match snapshot_contents(db, scope, expression, snapshot, argument_type, reachability) {
        ContentsValue::Mapping(mapping) => Ok(mapping.dictionary),
        ContentsValue::Unreachable => Err(DictionaryFallback::Unreachable),
        ContentsValue::Pending => Err(DictionaryFallback::Unavailable),
        ContentsValue::Unavailable => Err(DictionaryFallback::Unavailable),
    }
}

/// Observe the dictionary stored under a key of an unpacked call argument after all arguments
/// have been evaluated. The index records the child at this call only while the receiver still
/// identifies the value read for unpacking.
pub(super) fn unpacked_keyword<'db>(
    db: &'db dyn Db,
    scope: ScopeId<'db>,
    expression: &ast::Expr,
    call: &ast::ExprCall,
    name: &str,
    reachability: &ReachabilityEvaluationCache<'db>,
) -> Option<DictionaryItems<'db>> {
    let index = semantic_index(db, scope.program_file(db));
    let table = index.place_table(scope.file_scope_id(db));
    let root = table.place_id(&PlaceExpr::contents(expression)?)?;
    let key = table.contents_key(root, name)?;
    let child = table.contents_place(key)?;
    let use_id = index.try_expression_use_id(call.into())?;
    let bindings = index
        .use_def_map(scope.file_scope_id(db))
        .multi_bindings_at_use(use_id, child)?;
    let Contents {
        value: ContentsValue::Mapping(mut mapping),
        captured: false,
    } = from_bindings(db, scope, bindings, reachability)
    else {
        return None;
    };
    mapping.localize(scope.program_file(db), expression.range());
    Some(mapping.dictionary)
}

/// Recover a first field observation from a factory's pre-retention snapshot or from a frozen
/// exported holder. No alias is installed in the contents graph: later field effects, uncertain
/// source history, or another binding all fall back to ordinary inference.
fn retained_field_contents<'db>(
    db: &'db dyn Db,
    scope: ScopeId<'db>,
    expression: &ast::Expr,
    snapshot: ast::ExprRef<'_>,
    reachability: &ReachabilityEvaluationCache<'db>,
) -> Option<ContentsValue<'db>> {
    let ast::Expr::Attribute(attribute) = expression else {
        return None;
    };
    let ast::Expr::Name(holder) = attribute.value.as_ref() else {
        return None;
    };
    let file = scope.program_file(db);
    let index = semantic_index(db, file);
    let table = index.place_table(scope.file_scope_id(db));
    let holder_symbol = table.symbol(table.symbol_id(holder.id.as_str())?);
    if !holder_symbol.is_local() || holder_symbol.is_reassigned() {
        return None;
    }
    let use_def = index.use_def_map(scope.file_scope_id(db));
    let holder_use = index.try_expression_use_id(attribute.value.as_ref().into())?;
    let mut bindings = use_def.bindings_at_use(holder_use);
    let definition = bindings.next()?.binding.definition()?;
    if bindings.next().is_some() || definition.scope(db) != scope {
        return None;
    }
    if matches!(definition.kind(db), DefinitionKind::ProvidedBinding(_))
        && let ProvidedBindingValue::Export {
            file,
            name,
            value: None,
        } = db.provided_binding(definition).value
    {
        let result = frozen_exported_field_contents(db, file, name, attribute.attr.id.clone());
        return match result {
            ContentsValue::Unavailable => None,
            result => Some(result),
        };
    }
    let module = parsed_module(db, file.python_file(db)).load(db);
    let (target, value) = match definition.kind(db) {
        DefinitionKind::Assignment(assignment) if assignment.is_single_target(&module) => {
            (assignment.target(&module), assignment.value(&module))
        }
        DefinitionKind::AnnotatedAssignment(assignment) => {
            (assignment.target(&module), assignment.value(&module)?)
        }
        _ => return None,
    };
    let field_place = table.place_id(&PlaceExpr::contents(expression)?)?;
    let target_use = index.try_expression_use_id(target.into())?;
    let current_use = index.try_expression_use_id(snapshot)?;
    let field_value = table.place_id(&PlaceExpr::try_from_expr(expression)?)?;
    let field_use = index.try_expression_use_id(expression.into())?;
    for (place, mut current) in [
        (
            field_place,
            use_def.multi_bindings_at_use(current_use, field_place)?,
        ),
        (field_value, use_def.bindings_at_use(field_use)),
    ] {
        let mut initial = use_def.multi_bindings_at_use(target_use, place)?;
        let initial_binding = initial.next()?;
        if initial_binding.binding != DefinitionState::Deleted
            || initial.next().is_some()
            || current.next()?.binding_order != initial_binding.binding_order
            || current.next().is_some()
        {
            return None;
        }
    }
    let ast::Expr::Call(call) = value else {
        return None;
    };
    let keyword = call.arguments.keywords.iter().find(|keyword| {
        keyword
            .arg
            .as_ref()
            .is_some_and(|name| name.as_str() == attribute.attr.as_str())
    })?;
    let source = retained_keyword_source(table, call, keyword)?;
    let domain = reachability.body_domain();
    let inference = StatementInference::Definition(
        definition,
        infer_definition_with_body_domain(db, definition, domain),
    );
    if inference.is_provisional() {
        return Some(ContentsValue::Pending);
    }
    checked_keyword_field_factory(db, scope, call, &inference)?;

    let source_contents = table.place_id(&PlaceExpr::contents(source)?)?;
    let call_use = index.try_expression_use_id(call.into())?;
    let before = use_def.multi_bindings_at_use(call_use, source_contents)?;
    let current_use = index.try_expression_use_id(snapshot)?;
    let after = use_def.multi_bindings_at_use(current_use, source_contents)?;
    for (bindings, origin) in [
        (before, KeyHistoryOrigin::FreshSource),
        (
            after,
            KeyHistoryOrigin::RetainedCall(call.node_index().load()),
        ),
    ] {
        match check_contents_history(
            db,
            scope,
            bindings.map(|binding| binding.binding).collect(),
            origin,
            domain,
        ) {
            KeyPreservation::Preserved => {}
            KeyPreservation::Pending => return Some(ContentsValue::Pending),
            KeyPreservation::Changed => return None,
        }
    }
    Some(snapshot_contents(
        db,
        scope,
        source,
        call.into(),
        inference.try_expression_type(source)?,
        reachability,
    ))
}

fn retained_keyword_source<'ast>(
    table: &PlaceTable,
    call: &'ast ast::ExprCall,
    keyword: &'ast ast::Keyword,
) -> Option<&'ast ast::Expr> {
    // No unpacking or repeated/nested occurrences of the retained source are admitted.
    if !call.arguments.args.is_empty()
        || call
            .arguments
            .keywords
            .iter()
            .any(|keyword| keyword.arg.is_none())
    {
        return None;
    }
    let source = &keyword.value;
    let ast::Expr::Name(name) = source else {
        return None;
    };
    let symbol = table.symbol(table.symbol_id(name.id.as_str())?);
    if !symbol.is_local() || symbol.is_reassigned() {
        return None;
    }
    let source_place = PlaceExpr::from_expr_name(name);
    let mentions_source = |expression: &ast::Expr| {
        any_over_expr(expression, |expression| {
            PlaceExpr::try_from_expr(expression).as_ref() == Some(&source_place)
        })
    };
    if mentions_source(&call.func)
        || call
            .arguments
            .keywords
            .iter()
            .filter(|keyword| mentions_source(&keyword.value))
            .count()
            != 1
    {
        return None;
    }
    Some(source)
}

fn checked_keyword_field_factory<'db>(
    db: &'db dyn Db,
    scope: ScopeId<'db>,
    call: &ast::ExprCall,
    inference: &StatementInference<'db>,
) -> Option<Definition<'db>> {
    let callee @ Type::FunctionLiteral(_) = inference.try_expression_type(&call.func)? else {
        return None;
    };
    let env = ProgramEnvironment::from_scope(scope);
    let bindings = callee.bindings(db, &env);
    let callable = bindings.single_element()?;
    if callable.bound_type.is_some() {
        return None;
    }
    let [binding] = callable.overloads() else {
        return None;
    };
    let declaration = binding.signature.definition()?;
    if !db.provided_keyword_field_factory(declaration) {
        return None;
    }
    let arguments = CallArguments::from_arguments_typed(&call.arguments, |expression| {
        inference
            .try_expression_type(expression)
            .unwrap_or(Type::unknown())
    });
    let matched = bindings.match_parameters(db, &env, &arguments);
    let [binding] = matched.single_element()?.overloads() else {
        return None;
    };
    binding.errors().is_empty().then_some(declaration)
}

/// Recover a retained dictionary only for the next checked call. The ordinary contents state
/// remains exposed: the returned holder is another path to the mutable dictionary.
pub(crate) fn retained_argument_items<'db>(
    db: &'db dyn Db,
    scope: ScopeId<'db>,
    observed: &ast::ExprCall,
    expression: &ast::Expr,
    reachability: &ReachabilityEvaluationCache<'db>,
) -> Option<DictionaryItems<'db>> {
    let ast::Expr::Name(name) = expression else {
        return None;
    };
    let file = scope.program_file(db);
    let index = semantic_index(db, file);
    let table = index.place_table(scope.file_scope_id(db));
    let contents_place = table.place_id(&PlaceExpr::contents(expression)?)?;
    let use_id = index.try_expression_use_id(expression.into())?;
    let use_def = index.use_def_map(scope.file_scope_id(db));
    let mut source_bindings = use_def.bindings_at_use(use_id);
    let source_definition = source_bindings.next()?.binding.definition()?;
    if source_bindings.next().is_some() || source_definition.scope(db) != scope {
        return None;
    }
    let mut bindings = use_def.multi_bindings_at_use(use_id, contents_place)?;
    let effect_definition = bindings.next()?.binding.definition()?;
    if bindings.next().is_some() || effect_definition.scope(db) != scope {
        return None;
    }
    let DefinitionKind::DictionaryContents(contents) = effect_definition.kind(db) else {
        return None;
    };
    let DictionaryContentsDefinitionKind::Operation {
        receiver,
        effect:
            DictionaryContentsEffect::Call {
                call,
                owner: Some(owner @ DictionaryContentsInferenceOwner::Statement(statement)),
                retained: true,
            },
    } = contents.as_ref()
    else {
        return None;
    };
    let module = parsed_module(db, file.python_file(db)).load(db);
    let statement = statement.node(&module);
    let ast::Stmt::Assign(retaining_assignment) = statement else {
        return None;
    };
    let [ast::Expr::Name(holder)] = retaining_assignment.targets.as_slice() else {
        return None;
    };
    let retaining_call = call.node(&module);
    if !retaining_assignment
        .value
        .as_call_expr()
        .is_some_and(|value| std::ptr::eq(value, retaining_call))
    {
        return None;
    }
    let body = match scope.node(db) {
        NodeWithScopeKind::Module => module.suite(),
        NodeWithScopeKind::Function(function) => &function.node(&module).body,
        _ => return None,
    };
    let end = body.partition_point(|statement| statement.start() < observed.start());
    let [previous, ast::Stmt::Assign(observing_assignment)] = body.get(end.checked_sub(2)?..end)?
    else {
        return None;
    };
    if !std::ptr::eq(previous, statement)
        || !matches!(
            observing_assignment.targets.as_slice(),
            [ast::Expr::Name(_)]
        )
        || !observing_assignment
            .value
            .as_call_expr()
            .is_some_and(|value| std::ptr::eq(value, observed))
    {
        return None;
    }
    let holder_symbol = table.symbol(table.symbol_id(holder.id.as_str())?);
    if !holder_symbol.is_local() || holder_symbol.is_reassigned() {
        return None;
    }
    let keyword = retaining_call.arguments.keywords.iter().find(|keyword| {
        keyword
            .value
            .as_name_expr()
            .is_some_and(|value| value.id == name.id)
    })?;
    let source = retained_keyword_source(table, retaining_call, keyword)?;
    if !std::ptr::eq(receiver.node(&module), source)
        || !inert_retained_argument_call(
            observed,
            name,
            holder,
            retaining_call,
            keyword.arg.as_ref()?.as_str(),
        )
    {
        return None;
    }
    let domain = reachability.body_domain();
    let inference = operand_types(db, scope, Some(owner), domain)?;
    if inference.is_provisional() {
        return None;
    }
    checked_keyword_field_factory(db, scope, retaining_call, &inference)?;
    if !matches!(
        check_contents_history(
            db,
            scope,
            use_def
                .bindings_at_definition(effect_definition)
                .map(|binding| binding.binding)
                .collect(),
            KeyHistoryOrigin::FreshSource,
            domain,
        ),
        KeyPreservation::Preserved
    ) {
        return None;
    }
    let Contents {
        value: ContentsValue::Mapping(mut mapping),
        captured: false,
    } = from_bindings(
        db,
        scope,
        use_def.bindings_at_definition(effect_definition),
        reachability,
    )
    else {
        return None;
    };
    if !mapping.dictionary.is_complete() {
        return None;
    }
    mapping.localize(file, expression.range());
    Some(mapping.dictionary)
}

fn inert_retained_argument_call(
    observed: &ast::ExprCall,
    source: &ast::ExprName,
    holder: &ast::ExprName,
    retaining_call: &ast::ExprCall,
    retained_field: &str,
) -> bool {
    let Some(callee) = observed.func.as_name_expr() else {
        return false;
    };
    if callee.id == holder.id || callee.id == source.id {
        return false;
    }
    let mut found = false;
    let inert = observed.arguments.iter_source_order().all(|argument| {
        let expression = match argument {
            ast::ArgOrKeyword::Arg(expression) => expression,
            ast::ArgOrKeyword::Keyword(keyword) if keyword.arg.is_some() => &keyword.value,
            ast::ArgOrKeyword::Keyword(_) => return false,
        };
        match expression {
            ast::Expr::Name(name) if std::ptr::eq(name, source) => {
                found = true;
                true
            }
            ast::Expr::Name(name) => name.id != holder.id && name.id != source.id,
            ast::Expr::Attribute(attribute) => {
                attribute
                    .value
                    .as_name_expr()
                    .is_some_and(|name| name.id == holder.id)
                    && attribute.attr.as_str() != retained_field
                    && retaining_call.arguments.keywords.iter().any(|keyword| {
                        keyword
                            .arg
                            .as_ref()
                            .is_some_and(|name| name.as_str() == attribute.attr.as_str())
                    })
            }
            expression => expression.is_literal_expr(),
        }
    });
    inert && found
}

pub(super) fn snapshot_contents<'db>(
    db: &'db dyn Db,
    scope: ScopeId<'db>,
    expression: &ast::Expr,
    snapshot: ast::ExprRef<'_>,
    argument_type: Type<'db>,
    reachability: &ReachabilityEvaluationCache<'db>,
) -> ContentsValue<'db> {
    let observed = (|| {
        let explicit_typed_dict = has_explicit_typed_dict_items(db, argument_type);
        if !explicit_typed_dict
            && ParamSpecKeywords::from_type(db, argument_type).is_none()
            && !super::has_dict_type(db, &ProgramEnvironment::from_scope(scope), argument_type)
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
        // A nested scope can replace a captured binding with another dictionary. Its
        // alternative type survives ordinary inference but has no local contents seed.
        if !explicit_typed_dict
            && argument_type.as_nominal_instance().is_none()
            && super::records::for_binding(db, scope, expression).is_none()
        {
            let receiver = PlaceExpr::try_from_expr(expression)?;
            let receiver = index
                .place_table(scope.file_scope_id(db))
                .place_id(&receiver)?;
            if use_def.reachable_bindings(receiver).any(|binding| {
                let DefinitionState::Defined(definition) = binding.binding else {
                    return false;
                };
                matches!(definition.kind(db), DefinitionKind::NestedBindings(_))
            }) {
                return None;
            }
        }
        let bindings = use_def.multi_bindings_at_use(use_id, contents_place)?;
        if let ast::Expr::Attribute(attribute) = expression
            && attribute.value.is_name_expr()
            && let Some(retained) =
                retained_field_contents(db, scope, expression, snapshot, reachability)
        {
            return Some(retained);
        }
        let Contents { value, captured: _ } = from_bindings(db, scope, bindings, reachability);
        Some(value)
    })();
    match observed {
        Some(ContentsValue::Mapping(mut mapping)) => {
            mapping.localize(scope.program_file(db), expression.range());
            ContentsValue::Mapping(mapping)
        }
        Some(contents) => contents,
        None => ContentsValue::Unavailable,
    }
}

pub(crate) fn has_explicit_typed_dict_items(db: &dyn Db, ty: Type<'_>) -> bool {
    ty.resolve_type_alias(db)
        .as_typed_dict()
        .is_some_and(|typed_dict| !typed_dict.openness(db).is_implicitly_open())
}
