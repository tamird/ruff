//! Syntax-only discovery of places whose mapping contents can be observed.

use ruff_python_ast as ast;
use ruff_python_ast::visitor::{Visitor, walk_expr, walk_stmt};
use ruff_text_size::Ranged;
use rustc_hash::FxHashMap;
use smallvec::SmallVec;

use crate::SourceExclusions;
use crate::ast_node_ref::AstNodeRef;
use crate::definition::{
    Definition, DefinitionKind, DefinitionNodeKey, DictionaryContentsDefinitionKind,
    DictionaryContentsEffect, DictionaryContentsInferenceOwner, NestedBindingExecution,
};
use crate::member::MemberExprBuilder;
use crate::place::{
    DictionaryFirstValueRead, PlaceExpr, PlaceExprRef, PlaceTableBuilder, ScopedPlaceId,
};
use crate::scope::NodeWithScopeRef;

use super::{SemanticIndexBuilder, UnresolvedCapture};
use crate::use_def::{
    FutureDefinitions, ImportedQualifierAction, LiveBinding, PreviousDefinitions,
};

impl<'db, 'ast> SemanticIndexBuilder<'db, 'ast> {
    pub(super) fn first_value_sources(&self, expression: &ast::Expr) -> Vec<&'ast ast::Expr> {
        struct Sources<'a, 'db, 'ast> {
            builder: &'a SemanticIndexBuilder<'db, 'ast>,
            receivers: Vec<&'ast ast::Expr>,
        }
        impl Visitor<'_> for Sources<'_, '_, '_> {
            fn visit_expr(&mut self, expression: &ast::Expr) {
                if expression.is_name_expr()
                    && let Some(use_id) = self.builder.current_ast_ids().try_use_id(expression)
                {
                    let use_def = self.builder.current_use_def_map();
                    let mut bindings = use_def.bindings_at_use(use_id);
                    if let Some(first) = bindings.next()
                        && bindings.all(|binding| binding.binding() == first.binding())
                        && let Some(definition) = use_def.definition(first.binding()).definition()
                        && let Some(subscript) = DictionaryFirstValueRead::assigned_subscript(
                            definition.kind(self.builder.db),
                            self.builder.module,
                        )
                        && let Some(read) = DictionaryFirstValueRead::from_subscript(subscript)
                    {
                        self.receivers.push(read.receiver);
                    }
                }
                walk_expr(self, expression);
            }
        }
        let mut sources = Sources {
            builder: self,
            receivers: Vec::new(),
        };
        sources.visit_expr(expression);
        sources.receivers
    }

    pub(super) fn record_contents_loop_capture(
        &mut self,
        place: ScopedPlaceId,
        header: Definition<'db>,
    ) {
        let crate::place::PlaceExprRef::Member(member) = self.current_place_table().place(place)
        else {
            return;
        };
        if !member.is_contents() {
            return;
        }
        let range = header.kind(self.db).target_range(self.module);
        let definition = Definition::new(
            self.db,
            self.current_scope_id(),
            place,
            DefinitionKind::DictionaryContents(Box::new(
                DictionaryContentsDefinitionKind::LoopCapture { header, range },
            )),
            false,
        );
        self.current_use_def_map_mut().record_binding(
            place,
            definition,
            PreviousDefinitions::AreKept,
            FutureDefinitions::DontShadowThisOne,
            ImportedQualifierAction::Preserve,
        );
    }

    fn register_receiver_place(&mut self, receiver: &'ast ast::Expr) {
        match receiver {
            ast::Expr::Attribute(attribute) => self.register_contents_place(&attribute.value),
            ast::Expr::Subscript(subscript) => self.register_contents_place(&subscript.value),
            ast::Expr::Named(named) => self.register_contents_place(&named.target),
            _ => {}
        }
        if !receiver.is_name_expr()
            && let Some(place) = PlaceExpr::try_from_expr(receiver)
        {
            self.add_place(place);
        }
    }

    pub(super) fn register_contents_place(&mut self, receiver: &'ast ast::Expr) {
        let Some(contents) = PlaceExpr::contents(receiver) else {
            return;
        };
        // Member parents precede their contents; root symbols keep the ordinary traversal's
        // order. The place table connects those roots when they are first visited.
        self.register_receiver_place(receiver);
        self.add_place(contents);
    }

    pub(super) fn contents_place(&self, receiver: &ast::Expr) -> Option<ScopedPlaceId> {
        let contents = PlaceExpr::contents(receiver)?;
        self.current_place_table().place_id((&contents).into())
    }

    pub(super) fn record_contents_effect(
        &mut self,
        receiver: &'ast ast::Expr,
        effect: DictionaryContentsEffect<'db>,
    ) {
        let Some(place) = self.contents_place(receiver) else {
            return;
        };
        let _ = self.record_contents_effect_at(place, receiver, effect);
    }

    fn record_contents_effect_at(
        &mut self,
        place: ScopedPlaceId,
        receiver: &'ast ast::Expr,
        mut effect: DictionaryContentsEffect<'db>,
    ) -> Option<Definition<'db>> {
        let owner = match &mut effect {
            DictionaryContentsEffect::SetItem {
                subscript: _,
                owner,
            } => Some(owner),
            DictionaryContentsEffect::DeleteItem {
                subscript: _,
                owner,
            } => Some(owner),
            DictionaryContentsEffect::Call {
                call: _,
                owner,
                retained: _,
            } => Some(owner),
            DictionaryContentsEffect::AugmentItem(_) => None,
            DictionaryContentsEffect::ProjectedCall(_) => None,
            DictionaryContentsEffect::UnknownMutation => None,
            DictionaryContentsEffect::Expose => None,
        };
        if let Some(owner) = owner {
            let statement = self.current_statement_mut()?;
            let statement = statement.node;
            *owner = self.contents_inference_owner(statement, receiver);
            if matches!(owner, Some(DictionaryContentsInferenceOwner::Statement(_)))
                && let Some(statement) = self.current_statement_mut()
            {
                statement.contains_contents = true;
            }
        }
        let kind = DefinitionKind::DictionaryContents(Box::new(
            DictionaryContentsDefinitionKind::Operation {
                receiver: AstNodeRef::new(self.module, receiver),
                effect,
            },
        ));
        let key = DefinitionNodeKey::from_node_ref(receiver.into());
        let (definition, _) = self.create_definition_with_kind(place, key, kind);
        self.record_definition(place, definition, None);
        Some(definition)
    }

    fn record_nested_contents_effect(
        &mut self,
        receiver: &'ast ast::Expr,
        effect: &DictionaryContentsEffect<'db>,
        direct_receiver: Option<&ast::Expr>,
    ) {
        for place in nested_contents_places(self.current_place_table(), receiver, direct_receiver) {
            let _ = self.record_contents_effect_at(place, receiver, effect.clone());
        }
    }

    pub(super) fn record_contents_capture(&mut self, capture: &UnresolvedCapture) {
        let places: Vec<_> = self
            .current_place_table()
            .associated_symbol_members_by_name(&capture.name)
            .iter()
            .copied()
            .filter(|place| self.current_place_table().member(*place).is_contents())
            .collect();
        let Some(node) = self.scopes[capture.nested_scope].node().node_index() else {
            return;
        };
        let range = self.module.get_by_index(node).range();
        for place in places {
            let definition = Definition::new(
                self.db,
                self.current_scope_id(),
                place.into(),
                DefinitionKind::DictionaryContents(Box::new(
                    DictionaryContentsDefinitionKind::Capture {
                        nested_scope: capture.nested_scope,
                        name: capture.name.clone(),
                        range,
                        execution: if capture.laziness.is_lazy() {
                            NestedBindingExecution::Lazy
                        } else {
                            NestedBindingExecution::Eager
                        },
                        resolution: capture.resolution,
                    },
                )),
                false,
            );
            self.current_use_def_map_mut().record_binding(
                place.into(),
                definition,
                if capture.laziness.is_lazy() {
                    PreviousDefinitions::AreKept
                } else {
                    PreviousDefinitions::AreShadowed
                },
                if capture.laziness.is_lazy() {
                    FutureDefinitions::DontShadowThisOne
                } else {
                    FutureDefinitions::ShadowThisOne
                },
                ImportedQualifierAction::Preserve,
            );
        }
    }

    fn contents_inference_owner(
        &self,
        statement: &'ast ast::Stmt,
        receiver: &'ast ast::Expr,
    ) -> Option<DictionaryContentsInferenceOwner> {
        let contains_receiver = |root: &&ast::Expr| root.range().contains_range(receiver.range());
        let expression = match statement {
            ast::Stmt::If(statement) => std::iter::once(statement.test.as_ref())
                .chain(
                    statement
                        .elif_else_clauses
                        .iter()
                        .filter_map(|clause| clause.test.as_ref()),
                )
                .find(contains_receiver),
            ast::Stmt::While(statement) => Some(statement.test.as_ref()),
            ast::Stmt::For(statement) => Some(statement.iter.as_ref()),
            ast::Stmt::With(statement) => statement
                .items
                .iter()
                .map(|item| &item.context_expr)
                .find(contains_receiver),
            ast::Stmt::Match(statement) => std::iter::once(statement.subject.as_ref())
                .chain(
                    statement
                        .cases
                        .iter()
                        .filter_map(|case| case.guard.as_deref()),
                )
                .find(contains_receiver),
            // Exception and pattern headers may lack an independent ordinary inference owner.
            // Their effects remain recorded, but cannot establish a precise transfer.
            ast::Stmt::Try(_) => return None,
            _ => {
                return Some(DictionaryContentsInferenceOwner::Statement(
                    AstNodeRef::new(self.module, statement),
                ));
            }
        }?;
        Some(DictionaryContentsInferenceOwner::Expression(
            AstNodeRef::new(self.module, expression),
        ))
    }

    pub(super) fn record_contents_initializer(&mut self, definition: Definition<'db>) {
        if !definition.category(self.db, self.module).is_binding() {
            return;
        }
        let receiver = self.current_place_table().place(definition.place(self.db));
        let Some(contents) = MemberExprBuilder::from_place(receiver)
            .with_contents()
            .and_then(PlaceExpr::try_from_member_expr)
        else {
            return;
        };
        let Some(place) = self.current_place_table().place_id((&contents).into()) else {
            return;
        };
        let range = definition.kind(self.db).target_range(self.module);
        let initializer = Definition::new(
            self.db,
            self.current_scope_id(),
            place,
            DefinitionKind::DictionaryContents(Box::new(
                DictionaryContentsDefinitionKind::Initialize { definition, range },
            )),
            false,
        );
        self.record_definition(place, initializer, None);
    }

    pub(super) fn record_contents_store(&mut self, subscript: &'ast ast::ExprSubscript) {
        self.record_contents_effect(
            &subscript.value,
            DictionaryContentsEffect::SetItem {
                subscript: AstNodeRef::new(self.module, subscript),
                owner: None,
            },
        );
    }

    pub(super) fn record_contents_use(&mut self, expression: &'ast ast::Expr) {
        let Some(use_id) = self.ast_ids[self.current_scope()].try_use_id(expression) else {
            return;
        };
        let mut places: SmallVec<[_; 2]> = self.contents_place(expression).into_iter().collect();
        if let ast::Expr::Subscript(subscript) = expression
            && let Some(place) = self.contents_place(&subscript.value)
        {
            places.push(place);
        }
        if let ast::Expr::Name(name) = expression
            && let Some(alias) = self.narrowing_aliases.get(&name.id)
        {
            places.extend(
                super::PossiblyNarrowedPlacesBuilder::new(self.db, self.current_place_table())
                    .expression(alias.expression)
                    .into_iter()
                    .filter(|place| match self.current_place_table().place(*place) {
                        crate::place::PlaceExprRef::Member(member) => member.is_contents(),
                        crate::place::PlaceExprRef::Symbol(_) => false,
                    }),
            );
        }
        if expression.is_name_expr() {
            places.extend(
                self.first_value_sources(expression)
                    .into_iter()
                    .filter_map(|receiver| self.contents_place(receiver)),
            );
        }
        self.current_use_def_map_mut()
            .record_multi_use(places.into_iter(), use_id);
    }

    pub(super) fn record_contents_snapshot(
        &mut self,
        expression: &'ast ast::Expr,
        sources: &[&'ast ast::Expr],
    ) {
        let mut places: SmallVec<[_; 2]> = SmallVec::new();
        for &source in sources {
            let Some(contents) = self.contents_place(source) else {
                continue;
            };
            let Some(receiver) = PlaceExpr::try_from_expr(source) else {
                continue;
            };
            let Some(receiver) = self.current_place_table().place_id((&receiver).into()) else {
                continue;
            };
            let Some(original_use) = self.ast_ids[self.current_scope()].try_use_id(source) else {
                continue;
            };
            // Operands are read before the copy executes. Later evaluation can mutate their
            // contents, but a rebound place no longer identifies the previously read value.
            let original: SmallVec<[_; 2]> = self
                .current_use_def_map()
                .bindings_at_use(original_use)
                .map(LiveBinding::binding)
                .collect();
            let current: SmallVec<[_; 2]> = self
                .current_use_def_map_mut()
                .current_bindings(receiver)
                .map(|binding| binding.binding())
                .collect();
            if original == current && !places.contains(&(receiver, contents)) {
                places.push((receiver, contents));
            }
        }
        let Some((receiver, _)) = places.first() else {
            return;
        };
        // Each use has one indexed primary binding; contents observations read the separate
        // multi-use entries for every operand.
        let use_id = if let Some(use_id) = self.current_ast_ids().try_use_id(expression) {
            places.retain(|(_, place)| {
                self.current_use_def_map()
                    .multi_binding_ids_at_use(use_id, *place)
                    .is_empty()
            });
            use_id
        } else {
            let use_id = self.current_ast_ids_mut().record_use(expression);
            self.current_use_def_map_mut().record_use(*receiver, use_id);
            use_id
        };
        self.current_use_def_map_mut()
            .record_multi_use(places.into_iter().map(|(_, contents)| contents), use_id);
    }

    pub(super) fn record_contents_call(
        &mut self,
        expression: &'ast ast::Expr,
        call: &'ast ast::ExprCall,
    ) {
        // A positional mapping is copied after every argument has evaluated.
        if let [source] = call.arguments.args.as_ref() {
            self.record_contents_snapshot(expression, &[source]);
        }

        let occurrences = call_receivers(call);
        let sources: Vec<_> = occurrences
            .iter()
            .map(|&(receiver, _)| {
                let outermost =
                    outermost_receiver(receiver, occurrences.iter().map(|(value, _)| *value));
                let source = if self.contents_place(outermost).is_some() {
                    outermost
                } else {
                    receiver
                };
                (receiver, source)
            })
            .collect();
        let mut receivers: Vec<(ScopedPlaceId, &ast::Expr, bool)> = Vec::new();
        for &(receiver, retained) in &occurrences {
            let Some(place) = self.contents_place(receiver) else {
                continue;
            };
            if let Some((_, _, previous)) = receivers.iter_mut().find(|(id, _, _)| *id == place) {
                *previous |= retained;
            } else {
                receivers.push((place, receiver, retained));
            }
        }
        let mut originals = Vec::new();
        for (place, receiver, retained) in receivers {
            if !sources
                .iter()
                .any(|(_, source)| self.contents_place(source) == Some(place))
            {
                continue;
            }
            let definition = self.record_contents_effect_at(
                place,
                receiver,
                DictionaryContentsEffect::Call {
                    call: AstNodeRef::new(self.module, call),
                    owner: None,
                    retained,
                },
            );
            if let Some(definition) = definition {
                originals.push((place, definition));
            }
        }
        for (receiver, source) in sources {
            let Some(source_place) = self.contents_place(source) else {
                continue;
            };
            let Some(&(_, definition)) = originals.iter().find(|(id, _)| *id == source_place)
            else {
                continue;
            };
            if self.contents_place(receiver) != Some(source_place) {
                self.record_contents_effect(
                    receiver,
                    DictionaryContentsEffect::ProjectedCall(definition),
                );
            }
            self.record_nested_contents_effect(
                receiver,
                &DictionaryContentsEffect::ProjectedCall(definition),
                Some(source),
            );
        }
    }

    pub(super) fn record_value_exposure(&mut self, value: &'ast ast::Expr) {
        let mut receivers = Vec::new();
        value_receivers(value, &mut receivers);
        for &receiver in &receivers {
            self.record_contents_effect(receiver, DictionaryContentsEffect::Expose);
            self.record_nested_contents_effect(receiver, &DictionaryContentsEffect::Expose, None);
        }
    }
}

/// Attribute traversal can mention a containing object that is not itself passed or stored.
pub(super) fn outermost_receiver<'ast>(
    receiver: &'ast ast::Expr,
    receivers: impl Iterator<Item = &'ast ast::Expr>,
) -> &'ast ast::Expr {
    receivers.fold(receiver, |outermost, other| {
        if other.range().contains_range(outermost.range()) {
            other
        } else {
            outermost
        }
    })
}

/// Both ordinary indexing and loop-header discovery use the same demanded descendants.
pub(super) fn nested_contents_places(
    table: &PlaceTableBuilder,
    receiver: &ast::Expr,
    direct_receiver: Option<&ast::Expr>,
) -> SmallVec<[ScopedPlaceId; 2]> {
    let Some(parent) =
        PlaceExpr::try_from_expr(receiver).and_then(|place| table.place_id((&place).into()))
    else {
        return SmallVec::new();
    };
    let direct = PlaceExpr::contents(receiver).and_then(|place| table.place_id((&place).into()));
    let invoked = direct_receiver
        .and_then(PlaceExpr::contents)
        .and_then(|place| table.place_id((&place).into()));
    table
        .associated_place_ids(parent)
        .iter()
        .copied()
        .map(ScopedPlaceId::from)
        .filter(|place| {
            Some(*place) != direct
                && Some(*place) != invoked
                && match table.place(*place) {
                    PlaceExprRef::Member(member) => member.is_contents(),
                    PlaceExprRef::Symbol(_) => false,
                }
        })
        .collect()
}

/// Values stored in another object can retain a mapping; a subscript read does not expose its
/// receiver. Container construction records stored elements. Calls handle their own arguments
/// and return an independently inferred value.
pub(super) fn value_receivers<'ast>(
    expression: &'ast ast::Expr,
    receivers: &mut Vec<&'ast ast::Expr>,
) {
    match expression {
        ast::Expr::Name(_) => receivers.push(expression),
        ast::Expr::Named(named) => value_receivers(&named.target, receivers),
        ast::Expr::Attribute(attribute) => {
            receivers.push(expression);
            value_receivers(&attribute.value, receivers);
        }
        ast::Expr::Subscript(_) => receivers.push(expression),
        ast::Expr::If(if_expr) => {
            value_receivers(&if_expr.body, receivers);
            value_receivers(&if_expr.orelse, receivers);
        }
        ast::Expr::BoolOp(boolean) => {
            for value in &boolean.values {
                value_receivers(value, receivers);
            }
        }
        ast::Expr::Starred(starred) => value_receivers(&starred.value, receivers),
        _ => {}
    }
}

pub(super) fn call_receivers<'ast>(call: &'ast ast::ExprCall) -> Vec<(&'ast ast::Expr, bool)> {
    let mut result = Vec::new();
    let mut add_receivers = |expression: &'ast ast::Expr, direct: bool| {
        let direct = direct
            .then(|| PlaceExpr::try_from_expr(expression))
            .flatten();
        if direct.is_some() {
            result.push((expression, false));
        }
        let mut receivers = Vec::new();
        value_receivers(expression, &mut receivers);
        result.extend(
            receivers
                .into_iter()
                .filter(|receiver| PlaceExpr::try_from_expr(*receiver) != direct)
                .map(|receiver| (receiver, true)),
        );
    };
    if let ast::Expr::Attribute(attribute) = call.func.as_ref() {
        add_receivers(&attribute.value, true);
    } else {
        add_receivers(&call.func, false);
    }
    for argument in &call.arguments.args {
        add_receivers(argument, true);
    }
    for keyword in &call.arguments.keywords {
        if keyword.arg.is_some() {
            add_receivers(&keyword.value, false);
        }
    }
    result
}

#[derive(Clone, Copy)]
enum Observation {
    Contents,
    FirstValue,
}

struct Candidate<'ast> {
    receiver: &'ast ast::Expr,
    dependencies: Vec<usize>,
    observation: Option<Observation>,
    iteration_target: bool,
    list_literal: bool,
}

/// The graph carries only place identity, and is discarded before normal indexing. A demand
/// for an assignment's target propagates to possible source mappings, never from an arbitrary
/// argument to a call's return value. Dictionary syntax and observable call arguments seed
/// candidates; other assigned call results wait for a use that can observe their contents.
/// Constructor spelling is only a discovery hint. Semantic inference checks builtin identity,
/// and the ordinary source-ordered visit owns all effects.
struct Candidates<'ast, 'a> {
    exclusions: &'a SourceExclusions,
    by_place: FxHashMap<MemberExprBuilder, usize>,
    nodes: Vec<Candidate<'ast>>,
}

impl<'ast> Candidates<'ast, '_> {
    fn place(&mut self, receiver: &'ast ast::Expr) -> Option<usize> {
        let place = MemberExprBuilder::visit_expr(receiver.into())?;
        let next = self.nodes.len();
        let index = *self.by_place.entry(place).or_insert_with(|| {
            self.nodes.push(Candidate {
                receiver,
                dependencies: Vec::new(),
                observation: None,
                iteration_target: false,
                list_literal: false,
            });
            next
        });
        Some(index)
    }

    fn demand(&mut self, receiver: &'ast ast::Expr) {
        if let ast::Expr::BinOp(binary) = receiver
            && binary.op == ast::Operator::BitOr
        {
            self.demand(&binary.left);
            self.demand(&binary.right);
        }
        if let Some(index) = self.place(receiver) {
            self.nodes[index]
                .observation
                .get_or_insert(Observation::Contents);
        }
    }

    fn assignment(&mut self, target: &'ast ast::Expr, value: &'ast ast::Expr) {
        let Some(index) = self.place(target) else {
            return;
        };
        let mapping_syntax = match value {
            ast::Expr::Dict(_) => true,
            ast::Expr::DictComp(_) => true,
            ast::Expr::Call(call) => {
                matches!(call.func.as_ref(), ast::Expr::Name(name) if name.id == "dict")
            }
            _ => false,
        };
        if mapping_syntax {
            self.nodes[index]
                .observation
                .get_or_insert(Observation::Contents);
        }
        self.source_dependencies(index, value);
    }

    fn source_dependencies(&mut self, target: usize, value: &'ast ast::Expr) {
        if let Some(source) = self.place(value) {
            self.nodes[target].dependencies.push(source);
            return;
        }
        match value {
            ast::Expr::BinOp(binary) => {
                if binary.op == ast::Operator::BitOr {
                    self.source_dependencies(target, &binary.left);
                    self.source_dependencies(target, &binary.right);
                }
            }
            ast::Expr::Call(call) => {
                for argument in &call.arguments.args {
                    self.source_dependencies(target, argument);
                }
                for keyword in &call.arguments.keywords {
                    if keyword.arg.is_none() {
                        self.source_dependencies(target, &keyword.value);
                    }
                }
            }
            ast::Expr::If(if_expr) => {
                self.source_dependencies(target, &if_expr.body);
                self.source_dependencies(target, &if_expr.orelse);
            }
            ast::Expr::BoolOp(boolean) => {
                for operand in &boolean.values {
                    self.source_dependencies(target, operand);
                }
            }
            _ => {}
        }
    }

    fn comprehension(&mut self, generators: &'ast [ast::Comprehension]) {
        for (index, generator) in generators.iter().enumerate() {
            if index != 0 {
                self.visit_expr(&generator.iter);
            }
            self.visit_expr(&generator.target);
            for condition in &generator.ifs {
                self.visit_expr(condition);
            }
        }
    }

    fn finish(self) -> Vec<(&'ast ast::Expr, bool)> {
        let Self {
            exclusions: _,
            by_place: _,
            nodes: mut candidates,
        } = self;
        let mut pending: Vec<_> = candidates
            .iter()
            .enumerate()
            .filter_map(|(index, candidate)| candidate.observation.map(|_| index))
            .collect();
        while let Some(index) = pending.pop() {
            for dependency in std::mem::take(&mut candidates[index].dependencies) {
                if candidates[dependency].observation.is_none() {
                    candidates[dependency].observation = Some(Observation::Contents);
                    pending.push(dependency);
                }
            }
        }
        candidates
            .into_iter()
            .filter_map(|candidate| {
                let Candidate {
                    receiver,
                    dependencies: _,
                    observation,
                    iteration_target: _,
                    list_literal: _,
                } = candidate;
                observation
                    .map(|observation| (receiver, matches!(observation, Observation::FirstValue)))
            })
            .collect()
    }
}

impl<'ast> Visitor<'ast> for Candidates<'ast, '_> {
    fn visit_stmt(&mut self, statement: &'ast ast::Stmt) {
        if self.exclusions.contains(statement.range()) {
            return;
        }
        match statement {
            ast::Stmt::For(for_stmt) => {
                if for_stmt.iter.is_name_expr()
                    && let Some(iterable) = self.place(&for_stmt.iter)
                    && self.nodes[iterable].list_literal
                    && for_stmt.target.is_name_expr()
                    && let Some(index) = self.place(&for_stmt.target)
                {
                    self.nodes[index].iteration_target = true;
                }
            }
            ast::Stmt::Assign(assign) => {
                if let [target] = assign.targets.as_slice()
                    && target.is_name_expr()
                    && assign.value.is_list_expr()
                    && let Some(index) = self.place(target)
                {
                    self.nodes[index].list_literal = true;
                }
                for target in &assign.targets {
                    self.assignment(target, &assign.value);
                }
            }
            ast::Stmt::AnnAssign(assign) => {
                if let Some(value) = &assign.value {
                    self.assignment(&assign.target, value);
                }
            }
            ast::Stmt::FunctionDef(function) => {
                for decorator in &function.decorator_list {
                    self.visit_decorator(decorator);
                }
                for parameter in function.parameters.iter_non_variadic_params() {
                    if let Some(default) = &parameter.default {
                        self.visit_expr(default);
                    }
                }
                return;
            }
            ast::Stmt::ClassDef(class) => {
                for decorator in &class.decorator_list {
                    self.visit_decorator(decorator);
                }
                if let Some(arguments) = &class.arguments {
                    self.visit_arguments(arguments);
                }
                return;
            }
            ast::Stmt::TypeAlias(_) => return,
            _ => {}
        }
        walk_stmt(self, statement);
    }

    fn visit_annotation(&mut self, _expression: &'ast ast::Expr) {}

    fn visit_keyword(&mut self, keyword: &'ast ast::Keyword) {
        self.demand(&keyword.value);
        self.visit_expr(&keyword.value);
    }

    fn visit_expr(&mut self, expression: &'ast ast::Expr) {
        if self.exclusions.contains(expression.range()) {
            return;
        }
        match expression {
            ast::Expr::Named(named) => self.assignment(&named.target, &named.value),
            ast::Expr::Subscript(subscript) => {
                if let Some(read) = DictionaryFirstValueRead::from_subscript(subscript)
                    && let Some(index) = self.place(read.receiver)
                {
                    self.nodes[index].observation = Some(Observation::FirstValue);
                }
                if matches!(
                    subscript.ctx,
                    ast::ExprContext::Store | ast::ExprContext::Del
                ) {
                    self.demand(&subscript.value);
                } else if subscript.slice.is_string_literal_expr()
                    && subscript.value.is_name_expr()
                    && let Some(index) = self.place(&subscript.value)
                    && self.nodes[index].iteration_target
                {
                    self.nodes[index]
                        .observation
                        .get_or_insert(Observation::Contents);
                }
            }
            ast::Expr::Call(call) => {
                for argument in &call.arguments.args {
                    self.demand(argument);
                }
                if let ast::Expr::Attribute(attribute) = call.func.as_ref()
                    && matches!(
                        attribute.attr.as_str(),
                        "update" | "clear" | "pop" | "popitem" | "setdefault" | "copy"
                    )
                {
                    self.demand(&attribute.value);
                    if attribute.attr.as_str() == "update"
                        && let Some(target) = self.place(&attribute.value)
                    {
                        for source in &call.arguments.args {
                            self.source_dependencies(target, source);
                        }
                    }
                }
            }
            ast::Expr::Dict(dict) => {
                for item in &dict.items {
                    if item.key.is_none() {
                        self.demand(&item.value);
                    }
                }
            }
            ast::Expr::Lambda(lambda) => {
                if let Some(parameters) = &lambda.parameters {
                    for parameter in parameters.iter_non_variadic_params() {
                        if let Some(default) = &parameter.default {
                            self.visit_expr(default);
                        }
                    }
                }
                return;
            }
            ast::Expr::ListComp(comp) => {
                if let Some(first) = comp.generators.first() {
                    self.visit_expr(&first.iter);
                }
                return;
            }
            ast::Expr::SetComp(comp) => {
                if let Some(first) = comp.generators.first() {
                    self.visit_expr(&first.iter);
                }
                return;
            }
            ast::Expr::DictComp(comp) => {
                if let Some(first) = comp.generators.first() {
                    self.visit_expr(&first.iter);
                }
                return;
            }
            ast::Expr::Generator(comp) => {
                if let Some(first) = comp.generators.first() {
                    self.visit_expr(&first.iter);
                }
                return;
            }
            _ => {}
        }
        walk_expr(self, expression);
    }
}

pub(super) fn candidates<'ast>(
    node: NodeWithScopeRef<'ast>,
    module: &'ast [ast::Stmt],
    exclusions: &SourceExclusions,
) -> Vec<(&'ast ast::Expr, bool)> {
    let mut visitor = Candidates {
        exclusions,
        by_place: FxHashMap::default(),
        nodes: Vec::new(),
    };
    match node {
        NodeWithScopeRef::Module => visitor.visit_body(module),
        NodeWithScopeRef::Class(class) => visitor.visit_body(&class.body),
        NodeWithScopeRef::Function(function) => visitor.visit_body(&function.body),
        NodeWithScopeRef::Lambda(lambda) => visitor.visit_expr(&lambda.body),
        NodeWithScopeRef::ListComprehension(comp) => {
            visitor.comprehension(&comp.generators);
            visitor.visit_expr(&comp.elt);
        }
        NodeWithScopeRef::SetComprehension(comp) => {
            visitor.comprehension(&comp.generators);
            visitor.visit_expr(&comp.elt);
        }
        NodeWithScopeRef::DictComprehension(comp) => {
            visitor.comprehension(&comp.generators);
            if let Some(key) = &comp.key {
                visitor.visit_expr(key);
            }
            visitor.visit_expr(&comp.value);
        }
        NodeWithScopeRef::GeneratorExpression(comp) => {
            visitor.comprehension(&comp.generators);
            visitor.visit_expr(&comp.elt);
        }
        NodeWithScopeRef::FunctionTypeParameters(_) => {}
        NodeWithScopeRef::ClassTypeParameters(_) => {}
        NodeWithScopeRef::TypeAlias(_) => {}
        NodeWithScopeRef::TypeAliasTypeParameters(_) => {}
    }
    visitor.finish()
}
