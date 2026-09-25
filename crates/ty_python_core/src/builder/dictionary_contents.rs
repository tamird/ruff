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
use crate::place::{PlaceExpr, ScopedPlaceId};
use crate::scope::NodeWithScopeRef;

use super::{SemanticIndexBuilder, UnresolvedCapture};
use crate::use_def::{
    FutureDefinitions, ImportedQualifierAction, LiveBinding, PreviousDefinitions,
};

impl<'db, 'ast> SemanticIndexBuilder<'db, 'ast> {
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
            ast::Expr::Attribute(attribute) => self.register_receiver_place(&attribute.value),
            ast::Expr::Subscript(subscript) => self.register_receiver_place(&subscript.value),
            ast::Expr::Named(named) => self.register_receiver_place(&named.target),
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
        mut effect: DictionaryContentsEffect<'db>,
    ) {
        let Some(place) = self.contents_place(receiver) else {
            return;
        };
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
            DictionaryContentsEffect::UnknownMutation => None,
            DictionaryContentsEffect::Expose => None,
        };
        if let Some(owner) = owner {
            let Some(statement) = self.current_statement_mut() else {
                return;
            };
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
        self.current_use_def_map_mut()
            .record_multi_use(places.into_iter(), use_id);
    }

    pub(super) fn record_contents_call(
        &mut self,
        expression: &'ast ast::Expr,
        call: &'ast ast::ExprCall,
    ) {
        // A positional mapping is copied by the invoked constructor after every argument has
        // evaluated. Its earlier receiver binding must still identify the same value.
        if let [source] = call.arguments.args.as_ref()
            && let Some(contents) = self.contents_place(source)
            && let Some(receiver) = PlaceExpr::try_from_expr(source)
            && let Some(receiver) = self.current_place_table().place_id((&receiver).into())
            && let Some(original_use) = self.ast_ids[self.current_scope()].try_use_id(source)
        {
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
            if original == current {
                let use_id = self.current_ast_ids_mut().record_use(expression);
                self.current_use_def_map_mut().record_use(receiver, use_id);
                self.current_use_def_map_mut()
                    .record_multi_use(std::iter::once(contents), use_id);
            }
        }

        let mut receivers: Vec<(ScopedPlaceId, &ast::Expr, bool)> = Vec::new();
        for (receiver, retained) in call_receivers(call) {
            let Some(place) = self.contents_place(receiver) else {
                continue;
            };
            if let Some((_, _, previous)) = receivers.iter_mut().find(|(id, _, _)| *id == place) {
                *previous |= retained;
            } else {
                receivers.push((place, receiver, retained));
            }
        }
        for (_, receiver, retained) in receivers {
            self.record_contents_effect(
                receiver,
                DictionaryContentsEffect::Call {
                    call: AstNodeRef::new(self.module, call),
                    owner: None,
                    retained,
                },
            );
        }
    }

    pub(super) fn record_value_exposure(&mut self, value: &'ast ast::Expr) {
        let mut receivers = Vec::new();
        value_receivers(value, &mut receivers);
        for receiver in receivers {
            self.record_contents_effect(receiver, DictionaryContentsEffect::Expose);
        }
    }
}

/// Values stored in another object can retain a mapping; a subscript read does not expose its
/// receiver. Calls handle their own arguments and return an independently inferred value.
pub(super) fn value_receivers<'ast>(
    expression: &'ast ast::Expr,
    receivers: &mut Vec<&'ast ast::Expr>,
) {
    match expression {
        ast::Expr::Name(_) => receivers.push(expression),
        ast::Expr::Attribute(attribute) => {
            receivers.push(expression);
            receivers.push(&attribute.value);
        }
        ast::Expr::Subscript(_) => receivers.push(expression),
        ast::Expr::List(list) => {
            for value in &list.elts {
                value_receivers(value, receivers);
            }
        }
        ast::Expr::Tuple(tuple) => {
            for value in &tuple.elts {
                value_receivers(value, receivers);
            }
        }
        ast::Expr::Set(set) => {
            for value in &set.elts {
                value_receivers(value, receivers);
            }
        }
        ast::Expr::Dict(dict) => {
            for item in &dict.items {
                if item.key.is_some() {
                    value_receivers(&item.value, receivers);
                }
            }
        }
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

pub(super) fn call_receivers(call: &ast::ExprCall) -> Vec<(&ast::Expr, bool)> {
    let mut result = Vec::new();
    if let ast::Expr::Attribute(attribute) = call.func.as_ref() {
        result.push((attribute.value.as_ref(), false));
    }
    for argument in &call.arguments.args {
        if PlaceExpr::try_from_expr(argument).is_some() {
            result.push((argument, false));
        } else {
            let mut nested = Vec::new();
            value_receivers(argument, &mut nested);
            result.extend(nested.into_iter().map(|receiver| (receiver, true)));
        }
    }
    for keyword in &call.arguments.keywords {
        if keyword.arg.is_some() {
            let mut nested = Vec::new();
            value_receivers(&keyword.value, &mut nested);
            result.extend(nested.into_iter().map(|receiver| (receiver, true)));
        }
    }
    result
}

struct Candidate<'ast> {
    receiver: &'ast ast::Expr,
    dependencies: Vec<usize>,
    demanded: bool,
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
                demanded: false,
            });
            next
        });
        Some(index)
    }

    fn demand(&mut self, receiver: &'ast ast::Expr) {
        if let Some(index) = self.place(receiver) {
            self.nodes[index].demanded = true;
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
            self.nodes[index].demanded = true;
        }
        self.source_dependencies(index, value);
    }

    fn source_dependencies(&mut self, target: usize, value: &'ast ast::Expr) {
        if let Some(source) = self.place(value) {
            self.nodes[target].dependencies.push(source);
            return;
        }
        match value {
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

    fn finish(self) -> Vec<&'ast ast::Expr> {
        let Self {
            exclusions: _,
            by_place: _,
            nodes: mut candidates,
        } = self;
        let mut pending: Vec<_> = candidates
            .iter()
            .enumerate()
            .filter_map(|(index, candidate)| candidate.demanded.then_some(index))
            .collect();
        while let Some(index) = pending.pop() {
            for dependency in std::mem::take(&mut candidates[index].dependencies) {
                if !candidates[dependency].demanded {
                    candidates[dependency].demanded = true;
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
                    demanded,
                } = candidate;
                demanded.then_some(receiver)
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
            ast::Stmt::Assign(assign) => {
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
                if matches!(
                    subscript.ctx,
                    ast::ExprContext::Store | ast::ExprContext::Del
                ) {
                    self.demand(&subscript.value);
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
) -> Vec<&'ast ast::Expr> {
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
