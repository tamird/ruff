//! Context for returned locals whose every use has the same declared expectation.

use itertools::Itertools;
use ruff_db::parsed::parsed_module;
use ruff_python_ast::{
    self as ast, ExprRef,
    visitor::{self, Visitor},
};
use ty_python_core::definition::{BindingsOwner, Definition, DefinitionKind, DefinitionState};
use ty_python_core::place::PlaceExpr;
use ty_python_core::reachability_constraints::ScopedReachabilityConstraintId;
use ty_python_core::scope::{FileScopeId, ScopeId};
use ty_python_core::{SemanticIndex, semantic_index};

use super::nearest_enclosing_function;
use crate::place_load::{
    ImplicitPlaceLoad, PlaceLoadMode, PlaceLoadResolutionStep, PlaceLoadSourceKind,
    resolve_place_load,
};
use crate::types::call::CallArguments;
use crate::types::function::same_module_uncached_raw_signature;
use crate::types::signatures::ReturnCallableTypeVarScope;
use crate::types::string_annotation::SourceAnnotation;
use crate::types::{Type, binding_type};
use crate::{Db, FxIndexMap, ProgramEnvironment};

#[derive(Clone, Copy)]
enum Use<'ast> {
    Return,
    Argument(&'ast ast::ExprCall, usize),
    Other,
}

struct Uses<'ast> {
    names: Vec<(&'ast ast::ExprName, Use<'ast>)>,
    eligible: bool,
    own_returns: bool,
}

impl<'ast> Uses<'ast> {
    fn expression(&mut self, expression: &'ast ast::Expr, usage: Use<'ast>) {
        if let ast::Expr::Name(name) = expression {
            self.names.push((name, usage));
        } else {
            self.visit_expr(expression);
        }
    }
}

impl<'ast> Visitor<'ast> for Uses<'ast> {
    fn visit_stmt(&mut self, statement: &'ast ast::Stmt) {
        if self.own_returns
            && let ast::Stmt::Return(ret) = statement
        {
            if let Some(value) = &ret.value {
                self.expression(value, Use::Return);
            }
            return;
        }
        let eligible = self.eligible;
        let own_returns = self.own_returns;
        if matches!(
            statement,
            ast::Stmt::FunctionDef(_) | ast::Stmt::ClassDef(_) | ast::Stmt::TypeAlias(_)
        ) {
            self.eligible = false;
            self.own_returns = false;
        }
        visitor::walk_stmt(self, statement);
        self.eligible = eligible;
        self.own_returns = own_returns;
    }

    fn visit_annotation(&mut self, expression: &'ast ast::Expr) {
        let eligible = self.eligible;
        self.eligible = false;
        self.visit_expr(expression);
        self.eligible = eligible;
    }

    fn visit_expr(&mut self, expression: &'ast ast::Expr) {
        match expression {
            ast::Expr::Name(name) => self.names.push((name, Use::Other)),
            ast::Expr::Lambda(lambda) => {
                let eligible = self.eligible;
                self.eligible = false;
                if let Some(parameters) = &lambda.parameters {
                    self.visit_parameters(parameters);
                }
                self.eligible = eligible;
                self.visit_expr(&lambda.body);
            }
            ast::Expr::Call(call) => {
                self.visit_expr(&call.func);
                for (index, argument) in call.arguments.iter_source_order().enumerate() {
                    let value = argument.value();
                    let usage = if self.eligible && !argument.is_variadic() {
                        Use::Argument(call, index)
                    } else {
                        Use::Other
                    };
                    self.expression(value, usage);
                }
            }
            _ => visitor::walk_expr(self, expression),
        }
    }
}

/// This query does not infer candidate initializers or statements containing their uses.
/// The complete raw reference check precedes all helper signature queries.
#[salsa::tracked(returns(ref), cycle_initial=|_, _, _| Box::default(), heap_size=ruff_memory_usage::heap_size)]
pub(super) fn returned_local_contexts<'db>(
    db: &'db dyn Db,
    scope: ScopeId<'db>,
) -> Box<[(Definition<'db>, Type<'db>)]> {
    let file = scope.program_file(db);
    let index = semantic_index(db, file);
    let Some(function_ref) = scope.node(db).as_function() else {
        return Box::default();
    };
    if scope.file_scope_id(db).is_generator_function(index) {
        return Box::default();
    }
    let module = parsed_module(db, file.python_file(db)).load(db);
    let function = function_ref.node(&module);
    if SourceAnnotation::function_return(db, file, function).is_none() {
        return Box::default();
    }
    let Some(function_type) = nearest_enclosing_function(db, index, scope) else {
        return Box::default();
    };
    let signature =
        same_module_uncached_raw_signature(db, function_type, ReturnCallableTypeVarScope::Lexical);
    let expected = signature.return_ty;
    let env = ProgramEnvironment::from_file(file);
    if signature.generic_context.is_some()
        || expected.is_unknown()
        || expected.is_divergent()
        || expected.has_provisional_marker(db, &env)
        || matches!(
            expected.resolve_type_alias(db),
            Type::TypeIs(_) | Type::TypeGuard(_)
        )
    {
        return Box::default();
    }
    let mut uses = Uses {
        names: Vec::new(),
        eligible: true,
        own_returns: true,
    };
    uses.visit_body(&function.body);
    let mut candidates = FxIndexMap::default();
    for &(name, usage) in &uses.names {
        if !matches!(usage, Use::Return) {
            continue;
        }
        let Some(definition) = raw_definition(db, index, scope, name) else {
            continue;
        };
        if definition.scope(db) != scope {
            continue;
        }
        let DefinitionKind::Assignment(assignment) = definition.kind(db) else {
            continue;
        };
        if assignment.owner() != BindingsOwner::Definition {
            continue;
        }
        let table = index.place_table(scope.file_scope_id(db));
        let Some(symbol) = table.symbol_id(&name.id) else {
            continue;
        };
        if !table.symbol(symbol).is_local() {
            continue;
        }
        let mut history = index
            .use_def_map(scope.file_scope_id(db))
            .reachable_symbol_bindings(symbol);
        if history.next().map(|binding| binding.binding) != Some(DefinitionState::Undefined)
            || history.any(|binding| binding.binding != DefinitionState::Defined(definition))
        {
            continue;
        }
        candidates.insert(name.id.as_str(), (definition, Vec::new()));
    }
    if candidates.is_empty() {
        return Box::default();
    }

    for &(name, usage) in &uses.names {
        let Some((definition, contexts)) = candidates.get_mut(name.id.as_str()) else {
            continue;
        };
        if index.try_expression_use_id(name.into()).is_none() && name.ctx.is_store() {
            continue;
        }
        let resolved = index
            .try_expression_scope_id(&ExprRef::from(name))
            .and_then(|use_scope| raw_definition(db, index, use_scope.to_scope_id(db, file), name));
        if let Some(resolved) = resolved {
            if resolved != *definition {
                continue;
            }
            if !matches!(usage, Use::Other) {
                contexts.push(usage);
                continue;
            }
        }
        candidates.shift_remove(name.id.as_str());
    }
    if candidates.is_empty() {
        return Box::default();
    }

    candidates
        .into_iter()
        .filter_map(|(_, (definition, uses))| {
            uses.into_iter()
                .all(|usage| match usage {
                    Use::Return => true,
                    Use::Argument(call, argument) => {
                        let formal = formal_context(db, index, scope, call, argument);
                        formal == Some(expected)
                    }
                    Use::Other => false,
                })
                .then_some((definition, expected))
        })
        .collect()
}

fn raw_definition<'db>(
    db: &'db dyn Db,
    index: &'db SemanticIndex<'db>,
    scope: ScopeId<'db>,
    name: &ast::ExprName,
) -> Option<Definition<'db>> {
    index.try_expression_use_id(name.into())?;
    let file = scope.program_file(db);
    for step in resolve_place_load(
        db,
        index,
        scope,
        PlaceExpr::from_expr_name(name),
        PlaceLoadMode::AtExpression(name.into()),
    ) {
        let source = match step {
            PlaceLoadResolutionStep::Source(source) => source,
            PlaceLoadResolutionStep::MemberResolutionCondition(_) => return None,
            PlaceLoadResolutionStep::Exhausted(_) => return None,
        };
        let bindings = match source.kind {
            PlaceLoadSourceKind::Bindings(bindings) => bindings,
            PlaceLoadSourceKind::DefinitionsFromOwningScope { scope, id } => {
                if scope.program_file(db) != file {
                    return None;
                }
                let mut history = index
                    .use_def_map(scope.file_scope_id(db))
                    .reachable_bindings(id);
                // Unlike a use snapshot, accumulated history prepends a scope-entry sentinel.
                // This selects binding identity; ordinary place inference retains boundness.
                if history.next()?.binding != DefinitionState::Undefined {
                    return None;
                }
                history
            }
            PlaceLoadSourceKind::Implicit(implicit) => match implicit {
                ImplicitPlaceLoad::ExplicitGlobalSymbol {
                    file: global_file,
                    name,
                } => {
                    if global_file != file {
                        return None;
                    }
                    let symbol = index.place_table(FileScopeId::global()).symbol_id(&name)?;
                    index
                        .use_def_map(FileScopeId::global())
                        .end_of_scope_symbol_bindings(symbol)
                }
                ImplicitPlaceLoad::ClassBodySymbol(_) => continue,
                ImplicitPlaceLoad::DunderClass(_) => return None,
                ImplicitPlaceLoad::ModuleImplicitGlobal { file: _, name: _ } => return None,
                ImplicitPlaceLoad::Builtin(_) => return None,
            },
        };
        let bindings: Vec<_> = bindings
            .filter(|binding| {
                binding.reachability_constraint != ScopedReachabilityConstraintId::ALWAYS_FALSE
            })
            .map(|binding| binding.binding)
            .collect();
        if bindings
            .iter()
            .all(|binding| *binding == DefinitionState::Undefined)
        {
            continue;
        }
        let [DefinitionState::Defined(definition)] = bindings.as_slice() else {
            return None;
        };
        if matches!(
            definition.kind(db),
            DefinitionKind::LoopHeader(_) | DefinitionKind::NestedBindings(_)
        ) {
            return None;
        }
        return Some(*definition);
    }
    None
}

fn formal_context<'db>(
    db: &'db dyn Db,
    index: &'db SemanticIndex<'db>,
    scope: ScopeId<'db>,
    call: &ast::ExprCall,
    argument: usize,
) -> Option<Type<'db>> {
    if call
        .arguments
        .iter_source_order()
        .any(ast::ArgOrKeyword::is_variadic)
    {
        return None;
    }
    let name = call.func.as_name_expr()?;
    let call_scope = index
        .expression_scope_id(&ExprRef::from(name))
        .to_scope_id(db, scope.program_file(db));
    let definition = raw_definition(db, index, call_scope, name)?;
    if !matches!(definition.kind(db), DefinitionKind::Function(_)) {
        return None;
    }
    let Type::FunctionLiteral(function) = binding_type(db, definition) else {
        return None;
    };
    let signature = function.signature(db).iter().exactly_one().ok()?;
    if signature.generic_context.is_some() {
        return None;
    }
    let env = ProgramEnvironment::from_file(scope.program_file(db));
    let arguments = CallArguments::from_arguments(&call.arguments, |_, _| Type::unknown());
    let bindings = Type::FunctionLiteral(function)
        .bindings(db, &env)
        .match_parameters(db, &env, &arguments);
    let binding = bindings
        .single_element()?
        .matching_overloads()
        .exactly_one()
        .ok()?
        .1;
    let matched = binding.argument_matches().get(argument)?;
    if !matched.matched {
        return None;
    }
    let [parameter] = matched.parameters.as_slice() else {
        return None;
    };
    Some(
        binding
            .signature
            .parameters()
            .get(parameter.index)?
            .annotated_type(),
    )
}
