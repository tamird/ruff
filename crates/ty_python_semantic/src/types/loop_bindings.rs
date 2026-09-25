//! Certificates for an initial binding that survives a loop unchanged.

use ruff_db::parsed::parsed_module;
use ruff_python_ast as ast;
use ruff_python_ast::visitor::{Visitor, walk_expr, walk_stmt};
use ruff_text_size::{Ranged, TextSize};
use rustc_hash::FxHashSet;
use ty_python_core::definition::{BindingsOwner, Definition, DefinitionKind, DefinitionState};
use ty_python_core::expression::Expression;
use ty_python_core::predicate::{Predicate, PredicateNode};
use ty_python_core::scope::FileScopeId;
use ty_python_core::{SemanticIndex, semantic_index, use_def_map};

use crate::Db;
use crate::place::MAX_EXACT_LOOP_HEADER_REACHABILITY_NODES;
use crate::semantic_model::SemanticModel;
use crate::types::function::KnownFunction;
use crate::types::{Type, TypeContext, infer_expression_types};

/// Cheap syntax eligibility precedes tracked proof creation.
pub(crate) fn certifies_predicate<'db>(
    db: &'db dyn Db,
    binding: Definition<'db>,
    predicate: &Predicate<'db>,
) -> bool {
    let guard = match predicate.node {
        PredicateNode::Expression(expression) => expression,
        PredicateNode::Condition(expression) => expression,
        _ => return false,
    };
    if guard.scope(db) != binding.scope(db) {
        return false;
    }
    let module = parsed_module(db, guard.scope(db).python_file(db)).load(db);
    let node = guard.node_ref(db).node(&module);
    if empty_length_guard(node).is_none() {
        return false;
    }
    initial_binding_implies_empty(db, binding, guard)
}

fn empty_length_guard(node: &ast::Expr) -> Option<(&ast::ExprCall, &ast::ExprName)> {
    let comparison = node.as_compare_expr()?;
    let (left, operator, right) = comparison.as_single()?;
    if *operator != ast::CmpOp::Eq {
        return None;
    }
    let call = left.as_call_expr()?;
    // A known len result does not make an effectful callee expression pure.
    call.func.as_name_expr()?;
    let zero = right.as_number_literal_expr()?;
    let integer = zero.value.as_int()?;
    if integer.as_i64() != Some(0) || !call.arguments.keywords.is_empty() {
        return None;
    }
    let [argument] = call.arguments.args.as_ref() else {
        return None;
    };
    let source = argument.as_name_expr()?;
    Some((call, source))
}

/// Under this exact initial binding, the compared list still denotes its untouched empty
/// allocation. False also covers provisional inference and unsupported control flow.
#[salsa::tracked(
    returns(copy),
    cycle_initial = |_, _, _, _| false,
    cycle_fn = |_, cycle: &salsa::Cycle, previous: &bool, result: bool, _, _| {
        if cycle.iteration() > crate::TAINTED_CYCLES {
            *previous && result
        } else {
            result
        }
    },
    heap_size = get_size2::GetSize::get_heap_size
)]
fn initial_binding_implies_empty<'db>(
    db: &'db dyn Db,
    binding: Definition<'db>,
    guard: Expression<'db>,
) -> bool {
    prove_initial_binding_implies_empty(db, binding, guard).is_some()
}

fn prove_initial_binding_implies_empty<'db>(
    db: &'db dyn Db,
    binding: Definition<'db>,
    guard: Expression<'db>,
) -> Option<()> {
    let scope = binding.scope(db);
    if scope != guard.scope(db) {
        return None;
    }
    let file = scope.program_file(db);
    let index = semantic_index(db, file);
    let file_scope = scope.file_scope_id(db);
    let function = index.scope(file_scope).node().as_function()?;
    let module = parsed_module(db, scope.python_file(db)).load(db);
    let function = function.node(&module);
    let use_def = use_def_map(db, scope);
    let constraints = use_def.reachability_constraints();
    if constraints.used_interiors().len() > MAX_EXACT_LOOP_HEADER_REACHABILITY_NODES {
        return None;
    }
    let DefinitionKind::Assignment(assignment) = binding.kind(db) else {
        return None;
    };
    if assignment.owner() != BindingsOwner::Definition
        || !assignment.value(&module).is_none_literal_expr()
    {
        return None;
    }
    let table = index.place_table(file_scope);
    let target = assignment.target(&module).as_name_expr()?;
    let target_symbol = table.symbol_id(&target.id)?;
    if !table.symbol(target_symbol).is_local() || table.symbol(target_symbol).is_declared() {
        return None;
    }

    let guard_node = guard.node_ref(db).node(&module);
    let (call, source) = empty_length_guard(guard_node)?;
    let source_symbol = table.symbol_id(&source.id)?;
    if source_symbol == target_symbol
        || !table.symbol(source_symbol).is_local()
        || table.symbol(source_symbol).is_declared()
    {
        return None;
    }
    // A direct post-loop condition gives the reference interval an execution boundary:
    // statements after it cannot mutate the initial allocation on an earlier iteration.
    if !function.body.iter().any(|statement| {
        statement
            .as_if_stmt()
            .is_some_and(|statement| statement.test.range() == guard_node.range())
    }) {
        return None;
    }

    let mut target_header = None;
    for alternative in use_def.reachable_symbol_bindings(target_symbol) {
        let DefinitionState::Defined(definition) = alternative.binding else {
            continue;
        };
        match definition.kind(db) {
            DefinitionKind::NestedBindings(_) => return None,
            DefinitionKind::LoopHeader(_) => {
                if definition.kind(db).full_range(&module).start() >= guard_node.start() {
                    continue;
                }
                if target_header.replace(definition).is_some() {
                    return None;
                }
            }
            _ => {}
        }
    }
    let target_header = target_header?;
    let DefinitionKind::LoopHeader(target_header_kind) = target_header.kind(db) else {
        return None;
    };
    let loop_stmt = target_header_kind.for_stmt(&module)?;
    if loop_stmt.is_async
        || !loop_stmt.orelse.is_empty()
        || loop_stmt.end() > guard_node.start()
        || !function.body.iter().any(|statement| {
            statement
                .as_for_stmt()
                .is_some_and(|statement| statement.range() == loop_stmt.range())
        })
    {
        return None;
    }
    let mut transfer = SimpleTransfer { valid: true };
    transfer.visit_body(&loop_stmt.body);
    if !transfer.valid {
        return None;
    }
    let mut incoming_target = use_def.bindings_at_definition(target_header);
    if incoming_target.next()?.binding != DefinitionState::Defined(binding)
        || incoming_target.next().is_some()
    {
        return None;
    }

    let mut source_header = None;
    for alternative in use_def.reachable_symbol_bindings(source_symbol) {
        let DefinitionState::Defined(definition) = alternative.binding else {
            continue;
        };
        match definition.kind(db) {
            DefinitionKind::NestedBindings(_) => return None,
            DefinitionKind::LoopHeader(header) => {
                if definition.kind(db).full_range(&module).start() >= guard_node.start() {
                    continue;
                }
                if header.loop_header_id() != target_header_kind.loop_header_id()
                    || source_header.replace(definition).is_some()
                {
                    return None;
                }
            }
            _ => {}
        }
    }
    let source_header = source_header?;
    let mut incoming_source = use_def.bindings_at_definition(source_header);
    let DefinitionState::Defined(initial) = incoming_source.next()?.binding else {
        return None;
    };
    if incoming_source.next().is_some() {
        return None;
    }
    let DefinitionKind::Assignment(initial_assignment) = initial.kind(db) else {
        return None;
    };
    // These initializer definitions must each identify a single execution, including the
    // zero-iteration case. A definition inside another loop is not such an initial value.
    for definition in [binding, initial] {
        if !function
            .body
            .iter()
            .any(|statement| statement.range() == definition.kind(db).full_range(&module))
        {
            return None;
        }
    }
    if initial_assignment.owner() != BindingsOwner::Definition
        || !initial_assignment
            .value(&module)
            .as_list_expr()?
            .elts
            .is_empty()
    {
        return None;
    }

    let source_use = index.try_expression_use_id(source.into())?;
    for alternative in use_def.bindings_at_use(source_use) {
        let DefinitionState::Defined(definition) = alternative.binding else {
            return None;
        };
        if definition != initial
            && definition != source_header
            && !loop_stmt
                .range()
                .contains_range(definition.kind(db).full_range(&module))
        {
            return None;
        }
    }

    let header = use_def.loop_header(target_header_kind.loop_header_id());
    let incoming = header.incoming_for_place(target_symbol.into())?;
    for replacement in header.bindings_for_place(source_symbol.into()) {
        if !constraints.runtime_paths_are_disjoint(
            incoming,
            replacement.reachability_constraint(),
            MAX_EXACT_LOOP_HEADER_REACHABILITY_NODES,
        ) {
            return None;
        }
    }

    let mut lifetime = InitialListUses {
        model: SemanticModel::new(db, file),
        index,
        candidates: FxHashSet::from_iter([initial]),
        source_name: source.id.as_str(),
        guard_start: guard_node.start(),
        valid: true,
    };
    lifetime.visit_body(&function.body);
    if !lifetime.valid {
        return None;
    }

    let inference = infer_expression_types(db, guard, TypeContext::default());
    if inference.is_provisional() {
        return None;
    }
    let Type::FunctionLiteral(function) = inference.expression_type(&*call.func) else {
        return None;
    };
    (function.known(db) == Some(KnownFunction::Len)).then_some(())
}

struct SimpleTransfer {
    valid: bool,
}

impl<'ast> Visitor<'ast> for SimpleTransfer {
    fn visit_stmt(&mut self, statement: &'ast ast::Stmt) {
        let Self { valid } = self;
        if matches!(
            statement,
            ast::Stmt::Break(_)
                | ast::Stmt::For(_)
                | ast::Stmt::While(_)
                | ast::Stmt::Try(_)
                | ast::Stmt::With(_)
                | ast::Stmt::FunctionDef(_)
                | ast::Stmt::ClassDef(_)
        ) {
            *valid = false;
        } else if *valid {
            walk_stmt(self, statement);
        }
    }
}

struct InitialListUses<'a, 'db> {
    model: SemanticModel<'db>,
    index: &'a SemanticIndex<'db>,
    candidates: FxHashSet<Definition<'db>>,
    source_name: &'a str,
    guard_start: TextSize,
    valid: bool,
}

impl<'ast> Visitor<'ast> for InitialListUses<'_, '_> {
    fn visit_expr(&mut self, expression: &'ast ast::Expr) {
        let Self {
            model,
            index,
            candidates,
            source_name,
            guard_start,
            valid,
        } = self;
        if !*valid || expression.start() >= *guard_start {
            return;
        }
        if crate::semantic_model::explicitly_reads_local_namespace(expression) {
            *valid = false;
            return;
        }
        if let ast::Expr::Name(name) = expression
            && name.id.as_str() == *source_name
            && index.try_expression_use_id(name.into()).is_some()
        {
            let scope: FileScopeId = index.expression_scope_id(expression);
            *valid = model.name_may_reference_definitions(name, scope, candidates) == Some(false);
        }
        if *valid {
            walk_expr(self, expression);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::db::tests::TestDbBuilder;
    use crate::{HasType, ProgramEnvironment};
    use ruff_db::files::system_path_to_file;
    use ruff_db::parsed::ParsedModuleRef;
    use ruff_db::system::DbWithWritableSystem as _;

    const ORIGINAL: &str = r#"
def select(rows: list[tuple[bool, list[str], str]]) -> str:
    tags = []
    name = None
    for root, values, configured in rows:
        if root:
            tags = list(values)
            name = configured
    if len(tags) == 0:
        raise RuntimeError
    return name
"#;

    fn inputs<'db>(
        db: &'db dyn Db,
        file: ty_python_core::ProgramFile<'db>,
        module: &ParsedModuleRef,
    ) -> (Definition<'db>, Expression<'db>) {
        let index = semantic_index(db, file);
        for (scope, expression, use_id) in index.expression_uses(module) {
            let ast::ExprRef::Name(name) = expression else {
                continue;
            };
            if name.id != "name" {
                continue;
            }
            let use_def = index.use_def_map(scope);
            for alternative in use_def.bindings_at_use(use_id) {
                let DefinitionState::Defined(definition) = alternative.binding else {
                    continue;
                };
                let DefinitionKind::Assignment(assignment) = definition.kind(db) else {
                    continue;
                };
                if !assignment.value(module).is_none_literal_expr() {
                    continue;
                }
                for predicate in use_def.predicates().iter() {
                    let guard = match predicate.node {
                        PredicateNode::Expression(expression) => expression,
                        PredicateNode::Condition(expression) => expression,
                        _ => continue,
                    };
                    if empty_length_guard(guard.node_ref(db).node(module)).is_some() {
                        return (definition, guard);
                    }
                }
            }
        }
        panic!("initial binding and length guard must be indexed");
    }

    #[test]
    fn loop_binding_original_query_order() -> anyhow::Result<()> {
        for guard_first in [false, true] {
            let db = TestDbBuilder::new()
                .with_file("/src/main.py", ORIGINAL)
                .build()?;
            let file = db.program_file(system_path_to_file(&db, "/src/main.py")?);
            let module = parsed_module(&db, file.python_file(&db)).load(&db);
            let (binding, guard) = inputs(&db, file, &module);
            if guard_first {
                assert!(
                    !infer_expression_types(&db, guard, TypeContext::default()).is_provisional()
                );
            }
            assert!(initial_binding_implies_empty(&db, binding, guard));
            let diagnostics = crate::types::check_types(&db, file);
            assert!(diagnostics.is_empty(), "{diagnostics:?}");
            let model = SemanticModel::new(&db, file);
            let env = ProgramEnvironment::from_file(file);
            for (_, expression, _) in semantic_index(&db, file).expression_uses(&module) {
                let ast::ExprRef::Name(name) = expression else {
                    continue;
                };
                if name.id == "name" {
                    let ty = expression
                        .inferred_type(&model)
                        .expect("checked return value");
                    assert_eq!(ty.display(&db, &env).to_string(), "str");
                }
            }
        }
        Ok(())
    }

    #[test]
    fn loop_binding_tracks_partial_write_and_allocation_edits() -> anyhow::Result<()> {
        let partial = ORIGINAL.replace(
            "            name = configured",
            "            if root:\n                continue\n            name = configured",
        );
        let missing = ORIGINAL.replace("            name = configured", "            pass");
        let mutated = ORIGINAL.replace(
            "    name = None",
            "    name = None\n    tags.append('extra')",
        );
        let mut db = TestDbBuilder::new().with_file("/src/main.py", "").build()?;
        for (source, accepted) in [
            (ORIGINAL, true),
            (&partial, false),
            (ORIGINAL, true),
            (&missing, false),
            (ORIGINAL, true),
            (&mutated, false),
            (ORIGINAL, true),
        ] {
            db.write_file("/src/main.py", source)?;
            let file = db.program_file(system_path_to_file(&db, "/src/main.py")?);
            let diagnostics = crate::types::check_types(&db, file);
            if accepted {
                assert!(diagnostics.is_empty(), "{diagnostics:?}");
            } else {
                let [diagnostic] = diagnostics.as_slice() else {
                    panic!("expected retained return error: {diagnostics:?}");
                };
                assert_eq!(diagnostic.id().as_str(), "invalid-return-type");
                let range = diagnostic
                    .primary_span()
                    .expect("return diagnostic")
                    .range()
                    .expect("return span");
                assert_eq!(&source[range], "name");
            }
        }
        Ok(())
    }

    #[test]
    fn loop_binding_cycle_preserves_types_and_errors() -> anyhow::Result<()> {
        let source = ORIGINAL.replace(
            "    return name",
            "    tags.append(name)\n    number('wrong')\n    return name",
        ) + "\ndef number(value: int) -> None: ...\n";
        for guard_first in [false, true] {
            let mut db = TestDbBuilder::new()
                .with_file("/src/main.py", &source)
                .build()?;
            let file = db.program_file(system_path_to_file(&db, "/src/main.py")?);
            let module = parsed_module(&db, file.python_file(&db)).load(&db);
            let (binding, guard) = inputs(&db, file, &module);
            if guard_first {
                let _inference = infer_expression_types(&db, guard, TypeContext::default());
            }
            assert!(initial_binding_implies_empty(&db, binding, guard));
            let diagnostics = crate::types::check_types(&db, file);
            let [diagnostic] = diagnostics.as_slice() else {
                panic!("expected independent argument error: {diagnostics:?}");
            };
            assert_eq!(diagnostic.id().as_str(), "invalid-argument-type");
            let range = diagnostic
                .primary_span()
                .expect("argument error")
                .range()
                .expect("argument range");
            assert_eq!(&source[range], "'wrong'");
            let model = SemanticModel::new(&db, file);
            let env = ProgramEnvironment::from_file(file);
            let mut reads = 0;
            for (_, expression, _) in semantic_index(&db, file).expression_uses(&module) {
                let ast::ExprRef::Name(name) = expression else {
                    continue;
                };
                if name.id == "name" {
                    let ty = expression.inferred_type(&model).expect("checked value");
                    assert_eq!(ty.display(&db, &env).to_string(), "str");
                    reads += 1;
                }
            }
            assert_eq!(reads, 2, "append and return must agree");
            let events = db.take_salsa_events();
            let queries: Vec<_> = salsa::attach(&db, || {
                events
                    .iter()
                    .filter_map(|event| {
                        let salsa::EventKind::WillIterateCycle { database_key, .. } = event.kind
                        else {
                            return None;
                        };
                        Some(format!("{database_key:?}"))
                    })
                    .collect()
            });
            let expected_query = if guard_first {
                "infer_expression_types_impl"
            } else {
                "initial_binding_implies_empty"
            };
            assert!(
                queries
                    .iter()
                    .any(|query| query.starts_with(expected_query)),
                "the admitted feedback must cycle in {expected_query}: {queries:?}"
            );
        }
        Ok(())
    }
}
