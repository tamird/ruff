//! Dictionary elements of a confined, locally produced list.

use ruff_db::parsed::{ParsedModuleRef, parsed_module};
use ruff_python_ast::visitor::{Visitor, walk_expr};
use ruff_python_ast::{self as ast, ExprRef};
use ruff_text_size::Ranged;
use rustc_hash::{FxHashMap, FxHashSet};
use ty_python_core::definition::{BindingsOwner, Definition, DefinitionKind, DefinitionState};
use ty_python_core::predicate::PredicateNode;
use ty_python_core::scope::FileScopeId;
use ty_python_core::{ExpressionNodeKey, SemanticIndex, Statement, semantic_index};

use crate::types::infer::{StatementInference, infer_definition_types, infer_statement_types};
use crate::types::{KnownClass, MemberLookupPolicy, ProgramEnvironment, Type};
use crate::{Db, FxIndexSet, SemanticModel};

use super::contents::{ContentsValue, MappingContents};
use super::{DictionaryFallback, DictionaryItems};

fn local_binding<'db>(
    db: &'db dyn Db,
    index: &SemanticIndex<'db>,
    scope: ty_python_core::scope::FileScopeId,
    name: &ast::ExprName,
) -> Option<Definition<'db>> {
    let table = index.place_table(scope);
    let symbol = table.symbol_id(&name.id)?;
    if !table.symbol(symbol).is_local() || table.symbol(symbol).is_declared() {
        return None;
    }
    let use_id = index.try_expression_use_id(name.into())?;
    let mut bindings = index.use_def_map(scope).bindings_at_use(use_id);
    let DefinitionState::Defined(definition) = bindings.next()?.binding else {
        return None;
    };
    if bindings.next().is_some() || definition.scope(db).file_scope_id(db) != scope {
        return None;
    }
    Some(definition)
}

struct Producers<'db, 'ast> {
    initial: &'ast ast::ExprList,
    appends: Vec<Append<'db, 'ast>>,
}

struct Append<'db, 'ast> {
    statement: Statement<'db>,
    callee: &'ast ast::Expr,
    receiver: &'ast ast::Expr,
    value: &'ast ast::Expr,
}

/// Syntax selects possible producers and readers; the indexed raw uses close the proof.
/// Row bindings are separate loop definitions, whose only permitted observations read keys.
fn producers<'db, 'ast>(
    db: &'db dyn Db,
    definition: Definition<'db>,
    module: &'ast ParsedModuleRef,
) -> Option<Producers<'db, 'ast>> {
    let scope = definition.scope(db);
    let file = scope.program_file(db);
    let index = semantic_index(db, file);
    let file_scope = scope.file_scope_id(db);
    let function = index.scope(file_scope).node().as_function()?;
    let function = function.node(module);
    let table = index.place_table(file_scope);
    let use_def = index.use_def_map(file_scope);
    let DefinitionKind::Assignment(assignment) = definition.kind(db) else {
        return None;
    };
    if assignment.owner() != BindingsOwner::Definition {
        return None;
    }
    let target = assignment.target(module).as_name_expr()?;
    let symbol = table.symbol_id(&target.id)?;
    if !table.symbol(symbol).is_local() || table.symbol(symbol).is_declared() {
        return None;
    }
    let initial = assignment.value(module).as_list_expr()?;
    if !initial.elts.iter().all(ast::Expr::is_dict_expr) {
        return None;
    }
    let mut history = use_def.reachable_symbol_bindings(symbol);
    if history.next()?.binding != DefinitionState::Undefined
        || history.any(|binding| binding.binding != DefinitionState::Defined(definition))
    {
        return None;
    }

    let mut allowed = FxHashSet::default();
    let mut appends = Vec::new();
    for (statement, _) in index.constraining_collection_uses(definition) {
        let Statement::Expression(expression) = statement else {
            return None;
        };
        let call = expression.node_ref(db).node(module).as_call_expr()?;
        let attribute = call.func.as_attribute_expr()?;
        let receiver = attribute.value.as_name_expr()?;
        let [argument] = call.arguments.args.as_ref() else {
            return None;
        };
        if attribute.attr.as_str() != "append"
            || !call.arguments.keywords.is_empty()
            || !argument.is_dict_expr()
            || local_binding(db, index, file_scope, receiver)? != definition
        {
            return None;
        }
        allowed.insert(ExpressionNodeKey::from(ExprRef::Name(receiver)));
        appends.push(Append {
            statement,
            callee: &call.func,
            receiver: &attribute.value,
            value: argument,
        });
    }

    let mut relevant_names = FxHashSet::from_iter([target.id.as_str()]);
    let mut rows = FxHashMap::default();
    let mut row_symbols = FxIndexSet::default();
    let mut loops = FxHashSet::default();
    for (_, candidate, _) in use_def.definitions_with_usage() {
        let DefinitionKind::For(for_stmt) = candidate.kind(db) else {
            continue;
        };
        let Some(iterable) = for_stmt.iterable(module).as_name_expr() else {
            continue;
        };
        if local_binding(db, index, file_scope, iterable) != Some(definition) {
            continue;
        }
        if for_stmt.is_async() {
            return None;
        }
        let node = for_stmt.node(module);
        let row = node.target.as_name_expr()?;
        let row_symbol = table.symbol_id(&row.id)?;
        if !table.symbol(row_symbol).is_local() || table.symbol(row_symbol).is_declared() {
            return None;
        }
        relevant_names.insert(row.id.as_str());
        let first = node.body.first()?;
        let last = node.body.last()?;
        rows.insert(candidate, first.range().cover(last.range()));
        row_symbols.insert(row_symbol);
        loops.insert(for_stmt.node(module).range());
        allowed.insert(ExpressionNodeKey::from(ExprRef::Name(iterable)));
    }
    if rows.is_empty() {
        return None;
    }
    for symbol in row_symbols {
        let mut history = use_def.reachable_symbol_bindings(symbol);
        if history.next()?.binding != DefinitionState::Undefined {
            return None;
        }
        for binding in history {
            let DefinitionState::Defined(binding) = binding.binding else {
                return None;
            };
            match binding.kind(db) {
                DefinitionKind::For(_) => {
                    if !rows.contains_key(&binding) {
                        return None;
                    }
                }
                DefinitionKind::LoopHeader(_) => {
                    if !loops.contains(&binding.kind(db).target_range(module)) {
                        return None;
                    }
                }
                _ => return None,
            }
        }
    }

    // `not` produces a bool even in value context. A bare Name predicate alone can
    // also occur in `alias = entries or []`, so only actual Boolean roots admit it.
    for predicate in use_def.predicates().iter() {
        let expression = match predicate.node {
            PredicateNode::Expression(expression) => expression,
            PredicateNode::Condition(expression) => expression,
            _ => continue,
        };
        let ast::Expr::UnaryOp(unary) = expression.node_ref(db).node(module) else {
            continue;
        };
        if unary.op == ast::UnaryOp::Not
            && let Some(name) = unary.operand.as_name_expr()
            && local_binding(db, index, file_scope, name) == Some(definition)
        {
            allowed.insert(ExpressionNodeKey::from(ExprRef::Name(name)));
        }
    }

    let mut candidates: FxHashSet<_> = rows.keys().copied().collect();
    candidates.insert(definition);
    let model = SemanticModel::new(db, file);
    let mut uses = LocalUses {
        index,
        valid: true,
        inspect: |use_scope, expression| {
            match expression {
                ExprRef::Subscript(subscript) => {
                    if use_scope != file_scope
                        || subscript.ctx != ast::ExprContext::Load
                        || !subscript.slice.is_string_literal_expr()
                    {
                        return true;
                    }
                    let Some(name) = subscript.value.as_name_expr() else {
                        return true;
                    };
                    let Some(binding) = local_binding(db, index, file_scope, name) else {
                        return true;
                    };
                    if rows
                        .get(&binding)
                        .is_some_and(|body| body.contains_range(subscript.range()))
                    {
                        allowed.insert(ExpressionNodeKey::from(ExprRef::Name(name)));
                    }
                }
                ExprRef::Name(name) => {
                    if name.id == target.id
                        && use_scope == file_scope
                        && index.is_boolean_test_root(&ast::Expr::Name(name.clone()))
                        && local_binding(db, index, file_scope, name) == Some(definition)
                    {
                        allowed.insert(expression.into());
                    }
                    if relevant_names.contains(name.id.as_str())
                        && !allowed.contains(&ExpressionNodeKey::from(expression))
                    {
                        return model.name_may_reference_definitions(name, use_scope, &candidates)
                            == Some(false);
                    }
                }
                _ => {}
            }
            true
        },
    };
    uses.visit_body(&function.body);
    if !uses.valid {
        return None;
    }
    Some(Producers { initial, appends })
}

/// Walk the owning function and its nested scopes, checking only indexed place uses.
/// A subscript precedes its receiver, so admitted key reads are known before checking Names.
/// Actual indexed scopes and raw resolution distinguish captures from unrelated shadows.
struct LocalUses<'a, 'db, F> {
    index: &'a SemanticIndex<'db>,
    inspect: F,
    valid: bool,
}

impl<'ast, F> Visitor<'ast> for LocalUses<'_, '_, F>
where
    F: FnMut(FileScopeId, ExprRef<'ast>) -> bool,
{
    fn visit_expr(&mut self, expression: &'ast ast::Expr) {
        let Self {
            index,
            inspect,
            valid,
        } = self;
        if !*valid {
            return;
        }
        if matches!(expression, ast::Expr::Name(_) | ast::Expr::Subscript(_))
            && index.try_expression_use_id(expression.into()).is_some()
        {
            *valid = inspect(index.expression_scope_id(expression), expression.into());
        }
        if *valid {
            walk_expr(self, expression);
        }
    }
}

pub(super) fn for_binding<'db>(
    db: &'db dyn Db,
    scope: ty_python_core::scope::ScopeId<'db>,
    receiver: &ast::Expr,
) -> Option<Definition<'db>> {
    let receiver = receiver.as_name_expr()?;
    let index = semantic_index(db, scope.program_file(db));
    let definition = local_binding(db, index, scope.file_scope_id(db), receiver)?;
    matches!(definition.kind(db), DefinitionKind::For(_)).then_some(definition)
}

pub(super) fn for_target<'db>(db: &'db dyn Db, definition: Definition<'db>) -> ContentsValue<'db> {
    let DefinitionKind::For(for_stmt) = definition.kind(db) else {
        return ContentsValue::Unavailable;
    };
    let scope = definition.scope(db);
    let file = scope.program_file(db);
    let module = parsed_module(db, file.python_file(db)).load(db);
    let index = semantic_index(db, file);
    let Some(iterable) = for_stmt.iterable(&module).as_name_expr() else {
        return ContentsValue::Unavailable;
    };
    let Some(initializer) = local_binding(db, index, scope.file_scope_id(db), iterable) else {
        return ContentsValue::Unavailable;
    };
    element_contents(db, initializer)
}

#[salsa::tracked(
    returns(clone),
    cycle_initial=|_, _, _| ContentsValue::Pending,
    cycle_fn=|db, cycle, previous: &ContentsValue<'db>, result: ContentsValue<'db>, definition: Definition<'db>| {
        result.cycle_normalized(db, &ProgramEnvironment::from_definition(definition), previous, cycle)
    },
    heap_size=get_size2::GetSize::get_heap_size,
)]
fn element_contents<'db>(db: &'db dyn Db, definition: Definition<'db>) -> ContentsValue<'db> {
    let scope = definition.scope(db);
    let file = scope.program_file(db);
    let module = parsed_module(db, file.python_file(db)).load(db);
    let Some(Producers { initial, appends }) = producers(db, definition, &module) else {
        return ContentsValue::Unavailable;
    };
    let env = ProgramEnvironment::from_scope(scope);
    let mut result: Option<MappingContents<'db>> = None;
    let mut add = |dictionary| {
        let next = MappingContents {
            file,
            dictionary,
            exposed: false,
            value_bound: None,
        };
        result = Some(match result.take() {
            Some(previous) => previous.join(db, &env, &next),
            None => next,
        });
    };
    if !initial.elts.is_empty() {
        let inference =
            StatementInference::Definition(definition, infer_definition_types(db, definition));
        for value in &initial.elts {
            match literal(db, &env, scope, value, &inference) {
                Ok(dictionary) => add(dictionary),
                Err(fallback) => return fallback,
            }
        }
    }
    if appends.is_empty() {
        return result.map_or(ContentsValue::Unavailable, ContentsValue::Mapping);
    }
    let Some(declared) = KnownClass::List
        .to_instance(db, &env)
        .member_lookup_with_policy(db, &env, "append", MemberLookupPolicy::NO_INSTANCE_FALLBACK)
        .place
        .ignore_possibly_undefined()
    else {
        return ContentsValue::Unavailable;
    };
    let Type::BoundMethod(declared) = declared else {
        return ContentsValue::Unavailable;
    };
    let Some(declaration) = declared.function(db) else {
        return ContentsValue::Unavailable;
    };
    for Append {
        statement,
        callee,
        receiver,
        value,
    } in appends
    {
        let inference = infer_statement_types(db, statement);
        if inference.is_provisional() {
            return ContentsValue::Pending;
        }
        let Some(Type::NominalInstance(instance)) = inference.try_expression_type(receiver) else {
            return ContentsValue::Unavailable;
        };
        if !instance.has_known_class(db, KnownClass::List) {
            return ContentsValue::Unavailable;
        }
        let Some(Type::BoundMethod(method)) = inference.try_expression_type(callee) else {
            return ContentsValue::Unavailable;
        };
        let Some(function) = method.function(db) else {
            return ContentsValue::Unavailable;
        };
        if function.definition(db) != declaration.definition(db) {
            return ContentsValue::Unavailable;
        }
        match literal(db, &env, scope, value, &inference) {
            Ok(dictionary) => add(dictionary),
            Err(fallback) => return fallback,
        }
    }
    result.map_or(ContentsValue::Unavailable, ContentsValue::Mapping)
}

fn literal<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    scope: ty_python_core::scope::ScopeId<'db>,
    value: &ast::Expr,
    inference: &StatementInference<'db>,
) -> Result<DictionaryItems<'db>, ContentsValue<'db>> {
    if inference.is_provisional() {
        return Err(ContentsValue::Pending);
    }
    let ast::Expr::Dict(dictionary) = value else {
        return Err(ContentsValue::Unavailable);
    };
    if dictionary.items.iter().any(|item| {
        !item
            .key
            .as_ref()
            .is_some_and(ast::Expr::is_string_literal_expr)
    }) {
        return Err(ContentsValue::Unavailable);
    }
    let mut pending = false;
    let observed = DictionaryItems::expression(db, env, scope, value, &mut |expression| {
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
        Err(ContentsValue::Pending)
    } else {
        observed.map_err(|_| ContentsValue::Unavailable)
    }
}

/// Publish only proved For-row observations; scalar stores and other mappings keep their
/// existing inference. Both subscript return paths still perform ordinary checked dispatch.
pub(crate) fn item_type<'db>(
    db: &'db dyn Db,
    scope: ty_python_core::scope::ScopeId<'db>,
    subscript: &ast::ExprSubscript,
    receiver_type: Type<'db>,
    reachability: &crate::reachability::ReachabilityEvaluationCache<'db>,
) -> Option<Type<'db>> {
    if !super::is_exact_dict(db, receiver_type) {
        return None;
    }
    let key = subscript.slice.as_string_literal_expr()?.value.to_str();
    for_binding(db, scope, &subscript.value)?;
    let dictionary =
        match DictionaryItems::observed(db, scope, &subscript.value, receiver_type, reachability) {
            Ok(dictionary) => dictionary,
            Err(fallback) => match fallback {
                DictionaryFallback::Unavailable => return None,
                DictionaryFallback::Unreachable => return Some(Type::Never),
            },
        };
    dictionary
        .items
        .iter()
        .find(|item| item.name == key && item.is_required())
        .map(|item| item.ty)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::HasType;
    use crate::db::tests::TestDbBuilder;
    use ruff_db::files::system_path_to_file;
    use ruff_db::system::DbWithWritableSystem as _;

    const ORIGINAL: &str = r#"
def text(value: str) -> None: ...
def number(value: int) -> None: ...
def optional(value: str) -> str | None: ...

def checksum(paths: list[str]) -> None:
    entries = []
    for path in paths:
        expected = optional(path)
        entries.append({"name": path, "size": len(path), "expected": expected})
    if not entries:
        return
    names = []
    for entry in entries:
        names.append(entry["name"])
        text(entry["name"])
        number(entry["size"])
        if entry["expected"]:
            expected = entry["expected"]
            text(expected)
    for entry in entries:
        text(entry["name"])
        number(entry["size"])
        if entry["expected"]:
            text(entry["expected"])
    for name in names:
        text(name)
"#;

    fn initializer<'db>(
        db: &'db dyn Db,
        file: ty_python_core::ProgramFile<'db>,
        module: &ParsedModuleRef,
    ) -> Definition<'db> {
        let index = semantic_index(db, file);
        index
            .expression_uses(module)
            .find_map(|(scope, expression, use_id)| {
                let ExprRef::Name(name) = expression else {
                    return None;
                };
                if name.id != "entries" {
                    return None;
                }
                index
                    .use_def_map(scope)
                    .bindings_at_use(use_id)
                    .find_map(|binding| {
                        let DefinitionState::Defined(definition) = binding.binding else {
                            return None;
                        };
                        matches!(
                            definition.kind(db),
                            DefinitionKind::Assignment(_) | DefinitionKind::AnnotatedAssignment(_)
                        )
                        .then_some(definition)
                    })
            })
            .expect("the list is referenced")
    }

    #[test]
    fn automatic_record_original_producers_and_two_consumers() -> anyhow::Result<()> {
        for (second_producer, expected_row, expected_size) in [
            (false, "dict[str, str | int | None]", "int"),
            (
                true,
                "dict[str, str | int | None] | dict[str, str | None]",
                "int | Literal[\"wrong\"]",
            ),
        ] {
            let source = if second_producer {
                ORIGINAL.replace("    if not entries:", "    entries.append({\"name\": \"wrong\", \"size\": \"wrong\", \"expected\": None})\n    if not entries:")
            } else {
                ORIGINAL.to_owned()
            };
            for producer_first in [false, true] {
                let db = TestDbBuilder::new()
                    .with_file("/src/main.py", &source)
                    .build()?;
                let file = db.program_file(system_path_to_file(&db, "/src/main.py")?);
                let module = parsed_module(&db, file.python_file(&db)).load(&db);
                let definition = initializer(&db, file, &module);
                let selected = producers(&db, definition, &module)
                    .expect("original reference geometry is confined");
                assert_eq!(selected.appends.len(), if second_producer { 2 } else { 1 });
                if producer_first {
                    for append in selected.appends {
                        assert!(!infer_statement_types(&db, append.statement).is_provisional());
                    }
                }
                let ContentsValue::Mapping(mapping) = element_contents(&db, definition) else {
                    panic!("original producers must settle to known contents");
                };
                let env = ProgramEnvironment::from_file(file);
                let ordinary = infer_definition_types(&db, definition).binding_type(definition);
                assert_eq!(
                    ordinary.display(&db, &env).to_string(),
                    format!("list[{expected_row}]")
                );
                let items: Vec<_> = mapping
                    .dictionary
                    .items
                    .iter()
                    .map(|item| {
                        (
                            item.name.as_str(),
                            item.ty.display(&db, &env).to_string(),
                            item.is_required(),
                        )
                    })
                    .collect();
                assert_eq!(
                    items,
                    [
                        ("name", "str".to_owned(), true),
                        ("size", expected_size.to_owned(), true),
                        ("expected", "str | None".to_owned(), true)
                    ]
                );
                let diagnostics = crate::types::check_types(&db, file);
                assert_eq!(
                    diagnostics.len(),
                    if second_producer { 2 } else { 0 },
                    "{diagnostics:#?}"
                );
                for diagnostic in diagnostics {
                    assert_eq!(diagnostic.id().as_str(), "invalid-argument-type");
                    let range = diagnostic
                        .primary_span()
                        .expect("source error")
                        .range()
                        .expect("argument range");
                    assert_eq!(&source[range], "entry[\"size\"]");
                }
                let scope = definition.scope(&db);
                for (_, definition, _) in semantic_index(&db, file)
                    .use_def_map(scope.file_scope_id(&db))
                    .definitions_with_usage()
                {
                    let DefinitionKind::For(for_stmt) = definition.kind(&db) else {
                        continue;
                    };
                    if for_stmt
                        .iterable(&module)
                        .as_name_expr()
                        .is_some_and(|name| name.id == "entries")
                    {
                        let row_type =
                            infer_definition_types(&db, definition).binding_type(definition);
                        assert_eq!(row_type.display(&db, &env).to_string(), expected_row);
                    }
                }
            }
        }
        Ok(())
    }

    #[test]
    fn automatic_record_recursive_producers_preserve_fallback_and_errors() -> anyhow::Result<()> {
        let source = r#"
def number(value: int) -> None: ...
def checksum() -> None:
    entries = [{"name": "ok", "size": 1}]
    for entry in entries:
        entries.append({"name": "ok", "size": entry["size"]})
        break
    entries.append({"name": "ok", "size": "wrong"})
    for entry in entries:
        number(entry["size"])
    number("wrong")
"#;
        // Direct recursive values use ordinary inference, which currently loses the field
        // error. A fixed-result conversion grounds the value type and retains that error.
        for (feedback, known) in [("entry[\"size\"]", false), ("int(entry[\"size\"])", true)] {
            let source = source.replace(
                "\"size\": entry[\"size\"]",
                &format!("\"size\": {feedback}"),
            );
            let mut previous_types = None;
            for producer_first in [false, true] {
                let mut db = TestDbBuilder::new()
                    .with_file("/src/main.py", &source)
                    .build()?;
                let file = db.program_file(system_path_to_file(&db, "/src/main.py")?);
                let module = parsed_module(&db, file.python_file(&db)).load(&db);
                let definition = initializer(&db, file, &module);
                let selected =
                    producers(&db, definition, &module).expect("feedback uses are confined");
                if producer_first {
                    for Append {
                        statement,
                        callee: _,
                        receiver: _,
                        value: _,
                    } in selected.appends
                    {
                        let _inference = infer_statement_types(&db, statement);
                    }
                }
                let observed = element_contents(&db, definition);
                assert_eq!(matches!(observed, ContentsValue::Mapping(_)), known);
                if !known {
                    assert!(matches!(
                        observed,
                        ContentsValue::Pending | ContentsValue::Unavailable
                    ));
                }
                let diagnostics = crate::types::check_types(&db, file);
                let mut errors: Vec<_> = diagnostics
                    .iter()
                    .map(|diagnostic| {
                        let range = diagnostic
                            .primary_span()
                            .expect("source diagnostic")
                            .range()
                            .expect("argument span");
                        (diagnostic.id().as_str(), source[range].to_owned())
                    })
                    .collect();
                errors.sort();
                let mut expected = vec![("invalid-argument-type", "\"wrong\"".to_owned())];
                if known {
                    expected.push(("invalid-argument-type", "entry[\"size\"]".to_owned()));
                }
                expected.sort();
                assert_eq!(errors, expected);

                let model = SemanticModel::new(&db, file);
                let env = ProgramEnvironment::from_file(file);
                let mut types: Vec<_> = semantic_index(&db, file)
                    .expression_uses(&module)
                    .filter_map(|(_, expression, _)| {
                        let ExprRef::Subscript(subscript) = expression else {
                            return None;
                        };
                        if subscript
                            .value
                            .as_name_expr()
                            .is_none_or(|name| name.id != "entry")
                        {
                            return None;
                        }
                        let ty = expression.inferred_type(&model).expect("checked subscript");
                        Some((subscript.range(), ty.display(&db, &env).to_string()))
                    })
                    .collect();
                types.sort_by_key(|(range, _)| range.start());
                if let Some(previous) = previous_types.replace(types.clone()) {
                    assert_eq!(types, previous);
                }
                let events = db.take_salsa_events();
                let queries: Vec<_> = salsa::attach(&db, || {
                    events
                        .iter()
                        .filter_map(|event| {
                            let salsa::EventKind::WillIterateCycle { database_key, .. } =
                                event.kind
                            else {
                                return None;
                            };
                            Some(format!("{database_key:?}"))
                        })
                        .collect()
                });
                assert!(
                    queries
                        .iter()
                        .any(|query| query.starts_with("infer_definition_types")
                            || query.starts_with("infer_expression_types_impl")),
                    "the natural collection inference must enter a cycle: {queries:?}"
                );
                if known && !producer_first {
                    assert!(
                        queries
                            .iter()
                            .any(|query| query.starts_with("element_contents")),
                        "fixed-result feedback must enter the observation cycle: {queries:?}"
                    );
                }
            }
        }
        Ok(())
    }

    #[test]
    fn automatic_record_reference_proof_rejects_mutation_and_escape() -> anyhow::Result<()> {
        for (before, after, expected) in [
            ("entries = []", "entries = alias = []", false),
            (
                "entries = []",
                "entries: list[dict[str, object]] = []",
                false,
            ),
            ("entries = []", "entries = []\n    alias = entries", false),
            (
                "entries = []",
                "entries = []\n    alias = entries or []",
                false,
            ),
            (
                "entries = []",
                "entries = []\n    append = entries.append",
                false,
            ),
            ("entries = []", "entries = []\n    corrupt(entries)", false),
            ("entries = []", "entries = []\n    del entries[0]", false),
            ("entries = []", "entries = []\n    entries += []", false),
            (
                "entries = []",
                "entries = []\n    def capture(value=entries): pass",
                false,
            ),
            (
                "entries = []",
                "entries = []\n    class Capture:\n        value = entries",
                false,
            ),
            ("entries = []", "entries = []\n    entries = []", false),
            (
                "entries = []",
                "entries = []\n    def capture(): return entries",
                false,
            ),
            (
                "entries = []",
                "entries = []\n    def reset():\n        nonlocal entries\n        entries = []",
                false,
            ),
            (
                "entries = []",
                "entries = []\n    def other(entries): return entries",
                true,
            ),
            ("if not entries:", "if entries:", true),
            (
                "for entry in entries:",
                "for entry, other in entries:",
                false,
            ),
            (
                "for entry in entries:",
                "for entry in entries:\n        alias = entry",
                false,
            ),
            (
                "for entry in entries:",
                "for entry in entries:\n        entry[\"name\"] = 1",
                false,
            ),
            (
                "for entry in entries:",
                "for entry in entries:\n        entry.clear()",
                false,
            ),
            (
                "for entry in entries:",
                "for entry in entries:\n        entry[\"size\"] += 1",
                false,
            ),
            (
                "for entry in entries:",
                "for entry in entries:\n        corrupt(entry)",
                false,
            ),
            (
                "for entry in entries:",
                "for entry in entries:\n        aggregate = [entry]",
                false,
            ),
            (
                "for entry in entries:",
                "for entry in entries:\n        def capture(): return entry[\"name\"]",
                false,
            ),
            (
                "for entry in entries:",
                "for entry in entries:\n        entry = {}",
                false,
            ),
            (
                "for entry in entries:",
                "for entry in entries:\n        del entry",
                false,
            ),
        ] {
            // Alter the first consumer only, so its mutation must also deny the second seed.
            let source = ORIGINAL.replacen(before, after, 1);
            let db = TestDbBuilder::new()
                .with_file("/src/main.py", &source)
                .build()?;
            let file = db.program_file(system_path_to_file(&db, "/src/main.py")?);
            let module = parsed_module(&db, file.python_file(&db)).load(&db);
            let definition = initializer(&db, file, &module);
            assert_eq!(
                producers(&db, definition, &module).is_some(),
                expected,
                "{source}"
            );
        }
        Ok(())
    }

    #[test]
    fn automatic_record_observation_tracks_producer_and_reference_edits() -> anyhow::Result<()> {
        let source = r#"
def text(value: str) -> None: ...
def checksum() -> None:
    entries = []
    entries.append({"name": "ok", "size": 1})
    for entry in entries:
        text(entry["name"])
    for entry in entries:
        text(entry["name"])
"#;
        let wrong = source.replace("\"name\": \"ok\"", "\"name\": 1");
        let mutated = source.replacen(
            "    for entry in entries:",
            "    for entry in entries:\n        entry[\"name\"] = 1",
            1,
        );
        let mut db = TestDbBuilder::new().with_file("/src/main.py", "").build()?;
        for (source, known, errors) in [
            (source, true, 0),
            (wrong.as_str(), true, 2),
            (source, true, 0),
            (mutated.as_str(), false, 2),
            (source, true, 0),
        ] {
            db.write_file("/src/main.py", source)?;
            let file = db.program_file(system_path_to_file(&db, "/src/main.py")?);
            let module = parsed_module(&db, file.python_file(&db)).load(&db);
            let definition = initializer(&db, file, &module);
            assert_eq!(
                matches!(element_contents(&db, definition), ContentsValue::Mapping(_)),
                known
            );
            let diagnostics = crate::types::check_types(&db, file);
            assert_eq!(diagnostics.len(), errors, "{diagnostics:#?}");
            let mut ranges = FxHashSet::default();
            for diagnostic in diagnostics {
                assert_eq!(diagnostic.id().as_str(), "invalid-argument-type");
                let range = diagnostic
                    .primary_span()
                    .expect("source error")
                    .range()
                    .expect("argument range");
                assert_eq!(&source[range], "entry[\"name\"]");
                assert!(
                    ranges.insert(range),
                    "both consumers must retain their errors"
                );
            }
        }
        Ok(())
    }

    #[test]
    fn automatic_record_empty_list_has_no_row_observation() -> anyhow::Result<()> {
        for (initial, inhabited) in [("[]", false), ("[{}]", true)] {
            let source = format!(
                "def checksum():\n    entries = {initial}\n    for entry in entries:\n        entry[\"missing\"]\n"
            );
            let db = TestDbBuilder::new()
                .with_file("/src/main.py", &source)
                .build()?;
            let file = db.program_file(system_path_to_file(&db, "/src/main.py")?);
            let module = parsed_module(&db, file.python_file(&db)).load(&db);
            let definition = initializer(&db, file, &module);
            match element_contents(&db, definition) {
                ContentsValue::Mapping(mapping) => {
                    assert!(inhabited);
                    assert!(mapping.dictionary.items.is_empty());
                }
                ContentsValue::Unavailable => assert!(!inhabited),
                other => panic!("empty allocation is not unreachable or provisional: {other:?}"),
            }
        }
        Ok(())
    }
}
