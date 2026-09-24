use ruff_db::PythonFile;
use ruff_db::files::system_path_to_file;
use ruff_db::parsed::parsed_module;
use ruff_db::source::source_text;
use ruff_db::system::{DbWithWritableSystem as _, SystemPath};
use ruff_db::testing::{
    assert_function_query_was_not_run, assert_function_query_was_not_run_by_name,
};
use ruff_python_ast::visitor::{Visitor, walk_expr, walk_stmt};
use ruff_python_ast::{NodeIndex, PySourceType};
use ruff_text_size::{Ranged, TextRange, TextSize};
use ty_python_core::Db as _;
use ty_python_core::definition::Definition;
use ty_python_core::definition::{DefinitionKind, ProvidedBinding, ProvidedStatement};
use ty_python_core::{ProgramFileKind, ProvidedAnnotation, semantic_index};

use super::*;
use crate::db::tests::{SourceProvider, TestDb, TestDbBuilder};
use crate::types::{KnownClass, TypedDictFieldBuilder, TypedDictType};
use crate::{HasType, ProgramEnvironment, SemanticModel};

/// Pairs top-level functions by name and their ordinary parameters by position.
/// Signature compatibility is the consumer's responsibility; this fixture exercises
/// annotation ownership after the consumer has selected a correspondence.
/// Functions named `provided_*` also receive a structural return contract when present.
struct ExternalSource;

impl SourceProvider for ExternalSource {
    fn return_type<'db>(
        &self,
        db: &'db TestDb,
        definition: Definition<'db>,
    ) -> Option<ProvidedReturnType<'db>> {
        let DefinitionKind::Function(function) = definition.kind(db) else {
            return None;
        };
        let module = parsed_module(db, definition.python_file(db)).load(db);
        if !function.node(&module).name.starts_with("provided_") {
            return None;
        }
        let source = system_path_to_file(db, "/src/return.pyi").ok()?;
        let value = ProvidedBindingValue::Export {
            file: db.program_file(source),
            name: Name::new_static("value"),
        }
        .resolve_type(db)?;
        let schema = [(
            Name::new_static("value"),
            TypedDictFieldBuilder::new(value).required(true).build(),
        )]
        .into_iter()
        .collect();
        Some(ProvidedReturnType {
            ty: Type::TypedDict(TypedDictType::from_schema_items(db, schema)),
            source: Some(FileRange::new(source, TextRange::new(0.into(), 5.into()))),
        })
    }

    fn statements(&self, _db: &TestDb, _file: ProgramFile<'_>) -> Vec<ProvidedStatement> {
        Vec::new()
    }

    fn annotation<'db>(
        &self,
        db: &'db TestDb,
        file: ProgramFile<'db>,
        owner: NodeIndex,
    ) -> Option<ProvidedAnnotation<'db>> {
        if file.file(db).path(db).as_system_path()?.as_str() != "/src/main.py" {
            return None;
        }
        let target = db.program_file(system_path_to_file(db, "/src/contracts.pyi").ok()?);
        let module = parsed_module(db, file.python_file(db)).load(db);
        let declarations = parsed_module(db, target.python_file(db)).load(db);
        for statement in module.suite() {
            let target_name = match statement {
                ast::Stmt::Assign(assignment) => match assignment.targets.as_slice() {
                    [target] => Some(target),
                    _ => None,
                },
                ast::Stmt::AnnAssign(assignment) => Some(assignment.target.as_ref()),
                _ => None,
            };
            if let Some(ast::Expr::Name(name)) = target_name
                && name.node_index().load() == owner
            {
                let foreign = declarations.suite().iter().find_map(|statement| {
                    let ast::Stmt::AnnAssign(declaration) = statement else {
                        return None;
                    };
                    let ast::Expr::Name(target) = declaration.target.as_ref() else {
                        return None;
                    };
                    (target.id == name.id).then_some(declaration)
                })?;
                return Some(ProvidedAnnotation::External {
                    file: target,
                    owner: foreign.node_index().load(),
                });
            }
            let ast::Stmt::FunctionDef(function) = statement else {
                continue;
            };
            // Deliberately supply mismatched value/function exports to exercise recovery.
            if (function.node_index().load() == owner
                || function
                    .parameters
                    .iter()
                    .any(|parameter| parameter.as_parameter().node_index().load() == owner))
                && let Some(foreign) = declarations.suite().iter().find_map(|statement| {
                    let ast::Stmt::AnnAssign(declaration) = statement else {
                        return None;
                    };
                    let ast::Expr::Name(target) = declaration.target.as_ref() else {
                        return None;
                    };
                    (target.id == function.name.id).then_some(declaration)
                })
            {
                return Some(ProvidedAnnotation::External {
                    file: target,
                    owner: foreign.node_index().load(),
                });
            }
            let Some(foreign) = declarations.suite().iter().find_map(|statement| {
                let ast::Stmt::FunctionDef(declaration) = statement else {
                    return None;
                };
                (declaration.name.as_str() == function.name.as_str()).then_some(declaration)
            }) else {
                continue;
            };
            let foreign_owner =
                if function.node_index().load() == owner {
                    foreign.returns.as_ref()?;
                    foreign.node_index().load()
                } else {
                    let Some(index) = function.parameters.iter().position(|parameter| {
                        parameter.as_parameter().node_index().load() == owner
                    }) else {
                        continue;
                    };
                    let parameter = foreign.parameters.iter().nth(index)?;
                    parameter.as_parameter().annotation()?;
                    parameter.as_parameter().node_index().load()
                };
            return Some(ProvidedAnnotation::External {
                file: target,
                owner: foreign_owner,
            });
        }
        None
    }

    fn binding<'db>(
        &self,
        _db: &'db TestDb,
        _definition: Definition<'db>,
    ) -> ProvidedBindingResolution<'db> {
        ProvidedBindingValue::Unresolved.into()
    }

    fn builtin<'db>(
        &self,
        _db: &'db TestDb,
        _file: ProgramFile<'db>,
        _name: &str,
        _usage: BuiltinUsage,
    ) -> Option<ProvidedBindingValue<'db>> {
        None
    }
}

#[test]
fn supplied_returns_check_bodies_and_track_contract_edits() -> anyhow::Result<()> {
    let mut db = TestDbBuilder::new()
        .with_file(
            "/src/main.py",
            "def provided_make():\n    return {'value': 1}\nobserved = provided_make()['value']\n",
        )
        .with_file("/src/return.pyi", "value: int\n")
        .with_source_provider(ExternalSource)
        .build()?;
    let file = system_path_to_file(&db, "/src/main.py")?;
    for expected in ["int", "str", "int"] {
        db.write_file("/src/return.pyi", format!("value: {expected}\n"))?;
        let diagnostics = db.check_file(file);
        assert_eq!(
            diagnostics.is_empty(),
            expected == "int",
            "{diagnostics:#?}"
        );
        let program_file = db.program_file(file);
        let module = parsed_module(&db, program_file.python_file(&db)).load(&db);
        let ast::Stmt::Assign(observed) = &module.suite()[1] else {
            panic!("expected observed assignment");
        };
        let model = SemanticModel::new(&db, program_file);
        assert_eq!(
            observed
                .value
                .inferred_type(&model)
                .unwrap()
                .display(&db, &model.program_environment())
                .to_string(),
            expected
        );
    }
    Ok(())
}

#[test]
fn supplied_returns_preserve_annotations_and_check_all_exits() -> anyhow::Result<()> {
    let db = TestDbBuilder::new()
        .with_file(
            "/src/main.py",
            "\
def provided_missing():
    return {}
def provided_fallthrough(flag: bool):
    if flag:
        return {'value': 1}
def provided_bare():
    return
def provided_native() -> int:
    return 1
def provided_external():
    return 'ok'
def provided_wrong():
    return 1
",
        )
        .with_file(
            "/src/contracts.pyi",
            "def provided_external() -> str: ...\n",
        )
        .with_file("/src/return.pyi", "value: int\n")
        .with_source_provider(ExternalSource)
        .build()?;
    let file = system_path_to_file(&db, "/src/main.py")?;
    let diagnostics = db.check_file(file);
    assert_eq!(
        diagnostics
            .iter()
            .map(|diagnostic| diagnostic.id().as_str())
            .collect::<Vec<_>>(),
        [
            "invalid-return-type",
            "missing-typed-dict-key",
            "invalid-return-type",
            "invalid-return-type",
            "invalid-return-type"
        ],
        "{diagnostics:#?}"
    );
    let contract = system_path_to_file(&db, "/src/return.pyi")?;
    assert!(
        diagnostics
            .iter()
            .flat_map(Diagnostic::annotations)
            .any(|annotation| annotation.get_span().file()
                == &ruff_db::diagnostic::UnifiedFile::Ty(contract)),
        "{diagnostics:#?}"
    );
    Ok(())
}

#[test]
fn external_annotations_check_implementations_in_their_own_scope() -> anyhow::Result<()> {
    let mut db = TestDbBuilder::new()
        .with_file("/src/main.py", "Scalar = int\ndef helper():\n    return 1\ndef compute(value=1):\n    value = 1\n    return 1\ndef implicit(value):\n    print(value)\ndef native(value: int) -> int:\n    return value\n")
        .with_file("/src/contracts.pyi", "")
        .with_source_provider(ExternalSource)
        .build()?;
    let file = system_path_to_file(&db, "/src/main.py")?;
    let stub = system_path_to_file(&db, "/src/contracts.pyi")?;
    for (scalar, expected) in [
        (
            "str",
            vec![
                "invalid-assignment",
                "invalid-parameter-default",
                "invalid-return-type",
                "invalid-return-type",
            ],
        ),
        ("int", vec!["invalid-return-type"]),
        (
            "str",
            vec![
                "invalid-assignment",
                "invalid-parameter-default",
                "invalid-return-type",
                "invalid-return-type",
            ],
        ),
    ] {
        // Deliberately place the foreign annotations past the end of the implementation.
        db.write_file("/src/contracts.pyi", format!("{}Scalar = {scalar}\ndef compute(value: Scalar = ...) -> Scalar: ...\ndef implicit(value: Scalar) -> Scalar: ...\ndef native(value: str) -> str: ...\n", "# declarations\n".repeat(30)))?;
        let diagnostics = db.check_file(file);
        let mut ids = diagnostics
            .iter()
            .map(|diagnostic| diagnostic.id().as_str())
            .collect::<Vec<_>>();
        ids.sort_unstable();
        assert_eq!(ids, expected, "{diagnostics:#?}");
        for diagnostic in &diagnostics {
            let primary = diagnostic.primary_annotation().unwrap();
            assert_eq!(
                primary.get_span().file(),
                &ruff_db::diagnostic::UnifiedFile::Ty(file)
            );
        }
        let foreign_annotations = diagnostics
            .iter()
            .flat_map(ruff_db::diagnostic::Diagnostic::annotations)
            .filter(|annotation| {
                annotation.get_span().file() == &ruff_db::diagnostic::UnifiedFile::Ty(stub)
            })
            .count();
        // Explicit return and reassignment errors identify the declaring stub.
        assert_eq!(foreign_annotations, if scalar == "str" { 2 } else { 0 });
    }
    let file = db.program_file(file);
    let module = parsed_module(&db, file.python_file(&db)).load(&db);
    let function = module.suite()[2].as_function_def_stmt().unwrap();
    let model = SemanticModel::new(&db, file);
    for owner in [
        function.node_index().load(),
        function.parameters.args[0].parameter.node_index().load(),
    ] {
        assert!(model.enter_provided_annotation(owner).is_none());
    }
    Ok(())
}

#[test]
fn external_annotations_preserve_variadic_and_nominal_types() -> anyhow::Result<()> {
    let db = TestDbBuilder::new()
        .with_file("/src/main.py", "class Item: pass\ndef collect(*items, **labels):\n    labels = 1\n    return items[0]\ndef echo(value):\n    return value\ncollect(Item(), bad=1)\necho([Item()])\necho([1])\n")
        .with_file("/src/contracts.pyi", "from main import Item\ndef collect(*items: Item, **labels: str) -> Item: ...\ndef echo(value: list[Item] | None) -> list[Item] | None: ...\n")
        .with_source_provider(ExternalSource)
        .build()?;
    let file = system_path_to_file(&db, "/src/main.py")?;
    let diagnostics = db.check_file(file);
    assert_eq!(
        diagnostics
            .iter()
            .map(|diagnostic| diagnostic.id().as_str())
            .collect::<Vec<_>>(),
        [
            "invalid-assignment",
            "invalid-argument-type",
            "invalid-argument-type"
        ],
        "{diagnostics:#?}"
    );
    Ok(())
}

#[test]
fn semantic_file_kind_is_independent_of_parser_grammar() -> anyhow::Result<()> {
    let source = "value: int\nplaceholder: int = ...\ndef make(arg: Later = ...) -> int: ...\nclass Later: ...\nobserved = value\n";
    let db = TestDbBuilder::new()
        .with_file("/src/declarations.api", source)
        .with_file("/src/declarations.pyi", source)
        .with_file("/src/declarations.py", "value = 1\n")
        .build()?;
    for (path, grammar, default_kind) in [
        (
            "/src/declarations.api",
            PySourceType::Stub,
            ProgramFileKind::Source,
        ),
        (
            "/src/declarations.pyi",
            PySourceType::Python,
            ProgramFileKind::Stub,
        ),
    ] {
        let physical = system_path_to_file(&db, path)?;
        let program = db.program_file(physical).program(&db);
        let python_file =
            PythonFile::new_with_source_type(&db, physical, program.python_version(&db), grammar);
        let default = ProgramFile::from_python_file(&db, python_file, program);
        assert_eq!(default.kind(&db), default_kind);
        let implementation = ProgramFile::from_python_file_with_kind(
            &db,
            python_file,
            program,
            ProgramFileKind::Source,
        );
        let stub = ProgramFile::from_python_file_with_kind(
            &db,
            python_file,
            program,
            ProgramFileKind::Stub,
        );
        assert_ne!(implementation, stub);
        assert_eq!(implementation.python_file(&db), stub.python_file(&db));
        for file in [implementation, stub, implementation, stub] {
            let module = parsed_module(&db, file.python_file(&db)).load(&db);
            let [ast::Stmt::AnnAssign(assignment), ..] = module.suite().as_slice() else {
                panic!("expected the value declaration");
            };
            let definition = semantic_index(&db, file).expect_single_definition(assignment);
            let resolved = crate::ResolvedDefinition::Definition(definition);
            assert_eq!(resolved.program_file(&db), Some(file));
            let mapped = crate::types::ide_support::map_stub_definition(&db, &resolved, None);
            if file.is_stub(&db) && physical.is_stub(&db) {
                let Some(mapped) = mapped else {
                    panic!("expected the Python implementation");
                };
                let [target] = mapped.as_slice() else {
                    panic!("expected one definition: {mapped:?}");
                };
                assert_eq!(
                    target.focus_range(&db).file(),
                    system_path_to_file(&db, "/src/declarations.py")?
                );
            } else {
                assert!(mapped.is_none(), "{mapped:?}");
            }
            let diagnostics = crate::check_file_unwrap(&db, file);
            if file.is_stub(&db) {
                assert!(diagnostics.is_empty(), "{path}: {diagnostics:#?}");
                let ty = ProvidedBindingValue::Export {
                    file,
                    name: Name::new_static("value"),
                }
                .resolve_type(&db);
                assert_eq!(
                    ty,
                    Some(KnownClass::Int.to_instance(&db, &ProgramEnvironment::from_file(file)))
                );
            } else {
                assert!(
                    diagnostics
                        .iter()
                        .any(|diagnostic| diagnostic.id().as_str() == "invalid-assignment"),
                    "{path}: {diagnostics:#?}"
                );
                assert!(
                    diagnostics
                        .iter()
                        .any(|diagnostic| diagnostic.id().as_str() == "unresolved-reference"),
                    "{path}: {diagnostics:#?}"
                );
            }
        }
    }
    Ok(())
}

#[test]
fn semantic_namespaces_share_python_support_types() -> anyhow::Result<()> {
    let db = TestDbBuilder::new()
        .with_file("/src/native.pyi", "def consume(value: list[int]) -> int: ...\n")
        .with_file("/src/main.py", "from native import consume\nitems: list[int] = [1]\nconsume([1])\nconsume(items)\nconsume(['bad'])\n")
        .build()?;
    let source = system_path_to_file(&db, "/src/main.py")?;
    let default = db.program_file(source).program(&db);
    for namespace in ["first", "second"] {
        let program = ty_python_core::program::Program::with_semantic_namespace(
            &db,
            default.python_platform(&db),
            default.resolver_environment(&db),
            &Name::new(namespace),
        );
        let file = program.program_file(&db, source);
        let diagnostics = crate::check_file_unwrap(&db, file);
        assert_eq!(
            diagnostics
                .iter()
                .map(|diagnostic| diagnostic.id().as_str())
                .collect::<Vec<_>>(),
            ["invalid-argument-type"],
            "{diagnostics:#?}"
        );
        assert_eq!(
            KnownClass::Int.to_instance(&db, &ProgramEnvironment::from_file(file)),
            KnownClass::Int.to_instance(&db, &ProgramEnvironment::from_program(default)),
        );
    }
    Ok(())
}

/// A deliberately small source adapter: `include("name")` exports a native declaration,
/// trailing comments supply assignment, parameter, and return annotations; and
/// `context(callback)` supplies a native context to the callback's ordinary parameters.
struct CommentedSource;

impl SourceProvider for CommentedSource {
    fn exclusions(&self, db: &TestDb, file: ProgramFile<'_>) -> ty_python_core::SourceExclusions {
        #[derive(Default)]
        struct Omitted {
            roots: Vec<NodeIndex>,
            owner: Option<NodeIndex>,
        }
        impl<'ast> Visitor<'ast> for Omitted {
            fn visit_stmt(&mut self, stmt: &'ast ast::Stmt) {
                let previous = self.owner.replace(stmt.node_index().load());
                if matches!(stmt, ast::Stmt::While(_) | ast::Stmt::ClassDef(_)) {
                    self.roots.push(stmt.node_index().load());
                } else {
                    walk_stmt(self, stmt);
                }
                self.owner = previous;
            }
            fn visit_expr(&mut self, expr: &'ast ast::Expr) {
                if matches!(expr, ast::Expr::Named(_) | ast::Expr::EllipsisLiteral(_))
                    || matches!(expr, ast::Expr::Dict(dict) if dict.items.iter().any(|item| item.key.is_none()))
                {
                    self.roots
                        .push(self.owner.expect("expression has a statement owner"));
                } else {
                    walk_expr(self, expr);
                }
            }
        }
        if file
            .file(db)
            .path(db)
            .as_system_path()
            .map(SystemPath::as_str)
            != Some("/src/excluded.py")
        {
            return ty_python_core::SourceExclusions::default();
        }
        let module = parsed_module(db, file.python_file(db)).load(db);
        let mut omitted = Omitted::default();
        omitted.visit_body(module.suite());
        ty_python_core::SourceExclusions::from_statements(omitted.roots.into_iter().map(|node| {
            let ast::AnyRootNodeRef::Stmt(statement) = module.get_by_index(node) else {
                unreachable!()
            };
            statement
        }))
    }

    fn statements(&self, db: &TestDb, file: ProgramFile<'_>) -> Vec<ProvidedStatement> {
        let module = parsed_module(db, file.python_file(db)).load(db);
        module
            .suite()
            .iter()
            .filter_map(|statement| {
                let ast::Stmt::Expr(statement) = statement else {
                    return None;
                };
                let ast::Expr::Call(call) = statement.value.as_ref() else {
                    return None;
                };
                let ast::Expr::Name(function) = call.func.as_ref() else {
                    return None;
                };
                if function.id != "include" {
                    return None;
                }
                let [ast::Expr::StringLiteral(name)] = call.arguments.args.as_ref() else {
                    return None;
                };
                Some(ProvidedStatement {
                    statement: statement.node_index().load(),
                    bindings: Box::from([ProvidedBinding {
                        target: name.node_index().load(),
                        name: Name::new(name.value.to_str()),
                        range: name.range(),
                    }]),
                })
            })
            .collect()
    }

    fn annotation<'db>(
        &self,
        db: &'db TestDb,
        file: ProgramFile<'db>,
        owner: NodeIndex,
    ) -> Option<ProvidedAnnotation<'db>> {
        if file.file(db).path(db).as_system_path()?.as_str() != "/src/main.py" {
            return None;
        }
        let module = parsed_module(db, file.python_file(db)).load(db);
        let source = source_text(db, file.file(db));
        for statement in module.suite() {
            if let ast::Stmt::Assign(assignment) = statement
                && assignment
                    .targets
                    .iter()
                    .any(|target| target.node_index().load() == owner)
            {
                let tail = source[usize::from(assignment.value.end())..]
                    .lines()
                    .next()?;
                let marker = tail.find("# ")?;
                let start = assignment.value.end() + TextSize::try_from(marker + 2).unwrap();
                return Some(ProvidedAnnotation::Range(TextRange::at(
                    start,
                    TextSize::of(&tail[marker + 2..]),
                )));
            }
            let ast::Stmt::FunctionDef(function) = statement else {
                continue;
            };
            let header =
                &source[TextRange::new(function.parameters.end(), function.body.first()?.start())];
            let Some(marker) = header.find("# (") else {
                continue;
            };
            let offset = function.parameters.end() + TextSize::try_from(marker + 3).unwrap();
            let (parameter, returns) = source[usize::from(offset)..].split_once(") -> ")?;
            let range = if owner == function.node_index().load() {
                let start = offset + TextSize::of(parameter) + TextSize::new(5);
                TextRange::at(start, TextSize::of(returns.lines().next()?))
            } else {
                let [parameter_node] = function.parameters.args.as_ref() else {
                    continue;
                };
                if owner != parameter_node.parameter.node_index().load() {
                    continue;
                }
                TextRange::at(offset, TextSize::of(parameter))
            };
            return Some(ProvidedAnnotation::Range(range));
        }
        None
    }

    fn binding<'db>(
        &self,
        db: &'db TestDb,
        definition: Definition<'db>,
    ) -> ProvidedBindingResolution<'db> {
        let file = system_path_to_file(db, "/src/native.pyi").unwrap();
        ProvidedBindingValue::Export {
            file: db.program_file(file),
            name: match definition.kind(db) {
                DefinitionKind::ProvidedBinding(binding) => binding.binding.name.clone(),
                kind => panic!("expected supplied binding, got {kind:?}"),
            },
        }
        .into()
    }

    fn builtin<'db>(
        &self,
        db: &'db TestDb,
        _file: ProgramFile<'db>,
        name: &str,
        usage: BuiltinUsage,
    ) -> Option<ProvidedBindingValue<'db>> {
        if name != "Scalar" {
            return None;
        }
        let file = system_path_to_file(db, "/src/native.pyi").unwrap();
        Some(ProvidedBindingValue::Export {
            file: db.program_file(file),
            name: Name::new(match usage {
                BuiltinUsage::Runtime => "sentinel",
                BuiltinUsage::Annotation => "Scalar",
            }),
        })
    }

    fn parameter_type<'db>(
        &self,
        db: &'db TestDb,
        definition: Definition<'db>,
    ) -> Option<Type<'db>> {
        let file = definition.program_file(db);
        if file.file(db).path(db).as_system_path()?.as_str() != "/src/main.py" {
            return None;
        }
        let module = parsed_module(db, file.python_file(db)).load(db);
        let name = definition.scope(db).name(db, &module);
        for statement in module.suite() {
            let expression = match statement {
                ast::Stmt::Expr(statement) => statement.value.as_ref(),
                ast::Stmt::Assign(statement) => statement.value.as_ref(),
                _ => continue,
            };
            let ast::Expr::Call(call) = expression else {
                continue;
            };
            if call
                .func
                .as_name_expr()
                .is_none_or(|name| name.id != "context")
            {
                continue;
            }
            let [callback] = call.arguments.args.as_ref() else {
                continue;
            };
            let callback_name = match callback {
                ast::Expr::Name(callback) => &callback.id,
                ast::Expr::Attribute(callback) => &callback.attr.id,
                _ => continue,
            };
            if callback_name == name {
                let class = callback_context_class(db, file, call)?;
                return class.to_instance_approximation(db, &ProgramEnvironment::from_file(file));
            }
        }
        None
    }
}

/// The configuration selects an ordinary native class; the call supplies nominal identity.
fn callback_context_class<'db>(
    db: &'db TestDb,
    file: ProgramFile<'db>,
    call: &ast::ExprCall,
) -> Option<Type<'db>> {
    let configuration = system_path_to_file(db, "/src/context.cfg").ok()?;
    let native = system_path_to_file(db, "/src/native.pyi").ok()?;
    let name = source_text(db, configuration);
    let base = ProvidedBindingValue::Export {
        file: db.program_file(native),
        name: Name::new(name.trim()),
    }
    .resolve_type(db)?;
    SemanticModel::new(db, file).provided_class_at_call(
        call,
        ProvidedClass {
            name: Name::new_static("CallbackContext"),
            bases: Box::from([base]),
            class_members: Box::default(),
            instance_fields: ProvidedInstanceFields::default(),
        },
    )
}

#[test]
fn supplied_parameter_types_are_initial_bindings_only() -> anyhow::Result<()> {
    let db = TestDbBuilder::new()
        .with_file("/src/context.cfg", "Context")
        .with_file(
            "/src/native.pyi",
            "from typing import Callable\nclass Context:\n    value: int | None\ndef context(callback: Callable[..., object]) -> type: ...\n",
        )
        .with_file(
            "/src/main.py",
            "from native import context
from typing_extensions import Literal, assert_type
def callback(ctx):
    assert_type(ctx.value, int | None)
    if ctx.value is not None:
        assert_type(ctx.value, int)
    ctx = 'reassigned'
    assert_type(ctx, Literal['reassigned'])
context(callback)
callback(None)
",
        )
        .with_source_provider(CommentedSource)
        .build()?;
    let file = system_path_to_file(&db, "/src/main.py")?;
    let diagnostics = db.check_file(file);
    assert!(diagnostics.is_empty(), "{diagnostics:#?}");
    let callback = crate::place::global_symbol(&db, db.program_file(file), "callback")
        .place
        .expect_type()
        .expect_function_literal();
    let signature = callback.last_definition_signature(&db);
    let [parameter] = signature.parameters().as_slice() else {
        panic!("Expected one callback parameter, got {signature:?}");
    };
    assert_eq!(parameter.annotated_type(), Type::unknown());
    Ok(())
}

#[test]
fn supplied_parameter_types_preserve_annotation_default_and_variadic_types() -> anyhow::Result<()> {
    let db = TestDbBuilder::new()
        .with_file("/src/context.cfg", "Context")
        .with_file(
            "/src/native.pyi",
            "from typing import Callable\nclass Context: ...\ndef context(callback: Callable[..., object]) -> type: ...\n",
        )
        .with_file(
            "/src/main.py",
            "from native import context
from typing_extensions import assert_type
def annotated(ctx: int):
    assert_type(ctx, int)
def supplied(ctx): # (str) -> None
    assert_type(ctx, str)
def defaulted(ctx=1):
    ctx + 1
def variadic(*args, **kwargs):
    args.count(None)
    kwargs.keys()
class Owner:
    value: int
    def method(self):
        assert_type(self.value, int)
context(annotated)
context(supplied)
context(defaulted)
context(variadic)
context(Owner.method)
",
        )
        .with_source_provider(CommentedSource)
        .build()?;
    let file = system_path_to_file(&db, "/src/main.py")?;
    let diagnostics = db.check_file(file);
    assert!(diagnostics.is_empty(), "{diagnostics:#?}");
    Ok(())
}

#[test]
fn supplied_parameter_types_follow_source_native_and_configuration_edits() -> anyhow::Result<()> {
    let source =
        "from native import context\ndef callback(ctx):\n    ctx.value + 1\ncontext(callback)\n";
    let native = "from typing import Callable\nclass Context:\n    value: int\nclass Other:\n    value: str\ndef context(callback: Callable[..., object]) -> type: ...\n";
    let mut db = TestDbBuilder::new()
        .with_file("/src/main.py", source)
        .with_file("/src/native.pyi", native)
        .with_file("/src/context.cfg", "Context")
        .with_source_provider(CommentedSource)
        .build()?;
    let file = system_path_to_file(&db, "/src/main.py")?;
    assert!(db.check_file(file).is_empty());
    db.write_file("/src/context.cfg", "Other")?;
    let diagnostics = db.check_file(file);
    assert_eq!(diagnostics.len(), 1, "{diagnostics:#?}");
    assert_eq!(diagnostics[0].id().as_str(), "unsupported-operator");
    db.write_file(
        "/src/native.pyi",
        native.replace("value: str", "value: int"),
    )?;
    let diagnostics = db.check_file(file);
    assert!(diagnostics.is_empty(), "{diagnostics:#?}");
    let modified_source = source.replace("+ 1", "+ 'text'");
    db.write_file("/src/main.py", &modified_source)?;
    let diagnostics = db.check_file(file);
    assert_eq!(diagnostics.len(), 1, "{diagnostics:#?}");
    assert_eq!(diagnostics[0].id().as_str(), "unsupported-operator");
    db.write_file(
        "/src/main.py",
        modified_source.replace("context(callback)", ""),
    )?;
    let diagnostics = db.check_file(file);
    assert!(diagnostics.is_empty(), "{diagnostics:#?}");
    Ok(())
}

#[test]
fn supplied_class_identity_uses_the_source_call_without_inference() -> anyhow::Result<()> {
    let mut db = TestDbBuilder::new()
        .with_file(
            "/src/main.py",
            "first = missing(callback)\nsecond = missing(callback)\n",
        )
        .build()?;
    let file = system_path_to_file(&db, "/src/main.py")?;
    db.clear_salsa_events();
    {
        let file = db.program_file(file);
        let model = SemanticModel::new(&db, file);
        let module = parsed_module(&db, file.python_file(&db)).load(&db);
        let calls = module
            .suite()
            .iter()
            .map(|statement| {
                statement
                    .as_assign_stmt()
                    .unwrap()
                    .value
                    .as_call_expr()
                    .unwrap()
            })
            .collect::<Vec<_>>();
        let [first, second] = calls.as_slice() else {
            panic!("Expected two source calls");
        };
        let class = |call, name| {
            model
                .provided_class_at_call(
                    call,
                    ProvidedClass {
                        name: Name::new(name),
                        bases: Box::default(),
                        class_members: Box::default(),
                        instance_fields: ProvidedInstanceFields::default(),
                    },
                )
                .unwrap()
        };
        let first_type = class(first, "Context");
        assert_eq!(first_type, class(first, "Context"));
        assert_ne!(first_type, class(second, "Context"));
        assert_ne!(first_type, class(first, "Attributes"));
    }
    let events = db.take_salsa_events();
    for query in [
        "infer_scope_types_impl",
        "infer_expression_types_impl",
        "infer_definition_types",
    ] {
        assert_function_query_was_not_run_by_name(&db, query, None, &events);
    }
    Ok(())
}

#[test]
fn supplied_generic_constructors_keep_type_variables() -> anyhow::Result<()> {
    let db = TestDbBuilder::new()
        .with_file(
            "/src/native.pyi",
            r#"
from typing import Any, Self
class Container[T]:
    def __new__(cls, *args: Any, **kwargs: Any) -> Self: ...
    def __init__[U](self: Container[U], value: U) -> None: ...
    def value(self) -> T: ...
"#,
        )
        .with_file(
            "/src/main.py",
            r#"
from typing_extensions import Literal, assert_type
include("Container")
first = Container(1)
second = Container("two")
assert_type(first.value(), Literal[1])
assert_type(second.value(), Literal["two"])
"#,
        )
        .with_source_provider(CommentedSource)
        .build()?;
    let source = system_path_to_file(&db, "/src/main.py")?;
    let default = db.program_file(source).program(&db);
    let program = ty_python_core::program::Program::with_semantic_namespace(
        &db,
        default.python_platform(&db),
        default.resolver_environment(&db),
        &Name::new_static("embedded"),
    );
    let diagnostics = crate::check_file_unwrap(&db, program.program_file(&db, source));
    assert!(diagnostics.is_empty(), "{diagnostics:#?}");
    Ok(())
}

#[test]
fn supplied_declarations_follow_source_and_export_edits() -> anyhow::Result<()> {
    let source = "include(\"consume\")\ndef identity(value): # (Scalar) -> str\n    consume(value)\n    return value\nidentity(\"bad\")\n";
    let native = "Scalar = int\nsentinel: str\ndef consume(value: int) -> int: ...\n";
    let mut db = TestDbBuilder::new()
        .with_file("/src/main.py", source)
        .with_file("/src/native.pyi", native)
        .with_source_provider(CommentedSource)
        .build()?;
    let file = system_path_to_file(&db, "/src/main.py")?;
    {
        let program_file = db.program_file(file);
        let model = SemanticModel::new(&db, program_file);
        let parsed = parsed_module(&db, program_file.python_file(&db)).load(&db);
        let [ast::Stmt::Expr(statement), ..] = parsed.suite().as_slice() else {
            panic!("expected a supplied declaration");
        };
        let ast::Expr::Call(call) = statement.value.as_ref() else {
            panic!("expected the include call");
        };
        let [ast::Expr::StringLiteral(name)] = call.arguments.args.as_ref() else {
            panic!("expected the supplied name");
        };
        assert!(model.enter_string_annotation(name).is_none());
    }
    let diagnostics = db.check_file(file);
    let mut ids = diagnostics
        .iter()
        .map(|diagnostic| diagnostic.id().as_str())
        .collect::<Vec<_>>();
    ids.sort_unstable();
    assert_eq!(
        ids,
        ["invalid-argument-type", "invalid-return-type"],
        "{diagnostics:#?}"
    );

    db.write_file(
        "/src/native.pyi",
        native.replace("value: int", "value: str"),
    )?;
    let diagnostics = db.check_file(file);
    let mut ids = diagnostics
        .iter()
        .map(|diagnostic| diagnostic.id().as_str())
        .collect::<Vec<_>>();
    ids.sort_unstable();
    assert_eq!(
        ids,
        [
            "invalid-argument-type",
            "invalid-argument-type",
            "invalid-return-type"
        ],
        "{diagnostics:#?}"
    );

    db.write_file("/src/main.py", source.replace("(Scalar)", "(str)"))?;
    let diagnostics = db.check_file(file);
    assert!(diagnostics.is_empty(), "{diagnostics:#?}");

    db.write_file(
        "/src/main.py",
        source.replace("consume(value)", "value = None"),
    )?;
    let diagnostics = db.check_file(file);
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.id().as_str() == "invalid-assignment"),
        "{diagnostics:#?}"
    );
    Ok(())
}

#[test]
fn function_annotation_hover_uses_the_owning_signature_scope() -> anyhow::Result<()> {
    for (source, generic) in [
        (
            "def identity(value): # (list[Scalar]) -> list[Scalar]\n    return value\n",
            false,
        ),
        (
            "def identity[T](value): # (list[T]) -> list[T]\n    return value\n",
            true,
        ),
    ] {
        let db = TestDbBuilder::new()
            .with_file("/src/main.py", source)
            .with_file("/src/native.pyi", "Scalar = int\nsentinel: str\n")
            .with_source_provider(CommentedSource)
            .build()?;
        let file = db.program_file(system_path_to_file(&db, "/src/main.py")?);
        let module = parsed_module(&db, file.python_file(&db)).load(&db);
        let function = module.suite()[0].as_function_def_stmt().unwrap();
        let parameter = &function.parameters.args[0].parameter;
        let model = SemanticModel::new(&db, file);
        let env = model.program_environment();
        for owner in [function.node_index().load(), parameter.node_index().load()] {
            let Some(ProvidedAnnotation::Range(range)) = db.provided_annotation(file, owner) else {
                panic!("expected a local annotation");
            };
            let element = model
                .provided_annotation_type_at(owner, range.start() + TextSize::new(5))
                .unwrap();
            if generic {
                assert!(matches!(element, Type::TypeVar(_)), "{element:?}");
            } else {
                assert_eq!(element, KnownClass::Int.to_instance(&db, &env));
            }
            assert_eq!(
                model.provided_annotation_type_at(owner, range.end()),
                Some(KnownClass::List.to_specialized_instance(&db, &env, &[element])),
            );
            let (parsed, annotation_model) = model.enter_provided_annotation(owner).unwrap();
            assert_eq!(
                parsed.expr().inferred_type(&annotation_model),
                Some(KnownClass::List.to_specialized_instance(&db, &env, &[element])),
            );
        }
    }
    Ok(())
}

#[test]
fn supplied_annotation_names_use_the_declaration_scope() -> anyhow::Result<()> {
    let db = TestDbBuilder::new()
        .with_file(
            "/src/main.py",
            "class Item: pass\ndef identity(value): # (Item) -> Item\n    Item = str\n    return value\n",
        )
        .with_source_provider(CommentedSource)
        .build()?;
    let file = db.program_file(system_path_to_file(&db, "/src/main.py")?);
    let module = parsed_module(&db, file.python_file(&db)).load(&db);
    let class = module.suite()[0].as_class_def_stmt().unwrap();
    let function = module.suite()[1].as_function_def_stmt().unwrap();
    let expected = semantic_index(&db, file).expect_single_definition(class);
    let model = SemanticModel::new(&db, file);
    for owner in [
        function.node_index().load(),
        function.parameters.args[0].parameter.node_index().load(),
    ] {
        let (parsed, annotation_model) = model.enter_provided_annotation(owner).unwrap();
        assert_eq!(
            crate::definitions_for_name(
                &annotation_model,
                "Item",
                parsed.expr().into(),
                crate::ImportAliasResolution::PreserveAliases,
            ),
            [crate::ResolvedDefinition::Definition(expected)],
        );
    }
    Ok(())
}

#[test]
fn supplied_annotation_models_require_active_valid_ranges() -> anyhow::Result<()> {
    for source in [
        "def identity(value: str) -> str: # (int) -> int\n    return value\n",
        "def identity(value): # ([) -> [\n    return value\n",
    ] {
        let db = TestDbBuilder::new()
            .with_file("/src/main.py", source)
            .with_source_provider(CommentedSource)
            .build()?;
        let file = db.program_file(system_path_to_file(&db, "/src/main.py")?);
        let module = parsed_module(&db, file.python_file(&db)).load(&db);
        let function = module.suite()[0].as_function_def_stmt().unwrap();
        let model = SemanticModel::new(&db, file);
        for owner in [
            function.node_index().load(),
            function.parameters.args[0].parameter.node_index().load(),
        ] {
            assert!(model.enter_provided_annotation(owner).is_none(), "{source}");
        }
    }
    Ok(())
}

#[test]
fn nested_supplied_annotations_follow_source_edits() -> anyhow::Result<()> {
    let source = "def identity(value): # (list[\"Scalar\"]) -> list[\"Scalar\"]\n    return value\nitems = [] # list[\"Scalar\"]\n";
    let mut db = TestDbBuilder::new()
        .with_file("/src/main.py", source)
        .with_file("/src/native.pyi", "Scalar = int\n")
        .with_source_provider(CommentedSource)
        .build()?;
    let file = system_path_to_file(&db, "/src/main.py")?;
    for (prefix, name, expected) in [
        ("", "int", KnownClass::Int),
        ("", "str", KnownClass::Str),
        ("# moved\n", "str", KnownClass::Str),
        ("", "int", KnownClass::Int),
    ] {
        db.write_file("/src/main.py", format!("{prefix}{source}"))?;
        db.write_file("/src/native.pyi", format!("Scalar = {name}\n"))?;
        let diagnostics = db.check_file(file);
        assert!(diagnostics.is_empty(), "{diagnostics:#?}");
        let file = db.program_file(file);
        let module = parsed_module(&db, file.python_file(&db)).load(&db);
        let function = module.suite()[0].as_function_def_stmt().unwrap();
        let assignment = module.suite()[1].as_assign_stmt().unwrap();
        let model = SemanticModel::new(&db, file);
        for owner in [
            function.node_index().load(),
            function.parameters.args[0].parameter.node_index().load(),
            assignment.targets[0].node_index().load(),
        ] {
            let Some(ProvidedAnnotation::Range(range)) = db.provided_annotation(file, owner) else {
                panic!("expected a local annotation");
            };
            let env = model.program_environment();
            assert_eq!(
                model.provided_annotation_type_at(owner, range.end()),
                Some(KnownClass::List.to_specialized_instance(
                    &db,
                    &env,
                    &[expected.to_instance(&db, &env)],
                )),
            );
            let (parsed, annotation_model) = model.enter_provided_annotation(owner).unwrap();
            let string = parsed
                .expr()
                .as_subscript_expr()
                .unwrap()
                .slice
                .as_string_literal_expr()
                .unwrap();
            let (quoted, quoted_model) = annotation_model.enter_string_annotation(string).unwrap();
            assert_eq!(
                quoted.expr().inferred_type(&quoted_model),
                Some(expected.to_instance(&db, &env)),
            );
        }
    }
    Ok(())
}

#[test]
fn supplied_builtin_usage_selects_the_declaration() -> anyhow::Result<()> {
    let db = TestDbBuilder::new()
        .with_file(
            "/src/main.py",
            "value: Scalar = 1\nsentinel: str = Scalar\n",
        )
        .with_file("/src/native.pyi", "Scalar = int\nsentinel: str\n")
        .with_source_provider(CommentedSource)
        .build()?;
    let file = system_path_to_file(&db, "/src/main.py")?;
    let diagnostics = db.check_file(file);
    assert!(diagnostics.is_empty(), "{diagnostics:#?}");
    Ok(())
}

#[test]
fn supplied_assignment_annotations_contextualize_and_constrain_bindings() -> anyhow::Result<()> {
    let source = "items = [] # list[Scalar]\nitems.append('wrong')\nitems = ['wrong']\nruntime = Scalar # str\n";
    let mut db = TestDbBuilder::new()
        .with_file("/src/main.py", source)
        .with_file("/src/native.pyi", "Scalar = int\nsentinel: str\n")
        .with_source_provider(CommentedSource)
        .build()?;
    let file = system_path_to_file(&db, "/src/main.py")?;
    let diagnostics = db.check_file(file);
    let mut ids = diagnostics
        .iter()
        .map(|diagnostic| diagnostic.id().as_str())
        .collect::<Vec<_>>();
    ids.sort_unstable();
    assert_eq!(
        ids,
        ["invalid-argument-type", "invalid-assignment"],
        "{diagnostics:#?}"
    );

    let annotation_start = TextSize::try_from(source.find("list[Scalar]").unwrap())?;
    let annotation_range = TextRange::at(annotation_start, TextSize::of("list[Scalar]"));
    assert!(
        diagnostics.iter().any(|diagnostic| {
            diagnostic.id().as_str() == "invalid-assignment"
                && diagnostic
                    .secondary_annotations()
                    .any(|annotation| annotation.get_span().range() == Some(annotation_range))
        }),
        "{diagnostics:#?}"
    );

    let file = db.program_file(file);
    let module = parsed_module(&db, file.python_file(&db)).load(&db);
    let assignment = module.suite()[0].as_assign_stmt().unwrap();
    let owner = assignment.targets[0].node_index().load();
    let model = SemanticModel::new(&db, file);
    let env = model.program_environment();
    assert_eq!(
        model.provided_annotation_type_at(owner, annotation_start + TextSize::new(1)),
        Some(KnownClass::List.to_class_literal(&db, &env)),
    );
    assert_eq!(
        model.provided_annotation_type_at(owner, annotation_range.end()),
        Some(KnownClass::List.to_specialized_instance(
            &db,
            &env,
            &[KnownClass::Int.to_instance(&db, &env)],
        )),
    );
    assert_eq!(
        model.provided_annotation_type_at(owner, annotation_start + TextSize::new(6)),
        Some(KnownClass::Int.to_instance(&db, &env)),
    );

    db.write_file("/src/main.py", source.replace("list[Scalar]", "list[str]"))?;
    let diagnostics = db.check_file(system_path_to_file(&db, "/src/main.py")?);
    assert!(diagnostics.is_empty(), "{diagnostics:#?}");
    Ok(())
}

#[test]
fn assignment_annotation_hover_does_not_infer_an_unrelated_initializer() -> anyhow::Result<()> {
    let source = "items = [] # list[int]\nunrelated = missing\n";
    let mut db = TestDbBuilder::new()
        .with_file("/src/main.py", source)
        .with_source_provider(CommentedSource)
        .build()?;
    let file = system_path_to_file(&db, "/src/main.py")?;
    db.clear_salsa_events();
    {
        let file = db.program_file(file);
        let module = parsed_module(&db, file.python_file(&db)).load(&db);
        let assignment = module.suite()[0].as_assign_stmt().unwrap();
        let owner = assignment.targets[0].node_index().load();
        let model = SemanticModel::new(&db, file);
        let offset = TextSize::try_from(source.find("int").unwrap())?;
        assert_eq!(
            model.provided_annotation_type_at(owner, offset),
            Some(KnownClass::Int.to_instance(&db, &model.program_environment())),
        );
    }
    let events = db.take_salsa_events();
    let file = db.program_file(file);
    let module = parsed_module(&db, file.python_file(&db)).load(&db);
    let assignment = module.suite()[1].as_assign_stmt().unwrap();
    let target = assignment.targets[0].as_name_expr().unwrap();
    let definition = semantic_index(&db, file).expect_single_definition(target);
    assert_function_query_was_not_run(
        &db,
        crate::types::infer_definition_types,
        definition,
        &events,
    );
    Ok(())
}

#[test]
fn supplied_assignment_qualifiers_use_native_validation() -> anyhow::Result<()> {
    let db = TestDbBuilder::new()
        .with_file(
            "/src/main.py",
            "from typing import Final, ClassVar\nx = 1 # Final[int]\nx = 2\ny = 1 # ClassVar[int]\n",
        )
        .with_source_provider(CommentedSource)
        .build()?;
    let file = system_path_to_file(&db, "/src/main.py")?;
    let diagnostics = db.check_file(file);
    let mut ids = diagnostics
        .iter()
        .map(|diagnostic| diagnostic.id().as_str())
        .collect::<Vec<_>>();
    ids.sort_unstable();
    assert_eq!(
        ids,
        ["invalid-assignment", "invalid-type-form"],
        "{diagnostics:#?}"
    );
    Ok(())
}

#[test]
fn supplied_assignment_aliases_use_native_validation() -> anyhow::Result<()> {
    for source in [
        "from typing import TypeAlias\nBad: TypeAlias = 1\n",
        "from typing import TypeAlias\nBad = 1 # TypeAlias\n",
    ] {
        let db = TestDbBuilder::new()
            .with_file("/src/main.py", source)
            .with_source_provider(CommentedSource)
            .build()?;
        let file = system_path_to_file(&db, "/src/main.py")?;
        let diagnostics = db.check_file(file);
        assert_eq!(
            diagnostics
                .iter()
                .map(|diagnostic| diagnostic.id().as_str())
                .collect::<Vec<_>>(),
            ["invalid-type-form"],
            "{source}\n{diagnostics:#?}",
        );
    }
    Ok(())
}

#[test]
fn supplied_assignment_type_checking_validation_runs_once() -> anyhow::Result<()> {
    for source in [
        "TYPE_CHECKING: bool = True\n",
        "TYPE_CHECKING = True # bool\n",
    ] {
        let db = TestDbBuilder::new()
            .with_file("/src/main.py", source)
            .with_source_provider(CommentedSource)
            .build()?;
        let file = system_path_to_file(&db, "/src/main.py")?;
        let diagnostics = db.check_file(file);
        assert_eq!(
            diagnostics
                .iter()
                .map(|diagnostic| diagnostic.id().as_str())
                .collect::<Vec<_>>(),
            ["invalid-type-checking-constant"],
            "{source}\n{diagnostics:#?}",
        );
    }
    Ok(())
}

#[test]
fn malformed_assignment_annotation_still_checks_the_value() -> anyhow::Result<()> {
    let db = TestDbBuilder::new()
        .with_file("/src/main.py", "value = missing # list[\n")
        .with_source_provider(CommentedSource)
        .build()?;
    let file = system_path_to_file(&db, "/src/main.py")?;
    let diagnostics = db.check_file(file);
    let mut ids = diagnostics
        .iter()
        .map(|diagnostic| diagnostic.id().as_str())
        .collect::<Vec<_>>();
    ids.sort_unstable();
    assert_eq!(
        ids,
        ["invalid-type-form", "unresolved-reference"],
        "{diagnostics:#?}"
    );
    Ok(())
}

#[test]
fn excluded_source_has_no_bindings_or_flow_effects() -> anyhow::Result<()> {
    use crate::HasType;
    let mut db = TestDbBuilder::new()
        .with_source_provider(CommentedSource)
        .with_file("/src/excluded.py", "value = 1\n")
        .build()?;
    let file = system_path_to_file(&db, "/src/excluded.py")?;
    for source in [
        "value = 1\nobserved = value\n",
        "value = 1\nwhile True:\n    value = 'bad'\nclass value: pass\nfor item in [0]:\n    while True:\n        value = 'bad'\n    opaque = (value := 'bad')\nif not ...:\n    left = value\nelse:\n    right = value\nobserved = value\n",
        "value = 1\nobserved = value\n",
    ] {
        db.write_file("/src/excluded.py", source)?;
        let program_file = db.program_file(file);
        let module = parsed_module(&db, program_file.python_file(&db)).load(&db);
        let model = SemanticModel::new(&db, program_file);
        let ast::Stmt::Assign(last) = module.suite().last().unwrap() else {
            unreachable!()
        };
        assert_eq!(
            last.value
                .inferred_type(&model)
                .unwrap()
                .display(&db, &model.program_environment())
                .to_string(),
            "Literal[1]"
        );
        let diagnostics = crate::check_file_unwrap(&db, program_file);
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        if let Some(while_statement) = module
            .suite()
            .get(1)
            .filter(|stmt| matches!(stmt, ast::Stmt::While(_)))
        {
            assert_eq!(model.scope(while_statement.into()), None);
        }
    }
    Ok(())
}

#[test]
fn external_assignment_annotations_keep_scope_and_edits() -> anyhow::Result<()> {
    let mut db = TestDbBuilder::new()
        .with_file(
            "/src/main.py",
            "Scalar = int\nvalues = [1]\nnative: int = 1\n",
        )
        .with_file("/src/contracts.pyi", "")
        .with_source_provider(ExternalSource)
        .build()?;
    let file = system_path_to_file(&db, "/src/main.py")?;
    let stub = system_path_to_file(&db, "/src/contracts.pyi")?;
    for scalar in ["str", "int", "str"] {
        db.write_file(
            "/src/contracts.pyi",
            format!(
                "{}Scalar = {scalar}\nvalues: list[Scalar]\nnative: str\n",
                "# foreign declaration\n".repeat(20)
            ),
        )?;
        let diagnostics = db.check_file(file);
        assert_eq!(
            diagnostics.len(),
            usize::from(scalar == "str"),
            "{diagnostics:#?}"
        );
        for diagnostic in diagnostics {
            assert_eq!(diagnostic.id().as_str(), "invalid-assignment");
            assert_eq!(
                diagnostic.primary_annotation().unwrap().get_span().file(),
                &ruff_db::diagnostic::UnifiedFile::Ty(file)
            );
            assert!(
                diagnostic
                    .annotations()
                    .iter()
                    .any(|annotation| annotation.get_span().file()
                        == &ruff_db::diagnostic::UnifiedFile::Ty(stub)),
                "{diagnostic:#?}"
            );
        }
    }
    Ok(())
}

#[test]
fn external_assignment_annotations_preserve_qualifiers() -> anyhow::Result<()> {
    let db = TestDbBuilder::new()
        .with_file("/src/main.py", "value = 1\nvalue += 2\n")
        .with_file(
            "/src/contracts.pyi",
            "from typing import Final\nvalue: Final[int]\n",
        )
        .with_source_provider(ExternalSource)
        .build()?;
    let file = system_path_to_file(&db, "/src/main.py")?;
    let diagnostics = db.check_file(file);
    assert_eq!(diagnostics.len(), 1, "{diagnostics:#?}");
    assert_eq!(diagnostics[0].id().as_str(), "invalid-assignment");
    assert!(
        diagnostics[0].headline_message().contains("Final"),
        "{diagnostics:#?}"
    );
    Ok(())
}

#[test]
fn external_assignment_annotations_exclude_type_aliases() -> anyhow::Result<()> {
    let db = TestDbBuilder::new()
        .with_file("/src/main.py", "value = 1\n")
        .with_file(
            "/src/contracts.pyi",
            "from typing import TypeAlias\nvalue: TypeAlias = str\n",
        )
        .with_source_provider(ExternalSource)
        .build()?;
    let file = system_path_to_file(&db, "/src/main.py")?;
    assert!(db.check_file(file).is_empty());
    Ok(())
}

#[test]
fn external_assignment_annotation_cycles_keep_initializer_evidence() -> anyhow::Result<()> {
    let db = TestDbBuilder::new()
        .with_file("/src/main.py", "value = 1\n")
        .with_file(
            "/src/contracts.pyi",
            "from main import value as Alias\nvalue: Alias\n",
        )
        .with_source_provider(ExternalSource)
        .build()?;
    let file = system_path_to_file(&db, "/src/main.py")?;
    assert!(db.check_file(file).is_empty());
    let file = db.program_file(file);
    let model = SemanticModel::new(&db, file);
    let module = parsed_module(&db, file.python_file(&db)).load(&db);
    let ast::Stmt::Assign(assignment) = &module.suite()[0] else {
        panic!("expected assignment");
    };
    let ty = assignment.value.inferred_type(&model).unwrap();
    assert_eq!(
        ty.display(&db, &model.program_environment()).to_string(),
        "Literal[1]"
    );
    Ok(())
}

#[test]
fn external_assignment_annotations_do_not_become_signature_annotations() -> anyhow::Result<()> {
    let db = TestDbBuilder::new()
        .with_file(
            "/src/main.py",
            "def value(argument): return argument\nobserved = value('ok')\n",
        )
        .with_file(
            "/src/contracts.pyi",
            "from typing import Final\nvalue: Final[int]\n",
        )
        .with_source_provider(ExternalSource)
        .build()?;
    let file = system_path_to_file(&db, "/src/main.py")?;
    assert!(db.check_file(file).is_empty());
    let file = db.program_file(file);
    let module = parsed_module(&db, file.python_file(&db)).load(&db);
    let function = module.suite()[0].as_function_def_stmt().unwrap();
    assert!(
        crate::types::string_annotation::SourceAnnotation::new(&db, file, function, None).is_none()
    );
    assert!(
        crate::types::string_annotation::SourceAnnotation::new(
            &db,
            file,
            &function.parameters.args[0].parameter,
            None
        )
        .is_none()
    );
    let model = SemanticModel::new(&db, file);
    let observed = module.suite()[1].as_assign_stmt().unwrap();
    assert_eq!(observed.value.inferred_type(&model), Some(Type::unknown()));
    Ok(())
}
