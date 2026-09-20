use ruff_db::files::system_path_to_file;
use ruff_db::parsed::parsed_module;
use ruff_db::source::source_text;
use ruff_db::system::DbWithWritableSystem as _;
use ruff_python_ast::{self as ast, HasNodeIndex, NodeIndex};
use ruff_text_size::{Ranged, TextRange, TextSize};
use ty_python_core::definition::{Definition, DefinitionKind, ProvidedBinding, ProvidedStatement};

use super::*;
use crate::ProgramEnvironment;
use crate::db::tests::{SourceProvider, TestDb, TestDbBuilder};
use crate::types::KnownClass;

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
/// and a comment following a function header supplies its parameter and return types.
struct CommentedSource;

impl SourceProvider for CommentedSource {
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

    fn annotation(
        &self,
        db: &TestDb,
        file: ProgramFile<'_>,
        owner: NodeIndex,
    ) -> Option<TextRange> {
        let module = parsed_module(db, file.python_file(db)).load(db);
        let source = source_text(db, file.file(db));
        for statement in module.suite() {
            let ast::Stmt::FunctionDef(function) = statement else {
                continue;
            };
            let header =
                &source[TextRange::new(function.parameters.end(), function.body.first()?.start())];
            let offset =
                function.parameters.end() + TextSize::try_from(header.find("# (")? + 3).unwrap();
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
            return Some(range);
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
