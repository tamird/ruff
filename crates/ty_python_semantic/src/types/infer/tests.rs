use std::assert_matches;
use std::fmt::Write;

use super::builder::TypeInferenceBuilder;
use crate::db::tests::{TestDb, TestDbBuilder, setup_db};
use crate::lint::{LintSource, RuleSelection};
use crate::place::symbol;
use crate::place::{ConsideredDefinitions, Place, PlaceAndQualifiers};
use crate::types::{KnownClass, KnownInstanceType, check_types};
use crate::{FunctionInferenceMode, HasType};
use ruff_db::diagnostic::{Diagnostic, DiagnosticId, Severity};
use ruff_db::files::{File, system_path_to_file};
use ruff_db::source::source_text;
use ruff_db::system::DbWithWritableSystem as _;
use ruff_db::testing::{assert_function_query_was_not_run, assert_function_query_was_run};
use ruff_python_ast::PythonVersion;
use salsa::Database as _;
use salsa::plumbing::AsId;
use ty_python_core::definition::Definition;
use ty_python_core::program::Program;
use ty_python_core::scope::FileScopeId;
use ty_python_core::{
    ProgramFile, TestProgramDb as _, global_scope, place_table, semantic_index, use_def_map,
};

use super::*;

fn program_file(db: &TestDb, file: File) -> ProgramFile<'_> {
    ProgramFile::new(db, file, db.program_environment().program(db))
}

fn global_symbol<'db>(db: &'db TestDb, file: File, name: &str) -> PlaceAndQualifiers<'db> {
    crate::place::global_symbol(db, program_file(db, file), name)
}

#[track_caller]
fn get_symbol<'db>(
    db: &'db TestDb,
    file_name: &str,
    scopes: &[&str],
    symbol_name: &str,
) -> Place<'db> {
    let file = system_path_to_file(db, file_name).expect("file to exist");
    let file = program_file(db, file);
    let module = parsed_module(db, file.python_file(db)).load(db);
    let index = semantic_index(db, file);
    let mut file_scope_id = FileScopeId::global();
    let mut scope = file_scope_id.to_scope_id(db, file);
    for expected_scope_name in scopes {
        file_scope_id = index
            .child_scopes(file_scope_id)
            .next()
            .unwrap_or_else(|| panic!("scope of {expected_scope_name}"))
            .0;
        scope = file_scope_id.to_scope_id(db, file);
        assert_eq!(scope.name(db, &module), *expected_scope_name);
    }

    symbol(db, scope, symbol_name, ConsideredDefinitions::EndOfScope).place
}

#[track_caller]
fn assert_diagnostic_messages(diagnostics: &[Diagnostic], expected: &[&str]) {
    let messages: Vec<&str> = diagnostics
        .iter()
        .map(Diagnostic::headline_message)
        .collect();
    assert_eq!(&messages, expected);
}

#[track_caller]
fn assert_file_diagnostics(db: &TestDb, filename: &str, expected: &[&str]) {
    let file = system_path_to_file(db, filename).unwrap();
    let diagnostics = check_types(db, program_file(db, file));

    assert_diagnostic_messages(&diagnostics, expected);
}

#[track_caller]
fn assert_revealed_type(db: &TestDb, filename: &str, expected: &str) {
    let file = system_path_to_file(db, filename).unwrap();
    let diagnostics = check_types(db, program_file(db, file));
    assert_eq!(diagnostics.len(), 1, "{diagnostics:#?}");

    let diagnostic = &diagnostics[0];
    assert_eq!(diagnostic.id(), DiagnosticId::RevealedType);
    let expected = format!("`{expected}`");
    assert_eq!(
        diagnostic
            .primary_annotation()
            .and_then(|annotation| annotation.get_message()),
        Some(expected.as_str())
    );
}

#[test]
fn keyword_field_factory_context() -> anyhow::Result<()> {
    let mut db = TestDbBuilder::new()
        .with_python_version(PythonVersion::PY312)
        .with_keyword_field_factory(|db, definition| {
            let DefinitionKind::Function(function) = definition.kind(db) else {
                return false;
            };
            let module = parsed_module(db, definition.program_file(db).python_file(db)).load(db);
            function.node(&module).name.as_str() == "record"
        })
        .build()?;
    for (declaration, expected_type, argument, revealed) in [
        (
            r#"T = TypeVar('T')
class Parent(Protocol[T]):
    @property
    def run(self) -> Callable[[T], T]: ...
class Row(Parent[str], Protocol): ..."#,
            "Row",
            "run=lambda value: (reveal_type(value), value)[1]",
            "str",
        ),
        (
            r#"class Parent[T](Protocol):
    @property
    def run(self) -> Callable[[T], T]: ...
class Row(Parent[str], Protocol): ..."#,
            "Row",
            "run=lambda value: (reveal_type(value), value)[1]",
            "str",
        ),
        (
            "class Row(Protocol):\n    @property\n    def run(self) -> Callable[[Self], str]: ...",
            "Row",
            "run=lambda value: (reveal_type(value), 'ok')[1]",
            "Row",
        ),
        (
            "class Row(Protocol):\n    run: Callable[[str], str]",
            "Row",
            "run=lambda value: (reveal_type(value), value)[1]",
            "Unknown",
        ),
        (
            "class Row(Protocol):\n    def run(self, value: str) -> str: ...",
            "Row",
            "run=lambda value: (reveal_type(value), value)[1]",
            "Unknown",
        ),
        (
            r#"class Row(Protocol):
    @property
    def run(self) -> Callable[[str], str]: ...
    @run.setter
    def run(self, value: Callable[[str], str]) -> None: ..."#,
            "Row",
            "run=lambda value: (reveal_type(value), value)[1]",
            "Unknown",
        ),
        (
            "class Row(Protocol):\n    @property\n    def run(self) -> Callable[[str], str]: ...",
            "Row | None",
            "run=lambda value: (reveal_type(value), value)[1]",
            "Unknown",
        ),
        (
            "class Row(Protocol):\n    @property\n    def run(self) -> Callable[[str], str]: ...",
            "Row",
            "other=lambda value: (reveal_type(value), value)[1]",
            "Unknown",
        ),
        (
            "class Row(Protocol):\n    @property\n    def run(self) -> Callable[[str], str]: ...",
            "Row",
            "**{'run': lambda value: (reveal_type(value), value)[1]}",
            "Unknown",
        ),
    ] {
        db.write_file(
            "/src/main.py",
            format!(
                r#"from typing import Any, Callable, Protocol, Self, TypeVar, reveal_type
{declaration}
def record(**fields: object) -> Any: ...
value: {expected_type} = record({argument})
"#
            ),
        )?;
        assert_revealed_type(&db, "/src/main.py", revealed);
    }
    db.write_file(
        "/src/main.py",
        r#"from typing import Any, Callable, Protocol
class Row(Protocol):
    @property
    def run(self) -> Callable[[str], str]: ...
def record(**fields: int) -> Any: ...
value: Row = record(run=lambda value: value.lower())
"#,
    )?;
    assert_file_diagnostics(
        &db,
        "/src/main.py",
        &["Argument to function `record` is incorrect"],
    );
    Ok(())
}

#[test]
fn function_inference_facts() -> anyhow::Result<()> {
    let mut db = setup_db();
    db.write_dedented(
        "/src/main.py",
        r#"
        unrelated: int = "bad"

        def needs_int(value: int) -> int:
            return value

        def clean() -> int:
            return 1

        def bad_body() -> int:
            return "bad"

        def suppressed_body() -> int:
            return "bad"  # ty: ignore[invalid-return-type]

        def dead_body() -> int:
            if False:
                return "bad"  # ty: ignore[invalid-return-type]
            return 1

        def bad_default(value: int = needs_int("bad")) -> int:
            return value

        def suppressed_default(value: int = needs_int("bad")) -> int:  # ty: ignore[invalid-argument-type]
            return value
        "#,
    )?;
    let file = system_path_to_file(&db, "/src/main.py")?;
    let model = crate::SemanticModel::new(&db, program_file(&db, file));
    for (name, errors, diagnostics_or_suppressions) in [
        ("clean", false, false),
        ("bad_body", true, true),
        ("suppressed_body", false, true),
        ("dead_body", false, false),
        ("bad_default", true, true),
        ("suppressed_default", false, true),
    ] {
        let definition = first_public_binding(&db, file, name);
        let crate::FunctionInferenceFacts {
            return_type_correspondence: _,
            has_cycle_recovery,
            has_errors,
            has_diagnostics_or_suppressions,
            has_unproved_requirements: _,
        } = model.function_inference_facts(definition).unwrap();
        assert_eq!(
            (
                has_cycle_recovery,
                has_errors,
                has_diagnostics_or_suppressions,
            ),
            (false, errors, diagnostics_or_suppressions),
            "{name}",
        );
    }
    assert!(
        model
            .function_inference_facts(first_public_binding(&db, file, "unrelated"))
            .is_none()
    );
    Ok(())
}

#[test]
fn conservative_global_inputs() -> anyhow::Result<()> {
    let mut db = setup_db();
    db.write_dedented(
        "/src/dependency.pyi",
        r#"
        from typing import Any, Callable
        OPAQUE: list[Any]
        CALLBACKS: list[Callable[..., object]]
        "#,
    )?;
    db.write_dedented(
        "/src/main.py",
        r#"
        from collections.abc import Iterable, Sequence
        from dependency import OPAQUE, CALLBACKS

        def collect(extra: Iterable[object] | None) -> Sequence[object]:
            fresh = []
            fresh.append(1)
            if not extra:
                return OPAQUE
            out = list(OPAQUE)
            for item in extra:
                if item not in out:
                    out.append(item)
            return out

        def mutate() -> None:
            OPAQUE.append("x")
            OPAQUE[0] = "x"

        def invoke() -> None:
            CALLBACKS[0]()
            CALLBACKS[0](named=1)

        def wants_int(value: int) -> int:
            return value

        def launder_argument() -> int:
            return wants_int(OPAQUE[0])

        def launder_return() -> list[object]:
            return OPAQUE[0]

        def fresh_laundering() -> int:
            xs = []
            xs.append(OPAQUE[0])
            return wants_int(xs[0])

        def unselected() -> None:
            OPAQUE.append("ordinary")
            CALLBACKS[0](ordinary=1)
        "#,
    )?;
    let file = system_path_to_file(&db, "/src/main.py")?;
    let signature = |db: &TestDb| {
        global_symbol(db, file, "collect")
            .place
            .expect_type()
            .display(db, &db.program_environment())
            .to_string()
    };
    let original_signature = signature(&db);
    let local_type = |db: &TestDb, name: &str| {
        let module = program_file(db, file);
        let index = semantic_index(db, module);
        let Some((scope, _)) = index.child_scopes(FileScopeId::global()).next() else {
            panic!("collector body scope missing");
        };
        symbol(
            db,
            scope.to_scope_id(db, module),
            name,
            ConsideredDefinitions::AllReachable,
        )
        .place
        .expect_type()
        .display(db, &db.program_environment())
        .to_string()
    };
    assert_file_diagnostics(&db, "/src/main.py", &[]);
    assert_eq!(local_type(&db, "out"), "list[Any]");
    let selected = [
        "collect",
        "mutate",
        "invoke",
        "launder_argument",
        "launder_return",
        "fresh_laundering",
    ]
    .map(str::to_owned)
    .to_vec();
    db.select_function_inference(Some((
        file,
        selected,
        crate::FunctionInferenceMode::Conservative,
    )));
    let diagnostics = check_types(&db, program_file(&db, file));
    let selected_out = local_type(&db, "out");
    let selected_fresh = local_type(&db, "fresh");
    assert_eq!(selected_out, "list[object]");
    assert_eq!(selected_fresh, "list[int]");
    let source = source_text(&db, file);
    let actual: Vec<_> = diagnostics
        .iter()
        .map(|diagnostic| {
            let Some(range) = diagnostic.primary_span().and_then(|span| span.range()) else {
                panic!("diagnostic has no source range: {diagnostic:?}");
            };
            let start = usize::from(range.start());
            let line_start = source[..start].rfind('\n').map_or(0, |offset| offset + 1);
            let line_end = source[start..]
                .find('\n')
                .map_or(source.len(), |offset| start + offset);
            (
                diagnostic.id().to_string(),
                source[line_start..line_end].trim().to_owned(),
            )
        })
        .collect();
    assert_eq!(
        actual,
        [
            ("invalid-argument-type", "OPAQUE.append(\"x\")"),
            ("invalid-assignment", "OPAQUE[0] = \"x\""),
            ("call-top-callable", "CALLBACKS[0]()"),
            ("call-top-callable", "CALLBACKS[0](named=1)"),
            ("invalid-argument-type", "return wants_int(OPAQUE[0])"),
            ("invalid-return-type", "return OPAQUE[0]"),
            ("invalid-argument-type", "return wants_int(xs[0])"),
        ]
        .map(|(id, line)| (id.to_owned(), line.to_owned()))
    );
    assert_eq!(signature(&db), original_signature);
    assert_eq!(
        global_symbol(&db, file, "OPAQUE")
            .place
            .expect_type()
            .display(&db, &db.program_environment())
            .to_string(),
        "list[Any]"
    );
    db.select_function_inference(None);
    assert_file_diagnostics(&db, "/src/main.py", &[]);
    assert_eq!(signature(&db), original_signature);
    assert_eq!(local_type(&db, "out"), "list[Any]");
    Ok(())
}

#[test]
fn selected_function_contract_signatures() -> anyhow::Result<()> {
    let mut db = TestDbBuilder::new()
        .with_python_version(PythonVersion::PY313)
        .build()?;
    let source = r#"
from typing import Any, Callable, Iterator, TypeGuard, TypeIs, overload

def identity[T](value: T) -> T: return value
def plain(values: list[Any]) -> list[Any]: return values
alias = plain
def defaulted(values: list[Any] = []) -> list[Any]: return values
def variadic(*values: Any) -> object: return values
async def asynchronous(value: int) -> int: return value
def generator() -> Iterator[int]: yield 1
def generic[T](value: T) -> T: return value
def predicate(value: object) -> TypeIs[int]: return False
def guard(value: object) -> TypeGuard[int]: return False
def unresolved(value) -> int: return 1
@overload
def overloaded(value: int) -> int: ...
def overloaded(value: int | str) -> int: return 1
"#;
    db.write_file("/src/main.py", source)?;
    let file = system_path_to_file(&db, "/src/main.py")?;
    let names = [
        "plain",
        "defaulted",
        "variadic",
        "asynchronous",
        "generator",
        "generic",
        "predicate",
        "guard",
        "unresolved",
        "overloaded",
    ];
    for mode in [
        FunctionInferenceMode::Default,
        FunctionInferenceMode::OutputProof,
        FunctionInferenceMode::Conservative,
        FunctionInferenceMode::Default,
    ] {
        db.select_function_inference(Some((file, names.map(str::to_owned).to_vec(), mode)));
        for name in names.into_iter().chain(["alias"]) {
            let ty = global_symbol(&db, file, name).place.expect_type();
            let selected = ty
                .as_function_literal()
                .and_then(|function| function.selected_contract_signature(&db));
            assert_eq!(
                selected.is_some(),
                mode != FunctionInferenceMode::Default && matches!(name, "plain" | "alias"),
                "{name}: {mode:?}"
            );
        }
        let plain = global_symbol(&db, file, "plain").place.expect_type();
        assert_eq!(plain, global_symbol(&db, file, "alias").place.expect_type());
        let altered = plain.top_materialization(&db, &db.program_environment());
        assert!(
            altered
                .as_function_literal()
                .and_then(|function| function.selected_contract_signature(&db))
                .is_none()
        );
    }
    db.select_function_inference(Some((
        file,
        vec!["plain".to_owned()],
        FunctionInferenceMode::Conservative,
    )));
    for (source, expected) in [
        (
            source.replace("plain(values: list[Any])", "plain(values: list[Any] = [])"),
            false,
        ),
        (source.to_owned(), true),
        (source.replace("def plain(", "async def plain("), false),
        (source.to_owned(), true),
        (source.replace("def plain(", "@identity\ndef plain("), false),
        (source.to_owned(), true),
    ] {
        db.write_file("/src/main.py", source)?;
        let function = global_symbol(&db, file, "plain")
            .place
            .expect_type()
            .as_function_literal()
            .unwrap();
        assert_eq!(
            function.selected_contract_signature(&db).is_some(),
            expected
        );
    }
    Ok(())
}

#[test]
fn conservative_function_call_contexts() -> anyhow::Result<()> {
    for (argument, expected) in [
        ("callback", &[] as &[(&str, &str)]),
        ("lambda values: len(values)", &[]),
        (
            "lambda values: values.append(1) or 1",
            &[("invalid-argument-type", "1")],
        ),
    ] {
        let mut db = setup_db();
        db.write_file(
            "/src/main.py",
            format!(
                "from typing import Any, Callable

def forward(callback: Callable[[list[Any]], int]) -> Callable[[list[Any]], int]:
    return callback

def make(callback: Callable[[list[Any]], int]) -> Callable[[list[Any]], int]:
    return forward({argument})
"
            ),
        )?;
        let file = system_path_to_file(&db, "/src/main.py")?;
        let signature = |db: &TestDb| {
            global_symbol(db, file, "forward")
                .place
                .expect_type()
                .display(db, &db.program_environment())
                .to_string()
        };
        let original = signature(&db);
        for conservative in [false, true, false] {
            db.select_function_inference(conservative.then(|| {
                (
                    file,
                    vec![
                        "forward".to_owned(),
                        "make".to_owned(),
                        "<lambda>".to_owned(),
                    ],
                    crate::FunctionInferenceMode::Conservative,
                )
            }));
            let program = program_file(&db, file);
            let diagnostics = check_types(&db, program);
            let source = source_text(&db, file);
            let actual = diagnostics
                .iter()
                .map(|diagnostic| {
                    let range = diagnostic
                        .primary_span()
                        .and_then(|span| span.range())
                        .unwrap();
                    (diagnostic.id().to_string(), &source[range])
                })
                .collect::<Vec<_>>();
            let expected = if conservative { expected } else { &[] };
            assert_eq!(
                actual,
                expected
                    .iter()
                    .map(|(id, source)| ((*id).to_owned(), *source))
                    .collect::<Vec<_>>(),
                "{argument}, conservative={conservative}"
            );
            assert_eq!(signature(&db), original);
            let model = crate::SemanticModel::new(&db, program);
            let parsed = parsed_module(&db, program.python_file(&db)).load(&db);
            let Some(ast::Stmt::FunctionDef(function)) = parsed.suite().last() else {
                panic!("expected make");
            };
            let [ast::Stmt::Return(statement)] = function.body.as_slice() else {
                panic!("expected return");
            };
            let result = statement
                .value
                .as_deref()
                .unwrap()
                .inferred_type(&model)
                .unwrap();
            assert_eq!(
                result.is_equivalent_to(
                    &db,
                    &db.program_environment(),
                    result.top_materialization(&db, &db.program_environment())
                ),
                conservative,
                "{argument}"
            );
        }
    }
    Ok(())
}

#[test]
fn conservative_lambda_inputs() -> anyhow::Result<()> {
    use crate::HasType;
    use ty_python_core::scope::NodeWithScopeRef;

    for (
        parameters,
        expression,
        ordinary_signature,
        bounded_signature,
        ordinary_binding,
        bounded_binding,
        ordinary_diagnostics,
        bounded_diagnostics,
    ) in [
        (
            Some("values: list[Any]"),
            "lambda values: len(values)",
            "(values: list[Any]) -> int",
            "(values: Top[list[Any]]) -> int",
            "list[Any]",
            "Top[list[Any]]",
            &[] as &[(&str, &str)],
            &[] as &[(&str, &str)],
        ),
        (
            Some("values: list[Any]"),
            "lambda values: values.append(1)",
            "(values: list[Any]) -> None",
            "(values: Top[list[Any]]) -> None",
            "list[Any]",
            "Top[list[Any]]",
            &[] as &[(&str, &str)],
            &[("invalid-argument-type", "1")] as &[(&str, &str)],
        ),
        (
            Some("values: list[Any]"),
            "lambda values=DEFAULT: values",
            "(values: list[Any]) -> list[Any]",
            "(values: Top[list[Any]]) -> Top[list[Any]]",
            "list[Any]",
            "Top[list[Any]]",
            &[] as &[(&str, &str)],
            &[] as &[(&str, &str)],
        ),
        (
            Some("values: list[Any] = ..."),
            "lambda values=DEFAULT: values",
            "(values: list[Any] = ...) -> list[Any]",
            "(values: Top[list[Any]] = ...) -> Top[list[Any]]",
            "list[Any]",
            "Top[list[Any]]",
            &[] as &[(&str, &str)],
            &[] as &[(&str, &str)],
        ),
        (
            Some("values: int = ..."),
            "lambda values='bad': values + 1",
            "(values: int = \"bad\") -> Unknown",
            "(values: int = \"bad\") -> Unknown",
            "int | Literal[\"bad\"]",
            "int | Literal[\"bad\"]",
            &[("unsupported-operator", "values + 1")] as &[(&str, &str)],
            &[("unsupported-operator", "values + 1")] as &[(&str, &str)],
        ),
        (
            Some("*values: list[Any]"),
            "lambda *values: values[0].append(1)",
            "(*values: list[Any]) -> None",
            "(*values: Top[list[Any]]) -> None",
            "tuple[list[Any], ...]",
            "tuple[Top[list[Any]], ...]",
            &[] as &[(&str, &str)],
            &[("invalid-argument-type", "1")] as &[(&str, &str)],
        ),
        (
            Some("**values: list[Any]"),
            "lambda **values: values['first'].append(1)",
            "(**values: list[Any]) -> None",
            "(**values: Top[list[Any]]) -> None",
            "dict[str, list[Any]]",
            "dict[str, Top[list[Any]]]",
            &[] as &[(&str, &str)],
            &[("invalid-argument-type", "1")] as &[(&str, &str)],
        ),
        (
            Some("**values: Any"),
            "lambda **values: values.update(added=1)",
            "(**values: Any) -> None",
            "(**values: object) -> None",
            "dict[str, Any]",
            "dict[str, object]",
            &[] as &[(&str, &str)],
            &[] as &[(&str, &str)],
        ),
        (
            None,
            "lambda values: values",
            "(values) -> Unknown",
            "(values) -> Unknown",
            "Unknown",
            "Unknown",
            &[] as &[(&str, &str)],
            &[] as &[(&str, &str)],
        ),
        (
            Some("values: Missing"),
            "lambda values: values",
            "(values: Unknown) -> Unknown",
            "(values: Unknown) -> Unknown",
            "Unknown",
            "Unknown",
            &[("unresolved-reference", "Missing")] as &[(&str, &str)],
            &[("unresolved-reference", "Missing")] as &[(&str, &str)],
        ),
        (
            Some("values: list[Missing]"),
            "lambda values: values",
            "(values: list[Unknown]) -> list[Unknown]",
            "(values: list[Unknown]) -> list[Unknown]",
            "list[Unknown]",
            "list[Unknown]",
            &[("unresolved-reference", "Missing")] as &[(&str, &str)],
            &[("unresolved-reference", "Missing")] as &[(&str, &str)],
        ),
    ] {
        let mut db = setup_db();
        let (protocol, result) = if let Some(parameters) = parameters {
            (
                format!(
                    "class Callback(Protocol):\n    def __call__(self, {parameters}) -> object: ...\n"
                ),
                "Callback",
            )
        } else {
            (String::new(), "object")
        };
        db.write_file(
            "/src/main.py",
            format!(
                "from typing import Any, Protocol
DEFAULT: list[Any] = []
{protocol}def make() -> {result}:
    return {expression}
"
            ),
        )?;
        let file = system_path_to_file(&db, "/src/main.py")?;
        let signature = |db: &TestDb| {
            global_symbol(db, file, "make")
                .place
                .expect_type()
                .display(db, &db.program_environment())
                .to_string()
        };
        let original_signature = signature(&db);
        for (selection, expected_signature, expected_binding, expected_diagnostics) in [
            (
                None,
                ordinary_signature,
                ordinary_binding,
                ordinary_diagnostics,
            ),
            (
                Some("<lambda>"),
                bounded_signature,
                bounded_binding,
                bounded_diagnostics,
            ),
            (
                None,
                ordinary_signature,
                ordinary_binding,
                ordinary_diagnostics,
            ),
        ] {
            db.select_function_inference(selection.map(|name| {
                (
                    file,
                    vec![name.to_owned()],
                    crate::FunctionInferenceMode::Conservative,
                )
            }));
            let program = program_file(&db, file);
            let diagnostics = check_types(&db, program);
            let source = source_text(&db, file);
            assert_eq!(
                diagnostics
                    .iter()
                    .map(|diagnostic| {
                        let range = diagnostic
                            .primary_span()
                            .and_then(|span| span.range())
                            .expect("diagnostic has a source range");
                        (diagnostic.id().to_string(), &source[range])
                    })
                    .collect::<Vec<_>>(),
                expected_diagnostics
                    .iter()
                    .map(|(id, source)| ((*id).to_owned(), *source))
                    .collect::<Vec<_>>(),
                "{expression}: {selection:?}"
            );
            let model = crate::SemanticModel::new(&db, program);
            let parsed = parsed_module(&db, program.python_file(&db)).load(&db);
            let Some(ast::Stmt::FunctionDef(function)) = parsed.suite().last() else {
                panic!("expected make")
            };
            let [ast::Stmt::Return(statement)] = function.body.as_slice() else {
                panic!("expected return")
            };
            let lambda_expression = statement.value.as_deref().expect("expected return value");
            let ast::Expr::Lambda(lambda) = lambda_expression else {
                panic!("expected lambda")
            };
            let actual = lambda_expression.inferred_type(&model).unwrap();
            assert_eq!(
                actual.display(&db, &db.program_environment()).to_string(),
                expected_signature,
                "{expression}: {selection:?}"
            );
            let scope = semantic_index(&db, program)
                .node_scope(NodeWithScopeRef::Lambda(lambda))
                .to_scope_id(&db, program);
            let binding = symbol(&db, scope, "values", ConsideredDefinitions::AllReachable)
                .place
                .expect_type();
            assert_eq!(
                binding.display(&db, &db.program_environment()).to_string(),
                expected_binding,
                "{expression}: {selection:?}"
            );
            assert_eq!(signature(&db), original_signature);
        }
    }
    Ok(())
}

#[test]
fn conservative_parameter_inputs() -> anyhow::Result<()> {
    let mut db = setup_db();
    db.write_dedented(
        "/src/main.py",
        r#"
        from typing import Any, Callable

        def collect(values: list[Any]) -> list[object]:
            out = list(values)
            out.append(1)
            return out

        def mutate(values: list[Any]) -> None:
            values.append(1)
            values[0] = 1

        def narrowed(values: list[Any] | None) -> None:
            if values is not None:
                values.append(2)

        def invoke(callback: Callable[..., int]) -> int:
            callback()
            return 1

        def captured(callback: Callable[..., int]) -> Callable[[], int]:
            return lambda: callback()

        def forward(callback: Callable[..., int]) -> Callable[..., int]:
            return callback

        def variadic(*values: Any, **fields: Any) -> object:
            fields["added"] = 1
            return values[0]

        def keyword_items(**fields: list[Any]) -> None:
            fields["added"] = []
            fields["first"].append(4)

        def keyword_alias(values: dict[str, Any], **fields: Any) -> None:
            fields = values
            fields["aliased"] = 1

        def unselected(values: list[Any]) -> None:
            values.append(3)
        "#,
    )?;
    let file = system_path_to_file(&db, "/src/main.py")?;
    let names = [
        "collect",
        "mutate",
        "narrowed",
        "invoke",
        "captured",
        "forward",
        "variadic",
        "keyword_items",
        "keyword_alias",
    ];
    let signatures = |db: &TestDb| {
        names.map(|name| {
            global_symbol(db, file, name)
                .place
                .expect_type()
                .display(db, &db.program_environment())
                .to_string()
        })
    };
    let original = signatures(&db);
    assert_file_diagnostics(&db, "/src/main.py", &[]);
    db.select_function_inference(Some((
        file,
        names.map(str::to_owned).to_vec(),
        crate::FunctionInferenceMode::Conservative,
    )));
    let diagnostics = check_types(&db, program_file(&db, file));
    let source = source_text(&db, file);
    let actual: Vec<_> = diagnostics
        .iter()
        .map(|diagnostic| {
            let Some(range) = diagnostic.primary_span().and_then(|span| span.range()) else {
                panic!("diagnostic has no source range: {diagnostic:?}");
            };
            let start = usize::from(range.start());
            let line_start = source[..start].rfind('\n').map_or(0, |offset| offset + 1);
            let line_end = source[start..]
                .find('\n')
                .map_or(source.len(), |offset| start + offset);
            (
                diagnostic.id().to_string(),
                source[line_start..line_end].trim().to_owned(),
            )
        })
        .collect();
    assert_eq!(
        actual,
        [
            ("invalid-argument-type", "values.append(1)"),
            ("invalid-assignment", "values[0] = 1"),
            ("invalid-argument-type", "values.append(2)"),
            ("call-top-callable", "callback()"),
            ("call-top-callable", "return lambda: callback()"),
            ("invalid-argument-type", "fields[\"first\"].append(4)"),
            ("invalid-assignment", "fields[\"aliased\"] = 1"),
        ]
        .map(|(id, line)| (id.to_owned(), line.to_owned()))
    );
    assert_eq!(signatures(&db), original);
    db.select_function_inference(None);
    assert_file_diagnostics(&db, "/src/main.py", &[]);
    assert_eq!(signatures(&db), original);
    Ok(())
}

#[test]
fn conservative_assignment_contexts() -> anyhow::Result<()> {
    use crate::HasType;

    for (
        annotation,
        body,
        result,
        ordinary_type,
        conservative_type,
        ordinary_diagnostics,
        conservative_diagnostics,
    ) in [
        (
            "dict[str, list[Any]]",
            "values = dict(values)",
            "values",
            "dict[str, list[Any]]",
            "dict[str, Top[list[Any]]]",
            vec![],
            vec![],
        ),
        (
            "dict[str, list[Any]]",
            "values = dict(values)\n    values['key'].append(1)",
            "values",
            "dict[str, list[Any]]",
            "dict[str, Top[list[Any]]]",
            vec![],
            vec![("invalid-argument-type", "1")],
        ),
        (
            "list[Any]",
            "values = []\n    values.append(1)",
            "values",
            "list[Any]",
            "list[int]",
            vec![],
            vec![],
        ),
        (
            "list[int]",
            "values = []\n    values.append('bad')",
            "values",
            "list[int]",
            "list[int]",
            vec![("invalid-argument-type", "'bad'")],
            vec![("invalid-argument-type", "'bad'")],
        ),
        (
            "dict[str, list[Any]]",
            "copied = {key: value for key, value in values.items()}",
            "copied",
            "dict[str, list[Any]]",
            "dict[str, Top[list[Any]]]",
            vec![],
            vec![],
        ),
        (
            "dict[str, list[Any]]",
            "copied = {key: value for key, value in values.items()}\n    copied['key'].append(1)",
            "copied",
            "dict[str, list[Any]]",
            "dict[str, Top[list[Any]]]",
            vec![],
            vec![("invalid-argument-type", "1")],
        ),
        (
            "dict[str, list[Any]]",
            "copied = {key: value for key, value in values.items()}\n    mutate(copied)",
            "copied",
            "dict[str, list[Any]]",
            "dict[str, Top[list[Any]]]",
            vec![],
            vec![("invalid-argument-type", "copied")],
        ),
    ] {
        let mut db = setup_db();
        db.write_file(
            "/src/main.py",
            format!(
                r#"from typing import Any

def mutate(values: dict[str, list[Any]]) -> None:
    values["key"].append(1)

def collect(values: {annotation}) -> int:
    {body}
    return len({result})
"#
            ),
        )?;
        let file = system_path_to_file(&db, "/src/main.py")?;
        let signature = |db: &TestDb| {
            global_symbol(db, file, "collect")
                .place
                .expect_type()
                .display(db, &db.program_environment())
                .to_string()
        };
        let original_signature = signature(&db);
        for (mode, expected_type, expected_diagnostics) in [
            (None, ordinary_type, &ordinary_diagnostics),
            (
                Some(crate::FunctionInferenceMode::Conservative),
                conservative_type,
                &conservative_diagnostics,
            ),
            (None, ordinary_type, &ordinary_diagnostics),
        ] {
            db.select_function_inference(mode.map(|mode| (file, vec!["collect".to_owned()], mode)));
            let diagnostics = check_types(&db, program_file(&db, file));
            let source = source_text(&db, file);
            assert_eq!(
                diagnostics
                    .iter()
                    .map(|diagnostic| {
                        let range = diagnostic
                            .primary_span()
                            .and_then(|span| span.range())
                            .expect("diagnostic has a source range");
                        (diagnostic.id().to_string(), &source[range])
                    })
                    .collect::<Vec<_>>(),
                expected_diagnostics
                    .iter()
                    .map(|(id, argument)| ((*id).to_owned(), *argument))
                    .collect::<Vec<_>>(),
                "{body}"
            );
            let model = crate::SemanticModel::new(&db, program_file(&db, file));
            let definition = first_public_binding(&db, file, "collect");
            let DefinitionKind::Function(function) = definition.kind(&db) else {
                panic!("collect is a function");
            };
            let parsed = parsed_module(&db, program_file(&db, file).python_file(&db)).load(&db);
            let Some(ast::Stmt::Return(statement)) = function.node(&parsed).body.last() else {
                panic!("collect ends with a return");
            };
            let Some(ast::Expr::Call(call)) = statement.value.as_deref() else {
                panic!("collect returns a collection length");
            };
            let value = call.arguments.args.first().expect("len has one argument");
            assert_eq!(
                value
                    .inferred_type(&model)
                    .unwrap()
                    .display(&db, &db.program_environment())
                    .to_string(),
                expected_type,
                "{body}"
            );
            assert_eq!(signature(&db), original_signature);
        }
    }
    Ok(())
}

#[test]
fn declared_outputs_preserve_input_and_storage_domains() -> anyhow::Result<()> {
    let mut db = setup_db();
    db.write_dedented(
        "/src/main.py",
        r#"
        from typing import Any, Callable, Concatenate, Generic, Protocol, TypeVar, TypedDict, cast
        from typing_extensions import ReadOnly
        from ty_extensions._internal import Unknown

        def finite(value: int) -> int:
            return value
        def object_input(value: object) -> str:
            return str(value)
        def string_input(value: str) -> str:
            return value
        def wrong(value: int) -> str:
            return str(value)
        def unknown(value: int) -> Unknown:
            return value
        def only_strings(values: list[str]) -> int:
            return len(values[0])
        def higher(callback: Callable[..., int]) -> int:
            return 1
        def higher_return(value: int) -> Callable[[int], int]:
            return finite
        def missing_input(value) -> int:
            value.missing()
            return 1
        class OpaqueInput:
            def __call__(self, value) -> int:
                value.missing()
                return 1
        def consume(callback: Callable[[Any], int]) -> int:
            return callback(1)
        opaque_input = cast(OpaqueInput, None)
        nominal_input = cast(Callable[[OpaqueInput], int], None)
        unknown_list = cast(list[Unknown], None)
        any_list = cast(list[Any], None)
        T_contra = TypeVar("T_contra", contravariant=True)
        class Consumer(Generic[T_contra]):
            pass
        unknown_consumer = cast(Consumer[Unknown], None)
        any_consumer = cast(Consumer[Any], None)
        class UnknownWrite:
            value: Unknown
        class AnyWrite(Protocol):
            value: Any
        unknown_write = cast(UnknownWrite, None)
        any_write = cast(AnyWrite, None)
        class NamedRemainder(Protocol):
            def __call__(self, *, name: str, **kwargs: Any) -> int: ...
        named_remainder = cast(NamedRemainder, None)

        class Actual:
            @property
            def opaque(self) -> Callable[[int], int]: ...
        class Opaque(Protocol):
            @property
            def opaque(self) -> Callable[..., int]: ...
        class MixedActual:
            @property
            def opaque(self) -> Callable[[int], int]: ...
            @property
            def checked(self) -> Callable[[list[str]], int]: ...
        class Mixed(Protocol):
            @property
            def opaque(self) -> Callable[..., int]: ...
            @property
            def checked(self) -> Callable[[list[Any]], int]: ...
        class MutableActual:
            opaque: Callable[[int], int]
        class Mutable(Protocol):
            opaque: Callable[..., int]
        class ActualFields(TypedDict):
            value: str
        class ReadFields(TypedDict):
            value: ReadOnly[Any]
        class WriteFields(TypedDict):
            value: Any
        actual_fields = cast(ActualFields, None)
        read_fields = cast(ReadFields, None)
        write_fields = cast(WriteFields, None)
        class Missing:
            pass
        class AnyRead(Protocol):
            @property
            def value(self) -> Any: ...
        class ActualRead:
            @property
            def value(self) -> str: ...
        missing = cast(Missing, None)
        any_read = cast(AnyRead, None)
        actual_read = cast(ActualRead, None)
        unavailable = cast(Unknown, None)
        ellipsis = cast(Callable[..., int], None)
        ellipsis_any = cast(Callable[..., Any], None)
        ellipsis_unknown = cast(Callable[..., Unknown], None)
        explicit_any_result = cast(Callable[[Any], Any], None)
        explicit_any = cast(Callable[[Any], int], None)
        explicit_list = cast(Callable[[list[Any]], int], None)
        tuple_actual = (finite,)
        tuple_target = cast(tuple[Callable[..., int]], None)
        readonly_actual = cast(Actual, None)
        readonly_target = cast(Opaque, None)
        mixed_actual = cast(MixedActual, None)
        mixed_target = cast(Mixed, None)
        mutable_actual = cast(MutableActual, None)
        mutable_target = cast(Mutable, None)
        list_actual = cast(list[Callable[[int], int]], None)
        list_target = cast(list[Callable[..., int]], None)
        higher_target = cast(Callable[[Callable[[list[Any]], int]], int], None)
        higher_return_target = cast(Callable[[int], Callable[..., int]], None)
        prefix_target = cast(Callable[Concatenate[str, ...], int], None)
        "#,
    )?;
    let file = system_path_to_file(&db, "/src/main.py")?;
    let env = db.program_environment();
    for (actual, target, expected) in [
        ("missing_input", "explicit_any", false),
        ("missing_input", "ellipsis", true),
        ("opaque_input", "explicit_any", false),
        ("consume", "nominal_input", false),
        ("opaque_input", "opaque_input", true),
        ("unknown_list", "any_list", false),
        ("unknown_consumer", "any_consumer", false),
        ("unknown_write", "any_write", false),
        ("finite", "named_remainder", false),
        ("actual_fields", "read_fields", true),
        ("actual_fields", "write_fields", false),
        ("finite", "ellipsis", true),
        ("wrong", "ellipsis", false),
        ("unknown", "ellipsis", false),
        ("string_input", "ellipsis_any", true),
        ("unknown", "ellipsis_any", true),
        ("unavailable", "ellipsis_any", false),
        ("string_input", "ellipsis_unknown", false),
        ("object_input", "explicit_any_result", true),
        ("string_input", "explicit_any_result", false),
        ("finite", "explicit_any", false),
        ("only_strings", "explicit_list", false),
        ("tuple_actual", "tuple_target", true),
        ("readonly_actual", "readonly_target", true),
        ("mixed_actual", "mixed_target", false),
        ("mutable_actual", "mutable_target", false),
        ("list_actual", "list_target", false),
        ("list_target", "list_target", true),
        ("higher", "higher_target", false),
        ("higher_return", "higher_return_target", true),
        ("finite", "prefix_target", false),
        ("actual_read", "any_read", true),
        ("missing", "any_read", false),
    ] {
        let actual = global_symbol(&db, file, actual).place.expect_type();
        let target = global_symbol(&db, file, target).place.expect_type();
        assert_eq!(
            actual.satisfies_declared_output(&db, &env, target),
            expected,
            "{} -> {}",
            actual.display(&db, &env),
            target.display(&db, &env),
        );
    }
    Ok(())
}

#[test]
fn static_generic_callable_specializations() -> anyhow::Result<()> {
    let mut db = TestDbBuilder::new()
        .with_python_version(PythonVersion::PY313)
        .build()?;
    db.write_dedented(
        "/src/main.py",
        r#"
        from typing import Any, Callable, Generic, Protocol, TypeVar, cast
        from ty_extensions._internal import into_regular_callable

        T = TypeVar("T")
        B = TypeVar("B", bound=int)
        C = TypeVar("C", str, bytes)
        def identity(value: T) -> T: return value
        def pep_identity[U](value: U) -> U: return value
        def list_identity(value: list[T]) -> list[T]: return value
        def wrong(value: T) -> int: return 1
        def bounded(value: B) -> B: return value
        def constrained(value: C) -> C: return value
        generic_target = into_regular_callable(identity)
        fixed = cast(Callable[[str], str], None)
        wrong_result = cast(Callable[[str], int], None)
        any_input = cast(Callable[[Any], int], None)
        int_identity = cast(Callable[[int], int], None)
        fixed_list = cast(Callable[[list[str]], list[str]], None)
        wrong_list = cast(Callable[[list[str]], list[int]], None)

        class Box(Generic[T]): pass
        def constructor(**kwargs: T) -> Box[T]: return cast(Box[T], None)
        class Factory(Protocol):
            def __call__(self, **kwargs: str) -> Box[str]: ...
        factory = cast(Factory, None)

        class Required(Protocol):
            def __call__(self, value: str) -> str: ...
        class NarrowCallable:
            def __call__(self, value: B) -> B: return value
        def outer(callback: Required, value: T) -> T:
            callback("x")
            return value
        nested_bound = cast(Callable[[NarrowCallable, int], int], None)
        class GradualCallback:
            def __call__(self, value: Any) -> Any: return value
        class IntCallback:
            def __call__(self, value: int) -> int: return value
        def generic_callback(callback: Callable[[T], T]) -> T:
            return callback(cast(T, None))
        gradual_callback = cast(Callable[[GradualCallback], int], None)
        static_callback = cast(Callable[[IntCallback], int], None)

        T_co = TypeVar("T_co", covariant=True)
        class ReadField(Protocol[T_co]):
            @property
            def field(self) -> T_co: ...
        class AnyField:
            field: Any
        class IntField:
            field: int
        def generic_field(value: ReadField[T]) -> T: return value.field
        gradual_field = cast(Callable[[AnyField], int], None)
        static_field = cast(Callable[[IntField], int], None)
        "#,
    )?;
    let file = system_path_to_file(&db, "/src/main.py")?;
    let env = db.program_environment();
    let target = global_symbol(&db, file, "generic_target")
        .place
        .expect_type();
    let Type::Callable(callable) = target else {
        panic!(
            "expected a generic callable, got {}",
            target.display(&db, &env)
        );
    };
    let [signature] = callable.signatures(&db).overloads.as_slice() else {
        panic!("expected one generic signature");
    };
    assert!(signature.generic_context.is_some());
    for (actual, target, expected, assignable) in [
        ("identity", "fixed", true, Some(true)),
        ("pep_identity", "fixed", true, Some(true)),
        ("identity", "wrong_result", false, None),
        ("identity", "any_input", false, None),
        ("list_identity", "fixed_list", true, Some(true)),
        ("list_identity", "wrong_list", false, None),
        ("wrong", "fixed", false, None),
        ("bounded", "fixed", false, None),
        ("constrained", "int_identity", false, None),
        ("constructor", "factory", true, None),
        ("outer", "nested_bound", false, None),
        ("generic_callback", "gradual_callback", false, Some(true)),
        ("generic_callback", "static_callback", true, None),
        ("generic_field", "gradual_field", false, Some(true)),
        ("generic_field", "static_field", true, None),
        ("fixed", "generic_target", false, None),
    ] {
        let actual = global_symbol(&db, file, actual).place.expect_type();
        let target = global_symbol(&db, file, target).place.expect_type();
        if let Some(expected) = assignable {
            assert_eq!(
                actual.is_assignable_to(&db, &env, target),
                expected,
                "{} -> {}",
                actual.display(&db, &env),
                target.display(&db, &env),
            );
        }
        assert_eq!(
            actual.is_pure_redundant_with(&db, &env, target),
            expected,
            "{} -> {}",
            actual.display(&db, &env),
            target.display(&db, &env),
        );
        assert_eq!(
            actual.satisfies_declared_output(&db, &env, target),
            expected,
            "{} -> {}",
            actual.display(&db, &env),
            target.display(&db, &env),
        );
    }
    Ok(())
}

#[test]
fn function_output_correspondence() -> anyhow::Result<()> {
    let registry = crate::default_lint_registry();
    let mut rules = RuleSelection::from_registry(registry);
    rules.enable(
        registry.get("unsound-return-statement")?,
        Severity::Error,
        LintSource::File,
    );
    let mut db = TestDbBuilder::new()
        .with_rule_selection(rules)
        .with_python_version(PythonVersion::PY313)
        .build()?;
    db.write_dedented(
        "/src/main.py",
        r#"
        from typing import Any, Callable, Generator, Protocol, Sequence, TypeAlias, TypeAliasType, TypeGuard, TypeIs
        from ty_extensions._internal import Unknown

        Unrestricted: TypeAlias = Any
        StringGuard = TypeAliasType("StringGuard", TypeGuard[str])

        class Run(Protocol):
            def __call__(self, values: list[Any]) -> int: ...

        def only_strings(values: list[str]) -> int:
            return len(values[0])

        def length(values: Sequence[object]) -> int:
            return len(values)

        def one() -> int:
            return 1

        def unsafe() -> Run:
            return only_strings

        def safe() -> Run:
            return length

        def scalar() -> Unrestricted:
            return 1

        # An explicit Any output omits a value constraint inside the callable too.
        def nested_output() -> Callable[[], Any]:
            return one

        def unknown() -> Unknown:
            return 1

        def declared() -> Run:
            return length

        def forwarded() -> Run:
            return declared()

        def mixed(flag: bool) -> Run:
            return declared() if flag else only_strings

        def implicit() -> Any:
            pass

        def generator() -> Generator[int, None, Run]:
            yield 1
            return only_strings

        def generator_omitted() -> Generator[int, None, Callable[..., Any]]:
            yield 1
            return one

        def missing():
            return 1

        def guard(value: object) -> TypeGuard[str]:
            return True

        def predicate(value: object) -> TypeIs[str]:
            return False

        def aliased_guard(value: object) -> StringGuard:
            return True

        def as_bool(value: object) -> bool:
            return guard(value)

        def checked_guard(value: object) -> TypeGuard[str]:
            return type(value) is str

        def documented_guard(value: object) -> TypeGuard[str]:
            """Recognize strings."""
            return str is type(value)

        def wrong_target(value: object) -> TypeGuard[int]:
            return type(value) is str

        def prior_equality(value: int | str) -> TypeGuard[str]:
            assert value == "x"
            return value is value

        def prior_predicate(value: object) -> TypeGuard[str]:
            if guard(value):
                return value is value
            return type(value) is str

        _STRING_CLASS = type("")
        _CONSTRUCTED_CLASS = type(str())
        _ALIASED_CLASS = str

        def constant_class(value: object) -> TypeGuard[str]:
            return type(value) is _STRING_CLASS

        def constructed_class(value: object) -> TypeGuard[str]:
            return type(value) is _CONSTRUCTED_CLASS

        def aliased_class(value: object) -> TypeGuard[str]:
            return type(value) is _ALIASED_CLASS

        def local_class(value: object, tag: type[str]) -> TypeGuard[str]:
            return type(value) is tag

        def shadowed_classifier(value: object, type: Callable[[object], type[str]]) -> TypeGuard[str]:
            return type(value) is str

        def unsafe_equality(value: int | str) -> TypeGuard[str]:
            return value == "x"

        def rebound_guard(value: object) -> TypeGuard[str]:
            value = "x"
            return type(value) is str

        def alias_subject(value: object) -> TypeGuard[str]:
            alias = value
            return type(alias) is str

        def other_subject(value: object, other: object) -> TypeGuard[str]:
            return type(other) is str

        def unchecked_guard(value: object) -> TypeGuard[str]:
            return guard(value)

        def dead_return(value: object) -> TypeGuard[str]:
            if False:
                return True
            return type(value) is str

        def not_implemented_guard(value: object) -> TypeGuard[str]:
            return NotImplemented

        class Spoofed:
            @property
            def __class__(self) -> type[str]:
                return str

        def class_attribute(value: Spoofed) -> TypeGuard[str]:
            return value.__class__ is str

        def nested_writer(value: object) -> TypeGuard[str]:
            def rebind() -> None:
                nonlocal value
                value = "x"
            rebind()
            return type(value) is str

        class Guarded:
            pass

        def checked_class(value: object) -> TypeGuard[Guarded]:
            return type(value) is Guarded

        def condition() -> bool:
            return True

        if condition():
            class bytes(int):
                pass
            complex = type("")

        def conditional_class(value: object) -> TypeGuard[int]:
            return type(value) is bytes

        def conditional_constant(value: object) -> TypeGuard[str]:
            return type(value) is complex

        def late_builtin_class(value: object) -> TypeGuard[int]:
            return type(value) is float

        late_builtin_class(1.0)

        class float(int):
            pass

        def effectful_operand(value: object, change: Callable[[object], type[Guarded]]) -> TypeGuard[Guarded]:
            return type(value) is change(value)
        "#,
    )?;
    let file = system_path_to_file(&db, "/src/main.py")?;
    let names = [
        "unsafe",
        "safe",
        "scalar",
        "nested_output",
        "unknown",
        "forwarded",
        "mixed",
        "implicit",
        "generator",
        "generator_omitted",
        "missing",
        "guard",
        "predicate",
        "aliased_guard",
        "as_bool",
        "checked_guard",
        "documented_guard",
        "wrong_target",
        "prior_equality",
        "prior_predicate",
        "constant_class",
        "constructed_class",
        "aliased_class",
        "local_class",
        "shadowed_classifier",
        "unsafe_equality",
        "rebound_guard",
        "alias_subject",
        "other_subject",
        "unchecked_guard",
        "dead_return",
        "not_implemented_guard",
        "class_attribute",
        "nested_writer",
        "effectful_operand",
        "checked_class",
        "conditional_class",
        "conditional_constant",
        "late_builtin_class",
    ];
    let signatures = |db: &TestDb| {
        names.map(|name| {
            global_symbol(db, file, name)
                .place
                .expect_type()
                .display(db, &db.program_environment())
                .to_string()
        })
    };
    let correspondence = |db: &TestDb| {
        let model = crate::SemanticModel::new(db, program_file(db, file));
        names.map(|name| {
            model
                .function_inference_facts(first_public_binding(db, file, name))
                .unwrap()
                .return_type_correspondence
        })
    };
    let ordinary = signatures(&db);
    assert_file_diagnostics(&db, "/src/main.py", &[]);
    assert_eq!(correspondence(&db), names.map(|_| None));
    db.select_function_inference(Some((
        file,
        names.map(str::to_owned).to_vec(),
        crate::FunctionInferenceMode::OutputProof,
    )));
    assert_file_diagnostics(&db, "/src/main.py", &[]);
    assert_eq!(
        correspondence(&db),
        [
            Some(false),
            Some(true),
            Some(true),
            Some(true),
            Some(false),
            Some(true),
            Some(false),
            Some(true),
            Some(false),
            Some(true),
            None,
            None,
            None,
            None,
            Some(true),
            Some(true),
            Some(true),
            Some(false),
            None,
            None,
            Some(true),
            Some(true),
            None,
            None,
            None,
            None,
            None,
            None,
            None,
            None,
            None,
            None,
            None,
            None,
            None,
            Some(true),
            None,
            None,
            None,
        ]
    );
    assert_eq!(signatures(&db), ordinary);
    db.select_function_inference(Some((
        file,
        names.map(str::to_owned).to_vec(),
        crate::FunctionInferenceMode::Conservative,
    )));
    assert_file_diagnostics(&db, "/src/main.py", &[]);
    assert_eq!(correspondence(&db), names.map(|_| None));
    assert_eq!(signatures(&db), ordinary);
    db.select_function_inference(None);
    assert_file_diagnostics(&db, "/src/main.py", &[]);
    assert_eq!(correspondence(&db), names.map(|_| None));
    assert_eq!(signatures(&db), ordinary);
    Ok(())
}

#[test]
fn function_argument_correspondence_status() -> anyhow::Result<()> {
    let mut db = TestDbBuilder::new()
        .with_python_version(PythonVersion::PY313)
        .build()?;
    db.write_dedented(
        "/src/main.py",
        r#"
        from typing import Any, Callable, no_type_check

        class Factory:
            def __init__(self, cls: object, callback: Callable[..., None]) -> None:
                pass

        class Wrapped:
            __new__ = Factory

            def __init__(self, callback: Callable[[int], None]) -> None:
                pass

        def wrapped(callback: Callable[..., None]) -> object:
            return Wrapped(callback)

        def narrow(values: list[str]) -> None:
            pass

        def accept(callback: Callable[[list[Any]], None]) -> None:
            pass

        def needs_int(value: int) -> None:
            pass

        def bad() -> None:
            accept(narrow)

        def good() -> None:
            accept(lambda values: None)

        def dead() -> None:
            if False:
                accept(narrow)

        def suppressed() -> None:
            needs_int("bad")  # ty: ignore[invalid-argument-type]

        @no_type_check
        def unchecked() -> None:
            needs_int("bad")
        "#,
    )?;
    let file = system_path_to_file(&db, "/src/main.py")?;
    let names = ["bad", "good", "dead", "suppressed", "unchecked", "wrapped"];
    let signatures = |db: &TestDb| {
        names.map(|name| {
            global_symbol(db, file, name)
                .place
                .expect_type()
                .display(db, &db.program_environment())
                .to_string()
        })
    };
    let facts = |db: &TestDb| {
        let model = crate::SemanticModel::new(db, program_file(db, file));
        names.map(|name| {
            model
                .function_inference_facts(first_public_binding(db, file, name))
                .unwrap()
        })
    };
    let ordinary_signatures = signatures(&db);
    let ordinary = facts(&db);
    assert_eq!(
        ordinary.map(|fact| fact.has_unproved_requirements),
        names.map(|_| false)
    );
    assert_file_diagnostics(&db, "/src/main.py", &[]);

    db.select_function_inference(Some((
        file,
        names.map(str::to_owned).to_vec(),
        FunctionInferenceMode::OutputProof,
    )));
    let selected = facts(&db);
    assert_eq!(
        selected.map(|fact| fact.has_unproved_requirements),
        [true, false, false, true, true, true]
    );
    assert_eq!(
        selected.map(|fact| (fact.has_errors, fact.has_diagnostics_or_suppressions)),
        ordinary.map(|fact| (fact.has_errors, fact.has_diagnostics_or_suppressions))
    );
    assert_eq!(signatures(&db), ordinary_signatures);
    let file_result = crate::types::check_types_with_diagnostics(&db, program_file(&db, file), []);
    assert!(file_result.diagnostics.is_empty());
    assert!(file_result.has_unproved_requirements);
    // Repeat the queries after scope results have been cached.
    assert_eq!(
        facts(&db).map(|fact| fact.has_unproved_requirements),
        selected.map(|fact| fact.has_unproved_requirements)
    );
    assert!(
        crate::types::check_types_with_diagnostics(&db, program_file(&db, file), [])
            .has_unproved_requirements
    );

    db.select_function_inference(None);
    assert_eq!(
        facts(&db).map(|fact| fact.has_unproved_requirements),
        ordinary.map(|fact| fact.has_unproved_requirements)
    );
    assert_eq!(signatures(&db), ordinary_signatures);
    assert!(
        !crate::types::check_types_with_diagnostics(&db, program_file(&db, file), [])
            .has_unproved_requirements
    );
    assert_file_diagnostics(&db, "/src/main.py", &[]);
    Ok(())
}

#[test]
fn function_argument_correspondence_with_disabled_diagnostics() -> anyhow::Result<()> {
    let registry = crate::default_lint_registry();
    let mut rules = RuleSelection::from_registry(registry);
    rules.disable(registry.get("invalid-argument-type")?);
    let mut db = TestDbBuilder::new()
        .with_rule_selection(rules)
        .with_file(
            "/src/main.py",
            "def needs_int(value: int) -> None: ...\n\
             def bad() -> None:\n    needs_int('bad')\n",
        )
        .build()?;
    let file = system_path_to_file(&db, "/src/main.py")?;
    db.select_function_inference(Some((
        file,
        vec!["bad".to_owned()],
        FunctionInferenceMode::OutputProof,
    )));
    let result = crate::types::check_types_with_diagnostics(&db, program_file(&db, file), []);
    assert!(result.diagnostics.is_empty());
    assert!(!result.has_suppressed_inference_diagnostics);
    assert!(result.has_unproved_requirements);
    Ok(())
}

#[test]
fn indexed_store_correspondence() -> anyhow::Result<()> {
    let mut db = TestDbBuilder::new()
        .with_python_version(PythonVersion::PY313)
        .build()?;
    db.write_dedented(
        "/src/main.py",
        r#"
        from typing import Any, Callable, Literal, Protocol
        from typing_extensions import TypedDict

        class Named(Protocol):
            def __call__(self, *, name: str) -> None: ...

        class Bag(TypedDict):
            run: Named

        class OpenBag(TypedDict, extra_items=Named):
            run: Named

        class Pair(TypedDict):
            a: Named
            b: Named

        class First:
            def __setitem__(self, index: str, value: bytes) -> None: ...

        class Second:
            def __setitem__(self, index: int, value: Named) -> None: ...

        def list_closed(values: list[Named], value: Callable[..., None]) -> None:
            values[0] = value

        def list_known(values: list[Named], value: Named) -> None:
            values[0] = value

        def list_omitted(values: list[Callable[..., None]], value: Callable[..., None]) -> None:
            values[0] = value

        def dict_closed(values: dict[str, Named], value: Callable[..., None]) -> None:
            values["run"] = value

        def td_closed(values: Bag, value: Callable[..., None]) -> None:
            values["run"] = value

        def td_known(values: Bag, value: Named) -> None:
            values["run"] = value

        def td_extra(values: OpenBag, key: str, value: Callable[..., None]) -> None:
            values[key] = value

        def td_extra_known(values: OpenBag, key: str, value: Named) -> None:
            values[key] = value

        def td_extra_gradual(values: OpenBag, key: str | Any, value: Named) -> None:
            values[key] = value

        def td_dynamic(values: Bag, key: Any, value: Named) -> None:
            values[key] = value

        def td_multiple(values: Pair, key: Literal["a", "b"], value: Callable[..., None]) -> None:
            values[key] = value

        def union(values: list[Named] | dict[int, Named], value: Callable[..., None]) -> None:
            values[0] = value

        def intersection(values: First, value: Named) -> None:
            if isinstance(values, Second):
                values[0] = value

        def intersection_closed(values: First, value: Callable[..., None]) -> None:
            if isinstance(values, Second):
                values[0] = value
        "#,
    )?;
    let file = system_path_to_file(&db, "/src/main.py")?;
    let cases = [
        ("list_closed", true),
        ("list_known", false),
        ("list_omitted", false),
        ("dict_closed", true),
        ("td_closed", true),
        ("td_known", false),
        ("td_extra", true),
        ("td_extra_known", false),
        ("td_extra_gradual", true),
        // Gradual keys and callback domains do not establish the destination requirements.
        ("td_dynamic", true),
        ("td_multiple", true),
        ("union", true),
        ("intersection", false),
        ("intersection_closed", true),
    ];
    let facts = |db: &TestDb, name: &str| {
        crate::SemanticModel::new(db, program_file(db, file))
            .function_inference_facts(first_public_binding(db, file, name))
            .unwrap()
    };
    for (name, _) in cases {
        assert!(!facts(&db, name).has_unproved_requirements, "{name}");
    }
    assert_file_diagnostics(&db, "/src/main.py", &[]);

    db.select_function_inference(Some((
        file,
        cases.map(|(name, _)| name.to_owned()).to_vec(),
        FunctionInferenceMode::OutputProof,
    )));
    for (name, unproved) in cases {
        let result = facts(&db, name);
        assert_eq!(result.has_unproved_requirements, unproved, "{name}");
        assert_eq!(result.return_type_correspondence, Some(true), "{name}");
        assert!(!result.has_errors, "{name}");
    }
    assert_file_diagnostics(&db, "/src/main.py", &[]);

    db.select_function_inference(None);
    for (name, _) in cases {
        assert!(!facts(&db, name).has_unproved_requirements, "{name}");
    }
    assert_file_diagnostics(&db, "/src/main.py", &[]);
    Ok(())
}

#[test]
fn constructor_storage_correspondence() -> anyhow::Result<()> {
    let registry = crate::default_lint_registry();
    let mut rules = RuleSelection::from_registry(registry);
    for rule in [
        "invalid-argument-type",
        "invalid-key",
        "missing-argument",
        "missing-typed-dict-key",
        "unknown-argument",
    ] {
        rules.disable(registry.get(rule)?);
    }
    let mut db = TestDbBuilder::new()
        .with_python_version(PythonVersion::PY313)
        .with_rule_selection(rules)
        .build()?;
    db.write_dedented(
        "/src/main.py",
        r#"
        from typing import Callable, Literal, Protocol
        from typing_extensions import TypedDict

        class Named(Protocol):
            def __call__(self, *, name: str) -> None: ...

        class Bag(TypedDict):
            run: Named

        class OmittedBag(TypedDict):
            run: Callable[..., None]

        class OpenBag(TypedDict, extra_items=Named):
            pass

        class OpenOmittedBag(TypedDict, extra_items=Callable[..., None]):
            pass

        def pass_through(value: Named) -> Named:
            return value

        def key_from(value: Named) -> Literal["run"]:
            return "run"

        def context_closed(value: Callable[..., None]) -> Bag:
            return dict(run=value)

        def context_known(value: Named) -> Bag:
            return dict(run=value)

        def context_omitted(value: Callable[..., None]) -> OmittedBag:
            return dict(run=value)

        def class_closed(value: Callable[..., None]) -> Bag:
            return Bag(run=value)

        def class_known(value: Named) -> Bag:
            return Bag(run=value)

        def class_omitted(value: Callable[..., None]) -> OmittedBag:
            return OmittedBag(run=value)

        def literal_closed(value: Callable[..., None]) -> Bag:
            return Bag({"run": value})

        def literal_known(value: Named) -> Bag:
            return Bag({"run": value})

        def literal_omitted(value: Callable[..., None]) -> OmittedBag:
            return OmittedBag({"run": value})

        def mixed_overwritten(value: Callable[..., None], known: Named) -> Bag:
            return Bag({"run": value}, run=known)

        def mixed_child(value: Callable[..., None], known: Named) -> Bag:
            return Bag({"run": pass_through(value)}, run=known)

        def context_missing() -> Bag:
            return dict()

        def class_missing() -> Bag:
            return Bag()

        def literal_missing() -> Bag:
            return Bag({})

        def literal_invalid() -> Bag:
            return Bag({"run": 1})

        def context_unknown(value: Named) -> Bag:
            return dict(other=value)

        def mapping_closed(value: OmittedBag) -> Bag:
            return Bag(value)

        def default_closed(values: OpenBag, value: Callable[..., None]) -> Named:
            return values.setdefault("run", value)

        def default_known(values: OpenBag, value: Named) -> Named:
            return values.setdefault("run", value)

        def default_omitted(values: OpenOmittedBag, value: Callable[..., None]) -> Callable[..., None]:
            return values.setdefault("run", value)

        def default_key_child(values: OpenBag, value: Callable[..., None], known: Named) -> Named:
            return values.setdefault(key_from(value), known)
        "#,
    )?;
    let file = system_path_to_file(&db, "/src/main.py")?;
    let cases = [
        ("context_closed", true),
        ("context_known", false),
        ("context_omitted", false),
        ("class_closed", true),
        ("class_known", false),
        ("class_omitted", false),
        ("literal_closed", true),
        ("literal_known", false),
        ("literal_omitted", false),
        ("mixed_overwritten", false),
        ("mixed_child", true),
        ("context_missing", true),
        ("class_missing", true),
        ("literal_missing", true),
        ("literal_invalid", true),
        ("context_unknown", true),
        ("mapping_closed", true),
        ("default_closed", true),
        ("default_known", false),
        ("default_omitted", false),
        ("default_key_child", true),
    ];
    let facts = |db: &TestDb, name: &str| {
        crate::SemanticModel::new(db, program_file(db, file))
            .function_inference_facts(first_public_binding(db, file, name))
            .unwrap()
    };
    let signatures = |db: &TestDb| {
        cases.map(|(name, _)| {
            global_symbol(db, file, name)
                .place
                .expect_type()
                .display(db, &db.program_environment())
                .to_string()
        })
    };
    let ordinary = cases.map(|(name, _)| facts(&db, name).return_type_correspondence);
    let ordinary_signatures = signatures(&db);
    for (name, _) in cases {
        assert!(!facts(&db, name).has_unproved_requirements, "{name}");
    }
    assert_file_diagnostics(&db, "/src/main.py", &[]);

    db.select_function_inference(Some((
        file,
        cases.map(|(name, _)| name.to_owned()).to_vec(),
        FunctionInferenceMode::OutputProof,
    )));
    for (name, unproved) in cases {
        let result = facts(&db, name);
        assert_eq!(result.has_unproved_requirements, unproved, "{name}");
        assert!(!result.has_errors, "{name}");
    }
    assert_eq!(signatures(&db), ordinary_signatures);
    assert_file_diagnostics(&db, "/src/main.py", &[]);

    db.select_function_inference(None);
    for ((name, _), output) in cases.into_iter().zip(ordinary) {
        let result = facts(&db, name);
        assert!(!result.has_unproved_requirements, "{name}");
        assert_eq!(result.return_type_correspondence, output, "{name}");
    }
    assert_eq!(signatures(&db), ordinary_signatures);
    assert_file_diagnostics(&db, "/src/main.py", &[]);
    Ok(())
}

#[test]
fn typed_dict_merge_retains_selected_requirements() -> anyhow::Result<()> {
    let mut db = setup_db();
    db.write_dedented(
        "/src/main.py",
        r#"
        from typing import Callable, Protocol, TypedDict
        from typing_extensions import NotRequired

        class Named(Protocol):
            def __call__(self, *, name: str) -> None: ...

        class Row(TypedDict):
            cb: Named

        class OptionalRow(TypedDict):
            cb: NotRequired[Named]

        class OmittedRow(TypedDict):
            cb: Callable[..., None]

        def pass_through(callback: Named) -> Named:
            return callback

        def closed(row: Row, callback: Callable[..., None]) -> Row:
            return row | {"cb": callback}

        def known(row: Row, callback: Named) -> Row:
            return row | {"cb": callback}

        def omitted(row: OmittedRow, callback: Callable[..., None]) -> OmittedRow:
            return row | {"cb": callback}

        def overwritten(row: Row, callback: Callable[..., None]) -> Row:
            return {"cb": callback} | row

        def optional(row: OptionalRow, callback: Callable[..., None]) -> OptionalRow:
            return {"cb": callback} | row

        def executed_child(row: Row, callback: Callable[..., None]) -> Row:
            return {"cb": pass_through(callback)} | row

        def incompatible(row: Row) -> dict[str, object]:
            return row | {"cb": 1}

        def extra_key(row: Row) -> dict[str, object]:
            return row | {"extra": 1}
        "#,
    )?;
    let file = system_path_to_file(&db, "/src/main.py")?;
    let cases = [
        ("closed", true),
        ("known", false),
        ("omitted", false),
        ("overwritten", false),
        ("optional", true),
        ("executed_child", true),
        ("incompatible", false),
        ("extra_key", false),
    ];
    for mode in [
        FunctionInferenceMode::Default,
        FunctionInferenceMode::OutputProof,
        FunctionInferenceMode::Default,
    ] {
        db.select_function_inference(Some((
            file,
            cases.map(|(name, _)| name.to_owned()).to_vec(),
            mode,
        )));
        let model = crate::SemanticModel::new(&db, program_file(&db, file));
        for (name, unproved) in cases {
            let facts = model
                .function_inference_facts(first_public_binding(&db, file, name))
                .unwrap();
            assert_eq!(
                facts.has_unproved_requirements,
                mode == FunctionInferenceMode::OutputProof && unproved,
                "{mode:?} {name}"
            );
            assert!(!facts.has_errors, "{mode:?} {name}");
            assert_eq!(
                facts.return_type_correspondence,
                (mode == FunctionInferenceMode::OutputProof).then_some(true),
                "{mode:?} {name}"
            );
        }
        assert_file_diagnostics(&db, "/src/main.py", &[]);
    }
    Ok(())
}

#[test]
fn binary_and_augmented_argument_correspondence() -> anyhow::Result<()> {
    let mut db = setup_db();
    db.write_dedented(
        "/src/main.py",
        r#"
        from typing import Any, Callable, Protocol

        class Named(Protocol):
            def __call__(self, *, name: str) -> None: ...

        def closed(values: list[Callable[..., None]]) -> Named:
            callbacks: list[Named] = []
            callbacks += values
            return callbacks[0]

        def known(values: list[Named]) -> Named:
            callbacks: list[Named] = []
            callbacks += values
            return callbacks[0]

        def omitted(values: list[Callable[..., None]]) -> Callable[..., None]:
            callbacks: list[Callable[..., None]] = []
            callbacks += values
            return callbacks[0]

        def numeric(value: int) -> int:
            value += 1
            return value

        def dynamic(value: Any) -> Any:
            value += 1
            return value

        class Normal:
            def __add__(self, callback: Callable[[Any], None]) -> int:
                callback(1)
                return 1

        class Reflected:
            def __radd__(self, callback: Callable[[Any], None]) -> int: return 1

        def normal_closed(left: Normal, callback: Callable[[str], None]) -> int:
            result = left
            result += callback
            return result

        def normal_known(left: Normal, callback: Callable[[Any], None]) -> int:
            result = left
            result += callback
            return result

        def reflected_closed(right: Reflected, callback: Callable[[str], None]) -> int:
            result = callback
            result += right
            return result

        def reflected_known(right: Reflected, callback: Callable[[Any], None]) -> int:
            result = callback
            result += right
            return result

        class Rejected:
            def __add__(self, value: bytes) -> int: return 1

        class Accepted:
            def __radd__(self, value: Rejected) -> int: return 1

        def discarded(left: Rejected, right: Accepted) -> int:
            result = left
            result += right
            return result

        class Base:
            def __call__(self, value: str) -> None: pass
            def __add__(self, right: object) -> int: return 1

        class ClosedChild(Base):
            def __radd__(self, callback: Callable[[Any], None]) -> int: return 1

        class KnownChild(Base):
            def __radd__(self, left: Base) -> int: return 1

        def conditional_closed(left: Base, right: ClosedChild) -> int:
            result = left
            result += right
            return result

        def conditional_known(left: Base, right: KnownChild) -> int:
            result = left
            result += right
            return result

        class Factory:
            def __init__(self, cls: object, callback: Callable[..., None]) -> None: pass

        class Wrapped:
            __new__ = Factory
            def __init__(self, callback: Callable[[Any], None]) -> None: pass

        class Operator:
            __add__ = Wrapped

        def class_valued(left: Operator, callback: Callable[[str], None]) -> object:
            result = left
            result += callback
            return result

        def ordinary_normal_closed(left: Normal, callback: Callable[[str], None]) -> int:
            return left + callback

        def ordinary_normal_known(left: Normal, callback: Callable[[Any], None]) -> int:
            return left + callback

        def ordinary_reflected_closed(right: Reflected, callback: Callable[[str], None]) -> int:
            return callback + right

        def ordinary_reflected_known(right: Reflected, callback: Callable[[Any], None]) -> int:
            return callback + right

        def ordinary_discarded(left: Rejected, right: Accepted) -> int:
            return left + right

        def ordinary_conditional_closed(left: Base, right: ClosedChild) -> int:
            return left + right

        def ordinary_conditional_known(left: Base, right: KnownChild) -> int:
            return left + right

        def ordinary_class_valued(left: Operator, callback: Callable[[str], None]) -> object:
            return left + callback

        def ordinary_numeric(value: int) -> int:
            return value + 1
        "#,
    )?;
    let file = system_path_to_file(&db, "/src/main.py")?;
    let cases = [
        ("closed", true),
        ("known", false),
        ("omitted", false),
        ("numeric", false),
        ("dynamic", true),
        ("normal_closed", true),
        ("normal_known", false),
        ("reflected_closed", true),
        ("reflected_known", false),
        ("discarded", false),
        ("conditional_closed", true),
        ("conditional_known", false),
        ("class_valued", true),
        ("ordinary_normal_closed", true),
        ("ordinary_normal_known", false),
        ("ordinary_reflected_closed", true),
        ("ordinary_reflected_known", false),
        ("ordinary_discarded", false),
        ("ordinary_conditional_closed", true),
        ("ordinary_conditional_known", false),
        ("ordinary_class_valued", true),
        ("ordinary_numeric", false),
    ];
    let signatures = |db: &TestDb| {
        cases.map(|(name, _)| {
            global_symbol(db, file, name)
                .place
                .expect_type()
                .display(db, &db.program_environment())
                .to_string()
        })
    };
    let ordinary = signatures(&db);
    for mode in [
        FunctionInferenceMode::Default,
        FunctionInferenceMode::OutputProof,
        FunctionInferenceMode::Default,
    ] {
        db.select_function_inference(Some((
            file,
            cases.map(|(name, _)| name.to_owned()).to_vec(),
            mode,
        )));
        let model = crate::SemanticModel::new(&db, program_file(&db, file));
        for (name, unproved) in cases {
            let facts = model
                .function_inference_facts(first_public_binding(&db, file, name))
                .unwrap();
            assert_eq!(
                facts.has_unproved_requirements,
                mode == FunctionInferenceMode::OutputProof && unproved,
                "{mode:?} {name}"
            );
            assert!(!facts.has_errors, "{mode:?} {name}");
            assert_eq!(
                facts.return_type_correspondence,
                (mode == FunctionInferenceMode::OutputProof).then_some(true),
                "{mode:?} {name}"
            );
        }
        assert_eq!(signatures(&db), ordinary);
        assert_file_diagnostics(&db, "/src/main.py", &[]);
    }
    Ok(())
}

#[test]
fn parameter_default_correspondence() -> anyhow::Result<()> {
    let mut db = setup_db();
    for (body, unproved) in [
        (
            "def make(callback: Callable[[Any], None] = narrow): pass",
            true,
        ),
        (
            "def make(callback: Callable[[str], None] = narrow): pass",
            false,
        ),
        (
            "def make(callback: Callable[..., None] = narrow): pass",
            false,
        ),
        (
            "def make(callback: Callable[[Any], None] = wide): pass",
            false,
        ),
        ("def make(callback=narrow): pass", false),
        ("def make(callback: Unknown = narrow): pass", true),
        (
            "if False:\n    def make(callback: Callable[[Any], None] = narrow): pass",
            false,
        ),
    ] {
        db.write_file(
            "/src/main.py",
            format!(
                r#"from typing import Any, Callable
from ty_extensions._internal import Unknown
def narrow(value: str) -> None: pass
def wide(value: Any) -> None: pass
{body}
"#
            ),
        )?;
        let file = system_path_to_file(&db, "/src/main.py")?;
        let facts = |db: &TestDb| {
            let file = program_file(db, file);
            let module = parsed_module(db, file.python_file(db)).load(db);
            let [_, _, _, _, statement] = module.syntax().body.as_slice() else {
                panic!("expected imports, callbacks and one default declaration");
            };
            let function = match statement {
                ast::Stmt::FunctionDef(function) => function,
                ast::Stmt::If(branch) => {
                    let [ast::Stmt::FunctionDef(function)] = branch.body.as_slice() else {
                        panic!("expected an unreachable default declaration");
                    };
                    function
                }
                _ => panic!("expected a default declaration"),
            };
            let definition = semantic_index(db, file).expect_single_definition(function);
            let facts = crate::SemanticModel::new(db, file)
                .function_inference_facts(definition)
                .unwrap();
            let signature = infer_definition_types(db, definition)
                .binding_type(definition)
                .display(db, &db.program_environment())
                .to_string();
            (facts, signature)
        };
        let (ordinary, signature) = facts(&db);
        assert!(!ordinary.has_unproved_requirements, "{body}");
        assert_file_diagnostics(&db, "/src/main.py", &[]);
        db.select_function_inference(Some((
            file,
            vec!["<module>".to_owned()],
            FunctionInferenceMode::OutputProof,
        )));
        let (selected, selected_signature) = facts(&db);
        assert_eq!(selected.has_unproved_requirements, unproved, "{body}");
        assert!(!selected.has_errors, "{body}");
        assert_eq!(selected.return_type_correspondence, None, "{body}");
        assert_eq!(selected_signature, signature, "{body}");
        assert_file_diagnostics(&db, "/src/main.py", &[]);
        db.select_function_inference(None);
        let (restored, restored_signature) = facts(&db);
        assert!(!restored.has_unproved_requirements, "{body}");
        assert_eq!(restored_signature, signature, "{body}");
    }
    Ok(())
}

#[test]
fn declaration_storage_correspondence() -> anyhow::Result<()> {
    let registry = crate::default_lint_registry();
    let mut rules = RuleSelection::from_registry(registry);
    rules.disable(registry.get("unsound-assignment")?);
    let mut db = TestDbBuilder::new()
        .with_python_version(PythonVersion::PY313)
        .with_rule_selection(rules)
        .build()?;
    db.write_dedented(
        "/src/main.py",
        r#"
        from typing import Any, Callable, Final
        from ty_extensions._internal import Unknown

        def initialized(value: Callable[[str], None]) -> Callable[[Any], None]:
            callback: Callable[[Any], None] = value
            return callback

        def known(value: Callable[[Any], None]) -> Callable[[Any], None]:
            callback: Callable[[Any], None] = value
            return callback

        def omitted(value: Callable[[str], None]) -> Callable[..., None]:
            callback: Callable[..., None] = value
            return callback

        def inferred(value: Callable[[str], None]) -> Callable[[str], None]:
            callback = value
            return callback

        def later_assignment(value: Callable[[str], None]) -> Callable[[Any], None]:
            callback: Callable[[Any], None]
            callback = value
            return callback

        def prior_binding(value: Callable[[str], None]) -> Callable[[Any], None]:
            callback = value
            callback: Callable[[Any], None]
            return callback

        def typed_final(value: Callable[[str], None]) -> Callable[[Any], None]:
            callback: Final[Callable[[Any], None]] = value
            return callback

        def typed_final_known(value: Callable[[Any], None]) -> Callable[[Any], None]:
            callback: Final[Callable[[Any], None]] = value
            return callback

        def unknown_contract(value: object) -> object:
            callback: Unknown = value
            return callback

        def unknown_qualified_contract(value: object) -> object:
            callback: Final[Unknown] = value
            return callback

        def uninitialized() -> None:
            callback: Unknown

        def dead(value: Callable[[str], None]) -> None:
            if False:
                callback: Callable[[Any], None] = value

        def static_target(value: Any) -> int:
            callback: int = value
            return callback

        def bare_final(value: object) -> object:
            callback: Final = value
            return callback

        def bare_later(value: object) -> object:
            callback: Final
            callback = value
            return callback
        "#,
    )?;
    let file = system_path_to_file(&db, "/src/main.py")?;
    let cases = [
        ("initialized", Some(true)),
        ("known", Some(false)),
        ("omitted", Some(false)),
        ("inferred", Some(false)),
        ("later_assignment", Some(true)),
        ("prior_binding", Some(true)),
        ("typed_final", Some(true)),
        ("typed_final_known", Some(false)),
        ("unknown_contract", Some(true)),
        ("unknown_qualified_contract", Some(true)),
        ("uninitialized", Some(false)),
        ("dead", Some(false)),
        ("static_target", Some(true)),
        // Bare qualifiers share unresolved annotation metadata. Preserve their ordinary types
        // without promising that this proof mode can distinguish their absent value domain.
        ("bare_final", None),
        ("bare_later", None),
    ];
    let facts = |db: &TestDb, name: &str| {
        crate::SemanticModel::new(db, program_file(db, file))
            .function_inference_facts(first_public_binding(db, file, name))
            .unwrap()
    };
    let types = |db: &TestDb| {
        cases.map(|(name, _)| {
            let ty = global_symbol(db, file, name).place.expect_type();
            let scope = ty
                .as_function_literal()
                .unwrap()
                .literal(db)
                .last_definition
                .body_scope(db);
            (
                ty.display(db, &db.program_environment()).to_string(),
                symbol(db, scope, "callback", ConsideredDefinitions::EndOfScope)
                    .place
                    .ignore_possibly_undefined()
                    .map(|ty| ty.display(db, &db.program_environment()).to_string()),
            )
        })
    };
    let ordinary_types = types(&db);
    for (name, _) in cases {
        assert!(!facts(&db, name).has_unproved_requirements, "{name}");
    }
    assert_file_diagnostics(&db, "/src/main.py", &[]);

    db.select_function_inference(Some((
        file,
        cases.map(|(name, _)| name.to_owned()).to_vec(),
        FunctionInferenceMode::OutputProof,
    )));
    for (name, unproved) in cases {
        let result = facts(&db, name);
        if let Some(unproved) = unproved {
            assert_eq!(result.has_unproved_requirements, unproved, "{name}");
        }
        assert!(!result.has_errors, "{name}");
    }
    assert_eq!(types(&db), ordinary_types);
    assert_file_diagnostics(&db, "/src/main.py", &[]);

    db.select_function_inference(None);
    for (name, _) in cases {
        assert!(!facts(&db, name).has_unproved_requirements, "{name}");
    }
    assert_eq!(types(&db), ordinary_types);
    assert_file_diagnostics(&db, "/src/main.py", &[]);
    Ok(())
}

#[test]
fn contextual_literal_correspondence() -> anyhow::Result<()> {
    let mut db = TestDbBuilder::new()
        .with_python_version(PythonVersion::PY313)
        .build()?;
    db.write_dedented(
        "/src/main.py",
        r#"
        from typing import Any, Callable, Literal, Protocol
        from typing_extensions import TypedDict

        class Named(Protocol):
            def __call__(self, *, name: str) -> None: ...

        class Bag(TypedDict):
            run: Named

        class OmittedBag(TypedDict):
            run: Callable[..., None]

        class ClosedChoice(TypedDict):
            callbacks: list[Named]
            tag: Literal[0]

        class OmittedChoice(TypedDict):
            callbacks: list[Callable[..., None]]
            tag: Literal[1]

        def pass_through(value: Named) -> Named:
            return value

        def source(value: Named) -> list[int]:
            return [1]

        def list_closed(value: Callable[..., None]) -> Named:
            values: list[Named] = [value]
            return values[0]

        def list_known(value: Named) -> Named:
            values: list[Named] = [value]
            return values[0]

        def list_omitted(value: Callable[..., None]) -> Callable[..., None]:
            values: list[Callable[..., None]] = [value]
            return values[0]

        def dict_closed(value: Callable[..., None]) -> dict[str, Named]:
            values: dict[str, Named] = {"run": value}
            return values

        def dict_slow(value: Callable[..., None]) -> dict[str, Named]:
            empty: dict[str, Named] = {}
            values: dict[str, Named] = {**empty, "run": value}
            return values

        def dict_unpack(value: dict[str, Callable[..., None]]) -> dict[str, Named]:
            return {**value}

        def td_closed(value: Callable[..., None]) -> Bag:
            return {"run": value}

        def td_known(value: Named) -> Bag:
            return {"run": value}

        def td_omitted(value: Callable[..., None]) -> OmittedBag:
            return {"run": value}

        def td_overwritten(value: Callable[..., None], known: Named) -> Bag:
            return {"run": value, "run": known}

        def td_overwritten_child(value: Callable[..., None], known: Named) -> Bag:
            return {"run": pass_through(value), "run": known}

        def td_arbitrary(key: str, value: Callable[..., None], known: Named) -> Bag:
            return {"run": known, key: value}

        def td_spread(value: Any) -> Bag:
            return {**value}

        def td_candidates(value: Callable[..., None]) -> ClosedChoice | OmittedChoice:
            return {"callbacks": [value], "tag": 0}

        def td_fallback(value: Callable[..., None]) -> Bag | dict[str, Any]:
            return {"run": value}

        def union_candidate(value: Callable[..., None]) -> list[Named] | list[Callable[..., None] | int]:
            return [value, 1]

        def comp_live(value: Callable[..., None]) -> list[Named]:
            return [value for item in (1,)]

        def comp_dead(value: Callable[..., None]) -> list[Named]:
            return [value for item in (1,) if False]

        def comp_iterator(value: Callable[..., None]) -> list[Named]:
            return [value for item in source(value) if False]
        "#,
    )?;
    let file = system_path_to_file(&db, "/src/main.py")?;
    let cases = [
        ("list_closed", true),
        ("list_known", false),
        ("list_omitted", false),
        ("dict_closed", true),
        ("dict_slow", true),
        ("td_closed", true),
        ("td_known", false),
        ("td_omitted", false),
        ("td_overwritten", false),
        ("td_overwritten_child", true),
        ("td_arbitrary", true),
        ("td_spread", true),
        ("td_candidates", true),
        ("td_fallback", true),
        ("union_candidate", false),
        ("comp_live", true),
        ("comp_dead", false),
        ("comp_iterator", true),
    ];
    let facts = |db: &TestDb, name: &str| {
        crate::SemanticModel::new(db, program_file(db, file))
            .function_inference_facts(first_public_binding(db, file, name))
            .unwrap()
    };
    let signatures = |db: &TestDb| {
        cases.map(|(name, _)| {
            global_symbol(db, file, name)
                .place
                .expect_type()
                .display(db, &db.program_environment())
                .to_string()
        })
    };
    let ordinary_signatures = signatures(&db);
    for (name, _) in cases {
        assert!(!facts(&db, name).has_unproved_requirements, "{name}");
    }
    assert_file_diagnostics(&db, "/src/main.py", &[]);

    db.select_function_inference(Some((
        file,
        cases
            .map(|(name, _)| name.to_owned())
            .into_iter()
            .chain(["dict_unpack".to_owned()])
            .collect(),
        FunctionInferenceMode::OutputProof,
    )));
    for (name, unproved) in cases {
        let result = facts(&db, name);
        assert_eq!(result.has_unproved_requirements, unproved, "{name}");
        assert_eq!(result.return_type_correspondence, Some(true), "{name}");
        assert!(!result.has_errors, "{name}");
    }
    // Unpacked values keep their inference constraints instead of adopting element contexts.
    assert_eq!(
        facts(&db, "dict_unpack").return_type_correspondence,
        Some(false)
    );
    assert_eq!(signatures(&db), ordinary_signatures);
    assert_file_diagnostics(&db, "/src/main.py", &[]);

    db.select_function_inference(None);
    for (name, _) in cases {
        assert!(!facts(&db, name).has_unproved_requirements, "{name}");
    }
    assert_eq!(signatures(&db), ordinary_signatures);
    assert_file_diagnostics(&db, "/src/main.py", &[]);
    Ok(())
}

#[test]
fn conservative_source_globals() -> anyhow::Result<()> {
    let mut db = setup_db();
    db.write_dedented(
        "/src/dependency.py",
        r#"
        from typing import Any

        def opaque() -> Any:
            return None

        def provider(value: Any) -> int:
            return 1

        VALUES = [provider, opaque()]
        "#,
    )?;
    db.write_dedented(
        "/src/main.py",
        r#"
        from collections.abc import Iterable, Sequence
        from dependency import VALUES

        def collect(extra: Iterable[object] | None) -> Sequence[object]:
            if not extra:
                return VALUES
            out = list(VALUES)
            for item in extra:
                if item not in out:
                    out.append(item)
            return out

        SHARED = []

        def mutate_shared() -> None:
            SHARED.append(1)
        "#,
    )?;
    let file = system_path_to_file(&db, "/src/main.py")?;
    let dependency = system_path_to_file(&db, "/src/dependency.py")?;
    let public_types = |db: &TestDb| {
        [(dependency, "VALUES"), (file, "SHARED"), (file, "collect")].map(|(file, name)| {
            global_symbol(db, file, name)
                .place
                .expect_type()
                .display(db, &db.program_environment())
                .to_string()
        })
    };
    let ordinary = public_types(&db);
    assert_eq!(
        ordinary,
        [
            "list[((value: Any) -> int) | Any]",
            "list[Unknown]",
            "def collect(extra: Iterable[object] | None) -> Sequence[object]",
        ]
        .map(str::to_owned)
    );
    assert_file_diagnostics(&db, "/src/main.py", &[]);
    db.select_function_inference(Some((
        file,
        ["collect", "mutate_shared"].map(str::to_owned).to_vec(),
        crate::FunctionInferenceMode::Conservative,
    )));
    let selected = public_types(&db);
    let diagnostics = check_types(&db, program_file(&db, file));
    let module = program_file(&db, file);
    let index = semantic_index(&db, module);
    let Some((scope, _)) = index.child_scopes(FileScopeId::global()).next() else {
        panic!("collector body scope missing");
    };
    let out = symbol(
        &db,
        scope.to_scope_id(&db, module),
        "out",
        ConsideredDefinitions::AllReachable,
    )
    .place
    .expect_type()
    .display(&db, &db.program_environment())
    .to_string();
    assert_eq!(selected, ordinary);
    let source = source_text(&db, file);
    let failures: Vec<_> = diagnostics
        .iter()
        .map(|diagnostic| {
            let Some(range) = diagnostic.primary_span().and_then(|span| span.range()) else {
                panic!("diagnostic has no source range: {diagnostic:?}");
            };
            assert!(source[..usize::from(range.start())].ends_with("SHARED.append("));
            (diagnostic.id().to_string(), source[range].to_owned())
        })
        .collect();
    assert_eq!(
        failures,
        [("invalid-argument-type".to_owned(), "1".to_owned())]
    );
    assert_eq!(out, "list[object]");
    db.select_function_inference(None);
    assert_eq!(public_types(&db), ordinary);
    assert_file_diagnostics(&db, "/src/main.py", &[]);
    Ok(())
}

#[test]
fn successful_subscript_without_scope_inference() -> anyhow::Result<()> {
    let mut db = setup_db();
    db.write_dedented(
        "src/receivers.pyi",
        r#"
        from typing import NoReturn
        class Present:
            def __getitem__(self, key: int) -> int: ...
        class Absent:
            def __getitem__(self, key: int) -> NoReturn: ...
        "#,
    )?;
    db.write_dedented(
        "src/main.py",
        r#"
        from receivers import Present, Absent
        def f(value: Present | Absent):
            value[0]
            result = value
        "#,
    )?;
    let ty = get_symbol(&db, "src/main.py", &["f"], "result").expect_type();
    assert_eq!(
        ty.display(&db, &db.program_environment()).to_string(),
        "Present"
    );
    Ok(())
}

#[test]
fn same_file_at_different_python_versions() -> anyhow::Result<()> {
    let mut db = TestDbBuilder::new()
        .with_python_version(PythonVersion::PY311)
        .build()?;
    db.write_dedented(
        "src/main.py",
        r#"
        import sys

        from typing import reveal_type
        from zipfile._path import Path

        if sys.version_info >= (3, 12):
            from py312_dependency import value
        else:
            from py311_dependency import value

        type Alias = int

        reveal_type(value)
        "#,
    )?;
    db.write_dedented("src/py311_dependency.py", "value: str = 'py311'")?;
    db.write_dedented("src/py312_dependency.py", "value: int = 312")?;

    let file = system_path_to_file(&db, "src/main.py").expect("file to exist");
    let py311 = db.program().program_file(&db, file);
    let mut settings = db.program_settings().clone();
    settings.python_version.version = PythonVersion::PY312;
    let py312 = Program::from_settings(&db, &settings).program_file(&db, file);

    let check = |file, expected_type, expect_invalid_syntax, expect_unresolved_import| {
        let diagnostics = crate::check_file_unwrap(&db, file);

        assert_eq!(
            diagnostics
                .iter()
                .any(|diagnostic| diagnostic.id() == DiagnosticId::InvalidSyntax),
            expect_invalid_syntax,
            "{diagnostics:#?}"
        );
        assert_eq!(
            diagnostics
                .iter()
                .any(|diagnostic| diagnostic.headline_message().contains("zipfile._path")),
            expect_unresolved_import,
            "{diagnostics:#?}"
        );

        let revealed = diagnostics
            .iter()
            .find(|diagnostic| diagnostic.id() == DiagnosticId::RevealedType)
            .and_then(Diagnostic::primary_annotation)
            .and_then(|annotation| annotation.get_message());
        assert_eq!(revealed, Some(expected_type), "{diagnostics:#?}");
        assert_eq!(
            diagnostics.len(),
            1 + usize::from(expect_invalid_syntax) + usize::from(expect_unresolved_import),
            "{diagnostics:#?}"
        );
    };

    check(py311, "`str`", true, true);
    check(py312, "`int`", false, false);
    check(py311, "`str`", true, true);

    Ok(())
}

#[test]
fn program_file_changes_with_python_version() -> anyhow::Result<()> {
    let db = TestDbBuilder::new()
        .with_python_version(PythonVersion::PY311)
        .with_file("src/main.py", "type Alias = int")
        .build()?;
    let file = system_path_to_file(&db, "src/main.py").expect("file to exist");
    let program = db.program();
    let (program_file_id, py311) = {
        let program_file = program.program_file(&db, file);
        (program_file.as_id(), program_file.python_file(&db).as_id())
    };

    let mut settings = db.program_settings().clone();
    let equivalent_program = Program::from_settings(&db, &settings);
    assert_eq!(program, equivalent_program);
    assert_eq!(
        program_file_id,
        equivalent_program.program_file(&db, file).as_id()
    );

    settings.python_version.version = PythonVersion::PY312;
    let py312_program = Program::from_settings(&db, &settings);

    let program_file = py312_program.program_file(&db, file);
    assert_ne!(program_file_id, program_file.as_id());
    assert_eq!(program_file.python_version(&db), PythonVersion::PY312);
    assert_ne!(py311, program_file.python_file(&db).as_id());
    Ok(())
}

#[test]
fn expected_types_are_collected_only_for_open_files() -> anyhow::Result<()> {
    let has_expected_type = |open_file: bool| -> anyhow::Result<bool> {
        let mut db = setup_db();
        db.write_dedented(
            "src/a.py",
            r#"
            from typing_extensions import Literal

            value: Literal["apple", "banana"] = "app"
            "#,
        )?;

        let file = system_path_to_file(&db, "src/a.py").expect("file to exist");
        if open_file {
            db.open_file(file);
        }

        let module = parsed_module(&db, program_file(&db, file).python_file(&db)).load(&db);
        let assignment = module.syntax().body[1]
            .as_ann_assign_stmt()
            .expect("annotated assignment");
        let string_expr = assignment
            .value
            .as_deref()
            .expect("annotated assignment to have a value")
            .as_string_literal_expr()
            .expect("string literal value");
        let scope = global_scope(&db, program_file(&db, file));

        Ok(infer_complete_scope_types(&db, scope)
            .try_expected_type(ruff_python_ast::ExprRef::from(string_expr))
            .is_some())
    };

    assert!(!has_expected_type(false)?);
    assert!(has_expected_type(true)?);

    Ok(())
}

#[test]
fn compact_definition_types_omit_owner() -> anyhow::Result<()> {
    assert!(
        std::mem::size_of::<DefinitionTypes>()
            <= std::mem::size_of::<TypeAndQualifiers>() + std::mem::size_of::<usize>()
    );

    let mut db = setup_db();
    db.write_dedented(
        "/src/definitions.py",
        r#"
        first = 1
        second = 2
        "#,
    )?;

    let file = system_path_to_file(&db, "/src/definitions.py").unwrap();
    let module = parsed_module(&db, program_file(&db, file).python_file(&db)).load(&db);
    let first_assignment = module.syntax().body[0].as_assign_stmt().unwrap();
    let second_assignment = module.syntax().body[1].as_assign_stmt().unwrap();
    let first = semantic_index(&db, program_file(&db, file))
        .expect_single_definition(first_assignment.targets[0].as_name_expr().unwrap());
    let second = semantic_index(&db, program_file(&db, file))
        .expect_single_definition(second_assignment.targets[0].as_name_expr().unwrap());

    let owner_type = Type::unknown();
    let owner = DefinitionTypes::from_parts(first, vec![(first, owner_type)], vec![]);
    assert_matches!(owner, DefinitionTypes::Binding(ty) if ty == owner_type);
    assert_eq!(
        owner.bindings(first).collect::<Vec<_>>(),
        [(first, owner_type)]
    );

    let non_owner = DefinitionTypes::from_parts(first, vec![(second, owner_type)], vec![]);
    assert_matches!(non_owner, DefinitionTypes::Other(_));
    assert_eq!(
        non_owner.bindings(first).collect::<Vec<_>>(),
        [(second, owner_type)]
    );

    Ok(())
}

#[test]
fn not_literal_string() -> anyhow::Result<()> {
    let mut db = setup_db();
    let content = format!(
        r#"
            from typing_extensions import Literal, assert_type

            assert_type(not "{y}", bool)
            assert_type(not 10*"{y}", bool)
            assert_type(not "{y}"*10, bool)
            assert_type(not 0*"{y}", Literal[True])
            assert_type(not (-100)*"{y}", Literal[True])
            "#,
        y = "a".repeat(TypeInferenceBuilder::MAX_STRING_LITERAL_SIZE + 1),
    );
    db.write_dedented("src/a.py", &content)?;

    assert_file_diagnostics(
        &db,
        "src/a.py",
        &[
            "An empty string is always falsy",
            "An empty string is always falsy",
        ],
    );

    Ok(())
}

#[test]
fn multiplied_string() -> anyhow::Result<()> {
    let mut db = setup_db();
    let content = format!(
        r#"
            from typing_extensions import Literal, LiteralString, assert_type

            assert_type(2 * "hello", Literal["hellohello"])
            assert_type("goodbye" * 3, Literal["goodbyegoodbyegoodbye"])
            assert_type("a" * {y}, Literal["{a_repeated}"])
            assert_type({z} * "b", LiteralString)
            assert_type(0 * "hello", Literal[""])
            assert_type(-3 * "hello", Literal[""])
            "#,
        y = TypeInferenceBuilder::MAX_STRING_LITERAL_SIZE,
        z = TypeInferenceBuilder::MAX_STRING_LITERAL_SIZE + 1,
        a_repeated = "a".repeat(TypeInferenceBuilder::MAX_STRING_LITERAL_SIZE),
    );
    db.write_dedented("src/a.py", &content)?;

    assert_file_diagnostics(&db, "src/a.py", &[]);

    Ok(())
}

#[test]
fn multiplied_literal_string() -> anyhow::Result<()> {
    let mut db = setup_db();
    let content = format!(
        r#"
            from typing_extensions import Literal, LiteralString, assert_type

            assert_type("{y}", LiteralString)
            assert_type(10*"{y}", LiteralString)
            assert_type("{y}"*10, LiteralString)
            assert_type(0*"{y}", Literal[""])
            assert_type((-100)*"{y}", Literal[""])
            "#,
        y = "a".repeat(TypeInferenceBuilder::MAX_STRING_LITERAL_SIZE + 1),
    );
    db.write_dedented("src/a.py", &content)?;

    assert_file_diagnostics(&db, "src/a.py", &[]);

    Ok(())
}

#[test]
fn truncated_string_literals_become_literal_string() -> anyhow::Result<()> {
    let mut db = setup_db();
    let content = format!(
        r#"
            from typing_extensions import LiteralString, assert_type

            assert_type("{y}", LiteralString)
            assert_type("a" + "{z}", LiteralString)
            "#,
        y = "a".repeat(TypeInferenceBuilder::MAX_STRING_LITERAL_SIZE + 1),
        z = "a".repeat(TypeInferenceBuilder::MAX_STRING_LITERAL_SIZE),
    );
    db.write_dedented("src/a.py", &content)?;

    assert_file_diagnostics(&db, "src/a.py", &[]);

    Ok(())
}

#[test]
fn adding_string_literals_and_literal_string() -> anyhow::Result<()> {
    let mut db = setup_db();
    let content = format!(
        r#"
            from typing_extensions import LiteralString, assert_type

            assert_type("{y}", LiteralString)
            assert_type("{y}" + "a", LiteralString)
            assert_type("a" + "{y}", LiteralString)
            assert_type("{y}" + "{y}", LiteralString)
            "#,
        y = "a".repeat(TypeInferenceBuilder::MAX_STRING_LITERAL_SIZE + 1),
    );
    db.write_dedented("src/a.py", &content)?;

    assert_file_diagnostics(&db, "src/a.py", &[]);

    Ok(())
}

#[test]
fn pep695_type_params() {
    let mut db = setup_db();

    db.write_dedented(
        "src/a.py",
        "
            def f[T, U: A, V: (A, B), W = A, X: A = A1, Y: (int,)]():
                pass

            class A: ...
            class B: ...
            class A1(A): ...
            ",
    )
    .unwrap();

    let env = db.program_environment();
    let check_typevar = |var: &'static str,
                         display: &'static str,
                         upper_bound: Option<&'static str>,
                         constraints: Option<&[&'static str]>,
                         default: Option<&'static str>| {
        let var_ty = get_symbol(&db, "src/a.py", &["f"], var).expect_type();
        assert_eq!(var_ty.display(&db, &env).to_string(), display);

        let expected_name_ty = format!(r#"Literal["{var}"]"#);
        let name_ty = var_ty.member(&db, &env, "__name__").place.expect_type();
        assert_eq!(name_ty.display(&db, &env).to_string(), expected_name_ty);

        let Type::KnownInstance(KnownInstanceType::TypeVar(typevar)) = var_ty else {
            panic!("expected TypeVar");
        };

        assert_eq!(
            typevar
                .upper_bound(&db, &env)
                .map(|ty| ty.display(&db, &env).to_string()),
            upper_bound.map(std::borrow::ToOwned::to_owned)
        );
        assert_eq!(
            typevar.constraints(&db, &env).map(|tys| tys
                .iter()
                .map(|ty| ty.display(&db, &env).to_string())
                .collect::<Vec<_>>()),
            constraints.map(|strings| strings
                .iter()
                .map(std::string::ToString::to_string)
                .collect::<Vec<_>>())
        );
        assert_eq!(
            typevar
                .default_type(&db, &env)
                .map(|ty| ty.display(&db, &env).to_string()),
            default.map(std::borrow::ToOwned::to_owned)
        );
    };

    check_typevar("T", "TypeVar", None, None, None);
    check_typevar("U", "TypeVar", Some("A"), None, None);
    check_typevar("V", "TypeVar", None, Some(&["A", "B"]), None);
    check_typevar("W", "TypeVar", None, None, Some("A"));
    check_typevar("X", "TypeVar", Some("A"), None, Some("A1"));

    // a typevar with less than two constraints is treated as unconstrained
    check_typevar("Y", "TypeVar", None, None, None);
}

#[test]
fn simple_assignment_does_not_enter_salsa_cycle() {
    let mut db = setup_db();
    db.write_dedented("src/a.py", "x = 1; y = x + 1").unwrap();

    assert_file_diagnostics(&db, "src/a.py", &[]);

    let events = db.take_salsa_events();
    let cycles = salsa::attach(&db, || {
        events
            .iter()
            .filter_map(|event| {
                if let salsa::EventKind::WillIterateCycle { database_key, .. } = event.kind {
                    Some(format!("{database_key:?}"))
                } else {
                    None
                }
            })
            .collect::<Vec<_>>()
    });
    assert_eq!(cycles, Vec::<String>::new());
}

/// Comparison truthiness widens consistently in expression, statement, and definition inference
/// when an override is present in only one iteration.
///
/// A missing override falls back to the expression type's truthiness. Widening must compare the
/// effective truthiness from both iterations, including this fallback. Discarding an override from
/// the previous iteration could otherwise make a previously ambiguous condition definite again.
///
/// We construct inference results directly because mdtests cannot prescribe intermediate Salsa
/// results. A Python cycle can converge before widening starts, or drop an override without
/// changing any final types or diagnostics. No known Python example exposes the failures checked
/// here, so this is defensive coverage of the widening invariant.
#[test]
fn comparison_truthiness_widens_across_sparse_cycle_results() -> anyhow::Result<()> {
    let mut db = setup_db();
    db.write_dedented("src/comparison.py", "0 < 1 < 2")?;
    let file = program_file(&db, system_path_to_file(&db, "src/comparison.py")?);
    let module = parsed_module(&db, file.python_file(&db)).load(&db);
    let Some(ast::Stmt::Expr(statement)) = module.syntax().body.first() else {
        anyhow::bail!("expected a comparison expression statement");
    };
    let expression = ExpressionNodeKey::from(statement.value.as_ref());
    let scope = global_scope(&db, file);
    let env = ProgramEnvironment::from_scope(scope);
    let inference = |ty, truthiness: Option<Truthiness>| {
        (
            ExpressionInference {
                expressions: [(expression, ty)].into_iter().collect(),
                extra: truthiness.map(|truthiness| {
                    Box::new(ExpressionInferenceExtra {
                        comparison_truthiness: [(expression, truthiness)].into_iter().collect(),
                        ..ExpressionInferenceExtra::default()
                    })
                }),
                #[cfg(debug_assertions)]
                scope,
            },
            StatementInferenceInner {
                expressions: [(expression, ty)].into_iter().collect(),
                bindings: Box::default(),
                declarations: Box::default(),
                extra: truthiness.map(|truthiness| {
                    Box::new(StatementInferenceInnerExtra {
                        comparison_truthiness: [(expression, truthiness)].into_iter().collect(),
                        ..StatementInferenceInnerExtra::default()
                    })
                }),
                #[cfg(debug_assertions)]
                scope,
            },
            DefinitionInference {
                expressions: [(expression, ty)].into_iter().collect(),
                types: DefinitionTypes::Empty,
                extra: truthiness.map(|truthiness| {
                    Box::new(DefinitionInferenceExtra::Other(Box::new(
                        OtherDefinitionInferenceExtra {
                            comparison_truthiness: [(expression, truthiness)].into_iter().collect(),
                            ..OtherDefinitionInferenceExtra::default()
                        },
                    )))
                }),
                #[cfg(debug_assertions)]
                scope,
            },
        )
    };

    for (previous, current, expected) in [
        // A previously widened condition stays ambiguous even when the new result omits its
        // override and has a definite value-type fallback.
        (
            (Type::bool_literal(false), Some(Truthiness::Ambiguous)),
            (Type::bool_literal(false), None),
            Truthiness::Ambiguous,
        ),
        // A new override is compared with the previous result's value-type fallback.
        (
            (Type::bool_literal(true), None),
            (Type::unknown(), Some(Truthiness::AlwaysFalse)),
            Truthiness::Ambiguous,
        ),
        // Matching effective truthiness stays precise. Keep the override even though it agrees
        // with the current type: subsequent type widening can make that fallback ambiguous again.
        (
            (Type::unknown(), Some(Truthiness::AlwaysFalse)),
            (Type::bool_literal(false), None),
            Truthiness::AlwaysFalse,
        ),
    ] {
        let (previous_expression, previous_statement, previous_definition) =
            inference(previous.0, previous.1);
        let (mut current_expression, mut current_statement, mut current_definition) =
            inference(current.0, current.1);
        current_expression.widen_comparison_truthiness(&db, &env, &previous_expression);
        current_statement.widen_comparison_truthiness(&db, &env, &previous_statement);
        current_definition.widen_comparison_truthiness(&db, &env, &previous_definition);
        assert_eq!(
            current_expression.comparison_truthiness(expression),
            Some(expected)
        );
        assert_eq!(
            current_statement
                .extra
                .as_deref()
                .and_then(|extra| extra.comparison_truthiness.get(&expression))
                .copied(),
            Some(expected)
        );
        assert_eq!(
            current_definition
                .extra
                .as_deref()
                .and_then(DefinitionInferenceExtra::comparison_truthiness)
                .and_then(|overrides| overrides.get(&expression))
                .copied(),
            Some(expected)
        );
    }

    Ok(())
}

/// Resolving environment-guard provenance must not re-enter inference of the scope being checked.
/// This lookup runs during scope inference; asking for completed use-site types would create a
/// Salsa cycle. Cycle recovery can hide that mistake in the final diagnostics, so inspect Salsa's
/// events as well as checking that each condition produces a diagnostic.
#[test]
fn redundant_condition_lookup_does_not_reenter_scope_inference() -> anyhow::Result<()> {
    // Cover builtin names, including the numeric-compatibility special cases for `float` and
    // `complex`, and attribute lookup using an already-inferred receiver type.
    for source in [
        "if isinstance({}, dict):\n    pass\n",
        "if isinstance(1.0, float):\n    pass\n",
        "if isinstance(1j, complex):\n    pass\n",
        "class C:\n    flag = (1, 2)\n\nif C.flag:\n    pass\n",
    ] {
        let registry = crate::default_lint_registry();
        let mut rules = RuleSelection::from_registry(registry);
        rules.enable(
            registry.get("redundant-condition-strict")?,
            Severity::Warning,
            LintSource::File,
        );
        let mut db = TestDbBuilder::new()
            .with_file("/src/main.py", source)
            .with_rule_selection(rules)
            .build()?;
        let file = system_path_to_file(&db, "/src/main.py")?;
        let diagnostics = check_types(&db, program_file(&db, file));
        // Require the diagnostic so the cycle check cannot pass merely because the redundant
        // condition was never checked.
        assert_eq!(diagnostics.len(), 1, "{source}\n{diagnostics:#?}");

        let events = db.take_salsa_events();
        let scope_cycles = salsa::attach(&db, || {
            events
                .iter()
                .filter_map(|event| match event.kind {
                    salsa::EventKind::WillIterateCycle { database_key, .. } => {
                        Some(format!("{database_key:?}"))
                    }
                    _ => None,
                })
                .filter(|query| query.starts_with("infer_scope_types_impl("))
                .collect::<Vec<_>>()
        });
        assert!(scope_cycles.is_empty(), "{source}\n{scope_cycles:#?}");
    }
    Ok(())
}

/// Repeated conditions share cached definition and reachability summaries. Reassigned names need
/// different definitions at each read, but share the index of their original assignment guards.
/// Rebuilding that index for every condition would make these examples quadratic even if their
/// diagnostics were unchanged. Attribute fallback lookup also shares its definition summary.
/// Lazy closure reads share both the summary and boundness analysis of their outer bindings.
/// Conditions on distinct names also share the reachability summaries for preceding calls,
/// rather than traversing an increasingly long call prefix for each name.
#[test]
fn repeated_tuple_conditions_share_provenance() -> anyhow::Result<()> {
    let repetitions = 100;
    let names = "value = (1,)\nif value:\n    pass\n".repeat(repetitions);
    let lazy_closure = format!(
        "def outer():\n    def inner():\n{}{}",
        "        if value:\n            pass\n".repeat(repetitions),
        "    value = (1,)\n".repeat(repetitions),
    );
    let attributes = format!(
        "class C:\n{}\n{}",
        "    value = (1,)\n".repeat(repetitions),
        "if C.value:\n    pass\n".repeat(repetitions),
    );
    let mut calls = String::from(
        "def noop() -> None: ...
",
    );
    for index in 0..repetitions {
        writeln!(
            calls,
            "noop()
value_{index} = (1,)
if value_{index}:
    pass"
        )?;
    }

    for (source, query_name, max_queries) in [
        (names, "definition_reachability", 1),
        (lazy_closure, "owning_scope_condition_definition_info", 1),
        (attributes, "attribute_condition_definition_info", 1),
        (
            calls,
            "reachability_contains_special_cased_condition",
            3 * repetitions,
        ),
    ] {
        let mut db = TestDbBuilder::new()
            .with_file("/src/main.py", &source)
            .build()?;
        let file = system_path_to_file(&db, "/src/main.py")?;
        let diagnostics = check_types(&db, program_file(&db, file));
        // Sharing the definition lookup must still leave a diagnostic on every condition.
        assert_eq!(diagnostics.len(), repetitions);

        // Count actual query executions, excluding cache hits. This checks reuse deterministically
        // without a timing threshold, which would depend on the machine running the test.
        let events = db.take_salsa_events();
        let lookups = events
            .iter()
            .filter(|event| {
                matches!(
                    event.kind,
                    salsa::EventKind::WillExecute { database_key }
                        if db.ingredient_debug_name(database_key.ingredient_index()) == query_name
                )
            })
            .count();
        assert!(
            (1..=max_queries).contains(&lookups),
            "{query_name} should be shared across conditions; executed {lookups} queries"
        );
    }
    Ok(())
}

/// Test that a symbol known to be unbound in a scope does not still trigger cycle-causing
/// reachability-constraint checks in that scope.
#[test]
fn unbound_symbol_no_reachability_constraint_check() {
    let mut db = setup_db();

    // If the bug we are testing for is not fixed, what happens is that when inferring the
    // `flag: bool = True` definitions, we look up `bool` as a deferred name (thus from end of
    // scope), and because of the early return its "unbound" binding has a reachability
    // constraint of `~flag`, which we evaluate, meaning we have to evaluate the definition of
    // `flag` -- and we are in a cycle. With the fix, we short-circuit evaluating reachability
    // constraints on "unbound" if a symbol is otherwise not bound.
    db.write_dedented(
        "src/a.py",
        "
            from __future__ import annotations

            def f():
                flag: bool = True
                if flag:
                    return True
            ",
    )
    .unwrap();

    db.clear_salsa_events();
    assert_file_diagnostics(&db, "src/a.py", &[]);
    let events = db.take_salsa_events();
    let cycles = salsa::attach(&db, || {
        events
            .iter()
            .filter_map(|event| {
                if let salsa::EventKind::WillIterateCycle { database_key, .. } = event.kind {
                    Some(format!("{database_key:?}"))
                } else {
                    None
                }
            })
            .collect::<Vec<_>>()
    });
    let expected: Vec<String> = vec![];
    assert_eq!(cycles, expected);
}

const MANY_WIDGETS: usize = 400;
const MANY_NON_TERMINAL_CALLS: usize = 1_100;
const FEW_NON_TERMINAL_CALLS: usize = 80;

#[test]
fn implicit_attribute_after_many_non_terminal_calls() -> anyhow::Result<()> {
    let handle = std::thread::Builder::new()
        .name("implicit-attribute-stack-test".into())
        // Match the stack size used by ty's production worker threads.
        .stack_size(ruff_db::STACK_SIZE)
        .spawn(|| {
            let mut db = setup_db();
            let mut ui = String::from(
                r#"from widgets import Widget

class Ui:
    def setup(self):
"#,
            );

            for index in 0..MANY_WIDGETS {
                write!(
                    ui,
                    concat!(
                        "        self.widget_{index} = Widget()\n",
                        "        self.widget_{index}.configure()\n",
                        "        self.widget_{index}.configure()\n",
                        "        self.widget_{index}.configure()\n",
                    ),
                    index = index,
                )?;
            }
            ui.push_str("        self.target = Widget()\n");

            db.write_files([
                (
                    "/src/widgets.py",
                    r#"class Widget:
    def configure(self) -> None: ...
"#,
                ),
                ("/src/ui.py", &ui),
                (
                    "/src/consumer.py",
                    r#"from typing_extensions import reveal_type
from ui import Ui
from widgets import Widget

class Form(Ui):
    def target_widget(self) -> Widget:
        reveal_type(self.target)
        return self.target
"#,
                ),
            ])?;

            assert_revealed_type(&db, "/src/consumer.py", "Widget");

            Ok(())
        })?;

    handle.join().expect("regression test thread panicked")
}

#[test]
fn nested_implicit_attribute_graphs_do_not_overflow_stack() -> anyhow::Result<()> {
    let handle = std::thread::Builder::new()
        .name("nested-implicit-attribute-stack-test".into())
        .stack_size(ruff_db::STACK_SIZE)
        .spawn(|| {
            let mut db = setup_db();
            let mut inner = String::from(
                r#"from widgets import Widget

class Inner:
    def setup(self):
"#,
            );
            for index in 0..MANY_WIDGETS {
                write!(
                    inner,
                    concat!(
                        "        self.widget_{index} = Widget()\n",
                        "        self.widget_{index}.configure()\n",
                        "        self.widget_{index}.configure()\n",
                        "        self.widget_{index}.configure()\n",
                    ),
                    index = index,
                )?;
            }
            inner.push_str("        self.target = Widget()\n");

            let mut outer = String::from(
                r#"from inner import Inner

def noop() -> None: ...

class Outer:
    def setup(self, inner: Inner, flag: bool):
"#,
            );
            for _ in 0..FEW_NON_TERMINAL_CALLS {
                outer.push_str("        noop()\n");
            }
            outer.push_str(
                r#"        if flag:
            inner.target.configure()
        self.target = inner
"#,
            );

            db.write_files([
                (
                    "/src/widgets.py",
                    r#"class Widget:
    def configure(self) -> None: ...
"#,
                ),
                ("/src/inner.py", &inner),
                ("/src/outer.py", &outer),
                (
                    "/src/consumer.py",
                    r#"from typing_extensions import reveal_type
from inner import Inner
from outer import Outer

class Form(Outer):
    def target_inner(self) -> Inner:
        reveal_type(self.target)
        return self.target
"#,
                ),
            ])?;

            assert_revealed_type(&db, "/src/consumer.py", "Inner");

            Ok(())
        })?;

    handle.join().expect("regression test thread panicked")
}

#[test]
fn implicit_attribute_preserves_terminal_narrowing_after_many_calls() -> anyhow::Result<()> {
    let mut db = setup_db();
    let mut ui = String::from(
        r#"import sys

def noop() -> None: ...

class Ui:
    def setup(self, value: int | None):
"#,
    );
    for _ in 0..MANY_NON_TERMINAL_CALLS {
        ui.push_str("        noop()\n");
    }
    ui.push_str(
        r#"        if value is None:
            sys.exit()
        self.target = value
"#,
    );

    db.write_files([
        ("/src/package/__init__.py", ""),
        ("/src/package/ui.py", &ui),
        (
            "/src/package/consumer.py",
            r#"from typing_extensions import reveal_type
from .ui import Ui

class Form(Ui):
    def target_value(self) -> int:
        reveal_type(self.target)
        return self.target
"#,
        ),
    ])?;

    assert_revealed_type(&db, "/src/package/consumer.py", "int");

    Ok(())
}

#[test]
fn nested_binding_remains_precise_after_many_module_calls() -> anyhow::Result<()> {
    let mut db = setup_db();
    let calls = "noop()\n".repeat(MANY_NON_TERMINAL_CALLS);
    let source = format!(
        r#"def noop() -> None: ...
{calls}value = 1
values = [(value := 'abc') for _ in range(2)]
value.bit_count()
"#
    );
    db.write_file("/src/main.py", &source)?;

    assert_file_diagnostics(
        &db,
        "/src/main.py",
        &["Object of type `str` has no attribute `bit_count`"],
    );

    Ok(())
}

#[test]
fn redundant_cast_without_closing_parenthesis() -> anyhow::Result<()> {
    let mut db = setup_db();

    // A final newline changes the recovered argument range, so these files deliberately omit it.
    for suffix in ["", " # comment"] {
        let source =
            format!("from typing import cast\n\ndef f(x: int):\n    return cast(int, x{suffix}");
        db.write_file("/src/main.py", &source)?;
        assert_file_diagnostics(&db, "/src/main.py", &["Value is already of type `int`"]);
    }

    Ok(())
}

// Incremental inference tests
#[test]
fn captured_collection_context_after_rebinding() -> anyhow::Result<()> {
    for query_order in [["initial", "callback"], ["callback", "initial"]] {
        let mut db = setup_db();
        for (rebind, expected) in [
            ("", "list[str]"),
            ("    values = [1]\n", "list[Unknown]"),
            ("", "list[str]"),
        ] {
            let source = format!(
                r#"def outer():
    values = []
    initial = values
    callback = lambda: consume(values)
{rebind}
def consume(values: list[str]) -> None: ...
"#
            );
            db.write_file("/src/main.py", &source)?;
            for name in query_order {
                let ty = get_symbol(&db, "/src/main.py", &["outer"], name).expect_type();
                let expected = if name == "initial" {
                    expected
                } else {
                    "() -> None"
                };
                assert_eq!(
                    ty.display(&db, &db.program_environment()).to_string(),
                    expected,
                    "symbol {name}, query order {query_order:?}, rebind {rebind:?}",
                );
            }
            let expected_diagnostics = if rebind.is_empty() {
                &[][..]
            } else {
                &["Argument to function `consume` is incorrect"]
            };
            assert_file_diagnostics(&db, "/src/main.py", expected_diagnostics);
        }
    }
    Ok(())
}

#[test]
fn returned_local_context_after_formal_changes() -> anyhow::Result<()> {
    for query_order in [["binding", "file"], ["file", "binding"]] {
        let mut db = setup_db();
        for (annotation, expected) in [
            ("Callable[[str], str]", "(value: str) -> str"),
            ("object", "(value) -> str"),
            ("Callable[[str], str]", "(value: str) -> str"),
        ] {
            db.write_file(
                "/src/main.py",
                format!(
                    r#"from collections.abc import Callable

def consume(callback: {annotation}, value: str) -> str:
    return value

def factory() -> Callable[[str], str]:
    callback = lambda value: consume(callback, value)
    return callback
"#,
                ),
            )?;
            for query in query_order {
                if query == "file" {
                    assert_file_diagnostics(&db, "/src/main.py", &[]);
                } else {
                    let file = system_path_to_file(&db, "/src/main.py")?;
                    let file = program_file(&db, file);
                    let module = parsed_module(&db, file.python_file(&db)).load(&db);
                    let Some(ast::Stmt::FunctionDef(factory)) = module.syntax().body.last() else {
                        panic!("expected factory as the last statement");
                    };
                    let Some(ast::Stmt::Assign(assignment)) = factory.body.first() else {
                        panic!("expected callback assignment as the first statement");
                    };
                    let [ast::Expr::Name(target)] = assignment.targets.as_slice() else {
                        panic!("expected a single callback name target");
                    };
                    let definition = semantic_index(&db, file).expect_single_definition(target);
                    let ty = crate::types::binding_type(&db, definition);
                    assert_eq!(
                        ty.display(&db, &db.program_environment()).to_string(),
                        expected,
                        "query order {query_order:?}, formal {annotation}",
                    );
                }
            }
        }
    }
    Ok(())
}

#[track_caller]
fn first_public_binding<'db>(db: &'db TestDb, file: File, name: &str) -> Definition<'db> {
    let scope = global_scope(db, program_file(db, file));
    use_def_map(db, scope)
        .end_of_scope_symbol_bindings(place_table(db, scope).symbol_id(name).unwrap())
        .find_map(|b| b.binding.definition())
        .expect("no binding found")
}

#[test]
fn dependency_public_symbol_type_change() -> anyhow::Result<()> {
    let mut db = setup_db();

    db.write_files([
        ("/src/a.py", "from foo import x"),
        ("/src/foo.py", "x: int = 10\ndef foo(): ..."),
    ])?;

    let a = system_path_to_file(&db, "/src/a.py").unwrap();
    let x_ty = global_symbol(&db, a, "x").place.expect_type();

    assert_eq!(
        x_ty.display(&db, &db.program_environment()).to_string(),
        "int"
    );

    // Change `x` to a different value
    db.write_file("/src/foo.py", "x: bool = True\ndef foo(): ...")?;

    let a = system_path_to_file(&db, "/src/a.py").unwrap();

    let x_ty_2 = global_symbol(&db, a, "x").place.expect_type();

    assert_eq!(
        x_ty_2.display(&db, &db.program_environment()).to_string(),
        "bool"
    );

    Ok(())
}

#[test]
fn undefined_reveal_fix_updates_after_source_changes() -> anyhow::Result<()> {
    let mut db = TestDbBuilder::new()
        .with_python_version(PythonVersion::PY311)
        .build()?;

    // Recheck the same file after changing its imports and line endings. Both function
    // scopes should use the current file's import locations and formatting.
    for (prefix, line_ending, fixed_prefix) in [
        (
            "from typing import Any\n\n",
            "\n",
            "from typing import Any, reveal_type\n\n",
        ),
        (
            "from __future__ import annotations\r\n\r\n",
            "\r\n",
            "from __future__ import annotations\r\nfrom typing import reveal_type\r\n\r\n",
        ),
        ("", "\n", "from typing import reveal_type\n"),
    ] {
        let body = "def f():\n    reveal_type(1)\ndef g():\n    reveal_type(2)\n"
            .replace('\n', line_ending);
        let source = format!("{prefix}{body}");
        db.write_file("/src/main.py", &source)?;
        let file = system_path_to_file(&db, "/src/main.py")?;
        let diagnostics = check_types(&db, program_file(&db, file));
        let fixes: Vec<_> = diagnostics
            .iter()
            .filter(|diagnostic| diagnostic.id() == DiagnosticId::lint("undefined-reveal"))
            .filter_map(Diagnostic::fix)
            .collect();
        assert_eq!(fixes.len(), 2);
        for fix in fixes {
            let [edit] = fix.edits() else {
                anyhow::bail!("expected a single import edit");
            };
            let mut fixed = source.clone();
            fixed.replace_range(edit.range().to_std_range(), edit.content().unwrap_or(""));
            assert_eq!(fixed, format!("{fixed_prefix}{body}"));
        }
    }
    Ok(())
}

#[test]
fn redundant_elif_fix_preserves_line_endings_and_checks_cleanly() -> anyhow::Result<()> {
    let registry = crate::default_lint_registry();
    let mut rules = RuleSelection::from_registry(registry);
    rules.enable(
        registry.get("redundant-condition-strict")?,
        Severity::Warning,
        LintSource::File,
    );
    let mut db = TestDbBuilder::new()
        .with_python_version(PythonVersion::PY311)
        .with_rule_selection(rules)
        .build()?;

    // Reuse the file to check that edits use the current imports and source style.
    for (newline, indent, trailing_newline, existing_import) in [
        ("\n", "    ", true, false),
        ("\r\n", "\t", false, true),
        ("\r", "  ", false, false),
    ] {
        let mut source = format!(
            "def f(value: str | int):\n\
            {indent}if isinstance(value, str):\n\
            {indent}{indent}print(value)\n\
            {indent}elif isinstance(value, int):\n\
            {indent}{indent}print(value)  # Inline comment.\n\
            {indent}{indent}# Trailing comment."
        )
        .replace('\n', newline);
        let (import, name) = if existing_import {
            (
                "from typing import assert_never as unreachable",
                "unreachable",
            )
        } else {
            ("from typing import assert_never", "assert_never")
        };
        if existing_import {
            source = format!("{import}{newline}{source}");
        }
        if trailing_newline {
            source.push_str(newline);
        }
        db.write_file("/src/main.py", &source)?;
        let file = system_path_to_file(&db, "/src/main.py")?;
        let diagnostics = check_types(&db, program_file(&db, file));
        let [diagnostic] = diagnostics.as_slice() else {
            anyhow::bail!("expected one diagnostic: {diagnostics:#?}");
        };
        let fix = diagnostic
            .fix()
            .ok_or_else(|| anyhow::anyhow!("expected an autofix"))?;
        let mut fixed = source.clone();
        for edit in fix.edits().iter().rev() {
            fixed.replace_range(edit.range().to_std_range(), edit.content().unwrap_or(""));
        }
        let prefix = if existing_import {
            String::new()
        } else {
            format!("{import}{newline}")
        };
        let separator = if trailing_newline { "" } else { newline };
        assert_eq!(
            fixed,
            format!(
                "{prefix}{source}{separator}{indent}else:{newline}{indent}{indent}{name}(value){newline}"
            )
        );
        db.write_file("/src/main.py", fixed)?;
        assert_file_diagnostics(&db, "/src/main.py", &[]);
    }
    Ok(())
}

#[test]
fn function_inference_regions_are_disjoint() -> anyhow::Result<()> {
    let mut db = setup_db();
    db.write_dedented(
        "/src/main.py",
        r#"
        def f(x: int = 1) -> int: return x
        def annotated(x: int) -> int: return x
        def defaulted(x=1): return x
        "#,
    )?;
    let file = system_path_to_file(&db, "/src/main.py")?;
    db.clear_salsa_events();
    assert_file_diagnostics(&db, "/src/main.py", &[]);
    let events = db.take_salsa_events();
    assert_function_query_was_run(
        &db,
        infer_function_default_types,
        first_public_binding(&db, file, "f"),
        &events,
    );
    assert_function_query_was_not_run(
        &db,
        infer_function_default_types,
        first_public_binding(&db, file, "annotated"),
        &events,
    );
    assert_function_query_was_not_run(
        &db,
        infer_deferred_types,
        first_public_binding(&db, file, "defaulted"),
        &events,
    );

    let definition = first_public_binding(&db, file, "f");
    let module = parsed_module(&db, program_file(&db, file).python_file(&db)).load(&db);
    let DefinitionKind::Function(function) = definition.kind(&db) else {
        anyhow::bail!("expected a function definition");
    };
    let Some(parameter) = function.node(&module).parameters.find("x") else {
        anyhow::bail!("expected parameter x");
    };
    let (Some(annotation), Some(default)) = (parameter.annotation(), parameter.default()) else {
        anyhow::bail!("expected an annotated parameter with a default");
    };

    let annotations = infer_deferred_types(&db, definition);
    assert!(annotations.try_expression_type(annotation).is_some());
    assert!(annotations.try_expression_type(default).is_none());
    let defaults = infer_function_default_types(&db, definition);
    assert!(defaults.try_expression_type(default).is_some());
    assert!(defaults.try_expression_type(annotation).is_none());
    assert_eq!(
        crate::types::definition_expression_type(&db, definition, default),
        defaults.expression_type(default)
    );
    Ok(())
}

#[test]
fn lazy_parameter_defaults() -> anyhow::Result<()> {
    let mut db = setup_db();
    db.write_files([
        ("/src/defaults.py", "def f(x: int = 1) -> int: return x"),
        ("/src/main.py", "from defaults import f\nresult = f()"),
    ])?;
    let source = system_path_to_file(&db, "/src/defaults.py")?;
    let main = system_path_to_file(&db, "/src/main.py")?;
    db.clear_salsa_events();
    let result = global_symbol(&db, main, "result").place.expect_type();
    assert_eq!(
        result.display(&db, &db.program_environment()).to_string(),
        "int"
    );
    let events = db.take_salsa_events();
    assert_function_query_was_not_run(
        &db,
        infer_function_default_types,
        first_public_binding(&db, source, "f"),
        &events,
    );

    // Display needs the actual default, unlike call checking.
    let function = global_symbol(&db, source, "f").place.expect_type();
    assert_eq!(
        function.display(&db, &db.program_environment()).to_string(),
        "def f(x: int = 1) -> int"
    );
    let events = db.take_salsa_events();
    assert_function_query_was_run(
        &db,
        infer_function_default_types,
        first_public_binding(&db, source, "f"),
        &events,
    );

    db.write_file("/src/defaults.py", "def f(x: int = 2) -> int: return x")?;
    db.clear_salsa_events();
    let result = global_symbol(&db, main, "result").place.expect_type();
    assert_eq!(
        result.display(&db, &db.program_environment()).to_string(),
        "int"
    );
    let events = db.take_salsa_events();
    assert_function_query_was_not_run(
        &db,
        infer_definition_types,
        first_public_binding(&db, main, "result"),
        &events,
    );
    let function = global_symbol(&db, source, "f").place.expect_type();
    assert_eq!(
        function.display(&db, &db.program_environment()).to_string(),
        "def f(x: int = 2) -> int"
    );
    Ok(())
}

#[test]
fn parameter_default_presence_invalidates_caller() -> anyhow::Result<()> {
    let mut db = setup_db();
    let with_default = "def f(x: int = 1) -> int: return x";
    db.write_files([
        ("/src/defaults.py", with_default),
        ("/src/main.py", "from defaults import f\nf()"),
    ])?;
    assert_file_diagnostics(&db, "/src/main.py", &[]);

    db.write_file("/src/defaults.py", "def f(x: int) -> int: return x")?;
    assert_file_diagnostics(
        &db,
        "/src/main.py",
        &["No argument provided for required parameter `x` of function `f`"],
    );

    db.write_file("/src/defaults.py", with_default)?;
    assert_file_diagnostics(&db, "/src/main.py", &[]);
    Ok(())
}

#[test]
fn dynamic_class_metaclass_updates_after_base_change() -> anyhow::Result<()> {
    let mut db = setup_db();
    let base = "\
class Meta1(type): ...
class Meta2(type): ...
class Base(metaclass=Meta1): ...
";
    db.write_files([
        ("/src/base.py", base),
        (
            "/src/main.py",
            "\
from typing_extensions import reveal_type
from base import Base

C = type('C', (Base,), {})
reveal_type(type(C))
",
        ),
    ])?;
    assert_revealed_type(&db, "/src/main.py", "<class 'Meta1'>");

    db.write_file(
        "/src/base.py",
        base.replace("metaclass=Meta1", "metaclass=Meta2"),
    )?;
    assert_revealed_type(&db, "/src/main.py", "<class 'Meta2'>");

    db.write_file("/src/base.py", base)?;
    assert_revealed_type(&db, "/src/main.py", "<class 'Meta1'>");
    Ok(())
}

#[test]
fn field_specifier_default_value_invalidates_caller() -> anyhow::Result<()> {
    let mut db = setup_db();
    let field_source = r#"from typing import Any

def field(*, init: bool = False) -> Any: ...
"#;
    db.write_files([
        ("/src/fields.py", field_source),
        (
            "/src/model.py",
            r#"from typing_extensions import dataclass_transform
from fields import field

@dataclass_transform(field_specifiers=(field,))
class ModelBase: ...

class Model(ModelBase):
    value: int = field()
"#,
        ),
        ("/src/main.py", "from model import Model\nModel()"),
    ])?;
    assert_file_diagnostics(&db, "/src/main.py", &[]);

    // This changes a default's value, not the field specifier's callable signature.
    db.write_file(
        "/src/fields.py",
        field_source.replace("init: bool = False", "init: bool = True"),
    )?;
    assert_file_diagnostics(
        &db,
        "/src/main.py",
        &["No argument provided for required parameter `value`"],
    );

    db.write_file("/src/fields.py", field_source)?;
    assert_file_diagnostics(&db, "/src/main.py", &[]);
    Ok(())
}

#[test]
fn dependency_internal_symbol_change() -> anyhow::Result<()> {
    let mut db = setup_db();

    db.write_files([
        ("/src/a.py", "from foo import x"),
        ("/src/foo.py", "x: int = 10\ndef foo(): y = 1"),
    ])?;

    let a = system_path_to_file(&db, "/src/a.py").unwrap();
    let x_ty = global_symbol(&db, a, "x").place.expect_type();

    assert_eq!(
        x_ty.display(&db, &db.program_environment()).to_string(),
        "int"
    );

    db.write_file("/src/foo.py", "x: int = 10\ndef foo(): pass")?;

    let a = system_path_to_file(&db, "/src/a.py").unwrap();

    db.clear_salsa_events();

    let x_ty_2 = global_symbol(&db, a, "x").place.expect_type();

    assert_eq!(
        x_ty_2.display(&db, &db.program_environment()).to_string(),
        "int"
    );

    let events = db.take_salsa_events();

    assert_function_query_was_not_run(
        &db,
        infer_definition_types,
        first_public_binding(&db, a, "x"),
        &events,
    );

    Ok(())
}

#[test]
fn dependency_unrelated_symbol() -> anyhow::Result<()> {
    let mut db = setup_db();

    db.write_files([
        ("/src/a.py", "from foo import x"),
        ("/src/foo.py", "x: int = 10\ny: bool = True"),
    ])?;

    let a = system_path_to_file(&db, "/src/a.py").unwrap();
    let x_ty = global_symbol(&db, a, "x").place.expect_type();

    assert_eq!(
        x_ty.display(&db, &db.program_environment()).to_string(),
        "int"
    );

    db.write_file("/src/foo.py", "x: int = 10\ny: bool = False")?;

    let a = system_path_to_file(&db, "/src/a.py").unwrap();

    db.clear_salsa_events();

    let x_ty_2 = global_symbol(&db, a, "x").place.expect_type();

    assert_eq!(
        x_ty_2.display(&db, &db.program_environment()).to_string(),
        "int"
    );

    let events = db.take_salsa_events();

    assert_function_query_was_not_run(
        &db,
        infer_definition_types,
        first_public_binding(&db, a, "x"),
        &events,
    );
    Ok(())
}

#[test]
fn dependency_implicit_instance_attribute() -> anyhow::Result<()> {
    fn x_rhs_expression(db: &TestDb) -> Expression<'_> {
        let file_main = system_path_to_file(db, "/src/main.py").unwrap();
        let ast = parsed_module(db, program_file(db, file_main).python_file(db)).load(db);
        // Get the second statement in `main.py` (x = …) and extract the expression
        // node on the right-hand side:
        let x_rhs_node = &ast.syntax().body[1].as_assign_stmt().unwrap().value;

        let index = semantic_index(db, program_file(db, file_main));
        index.expression(x_rhs_node.as_ref())
    }

    let mut db = setup_db();

    db.write_dedented(
        "/src/mod.py",
        r#"
        class C:
            def f(self):
                self.attr: int | None = None
        "#,
    )?;
    db.write_dedented(
        "/src/main.py",
        r#"
        from mod import C
        # multiple targets ensures RHS is a standalone expression, relied on by this test
        x = y = C().attr
        "#,
    )?;

    let file_main = system_path_to_file(&db, "/src/main.py").unwrap();
    let attr_ty = global_symbol(&db, file_main, "x").place.expect_type();
    assert_eq!(
        attr_ty.display(&db, &db.program_environment()).to_string(),
        "int | None"
    );

    // Change the type of `attr` to `str | None`; this should trigger the type of `x` to be re-inferred
    db.write_dedented(
        "/src/mod.py",
        r#"
        class C:
            def f(self):
                self.attr: str | None = None
        "#,
    )?;

    let events = {
        db.clear_salsa_events();
        let attr_ty = global_symbol(&db, file_main, "x").place.expect_type();
        assert_eq!(
            attr_ty.display(&db, &db.program_environment()).to_string(),
            "str | None"
        );
        db.take_salsa_events()
    };
    assert_function_query_was_run(
        &db,
        infer_expression_types_impl,
        InferExpression::Bare(x_rhs_expression(&db)),
        &events,
    );

    // Add a comment; this should not trigger the type of `x` to be re-inferred
    db.write_dedented(
        "/src/mod.py",
        r#"
        class C:
            def f(self):
                # a comment!
                self.attr: str | None = None
        "#,
    )?;

    let events = {
        db.clear_salsa_events();
        let attr_ty = global_symbol(&db, file_main, "x").place.expect_type();
        assert_eq!(
            attr_ty.display(&db, &db.program_environment()).to_string(),
            "str | None"
        );
        db.take_salsa_events()
    };

    assert_function_query_was_not_run(
        &db,
        infer_expression_types_impl,
        InferExpression::Bare(x_rhs_expression(&db)),
        &events,
    );

    Ok(())
}

/// This test verifies that changing a class's declaration in a non-meaningful way (e.g. by adding a comment)
/// doesn't trigger type inference for expressions that depend on the class's members.
#[test]
fn dependency_own_instance_member() -> anyhow::Result<()> {
    fn x_rhs_expression(db: &TestDb) -> Expression<'_> {
        let file_main = system_path_to_file(db, "/src/main.py").unwrap();
        let ast = parsed_module(db, program_file(db, file_main).python_file(db)).load(db);
        // Get the second statement in `main.py` (x = …) and extract the expression
        // node on the right-hand side:
        let x_rhs_node = &ast.syntax().body[1].as_assign_stmt().unwrap().value;

        let index = semantic_index(db, program_file(db, file_main));
        index.expression(x_rhs_node.as_ref())
    }

    let mut db = setup_db();

    db.write_dedented(
        "/src/mod.py",
        r#"
        class C:
            if random.choice([True, False]):
                attr: int = 42
            else:
                attr: None = None
        "#,
    )?;
    db.write_dedented(
        "/src/main.py",
        r#"
        from mod import C
        # multiple targets ensures RHS is a standalone expression, relied on by this test
        x = y = C().attr
        "#,
    )?;

    let file_main = system_path_to_file(&db, "/src/main.py").unwrap();
    let attr_ty = global_symbol(&db, file_main, "x").place.expect_type();
    assert_eq!(
        attr_ty.display(&db, &db.program_environment()).to_string(),
        "int | None"
    );

    // Change the type of `attr` to `str | None`; this should trigger the type of `x` to be re-inferred
    db.write_dedented(
        "/src/mod.py",
        r#"
        class C:
            if random.choice([True, False]):
                attr: str = "42"
            else:
                attr: None = None
        "#,
    )?;

    let events = {
        db.clear_salsa_events();
        let attr_ty = global_symbol(&db, file_main, "x").place.expect_type();
        assert_eq!(
            attr_ty.display(&db, &db.program_environment()).to_string(),
            "str | None"
        );
        db.take_salsa_events()
    };
    assert_function_query_was_run(
        &db,
        infer_expression_types_impl,
        InferExpression::Bare(x_rhs_expression(&db)),
        &events,
    );

    // Add a comment; this should not trigger the type of `x` to be re-inferred
    db.write_dedented(
        "/src/mod.py",
        r#"
        class C:
            # comment
            if random.choice([True, False]):
                attr: str = "42"
            else:
                attr: None = None
        "#,
    )?;

    let events = {
        db.clear_salsa_events();
        let attr_ty = global_symbol(&db, file_main, "x").place.expect_type();
        assert_eq!(
            attr_ty.display(&db, &db.program_environment()).to_string(),
            "str | None"
        );
        db.take_salsa_events()
    };

    assert_function_query_was_not_run(
        &db,
        infer_expression_types_impl,
        InferExpression::Bare(x_rhs_expression(&db)),
        &events,
    );

    Ok(())
}

#[test]
fn dependency_implicit_class_member() -> anyhow::Result<()> {
    fn x_rhs_expression(db: &TestDb) -> Expression<'_> {
        let file_main = system_path_to_file(db, "/src/main.py").unwrap();
        let ast = parsed_module(db, program_file(db, file_main).python_file(db)).load(db);
        // Get the third statement in `main.py` (x = …) and extract the expression
        // node on the right-hand side:
        let x_rhs_node = &ast.syntax().body[2].as_assign_stmt().unwrap().value;

        let index = semantic_index(db, program_file(db, file_main));
        index.expression(x_rhs_node.as_ref())
    }

    let mut db = setup_db();

    db.write_dedented(
        "/src/mod.py",
        r#"
        class C:
            def __init__(self):
                self.instance_attr: str = "24"

            @classmethod
            def method(cls):
                cls.class_attr: int = 42
        "#,
    )?;
    db.write_dedented(
        "/src/main.py",
        r#"
        from mod import C
        C.method()
        # multiple targets ensures RHS is a standalone expression, relied on by this test
        x = y = C().class_attr
        "#,
    )?;

    let file_main = system_path_to_file(&db, "/src/main.py").unwrap();
    let attr_ty = global_symbol(&db, file_main, "x").place.expect_type();
    assert_eq!(
        attr_ty.display(&db, &db.program_environment()).to_string(),
        "int"
    );

    // Change the type of `class_attr` to `str`; this should trigger the type of `x` to be re-inferred
    db.write_dedented(
        "/src/mod.py",
        r#"
        class C:
            def __init__(self):
                self.instance_attr: str = "24"

            @classmethod
            def method(cls):
                cls.class_attr: str = "42"
        "#,
    )?;

    let events = {
        db.clear_salsa_events();
        let attr_ty = global_symbol(&db, file_main, "x").place.expect_type();
        assert_eq!(
            attr_ty.display(&db, &db.program_environment()).to_string(),
            "str"
        );
        db.take_salsa_events()
    };
    assert_function_query_was_run(
        &db,
        infer_expression_types_impl,
        InferExpression::Bare(x_rhs_expression(&db)),
        &events,
    );

    // Add a comment; this should not trigger the type of `x` to be re-inferred
    db.write_dedented(
        "/src/mod.py",
        r#"
        class C:
            def __init__(self):
                self.instance_attr: str = "24"

            @classmethod
            def method(cls):
                # comment
                cls.class_attr: str = "42"
        "#,
    )?;

    let events = {
        db.clear_salsa_events();
        let attr_ty = global_symbol(&db, file_main, "x").place.expect_type();
        assert_eq!(
            attr_ty.display(&db, &db.program_environment()).to_string(),
            "str"
        );
        db.take_salsa_events()
    };

    assert_function_query_was_not_run(
        &db,
        infer_expression_types_impl,
        InferExpression::Bare(x_rhs_expression(&db)),
        &events,
    );

    Ok(())
}

/// Inferring the result of a call-expression shouldn't need to re-run after
/// a trivial change to the function's file (e.g. by adding a docstring to the function).
#[test]
fn call_type_doesnt_rerun_when_only_callee_changed() -> anyhow::Result<()> {
    let mut db = setup_db();

    db.write_dedented(
        "src/foo.py",
        r#"
        def foo() -> int:
            return 5
    "#,
    )?;
    db.write_dedented(
        "src/bar.py",
        r#"
        from foo import foo

        # multiple targets ensures RHS is a standalone expression, relied on by this test
        a = b = foo()
        "#,
    )?;

    let bar = system_path_to_file(&db, "src/bar.py")?;
    let a = global_symbol(&db, bar, "a").place;

    assert_eq!(
        a.expect_type(),
        KnownClass::Int.to_instance(&db, &db.program_environment())
    );
    let events = db.take_salsa_events();

    let module = parsed_module(&db, program_file(&db, bar).python_file(&db)).load(&db);
    let call = &*module.syntax().body[1].as_assign_stmt().unwrap().value;
    let foo_call = semantic_index(&db, program_file(&db, bar)).expression(call);

    assert_function_query_was_run(
        &db,
        infer_expression_types_impl,
        InferExpression::Bare(foo_call),
        &events,
    );

    // Add a docstring to foo to trigger a re-run.
    // The bar-call site of foo should not be re-run because of that
    db.write_dedented(
        "src/foo.py",
        r#"
        def foo() -> int:
            "Computes a value"
            return 5
        "#,
    )?;
    db.clear_salsa_events();

    let a = global_symbol(&db, bar, "a").place;

    assert_eq!(
        a.expect_type(),
        KnownClass::Int.to_instance(&db, &db.program_environment())
    );
    let events = db.take_salsa_events();

    let module = parsed_module(&db, program_file(&db, bar).python_file(&db)).load(&db);
    let call = &*module.syntax().body[1].as_assign_stmt().unwrap().value;
    let foo_call = semantic_index(&db, program_file(&db, bar)).expression(call);

    assert_function_query_was_not_run(
        &db,
        infer_expression_types_impl,
        InferExpression::Bare(foo_call),
        &events,
    );

    Ok(())
}

#[test]
fn function_output_correspondence_ignores_unreachable_returns() -> anyhow::Result<()> {
    let mut db = setup_db();
    db.write_dedented(
        "/src/main.py",
        r#"
        from typing import Generator
        def dead() -> int:
            if False:
                return "bad"
            return 1
        def live() -> int:
            return "bad"
        def generator() -> Generator[int, None, int]:
            yield 1
            if False:
                return "bad"
            return 1
    "#,
    )?;
    let file = system_path_to_file(&db, "/src/main.py")?;
    let names = ["dead", "live", "generator"];
    db.select_function_inference(Some((
        file,
        names.map(str::to_owned).to_vec(),
        crate::FunctionInferenceMode::OutputProof,
    )));
    let model = crate::SemanticModel::new(&db, program_file(&db, file));
    for (name, corresponds, has_errors) in [
        ("dead", true, false),
        ("live", false, true),
        ("generator", true, false),
    ] {
        let facts = model
            .function_inference_facts(first_public_binding(&db, file, name))
            .unwrap();
        assert_eq!(
            facts.return_type_correspondence,
            Some(corresponds),
            "{name}"
        );
        assert_eq!(facts.has_errors, has_errors, "{name}");
    }
    let diagnostics = crate::types::check_types(&db, program_file(&db, file));
    let ids: Vec<_> = diagnostics
        .iter()
        .map(|diagnostic| diagnostic.id().as_str())
        .collect();
    assert_eq!(ids, ["invalid-return-type"]);
    Ok(())
}

#[test]
fn keyword_unpack_correspondence() -> anyhow::Result<()> {
    let mut db = TestDbBuilder::new()
        .with_python_version(PythonVersion::PY313)
        .build()?;
    db.write_dedented(
        "/src/main.py",
        r#"
        from typing import Any, Callable, Protocol
        from typing_extensions import NotRequired, TypedDict, Unpack

        class Named(Protocol):
            def __call__(self, *, name: str) -> None: ...

        class Closed(TypedDict, closed=True):
            run: Named

        class Opaque(TypedDict, closed=True):
            run: Callable[..., None]

        class Optional(TypedDict, total=False, closed=True):
            run: Named

        class Open(TypedDict):
            run: Named

        class Tag(TypedDict, closed=True):
            tag: str

        class Forward(TypedDict, closed=True):
            name: str
            run: NotRequired[Named]

        class OptionalOpaque(TypedDict, total=False, closed=True):
            run: Callable[..., None]

        class OptionalNarrow(TypedDict, total=False, closed=True):
            run: Callable[[str], None]

        class OpenForward(TypedDict):
            name: str
            run: NotRequired[Named]

        def callback(*, name: str) -> None: pass
        def consume(*, run: Named = callback) -> None: pass
        def consume_omitted(*, run: Callable[..., None]) -> None: pass
        def consume_required(*, run: Named) -> None: pass
        def consume_forward(*, name: str, run: Named = callback) -> None: pass
        def consume_open(*, name: str, **kwargs: object) -> None: pass
        def consume_positional_only(name: str, /, **kwargs: object) -> None: pass
        def consume_positional_name(name: str, **kwargs: object) -> None: pass
        def consume_open_default(*, name: str = "target", **kwargs: object) -> None: pass
        def wide(value: Any) -> None: pass
        def consume_wide(*, run: Callable[[Any], None] = wide) -> None: pass
        def consume_optional_omitted(*, run: Callable[..., None] = wide) -> None: pass
        def consume_objects(**kwargs: object) -> None: pass
        def consume_named(**kwargs: Named) -> None: pass
        def empty() -> None: pass

        class Consumer:
            def accept(self, *, run: Named) -> None: pass
            def forward(self, *, name: str, run: Named = callback) -> None: pass

        def pass_through(value: Named) -> Named:
            return value

        def known(value: Closed) -> None:
            consume(**value)

        def opaque(value: Opaque) -> None:
            consume(**value)

        def omitted(value: Opaque) -> None:
            consume_omitted(**value)

        def literal() -> None:
            consume(**{'run': callback})

        def empty_literal() -> None:
            empty(**{})

        def optional(value: Optional) -> None:
            consume(**value)

        def optional_required(value: Optional) -> None:
            consume_required(**value)

        def optional_union(value: Closed | Optional) -> None:
            consume_required(**value)

        def forward(value: Forward) -> None:
            consume_forward(**value)

        def direct_and_optional(value: Optional) -> None:
            consume_forward(name="target", **value)

        def optional_literal(value: Optional) -> None:
            consume(**{**value})

        def optional_narrow(value: OptionalNarrow) -> None:
            consume_wide(**value)

        def optional_omitted(value: OptionalOpaque) -> None:
            consume_optional_omitted(**value)

        def open_forward(value: OpenForward) -> None:
            consume_open(**value)

        def forward_unpacked(**kwargs: Unpack[Forward]) -> None:
            consume_forward(**kwargs)

        def method_optional(consumer: Consumer, value: Forward) -> None:
            consumer.forward(**value)

        def mapping(value: dict[str, Named]) -> None:
            consume_named(**value)

        def open_objects(value: Open) -> None:
            consume_objects(**value)

        def open_direct(value: Open) -> None:
            consume_open(name="target", **value)

        def open_positional_only(value: Open) -> None:
            consume_positional_only("target", **value)

        def open_positional_name(value: Open) -> None:
            consume_positional_name("target", **value)

        def open_hidden_name(value: Open) -> None:
            consume_open_default(**value)

        def duplicate_packs(left: Closed, right: Closed) -> None:
            consume_objects(**left, **right)

        def disjoint_packs(left: Closed, right: Tag) -> None:
            consume_objects(**left, **{}, **right)

        def open_named(value: Open) -> None:
            consume_named(**value)

        def method(consumer: Consumer, value: Closed) -> None:
            consumer.accept(**value)

        def child(value: Callable[..., None]) -> None:
            consume(**{'run': pass_through(value)})
        "#,
    )?;
    let file = system_path_to_file(&db, "/src/main.py")?;
    let cases = [
        ("known", false),
        ("opaque", true),
        ("omitted", false),
        ("literal", false),
        ("empty_literal", false),
        ("optional", false),
        ("optional_required", true),
        ("optional_union", true),
        ("forward", false),
        ("direct_and_optional", false),
        ("optional_literal", false),
        ("optional_narrow", true),
        ("optional_omitted", false),
        ("open_forward", false),
        ("forward_unpacked", false),
        ("method_optional", false),
        ("mapping", true),
        ("open_objects", false),
        ("open_direct", true),
        ("open_positional_only", false),
        ("open_positional_name", true),
        ("open_hidden_name", true),
        ("duplicate_packs", true),
        ("disjoint_packs", false),
        ("open_named", true),
        ("method", false),
        ("child", true),
    ];
    let facts = |db: &TestDb, name: &str| {
        crate::SemanticModel::new(db, program_file(db, file))
            .function_inference_facts(first_public_binding(db, file, name))
            .unwrap()
    };
    let signatures = |db: &TestDb| {
        cases.map(|(name, _)| {
            global_symbol(db, file, name)
                .place
                .expect_type()
                .display(db, &db.program_environment())
                .to_string()
        })
    };
    let ordinary_signatures = signatures(&db);
    let ordinary = cases.map(|(name, _)| facts(&db, name));
    for ((name, _), fact) in cases.into_iter().zip(&ordinary) {
        assert_eq!(fact.has_errors, name == "open_named", "{name}");
    }
    assert!(ordinary.iter().all(|fact| !fact.has_unproved_requirements));
    db.select_function_inference(Some((
        file,
        cases.map(|(name, _)| name.to_owned()).to_vec(),
        FunctionInferenceMode::OutputProof,
    )));
    let mut requirements = Vec::new();
    for ((name, _), ordinary) in cases.into_iter().zip(ordinary) {
        let selected = facts(&db, name);
        requirements.push((name, selected.has_unproved_requirements));
        assert_eq!(selected.return_type_correspondence, Some(true), "{name}");
        assert_eq!(
            (
                selected.has_errors,
                selected.has_diagnostics_or_suppressions
            ),
            (
                ordinary.has_errors,
                ordinary.has_diagnostics_or_suppressions
            ),
            "{name}",
        );
    }
    assert_eq!(requirements, cases);
    assert_eq!(signatures(&db), ordinary_signatures);
    db.select_function_inference(None);
    assert!(
        cases
            .iter()
            .all(|(name, _)| !facts(&db, name).has_unproved_requirements)
    );
    assert_eq!(signatures(&db), ordinary_signatures);
    Ok(())
}

#[test]
fn empty_generic_arguments_use_final_context() -> anyhow::Result<()> {
    let mut db = TestDbBuilder::new()
        .with_python_version(PythonVersion::PY313)
        .build()?;
    db.write_dedented(
        "/src/declarations.pyi",
        r#"
        from typing import Callable, overload
        from typing_extensions import TypeVar

        T = TypeVar("T")
        D = TypeVar("D", default=str)
        S = TypeVar("S", bound=str, default=str)
        I = TypeVar("I", bound=int)
        V = TypeVar("V", bound=int, default=int)
        C = TypeVar("C", str, int, default=int)
        type Items[T] = list[T]

        def identity(value: list[T]) -> list[T]: ...
        def defaulted(value: list[D]) -> list[D]: ...
        def bounded(value: list[I]) -> list[I]: ...
        def attrs(value: dict[S, V]) -> dict[S, V]: ...
        def pair(values: list[D], item: D) -> list[D]: ...
        def reverse(item: D, values: list[D]) -> list[D]: ...
        def nested(value: dict[str, list[D]]) -> dict[str, list[D]]: ...
        def fixed(value: list) -> list: ...
        def constrained(value: list[C]) -> list[C]: ...
        def aliased(value: Items[D]) -> Items[D]: ...
        def callback_then_empty(callback: Callable[[str], str], value: list[T]) -> list[T]: ...
        @overload
        def choose(value: list[D]) -> list[D]: ...
        @overload
        def choose(value: int) -> int: ...
        opaque_list: list
        opaque_dict: dict
        "#,
    )?;
    db.write_dedented(
        "/src/main.py",
        r#"
        from declarations import (
            identity, defaulted, bounded, attrs, pair, reverse, nested, fixed,
            opaque_list, opaque_dict, constrained, aliased, choose, callback_then_empty,
        )
        default_list = defaulted([])
        default_dict = attrs({})
        bounded_list = bounded([])
        peer = pair([], 1)
        reversed_peer = reverse(1, [])
        contextual: list[str] = identity([])
        unresolved = identity([])
        unresolved.append(1)
        opaque = defaulted(opaque_list)
        opaque_attributes = attrs(opaque_dict)
        fixed_unknown = fixed([])
        no_context = []
        spread = defaulted([*opaque_list])
        nested_empty = nested({"key": []})
        nested_call = defaulted(identity([]))
        constrained_default = constrained([])
        alias_context = defaulted(aliased([]))
        overloaded = choose([])
        mixed_contexts = callback_then_empty(lambda value: value, [])
        wrong = attrs({1: "wrong"})
        "#,
    )?;
    let file = system_path_to_file(&db, "/src/main.py")?;
    let expected = [
        ("default_list", "list[str]"),
        ("default_dict", "dict[str, int]"),
        ("bounded_list", "list[Unknown]"),
        ("peer", "list[int]"),
        ("reversed_peer", "list[int]"),
        ("contextual", "list[str]"),
        ("unresolved", "list[Unknown]"),
        ("opaque", "list[Unknown]"),
        ("opaque_attributes", "dict[Unknown, Unknown]"),
        ("fixed_unknown", "list[Unknown]"),
        ("no_context", "list[Unknown]"),
        ("spread", "list[Unknown]"),
        ("nested_empty", "dict[str, list[Unknown]]"),
        ("nested_call", "list[Unknown]"),
        ("constrained_default", "list[int]"),
        ("alias_context", "list[str]"),
        ("overloaded", "list[str]"),
        ("mixed_contexts", "list[Unknown]"),
        ("wrong", "dict[str, int]"),
    ];
    for mode in [
        FunctionInferenceMode::Default,
        FunctionInferenceMode::OutputProof,
        FunctionInferenceMode::Default,
    ] {
        db.select_function_inference(Some((file, vec!["<module>".to_owned()], mode)));
        let program_file = program_file(&db, file);
        let model = crate::SemanticModel::new(&db, program_file);
        let env = db.program_environment();
        let parsed = parsed_module(&db, program_file.python_file(&db)).load(&db);
        let mut checked = 0;
        for statement in parsed.suite() {
            let (name, expression) = match statement {
                ast::Stmt::Assign(assignment) => {
                    let [ast::Expr::Name(name)] = assignment.targets.as_slice() else {
                        continue;
                    };
                    (name.id.as_str(), assignment.value.as_ref())
                }
                ast::Stmt::AnnAssign(assignment) => {
                    let ast::Expr::Name(name) = assignment.target.as_ref() else {
                        continue;
                    };
                    let Some(value) = assignment.value.as_deref() else {
                        continue;
                    };
                    (name.id.as_str(), value)
                }
                _ => continue,
            };
            let Some((_, expected)) = expected.iter().find(|(case, _)| *case == name) else {
                continue;
            };
            checked += 1;
            let result = expression.inferred_type(&model).unwrap();
            assert_eq!(result.display(&db, &env).to_string(), *expected, "{name}");
            assert!(!result.has_provisional_marker(&db, &env), "{name}");
            assert!(!result.has_unspecialized_type_var(&db, &env), "{name}");
            if let ast::Expr::Call(call) = expression {
                for argument in &call.arguments.args {
                    let actual = argument.inferred_type(&model).unwrap();
                    assert!(!actual.has_provisional_marker(&db, &env), "{name}");
                    assert!(!actual.has_unspecialized_type_var(&db, &env), "{name}");
                }
            }
        }
        assert_eq!(checked, expected.len());
        let diagnostics = crate::check_file_unwrap(&db, program_file);
        let ids: Vec<_> = diagnostics
            .iter()
            .map(|diagnostic| diagnostic.id().as_str())
            .collect();
        assert_eq!(ids, ["invalid-argument-type"]);
    }
    Ok(())
}
