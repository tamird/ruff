use std::assert_matches;

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
use crate::types::{BodyDomainError, KnownClass, check_overload_body};
use crate::{HasType, ProgramEnvironment, SemanticModel};

/// Pairs top-level functions by name and their ordinary parameters by position.
/// Signature compatibility is the consumer's responsibility; this fixture exercises
/// annotation ownership after the consumer has selected a correspondence.
enum ExternalSource {
    Annotation,
    MixedFunctionAnnotations,
    LocalAnnotations,
}

impl SourceProvider for ExternalSource {
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
        if matches!(self, Self::LocalAnnotations)
            && let ast::AnyRootNodeRef::Expr(expression) = module.get_by_index(owner)
            && let Some(name) = expression.as_name_expr()
        {
            let source = source_text(db, file.file(db));
            let tail = source[usize::from(name.end())..].lines().next()?;
            if let Some(marker) = tail.find("# type: ") {
                let offset = marker + "# type: ".len();
                return Some(ProvidedAnnotation::Range(TextRange::at(
                    name.end() + TextSize::try_from(offset).unwrap(),
                    TextSize::of(&tail[offset..]),
                )));
            }
        }
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
            let Some(foreign) = declarations.suite().iter().rev().find_map(|statement| {
                let ast::Stmt::FunctionDef(declaration) = statement else {
                    return None;
                };
                let name = if matches!(self, Self::MixedFunctionAnnotations)
                    && function.node_index().load() != owner
                {
                    "other"
                } else {
                    function.name.as_str()
                };
                (declaration.name.as_str() == name).then_some(declaration)
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
fn external_overload_body_domains() -> anyhow::Result<()> {
    fn function(db: &TestDb) -> crate::types::FunctionType<'_> {
        let file = db.program_file(system_path_to_file(db, "/src/main.py").unwrap());
        crate::place::global_symbol(db, file, "pick")
            .place
            .expect_type()
            .expect_function_literal()
    }

    let source = indoc::indoc! {r#"
            from contracts import pick as public_pick

            def pick(*, executable, test):
                if test:
                    return 'test'
                elif executable:
                    return 1
                else:
                    return b'alias'

            ordinary = pick(executable=True, test=False)
            public_test = public_pick(executable=False, test=True)
            public_executable = public_pick(executable=True, test=False)
            public_alias = public_pick(executable=False, test=False)
        "#};
    let donor = indoc::indoc! {r#"
            from typing import Literal, overload

            # Keep donor and source offsets deliberately different.

            @overload
            def pick(*, executable: bool, test: Literal[True]) -> str: ...
            @overload
            def pick(*, executable: Literal[True], test: Literal[False]) -> int: ...
            @overload
            def pick(*, executable: Literal[False], test: Literal[False]) -> bytes: ...
            @overload
            def pick(*, executable: bool, test: bool) -> str | int | bytes: ...
            def pick(*, executable: bool, test: bool) -> str | int | bytes: ...
        "#};
    let mut db = TestDbBuilder::new()
        .with_file("/src/main.py", source)
        .with_file("/src/contracts.pyi", donor)
        .with_source_provider(ExternalSource::Annotation)
        .build()?;
    let source_file = system_path_to_file(&db, "/src/main.py")?;
    let file = db.program_file(source_file);
    for index in [0, 3, 1, 2, 1, 0] {
        let diagnostics = check_overload_body(&db, function(&db), index)
            .unwrap()
            .into_diagnostics();
        assert!(diagnostics.is_empty(), "domain {index}: {diagnostics:#?}");
        assert!(db.check_file(source_file).is_empty());
        for (name, expected) in [
            ("ordinary", "str | int | bytes"),
            ("public_test", "str"),
            ("public_executable", "int"),
            ("public_alias", "bytes"),
        ] {
            let ty = crate::place::global_symbol(&db, file, name)
                .place
                .expect_type();
            assert_eq!(
                ty.display(&db, &ProgramEnvironment::from_file(file))
                    .to_string(),
                expected
            );
        }
    }
    db.write_file(
        "/src/main.py",
        source.replace("return 'test'", "return b'alias'"),
    )?;
    assert!(db.check_file(source_file).is_empty());
    let diagnostics = check_overload_body(&db, function(&db), 0)
        .unwrap()
        .into_diagnostics();
    assert_eq!(diagnostics.len(), 1, "{diagnostics:#?}");
    assert_eq!(diagnostics[0].id().as_str(), "invalid-return-type");
    assert_eq!(
        diagnostics[0]
            .primary_annotation()
            .unwrap()
            .get_span()
            .file(),
        &ruff_db::diagnostic::UnifiedFile::Ty(source_file)
    );
    assert!(
        check_overload_body(&db, function(&db), 1)
            .unwrap()
            .is_empty()
    );

    // Editing only the donor changes the selected promise and invalidates its body check.
    db.write_file(
        "/src/contracts.pyi",
        donor.replace(
            "test: Literal[True]) -> str",
            "test: Literal[True]) -> bytes",
        ),
    )?;
    assert!(
        check_overload_body(&db, function(&db), 0)
            .unwrap()
            .is_empty()
    );
    db.write_file("/src/contracts.pyi", donor)?;
    assert_eq!(
        check_overload_body(&db, function(&db), 0)
            .unwrap()
            .diagnostics()
            .len(),
        1
    );

    // An unsupported sibling must not conceal a completed inconsistent return check.
    db.write_file(
        "/src/contracts.pyi",
        donor
            .replace(
                "from typing import Literal, overload",
                "from typing import Any, Literal, overload",
            )
            .replace(
                "executable: bool, test: bool) -> str | int | bytes: ...\ndef pick",
                "executable: bool, test: bool) -> Any: ...\ndef pick",
            ),
    )?;
    assert_eq!(
        check_overload_body(&db, function(&db), 3).unwrap_err(),
        BodyDomainError::Unsupported
    );
    assert_eq!(
        check_overload_body(&db, function(&db), 0)
            .unwrap()
            .diagnostics()
            .len(),
        1
    );
    Ok(())
}

#[test]
fn external_overload_body_domains_use_source_defaults() -> anyhow::Result<()> {
    fn function(db: &TestDb) -> crate::types::FunctionType<'_> {
        let file = db.program_file(system_path_to_file(db, "/src/main.py").unwrap());
        crate::place::global_symbol(db, file, "pick")
            .place
            .expect_type()
            .expect_function_literal()
    }

    let source = indoc::indoc! {r#"
        from contracts import pick as public_pick
        shared = 1
        def pick(value=shared):
            return value
        ordinary = pick()
        public_omitted = public_pick()
        public_supplied = public_pick('ok')
    "#};
    let donor = indoc::indoc! {r#"
        from typing import overload
        @overload
        def pick() -> int: ...
        @overload
        def pick(value: str) -> str: ...
        def pick(value: int | str = ...) -> int | str: ...
    "#};
    let mut db = TestDbBuilder::new()
        .with_file("/src/main.py", source)
        .with_file("/src/contracts.pyi", donor)
        .with_source_provider(ExternalSource::Annotation)
        .build()?;
    let source_file = system_path_to_file(&db, "/src/main.py")?;
    // The donor can spell its optional default differently without changing the source value.
    for default in ["...", "'other'", "..."] {
        db.write_file(
            "/src/contracts.pyi",
            donor.replace("= ...)", &format!("= {default})")),
        )?;
        for index in [1, 0, 1] {
            assert!(
                check_overload_body(&db, function(&db), index)
                    .unwrap()
                    .is_empty()
            );
            assert!(db.check_file(source_file).is_empty());
        }
        let file = db.program_file(source_file);
        for (name, expected) in [
            ("ordinary", "int | str"),
            ("public_omitted", "int"),
            ("public_supplied", "str"),
        ] {
            let ty = crate::place::global_symbol(&db, file, name)
                .place
                .expect_type();
            assert_eq!(
                ty.display(&db, &ProgramEnvironment::from_file(file))
                    .to_string(),
                expected
            );
        }
    }
    // Only the omitted domain observes a change to the original shared default.
    db.write_file(
        "/src/main.py",
        source.replace("shared = 1", "shared = 'wrong'"),
    )?;
    assert!(db.check_file(source_file).is_empty());
    assert!(
        check_overload_body(&db, function(&db), 1)
            .unwrap()
            .is_empty()
    );
    let diagnostics = check_overload_body(&db, function(&db), 0)
        .unwrap()
        .into_diagnostics();
    assert_eq!(diagnostics.len(), 1, "{diagnostics:#?}");
    assert_eq!(diagnostics[0].id().as_str(), "invalid-return-type");
    db.write_file("/src/main.py", source)?;
    assert!(
        check_overload_body(&db, function(&db), 0)
            .unwrap()
            .is_empty()
    );
    Ok(())
}

#[test]
fn external_overload_body_domains_require_whole_signature_provenance() -> anyhow::Result<()> {
    for (provider, source) in [
        (
            ExternalSource::MixedFunctionAnnotations,
            "def pick(flag):\n    return flag\n",
        ),
        (
            ExternalSource::Annotation,
            "def pick(flag: bool):\n    return flag\n",
        ),
    ] {
        let db = TestDbBuilder::new()
            .with_file("/src/main.py", source)
            .with_file(
                "/src/contracts.pyi",
                indoc::indoc! {r#"
            from typing import Literal, overload
            @overload
            def pick(flag: Literal[True]) -> Literal[True]: ...
            @overload
            def pick(flag: Literal[False]) -> Literal[False]: ...
            def pick(flag: bool) -> bool: ...
            def other(flag: bool) -> bool: ...
        "#},
            )
            .with_source_provider(provider)
            .build()?;
        let file = db.program_file(system_path_to_file(&db, "/src/main.py")?);
        let function = crate::place::global_symbol(&db, file, "pick")
            .place
            .expect_type()
            .expect_function_literal();
        assert_eq!(
            check_overload_body(&db, function, 0).unwrap_err(),
            BodyDomainError::Unsupported
        );
    }
    Ok(())
}

#[test]
fn external_overload_body_domain_fallthrough_location() -> anyhow::Result<()> {
    let db = TestDbBuilder::new()
        .with_file(
            "/src/main.py",
            "def pick(flag):\n    if flag:\n        return 1\n",
        )
        .with_file(
            "/src/contracts.pyi",
            indoc::indoc! {r#"
            from typing import Literal, overload





            @overload
            def pick(flag: Literal[True]) -> int: ...
            @overload
            def pick(flag: Literal[False]) -> str: ...
            def pick(flag: bool) -> int | str: ...
        "#},
        )
        .with_source_provider(ExternalSource::Annotation)
        .build()?;
    let file = system_path_to_file(&db, "/src/main.py")?;
    let program_file = db.program_file(file);
    let function = crate::place::global_symbol(&db, program_file, "pick")
        .place
        .expect_type()
        .expect_function_literal();
    assert!(check_overload_body(&db, function, 0).unwrap().is_empty());
    let diagnostics = check_overload_body(&db, function, 1)
        .unwrap()
        .into_diagnostics();
    assert_eq!(diagnostics.len(), 1, "{diagnostics:#?}");
    assert_eq!(diagnostics[0].id().as_str(), "invalid-return-type");
    let span = diagnostics[0].primary_annotation().unwrap().get_span();
    assert_eq!(span.file(), &ruff_db::diagnostic::UnifiedFile::Ty(file));
    assert_eq!(
        span.range(),
        Some(TextRange::new(TextSize::new(4), TextSize::new(8)))
    );
    Ok(())
}

#[test]
fn external_generic_function_annotations() -> anyhow::Result<()> {
    let mut db = TestDbBuilder::new().with_python_version(ruff_python_ast::PythonVersion::PY312)
        .with_file(
            "/src/main.py",
            "def identity(value):\n    return value\nfirst = identity(1)\nsecond = identity('ok')\n",
        )
        .with_file("/src/contracts.pyi", "")
        .with_source_provider(ExternalSource::Annotation)
        .build()?;
    let file = system_path_to_file(&db, "/src/main.py")?;
    for (contract, expected) in [
        (
            "def identity[T](value: T) -> T: ...",
            ["Literal[1]", "Literal[\"ok\"]"],
        ),
        (
            "def identity[T](value: T) -> list[T]: ...",
            ["list[int]", "list[str]"],
        ),
        (
            "def identity[T](value: T) -> T: ...",
            ["Literal[1]", "Literal[\"ok\"]"],
        ),
    ] {
        db.write_file("/src/contracts.pyi", contract)?;
        let diagnostics = db.check_file(file);
        assert_eq!(
            diagnostics.len(),
            usize::from(contract.contains("list[T]")),
            "{diagnostics:#?}"
        );
        for diagnostic in diagnostics {
            assert_eq!(diagnostic.id().as_str(), "invalid-return-type");
            assert_eq!(
                diagnostic.primary_annotation().unwrap().get_span().file(),
                &ruff_db::diagnostic::UnifiedFile::Ty(file)
            );
        }
        let program = db.program_file(file);
        let module = parsed_module(&db, program.python_file(&db)).load(&db);
        let model = SemanticModel::new(&db, program);
        let observed: Vec<_> = module
            .suite()
            .iter()
            .filter_map(|statement| {
                let ast::Stmt::Assign(assignment) = statement else {
                    return None;
                };
                Some(
                    assignment
                        .value
                        .inferred_type(&model)
                        .unwrap()
                        .display(&db, &model.program_environment())
                        .to_string(),
                )
            })
            .collect();
        assert_eq!(observed, expected);
    }
    Ok(())
}

#[test]
fn external_generic_function_local_annotations() -> anyhow::Result<()> {
    let db = TestDbBuilder::new()
        .with_python_version(ruff_python_ast::PythonVersion::PY312)
        .with_file(
            "/src/main.py",
            "
T = str

def identity(value):
    copied: T = value
    def inner():
        nested: T = value
        return nested
    def own[T](argument: T) -> T:
        local: T = argument
        return local
    return copied

def wrong(value):
    copied: T = 42
    return value
",
        )
        .with_file(
            "/src/contracts.pyi",
            "
def identity[T](value: T) -> T: ...
def wrong[T](value: T) -> T: ...
",
        )
        .with_source_provider(ExternalSource::Annotation)
        .build()?;
    let file = system_path_to_file(&db, "/src/main.py")?;
    let diagnostics = db.check_file(file);
    assert_eq!(
        diagnostics
            .iter()
            .map(|diagnostic| diagnostic.id().as_str())
            .collect::<Vec<_>>(),
        ["shadowed-type-variable", "invalid-assignment"],
        "{diagnostics:#?}",
    );
    let program = db.program_file(file);
    let module = parsed_module(&db, program.python_file(&db)).load(&db);
    let function = module.suite()[1].as_function_def_stmt().unwrap();
    let annotation = function.body[0]
        .as_ann_assign_stmt()
        .unwrap()
        .annotation
        .as_name_expr()
        .unwrap();
    let model = SemanticModel::new(&db, program);
    let definitions = crate::types::ide_support::definitions_for_name(
        &model,
        "T",
        annotation.into(),
        crate::types::ide_support::ImportAliasResolution::ResolveAliases,
    );
    let donor_file = system_path_to_file(&db, "/src/contracts.pyi")?;
    let donor = db.program_file(donor_file);
    let donor_module = parsed_module(&db, donor.python_file(&db)).load(&db);
    let donor_function = donor_module.suite()[0].as_function_def_stmt().unwrap();
    assert_matches!(
        donor_function.type_params.as_ref().unwrap().type_params.as_slice(),
        [ast::TypeParam::TypeVar(parameter)]
            if definitions.len() == 1 && definitions[0].definition()
                == Some(semantic_index(&db, donor).expect_single_definition(parameter))
    );
    Ok(())
}

#[test]
fn external_generic_annotation_names_keep_source_precedence() -> anyhow::Result<()> {
    for (source, expected) in [
        (
            "def identity(value):\n    T = int\n    copied: T = value\n    return value\n",
            vec!["invalid-assignment"],
        ),
        (
            "def identity(value):\n    copied: T = value\n    T = 42\n    return value\n",
            vec!["unresolved-reference"],
        ),
        (
            "def identity(value):\n    return T\n",
            vec!["unresolved-reference"],
        ),
        (
            "T = int\ndef identity(value):\n    global T\n    copied: T = value\n    return value\n",
            vec!["invalid-assignment"],
        ),
        (
            "def identity(value):\n    T = int\n    def nested():\n        copied: T = value\n    return value\n",
            vec!["invalid-assignment"],
        ),
        (
            "def identity(value):\n    def nested():\n        nonlocal T\n        copied: T = value\n    return value\n",
            vec!["invalid-syntax", "unresolved-reference"],
        ),
        (
            "def identity(value):\n    def middle():\n        nonlocal T\n        def nested():\n            copied: T = value\n    return value\n",
            vec!["invalid-syntax", "unresolved-reference"],
        ),
    ] {
        let db = TestDbBuilder::new()
            .with_python_version(ruff_python_ast::PythonVersion::PY312)
            .with_file("/src/main.py", source)
            .with_file(
                "/src/contracts.pyi",
                "def identity[T](value: T) -> T: ...\n",
            )
            .with_source_provider(ExternalSource::Annotation)
            .build()?;
        let file = system_path_to_file(&db, "/src/main.py")?;
        let diagnostics = db.check_file(file);
        assert_eq!(
            diagnostics
                .iter()
                .map(|diagnostic| diagnostic.id().as_str())
                .collect::<Vec<_>>(),
            expected,
            "{source}\n{diagnostics:#?}",
        );
    }
    Ok(())
}

#[test]
fn external_generic_detached_annotations_follow_donor_edits() -> anyhow::Result<()> {
    let mut db = TestDbBuilder::new()
        .with_python_version(ruff_python_ast::PythonVersion::PY312)
        .with_file(
            "/src/main.py",
            "def identity(value):\n    copied = value  # type: T\n    return copied\n",
        )
        .with_file(
            "/src/contracts.pyi",
            "def identity[T](value: T) -> T: ...\n",
        )
        .with_source_provider(ExternalSource::LocalAnnotations)
        .build()?;
    let file = system_path_to_file(&db, "/src/main.py")?;
    assert!(db.check_file(file).is_empty());
    db.write_file(
        "/src/main.py",
        "def identity(value):\n    copied = 42  # type: T\n    return copied\n",
    )?;
    let diagnostics = db.check_file(file);
    assert_eq!(diagnostics.len(), 1, "{diagnostics:#?}");
    assert_eq!(diagnostics[0].id().as_str(), "invalid-assignment");
    db.write_file(
        "/src/main.py",
        "def identity(value):\n    copied = value  # type: T\n    return copied\n",
    )?;
    assert!(db.check_file(file).is_empty());
    db.write_file(
        "/src/contracts.pyi",
        "def identity[U](value: U) -> U: ...\n",
    )?;
    let diagnostics = db.check_file(file);
    assert_eq!(diagnostics.len(), 1, "{diagnostics:#?}");
    assert_eq!(diagnostics[0].id().as_str(), "unresolved-reference");
    Ok(())
}

#[test]
fn external_generic_function_body_and_defaults() -> anyhow::Result<()> {
    let db = TestDbBuilder::new().with_python_version(ruff_python_ast::PythonVersion::PY312)
        .with_file("/src/main.py", r#"def literal(value): return 1
def fresh(value): return []
def operation(value): return value.missing()
def default(value=1): return value
def native[T](value: T = 1) -> T: return value
first = default()
second = default('ok')
third = native()
fourth = native('ok')
"#)
        .with_file("/src/contracts.pyi", "def literal[T](value: T) -> T: ...\ndef fresh[T](value: T) -> T: ...\ndef operation[T](value: T) -> T: ...\ndef default[T](value: T = ...) -> T: ...\n")
        .with_source_provider(ExternalSource::Annotation)
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
            "invalid-return-type",
            "unresolved-attribute",
            "invalid-return-type",
            "invalid-parameter-default"
        ],
        "{diagnostics:#?}"
    );
    let program = db.program_file(file);
    let module = parsed_module(&db, program.python_file(&db)).load(&db);
    let model = SemanticModel::new(&db, program);
    for statement in module.suite() {
        let ast::Stmt::FunctionDef(function) = statement else {
            continue;
        };
        if function.name.as_str() != "default" && function.name.as_str() != "native" {
            continue;
        }
        let definition = semantic_index(&db, program).expect_single_definition(function);
        let function = crate::types::infer::infer_definition_types(&db, definition)
            .function_type(definition)
            .unwrap();
        assert_eq!(
            function.last_definition_signature(&db).parameters()[0].default_type(&db),
            Some(Type::int_literal(1))
        );
    }
    let observed: Vec<_> = module
        .suite()
        .iter()
        .filter_map(|statement| {
            let ast::Stmt::Assign(assignment) = statement else {
                return None;
            };
            Some(
                assignment
                    .value
                    .inferred_type(&model)
                    .unwrap()
                    .display(&db, &model.program_environment())
                    .to_string(),
            )
        })
        .collect();
    assert_eq!(
        observed,
        ["Unknown", "Literal[\"ok\"]", "Unknown", "Literal[\"ok\"]"]
    );
    Ok(())
}

#[test]
fn external_generic_function_requires_one_complete_donor() -> anyhow::Result<()> {
    for (source, contract, provider) in [
        (
            "def identity(value) -> int: return 1",
            "def identity[T](value: T) -> T: ...",
            ExternalSource::Annotation,
        ),
        (
            "def identity(value: int): return value",
            "def identity[T](value: T) -> T: ...",
            ExternalSource::Annotation,
        ),
        (
            "def identity(value, missing): return value",
            "def identity[T](value: T, missing) -> T: ...",
            ExternalSource::Annotation,
        ),
        (
            "def identity(value): return value",
            "def identity[T](value: T): ...",
            ExternalSource::Annotation,
        ),
        (
            "def identity(value): return value",
            "def identity[T](value: T) -> T: ...\ndef other[U](value: U) -> U: ...",
            ExternalSource::MixedFunctionAnnotations,
        ),
    ] {
        let db = TestDbBuilder::new()
            .with_python_version(ruff_python_ast::PythonVersion::PY312)
            .with_file("/src/main.py", source)
            .with_file("/src/contracts.pyi", contract)
            .with_source_provider(provider)
            .build()?;
        let program = db.program_file(system_path_to_file(&db, "/src/main.py")?);
        let module = parsed_module(&db, program.python_file(&db)).load(&db);
        let function = module.suite()[0].as_function_def_stmt().unwrap();
        let definition = semantic_index(&db, program).expect_single_definition(function);
        let function = crate::types::infer::infer_definition_types(&db, definition)
            .function_type(definition)
            .unwrap();
        assert!(
            function
                .last_definition_signature(&db)
                .generic_context
                .is_none(),
            "{source}"
        );
    }
    Ok(())
}

#[test]
fn external_generic_function_scopes_returned_callable() -> anyhow::Result<()> {
    let db = TestDbBuilder::new()
        .with_python_version(ruff_python_ast::PythonVersion::PY312)
        .with_file(
            "/src/main.py",
            r#"from typing import Callable
def make(): return lambda value: value
def native[T]() -> Callable[[T], T]: return lambda value: value
first = make()(1)
second = make()('ok')
third = native()(1)
fourth = native()('ok')
"#,
        )
        .with_file(
            "/src/contracts.pyi",
            "from typing import Callable\ndef make[T]() -> Callable[[T], T]: ...\n",
        )
        .with_source_provider(ExternalSource::Annotation)
        .build()?;
    let file = system_path_to_file(&db, "/src/main.py")?;
    assert!(db.check_file(file).is_empty(), "{:#?}", db.check_file(file));
    let program = db.program_file(file);
    let module = parsed_module(&db, program.python_file(&db)).load(&db);
    let model = SemanticModel::new(&db, program);
    let observed: Vec<_> = module
        .suite()
        .iter()
        .filter_map(|statement| {
            let ast::Stmt::Assign(assignment) = statement else {
                return None;
            };
            Some(
                assignment
                    .value
                    .inferred_type(&model)
                    .unwrap()
                    .display(&db, &model.program_environment())
                    .to_string(),
            )
        })
        .collect();
    assert_eq!(
        observed,
        [
            "Literal[1]",
            "Literal[\"ok\"]",
            "Literal[1]",
            "Literal[\"ok\"]"
        ]
    );
    Ok(())
}

#[test]
fn external_annotations_check_implementations_in_their_own_scope() -> anyhow::Result<()> {
    let mut db = TestDbBuilder::new()
        .with_file("/src/main.py", "Scalar = int\ndef helper():\n    return 1\ndef compute(value=1):\n    value = 2\n    return 1\ndef implicit(value):\n    print(value)\ndef native(value: int) -> int:\n    return value\n")
        .with_file("/src/contracts.pyi", "")
        .with_source_provider(ExternalSource::Annotation)
        .build()?;
    let file = system_path_to_file(&db, "/src/main.py")?;
    let stub = system_path_to_file(&db, "/src/contracts.pyi")?;
    for (scalar, expected) in [
        ("str", vec!["invalid-return-type", "invalid-return-type"]),
        ("int", vec!["invalid-return-type"]),
        ("str", vec!["invalid-return-type", "invalid-return-type"]),
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
        // Explicit return errors identify the declaring stub.
        assert_eq!(foreign_annotations, usize::from(scalar == "str"));
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
fn external_parameter_contracts_allow_local_rebinding() -> anyhow::Result<()> {
    for (parameter, entry, result, call, expected) in [
        ("value", "int", "str", "", vec![]),
        (
            "value: int",
            "int",
            "str",
            "",
            vec!["invalid-assignment", "invalid-return-type"],
        ),
        ("value", "str", "str", "", vec!["unsupported-operator"]),
        ("value", "int", "int", "", vec!["invalid-return-type"]),
        (
            "value",
            "int",
            "str",
            "convert('bad')",
            vec!["invalid-argument-type"],
        ),
    ] {
        let db = TestDbBuilder::new()
            .with_file(
                "/src/main.py",
                &format!("def convert({parameter}):\n    before = value + 1\n    value = str(before)\n    return value\n{call}\n"),
            )
            .with_file(
                "/src/contracts.pyi",
                &format!("def convert(value: {entry}) -> {result}: ...\n"),
            )
            .with_source_provider(ExternalSource::Annotation)
            .build()?;
        let file = system_path_to_file(&db, "/src/main.py")?;
        let diagnostics = db.check_file(file);
        assert_eq!(
            diagnostics
                .iter()
                .map(|diagnostic| diagnostic.id().as_str())
                .collect::<Vec<_>>(),
            expected,
            "{parameter}, {entry} -> {result}, {call}: {diagnostics:#?}",
        );
    }
    Ok(())
}

#[test]
fn external_annotations_preserve_variadic_and_nominal_types() -> anyhow::Result<()> {
    let db = TestDbBuilder::new()
        .with_file("/src/main.py", "from typing_extensions import assert_type\nclass Item: pass\ndef collect(*items, **labels):\n    first = items[0]\n    name = labels['name']\n    assert_type(first, Item)\n    assert_type(name, str)\n    items = 1\n    labels = 1\n    return first, name\ndef echo(value):\n    return value\ncollect(Item(), bad=1)\necho([Item()])\necho([1])\n")
        .with_file("/src/contracts.pyi", "from main import Item\ndef collect(*items: Item, **labels: str) -> tuple[Item, str]: ...\ndef echo(value: list[Item] | None) -> list[Item] | None: ...\n")
        .with_source_provider(ExternalSource::Annotation)
        .build()?;
    let file = system_path_to_file(&db, "/src/main.py")?;
    let diagnostics = db.check_file(file);
    assert_eq!(
        diagnostics
            .iter()
            .map(|diagnostic| diagnostic.id().as_str())
            .collect::<Vec<_>>(),
        ["invalid-argument-type", "invalid-argument-type"],
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
                    value: None,
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

#[test]
fn semantic_namespaces_preserve_generic_callable_materialization() -> anyhow::Result<()> {
    let db = TestDbBuilder::new()
        .with_file(
            "/src/native.pyi",
            r"from typing import Any, Callable, ParamSpec, TypeVar
P = ParamSpec('P')
R = TypeVar('R')
class Factory:
    def consume(self, callback: Callable[P, R]) -> None: ...
    def gradual(self, callback: Callable[P, Any]) -> None: ...
factory: Factory
",
        )
        .with_file(
            "/src/main.py",
            "from native import factory\nfactory.consume\nfactory.gradual\n",
        )
        .build()?;
    let source = system_path_to_file(&db, "/src/main.py")?;
    let file = db.program_file(source);
    let default = file.program(&db);
    let module = parsed_module(&db, file.python_file(&db)).load(&db);
    let model = SemanticModel::new(&db, file);
    let expressions: Vec<_> = module
        .suite()
        .iter()
        .filter_map(ast::Stmt::as_expr_stmt)
        .collect();
    assert_eq!(expressions.len(), 2);
    let original_env = ProgramEnvironment::from_program(default);
    let gradual_tuple = Type::homogeneous_tuple(&db, &original_env, Type::any());
    for program in [
        default,
        ty_python_core::program::Program::with_semantic_namespace(
            &db,
            default.python_platform(&db),
            default.resolver_environment(&db),
            &Name::new("consumer"),
        ),
    ] {
        let env = ProgramEnvironment::from_program(program);
        // A consumer can inspect a native declaration without rebinding it to its namespace.
        for (expression, fully_static) in expressions.iter().zip([true, false]) {
            let ty = expression.value.inferred_type(&model).unwrap();
            for materialized in [
                ty.top_materialization(&db, &env),
                ty.bottom_materialization(&db, &env),
            ] {
                assert_eq!(
                    ty.is_equivalent_to(&db, &env, materialized),
                    fully_static,
                    "{} vs {}",
                    ty.display(&db, &env),
                    materialized.display(&db, &env),
                );
            }
        }
        // Elements still transform, including normalization of an empty variable segment.
        assert_eq!(
            gradual_tuple.top_materialization(&db, &env),
            Type::homogeneous_tuple(&db, &original_env, Type::object()),
        );
        assert_eq!(
            gradual_tuple.bottom_materialization(&db, &env),
            Type::homogeneous_tuple(&db, &original_env, Type::Never),
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
        let name = match definition.kind(db) {
            DefinitionKind::ProvidedBinding(binding) => binding.binding.name.clone(),
            kind => panic!("expected supplied binding, got {kind:?}"),
        };
        let env = ProgramEnvironment::from_file(definition.program_file(db));
        let value = (name == "refined").then(|| KnownClass::Str.to_instance(db, &env));
        ProvidedBindingValue::Export {
            file: db.program_file(file),
            name,
            value,
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
            value: None,
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
        let call = callback_registration(module.suite(), name)?;
        let variadic = match definition.kind(db) {
            DefinitionKind::Parameter(parameter) => match parameter {
                ty_python_core::definition::ParameterDefinitionNodeKind::VariadicPositionalParameter(_) => Some("positional"),
                ty_python_core::definition::ParameterDefinitionNodeKind::VariadicKeywordParameter(_) => Some("keywords"),
                ty_python_core::definition::ParameterDefinitionNodeKind::Parameter(_) => None,
            },
            _ => None,
        };
        if let Some(name) = variadic {
            let native = system_path_to_file(db, "/src/native.pyi").ok()?;
            return ProvidedBindingValue::Export {
                file: db.program_file(native),
                name: Name::new(name),
                value: None,
            }
            .resolve_type(db);
        }
        let class = callback_context_class(db, file, call)?;
        class.to_instance_approximation(db, &ProgramEnvironment::from_file(file))
    }

    fn function_return_type<'db>(
        &self,
        db: &'db TestDb,
        definition: Definition<'db>,
    ) -> Option<ProvidedReturnType<'db>> {
        let file = definition.program_file(db);
        let path = file.file(db).path(db).as_system_path()?;
        if path.as_str() != "/src/main.py" {
            return None;
        }
        let module = parsed_module(db, file.python_file(db)).load(db);
        let name = definition.name(db)?;
        callback_registration(module.suite(), &name)?;
        let native = system_path_to_file(db, "/src/native.pyi").ok()?;
        let ty = ProvidedBindingValue::Export {
            file: db.program_file(native),
            name: Name::new_static("result"),
            value: None,
        }
        .resolve_type(db)?;
        Some(ProvidedReturnType {
            ty,
            source: FileRange::new(native, TextRange::new(0.into(), 6.into())),
        })
    }
}

fn callback_registration<'a>(statements: &'a [ast::Stmt], name: &str) -> Option<&'a ast::ExprCall> {
    statements.iter().find_map(|statement| {
        let expression = match statement {
            ast::Stmt::Expr(statement) => statement.value.as_ref(),
            ast::Stmt::Assign(statement) => statement.value.as_ref(),
            _ => return None,
        };
        let ast::Expr::Call(call) = expression else {
            return None;
        };
        if call
            .func
            .as_name_expr()
            .is_none_or(|name| name.id != "context")
        {
            return None;
        }
        let [callback] = call.arguments.args.as_ref() else {
            return None;
        };
        let callback_name = match callback {
            ast::Expr::Name(callback) => &callback.id,
            ast::Expr::Attribute(callback) => &callback.attr.id,
            _ => return None,
        };
        (callback_name == name).then_some(call)
    })
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
        value: None,
    }
    .resolve_type(db)?;
    SemanticModel::new(db, file).provided_class_at_call(
        call,
        ProvidedClass {
            name: Name::new_static("CallbackContext"),
            bases: Box::from([base]),
            class_members: Box::default(),
            instance_fields: ProvidedInstanceFields::default().into(),
        },
    )
}

#[test]
fn supplied_parameter_types_are_initial_bindings_only() -> anyhow::Result<()> {
    let db = TestDbBuilder::new()
        .with_file("/src/context.cfg", "Context")
        .with_file(
            "/src/native.pyi",
            "from typing import Callable\nclass Context:\n    value: int | None\ndef context[**P, R](callback: Callable[P, R]) -> type: ...\n",
        )
        .with_file(
            "/src/main.py",
            "from native import context
from typing_extensions import Literal, assert_type
def callback(ctx) -> None:
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
    let model = SemanticModel::new(&db, db.program_file(file));
    let view = signature
        .clone()
        .with_inferred_parameter_context(|definition| Some(model.definition_type(definition)));
    assert_eq!(view.return_type(), signature.return_type());
    assert!(!view.parameters()[0].annotated_type().is_unknown());
    let view = Type::single_callable(&db, view);
    let module = parsed_module(&db, model.program_file().python_file(&db)).load(&db);
    let call = callback_registration(module.suite(), "callback").unwrap();
    let inputs =
        crate::types::ide_support::call_input_types_with_context(&model, call, |expression| {
            matches!(expression, ast::Expr::Name(name) if name.id == "callback").then_some(view)
        })
        .unwrap();
    let [argument] = inputs.as_slice() else {
        panic!("expected one contextual argument: {inputs:?}");
    };
    let [input] = argument.as_slice() else {
        panic!("expected one contextual contract: {argument:?}");
    };
    let env = model.program_environment();
    assert!(
        input
            .argument_type
            .is_subtype_of(&db, &env, input.parameter_type)
    );
    assert_eq!(callback.last_definition_signature(&db), signature);
    Ok(())
}

#[test]
fn supplied_parameter_types_preserve_annotation_default_and_variadic_types() -> anyhow::Result<()> {
    let db = TestDbBuilder::new()
        .with_file("/src/context.cfg", "Context")
        .with_file(
            "/src/native.pyi",
            "from typing import Callable\nclass Context:\n    value: int\ndef context(callback: Callable[..., object]) -> type: ...\n",
        )
        .with_file(
            "/src/main.py",
            "from native import context
from typing_extensions import Literal, assert_type
def annotated(ctx: int):
    assert_type(ctx, int)
def supplied(ctx): # (str) -> None
    assert_type(ctx, str)
def defaulted(ctx=1):
    if isinstance(ctx, int):
        integer: int = ctx
    else:
        assert_type(ctx.value, int)
    ctx = 'reassigned'
    assert_type(ctx, Literal['reassigned'])
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
    let model = SemanticModel::new(&db, db.program_file(file));
    for name in ["annotated", "supplied", "defaulted", "variadic"] {
        let function = crate::place::global_symbol(&db, model.program_file(), name)
            .place
            .expect_type()
            .expect_function_literal();
        let signature = function.last_definition_signature(&db);
        let view = signature
            .clone()
            .with_inferred_parameter_context(|definition| Some(model.definition_type(definition)));
        if name == "defaulted" {
            let [original] = signature.parameters().as_slice() else {
                panic!("expected one defaulted parameter");
            };
            let [contextual] = view.parameters().as_slice() else {
                panic!("expected one contextual parameter");
            };
            assert!(!contextual.annotated_type().is_unknown());
            assert_eq!(contextual.default_type(&db), original.default_type(&db));
            assert_eq!(view.return_type(), signature.return_type());
        } else {
            assert_eq!(&view, signature, "{name}");
        }
    }
    Ok(())
}

#[test]
fn supplied_variadic_parameters_use_complete_entry_types() -> anyhow::Result<()> {
    let db = TestDbBuilder::new()
        .with_file(
            "/src/native.pyi",
            "from typing import Callable, TypedDict
from typing_extensions import NotRequired
class Fields(TypedDict):
    value: str
    optional: NotRequired[int]
positional: tuple[int, str]
keywords: Fields
def context(callback: Callable[..., object]) -> type: ...
",
        )
        .with_file(
            "/src/main.py",
            "from native import context
from typing_extensions import Literal, assert_type
def callback(*args, **kwargs):
    assert_type(args, tuple[int, str])
    assert_type(kwargs['value'], str)
    assert_type(kwargs.get('optional'), int | None)
    kwargs['value'] + 1
    args = 1
    assert_type(args, Literal[1])
    kwargs = None
    assert_type(kwargs, None)
def annotated(*args: str, **kwargs: int):
    assert_type(args, tuple[str, ...])
    assert_type(kwargs, dict[str, int])
context(callback)
context(annotated)
",
        )
        .with_source_provider(CommentedSource)
        .build()?;
    let file = system_path_to_file(&db, "/src/main.py")?;
    let diagnostics = db.check_file(file);
    assert_eq!(
        diagnostics
            .iter()
            .map(|diagnostic| diagnostic.id().as_str())
            .collect::<Vec<_>>(),
        ["unsupported-operator"],
        "{diagnostics:#?}"
    );
    Ok(())
}

#[test]
fn supplied_return_types_check_bodies_without_declaring_signatures() -> anyhow::Result<()> {
    let db = TestDbBuilder::new()
        .with_file("/src/context.cfg", "Context")
        .with_file(
            "/src/native.pyi",
            "result: Result
from typing import Callable, TypedDict
class Context(int): ...
class Result(TypedDict):
    value: int
def context(callback: Callable[..., object]) -> type: ...
",
        )
        .with_file(
            "/src/main.py",
            "from native import context
from typing import overload
def good(ctx):
    ctx = 'reassigned'
    return {'value': 1}
def missing(ctx):
    return {}
def wrong_field(ctx):
    return {'value': 'bad'}
def wrong_return(ctx):
    return 42
def bad_default(ctx=None):
    return {'value': ctx}
def explicit(ctx) -> str:
    return 'source'
def commented(ctx): # (int) -> str
    return 'source'
def unreachable(ctx):
    if False:
        return 42
    return {'value': 1}
def suppressed(ctx):
    return 42 # ty: ignore[invalid-return-type]
def fallthrough(ctx):
    if ctx:
        return {'value': 1}
@overload
def overloaded(ctx: int) -> object: ...
@overload
def overloaded(ctx: str) -> object: ...
def overloaded(ctx):
    return {}
context(good)
context(missing)
context(wrong_field)
context(wrong_return)
context(bad_default)
context(explicit)
context(commented)
context(unreachable)
context(suppressed)
context(fallthrough)
context(overloaded)
actual_return: int = wrong_return(None)
",
        )
        .with_source_provider(CommentedSource)
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
            "invalid-argument-type",
            "invalid-return-type",
            "invalid-return-type",
            "invalid-argument-type",
            "invalid-return-type",
            "invalid-return-type",
            "missing-typed-dict-key"
        ],
        "{diagnostics:#?}",
    );
    let native = system_path_to_file(&db, "/src/native.pyi")?;
    let expected_span =
        ruff_db::diagnostic::Span::from(native).with_range(TextRange::new(0.into(), 6.into()));
    assert!(
        diagnostics.iter().any(|diagnostic| {
            diagnostic.id().as_str() == "invalid-return-type"
                && diagnostic
                    .annotations()
                    .iter()
                    .any(|annotation| annotation.get_span() == &expected_span)
        }),
        "{diagnostics:#?}"
    );
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
                        instance_fields: ProvidedInstanceFields::default().into(),
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
fn supplied_class_identity_can_use_empty_declarations() -> anyhow::Result<()> {
    let mut db = TestDbBuilder::new()
        .with_file(
            "/src/main.py",
            "def outer():\n    class Empty: pass\n    def factory[T](value: T) -> T: return value\n    other = 1\n",
        )
        .build()?;
    let file = system_path_to_file(&db, "/src/main.py")?;
    db.clear_salsa_events();
    {
        let file = db.program_file(file);
        let module = parsed_module(&db, file.python_file(&db)).load(&db);
        let [ast::Stmt::FunctionDef(outer)] = module.suite().as_slice() else {
            panic!("expected the enclosing function");
        };
        let [
            ast::Stmt::ClassDef(class),
            ast::Stmt::FunctionDef(function),
            ast::Stmt::Assign(other),
        ] = outer.body.as_slice()
        else {
            panic!("expected the nested declarations");
        };
        let index = semantic_index(&db, file);
        let class_definition = index.expect_single_definition(class);
        let function_definition = index.expect_single_definition(function);
        let supplied = |definition| {
            ProvidedClass {
                name: Name::new_static("Key"),
                bases: Box::default(),
                class_members: Box::default(),
                instance_fields: ProvidedInstanceFields::default().into(),
            }
            .into_type_at_definition(&db, definition)
        };
        let first = supplied(class_definition);
        let second = supplied(function_definition);
        assert!(first.is_some());
        assert!(second.is_some());
        assert_eq!(first, supplied(class_definition));
        assert_eq!(second, supplied(function_definition));
        assert_ne!(first, second);
        let [target] = other.targets.as_slice() else {
            panic!("expected one assignment target");
        };
        let ast::Expr::Name(target) = target else {
            panic!("expected a name assignment");
        };
        assert_eq!(supplied(index.expect_single_definition(target)), None);
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
fn supplied_export_refinements_keep_source_resolution() -> anyhow::Result<()> {
    let mut db = TestDbBuilder::new()
        .with_file("/src/main.py", "include(\"refined\")\nrefined\n")
        .with_file("/src/native.pyi", "refined: int\n")
        .with_source_provider(CommentedSource)
        .build()?;
    let file = system_path_to_file(&db, "/src/main.py")?;
    let native = system_path_to_file(&db, "/src/native.pyi")?;
    for present in [true, false, true] {
        db.write_file(
            "/src/native.pyi",
            if present { "refined: int\n" } else { "" },
        )?;
        let file = db.program_file(file);
        let native = db.program_file(native);
        let module = parsed_module(&db, file.python_file(&db)).load(&db);
        let [_, ast::Stmt::Expr(statement)] = module.suite().as_slice() else {
            panic!("expected the supplied binding and its use");
        };
        let model = SemanticModel::new(&db, file);
        let definitions = crate::definitions_for_name(
            &model,
            "refined",
            statement.value.as_ref().into(),
            crate::ImportAliasResolution::ResolveAliases,
        );
        let env = model.program_environment();
        if present {
            assert_eq!(
                statement.value.inferred_type(&model),
                Some(KnownClass::Str.to_instance(&db, &env)),
            );
            let native_module = parsed_module(&db, native.python_file(&db)).load(&db);
            let [ast::Stmt::AnnAssign(declaration)] = native_module.suite().as_slice() else {
                panic!("expected the exported declaration");
            };
            let expected = semantic_index(&db, native).expect_single_definition(declaration);
            assert_eq!(
                definitions,
                [crate::ResolvedDefinition::Definition(expected)]
            );
            let diagnostics = crate::check_file_unwrap(&db, file);
            assert!(diagnostics.is_empty(), "{diagnostics:#?}");
        } else {
            assert_eq!(
                definitions,
                crate::definitions_for_name(
                    &model,
                    "refined",
                    statement.value.as_ref().into(),
                    crate::ImportAliasResolution::PreserveAliases,
                ),
            );
            assert_eq!(
                ProvidedBindingValue::Export {
                    file: native,
                    name: Name::new_static("refined"),
                    value: Some(KnownClass::Str.to_instance(&db, &env)),
                }
                .resolve_type(&db),
                None,
            );
        }
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
fn supplied_builtin_calls_propagate_never_arguments() -> anyhow::Result<()> {
    struct Calls<'a, 'db> {
        model: &'a SemanticModel<'db>,
        types: Vec<Type<'db>>,
    }
    impl<'ast> Visitor<'ast> for Calls<'_, '_> {
        fn visit_expr(&mut self, expression: &'ast ast::Expr) {
            if let ast::Expr::Call(call) = expression
                && let ast::Expr::Name(name) = call.func.as_ref()
                && matches!(
                    name.id.as_str(),
                    "Scalar" | "sentinel" | "identity" | "noargs"
                )
            {
                self.types
                    .push(expression.inferred_type(self.model).unwrap());
            }
            walk_expr(self, expression);
        }
    }

    let db = TestDbBuilder::new()
        .with_file(
            "/src/native.pyi",
            "from typing import overload\nScalar = int\n@overload\ndef sentinel(value: int) -> str: ...\n@overload\ndef sentinel(value: str) -> bytes: ...\ndef identity[T](value: T) -> T: ...\ndef noargs() -> int: ...\n",
        )
        .with_file(
            "/src/main.py",
            r#"
from typing import Any
from typing_extensions import Never, TypedDict
from native import identity, noargs, sentinel

class Record:
    def method(self) -> None: ...

def absent(value: Record):
    if not hasattr(value, "method"):
        Scalar(value)
        sentinel(value)

def bottom(value: Never):
    Scalar(value)
    Scalar(*value)
    Scalar(**value)
    Scalar(value, 1)

def gradual(value: Any | int):
    Scalar(value)
    identity(value)

def dynamic(value: Any):
    identity(value)

def reachable(value: int):
    Scalar(value)

class Empty(TypedDict, closed=True):
    pass

def empty(positional: tuple[()], keywords: Empty):
    noargs(*positional)
    noargs(**keywords)

Scalar(None)
"#,
        )
        .with_source_provider(CommentedSource)
        .build()?;
    let file = system_path_to_file(&db, "/src/main.py")?;
    let diagnostics = db.check_file(file);
    assert_eq!(diagnostics.len(), 2, "{diagnostics:#?}");
    assert!(
        diagnostics
            .iter()
            .all(|diagnostic| diagnostic.id().as_str() == "no-matching-overload")
    );
    let file = db.program_file(file);
    let module = parsed_module(&db, file.python_file(&db)).load(&db);
    let model = SemanticModel::new(&db, file);
    let mut calls = Calls {
        model: &model,
        types: Vec::new(),
    };
    calls.visit_body(module.suite());
    let env = model.program_environment();
    let string = KnownClass::Str.to_instance(&db, &env);
    let integer = KnownClass::Int.to_instance(&db, &env);
    assert_matches!(
        calls.types.as_slice(),
        [Type::Never, Type::Never, Type::Never, Type::Never, Type::Never, Type::Never,
         gradual_overload, gradual, dynamic, reachable, empty_positional, empty_keywords, invalid]
            if *gradual_overload == string
                && !gradual.is_never()
                && !gradual.is_fully_static(&db, &env)
                && *dynamic == Type::any()
                && *reachable == string
                && *empty_positional == integer
                && *empty_keywords == integer
                && invalid.is_unknown()
    );
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
        .with_source_provider(ExternalSource::Annotation)
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
        .with_source_provider(ExternalSource::Annotation)
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
        .with_source_provider(ExternalSource::Annotation)
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
        .with_source_provider(ExternalSource::Annotation)
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
        .with_source_provider(ExternalSource::Annotation)
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

#[test]
fn external_annotations_preserve_dictionary_key_checks() -> anyhow::Result<()> {
    let schema =
        "from typing import TypedDict\nclass Row(TypedDict):\n    value: int\nresult: Row\n";
    for source in [
        "from contracts import Row\nresult: Row = {'value': 1, 'hidden': []}\n",
        "result = {'value': 1, 'hidden': []}\n",
        "from contracts import Row\ndef accept(value: Row) -> Row: return value\nresult = accept({'value': 1, 'hidden': []})\n",
    ] {
        let db = TestDbBuilder::new()
            .with_file("/src/main.py", source)
            .with_file("/src/contracts.pyi", schema)
            .with_source_provider(ExternalSource::Annotation)
            .build()?;
        let file = system_path_to_file(&db, "/src/main.py")?;
        let diagnostics = db.check_file(file);
        assert!(
            diagnostics
                .iter()
                .any(|diagnostic| diagnostic.id().as_str() == "invalid-key"),
            "{source}\n{diagnostics:#?}"
        );
    }
    Ok(())
}
