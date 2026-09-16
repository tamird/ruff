use ruff_db::files::{File, system_path_to_file};
use ruff_db::system::{DbWithTestSystem as _, DbWithWritableSystem as _};
use ruff_text_size::Ranged;

use crate::bazel::BazelRepository;
use crate::source::BazelSource;
use crate::testing::test_db;
use ty_python_core::starlark::StarlarkType;

use super::{
    BazelStubAdmission, BazelStubDeclarations, BazelStubError, BazelStubFailure, admit_bazel_stub,
};

fn admitted(admission: &BazelStubAdmission) -> anyhow::Result<&BazelStubDeclarations> {
    match admission {
        BazelStubAdmission::Admitted(declarations) => Ok(declarations),
        other => anyhow::bail!("expected stub declarations, found {other:?}"),
    }
}

fn opaque(admission: &BazelStubAdmission) -> anyhow::Result<&BazelStubFailure> {
    match admission {
        BazelStubAdmission::Opaque(failure) => Ok(failure),
        other => anyhow::bail!("expected an opaque stub, found {other:?}"),
    }
}

#[test]
fn parses_exact_sibling_primitive_declarations_without_claiming_runtime_types() -> anyhow::Result<()>
{
    let (db, root) = test_db(&[
        ("MODULE.bazel", ""),
        ("pkg/BUILD", ""),
        (
            "pkg/defs.bzl",
            "def check(value, text=\"s\"):\n    return True\ndef identity(value):\n    return value\n",
        ),
        (
            "pkg/defs.bzl.pyi",
            "\"Ty declarations\"\ndef check(value: int, text: str = ...) -> bool: ...\ndef identity(value: None) -> None: pass\n",
        ),
    ])?;
    let source_file = system_path_to_file(&db, root.join("pkg/defs.bzl"))?;
    let stub_file = system_path_to_file(&db, root.join("pkg/defs.bzl.pyi"))?;
    let source = BazelSource::new(&db, BazelRepository::new(&db, root), source_file);
    let declarations = admitted(admit_bazel_stub(&db, source))?;
    assert_eq!(declarations.file(), stub_file);
    let [check, identity] = declarations.annotations() else {
        anyhow::bail!("expected two matched functions: {declarations:?}");
    };
    assert_eq!(
        check.returns.as_ref().map(|value| value.ty),
        Some(StarlarkType::Bool)
    );
    let [value, text] = check.parameters.as_ref() else {
        anyhow::bail!("expected two parameters");
    };
    assert_eq!(value.annotation.ty, StarlarkType::Int);
    assert_eq!(text.annotation.ty, StarlarkType::Str);
    assert_eq!(value.annotation.origin.file(), stub_file);
    assert_ne!(value.parameter, value.annotation.origin.range());
    assert_eq!(
        identity.returns.as_ref().map(|value| value.ty),
        Some(StarlarkType::None)
    );
    Ok(())
}

#[test]
fn absent_sibling_revalidates_on_creation_edit_and_removal() -> anyhow::Result<()> {
    let (mut db, root) = test_db(&[
        ("WORKSPACE.bazel", ""),
        ("pkg/BUILD", ""),
        ("pkg/defs.bzl", "def identity(value):\n    return value\n"),
        (
            "pkg/other.bzl.pyi",
            "def identity(value: str) -> str: ...\n",
        ),
    ])?;
    let source_file = system_path_to_file(&db, root.join("pkg/defs.bzl"))?;
    assert!(matches!(
        admit_bazel_stub(
            &db,
            BazelSource::new(&db, BazelRepository::new(&db, root.clone()), source_file)
        ),
        BazelStubAdmission::Absent
    ));

    let sibling = root.join("pkg/defs.bzl.pyi");
    db.write_file(&sibling, "def identity(value: int) -> int: ...\n")?;
    File::sync_path(&mut db, &sibling);
    assert_eq!(
        admitted(admit_bazel_stub(
            &db,
            BazelSource::new(&db, BazelRepository::new(&db, root.clone()), source_file)
        ))?
        .annotations()[0]
            .returns
            .as_ref()
            .map(|value| value.ty),
        Some(StarlarkType::Int)
    );

    db.write_file(&sibling, "from typing import Any\n")?;
    File::sync_path(&mut db, &sibling);
    assert!(matches!(
        opaque(admit_bazel_stub(
            &db,
            BazelSource::new(&db, BazelRepository::new(&db, root.clone()), source_file)
        ))?
        .reason(),
        BazelStubError::Unsupported("non-function stub declarations")
    ));

    db.memory_file_system().remove_file(&sibling)?;
    File::sync_path(&mut db, &sibling);
    assert!(matches!(
        admit_bazel_stub(
            &db,
            BazelSource::new(&db, BazelRepository::new(&db, root), source_file)
        ),
        BazelStubAdmission::Absent
    ));
    Ok(())
}

#[test]
fn malformed_stub_cannot_expose_earlier_valid_declarations() -> anyhow::Result<()> {
    let malformed = "def good(value: int) -> int: ...\ndef broken(value: int -> int: ...\n";
    let (db, root) = test_db(&[
        ("MODULE.bazel", ""),
        ("pkg/BUILD", ""),
        ("pkg/defs.bzl", "def good(value):\n    return value\n"),
        ("pkg/defs.bzl.pyi", malformed),
    ])?;
    let source_file = system_path_to_file(&db, root.join("pkg/defs.bzl"))?;
    let stub_file = system_path_to_file(&db, root.join("pkg/defs.bzl.pyi"))?;
    let source = BazelSource::new(&db, BazelRepository::new(&db, root), source_file);
    let failure = opaque(admit_bazel_stub(&db, source))?;
    assert_eq!(failure.file(), Some(stub_file));
    assert!(matches!(failure.reason(), BazelStubError::Parser(_)));
    let start = failure
        .range()
        .ok_or(anyhow::anyhow!("parser span"))?
        .start();
    assert!(start.to_usize() >= malformed.find("broken").ok_or(anyhow::anyhow!("broken"))?);
    Ok(())
}

#[test]
fn present_unsupported_stub_declarations_are_wholly_opaque() -> anyhow::Result<()> {
    for (stub, reason) in [
        (
            "def good(value: int) -> int: ...\nfrom typing import Any\n",
            "non-function stub declarations",
        ),
        (
            "def good(value: int) -> int: ...\ndef bad(value: list[int]) -> int: ...\n",
            "non-primitive parameter annotations",
        ),
        (
            "def good(value: int) -> int: ...\ndef bad(value: int = 1) -> int: ...\n",
            "defaults other than the ... stub marker",
        ),
        (
            "def good(value: int) -> int: ...\ndef bad(value: int) -> int:\n    return value\n",
            "function bodies other than pass or ...",
        ),
        (
            "def good(value: int) -> int: ...\ndef bad(value) -> int: ...\n",
            "parameters without primitive annotations",
        ),
    ] {
        let (db, root) = test_db(&[
            ("MODULE.bazel", ""),
            ("pkg/BUILD", ""),
            ("pkg/defs.bzl", "def good(value):\n    return value\n"),
            ("pkg/defs.bzl.pyi", stub),
        ])?;
        let source_file = system_path_to_file(&db, root.join("pkg/defs.bzl"))?;
        let stub_file = system_path_to_file(&db, root.join("pkg/defs.bzl.pyi"))?;
        let source = BazelSource::new(&db, BazelRepository::new(&db, root), source_file);
        let failure = opaque(admit_bazel_stub(&db, source))?;
        assert_eq!(failure.file(), Some(stub_file), "{stub}");
        assert!(
            matches!(failure.reason(), BazelStubError::Unsupported(actual) if *actual == reason),
            "{stub}: {:?}",
            failure.reason()
        );
        assert!(failure.range().is_some());
    }
    Ok(())
}

#[test]
fn duplicate_declarations_and_opaque_source_fail_closed() -> anyhow::Result<()> {
    let (db, root) = test_db(&[
        ("MODULE.bazel", ""),
        ("pkg/BUILD", ""),
        ("pkg/defs.bzl", "GOOD = 1\nclass Broken: pass\n"),
        (
            "pkg/defs.bzl.pyi",
            "def good(value: int) -> int: ...\ndef good(value: str) -> str: ...\n",
        ),
    ])?;
    let source_file = system_path_to_file(&db, root.join("pkg/defs.bzl"))?;
    let source = BazelSource::new(&db, BazelRepository::new(&db, root.clone()), source_file);
    let failure = opaque(admit_bazel_stub(&db, source))?;
    assert_eq!(failure.file(), Some(source_file));
    assert_eq!(failure.path(), Some(root.join("pkg/defs.bzl").as_path()));
    assert!(matches!(failure.reason(), BazelStubError::Source(_)));
    assert!(failure.range().is_some());

    let (db, root) = test_db(&[
        ("MODULE.bazel", ""),
        ("pkg/BUILD", ""),
        ("pkg/defs.bzl", "def good(value):\n    return value\n"),
        (
            "pkg/defs.bzl.pyi",
            "def good(value: int) -> int: ...\ndef good(value: str) -> str: ...\n",
        ),
    ])?;
    let source_file = system_path_to_file(&db, root.join("pkg/defs.bzl"))?;
    let stub_file = system_path_to_file(&db, root.join("pkg/defs.bzl.pyi"))?;
    let source = BazelSource::new(&db, BazelRepository::new(&db, root), source_file);
    let failure = opaque(admit_bazel_stub(&db, source))?;
    assert_eq!(failure.file(), Some(stub_file));
    assert!(matches!(
        failure.reason(),
        BazelStubError::DuplicateFunction(name) if name == "good"
    ));
    Ok(())
}

#[test]
fn a_directory_at_the_sibling_path_is_not_an_absent_stub() -> anyhow::Result<()> {
    let (mut db, root) = test_db(&[
        ("MODULE.bazel", ""),
        ("pkg/BUILD", ""),
        ("pkg/defs.bzl", "GOOD = 1\n"),
    ])?;
    let sibling = root.join("pkg/defs.bzl.pyi");
    db.memory_file_system().create_directory_all(&sibling)?;
    File::sync_path(&mut db, &sibling);
    let source_file = system_path_to_file(&db, root.join("pkg/defs.bzl"))?;
    let source = BazelSource::new(&db, BazelRepository::new(&db, root), source_file);
    let failure = opaque(admit_bazel_stub(&db, source))?;
    assert!(matches!(failure.reason(), BazelStubError::IsDirectory));
    assert_eq!(failure.file(), None);
    assert_eq!(failure.path(), Some(sibling.as_path()));
    Ok(())
}

#[test]
fn companion_must_match_a_public_source_signature() -> anyhow::Result<()> {
    for (runtime, stub, expected) in [
        (
            "def f(x):\n    return x\n",
            "def missing(x: int) -> int: ...\n",
            "does not name a public",
        ),
        (
            "def _f(x):\n    return x\n",
            "def _f(x: int) -> int: ...\n",
            "does not name a public",
        ),
        (
            "def f(x):\n    return x\n",
            "def f(y: int) -> int: ...\n",
            "does not match source parameter",
        ),
        (
            "def f(*x):\n    return x\n",
            "def f(x: int) -> int: ...\n",
            "different parameter kinds or count",
        ),
        (
            "def f(x=1):\n    return x\n",
            "def f(x: int) -> int: ...\n",
            "default's presence",
        ),
    ] {
        let (db, root) = test_db(&[
            ("MODULE.bazel", ""),
            ("pkg/BUILD", ""),
            ("pkg/defs.bzl", runtime),
            ("pkg/defs.bzl.pyi", stub),
        ])?;
        let file = system_path_to_file(&db, root.join("pkg/defs.bzl"))?;
        let source = BazelSource::new(&db, BazelRepository::new(&db, root), file);
        let failure = opaque(admit_bazel_stub(&db, source))?;
        assert!(
            failure.reason().to_string().contains(expected),
            "{runtime}: {failure:?}"
        );
    }
    Ok(())
}
