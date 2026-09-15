use ruff_db::files::{File, system_path_to_file};
use ruff_db::system::{DbWithTestSystem as _, DbWithWritableSystem as _};

use crate::bazel::BazelRepository;
use crate::checker::{
    BazelCheckedSource, BazelExport, BazelExportKind, BazelScalar, summarize_bazel_source,
};
use crate::source::BazelSource;
use crate::testing::test_db;

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
    assert_eq!(declarations.functions().len(), 2);
    let check = declarations
        .function("check")
        .ok_or(anyhow::anyhow!("check"))?;
    assert!(!check.range().is_empty());
    assert_eq!(check.result(), BazelScalar::Bool);
    assert_ne!(check.range(), check.result_range());
    assert_eq!(check.parameters().len(), 2);
    assert_eq!(check.parameters()[0].name(), "value");
    assert_eq!(check.parameters()[0].scalar(), BazelScalar::Int);
    assert!(!check.parameters()[0].has_default());
    assert_eq!(check.parameters()[1].name(), "text");
    assert_eq!(check.parameters()[1].scalar(), BazelScalar::Str);
    assert!(check.parameters()[1].has_default());
    assert!(!check.parameters()[1].name_range().is_empty());
    assert!(!check.parameters()[1].annotation_range().is_empty());
    assert_ne!(
        check.parameters()[1].name_range(),
        check.parameters()[1].annotation_range()
    );
    let identity = declarations
        .function("identity")
        .ok_or(anyhow::anyhow!("identity"))?;
    assert_eq!(identity.result(), BazelScalar::None);
    assert_eq!(identity.parameters()[0].scalar(), BazelScalar::None);

    let BazelCheckedSource::Checked(summary) = summarize_bazel_source(&db, source) else {
        anyhow::bail!("the runtime must remain checked independently of declarations")
    };
    let Some(BazelExportKind::Function(function)) =
        summary.export("identity").map(BazelExport::kind)
    else {
        anyhow::bail!("the runtime identity export is missing")
    };
    assert_eq!(function.result(), BazelScalar::Unknown);
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
        .function("identity")
        .ok_or(anyhow::anyhow!("identity"))?
        .result(),
        BazelScalar::Int
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
        (
            "pkg/defs.bzl",
            "GOOD = 1\ndef broken():\n    return not_defined\n",
        ),
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
