use ruff_db::diagnostic::DiagnosticId;
use ruff_db::files::system_path_to_file;
use ruff_db::system::DbWithWritableSystem as _;

use crate::bazel::BazelRepository;
use crate::source::{BazelSource, BazelSourceAdmission, admit_bazel_source};
use crate::testing::test_db;

use super::{BazelPreflight, BazelPreflightError, BazelPreflightFailure, preflight_bazel_source};

fn ready(preflight: &BazelPreflight) -> anyhow::Result<()> {
    match preflight {
        BazelPreflight::Ready => Ok(()),
        BazelPreflight::Opaque(failure) => {
            anyhow::bail!("expected complete stable Bazel preflight, found {failure:?}")
        }
    }
}

fn opaque(preflight: &BazelPreflight) -> anyhow::Result<&BazelPreflightFailure> {
    match preflight {
        BazelPreflight::Opaque(failure) => Ok(failure),
        BazelPreflight::Ready => anyhow::bail!("expected whole-file opaque preflight"),
    }
}

#[test]
fn stable_unannotated_source_checks_scalars_defaults_and_locals() -> anyhow::Result<()> {
    let (db, root) = test_db(&[
        ("MODULE.bazel", ""),
        ("pkg/BUILD", ""),
        (
            "pkg/defs.bzl",
            "\"Module docs\"\nFIRST = 1\nNEXT = FIRST\nMINUS = -1\ndef later(value=NEXT):\n    copy = value\n    return copy\n",
        ),
    ])?;
    let file = system_path_to_file(&db, root.join("pkg/defs.bzl"))?;
    let source = BazelSource::new(&db, BazelRepository::new(&db, root), file);
    ready(preflight_bazel_source(&db, source))
}

#[test]
fn forward_function_globals_are_valid_after_module_initialization() -> anyhow::Result<()> {
    let (db, root) = test_db(&[
        ("WORKSPACE.bazel", ""),
        ("pkg/BUILD", ""),
        (
            "pkg/defs.bzl",
            "def first(value):\n    return second(value)\n\ndef second(value):\n    return LATER\n\nLATER = 2\n",
        ),
    ])?;
    let file = system_path_to_file(&db, root.join("pkg/defs.bzl"))?;
    let source = BazelSource::new(&db, BazelRepository::new(&db, root), file);
    ready(preflight_bazel_source(&db, source))
}

#[test]
fn undefined_name_in_unused_function_taints_later_scalar_export() -> anyhow::Result<()> {
    let code = "def broken(value):\n    return missing\n\nGOOD = 1\n";
    let (db, root) = test_db(&[
        ("REPO.bazel", ""),
        ("pkg/BUILD", ""),
        ("pkg/defs.bzl", code),
    ])?;
    let file = system_path_to_file(&db, root.join("pkg/defs.bzl"))?;
    let source = BazelSource::new(&db, BazelRepository::new(&db, root), file);
    let failure = opaque(preflight_bazel_source(&db, source))?;
    assert!(matches!(
        failure.reason(),
        BazelPreflightError::UnknownName(name) if name == "missing"
    ));
    assert_eq!(failure.file(), file);
    assert_eq!(
        failure.range().map(|range| range.start().to_usize()),
        code.find("missing")
    );
    assert!(failure.admission_diagnostic().is_none());
    Ok(())
}

#[test]
fn local_names_shadow_globals_even_before_assignment() -> anyhow::Result<()> {
    for (code, name) in [
        (
            "GLOBAL = 1\ndef broken():\n    return GLOBAL\n    GLOBAL = 2\nGOOD = 1\n",
            "GLOBAL",
        ),
        (
            "def broken():\n    return later\n    later = 1\nGOOD = 1\n",
            "later",
        ),
    ] {
        let (db, root) = test_db(&[
            ("MODULE.bazel", ""),
            ("pkg/BUILD", ""),
            ("pkg/defs.bzl", code),
        ])?;
        let file = system_path_to_file(&db, root.join("pkg/defs.bzl"))?;
        let source = BazelSource::new(&db, BazelRepository::new(&db, root), file);
        let failure = opaque(preflight_bazel_source(&db, source))?;
        assert!(
            matches!(failure.reason(), BazelPreflightError::UninitializedLocal(found) if found == name),
            "{code}: {:?}",
            failure.reason()
        );
    }
    Ok(())
}

#[test]
fn module_bindings_and_defaults_evaluate_in_source_order() -> anyhow::Result<()> {
    for (code, name) in [
        ("FIRST = LATER\nLATER = 1\n", "LATER"),
        (
            "def identity(value=LATER):\n    return value\nLATER = 1\n",
            "LATER",
        ),
        (
            "def identity(value=identity):\n    return value\n",
            "identity",
        ),
    ] {
        let (db, root) = test_db(&[
            ("WORKSPACE.bazel", ""),
            ("pkg/BUILD", ""),
            ("pkg/defs.bzl", code),
        ])?;
        let file = system_path_to_file(&db, root.join("pkg/defs.bzl"))?;
        let source = BazelSource::new(&db, BazelRepository::new(&db, root), file);
        let failure = opaque(preflight_bazel_source(&db, source))?;
        assert!(
            matches!(failure.reason(), BazelPreflightError::UninitializedModule(found) if found == name),
            "{code}: {:?}",
            failure.reason()
        );
    }
    Ok(())
}

#[test]
fn eager_function_call_or_default_taints_entire_source() -> anyhow::Result<()> {
    for code in [
        "GOOD = 1\ndef compute():\n    return GOOD\nRESULT = compute()\n",
        "def compute():\n    return 1\ndef public(value=compute()):\n    return value\nGOOD = 1\n",
    ] {
        let (db, root) = test_db(&[
            ("MODULE.bazel", ""),
            ("pkg/BUILD", ""),
            ("pkg/defs.bzl", code),
        ])?;
        let file = system_path_to_file(&db, root.join("pkg/defs.bzl"))?;
        let source = BazelSource::new(&db, BazelRepository::new(&db, root), file);
        let failure = opaque(preflight_bazel_source(&db, source))?;
        assert!(
            matches!(
                failure.reason(),
                BazelPreflightError::Unsupported("dynamic module initializers or defaults")
            ),
            "{code}: {:?}",
            failure.reason()
        );
    }
    Ok(())
}

#[test]
fn duplicate_module_names_taint_every_export() -> anyhow::Result<()> {
    for code in [
        "GOOD = 1\nGOOD = 2\n",
        "def good():\n    return 1\ndef good():\n    return 2\n",
        "GOOD = 1\ndef GOOD():\n    return 2\n",
    ] {
        let (db, root) = test_db(&[
            ("MODULE.bazel", ""),
            ("pkg/BUILD", ""),
            ("pkg/defs.bzl", code),
        ])?;
        let file = system_path_to_file(&db, root.join("pkg/defs.bzl"))?;
        let source = BazelSource::new(&db, BazelRepository::new(&db, root), file);
        let failure = opaque(preflight_bazel_source(&db, source))?;
        assert!(
            matches!(failure.reason(), BazelPreflightError::DuplicateGlobal(name) if name == "GOOD" || name == "good"),
            "{code}: {:?}",
            failure.reason()
        );
    }
    Ok(())
}

#[test]
fn duplicate_parameter_names_taint_unused_function_and_export() -> anyhow::Result<()> {
    let (db, root) = test_db(&[
        ("MODULE.bazel", ""),
        ("pkg/BUILD", ""),
        (
            "pkg/defs.bzl",
            "def broken(value, value):\n    return value\nGOOD = 1\n",
        ),
    ])?;
    let file = system_path_to_file(&db, root.join("pkg/defs.bzl"))?;
    let source = BazelSource::new(&db, BazelRepository::new(&db, root), file);
    let failure = opaque(preflight_bazel_source(&db, source))?;
    assert!(matches!(
        failure.reason(),
        BazelPreflightError::DuplicateParameter(name) if name == "value"
    ));
    assert!(failure.range().is_some());
    Ok(())
}

#[test]
fn eager_unverified_integer_literals_taint_later_export() -> anyhow::Result<()> {
    for value in ["2147483648", "-2147483648"] {
        let code = format!("TOO_LARGE = {value}\nGOOD = 1\n");
        let (db, root) = test_db(&[
            ("MODULE.bazel", ""),
            ("pkg/BUILD", ""),
            ("pkg/defs.bzl", &code),
        ])?;
        let file = system_path_to_file(&db, root.join("pkg/defs.bzl"))?;
        let source = BazelSource::new(&db, BazelRepository::new(&db, root), file);
        let failure = opaque(preflight_bazel_source(&db, source))?;
        assert!(matches!(
            failure.reason(),
            BazelPreflightError::Unsupported("integer literal outside supported range")
        ));
        assert!(failure.range().is_some());
    }
    Ok(())
}

#[test]
fn inline_annotations_need_an_explicit_typed_bazel_profile() -> anyhow::Result<()> {
    let (db, root) = test_db(&[
        ("MODULE.bazel", ""),
        ("pkg/BUILD", ""),
        (
            "pkg/defs.bzl",
            "def typed(value: int) -> int:\n    return value\nGOOD = 1\n",
        ),
    ])?;
    let file = system_path_to_file(&db, root.join("pkg/defs.bzl"))?;
    let source = BazelSource::new(&db, BazelRepository::new(&db, root), file);
    assert!(matches!(
        admit_bazel_source(&db, source),
        BazelSourceAdmission::Admitted(_)
    ));
    let failure = opaque(preflight_bazel_source(&db, source))?;
    assert!(matches!(
        failure.reason(),
        BazelPreflightError::InlineAnnotation
    ));
    assert!(failure.range().is_some());
    Ok(())
}

#[test]
fn unresolved_loads_and_unmodeled_body_control_flow_are_opaque() -> anyhow::Result<()> {
    for code in [
        "load(\":defs.bzl\", \"symbol\")\nGOOD = 1\n",
        "def public(value):\n    if value:\n        return 1\n    return 0\nGOOD = 1\n",
    ] {
        let (db, root) = test_db(&[
            ("MODULE.bazel", ""),
            ("pkg/BUILD", ""),
            ("pkg/defs.bzl", code),
        ])?;
        let file = system_path_to_file(&db, root.join("pkg/defs.bzl"))?;
        let source = BazelSource::new(&db, BazelRepository::new(&db, root), file);
        let failure = opaque(preflight_bazel_source(&db, source))?;
        assert!(
            matches!(failure.reason(), BazelPreflightError::Unsupported(_)),
            "{code}: {:?}",
            failure.reason()
        );
        assert!(failure.range().is_some());
    }
    Ok(())
}

#[test]
fn source_admission_failure_is_carried_into_name_preflight() -> anyhow::Result<()> {
    let (db, root) = test_db(&[
        ("WORKSPACE", ""),
        ("pkg/BUILD", ""),
        ("pkg/defs.bzl", "class PythonOnly:\n    pass\nGOOD = 1\n"),
    ])?;
    let file = system_path_to_file(&db, root.join("pkg/defs.bzl"))?;
    let source = BazelSource::new(&db, BazelRepository::new(&db, root), file);
    let failure = opaque(preflight_bazel_source(&db, source))?;
    assert!(matches!(
        failure.reason(),
        BazelPreflightError::Admission(_)
    ));
    assert_eq!(failure.file(), file);
    assert_eq!(
        failure
            .admission_diagnostic()
            .map(|diagnostic| diagnostic.id()),
        Some(DiagnosticId::InvalidSyntax)
    );
    Ok(())
}

#[test]
fn source_changes_revalidate_names_without_new_repository_key() -> anyhow::Result<()> {
    let (mut db, root) = test_db(&[
        ("MODULE.bazel", ""),
        ("pkg/BUILD", ""),
        (
            "pkg/defs.bzl",
            "GOOD = 1\ndef public(value):\n    return value\n",
        ),
    ])?;
    let path = root.join("pkg/defs.bzl");
    let file = system_path_to_file(&db, &path)?;
    let source = BazelSource::new(&db, BazelRepository::new(&db, root.clone()), file);
    ready(preflight_bazel_source(&db, source))?;

    db.write_file(&path, "GOOD = 1\ndef broken():\n    return missing\n")?;
    let source = BazelSource::new(&db, BazelRepository::new(&db, root.clone()), file);
    let failure = opaque(preflight_bazel_source(&db, source))?;
    assert!(matches!(
        failure.reason(),
        BazelPreflightError::UnknownName(name) if name == "missing"
    ));
    db.write_file(&path, "GOOD = 1\ndef public(value):\n    return value\n")?;
    let source = BazelSource::new(&db, BazelRepository::new(&db, root), file);
    ready(preflight_bazel_source(&db, source))
}
