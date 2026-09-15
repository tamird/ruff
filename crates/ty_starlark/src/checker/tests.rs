use std::fmt::Write as _;

use ruff_db::files::system_path_to_file;
use ruff_db::system::DbWithWritableSystem as _;

use crate::bazel::BazelRepository;
use crate::preflight::BazelPreflightError;
use crate::source::BazelSource;
use crate::testing::test_db;

use super::{
    BazelCheckError, BazelCheckedSource, BazelExport, BazelExportKind, BazelFunction,
    BazelModuleSummary, BazelScalar, summarize_bazel_source,
};

fn checked(source: &BazelCheckedSource) -> anyhow::Result<&BazelModuleSummary> {
    match source {
        BazelCheckedSource::Checked(summary) => Ok(summary),
        BazelCheckedSource::Opaque(failure) => {
            anyhow::bail!("expected a checked Bazel source, found {failure:?}")
        }
    }
}

fn scalar(summary: &BazelModuleSummary, name: &str) -> anyhow::Result<BazelScalar> {
    match summary.export(name).map(BazelExport::kind) {
        Some(BazelExportKind::Scalar(scalar)) => Ok(*scalar),
        other => anyhow::bail!("expected scalar {name}, found {other:?}"),
    }
}

fn function<'summary>(
    summary: &'summary BazelModuleSummary,
    name: &str,
) -> anyhow::Result<&'summary BazelFunction> {
    match summary.export(name).map(BazelExport::kind) {
        Some(BazelExportKind::Function(function)) => Ok(function),
        other => anyhow::bail!("expected function {name}, found {other:?}"),
    }
}

#[test]
fn stable_runtime_infers_only_body_backed_scalars() -> anyhow::Result<()> {
    let (db, root) = test_db(&[
        ("MODULE.bazel", ""),
        ("pkg/BUILD", ""),
        (
            "pkg/defs.bzl",
            r#""Module docs"
GOOD = 1
ALIAS = GOOD
TEXT = "yes"
FLAG = True
EMPTY = None
NEGATIVE = -5
def global_value():
    return ALIAS
def identity(value=GOOD):
    return value
def ignores(value=GOOD):
    return TEXT
def implicit(value):
    pass
def calls_ignores():
    return ignores("any type")
"#,
        ),
    ])?;
    let file = system_path_to_file(&db, root.join("pkg/defs.bzl"))?;
    let source = BazelSource::new(&db, BazelRepository::new(&db, root), file);
    let summary = checked(summarize_bazel_source(&db, source))?;
    assert_eq!(summary.file(), file);
    assert_eq!(scalar(summary, "GOOD")?, BazelScalar::Int);
    assert_eq!(scalar(summary, "ALIAS")?, BazelScalar::Int);
    assert_eq!(scalar(summary, "TEXT")?, BazelScalar::Str);
    assert_eq!(scalar(summary, "FLAG")?, BazelScalar::Bool);
    assert_eq!(scalar(summary, "EMPTY")?, BazelScalar::None);
    assert_eq!(scalar(summary, "NEGATIVE")?, BazelScalar::Int);
    assert_eq!(
        function(summary, "global_value")?.result(),
        BazelScalar::Int
    );
    let identity = function(summary, "identity")?;
    assert_eq!(identity.result(), BazelScalar::Unknown);
    assert!(!identity.body_may_fail());
    assert_eq!(identity.required_positional(), 0);
    assert_eq!(identity.total_positional(), 1);
    assert_eq!(function(summary, "ignores")?.result(), BazelScalar::Str);
    assert_eq!(function(summary, "implicit")?.result(), BazelScalar::None);
    assert_eq!(
        function(summary, "calls_ignores")?.result(),
        BazelScalar::Str
    );
    assert!(summary.problems().is_empty());
    assert!(
        summary
            .exports()
            .iter()
            .all(|export| export.file() == file && !export.range().is_empty())
    );
    Ok(())
}

#[test]
fn private_bindings_remain_available_within_source_but_not_as_exports() -> anyhow::Result<()> {
    let (db, root) = test_db(&[
        ("MODULE.bazel", ""),
        ("pkg/BUILD", ""),
        (
            "pkg/defs.bzl",
            "_PRIVATE = 1\ndef _helper():\n    return _PRIVATE\ndef public():\n    return _helper()\n",
        ),
    ])?;
    let file = system_path_to_file(&db, root.join("pkg/defs.bzl"))?;
    let source = BazelSource::new(&db, BazelRepository::new(&db, root), file);
    let summary = checked(summarize_bazel_source(&db, source))?;
    assert_eq!(function(summary, "public")?.result(), BazelScalar::Int);
    assert_eq!(summary.exports().len(), 1);
    assert!(summary.export("_PRIVATE").is_none());
    assert!(summary.export("_helper").is_none());
    assert!(summary.problems().is_empty());
    Ok(())
}

#[test]
fn forward_bindings_and_file_edits_revalidate_function_results() -> anyhow::Result<()> {
    let runtime = "def first(value):\n    return second(value)\ndef second(value):\n    return LATER\nLATER = True\n";
    let (mut db, root) = test_db(&[
        ("WORKSPACE.bazel", ""),
        ("pkg/BUILD", ""),
        ("pkg/defs.bzl", runtime),
    ])?;
    let path = root.join("pkg/defs.bzl");
    let file = system_path_to_file(&db, &path)?;
    let repository = BazelRepository::new(&db, root.clone());
    let source = BazelSource::new(&db, repository, file);
    let summary = checked(summarize_bazel_source(&db, source))?;
    assert_eq!(function(summary, "first")?.result(), BazelScalar::Bool);
    assert_eq!(function(summary, "second")?.result(), BazelScalar::Bool);
    assert_eq!(scalar(summary, "LATER")?, BazelScalar::Bool);

    db.write_file(&path, runtime.replace("LATER = True", "LATER = \"text\""))?;
    let repository = BazelRepository::new(&db, root);
    let source = BazelSource::new(&db, repository, file);
    let summary = checked(summarize_bazel_source(&db, source))?;
    assert_eq!(function(summary, "first")?.result(), BazelScalar::Str);
    assert_eq!(function(summary, "second")?.result(), BazelScalar::Str);
    assert_eq!(scalar(summary, "LATER")?, BazelScalar::Str);
    Ok(())
}

#[test]
fn source_calls_use_supplied_values_and_only_omitted_defaults() -> anyhow::Result<()> {
    let (db, root) = test_db(&[
        ("MODULE.bazel", ""),
        ("pkg/BUILD", ""),
        (
            "pkg/defs.bzl",
            "BASE = 1\ndef echo(value=BASE):\n    return value\ndef default_call():\n    return echo()\ndef str_call():\n    return echo(\"text\")\ndef twice():\n    first = echo(2)\n    second = echo(\"other\")\n    return second\n",
        ),
    ])?;
    let file = system_path_to_file(&db, root.join("pkg/defs.bzl"))?;
    let source = BazelSource::new(&db, BazelRepository::new(&db, root), file);
    let summary = checked(summarize_bazel_source(&db, source))?;
    let echo = function(summary, "echo")?;
    assert_eq!(echo.result(), BazelScalar::Unknown);
    assert!(!echo.body_may_fail());
    assert_eq!(
        function(summary, "default_call")?.result(),
        BazelScalar::Int
    );
    assert_eq!(function(summary, "str_call")?.result(), BazelScalar::Str);
    assert_eq!(function(summary, "twice")?.result(), BazelScalar::Str);
    assert!(summary.problems().is_empty());
    Ok(())
}

#[test]
fn bad_call_site_is_reported_once_across_specialized_contexts() -> anyhow::Result<()> {
    let runtime = "def broken(value):\n    return keep()\ndef keep(value):\n    return 1\ndef first():\n    return broken(1)\ndef second():\n    return broken(\"text\")\nGOOD = 1\n";
    let (db, root) = test_db(&[
        ("MODULE.bazel", ""),
        ("pkg/BUILD", ""),
        ("pkg/defs.bzl", runtime),
    ])?;
    let file = system_path_to_file(&db, root.join("pkg/defs.bzl"))?;
    let source = BazelSource::new(&db, BazelRepository::new(&db, root), file);
    let summary = checked(summarize_bazel_source(&db, source))?;
    assert_eq!(scalar(summary, "GOOD")?, BazelScalar::Int);
    for name in ["broken", "first", "second"] {
        let affected = function(summary, name)?;
        assert_eq!(affected.result(), BazelScalar::Unknown);
        assert!(affected.body_may_fail());
    }
    let [problem] = summary.problems() else {
        anyhow::bail!("expected one source call problem: {:?}", summary.problems());
    };
    assert_eq!(problem.file(), file);
    assert_eq!(
        problem.range().start().to_usize(),
        runtime.find("keep()").unwrap()
    );
    Ok(())
}

#[test]
fn changed_argument_recursion_remains_unknown_after_prior_evaluation() -> anyhow::Result<()> {
    let (db, root) = test_db(&[
        ("MODULE.bazel", ""),
        ("pkg/BUILD", ""),
        (
            "pkg/defs.bzl",
            "def bounce(value):\n    return bounce(1)\ndef caller():\n    return bounce(\"text\")\n",
        ),
    ])?;
    let file = system_path_to_file(&db, root.join("pkg/defs.bzl"))?;
    let source = BazelSource::new(&db, BazelRepository::new(&db, root), file);
    let summary = checked(summarize_bazel_source(&db, source))?;
    assert!(function(summary, "bounce")?.body_may_fail());
    assert_eq!(function(summary, "bounce")?.result(), BazelScalar::Unknown);
    assert!(function(summary, "caller")?.body_may_fail());
    assert_eq!(function(summary, "caller")?.result(), BazelScalar::Unknown);
    Ok(())
}

#[test]
fn excessive_call_graph_depth_keeps_every_export_opaque() -> anyhow::Result<()> {
    let mut code = String::from("GOOD = 1\n");
    for index in 0..=super::MAX_ACTIVE_FUNCTIONS {
        if index < super::MAX_ACTIVE_FUNCTIONS {
            write!(
                code,
                "def step_{index}():\n    return step_{}()\n",
                index + 1
            )?;
        } else {
            write!(code, "def step_{index}():\n    return 1\n")?;
        }
    }
    let (db, root) = test_db(&[
        ("MODULE.bazel", ""),
        ("pkg/BUILD", ""),
        ("pkg/defs.bzl", &code),
    ])?;
    let file = system_path_to_file(&db, root.join("pkg/defs.bzl"))?;
    let source = BazelSource::new(&db, BazelRepository::new(&db, root), file);
    let BazelCheckedSource::Opaque(failure) = summarize_bazel_source(&db, source) else {
        anyhow::bail!("exhausted proof exposed checked exports");
    };
    assert_eq!(failure.file(), file);
    assert!(failure.range().is_some());
    assert!(matches!(
        failure.reason(),
        BazelPreflightError::AnalysisLimit
    ));
    Ok(())
}

#[test]
fn independent_generic_functions_do_not_consume_specialization_quota() -> anyhow::Result<()> {
    let mut code = String::from("GOOD = 1\n");
    for index in 0..=super::MAX_SPECIALIZED_CONTEXTS {
        write!(code, "def separate_{index}():\n    return 1\n")?;
    }
    let (db, root) = test_db(&[
        ("MODULE.bazel", ""),
        ("pkg/BUILD", ""),
        ("pkg/defs.bzl", &code),
    ])?;
    let file = system_path_to_file(&db, root.join("pkg/defs.bzl"))?;
    let source = BazelSource::new(&db, BazelRepository::new(&db, root), file);
    let summary = checked(summarize_bazel_source(&db, source))?;
    assert_eq!(scalar(summary, "GOOD")?, BazelScalar::Int);
    assert_eq!(summary.exports().len(), super::MAX_SPECIALIZED_CONTEXTS + 2);
    assert!(summary.problems().is_empty());
    Ok(())
}

#[test]
fn excessive_distinct_specializations_keep_every_export_opaque() -> anyhow::Result<()> {
    let mut code = String::from("GOOD = 1\n");
    for index in 0..=super::MAX_SPECIALIZED_CONTEXTS {
        write!(
            code,
            "def _helper_{index}(value):\n    return value\ndef public_{index}():\n    return _helper_{index}(1)\n"
        )?;
    }
    let (db, root) = test_db(&[
        ("MODULE.bazel", ""),
        ("pkg/BUILD", ""),
        ("pkg/defs.bzl", &code),
    ])?;
    let file = system_path_to_file(&db, root.join("pkg/defs.bzl"))?;
    let source = BazelSource::new(&db, BazelRepository::new(&db, root), file);
    let BazelCheckedSource::Opaque(failure) = summarize_bazel_source(&db, source) else {
        anyhow::bail!("exhausted specialization exposed checked exports");
    };
    assert_eq!(failure.file(), file);
    assert!(failure.range().is_some());
    assert!(matches!(
        failure.reason(),
        BazelPreflightError::AnalysisLimit
    ));
    Ok(())
}

#[test]
fn invalid_arity_in_unused_body_reports_range_without_opaque_exports() -> anyhow::Result<()> {
    let runtime = "def broken(value):\n    return keep(1, 2)\ndef keep(value):\n    return 1\ndef caller():\n    return broken(1)\nGOOD = 1\n";
    let (db, root) = test_db(&[
        ("REPO.bazel", ""),
        ("pkg/BUILD", ""),
        ("pkg/defs.bzl", runtime),
    ])?;
    let file = system_path_to_file(&db, root.join("pkg/defs.bzl"))?;
    let source = BazelSource::new(&db, BazelRepository::new(&db, root), file);
    let summary = checked(summarize_bazel_source(&db, source))?;
    assert_eq!(scalar(summary, "GOOD")?, BazelScalar::Int);
    assert_eq!(function(summary, "keep")?.result(), BazelScalar::Int);
    assert!(!function(summary, "keep")?.body_may_fail());
    assert_eq!(function(summary, "broken")?.result(), BazelScalar::Unknown);
    assert!(function(summary, "broken")?.body_may_fail());
    assert_eq!(function(summary, "caller")?.result(), BazelScalar::Unknown);
    assert!(function(summary, "caller")?.body_may_fail());
    let [problem] = summary.problems() else {
        anyhow::bail!("expected one invalid call: {:?}", summary.problems());
    };
    assert_eq!(problem.file(), file);
    assert_eq!(problem.declaration_file(), file);
    assert_eq!(
        problem.range().start().to_usize(),
        runtime.find("keep(1, 2)").unwrap()
    );
    assert_eq!(
        problem.declaration_range().start().to_usize(),
        runtime.find("keep(value)").unwrap()
    );
    assert!(matches!(
        problem.reason(),
        BazelCheckError::InvalidArity {
            callee,
            minimum: 1,
            maximum: 1,
            actual: 2,
        } if callee == "keep"
    ));
    Ok(())
}

#[test]
fn nested_argument_failure_taints_outer_literal_return() -> anyhow::Result<()> {
    let runtime = "def inner(value):\n    return 1\ndef outer(value):\n    return 7\ndef bad():\n    return outer(inner(1, 2))\nGOOD = 1\n";
    let (db, root) = test_db(&[
        ("MODULE.bazel", ""),
        ("pkg/BUILD", ""),
        ("pkg/defs.bzl", runtime),
    ])?;
    let file = system_path_to_file(&db, root.join("pkg/defs.bzl"))?;
    let source = BazelSource::new(&db, BazelRepository::new(&db, root), file);
    let summary = checked(summarize_bazel_source(&db, source))?;
    assert_eq!(scalar(summary, "GOOD")?, BazelScalar::Int);
    assert_eq!(function(summary, "outer")?.result(), BazelScalar::Int);
    assert_eq!(function(summary, "bad")?.result(), BazelScalar::Unknown);
    assert!(function(summary, "bad")?.body_may_fail());
    assert_eq!(summary.problems().len(), 1);
    assert_eq!(
        summary.problems()[0].range().start().to_usize(),
        runtime.find("inner(1, 2)").unwrap()
    );
    Ok(())
}

#[test]
fn recursive_assignment_failure_taints_literal_return_and_callers() -> anyhow::Result<()> {
    let (db, root) = test_db(&[
        ("MODULE.bazel", ""),
        ("pkg/BUILD", ""),
        (
            "pkg/defs.bzl",
            "def first():\n    ignored = second()\n    return 1\ndef second():\n    return first()\ndef caller():\n    return first()\nGOOD = \"safe\"\n",
        ),
    ])?;
    let file = system_path_to_file(&db, root.join("pkg/defs.bzl"))?;
    let source = BazelSource::new(&db, BazelRepository::new(&db, root), file);
    let summary = checked(summarize_bazel_source(&db, source))?;
    assert_eq!(scalar(summary, "GOOD")?, BazelScalar::Str);
    assert_eq!(function(summary, "first")?.result(), BazelScalar::Unknown);
    assert_eq!(function(summary, "second")?.result(), BazelScalar::Unknown);
    assert_eq!(function(summary, "caller")?.result(), BazelScalar::Unknown);
    assert!(function(summary, "first")?.body_may_fail());
    assert!(function(summary, "second")?.body_may_fail());
    assert!(function(summary, "caller")?.body_may_fail());
    assert!(summary.problems().is_empty());
    Ok(())
}

#[test]
fn unreachable_dynamic_calls_do_not_change_reachable_result() -> anyhow::Result<()> {
    let (db, root) = test_db(&[
        ("MODULE.bazel", ""),
        ("pkg/BUILD", ""),
        (
            "pkg/defs.bzl",
            "def early():\n    return 1\n    ignored = later(1, 2)\ndef later(value):\n    return None\n",
        ),
    ])?;
    let file = system_path_to_file(&db, root.join("pkg/defs.bzl"))?;
    let source = BazelSource::new(&db, BazelRepository::new(&db, root), file);
    let summary = checked(summarize_bazel_source(&db, source))?;
    assert_eq!(function(summary, "early")?.result(), BazelScalar::Int);
    assert!(!function(summary, "early")?.body_may_fail());
    assert_eq!(function(summary, "later")?.result(), BazelScalar::None);
    assert!(summary.problems().is_empty());
    Ok(())
}

#[test]
fn failed_preflight_never_exposes_superficially_valid_exports() -> anyhow::Result<()> {
    for runtime in [
        "def broken():\n    return missing\nGOOD = 1\n",
        "BAD = 1_0\nGOOD = 1\n",
        "GOOD = 1\ndef public():\n    return (1, 2)\n",
    ] {
        let (db, root) = test_db(&[
            ("MODULE.bazel", ""),
            ("pkg/BUILD", ""),
            ("pkg/defs.bzl", runtime),
        ])?;
        let file = system_path_to_file(&db, root.join("pkg/defs.bzl"))?;
        let source = BazelSource::new(&db, BazelRepository::new(&db, root), file);
        let BazelCheckedSource::Opaque(failure) = summarize_bazel_source(&db, source) else {
            anyhow::bail!("opaque runtime exposed a checked source: {runtime}");
        };
        assert_eq!(failure.file(), file);
        assert!(failure.range().is_some());
    }
    Ok(())
}
