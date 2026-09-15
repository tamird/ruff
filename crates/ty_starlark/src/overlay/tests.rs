use std::fmt::Write as _;

use ruff_db::files::{File, system_path_to_file};
use ruff_db::system::DbWithWritableSystem as _;

use crate::bazel::BazelRepository;
use crate::checker::{BazelCheckedSource, BazelExportKind, BazelScalar, summarize_bazel_source};
use crate::preflight::BazelPreflightError;
use crate::source::BazelSource;
use crate::testing::test_db;

use super::{
    BazelVerificationError, BazelVerificationFailure, BazelVerifiedExport, BazelVerifiedExportKind,
    BazelVerifiedFunction, BazelVerifiedModule, BazelVerifiedSource, verify_bazel_source,
};

fn checked(result: &BazelVerifiedSource) -> anyhow::Result<&BazelVerifiedModule> {
    match result {
        BazelVerifiedSource::Checked(module) => Ok(module),
        BazelVerifiedSource::Opaque(failure) => {
            anyhow::bail!("expected checked runtime and stub: {failure:?}")
        }
    }
}

fn opaque(result: &BazelVerifiedSource) -> anyhow::Result<&BazelVerificationFailure> {
    match result {
        BazelVerifiedSource::Opaque(failure) => Ok(failure),
        BazelVerifiedSource::Checked(module) => {
            anyhow::bail!("expected an opaque typed interface: {module:?}")
        }
    }
}

fn function<'module>(
    module: &'module BazelVerifiedModule,
    name: &str,
) -> anyhow::Result<&'module BazelVerifiedFunction> {
    match module.export(name).map(BazelVerifiedExport::kind) {
        Some(BazelVerifiedExportKind::Function(function)) => Ok(function),
        other => anyhow::bail!("expected function {name}, found {other:?}"),
    }
}

#[test]
fn stable_runtime_remains_authoritative_for_partial_primitive_stub() -> anyhow::Result<()> {
    let runtime = "BASE = 1\ndef identity(value):\n    return value\ndef constant(value):\n    return \"s\"\ndef omitted(value):\n    return value\n";
    let (db, root) = test_db(&[
        ("MODULE.bazel", ""),
        ("pkg/BUILD", ""),
        ("pkg/defs.bzl", runtime),
        (
            "pkg/defs.bzl.pyi",
            "def identity(value: int) -> int: ...\ndef constant(value: bool) -> str: ...\n",
        ),
    ])?;
    let source_file = system_path_to_file(&db, root.join("pkg/defs.bzl"))?;
    let stub_file = system_path_to_file(&db, root.join("pkg/defs.bzl.pyi"))?;
    let source = BazelSource::new(&db, BazelRepository::new(&db, root), source_file);
    let module = checked(verify_bazel_source(&db, source))?;
    assert_eq!(module.source_file(), source_file);
    assert_eq!(module.stub_file(), Some(stub_file));
    assert_eq!(module.exports().len(), 4);
    assert!(module.problems().is_empty());
    assert!(
        module
            .exports()
            .iter()
            .all(|export| export.source_file() == source_file && !export.source_range().is_empty())
    );
    let Some(BazelVerifiedExportKind::Scalar(BazelScalar::Int)) =
        module.export("BASE").map(BazelVerifiedExport::kind)
    else {
        anyhow::bail!("source-only BASE lost its int precision")
    };
    let identity = function(module, "identity")?;
    assert_eq!(identity.result(), BazelScalar::Int);
    assert_eq!(identity.stub_file(), Some(stub_file));
    assert!(identity.stub_result_range().is_some());
    assert_eq!(identity.parameters()[0].name(), "value");
    assert_eq!(identity.parameters()[0].scalar(), BazelScalar::Int);
    assert!(identity.parameters()[0].stub_annotation_range().is_some());
    assert!(!identity.body_may_fail());
    let constant = function(module, "constant")?;
    assert_eq!(constant.parameters()[0].scalar(), BazelScalar::Bool);
    assert_eq!(constant.result(), BazelScalar::Str);
    let omitted = function(module, "omitted")?;
    assert_eq!(omitted.stub_file(), None);
    assert_eq!(omitted.parameters()[0].scalar(), BazelScalar::Unknown);
    assert_eq!(omitted.result(), BazelScalar::Unknown);

    let BazelCheckedSource::Checked(source_only) = summarize_bazel_source(&db, source) else {
        anyhow::bail!("runtime summary unexpectedly opaque")
    };
    let Some(BazelExportKind::Function(identity)) = source_only
        .export("identity")
        .map(crate::checker::BazelExport::kind)
    else {
        anyhow::bail!("source-only identity is missing")
    };
    assert_eq!(identity.result(), BazelScalar::Unknown);
    Ok(())
}

#[test]
fn incompatible_and_unproved_returns_point_to_source_and_stub() -> anyhow::Result<()> {
    let runtime = "def identity(value):\n    return \"s\"\n";
    let stub = "def identity(value: int) -> int: ...\n";
    let (db, root) = test_db(&[
        ("MODULE.bazel", ""),
        ("pkg/BUILD", ""),
        ("pkg/defs.bzl", runtime),
        ("pkg/defs.bzl.pyi", stub),
    ])?;
    let source_file = system_path_to_file(&db, root.join("pkg/defs.bzl"))?;
    let stub_file = system_path_to_file(&db, root.join("pkg/defs.bzl.pyi"))?;
    let source = BazelSource::new(&db, BazelRepository::new(&db, root), source_file);
    let failure = opaque(verify_bazel_source(&db, source))?;
    assert!(matches!(
        failure.reason(),
        BazelVerificationError::ReturnType {
            name,
            actual: BazelScalar::Str,
            expected: BazelScalar::Int,
        } if name == "identity"
    ));
    assert_eq!(failure.file(), Some(source_file));
    assert_eq!(
        failure
            .range()
            .ok_or(anyhow::anyhow!("source range"))?
            .start()
            .to_usize(),
        runtime
            .find("\"s\"")
            .ok_or(anyhow::anyhow!("return literal"))?
    );
    assert_eq!(failure.related_file(), Some(stub_file));
    assert_eq!(
        failure
            .related_range()
            .ok_or(anyhow::anyhow!("stub result range"))?
            .start()
            .to_usize(),
        stub.find("-> int")
            .ok_or(anyhow::anyhow!("return annotation"))?
            + 3
    );

    for (runtime, reason) in [
        (
            "def identity():\n    pass\n",
            "runtime result of 'identity' is None; stub declares int",
        ),
        (
            "def helper():\n    return 1\ndef identity():\n    return helper\n",
            "runtime result of 'identity' is unproved as int",
        ),
    ] {
        let (db, root) = test_db(&[
            ("MODULE.bazel", ""),
            ("pkg/BUILD", ""),
            ("pkg/defs.bzl", runtime),
            ("pkg/defs.bzl.pyi", "def identity() -> int: ...\n"),
        ])?;
        let file = system_path_to_file(&db, root.join("pkg/defs.bzl"))?;
        let source = BazelSource::new(&db, BazelRepository::new(&db, root), file);
        let failure = opaque(verify_bazel_source(&db, source))?;
        assert_eq!(failure.reason().to_string(), reason, "{runtime}");
        assert_eq!(failure.file(), Some(file));
        assert!(failure.related_file().is_some());
    }
    Ok(())
}

#[test]
fn source_defaults_must_match_annotations_and_revalidate_with_source_edit() -> anyhow::Result<()> {
    let (mut db, root) = test_db(&[
        ("MODULE.bazel", ""),
        ("pkg/BUILD", ""),
        (
            "pkg/defs.bzl",
            "BASE = 1\ndef identity(value=BASE):\n    return value\n",
        ),
        (
            "pkg/defs.bzl.pyi",
            "def identity(value: str = ...) -> str: ...\n",
        ),
    ])?;
    let path = root.join("pkg/defs.bzl");
    let source_file = system_path_to_file(&db, &path)?;
    let stub_file = system_path_to_file(&db, root.join("pkg/defs.bzl.pyi"))?;
    let source = BazelSource::new(&db, BazelRepository::new(&db, root.clone()), source_file);
    let failure = opaque(verify_bazel_source(&db, source))?;
    assert!(matches!(
        failure.reason(),
        BazelVerificationError::DefaultType {
            name,
            actual: BazelScalar::Int,
            expected: BazelScalar::Str,
        } if name == "value"
    ));
    assert_eq!(failure.file(), Some(source_file));
    assert_eq!(failure.related_file(), Some(stub_file));

    db.write_file(
        &path,
        "BASE = \"s\"\ndef identity(value=BASE):\n    return value\n",
    )?;
    File::sync_path(&mut db, &path);
    let source = BazelSource::new(&db, BazelRepository::new(&db, root), source_file);
    let module = checked(verify_bazel_source(&db, source))?;
    let identity = function(module, "identity")?;
    assert_eq!(identity.result(), BazelScalar::Str);
    assert_eq!(identity.parameters()[0].scalar(), BazelScalar::Str);
    assert!(identity.parameters()[0].has_default());
    Ok(())
}

#[test]
fn stub_names_positions_and_default_presence_must_match_public_source() -> anyhow::Result<()> {
    for (runtime, stub, reason) in [
        (
            "def public(value):\n    return value\n",
            "def public(other: int) -> int: ...\n",
            "stub parameter 'other' differs from runtime 'value'",
        ),
        (
            "def public(value):\n    return value\n",
            "def public(value: int, extra: str) -> int: ...\n",
            "stub function 'public' has 2 parameters; runtime has 1",
        ),
        (
            "def public(value):\n    return value\n",
            "def public(value: int = ...) -> int: ...\n",
            "stub parameter 'value' disagrees with runtime default presence",
        ),
        (
            "def public(value):\n    return value\n",
            "def missing() -> int: ...\n",
            "stub function 'missing' has no exported runtime function",
        ),
        (
            "def _secret():\n    return 1\ndef public():\n    return 1\n",
            "def _secret() -> int: ...\n",
            "stub function '_secret' has no exported runtime function",
        ),
        (
            "public = 1\n",
            "def public() -> int: ...\n",
            "stub function 'public' has no exported runtime function",
        ),
    ] {
        let (db, root) = test_db(&[
            ("MODULE.bazel", ""),
            ("pkg/BUILD", ""),
            ("pkg/defs.bzl", runtime),
            ("pkg/defs.bzl.pyi", stub),
        ])?;
        let source_file = system_path_to_file(&db, root.join("pkg/defs.bzl"))?;
        let stub_file = system_path_to_file(&db, root.join("pkg/defs.bzl.pyi"))?;
        let source = BazelSource::new(&db, BazelRepository::new(&db, root), source_file);
        let failure = opaque(verify_bazel_source(&db, source))?;
        assert_eq!(failure.file(), Some(stub_file), "{stub}");
        assert_eq!(failure.reason().to_string(), reason, "{stub}");
        assert!(failure.range().is_some());
        if !stub.contains("missing") && !stub.contains("_secret") {
            assert_eq!(failure.related_file(), Some(source_file));
        }
    }
    Ok(())
}

#[test]
fn internal_calls_use_runtime_arguments_even_when_stub_claims_a_result() -> anyhow::Result<()> {
    let runtime = "def helper(value):\n    return 1\ndef wrapper():\n    return helper(\"s\")\n";
    let stub = "def helper(value: int) -> int: ...\ndef wrapper() -> int: ...\n";
    let (db, root) = test_db(&[
        ("MODULE.bazel", ""),
        ("pkg/BUILD", ""),
        ("pkg/defs.bzl", runtime),
        ("pkg/defs.bzl.pyi", stub),
    ])?;
    let source_file = system_path_to_file(&db, root.join("pkg/defs.bzl"))?;
    let stub_file = system_path_to_file(&db, root.join("pkg/defs.bzl.pyi"))?;
    let source = BazelSource::new(&db, BazelRepository::new(&db, root), source_file);
    let failure = opaque(verify_bazel_source(&db, source))?;
    assert!(matches!(
        failure.reason(),
        BazelVerificationError::InternalArgument {
            callee,
            actual: BazelScalar::Str,
            expected: BazelScalar::Int,
        } if callee == "helper"
    ));
    assert_eq!(failure.file(), Some(source_file));
    assert_eq!(
        failure
            .range()
            .ok_or(anyhow::anyhow!("argument span"))?
            .start()
            .to_usize(),
        runtime
            .find("\"s\"")
            .ok_or(anyhow::anyhow!("bad argument"))?
    );
    assert_eq!(failure.related_file(), Some(stub_file));
    assert_eq!(
        failure
            .related_range()
            .ok_or(anyhow::anyhow!("stub annotation"))?
            .start()
            .to_usize(),
        stub.find("value: int")
            .ok_or(anyhow::anyhow!("int annotation"))?
            + 7
    );
    Ok(())
}

#[test]
fn wrapper_parameter_types_flow_through_internal_calls() -> anyhow::Result<()> {
    let runtime = "def helper(x):\n    return 1\ndef route(x):\n    return helper(x)\n";
    let stub = "def helper(x: int) -> int: ...\ndef route(x: str) -> int: ...\n";
    let (mut db, root) = test_db(&[
        ("MODULE.bazel", ""),
        ("pkg/BUILD", ""),
        ("pkg/defs.bzl", runtime),
        ("pkg/defs.bzl.pyi", stub),
    ])?;
    let source_file = system_path_to_file(&db, root.join("pkg/defs.bzl"))?;
    let stub_path = root.join("pkg/defs.bzl.pyi");
    let stub_file = system_path_to_file(&db, &stub_path)?;
    let source = BazelSource::new(&db, BazelRepository::new(&db, root.clone()), source_file);
    let failure = opaque(verify_bazel_source(&db, source))?;
    assert!(matches!(
        failure.reason(),
        BazelVerificationError::InternalArgument {
            callee,
            actual: BazelScalar::Str,
            expected: BazelScalar::Int,
        } if callee == "helper"
    ));
    assert_eq!(failure.file(), Some(source_file));
    assert_eq!(
        failure
            .range()
            .ok_or(anyhow::anyhow!("wrapper argument span"))?
            .start()
            .to_usize(),
        runtime
            .rfind("helper(x)")
            .ok_or(anyhow::anyhow!("wrapper call"))?
            + 7
    );
    assert_eq!(failure.related_file(), Some(stub_file));
    assert_eq!(
        failure
            .related_range()
            .ok_or(anyhow::anyhow!("helper annotation span"))?
            .start()
            .to_usize(),
        stub.find("x: int")
            .ok_or(anyhow::anyhow!("helper annotation"))?
            + 3
    );

    db.write_file(
        &stub_path,
        "def helper(x: int) -> int: ...\ndef route(x: int) -> int: ...\n",
    )?;
    File::sync_path(&mut db, &stub_path);
    let source = BazelSource::new(&db, BazelRepository::new(&db, root), source_file);
    let module = checked(verify_bazel_source(&db, source))?;
    assert_eq!(function(module, "route")?.result(), BazelScalar::Int);
    assert_eq!(
        function(module, "route")?.parameters()[0].scalar(),
        BazelScalar::Int
    );
    Ok(())
}

#[test]
fn unproved_function_value_argument_never_justifies_a_stubbed_return() -> anyhow::Result<()> {
    let runtime = "def callback():\n    return 1\ndef helper(x):\n    return 1\ndef wrapper():\n    return helper(callback)\n";
    let stub = "def helper(x: int) -> int: ...\ndef wrapper() -> int: ...\n";
    let (db, root) = test_db(&[
        ("MODULE.bazel", ""),
        ("pkg/BUILD", ""),
        ("pkg/defs.bzl", runtime),
        ("pkg/defs.bzl.pyi", stub),
    ])?;
    let source_file = system_path_to_file(&db, root.join("pkg/defs.bzl"))?;
    let stub_file = system_path_to_file(&db, root.join("pkg/defs.bzl.pyi"))?;
    let source = BazelSource::new(&db, BazelRepository::new(&db, root), source_file);
    let failure = opaque(verify_bazel_source(&db, source))?;
    assert!(matches!(
        failure.reason(),
        BazelVerificationError::UnprovedArgument { callee, expected: BazelScalar::Int }
            if callee == "helper"
    ));
    assert_eq!(failure.file(), Some(source_file));
    assert_eq!(
        failure
            .range()
            .ok_or(anyhow::anyhow!("source argument"))?
            .start()
            .to_usize(),
        runtime
            .rfind("callback)")
            .ok_or(anyhow::anyhow!("function argument"))?
    );
    assert_eq!(failure.related_file(), Some(stub_file));
    assert_eq!(
        failure
            .related_range()
            .ok_or(anyhow::anyhow!("stub annotation"))?
            .start()
            .to_usize(),
        stub.find("x: int")
            .ok_or(anyhow::anyhow!("helper annotation"))?
            + 3
    );
    Ok(())
}

#[test]
fn unrelated_source_arity_problem_does_not_erase_checked_exports() -> anyhow::Result<()> {
    let runtime = "GOOD = 1\ndef keep(value):\n    return value\ndef broken():\n    return keep(1, 2)\ndef public():\n    return 1\n";
    let (mut db, root) = test_db(&[
        ("MODULE.bazel", ""),
        ("pkg/BUILD", ""),
        ("pkg/defs.bzl", runtime),
        ("pkg/defs.bzl.pyi", "def public() -> int: ...\n"),
    ])?;
    let source_file = system_path_to_file(&db, root.join("pkg/defs.bzl"))?;
    let stub_path = root.join("pkg/defs.bzl.pyi");
    let source = BazelSource::new(&db, BazelRepository::new(&db, root.clone()), source_file);
    let module = checked(verify_bazel_source(&db, source))?;
    assert_eq!(module.problems().len(), 1);
    assert_eq!(
        module.problems()[0].range().start().to_usize(),
        runtime
            .find("keep(1, 2)")
            .ok_or(anyhow::anyhow!("bad arity"))?
    );
    assert!(matches!(
        module.export("GOOD").map(BazelVerifiedExport::kind),
        Some(BazelVerifiedExportKind::Scalar(BazelScalar::Int))
    ));
    assert_eq!(function(module, "public")?.result(), BazelScalar::Int);
    assert_eq!(function(module, "broken")?.stub_file(), None);
    assert!(function(module, "broken")?.body_may_fail());

    db.write_file(
        &stub_path,
        "def public() -> int: ...\ndef broken() -> int: ...\n",
    )?;
    File::sync_path(&mut db, &stub_path);
    let source = BazelSource::new(&db, BazelRepository::new(&db, root), source_file);
    let failure = opaque(verify_bazel_source(&db, source))?;
    assert!(matches!(
        failure.reason(),
        BazelVerificationError::UnsafeBody(name) if name == "broken"
    ));
    Ok(())
}

#[test]
fn recursive_assignment_cannot_prove_even_a_literal_return() -> anyhow::Result<()> {
    let (db, root) = test_db(&[
        ("MODULE.bazel", ""),
        ("pkg/BUILD", ""),
        (
            "pkg/defs.bzl",
            "def loop(value):\n    return loop(1)\ndef route(value):\n    ignored = loop(value)\n    return 1\n",
        ),
        ("pkg/defs.bzl.pyi", "def route(value: int) -> int: ...\n"),
    ])?;
    let source_file = system_path_to_file(&db, root.join("pkg/defs.bzl"))?;
    let source = BazelSource::new(&db, BazelRepository::new(&db, root), source_file);
    let failure = opaque(verify_bazel_source(&db, source))?;
    assert!(matches!(
        failure.reason(),
        BazelVerificationError::UnsafeBody(name) if name == "route"
    ));
    assert_eq!(failure.file(), Some(source_file));
    Ok(())
}

#[test]
fn scalar_analysis_failure_cannot_be_revived_by_present_stub() -> anyhow::Result<()> {
    let mut runtime = String::from("GOOD = 1\n");
    for index in 0..=128 {
        if index < 128 {
            write!(
                runtime,
                "def step_{index}():\n    return step_{}()\n",
                index + 1
            )?;
        } else {
            write!(runtime, "def step_{index}():\n    return 1\n")?;
        }
    }
    let (db, root) = test_db(&[
        ("MODULE.bazel", ""),
        ("pkg/BUILD", ""),
        ("pkg/defs.bzl", &runtime),
        ("pkg/defs.bzl.pyi", "def step_0() -> int: ...\n"),
    ])?;
    let source_file = system_path_to_file(&db, root.join("pkg/defs.bzl"))?;
    let source = BazelSource::new(&db, BazelRepository::new(&db, root), source_file);
    let failure = opaque(verify_bazel_source(&db, source))?;
    assert_eq!(failure.file(), Some(source_file));
    assert!(matches!(
        failure.reason(),
        BazelVerificationError::Source(source_failure)
            if matches!(source_failure.reason(), BazelPreflightError::AnalysisLimit)
    ));
    Ok(())
}

#[test]
fn typed_proof_exhaustion_never_falls_back_to_claimed_stub_results() -> anyhow::Result<()> {
    let mut runtime = String::from("GOOD = 1\n");
    let mut stub = String::new();
    for index in 0..=1024 {
        writeln!(runtime, "def f_{index}(value):\n    return value")?;
        writeln!(stub, "def f_{index}(value: int) -> int: ...")?;
    }
    let (db, root) = test_db(&[
        ("MODULE.bazel", ""),
        ("pkg/BUILD", ""),
        ("pkg/defs.bzl", &runtime),
        ("pkg/defs.bzl.pyi", &stub),
    ])?;
    let source_file = system_path_to_file(&db, root.join("pkg/defs.bzl"))?;
    let stub_file = system_path_to_file(&db, root.join("pkg/defs.bzl.pyi"))?;
    let source = BazelSource::new(&db, BazelRepository::new(&db, root), source_file);
    assert!(matches!(
        summarize_bazel_source(&db, source),
        BazelCheckedSource::Checked(_)
    ));
    let failure = opaque(verify_bazel_source(&db, source))?;
    assert!(matches!(
        failure.reason(),
        BazelVerificationError::AnalysisLimit
    ));
    assert_eq!(failure.file(), Some(source_file));
    assert!(failure.range().is_some());
    assert_eq!(failure.related_file(), Some(stub_file));
    Ok(())
}
