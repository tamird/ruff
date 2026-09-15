use ruff_db::files::system_path_to_file;
use ruff_db::system::DbWithWritableSystem as _;

use crate::bazel::BazelRepository;
use crate::checker::{
    BazelCheckedSource, BazelExport, BazelExportKind, BazelModuleSummary, BazelScalar,
    summarize_bazel_source, summarize_verified_imports,
};
use crate::overlay::{BazelVerifiedSource, verify_bazel_source};
use crate::preflight::{BazelPreflight, preflight_bazel_source, preflighted_import_suite};
use crate::source::BazelSource;
use crate::testing::test_db;

use super::{
    BazelResolvedBinding, BazelResolvedImportError, BazelResolvedImports, BazelResolvedValue,
    resolve_verified_imports,
};

fn resolved<'db>(
    db: &'db dyn ruff_db::Db,
    source: BazelSource<'db>,
) -> anyhow::Result<BazelResolvedImports<'db>> {
    match resolve_verified_imports(db, source) {
        Ok(imports) => Ok(imports),
        Err(failure) => anyhow::bail!("expected checked imports: {failure:?}"),
    }
}

fn checked(summary: &BazelCheckedSource) -> anyhow::Result<&BazelModuleSummary> {
    match summary {
        BazelCheckedSource::Checked(summary) => Ok(summary),
        BazelCheckedSource::Opaque(failure) => {
            anyhow::bail!("expected checked summary: {failure:?}")
        }
    }
}

#[test]
fn checked_imports_reuse_full_file_names_and_scalar_checker() -> anyhow::Result<()> {
    let importer = concat!(
        "load(\"//shared:defs.bzl\", \"PUBLIC\", helper=\"identity\")\n",
        "COPIED = PUBLIC\n",
        "def valid():\n    return helper(1)\n",
        "def wrong():\n    return helper(\"bad\")\n",
        "def generic(value):\n    return helper(value)\n",
        "def ignored(value):\n    unused = helper(value)\n    return 1\n",
        "def bad_ignored():\n    return ignored(\"bad\")\n",
    );
    let (db, root) = test_db(&[
        ("MODULE.bazel", ""),
        ("shared/BUILD.bazel", ""),
        (
            "shared/defs.bzl",
            "PUBLIC = 1\ndef identity(value):\n    return value\n",
        ),
        (
            "shared/defs.bzl.pyi",
            "def identity(value: int) -> int: ...\n",
        ),
        ("pkg/BUILD", ""),
        ("pkg/consumer.bzl", importer),
    ])?;
    let file = system_path_to_file(&db, root.join("pkg/consumer.bzl"))?;
    let stub = system_path_to_file(&db, root.join("shared/defs.bzl.pyi"))?;
    let source = BazelSource::new(&db, BazelRepository::new(&db, root), file);

    // Syntactically valid loads are never enough for the public source-only
    // route, even when their target exists and has a sibling stub.
    assert!(matches!(
        preflight_bazel_source(&db, source),
        BazelPreflight::Opaque(_)
    ));
    assert!(matches!(
        summarize_bazel_source(&db, source),
        BazelCheckedSource::Opaque(_)
    ));
    assert!(matches!(
        verify_bazel_source(&db, source),
        BazelVerifiedSource::Opaque(_)
    ));

    let imports = resolved(&db, source)?;
    let bindings: Vec<_> = imports.bindings().collect();
    assert_eq!(bindings.len(), 2);
    assert_eq!(bindings[0].local_name(), "PUBLIC");
    let BazelResolvedValue::Function(function) = bindings[1].value() else {
        anyhow::bail!("expected runtime-backed imported function");
    };
    assert_eq!(function.parameters()[0].scalar(), BazelScalar::Int);
    assert_eq!(function.parameters()[0].stub_file(), Some(stub));
    assert_eq!(function.result(), BazelScalar::Int);
    assert!(preflighted_import_suite(&db, source, &imports).is_ok());
    let summary = summarize_verified_imports(&db, source, &imports);
    let summary = checked(&summary)?;
    assert_eq!(summary.file(), file);
    assert!(summary.export("PUBLIC").is_none());
    assert!(summary.export("helper").is_none());
    assert!(matches!(
        summary.export("COPIED").map(BazelExport::kind),
        Some(BazelExportKind::Scalar(BazelScalar::Int))
    ));
    let scalar_result = |name: &str| match summary.export(name).map(BazelExport::kind) {
        Some(BazelExportKind::Function(function)) => {
            Ok((function.result(), function.body_may_fail()))
        }
        other => anyhow::bail!("expected source function {name}, found {other:?}"),
    };
    assert_eq!(scalar_result("valid")?, (BazelScalar::Int, false));
    // A wrong or unknown input cannot claim the imported stub's result. The
    // generic source-only summary does not call it a guaranteed runtime fault.
    assert_eq!(scalar_result("wrong")?, (BazelScalar::Unknown, false));
    assert_eq!(scalar_result("generic")?, (BazelScalar::Unknown, false));
    assert_eq!(scalar_result("ignored")?, (BazelScalar::Unknown, false));
    assert_eq!(scalar_result("bad_ignored")?, (BazelScalar::Unknown, false));
    assert!(summary.problems().is_empty());
    Ok(())
}

#[test]
fn target_source_and_sibling_stub_edits_rebuild_checked_imports() -> anyhow::Result<()> {
    let importer = "load(\"//shared:defs.bzl\", helper=\"identity\")\ndef caller():\n    return helper(\"text\")\n";
    let runtime = "def identity(value):\n    return value\n";
    let (mut db, root) = test_db(&[
        ("MODULE.bazel", ""),
        ("shared/BUILD", ""),
        ("shared/defs.bzl", runtime),
        (
            "shared/defs.bzl.pyi",
            "def identity(value: int) -> int: ...\n",
        ),
        ("pkg/BUILD", ""),
        ("pkg/importer.bzl", importer),
    ])?;
    let file = system_path_to_file(&db, root.join("pkg/importer.bzl"))?;
    let runtime_path = root.join("shared/defs.bzl");
    let stub_path = root.join("shared/defs.bzl.pyi");
    {
        let source = BazelSource::new(&db, BazelRepository::new(&db, root.clone()), file);
        let imports = resolved(&db, source)?;
        let Some(BazelResolvedValue::Function(function)) =
            imports.bindings().next().map(BazelResolvedBinding::value)
        else {
            anyhow::bail!("expected an imported function");
        };
        assert_eq!(function.parameters()[0].scalar(), BazelScalar::Int);
    }

    let bad_runtime = "def identity(value):\n    return \"str\"\n";
    db.write_file(&runtime_path, bad_runtime)?;
    {
        let source = BazelSource::new(&db, BazelRepository::new(&db, root.clone()), file);
        let Err(failure) = resolve_verified_imports(&db, source) else {
            anyhow::bail!("stale source proof granted checked imports");
        };
        assert_eq!(failure.file(), file);
        assert_eq!(
            failure.range().map(|range| range.start().to_usize()),
            importer.find("\"//shared")
        );
        assert_eq!(
            failure.related_file(),
            Some(system_path_to_file(&db, &runtime_path)?)
        );
        assert_eq!(
            failure
                .related_range()
                .map(|range| range.start().to_usize()),
            bad_runtime.find("\"str\"")
        );
        assert!(matches!(
            failure.reason(),
            BazelResolvedImportError::TargetOpaque(_)
        ));
    }

    db.write_file(&runtime_path, runtime)?;
    db.write_file(&stub_path, "def identity(value: str) -> str: ...\n")?;
    {
        let source = BazelSource::new(&db, BazelRepository::new(&db, root), file);
        let imports = resolved(&db, source)?;
        let Some(BazelResolvedValue::Function(function)) =
            imports.bindings().next().map(BazelResolvedBinding::value)
        else {
            anyhow::bail!("expected an imported function");
        };
        assert_eq!(function.parameters()[0].scalar(), BazelScalar::Str);
        assert_eq!(function.result(), BazelScalar::Str);
        let summary = summarize_verified_imports(&db, source, &imports);
        let summary = checked(&summary)?;
        let Some(BazelExportKind::Function(caller)) =
            summary.export("caller").map(BazelExport::kind)
        else {
            anyhow::bail!("expected checked caller");
        };
        assert_eq!(caller.result(), BazelScalar::Str);
    }
    Ok(())
}

#[test]
fn missing_source_export_and_opaque_target_never_bind_an_import() -> anyhow::Result<()> {
    for (target, symbol, expected) in [
        ("PUBLIC = 1\n", "absent", false),
        (
            "def broken():\n    return unknown\nPUBLIC = 1\n",
            "PUBLIC",
            true,
        ),
    ] {
        let importer = format!("load(\"//shared:defs.bzl\", \"{symbol}\")\nGOOD = 1\n");
        let (db, root) = test_db(&[
            ("MODULE.bazel", ""),
            ("shared/BUILD", ""),
            ("shared/defs.bzl", target),
            ("pkg/BUILD", ""),
            ("pkg/importer.bzl", &importer),
        ])?;
        let file = system_path_to_file(&db, root.join("pkg/importer.bzl"))?;
        let source = BazelSource::new(&db, BazelRepository::new(&db, root), file);
        let Err(failure) = resolve_verified_imports(&db, source) else {
            anyhow::bail!("missing or opaque target granted checked imports");
        };
        assert_eq!(failure.file(), file);
        let expected_range = if expected {
            importer.find("\"//shared")
        } else {
            importer.find(&format!("\"{symbol}\""))
        };
        assert_eq!(
            failure.range().map(|range| range.start().to_usize()),
            expected_range
        );
        match failure.reason() {
            BazelResolvedImportError::TargetOpaque(_) if expected => {}
            BazelResolvedImportError::MissingExport(name) if !expected => {
                assert_eq!(name, symbol);
            }
            other => anyhow::bail!("unexpected import failure: {other:?}"),
        }
    }
    Ok(())
}
