use ruff_db::files::system_path_to_file;
use ruff_db::system::DbWithWritableSystem as _;

use crate::bazel::BazelRepository;
use crate::source::{BazelAdmissionError, BazelSource};
use crate::testing::test_db;

use super::{BazelLoadPlan, BazelLoadPlanError, BazelLoadPlanFailure, plan_bazel_loads};

fn pending(plan: &BazelLoadPlan) -> anyhow::Result<&[super::BazelCandidateLoad]> {
    match plan {
        BazelLoadPlan::Pending(loads) => Ok(loads),
        other => anyhow::bail!("expected unresolved candidate loads, found {other:?}"),
    }
}

fn opaque(plan: &BazelLoadPlan) -> anyhow::Result<&BazelLoadPlanFailure> {
    match plan {
        BazelLoadPlan::Opaque(failure) => Ok(failure),
        other => anyhow::bail!("expected an opaque load plan, found {other:?}"),
    }
}

#[test]
fn leading_loads_retain_original_labels_and_ranges() -> anyhow::Result<()> {
    let code = concat!(
        "\"Module docs\"\n",
        "load(\"//shared:defs.bzl\", \"direct\", _alias=\"public\", another=\"public\")\n",
        "load(\":local.bzl\", extra=\"public\")\n",
        "def own():\n    return direct\n",
    );
    let (db, root) = test_db(&[
        ("MODULE.bazel", ""),
        ("pkg/BUILD", ""),
        ("pkg/importer.bzl", code),
    ])?;
    let file = system_path_to_file(&db, root.join("pkg/importer.bzl"))?;
    let source = BazelSource::new(&db, BazelRepository::new(&db, root), file);
    let loads = pending(plan_bazel_loads(&db, source))?;
    assert_eq!(loads.len(), 2);
    assert_eq!(loads[0].label(), "//shared:defs.bzl");
    assert_eq!(loads[1].label(), ":local.bzl");
    assert_eq!(
        Some(loads[0].label_range().start().to_usize()),
        code.find("\"//shared")
    );
    assert_eq!(
        Some(loads[0].range().start().to_usize()),
        code.find("load(")
    );
    Ok(())
}

#[test]
fn quoted_names_must_identify_public_bazel_9_symbols() -> anyhow::Result<()> {
    for (symbol, expected_private) in [
        ("_hidden", true),
        ("𝒞", false),
        ("café", false),
        ("has.dot", false),
        ("", false),
        ("if", false),
    ] {
        for aliased in [false, true] {
            let argument = if aliased {
                format!("alias=\"{symbol}\"")
            } else {
                format!("\"{symbol}\"")
            };
            let code = format!("load(\":defs.bzl\", {argument})\nGOOD = 1\n");
            let (db, root) = test_db(&[
                ("MODULE.bazel", ""),
                ("pkg/BUILD", ""),
                ("pkg/importer.bzl", &code),
            ])?;
            let file = system_path_to_file(&db, root.join("pkg/importer.bzl"))?;
            let source = BazelSource::new(&db, BazelRepository::new(&db, root), file);
            let failure = opaque(plan_bazel_loads(&db, source))?;
            match failure.reason() {
                BazelLoadPlanError::PrivateSourceSymbol(name) if expected_private => {
                    assert_eq!(name, symbol);
                }
                BazelLoadPlanError::InvalidSourceSymbol(name) if !expected_private => {
                    assert_eq!(name, symbol);
                }
                other => anyhow::bail!("{code}: unexpected load failure {other:?}"),
            }
            assert_eq!(failure.file(), file);
            assert_eq!(
                failure.range().map(|range| range.start().to_usize()),
                code.find(&format!("\"{symbol}\"")),
                "{code}"
            );
        }
    }
    Ok(())
}

#[test]
fn file_block_aliases_cannot_conflict_with_each_other_or_globals() -> anyhow::Result<()> {
    for (code, expected, expected_name, site) in [
        (
            "load(\":one.bzl\", \"key\", key=\"other\")\nGOOD = 1\n",
            "duplicate",
            "key",
            "key=",
        ),
        (
            "load(\":one.bzl\", \"key\")\nload(\":two.bzl\", key=\"other\")\nGOOD = 1\n",
            "duplicate",
            "key",
            "key=",
        ),
        (
            "load(\":one.bzl\", other=\"key\")\ndef other():\n    return 1\n",
            "collision",
            "other",
            "other=",
        ),
        (
            "load(\":one.bzl\", \"key\")\nkey = 2\n",
            "collision",
            "key",
            "\"key\"",
        ),
        (
            "load(\":one.bzl\", \"key\")\n(key, other) = (1, 2)\n",
            "collision",
            "key",
            "\"key\"",
        ),
    ] {
        let (db, root) = test_db(&[
            ("MODULE.bazel", ""),
            ("pkg/BUILD", ""),
            ("pkg/importer.bzl", code),
        ])?;
        let file = system_path_to_file(&db, root.join("pkg/importer.bzl"))?;
        let source = BazelSource::new(&db, BazelRepository::new(&db, root), file);
        let failure = opaque(plan_bazel_loads(&db, source))?;
        match failure.reason() {
            BazelLoadPlanError::DuplicateLocalName(name) if expected == "duplicate" => {
                assert_eq!(name, expected_name, "{code}");
            }
            BazelLoadPlanError::ModuleNameCollision(name) if expected == "collision" => {
                assert_eq!(name, expected_name, "{code}");
            }
            other => anyhow::bail!("{code}: expected {expected}, found {other:?}"),
        }
        assert_eq!(failure.file(), file);
        assert_eq!(
            failure.range().map(|range| range.start().to_usize()),
            code.find(site),
            "{code}"
        );
        if expected == "duplicate" {
            assert_eq!(
                failure
                    .related_range()
                    .map(|range| range.start().to_usize()),
                code.find("\"key\""),
                "{code}"
            );
        }
    }
    Ok(())
}

#[test]
fn missing_literals_late_loads_and_mixed_order_parser_limits_remain_opaque() -> anyhow::Result<()> {
    for (code, expected_python_parser) in [
        ("load(\":defs.bzl\")\nGOOD = 1\n", false),
        ("load(\":defs.bzl\", symbol)\nGOOD = 1\n", false),
        (
            "load(\":defs.bzl\", \"symbol\")\nGOOD = 1\nload(\":defs.bzl\", \"other\")\n",
            false,
        ),
        (
            "def public():\n    load(\":defs.bzl\", \"symbol\")\n    return 1\n",
            false,
        ),
        (
            "load(\":defs.bzl\", \"symbol\", alias=\"public\", \"other\")\n",
            true,
        ),
    ] {
        let (db, root) = test_db(&[
            ("MODULE.bazel", ""),
            ("pkg/BUILD", ""),
            ("pkg/importer.bzl", code),
        ])?;
        let file = system_path_to_file(&db, root.join("pkg/importer.bzl"))?;
        let source = BazelSource::new(&db, BazelRepository::new(&db, root), file);
        let failure = opaque(plan_bazel_loads(&db, source))?;
        match failure.reason() {
            BazelLoadPlanError::Admission(admission) => match admission.reason() {
                BazelAdmissionError::PythonParser(_) if expected_python_parser => {}
                BazelAdmissionError::BazelSyntax(_) if !expected_python_parser => {}
                other => anyhow::bail!("{code}: unexpected admission reason {other:?}"),
            },
            other => anyhow::bail!("{code}: unexpected plan reason {other:?}"),
        }
        assert_eq!(failure.file(), file);
        assert!(failure.range().is_some());
    }
    Ok(())
}

#[test]
fn source_edits_revalidate_unresolved_bindings_without_new_keys() -> anyhow::Result<()> {
    let (mut db, root) = test_db(&[
        ("MODULE.bazel", ""),
        ("pkg/BUILD", ""),
        ("pkg/importer.bzl", "GOOD = 1\n"),
    ])?;
    let file = system_path_to_file(&db, root.join("pkg/importer.bzl"))?;
    let source = BazelSource::new(&db, BazelRepository::new(&db, root.clone()), file);
    assert!(matches!(
        plan_bazel_loads(&db, source),
        BazelLoadPlan::NoLoads
    ));

    db.write_file(
        root.join("pkg/importer.bzl"),
        "load(\":defs.bzl\", \"good\")\nGOOD = 1\n",
    )?;
    let source = BazelSource::new(&db, BazelRepository::new(&db, root.clone()), file);
    assert_eq!(pending(plan_bazel_loads(&db, source))?.len(), 1);

    db.write_file(
        root.join("pkg/importer.bzl"),
        "load(\":defs.bzl\", \"good\", good=\"other\")\nGOOD = 1\n",
    )?;
    let source = BazelSource::new(&db, BazelRepository::new(&db, root.clone()), file);
    assert!(matches!(
        opaque(plan_bazel_loads(&db, source))?.reason(),
        BazelLoadPlanError::DuplicateLocalName(name) if name == "good"
    ));

    db.write_file(root.join("pkg/importer.bzl"), "GOOD = 1\n")?;
    let source = BazelSource::new(&db, BazelRepository::new(&db, root), file);
    assert!(matches!(
        plan_bazel_loads(&db, source),
        BazelLoadPlan::NoLoads
    ));
    Ok(())
}
