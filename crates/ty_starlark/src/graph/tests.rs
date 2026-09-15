use ruff_db::files::{File, system_path_to_file};
use ruff_db::system::SystemPathBuf;
use ruff_db::system::{DbWithTestSystem as _, DbWithWritableSystem as _};

use crate::bazel::BazelRepository;
use crate::checker::{BazelCheckError, BazelScalar};
use crate::overlay::{BazelVerificationError, BazelVerifiedExport, BazelVerifiedExportKind};
use crate::source::BazelSource;
use crate::testing::{TestDb, test_db};

use super::{
    BazelCheckedGraph, BazelGraphError, BazelGraphNode, BazelGraphOutcome, check_bazel_graph,
};

fn checked(
    graph: &BazelCheckedGraph,
    file: File,
) -> anyhow::Result<&crate::overlay::BazelVerifiedModule> {
    match graph.node(file).map(BazelGraphNode::outcome) {
        Some(BazelGraphOutcome::Checked(module)) => Ok(module),
        other => anyhow::bail!("expected checked runtime file {file:?}, found {other:?}"),
    }
}

fn opaque(graph: &BazelCheckedGraph, file: File) -> anyhow::Result<&super::BazelGraphFailure> {
    match graph.node(file).map(BazelGraphNode::outcome) {
        Some(BazelGraphOutcome::Opaque(failure)) => Ok(failure),
        other => anyhow::bail!("expected opaque runtime file {file:?}, found {other:?}"),
    }
}

fn graph_for(
    db: &TestDb,
    root: &SystemPathBuf,
    selections: &[&str],
) -> anyhow::Result<BazelCheckedGraph> {
    let repository = BazelRepository::new(db, root.clone());
    let sources: Vec<_> = selections
        .iter()
        .map(|name| {
            Ok(BazelSource::new(
                db,
                repository,
                system_path_to_file(db, root.join(name))?,
            ))
        })
        .collect::<anyhow::Result<_>>()?;
    check_bazel_graph(db, &sources)
        .map_err(|failure| anyhow::anyhow!("could not select one repository: {failure:?}"))
}

#[test]
fn checked_target_stub_reports_wrong_imported_call_in_unused_body() -> anyhow::Result<()> {
    let importer_text = concat!(
        "load(\"//shared:defs.bzl\", \"PUBLIC\", helper=\"identity\")\n",
        "GOOD = PUBLIC\n",
        "def sane():\n    return helper(1)\n",
        "def rogue():\n    ignored = helper(\"wrong\")\n    return 1\n",
        "def unknown(value):\n    return helper(value)\n",
    );
    let stub = "def identity(value: int) -> int: ...\n";
    let (db, root) = test_db(&[
        ("MODULE.bazel", ""),
        ("shared/BUILD.bazel", ""),
        (
            "shared/defs.bzl",
            "PUBLIC = 1\ndef identity(value):\n    return value\n",
        ),
        ("shared/defs.bzl.pyi", stub),
        ("consumer/BUILD", ""),
        ("consumer/entry.bzl", importer_text),
    ])?;
    let file = system_path_to_file(&db, root.join("consumer/entry.bzl"))?;
    let graph = graph_for(&db, &root, &["consumer/entry.bzl"])?;
    let importer = checked(&graph, file)?;
    assert_eq!(graph.selected(), &[file]);
    assert!(importer.export("PUBLIC").is_none());
    assert!(importer.export("helper").is_none());
    assert!(matches!(
        importer.export("GOOD").map(BazelVerifiedExport::kind),
        Some(BazelVerifiedExportKind::Scalar(BazelScalar::Int))
    ));
    for (name, expected) in [
        ("sane", BazelScalar::Int),
        ("rogue", BazelScalar::Unknown),
        ("unknown", BazelScalar::Unknown),
    ] {
        let Some(BazelVerifiedExportKind::Function(function)) =
            importer.export(name).map(BazelVerifiedExport::kind)
        else {
            anyhow::bail!("expected verified source function {name}");
        };
        assert_eq!(function.result(), expected);
    }
    let [problem] = importer.typed_problems() else {
        anyhow::bail!(
            "expected one definite incorrect imported call: {:?}",
            importer.typed_problems()
        );
    };
    let stub_file = system_path_to_file(&db, root.join("shared/defs.bzl.pyi"))?;
    assert_eq!(problem.file(), file);
    assert_eq!(problem.related_file(), stub_file);
    assert_eq!(
        Some(problem.range().start().to_usize()),
        importer_text.find("\"wrong\"")
    );
    assert_eq!(
        Some(problem.related_range().start().to_usize()),
        stub.find("int")
    );
    assert!(importer.problems().is_empty());
    Ok(())
}

#[test]
fn imported_runtime_arity_keeps_target_declaration_file() -> anyhow::Result<()> {
    let runtime = "def keep(value):\n    return 1\n";
    let caller = concat!(
        "load(\"//shared:defs.bzl\", picked=\"keep\")\n",
        "def unused():\n    return picked(1, 2)\n",
    );
    let (db, root) = test_db(&[
        ("MODULE.bazel", ""),
        ("shared/BUILD.bazel", ""),
        ("shared/defs.bzl", runtime),
        ("consumer/BUILD.bazel", ""),
        ("consumer/entry.bzl", caller),
    ])?;
    let file = system_path_to_file(&db, root.join("consumer/entry.bzl"))?;
    let target = system_path_to_file(&db, root.join("shared/defs.bzl"))?;
    let graph = graph_for(&db, &root, &["consumer/entry.bzl"])?;
    let importer = checked(&graph, file)?;
    assert!(importer.typed_problems().is_empty());
    let [problem] = importer.problems() else {
        anyhow::bail!(
            "expected one imported arity error: {:?}",
            importer.problems()
        );
    };
    assert_eq!(problem.file(), file);
    assert_eq!(problem.declaration_file(), target);
    assert_eq!(
        Some(problem.range().start().to_usize()),
        caller.find("picked(1, 2)")
    );
    assert_eq!(
        Some(problem.declaration_range().start().to_usize()),
        runtime.find("keep(value)")
    );
    assert!(matches!(
        problem.reason(),
        BazelCheckError::InvalidArity {
            minimum: 1,
            maximum: 1,
            actual: 2,
            ..
        }
    ));
    Ok(())
}

#[test]
fn checked_target_cannot_import_a_missing_or_private_runtime_binding() -> anyhow::Result<()> {
    for (source_name, expected) in [("missing", true), ("_private", false)] {
        let importer = format!("load(\"//shared:defs.bzl\", asked=\"{source_name}\")\nGOOD = 1\n");
        let (db, root) = test_db(&[
            ("MODULE.bazel", ""),
            ("shared/BUILD", ""),
            ("shared/defs.bzl", "PUBLIC = 1\n_private = 1\n"),
            ("consumer/BUILD", ""),
            ("consumer/defs.bzl", &importer),
        ])?;
        let file = system_path_to_file(&db, root.join("consumer/defs.bzl"))?;
        let graph = graph_for(&db, &root, &["consumer/defs.bzl"])?;
        let failure = opaque(&graph, file)?;
        assert_eq!(failure.file(), file);
        assert_eq!(
            failure.range().map(|range| range.start().to_usize()),
            importer.find(&format!("\"{source_name}\""))
        );
        if expected {
            assert!(matches!(failure.reason(), BazelGraphError::Import(_)));
        } else {
            assert!(matches!(failure.reason(), BazelGraphError::LoadPlan(_)));
        }
    }
    Ok(())
}

#[test]
fn opaque_target_stub_owns_primary_and_importer_related_span() -> anyhow::Result<()> {
    let stub = "def identity(value: int) -> int: ...\ndef broken(:\n";
    let caller = "load(\"//shared:defs.bzl\", identity=\"identity\")\nGOOD = 1\n";
    let (db, root) = test_db(&[
        ("MODULE.bazel", ""),
        ("shared/BUILD.bazel", ""),
        (
            "shared/defs.bzl",
            "def identity(value):\n    return value\n",
        ),
        ("shared/defs.bzl.pyi", stub),
        ("consumer/BUILD.bazel", ""),
        ("consumer/entry.bzl", caller),
        ("good/BUILD.bazel", ""),
        ("good/defs.bzl", "GOOD = 1\n"),
    ])?;
    let importer_file = system_path_to_file(&db, root.join("consumer/entry.bzl"))?;
    let runtime_file = system_path_to_file(&db, root.join("shared/defs.bzl"))?;
    let stub_file = system_path_to_file(&db, root.join("shared/defs.bzl.pyi"))?;
    let graph = graph_for(&db, &root, &["consumer/entry.bzl", "good/defs.bzl"])?;
    let target_failure = opaque(&graph, runtime_file)?;
    let importer_failure = opaque(&graph, importer_file)?;
    assert_eq!(
        graph.node(runtime_file).map(BazelGraphNode::file),
        Some(runtime_file)
    );
    assert_eq!(target_failure.file(), stub_file);
    let Some(range) = target_failure.range() else {
        anyhow::bail!("expected concrete malformed-stub span: {target_failure:?}");
    };
    assert!(Some(range.start().to_usize()) >= stub.find("def broken"));
    assert!(matches!(
        target_failure.reason(),
        BazelGraphError::Source(failure) if matches!(failure.reason(), BazelVerificationError::Stub(_))
    ));
    assert_eq!(importer_failure.file(), importer_file);
    assert_eq!(importer_failure.related_file(), Some(stub_file));
    assert_eq!(importer_failure.related_range(), Some(range));
    assert!(matches!(
        importer_failure.reason(),
        BazelGraphError::Dependency(file) if *file == runtime_file
    ));
    assert_eq!(
        importer_failure
            .range()
            .map(|range| range.start().to_usize()),
        caller.find("\"//shared")
    );
    let good = system_path_to_file(&db, root.join("good/defs.bzl"))?;
    assert!(checked(&graph, good)?.export("GOOD").is_some());
    Ok(())
}

#[test]
fn dependent_load_cycles_stay_opaque_but_independent_source_checks() -> anyhow::Result<()> {
    let (db, root) = test_db(&[
        ("MODULE.bazel", ""),
        ("a/BUILD", ""),
        (
            "a/defs.bzl",
            "load(\"//b:defs.bzl\", _from_b=\"public\")\ndef public():\n    return 1\n",
        ),
        ("b/BUILD", ""),
        (
            "b/defs.bzl",
            "load(\"//a:defs.bzl\", _from_a=\"public\")\ndef public():\n    return 2\n",
        ),
        ("dependent/BUILD", ""),
        (
            "dependent/defs.bzl",
            "load(\"//a:defs.bzl\", borrowed=\"public\")\ndef other():\n    return borrowed()\n",
        ),
        ("self/BUILD", ""),
        (
            "self/defs.bzl",
            "load(\":defs.bzl\", neighbor=\"public\")\ndef public():\n    return 1\n",
        ),
        ("good/BUILD", ""),
        ("good/defs.bzl", "GOOD = 1\n"),
    ])?;
    let graph = graph_for(
        &db,
        &root,
        &[
            "a/defs.bzl",
            "b/defs.bzl",
            "dependent/defs.bzl",
            "self/defs.bzl",
            "good/defs.bzl",
        ],
    )?;
    let a = system_path_to_file(&db, root.join("a/defs.bzl"))?;
    for name in ["a/defs.bzl", "b/defs.bzl", "self/defs.bzl"] {
        let file = system_path_to_file(&db, root.join(name))?;
        let failure = opaque(&graph, file)?;
        assert_eq!(failure.file(), file);
        assert!(failure.range().is_some());
        assert!(matches!(failure.reason(), BazelGraphError::Cycle));
    }
    let dependent = system_path_to_file(&db, root.join("dependent/defs.bzl"))?;
    let failure = opaque(&graph, dependent)?;
    assert_eq!(failure.related_file(), Some(a));
    assert!(matches!(failure.reason(), BazelGraphError::Dependency(file) if *file == a));
    let good = system_path_to_file(&db, root.join("good/defs.bzl"))?;
    assert!(checked(&graph, good)?.export("GOOD").is_some());
    Ok(())
}

#[test]
fn checked_three_package_chain_revalidates_source_stub_and_build() -> anyhow::Result<()> {
    let a_runtime = concat!(
        "load(\"//middle:defs.bzl\", bridge=\"bridge\")\n",
        "load(\"//core:defs.bzl\", helper=\"helper\")\n",
        "GOOD = 1\n",
        "def okay():\n    return bridge(1)\n",
        "def rogue():\n    ignored = bridge(\"wrong\")\n    return 1\n",
        "def direct():\n    return helper(1)\n",
    );
    let b_runtime = "load(\"//core:defs.bzl\", helper=\"helper\")\ndef bridge(value):\n    return helper(value)\n";
    let c_runtime = "def helper(value):\n    return value\n";
    let c_stub = "def helper(value: int) -> int: ...\n";
    let b_stub = "def bridge(value: int) -> int: ...\n";
    let (mut db, root) = test_db(&[
        ("MODULE.bazel", ""),
        ("core/BUILD.bazel", ""),
        ("core/defs.bzl", c_runtime),
        ("core/defs.bzl.pyi", c_stub),
        ("middle/BUILD", ""),
        ("middle/defs.bzl", b_runtime),
        ("middle/defs.bzl.pyi", b_stub),
        ("consumer/BUILD.bazel", ""),
        ("consumer/defs.bzl", a_runtime),
        ("good/BUILD", ""),
        ("good/defs.bzl", "UNCHANGED = 1\n"),
    ])?;
    let a = system_path_to_file(&db, root.join("consumer/defs.bzl"))?;
    let b = system_path_to_file(&db, root.join("middle/defs.bzl"))?;
    let c = system_path_to_file(&db, root.join("core/defs.bzl"))?;
    let b_stub_file = system_path_to_file(&db, root.join("middle/defs.bzl.pyi"))?;
    let good = system_path_to_file(&db, root.join("good/defs.bzl"))?;
    let select = &["consumer/defs.bzl", "good/defs.bzl"][..];
    let initial = graph_for(&db, &root, select)?;
    let importer = checked(&initial, a)?;
    assert!(checked(&initial, b)?.export("bridge").is_some());
    assert!(checked(&initial, c)?.export("helper").is_some());
    assert_eq!(initial.nodes().len(), 4);
    for (name, expected) in [
        ("okay", BazelScalar::Int),
        ("rogue", BazelScalar::Unknown),
        ("direct", BazelScalar::Int),
    ] {
        let Some(BazelVerifiedExportKind::Function(function)) =
            importer.export(name).map(BazelVerifiedExport::kind)
        else {
            anyhow::bail!("expected source-backed {name} function");
        };
        assert_eq!(function.result(), expected);
    }
    let [typed] = importer.typed_problems() else {
        anyhow::bail!(
            "expected one unused wrong call: {:?}",
            importer.typed_problems()
        );
    };
    assert_eq!(typed.file(), a);
    assert_eq!(typed.related_file(), b_stub_file);
    assert_eq!(
        Some(typed.range().start().to_usize()),
        a_runtime.find("\"wrong\"")
    );
    assert_eq!(
        Some(typed.related_range().start().to_usize()),
        b_stub.find("int")
    );
    assert!(checked(&initial, good)?.export("UNCHANGED").is_some());

    // An owned old graph value cannot authorize a claim after a current edit.
    db.write_file(
        root.join("core/defs.bzl"),
        "def helper(value):\n    return \"s\"\n",
    )?;
    let changed = graph_for(&db, &root, select)?;
    let c_failure = opaque(&changed, c)?;
    assert!(matches!(c_failure.reason(), BazelGraphError::Source(_)));
    assert!(
        matches!(opaque(&changed, b)?.reason(), BazelGraphError::Dependency(file) if *file == c)
    );
    assert!(
        matches!(opaque(&changed, a)?.reason(), BazelGraphError::Dependency(file) if *file == b || *file == c)
    );
    assert!(checked(&changed, good)?.export("UNCHANGED").is_some());
    assert!(initial.node(a).is_some());

    db.write_file(root.join("core/defs.bzl"), c_runtime)?;
    let core_stub_path = root.join("core/defs.bzl.pyi");
    db.write_file(&core_stub_path, "def helper(value: str) -> str: ...\n")?;
    let changed = graph_for(&db, &root, select)?;
    assert!(opaque(&changed, b)?.related_file().is_some());
    assert!(matches!(
        opaque(&changed, a)?.reason(),
        BazelGraphError::Dependency(_)
    ));

    db.write_file(&core_stub_path, c_stub)?;
    assert!(
        checked(&graph_for(&db, &root, select)?, a)?
            .export("GOOD")
            .is_some()
    );
    db.memory_file_system().remove_file(&core_stub_path)?;
    File::sync_path(&mut db, &core_stub_path);
    let without_stub = graph_for(&db, &root, select)?;
    assert!(checked(&without_stub, c)?.typed_problems().is_empty());
    assert!(matches!(
        opaque(&without_stub, b)?.reason(),
        BazelGraphError::Source(_)
    ));
    assert!(matches!(
        opaque(&without_stub, a)?.reason(),
        BazelGraphError::Dependency(_)
    ));

    db.write_file(&core_stub_path, c_stub)?;
    let build_path = root.join("core/BUILD.bazel");
    db.memory_file_system().remove_file(&build_path)?;
    File::sync_path(&mut db, &build_path);
    let no_build = graph_for(&db, &root, select)?;
    assert!(matches!(
        opaque(&no_build, b)?.reason(),
        BazelGraphError::Resolution(_)
    ));
    assert!(matches!(
        opaque(&no_build, a)?.reason(),
        BazelGraphError::Resolution(_) | BazelGraphError::Dependency(_)
    ));
    db.write_file(&build_path, "")?;
    assert!(
        checked(&graph_for(&db, &root, select)?, a)?
            .export("GOOD")
            .is_some()
    );
    let nested_marker = root.join("core/MODULE.bazel");
    db.write_file(&nested_marker, "")?;
    let nested = graph_for(&db, &root, select)?;
    assert!(matches!(
        opaque(&nested, b)?.reason(),
        BazelGraphError::Resolution(_)
    ));
    assert!(matches!(
        opaque(&nested, a)?.reason(),
        BazelGraphError::Resolution(_) | BazelGraphError::Dependency(_)
    ));
    db.memory_file_system().remove_file(&nested_marker)?;
    File::sync_path(&mut db, &nested_marker);
    assert!(
        checked(&graph_for(&db, &root, select)?, a)?
            .export("GOOD")
            .is_some()
    );
    Ok(())
}

#[test]
fn explicit_load_visibility_never_revives_a_target_from_stub() -> anyhow::Result<()> {
    for visibility in ["private", "public"] {
        let runtime =
            format!("visibility(\"{visibility}\")\ndef helper(value):\n    return value\n");
        let (db, root) = test_db(&[
            ("MODULE.bazel", ""),
            ("shared/BUILD", ""),
            ("shared/defs.bzl", &runtime),
            (
                "shared/defs.bzl.pyi",
                "def helper(value: int) -> int: ...\n",
            ),
            ("consumer/BUILD", ""),
            (
                "consumer/entry.bzl",
                "load(\"//shared:defs.bzl\", helper=\"helper\")\nGOOD = 1\n",
            ),
        ])?;
        let graph = graph_for(&db, &root, &["consumer/entry.bzl"])?;
        let target = system_path_to_file(&db, root.join("shared/defs.bzl"))?;
        let importer = system_path_to_file(&db, root.join("consumer/entry.bzl"))?;
        let source_failure = opaque(&graph, target)?;
        assert_eq!(source_failure.file(), target);
        assert!(matches!(
            source_failure.reason(),
            BazelGraphError::Source(_)
        ));
        assert!(
            matches!(opaque(&graph, importer)?.reason(), BazelGraphError::Dependency(file) if *file == target)
        );
    }
    Ok(())
}

#[test]
fn importer_stub_proof_requires_fresh_complete_runtime_source() -> anyhow::Result<()> {
    let runtime = concat!(
        "load(\"//shared:defs.bzl\", helper=\"identity\")\n",
        "def wrap(value):\n    return helper(value)\n",
        "def wrap_ignored(value):\n    ignored = helper(value)\n    return 1\n",
    );
    let (mut db, root) = test_db(&[
        ("MODULE.bazel", ""),
        ("shared/BUILD", ""),
        (
            "shared/defs.bzl",
            "def identity(value):\n    return value\n",
        ),
        (
            "shared/defs.bzl.pyi",
            "def identity(value: int) -> int: ...\n",
        ),
        ("consumer/BUILD", ""),
        ("consumer/entry.bzl", runtime),
        (
            "consumer/entry.bzl.pyi",
            "def wrap(value: int) -> int: ...\ndef wrap_ignored(value: int) -> int: ...\n",
        ),
    ])?;
    let importer = system_path_to_file(&db, root.join("consumer/entry.bzl"))?;
    let original = graph_for(&db, &root, &["consumer/entry.bzl"])?;
    let Some(BazelVerifiedExportKind::Function(wrap)) = checked(&original, importer)?
        .export("wrap")
        .map(BazelVerifiedExport::kind)
    else {
        anyhow::bail!("expected verified source-backed wrapper");
    };
    assert_eq!(wrap.result(), BazelScalar::Int);
    let Some(BazelVerifiedExportKind::Function(ignored)) = checked(&original, importer)?
        .export("wrap_ignored")
        .map(BazelVerifiedExport::kind)
    else {
        anyhow::bail!("expected proved wrapper after unused typed call");
    };
    assert_eq!(ignored.result(), BazelScalar::Int);

    let broken = format!("{runtime}def broken():\n    return unknown\n");
    db.write_file(root.join("consumer/entry.bzl"), &broken)?;
    let graph = graph_for(&db, &root, &["consumer/entry.bzl"])?;
    let failure = opaque(&graph, importer)?;
    assert_eq!(failure.file(), importer);
    assert_eq!(
        failure.range().map(|range| range.start().to_usize()),
        broken.find("unknown")
    );
    assert!(matches!(failure.reason(), BazelGraphError::Source(_)));
    assert!(original.node(importer).is_some());
    Ok(())
}
