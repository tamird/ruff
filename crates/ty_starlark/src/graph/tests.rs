use ruff_db::diagnostic::{Diagnostic, DisplayDiagnosticConfig, DisplayDiagnostics};
use ruff_db::files::{File, system_path_to_file};
use ruff_db::system::{DbWithTestSystem as _, DbWithWritableSystem as _, SystemPathBuf};

use crate::bazel::BazelRepository;
use crate::source::BazelSource;
use crate::testing::{TestDb, test_db};

use super::check_bazel_graph;

fn graph_for(
    db: &TestDb,
    root: &SystemPathBuf,
    selections: &[&str],
) -> anyhow::Result<Vec<Diagnostic>> {
    let repository = BazelRepository::new(db, root.clone());
    let sources = selections
        .iter()
        .map(|name| {
            let file = system_path_to_file(db, root.join(name))?;
            Ok(BazelSource::new(db, repository, file))
        })
        .collect::<anyhow::Result<Vec<_>>>()?;
    Ok(check_bazel_graph(db, &sources)?)
}

fn rendered(db: &TestDb, diagnostics: &[Diagnostic]) -> String {
    DisplayDiagnostics::new(db, &DisplayDiagnosticConfig::new("sty"), diagnostics).to_string()
}

fn codes(diagnostics: &[Diagnostic]) -> Vec<String> {
    diagnostics
        .iter()
        .map(|diagnostic| diagnostic.id().to_string())
        .collect()
}

#[test]
fn companion_checks_original_bodies_and_loaded_calls() -> anyhow::Result<()> {
    let (db, root) = test_db(&[
        ("MODULE.bazel", ""),
        ("shared/BUILD", ""),
        ("consumer/BUILD", ""),
        (
            "shared/defs.bzl",
            "def identity(value):\n    return value\ndef wrong():\n    return False\n",
        ),
        (
            "shared/defs.bzl.pyi",
            "def identity(value: int) -> int: ...\ndef wrong() -> int: ...\n",
        ),
        (
            "consumer/entry.bzl",
            "load(\"//shared:defs.bzl\", helper=\"identity\")\ndef unused():\n    helper(1)\n    helper(\"wrong\")\n    helper(False)\n",
        ),
    ])?;
    let diagnostics = graph_for(&db, &root, &["consumer/entry.bzl"])?;
    assert_eq!(
        codes(&diagnostics),
        [
            "invalid-argument-type",
            "invalid-argument-type",
            "invalid-return-type"
        ]
    );
    let text = rendered(&db, &diagnostics);
    for fragment in [
        "consumer/entry.bzl",
        "shared/defs.bzl.pyi",
        "shared/defs.bzl",
        "Literal[\"wrong\"]",
        "Literal[False]",
    ] {
        assert!(text.contains(fragment), "missing {fragment}: {text}");
    }
    Ok(())
}

#[test]
fn imported_arity_retains_the_source_declaration() -> anyhow::Result<()> {
    let (db, root) = test_db(&[
        ("MODULE.bazel", ""),
        ("shared/BUILD", ""),
        ("consumer/BUILD", ""),
        ("shared/defs.bzl", "def keep(value):\n    return value\n"),
        (
            "consumer/entry.bzl",
            "load(\"//shared:defs.bzl\", picked=\"keep\")\ndef unused():\n    return picked(1, 2)\n",
        ),
    ])?;
    let diagnostics = graph_for(
        &db,
        &root,
        &[
            "consumer/entry.bzl",
            "shared/defs.bzl",
            "consumer/entry.bzl",
        ],
    )?;
    assert_eq!(codes(&diagnostics), ["too-many-positional-arguments"]);
    let text = rendered(&db, &diagnostics);
    assert!(
        text.contains("shared/defs.bzl") && text.contains("def keep(value)"),
        "{text}"
    );
    Ok(())
}

#[test]
fn missing_and_private_exports_cannot_be_loaded() -> anyhow::Result<()> {
    for (symbol, code) in [
        ("missing", "unresolved-import"),
        ("_private", "unsupported-starlark"),
    ] {
        let caller = format!("load(\"//shared:defs.bzl\", asked=\"{symbol}\")\n");
        let (db, root) = test_db(&[
            ("MODULE.bazel", ""),
            ("shared/BUILD", ""),
            ("consumer/BUILD", ""),
            ("shared/defs.bzl", "PUBLIC = 1\n_private = 1\n"),
            ("consumer/entry.bzl", &caller),
        ])?;
        let diagnostics = graph_for(&db, &root, &["consumer/entry.bzl"])?;
        assert_eq!(
            codes(&diagnostics),
            [code],
            "{}",
            rendered(&db, &diagnostics)
        );
    }
    Ok(())
}

#[test]
fn invalid_stub_blocks_importers_but_independent_modules_are_checked() -> anyhow::Result<()> {
    let (db, root) = test_db(&[
        ("MODULE.bazel", ""),
        ("shared/BUILD", ""),
        ("consumer/BUILD", ""),
        ("good/BUILD", ""),
        (
            "shared/defs.bzl",
            "def identity(value):\n    return value\n",
        ),
        (
            "shared/defs.bzl.pyi",
            "def identity(value: list[int]) -> int: ...\n",
        ),
        (
            "consumer/entry.bzl",
            "load(\"//shared:defs.bzl\", \"identity\")\nidentity(1)\n",
        ),
        (
            "good/defs.bzl",
            "def identity(value):\n    return value\nidentity(1, 2)\n",
        ),
    ])?;
    let diagnostics = graph_for(&db, &root, &["consumer/entry.bzl", "good/defs.bzl"])?;
    assert_eq!(
        codes(&diagnostics),
        [
            "too-many-positional-arguments",
            "unsupported-starlark",
            "unsupported-starlark"
        ]
    );
    let text = rendered(&db, &diagnostics);
    assert!(
        text.contains("shared/defs.bzl.pyi") && text.contains("loaded runtime target is opaque"),
        "{text}"
    );
    Ok(())
}

#[test]
fn cycles_are_distinct_from_their_importers() -> anyhow::Result<()> {
    let (db, root) = test_db(&[
        ("MODULE.bazel", ""),
        ("pkg/BUILD", ""),
        ("pkg/a.bzl", "load(\":b.bzl\", \"B\")\nA = 1\n"),
        ("pkg/b.bzl", "load(\":a.bzl\", \"A\")\nB = 1\n"),
        ("pkg/entry.bzl", "load(\":a.bzl\", \"A\")\n"),
        ("pkg/good.bzl", "missing_name\n"),
    ])?;
    let diagnostics = graph_for(&db, &root, &["pkg/entry.bzl", "pkg/good.bzl"])?;
    assert_eq!(
        diagnostics
            .iter()
            .filter(|d| d.headline_message().contains("contains a cycle"))
            .count(),
        2
    );
    assert_eq!(
        diagnostics
            .iter()
            .filter(|d| d
                .headline_message()
                .contains("loaded runtime target is opaque"))
            .count(),
        1
    );
    assert!(
        codes(&diagnostics).contains(&"unresolved-reference".to_string()),
        "{diagnostics:?}"
    );
    Ok(())
}

#[test]
fn ordinary_inference_leaves_unannotated_forwarding_unknown() -> anyhow::Result<()> {
    let (mut db, root) = test_db(&[
        ("MODULE.bazel", ""),
        ("pkg/BUILD", ""),
        ("pkg/helper.bzl", "def helper(value):\n    return value\n"),
        ("pkg/helper.bzl.pyi", "def helper(value: int) -> int: ...\n"),
        (
            "pkg/entry.bzl",
            "load(\":helper.bzl\", \"helper\")\ndef relay(value):\n    return helper(value)\nrelay(\"unknown\")\n",
        ),
    ])?;
    assert!(graph_for(&db, &root, &["pkg/entry.bzl"])?.is_empty());
    db.write_file(
        root.join("pkg/entry.bzl.pyi"),
        "def relay(value: int) -> int: ...\n",
    )?;
    let diagnostics = graph_for(&db, &root, &["pkg/entry.bzl"])?;
    assert_eq!(
        codes(&diagnostics),
        ["invalid-argument-type"],
        "{}",
        rendered(&db, &diagnostics)
    );
    Ok(())
}

#[test]
fn graph_revalidates_sources_stubs_packages_and_repositories() -> anyhow::Result<()> {
    let original = "def helper(value):\n    return value\n";
    let (mut db, root) = test_db(&[
        ("MODULE.bazel", ""),
        ("leaf/BUILD", ""),
        ("middle/BUILD", ""),
        ("root/BUILD", ""),
        ("leaf/defs.bzl", original),
        ("leaf/defs.bzl.pyi", "def helper(value: int) -> int: ...\n"),
        (
            "middle/defs.bzl",
            "load(\"//leaf:defs.bzl\", \"helper\")\nforward = helper\n",
        ),
        (
            "root/entry.bzl",
            "load(\"//middle:defs.bzl\", \"forward\")\nforward(1)\n",
        ),
    ])?;
    let check = |db: &TestDb| graph_for(db, &root, &["root/entry.bzl"]);
    assert!(check(&db)?.is_empty());
    db.write_file(
        root.join("leaf/defs.bzl"),
        "def helper(value):\n    return \"bad\"\n",
    )?;
    assert_eq!(codes(&check(&db)?), ["invalid-return-type"]);
    db.write_file(root.join("leaf/defs.bzl"), original)?;
    db.write_file(
        root.join("leaf/defs.bzl.pyi"),
        "def helper(value: str) -> str: ...\n",
    )?;
    assert_eq!(codes(&check(&db)?), ["invalid-argument-type"]);
    db.memory_file_system()
        .remove_file(root.join("leaf/defs.bzl.pyi"))?;
    File::sync_path(&mut db, &root.join("leaf/defs.bzl.pyi"));
    assert!(check(&db)?.is_empty());
    db.memory_file_system()
        .remove_file(root.join("leaf/BUILD"))?;
    File::sync_path(&mut db, &root.join("leaf/BUILD"));
    assert!(
        codes(&check(&db)?)
            .iter()
            .all(|code| code == "unsupported-starlark")
    );
    assert!(!check(&db)?.is_empty());
    db.write_file(root.join("leaf/BUILD"), "")?;
    assert!(check(&db)?.is_empty());
    db.write_file(root.join("leaf/MODULE.bazel"), "")?;
    assert!(!check(&db)?.is_empty());
    Ok(())
}

#[test]
fn semantic_diagnostics_own_the_checked_sources() -> anyhow::Result<()> {
    let (mut db, root) = test_db(&[
        ("MODULE.bazel", ""),
        ("pkg/BUILD", ""),
        (
            "pkg/defs.bzl",
            "def f(value):\n    return value\nf(\"original\")\n",
        ),
        ("pkg/defs.bzl.pyi", "def f(value: int) -> int: ...\n"),
    ])?;
    let diagnostics = graph_for(&db, &root, &["pkg/defs.bzl"])?;
    assert_eq!(codes(&diagnostics), ["invalid-argument-type"]);
    let before = rendered(&db, &diagnostics);
    db.write_file(root.join("pkg/defs.bzl"), "CHANGED = 1\n")?;
    db.write_file(root.join("pkg/defs.bzl.pyi"), "")?;
    assert_eq!(rendered(&db, &diagnostics), before);
    Ok(())
}

#[test]
fn bazel_builtin_contracts_preserve_host_signatures() -> anyhow::Result<()> {
    let (db, root) = test_db(&[
        ("MODULE.bazel", ""),
        ("pkg/BUILD", ""),
        (
            "pkg/defs.bzl",
            r#"
"a b".split(sep=" ")
" x ".strip(None)
sorted([1], None)
sorted([1], key=None)
{"x": 1}.get("y", default=0)
int("10", base=2)
int(1)
float(1)
list((1, 2))
dict([("x", 1)])
set([1, 2])
list(range(3))
len(range(3)[1:])
enumerate(list=[1], start=2)
zip([1], ["a"])
min([1, 2], key=None)
max(1, 2, 3)
reversed([1]).append(2)
abs(-1)
hash("key")
getattr(struct(), "missing", None)
hasattr(struct(), "missing")
dir(struct())
repr(1)
print("one", "two", sep=",")
def stop():
    fail("bad", sep=",", attr="name")
"#,
        ),
    ])?;
    let diagnostics = graph_for(&db, &root, &["pkg/defs.bzl"])?;
    assert!(diagnostics.is_empty(), "{}", rendered(&db, &diagnostics));
    Ok(())
}

#[test]
fn bazel_rejects_hosted_only_calls_and_type_operations() -> anyhow::Result<()> {
    for source in [
        "range()",
        "range(1, stop=3)",
        "hash(1)",
        "min([1], default=0)",
        "zip([1], strict=True)",
        "enumerate(\"abc\")",
        "len(1)",
        "int()",
        "int(1, 2)",
        "\"a b\".split()",
        "\"a b\".split(None)",
        "int | str",
        "int | int",
        "None | int",
        "ctor = int\nctor | int",
        "list[int]",
        "dict[str, int]",
        "def f(flag):\n    ctor = list if flag else dict\n    return ctor[int]",
        "isinstance(1, int)",
        "typing.Any",
    ] {
        let (db, root) = test_db(&[
            ("MODULE.bazel", ""),
            ("pkg/BUILD", ""),
            ("pkg/defs.bzl", source),
        ])?;
        let diagnostics = graph_for(&db, &root, &["pkg/defs.bzl"])?;
        assert!(!diagnostics.is_empty(), "accepted {source}");
        assert!(
            !codes(&diagnostics).contains(&"unsupported-starlark".to_string()),
            "must reach semantic analysis: {source}: {diagnostics:?}"
        );
    }
    Ok(())
}
