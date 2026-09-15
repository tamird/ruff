use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

use tempfile::TempDir;

struct Fixture {
    root: TempDir,
}

impl Fixture {
    fn unmarked() -> anyhow::Result<Self> {
        Ok(Self {
            root: tempfile::tempdir()?,
        })
    }

    fn new() -> anyhow::Result<Self> {
        let fixture = Self::unmarked()?;
        fixture.write("MODULE.bazel", "")?;
        Ok(fixture)
    }

    fn path(&self, relative: &str) -> PathBuf {
        self.root.path().join(relative)
    }

    fn write(&self, relative: &str, contents: &str) -> anyhow::Result<()> {
        let path = self.path(relative);
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent)?;
        }
        fs::write(path, contents)?;
        Ok(())
    }

    fn run(cwd: &Path, args: &[&str]) -> anyhow::Result<Output> {
        Ok(Command::new(env!("CARGO_BIN_EXE_sty"))
            .current_dir(cwd)
            .args(args)
            .output()?)
    }
}

fn stderr(output: &Output) -> String {
    String::from_utf8_lossy(&output.stderr).into_owned()
}

fn utf8_path(path: &Path) -> anyhow::Result<&str> {
    path.to_str()
        .ok_or_else(|| anyhow::anyhow!("non-UTF8 fixture source path: {path:?}"))
}

fn star_graph_json(
    path: &Path,
    source: &str,
    loads: &[serde_json::Value],
    modules: &[serde_json::Value],
) -> anyhow::Result<String> {
    let path = utf8_path(path)?;
    let graph = serde_json::json!({
        "version": "sty-star-graph-v1",
        "profile": "example-star-host-v1",
        "root": {"path": path, "source": source, "loads": loads},
        "modules": modules,
        "special_forms": [
            {
                "name": "record", "kind": "builtin_record", "validator": "none",
                "field_types": "named_keyword_type_expressions"
            },
            {
                "name": "wrapper_record", "kind": "record_with_validator",
                "validator": "first_positional_callable",
                "field_types": "named_keyword_type_expressions"
            }
        ]
    });
    Ok(serde_json::to_string(&graph)?)
}

#[cfg(unix)]
fn host_fixture(fixture: &Fixture) -> anyhow::Result<PathBuf> {
    use std::os::unix::fs::PermissionsExt;

    fixture.write(
        "host-checker",
        concat!(
            "#!/bin/sh\n",
            "printf '%s\\n' \"$@\" >> \"$STY_TEST_ARGV_LOG\"\n",
            "printf 'manifest:%s\\n' \"$RUNFILES_MANIFEST_FILE\" >> \"$STY_TEST_ARGV_LOG\"\n",
            "if [ \"$1\" = '--sty-graph-v1' ]; then\n",
            "  if [ \"${STY_TEST_GRAPH_EXIT:-0}\" -ne 0 ]; then\n",
            "    printf 'graph producer failed\\n' >&2\n",
            "    exit \"$STY_TEST_GRAPH_EXIT\"\n",
            "  fi\n",
            "  cat \"$STY_TEST_GRAPH\"\n",
            "  exit 0\n",
            "fi\n",
            "printf 'host stdout\\n'\n",
            "printf 'host stderr\\n' >&2\n",
            "exit 37\n",
        ),
    )?;
    let checker = fixture.path("host-checker");
    let mut permissions = fs::metadata(&checker)?.permissions();
    permissions.set_mode(0o755);
    fs::set_permissions(&checker, permissions)?;
    Ok(checker)
}

#[test]
fn absolute_labels_need_only_a_marked_root_and_relative_labels_need_cwd_build() -> anyhow::Result<()>
{
    let fixture = Fixture::new()?;
    fixture.write("pkg/BUILD.bazel", "")?;
    fixture.write("pkg/defs.bzl", "GOOD = 1\n")?;
    fs::create_dir_all(fixture.path("pkg/sub"))?;
    let selected = Fixture::run(fixture.root.path(), &["check", "//pkg:defs.bzl"])?;
    assert!(selected.status.success(), "{}", stderr(&selected));
    let main = Fixture::run(fixture.root.path(), &["check", "@@//pkg:defs.bzl"])?;
    assert!(main.status.success(), "{}", stderr(&main));

    let relative = Fixture::run(&fixture.path("pkg"), &["check", ":defs.bzl"])?;
    assert!(relative.status.success(), "{}", stderr(&relative));
    let nested = Fixture::run(&fixture.path("pkg/sub"), &["check", ":defs.bzl"])?;
    assert_eq!(nested.status.code(), Some(2), "{}", stderr(&nested));
    assert!(stderr(&nested).contains("relative target directory has no BUILD"));
    let nested_absolute = Fixture::run(&fixture.path("pkg/sub"), &["check", "//pkg:defs.bzl"])?;
    assert!(
        nested_absolute.status.success(),
        "{}",
        stderr(&nested_absolute)
    );
    let no_label = Fixture::run(fixture.root.path(), &["check"])?;
    assert_eq!(no_label.status.code(), Some(2), "{}", stderr(&no_label));
    let external = Fixture::run(fixture.root.path(), &["check", "@other//pkg:defs.bzl"])?;
    assert_eq!(external.status.code(), Some(2), "{}", stderr(&external));
    assert!(stderr(&external).contains("external repository labels"));
    Ok(())
}

#[test]
fn nearest_nested_marker_or_explicit_workspace_owns_selected_targets() -> anyhow::Result<()> {
    let fixture = Fixture::new()?;
    fixture.write("outer/BUILD", "")?;
    fixture.write("outer/defs.bzl", "OUTER = 1\n")?;
    fixture.write("outer/inner/MODULE.bazel", "")?;
    fixture.write("outer/inner/BUILD.bazel", "")?;
    fixture.write("outer/inner/defs.bzl", "INNER = 1\n")?;
    let root = fixture
        .root
        .path()
        .to_str()
        .ok_or_else(|| anyhow::anyhow!("non-UTF8 test path"))?;

    let inner = Fixture::run(&fixture.path("outer/inner"), &["check", "//:defs.bzl"])?;
    assert!(inner.status.success(), "{}", stderr(&inner));
    let outer = Fixture::run(&fixture.path("outer"), &["check", "//outer:defs.bzl"])?;
    assert!(outer.status.success(), "{}", stderr(&outer));
    let outside = Fixture::run(
        &fixture.path("outer/inner"),
        &["check", "--workspace", root, "//outer/inner:defs.bzl"],
    )?;
    assert!(!outside.status.success());
    assert!(stderr(&outside).contains("another Bazel repository"));
    let explicit = Fixture::run(
        &fixture.path("outer/inner"),
        &["check", "--workspace", root, "//outer:defs.bzl"],
    )?;
    assert!(explicit.status.success(), "{}", stderr(&explicit));
    let relative_outside = Fixture::run(
        &fixture.path("outer/inner"),
        &["check", "--workspace", root, ":defs.bzl"],
    )?;
    assert!(!relative_outside.status.success());
    assert!(stderr(&relative_outside).contains("outside the selected Bazel repository"));
    Ok(())
}

#[test]
fn full_graph_errors_include_source_stub_and_distinct_actual_argument_kinds() -> anyhow::Result<()>
{
    let fixture = Fixture::new()?;
    fixture.write("shared/BUILD", "")?;
    fixture.write(
        "shared/defs.bzl",
        "def identity(value):\n    return value\n",
    )?;
    fixture.write(
        "shared/defs.bzl.pyi",
        "def identity(value: int) -> int: ...\n",
    )?;
    fixture.write("consumer/BUILD", "")?;
    fixture.write(
        "consumer/entry.bzl",
        concat!(
            "load(\"//shared:defs.bzl\", helper=\"identity\")\n",
            "GOOD = 1\n",
            "def relay(value):\n    return helper(value)\n",
            "def wrong_str():\n    return relay(\"wrong\")\n",
            "def wrong_bool():\n    return relay(False)\n",
        ),
    )?;
    fixture.write(
        "consumer/other.bzl",
        "load(\"//shared:defs.bzl\", picked=\"identity\")\ndef bad_arity():\n    return picked(1, 2)\n",
    )?;
    let output = Fixture::run(
        fixture.root.path(),
        &["check", "//consumer:entry.bzl", "//consumer:other.bzl"],
    )?;
    assert_eq!(output.status.code(), Some(1), "{}", stderr(&output));
    let errors = stderr(&output);
    assert!(
        errors.contains("consumer/entry.bzl:4:19: error: function 'helper' can receive str"),
        "{errors}"
    );
    assert!(
        errors.contains("consumer/entry.bzl:4:19: error: function 'helper' can receive bool"),
        "{errors}"
    );
    assert_eq!(errors.matches("can receive").count(), 2);
    assert!(errors.contains("declared at"));
    assert!(errors.contains("shared/defs.bzl.pyi:1:"), "{errors}");
    assert!(errors.contains("consumer/other.bzl:3:12:"), "{errors}");
    assert!(
        errors.contains("expects 1 positional argument, got 2"),
        "{errors}"
    );
    assert!(errors.contains("shared/defs.bzl:1:"), "{errors}");
    Ok(())
}

#[test]
fn parser_limit_and_duplicate_loads_fail_with_concrete_reason_and_related_span()
-> anyhow::Result<()> {
    let fixture = Fixture::new()?;
    fixture.write("pkg/BUILD.bazel", "")?;
    fixture.write("pkg/defs.bzl", "GOOD = 1\n")?;
    fixture.write(
        "pkg/limited.bzl",
        "load(\":defs.bzl\", \"GOOD\", alias=\"GOOD\", \"LATE\")\nALSO = 1\n",
    )?;
    let limited = Fixture::run(fixture.root.path(), &["check", "//pkg:limited.bzl"])?;
    assert_eq!(limited.status.code(), Some(1));
    let limited_error = stderr(&limited);
    assert!(
        limited_error.contains("shared Python parser cannot check"),
        "{limited_error}"
    );
    assert!(
        limited_error.contains("pkg/limited.bzl:1:"),
        "{limited_error}"
    );

    fixture.write(
        "pkg/duplicate.bzl",
        "load(\":defs.bzl\", \"GOOD\")\nload(\":defs.bzl\", \"GOOD\")\nCOPIED = GOOD\n",
    )?;
    let duplicate = Fixture::run(fixture.root.path(), &["check", "//pkg:duplicate.bzl"])?;
    assert_eq!(duplicate.status.code(), Some(1));
    let duplicate_error = stderr(&duplicate);
    assert!(
        duplicate_error.contains("load binds local name 'GOOD' more than once"),
        "{duplicate_error}"
    );
    assert!(
        duplicate_error.contains("pkg/duplicate.bzl:2:"),
        "{duplicate_error}"
    );
    assert!(
        duplicate_error.contains("first bound at"),
        "{duplicate_error}"
    );
    assert!(
        duplicate_error.contains("pkg/duplicate.bzl:1:"),
        "{duplicate_error}"
    );
    Ok(())
}

#[test]
fn host_usage_errors_before_bazel_repository_discovery() -> anyhow::Result<()> {
    let fixture = Fixture::unmarked()?;
    let missing = Fixture::run(fixture.root.path(), &["check", "deploy.star"])?;
    assert_eq!(missing.status.code(), Some(2), "{}", stderr(&missing));
    assert!(stderr(&missing).contains(".star files require --host-checker"));

    let double_slash_source = format!("/{}", fixture.path("deploy.star").display());
    let double_slash = Fixture::run(
        fixture.root.path(),
        &["check", double_slash_source.as_str()],
    )?;
    assert_eq!(double_slash.status.code(), Some(2));
    assert!(stderr(&double_slash).contains(".star files require --host-checker"));

    let extra_input = Fixture::run(
        fixture.root.path(),
        &["check", "--input", "catalog=missing.json", "//pkg:defs.bzl"],
    )?;
    assert_eq!(extra_input.status.code(), Some(2));
    assert!(stderr(&extra_input).contains("--input requires --host-checker"));

    let invalid_label = Fixture::run(
        fixture.root.path(),
        &[
            "check",
            "--host-checker",
            "missing",
            "@external//pkg:defs.bzl",
        ],
    )?;
    assert_eq!(invalid_label.status.code(), Some(2));
    assert!(stderr(&invalid_label).contains("not a Bazel label"));

    let main_repo_label = Fixture::run(
        fixture.root.path(),
        &["check", "--host-checker", "missing", "//pkg:defs.star"],
    )?;
    assert_eq!(main_repo_label.status.code(), Some(2));
    assert!(stderr(&main_repo_label).contains("not a Bazel label"));

    let two_sources = Fixture::run(
        fixture.root.path(),
        &["check", "--host-checker", "missing", "a.star", "b.star"],
    )?;
    assert_eq!(two_sources.status.code(), Some(2));
    assert!(stderr(&two_sources).contains("exactly one .star"));

    let malformed_input = Fixture::run(
        fixture.root.path(),
        &[
            "check",
            "--host-checker",
            "missing",
            "--input",
            "catalog",
            "a.star",
        ],
    )?;
    assert_eq!(malformed_input.status.code(), Some(2));
    assert!(stderr(&malformed_input).contains("NAME=PATH form"));

    let bad_executable = Fixture::run(
        fixture.root.path(),
        &["check", "--host-checker", "./missing-host", "a.star"],
    )?;
    assert_eq!(bad_executable.status.code(), Some(2));
    assert!(stderr(&bad_executable).contains("cannot start host graph producer"));
    Ok(())
}

#[cfg(unix)]
#[test]
fn host_child_receives_exact_argv_env_output_and_exit_code() -> anyhow::Result<()> {
    let fixture = Fixture::unmarked()?;
    fixture.write("@notes.star", "VALUE = 1\n")?;
    fixture.write("source/local module=west.star", "VALUE = 2\n")?;
    let checker = host_fixture(&fixture)?;
    let log = fixture.path("host-argv.txt");
    let graph_file = fixture.path("graph.json");
    let cwd = fixture.root.path().canonicalize()?;
    let source_path = cwd.join("@notes.star");
    let graph = star_graph_json(&source_path, "VALUE = 1\n", &[], &[])?;
    fixture.write("graph.json", &graph)?;
    let absolute_input = fixture.path("source/../source/local module=west.star");
    let named_input = format!("local={}", absolute_input.display());
    let missing_input = "unused=missing data=west.json";
    let output = Command::new(env!("CARGO_BIN_EXE_sty"))
        .current_dir(fixture.root.path())
        .env("STY_TEST_ARGV_LOG", &log)
        .env("STY_TEST_GRAPH", &graph_file)
        .env("RUNFILES_MANIFEST_FILE", "host-manifest.txt")
        .arg("check")
        .arg("--host-checker")
        .arg(&checker)
        .arg("--input")
        .arg(&named_input)
        .arg("--input")
        .arg(missing_input)
        .arg("@notes.star")
        .output()?;
    assert_eq!(output.status.code(), Some(37), "{}", stderr(&output));
    assert_eq!(output.stdout, b"host stdout\n");
    assert_eq!(output.stderr, b"host stderr\n");
    let arguments = format!(
        "--source\n{}\n--input\n{named_input}\n--input\nunused={}\nmanifest:host-manifest.txt\n",
        source_path.display(),
        cwd.join("missing data=west.json").display(),
    );
    assert_eq!(
        fs::read_to_string(log)?,
        format!("--sty-graph-v1\n{arguments}--sty-check-v1\n{arguments}")
    );

    let double_slash_source = format!("/{}", source_path.display());
    let double_log = fixture.path("double-slash-argv.txt");
    let double_graph_file = fixture.path("double-graph.json");
    let double_graph = star_graph_json(Path::new(&double_slash_source), "VALUE = 1\n", &[], &[])?;
    fixture.write("double-graph.json", &double_graph)?;
    let double = Command::new(env!("CARGO_BIN_EXE_sty"))
        .current_dir(fixture.root.path())
        .env("STY_TEST_ARGV_LOG", &double_log)
        .env("STY_TEST_GRAPH", &double_graph_file)
        .env("RUNFILES_MANIFEST_FILE", "host-manifest.txt")
        .arg("check")
        .arg("--host-checker")
        .arg(&checker)
        .arg(&double_slash_source)
        .output()?;
    assert_eq!(double.status.code(), Some(37), "{}", stderr(&double));
    assert_eq!(
        fs::read_to_string(double_log)?,
        format!(
            "--sty-graph-v1\n--source\n{double_slash_source}\nmanifest:host-manifest.txt\n--sty-check-v1\n--source\n{double_slash_source}\nmanifest:host-manifest.txt\n"
        )
    );
    Ok(())
}

#[cfg(unix)]
#[test]
fn host_graph_yields_a_sty_owned_dead_branch_error_from_captured_text() -> anyhow::Result<()> {
    let fixture = Fixture::unmarked()?;
    let checker = host_fixture(&fixture)?;
    let root_path = fixture.path("root.star");
    let module_path = fixture.path("limits.star");
    let root_source = "load(\"//example:limits.star\", \"LimitConfig\")\nif False:\n    LimitConfig(max_connections=\"wrong\")\n";
    let declaration = "def validate(value):\n    pass\nLimitConfig = wrapper_record(validate, max_connections=int)\n";
    // The host graph owns the analyzed snapshot. The physical file has a
    // different line structure so disk reads would misreport this error.
    fixture.write("root.star", "GOOD = 1\n")?;
    fixture.write("limits.star", declaration)?;
    let literal = "\"//example:limits.star\"";
    let offset = root_source
        .find(literal)
        .ok_or_else(|| anyhow::anyhow!("fixture load label missing"))?;
    let start = u32::try_from(offset)?;
    let literal_len = u32::try_from(literal.len())?;
    let end = start + literal_len;
    let module_name = utf8_path(&module_path)?;
    let graph = star_graph_json(
        &root_path,
        root_source,
        &[serde_json::json!({
            "module_id": "//example:limits.star", "start": start, "end": end,
            "symbols": [{"local": "LimitConfig", "source": "LimitConfig"}]
        })],
        &[serde_json::json!({
            "id": "//example:limits.star", "path": module_name,
            "source": declaration, "loads": []
        })],
    )?;
    fixture.write("graph.json", &graph)?;
    let log = fixture.path("host-argv.txt");
    let graph_file = fixture.path("graph.json");
    let checker_name = utf8_path(&checker)?;
    let root_name = utf8_path(&root_path)?;
    let args = ["check", "--host-checker", checker_name, root_name];
    let output = Command::new(env!("CARGO_BIN_EXE_sty"))
        .current_dir(fixture.root.path())
        .env("STY_TEST_ARGV_LOG", &log)
        .env("STY_TEST_GRAPH", &graph_file)
        .env_remove("RUNFILES_MANIFEST_FILE")
        .args(args)
        .output()?;
    assert_eq!(output.status.code(), Some(1), "{}", stderr(&output));
    assert!(output.stdout.is_empty(), "graph stdout leaked source JSON");
    let diagnostic = stderr(&output);
    assert!(diagnostic.contains("root.star:3:"), "{diagnostic}");
    assert!(
        diagnostic.contains("LimitConfig.max_connections, expected int, got str"),
        "{diagnostic}"
    );
    assert!(diagnostic.contains("limits.star:3:"), "{diagnostic}");
    assert_eq!(
        fs::read_to_string(&log)?,
        format!(
            "--sty-graph-v1\n--source\n{}\nmanifest:\n",
            root_path.display()
        )
    );

    let mut stale: serde_json::Value = serde_json::from_str(&graph)?;
    stale["root"]["loads"][0]["symbols"][0]["local"] = "stale".into();
    let stale_graph = serde_json::to_string(&stale)?;
    fixture.write("graph.json", &stale_graph)?;
    fs::write(&log, "")?;
    let invalid = Command::new(env!("CARGO_BIN_EXE_sty"))
        .current_dir(fixture.root.path())
        .env("STY_TEST_ARGV_LOG", &log)
        .env("STY_TEST_GRAPH", &graph_file)
        .env_remove("RUNFILES_MANIFEST_FILE")
        .args(args)
        .output()?;
    assert_eq!(invalid.status.code(), Some(2), "{}", stderr(&invalid));
    assert!(stderr(&invalid).contains("parsed Starlark load differs"));
    assert_eq!(
        fs::read_to_string(log)?.matches("--sty-check-v1").count(),
        0
    );
    Ok(())
}

#[cfg(unix)]
#[test]
fn malformed_host_graph_exits_two_and_producer_failure_relays_its_status() -> anyhow::Result<()> {
    let fixture = Fixture::unmarked()?;
    fixture.write("root.star", "VALUE = 1\n")?;
    fixture.write("graph.json", "{")?;
    let root_path = fixture.path("root.star");
    let checker = host_fixture(&fixture)?;
    let graph_file = fixture.path("graph.json");
    let log = fixture.path("host-argv.txt");
    let checker_name = utf8_path(&checker)?;
    let root_name = utf8_path(&root_path)?;
    let args = ["check", "--host-checker", checker_name, root_name];
    let malformed = Command::new(env!("CARGO_BIN_EXE_sty"))
        .current_dir(fixture.root.path())
        .env("STY_TEST_ARGV_LOG", &log)
        .env("STY_TEST_GRAPH", &graph_file)
        .env_remove("RUNFILES_MANIFEST_FILE")
        .args(args)
        .output()?;
    assert_eq!(malformed.status.code(), Some(2), "{}", stderr(&malformed));
    assert!(stderr(&malformed).contains("invalid versioned JSON"));
    assert!(
        malformed.stdout.is_empty(),
        "malformed JSON leaked to stdout"
    );
    assert_eq!(
        fs::read_to_string(&log)?.matches("--sty-check-v1").count(),
        0
    );

    fs::write(&log, "")?;
    let failed = Command::new(env!("CARGO_BIN_EXE_sty"))
        .current_dir(fixture.root.path())
        .env("STY_TEST_ARGV_LOG", &log)
        .env("STY_TEST_GRAPH", &graph_file)
        .env("STY_TEST_GRAPH_EXIT", "23")
        .env_remove("RUNFILES_MANIFEST_FILE")
        .args(args)
        .output()?;
    assert_eq!(failed.status.code(), Some(23), "{}", stderr(&failed));
    assert_eq!(failed.stderr, b"graph producer failed\n");
    assert_eq!(
        fs::read_to_string(log)?.matches("--sty-check-v1").count(),
        0
    );
    Ok(())
}
