use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

#[cfg(unix)]
use std::io::{BufRead, BufReader, Read, Write};
#[cfg(unix)]
use std::process::Stdio;
#[cfg(unix)]
use std::thread;
#[cfg(unix)]
use std::time::{Duration, Instant};

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

#[cfg(unix)]
#[test]
fn invalid_stdio_editor_config_responds_before_client_exit_and_then_exits() -> anyhow::Result<()> {
    let fixture = Fixture::unmarked()?;
    let mut child = Command::new(env!("CARGO_BIN_EXE_sty"))
        .arg("server")
        .current_dir(fixture.root.path())
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;
    let initialize = serde_json::json!({
        "jsonrpc":"2.0", "id":1, "method":"initialize", "params":{
            "capabilities":{}, "initializationOptions":{"hostSources":[{
                "root":"relative.star", "checker":"/absolute/host-producer"
            }]}
        }
    });
    let bytes = serde_json::to_vec(&initialize)?;
    child
        .stdin
        .as_mut()
        .unwrap()
        .write_all(format!("Content-Length: {}\r\n\r\n", bytes.len()).as_bytes())?;
    child.stdin.as_mut().unwrap().write_all(&bytes)?;
    child.stdin.as_mut().unwrap().flush()?;

    let stdout = child.stdout.take().unwrap();
    let (send, receive) = std::sync::mpsc::channel();
    let reader = thread::spawn(move || {
        let mut stdout = BufReader::new(stdout);
        let mut length = String::new();
        stdout.read_line(&mut length).unwrap();
        let size: usize = length
            .strip_prefix("Content-Length: ")
            .unwrap()
            .trim()
            .parse()
            .unwrap();
        let mut separator = String::new();
        stdout.read_line(&mut separator).unwrap();
        assert_eq!(separator, "\r\n");
        let mut body = vec![0; size];
        stdout.read_exact(&mut body).unwrap();
        send.send(serde_json::from_slice::<serde_json::Value>(&body).unwrap())
            .unwrap();
    });
    let response = match receive.recv_timeout(Duration::from_secs(3)) {
        Ok(response) => response,
        Err(error) => {
            child.kill()?;
            child.wait()?;
            panic!("Sty did not send an initialize error while stdin was open: {error}");
        }
    };
    reader.join().unwrap();
    assert_eq!(response["id"], 1);
    assert_eq!(response["error"]["code"], -32602);
    assert!(
        response["error"]["message"]
            .as_str()
            .unwrap()
            .contains("absolute UTF-8 path")
    );
    assert!(child.try_wait()?.is_none(), "Sty exited before client exit");

    let exit = serde_json::json!({"jsonrpc":"2.0", "method":"exit", "params":null});
    let bytes = serde_json::to_vec(&exit)?;
    child
        .stdin
        .as_mut()
        .unwrap()
        .write_all(format!("Content-Length: {}\r\n\r\n", bytes.len()).as_bytes())?;
    child.stdin.as_mut().unwrap().write_all(&bytes)?;
    child.stdin.as_mut().unwrap().flush()?;
    let deadline = Instant::now() + Duration::from_secs(3);
    loop {
        if let Some(status) = child.try_wait()? {
            assert!(status.success(), "{status}");
            break;
        }
        if Instant::now() > deadline {
            child.kill()?;
            child.wait()?;
            panic!("Sty did not exit after the client's exit notification");
        }
        thread::sleep(Duration::from_millis(20));
    }
    Ok(())
}

fn star_graph_json(
    path: &Path,
    source: &str,
    loads: &[serde_json::Value],
    modules: &[serde_json::Value],
) -> anyhow::Result<String> {
    let path = utf8_path(path)?;
    let graph = serde_json::json!({
        "version": "sty-star-graph-v3",
        "profile": "example-star-host-v3",
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
        ],
        "intrinsics": [
            {"name": "field", "kind": "field_first_type_optional_default"},
            {"name": "struct", "kind": "struct_named_members"}
        ],
        "host_functions": [
            {
                "name": "example_host_native",
                "params": [
                    {"name": "value", "mode": "pos_or_named", "required": true, "type": "str"}
                ],
                "returns": "str",
                "availability": "any_module"
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
            "if [ \"$1\" = '--sty-graph-v3' ]; then\n",
            "  if [ \"${STY_TEST_GRAPH_EXIT:-0}\" -ne 0 ]; then\n",
            "    printf 'graph producer failed\\n' >&2\n",
            "    exit \"$STY_TEST_GRAPH_EXIT\"\n",
            "  fi\n",
            "  cat \"$STY_TEST_GRAPH\"\n",
            "  exit 0\n",
            "fi\n",
            "printf 'unexpected host command\\n' >&2\n",
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
fn build_labels_check_the_active_package_source() -> anyhow::Result<()> {
    let fixture = Fixture::new()?;
    fixture.write("pkg/BUILD", "filegroup(name=\"old\")\n")?;
    fixture.write(
        "pkg/BUILD.bazel",
        "filegroup(name=\"active\", srcs=glob([\"*.bzl\"]))\n",
    )?;
    let selected = Fixture::run(fixture.root.path(), &["check", "//pkg:BUILD.bazel"])?;
    assert!(selected.status.success(), "{}", stderr(&selected));
    let inactive = Fixture::run(fixture.root.path(), &["check", "//pkg:BUILD"])?;
    assert_eq!(inactive.status.code(), Some(2));
    assert!(stderr(&inactive).contains("shadowed by BUILD.bazel"));

    fixture.write("pkg/BUILD.bazel", "filegroup(name=1)\n")?;
    let invalid = Fixture::run(&fixture.path("pkg"), &["check", ":BUILD.bazel"])?;
    assert_eq!(invalid.status.code(), Some(1), "{}", stderr(&invalid));
    assert!(stderr(&invalid).contains("invalid-argument-type"));
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
            "def wrong_str():\n    return helper(\"wrong\")\n",
            "def wrong_bool():\n    return helper(False)\n",
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
    insta::assert_snapshot!(stderr(&output));
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
    insta::assert_snapshot!("parser_limit", stderr(&limited));

    fixture.write(
        "pkg/duplicate.bzl",
        "load(\":defs.bzl\", \"GOOD\")\nload(\":defs.bzl\", \"GOOD\")\nCOPIED = GOOD\n",
    )?;
    let duplicate = Fixture::run(fixture.root.path(), &["check", "//pkg:duplicate.bzl"])?;
    assert_eq!(duplicate.status.code(), Some(1));
    insta::assert_snapshot!("duplicate_load", stderr(&duplicate));
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
fn host_graph_receives_exact_argv_env_and_source_path() -> anyhow::Result<()> {
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
    assert!(output.status.success(), "{}", stderr(&output));
    assert!(output.stdout.is_empty());
    assert!(output.stderr.is_empty());
    let arguments = format!(
        "--source\n{}\n--input\n{named_input}\n--input\nunused={}\nmanifest:host-manifest.txt\n",
        source_path.display(),
        cwd.join("missing data=west.json").display(),
    );
    assert_eq!(
        fs::read_to_string(log)?,
        format!("--sty-graph-v3\n{arguments}")
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
    assert!(double.status.success(), "{}", stderr(&double));
    assert_eq!(
        fs::read_to_string(double_log)?,
        format!("--sty-graph-v3\n--source\n{double_slash_source}\nmanifest:host-manifest.txt\n")
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
        diagnostic.contains("invalid-argument-type") && diagnostic.contains("max_connections"),
        "{diagnostic}"
    );
    assert!(diagnostic.contains("limits.star:3:"), "{diagnostic}");
    assert_eq!(
        fs::read_to_string(&log)?,
        format!(
            "--sty-graph-v3\n--source\n{}\nmanifest:\n",
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
        fs::read_to_string(log)?,
        format!("--sty-graph-v3\n--source\n{root_name}\nmanifest:\n")
    );
    Ok(())
}

#[cfg(unix)]
#[test]
fn host_v3_field_error_uses_the_captured_argument_and_type_spans() -> anyhow::Result<()> {
    let fixture = Fixture::unmarked()?;
    let checker = host_fixture(&fixture)?;
    let path = fixture.path("root.star");
    let source = "Config = record(value=field(int, default=7))\nConfig(value=\"bad\")\n";
    fixture.write("root.star", "GOOD = 1\n")?;
    let graph = star_graph_json(&path, source, &[], &[])?;
    fixture.write("graph.json", &graph)?;
    let graph_file = fixture.path("graph.json");
    let log = fixture.path("host-argv.txt");
    let checker_name = utf8_path(&checker)?;
    let root_name = utf8_path(&path)?;
    let output = Command::new(env!("CARGO_BIN_EXE_sty"))
        .current_dir(fixture.root.path())
        .env("STY_TEST_ARGV_LOG", &log)
        .env("STY_TEST_GRAPH", &graph_file)
        .env_remove("RUNFILES_MANIFEST_FILE")
        .args(["check", "--host-checker", checker_name, root_name])
        .output()?;
    assert_eq!(output.status.code(), Some(1), "{}", stderr(&output));
    assert!(output.stdout.is_empty(), "source JSON leaked");
    insta::assert_snapshot!(stderr(&output).replace(utf8_path(fixture.root.path())?, "[ROOT]"));
    assert_eq!(
        fs::read_to_string(&log)?,
        format!("--sty-graph-v3\n--source\n{}\nmanifest:\n", path.display())
    );
    Ok(())
}

#[cfg(unix)]
#[test]
fn host_v3_struct_member_error_keeps_loaded_source_locations() -> anyhow::Result<()> {
    let fixture = Fixture::unmarked()?;
    let checker = host_fixture(&fixture)?;
    let root_path = fixture.path("root.star");
    let module_path = fixture.path("images.star");
    let module_id = "//example:images.star";
    let label = format!("\"{module_id}\"");
    let root_source = format!("load({label}, \"images\")\nimages.repository(name=7)\n");
    let module_source = "Repository = record(name=str)\nimages = struct(repository=Repository)\n";
    fixture.write("root.star", "GOOD = 1\n")?;
    fixture.write("images.star", module_source)?;
    let start = root_source
        .find(&label)
        .ok_or_else(|| anyhow::anyhow!("struct test lacks a load label"))?;
    let start = u32::try_from(start)?;
    let end = start + u32::try_from(label.len())?;
    let module_name = utf8_path(&module_path)?;
    let graph = star_graph_json(
        &root_path,
        &root_source,
        &[serde_json::json!({
            "module_id": module_id, "start": start, "end": end,
            "symbols": [{"local": "images", "source": "images"}]
        })],
        &[serde_json::json!({
            "id": module_id, "path": module_name,
            "source": module_source, "loads": []
        })],
    )?;
    fixture.write("graph.json", &graph)?;
    let graph_file = fixture.path("graph.json");
    let log = fixture.path("host-argv.txt");
    let checker_name = utf8_path(&checker)?;
    let root_name = utf8_path(&root_path)?;
    let output = Command::new(env!("CARGO_BIN_EXE_sty"))
        .current_dir(fixture.root.path())
        .env("STY_TEST_ARGV_LOG", &log)
        .env("STY_TEST_GRAPH", &graph_file)
        .env_remove("RUNFILES_MANIFEST_FILE")
        .args(["check", "--host-checker", checker_name, root_name])
        .output()?;
    assert_eq!(output.status.code(), Some(1), "{}", stderr(&output));
    assert!(output.stdout.is_empty(), "source JSON leaked");
    insta::assert_snapshot!(stderr(&output).replace(utf8_path(fixture.root.path())?, "[ROOT]"));
    assert_eq!(
        fs::read_to_string(&log)?,
        format!(
            "--sty-graph-v3\n--source\n{}\nmanifest:\n",
            root_path.display()
        )
    );
    Ok(())
}

#[cfg(unix)]
#[test]
fn host_v3_source_function_error_names_its_parameter_annotation() -> anyhow::Result<()> {
    let fixture = Fixture::unmarked()?;
    let checker = host_fixture(&fixture)?;
    let path = fixture.path("root.star");
    let source = "def choose(multiarch: bool):\n    pass\nchoose(multiarch=\"wrong\")\n";
    fixture.write("root.star", "GOOD = 1\n")?;
    fixture.write("graph.json", &star_graph_json(&path, source, &[], &[])?)?;
    let log = fixture.path("host-argv.txt");
    let checker_name = utf8_path(&checker)?;
    let root_name = utf8_path(&path)?;
    let output = Command::new(env!("CARGO_BIN_EXE_sty"))
        .current_dir(fixture.root.path())
        .env("STY_TEST_ARGV_LOG", &log)
        .env("STY_TEST_GRAPH", fixture.path("graph.json"))
        .env_remove("RUNFILES_MANIFEST_FILE")
        .args(["check", "--host-checker", checker_name, root_name])
        .output()?;
    assert_eq!(output.status.code(), Some(1), "{}", stderr(&output));
    assert!(output.stdout.is_empty(), "source JSON leaked");
    insta::assert_snapshot!(stderr(&output).replace(utf8_path(fixture.root.path())?, "[ROOT]"));
    assert_eq!(
        fs::read_to_string(&log)?,
        format!("--sty-graph-v3\n--source\n{}\nmanifest:\n", path.display())
    );
    Ok(())
}

#[cfg(unix)]
#[test]
fn host_v3_native_error_uses_captured_argument_and_attested_signature() -> anyhow::Result<()> {
    let fixture = Fixture::unmarked()?;
    let checker = host_fixture(&fixture)?;
    let path = fixture.path("root.star");
    let source = "if False:\n    example_host_native(value=7)\n";
    fixture.write("root.star", "GOOD = 1\n")?;
    fixture.write("graph.json", &star_graph_json(&path, source, &[], &[])?)?;
    let log = fixture.path("host-argv.txt");
    let checker_name = utf8_path(&checker)?;
    let root_name = utf8_path(&path)?;
    let output = Command::new(env!("CARGO_BIN_EXE_sty"))
        .current_dir(fixture.root.path())
        .env("STY_TEST_ARGV_LOG", &log)
        .env("STY_TEST_GRAPH", fixture.path("graph.json"))
        .env_remove("RUNFILES_MANIFEST_FILE")
        .args(["check", "--host-checker", checker_name, root_name])
        .output()?;
    assert_eq!(output.status.code(), Some(1), "{}", stderr(&output));
    assert!(output.stdout.is_empty(), "source JSON leaked");
    insta::assert_snapshot!(stderr(&output).replace(utf8_path(fixture.root.path())?, "[ROOT]"));
    assert_eq!(
        fs::read_to_string(&log)?,
        format!("--sty-graph-v3\n--source\n{}\nmanifest:\n", path.display())
    );
    Ok(())
}

#[cfg(unix)]
#[test]
fn host_v3_root_only_availability_uses_captured_call_and_attested_fact() -> anyhow::Result<()> {
    let fixture = Fixture::unmarked()?;
    let checker = host_fixture(&fixture)?;
    let path = fixture.path("root.star");
    let source = "if False:\n    example_host_native(value=\"ready\")\n";
    fixture.write("root.star", "GOOD = 1\n")?;
    let mut graph: serde_json::Value =
        serde_json::from_str(&star_graph_json(&path, source, &[], &[])?)?;
    graph["host_functions"][0]["availability"] = "loaded_module_initialization".into();
    fixture.write("graph.json", &serde_json::to_string(&graph)?)?;
    let log = fixture.path("host-argv.txt");
    let output = Command::new(env!("CARGO_BIN_EXE_sty"))
        .current_dir(fixture.root.path())
        .env("STY_TEST_ARGV_LOG", &log)
        .env("STY_TEST_GRAPH", fixture.path("graph.json"))
        .env_remove("RUNFILES_MANIFEST_FILE")
        .args([
            "check",
            "--host-checker",
            utf8_path(&checker)?,
            utf8_path(&path)?,
        ])
        .output()?;
    assert_eq!(output.status.code(), Some(1), "{}", stderr(&output));
    assert!(output.stdout.is_empty(), "source JSON leaked");
    insta::assert_snapshot!(stderr(&output).replace(utf8_path(fixture.root.path())?, "[ROOT]"));
    assert_eq!(
        fs::read_to_string(&log)?,
        format!("--sty-graph-v3\n--source\n{}\nmanifest:\n", path.display())
    );
    Ok(())
}

#[cfg(unix)]
#[test]
fn host_v3_native_shape_errors_use_call_and_argument_source_spans() -> anyhow::Result<()> {
    let fixture = Fixture::unmarked()?;
    let checker = host_fixture(&fixture)?;
    let path = fixture.path("root.star");
    let source = "if False:\n    example_host_native()\n    example_host_native(1, 7)\n";
    fixture.write("root.star", "GOOD = 1\n")?;
    let mut graph: serde_json::Value =
        serde_json::from_str(&star_graph_json(&path, source, &[], &[])?)?;
    graph["host_functions"][0]["params"] = serde_json::json!([
        {"name":"value", "mode":"pos_or_named", "required":true, "type":"any"},
        {"name":"sort_keys", "mode":"named_only", "required":false, "type":"bool"}
    ]);
    fixture.write("graph.json", &serde_json::to_string(&graph)?)?;
    let log = fixture.path("host-argv.txt");
    let checker_name = utf8_path(&checker)?;
    let root_name = utf8_path(&path)?;
    let output = Command::new(env!("CARGO_BIN_EXE_sty"))
        .current_dir(fixture.root.path())
        .env("STY_TEST_ARGV_LOG", &log)
        .env("STY_TEST_GRAPH", fixture.path("graph.json"))
        .env_remove("RUNFILES_MANIFEST_FILE")
        .args(["check", "--host-checker", checker_name, root_name])
        .output()?;
    assert_eq!(output.status.code(), Some(1), "{}", stderr(&output));
    assert!(output.stdout.is_empty(), "source JSON leaked");
    insta::assert_snapshot!(stderr(&output).replace(utf8_path(fixture.root.path())?, "[ROOT]"));
    assert_eq!(
        fs::read_to_string(&log)?,
        format!("--sty-graph-v3\n--source\n{}\nmanifest:\n", path.display())
    );
    Ok(())
}

#[cfg(unix)]
#[test]
fn host_v3_dead_function_default_reports_eager_native_call_span() -> anyhow::Result<()> {
    let fixture = Fixture::unmarked()?;
    let checker = host_fixture(&fixture)?;
    let path = fixture.path("root.star");
    let source = concat!(
        "if False:\n",
        "    def unused(value=example_host_native(7)):\n",
        "        pass\n",
    );
    fixture.write("root.star", "GOOD = 1\n")?;
    fixture.write("graph.json", &star_graph_json(&path, source, &[], &[])?)?;
    let log = fixture.path("host-argv.txt");
    let output = Command::new(env!("CARGO_BIN_EXE_sty"))
        .current_dir(fixture.root.path())
        .env("STY_TEST_ARGV_LOG", &log)
        .env("STY_TEST_GRAPH", fixture.path("graph.json"))
        .env_remove("RUNFILES_MANIFEST_FILE")
        .args([
            "check",
            "--host-checker",
            utf8_path(&checker)?,
            utf8_path(&path)?,
        ])
        .output()?;
    assert_eq!(output.status.code(), Some(1), "{}", stderr(&output));
    assert!(output.stdout.is_empty(), "source JSON leaked");
    insta::assert_snapshot!(stderr(&output).replace(utf8_path(fixture.root.path())?, "[ROOT]"));
    assert_eq!(
        fs::read_to_string(&log)?,
        format!("--sty-graph-v3\n--source\n{}\nmanifest:\n", path.display())
    );
    Ok(())
}

#[cfg(unix)]
#[test]
fn host_v3_deferred_call_keeps_the_captured_root_and_loaded_annotation_spans() -> anyhow::Result<()>
{
    let fixture = Fixture::unmarked()?;
    let checker = host_fixture(&fixture)?;
    let root_path = fixture.path("root.star");
    let module_path = fixture.path("api.star");
    let module_id = "//example:api.star";
    let label = format!("\"{module_id}\"");
    let root_source =
        format!("load({label}, \"api\")\ndef check():\n    api.submit(flag=\"wrong\")\n");
    let module_source = "Api = record(flag=bool)\napi = struct(submit=Api)\n";
    fixture.write("root.star", "GOOD = 1\n")?;
    fixture.write("api.star", module_source)?;
    let start = root_source
        .find(&label)
        .ok_or_else(|| anyhow::anyhow!("deferred test lacks load label"))?;
    let start = u32::try_from(start)?;
    let end = start + u32::try_from(label.len())?;
    let graph = star_graph_json(
        &root_path,
        &root_source,
        &[serde_json::json!({
            "module_id": module_id, "start": start, "end": end,
            "symbols": [{"local": "api", "source": "api"}]
        })],
        &[serde_json::json!({
            "id": module_id, "path": utf8_path(&module_path)?,
            "source": module_source, "loads": []
        })],
    )?;
    fixture.write("graph.json", &graph)?;
    let log = fixture.path("host-argv.txt");
    let output = Command::new(env!("CARGO_BIN_EXE_sty"))
        .current_dir(fixture.root.path())
        .env("STY_TEST_ARGV_LOG", &log)
        .env("STY_TEST_GRAPH", fixture.path("graph.json"))
        .env_remove("RUNFILES_MANIFEST_FILE")
        .args([
            "check",
            "--host-checker",
            utf8_path(&checker)?,
            utf8_path(&root_path)?,
        ])
        .output()?;
    assert_eq!(output.status.code(), Some(1), "{}", stderr(&output));
    assert!(output.stdout.is_empty(), "source JSON leaked");
    insta::assert_snapshot!(stderr(&output).replace(utf8_path(fixture.root.path())?, "[ROOT]"));
    assert_eq!(
        fs::read_to_string(&log)?,
        format!(
            "--sty-graph-v3\n--source\n{}\nmanifest:\n",
            root_path.display()
        )
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
        fs::read_to_string(log)?,
        format!("--sty-graph-v3\n--source\n{root_name}\nmanifest:\n")
    );
    Ok(())
}

#[cfg(unix)]
#[test]
fn host_v3_intrinsics_must_be_present_and_supported() -> anyhow::Result<()> {
    let fixture = Fixture::unmarked()?;
    fixture.write("root.star", "VALUE = 1\n")?;
    let root_path = fixture.path("root.star");
    let graph_file = fixture.path("graph.json");
    let log = fixture.path("host-argv.txt");
    let checker = host_fixture(&fixture)?;
    let checker_name = utf8_path(&checker)?;
    let root_name = utf8_path(&root_path)?;
    let graph = star_graph_json(&root_path, "VALUE = 1\n", &[], &[])?;
    let original: serde_json::Value = serde_json::from_str(&graph)?;
    for drift in [
        "missing intrinsics",
        "wrong intrinsic behavior",
        "duplicate intrinsic",
        "unknown intrinsic entry",
        "wrong graph version",
        "v2 graph downgrade",
    ] {
        let mut changed = original.clone();
        match drift {
            "missing intrinsics" => {
                let object = changed
                    .as_object_mut()
                    .ok_or_else(|| anyhow::anyhow!("graph fixture is not an object"))?;
                object.remove("intrinsics");
            }
            "wrong intrinsic behavior" => {
                changed["intrinsics"][0]["kind"] = "unknown_field_behavior".into();
            }
            "duplicate intrinsic" => {
                changed["intrinsics"][1]["name"] = "field".into();
            }
            "unknown intrinsic entry" => {
                changed["intrinsics"][0]["parameters"] = "unknown".into();
            }
            "wrong graph version" => {
                changed["version"] = "sty-star-graph-v1".into();
            }
            "v2 graph downgrade" => {
                changed["version"] = "sty-star-graph-v2".into();
            }
            _ => anyhow::bail!("unknown fixture drift {drift}"),
        }
        fixture.write("graph.json", &serde_json::to_string(&changed)?)?;
        fs::write(&log, "")?;
        let output = Command::new(env!("CARGO_BIN_EXE_sty"))
            .current_dir(fixture.root.path())
            .env("STY_TEST_ARGV_LOG", &log)
            .env("STY_TEST_GRAPH", &graph_file)
            .args(["check", "--host-checker", checker_name, root_name])
            .output()?;
        assert_eq!(
            output.status.code(),
            Some(2),
            "{drift}: {}",
            stderr(&output)
        );
        assert!(output.stdout.is_empty(), "{drift}: source JSON leaked");
    }
    Ok(())
}

#[cfg(unix)]
#[test]
fn host_v3_inventory_requires_present_and_valid_native_signature_facts() -> anyhow::Result<()> {
    let fixture = Fixture::unmarked()?;
    fixture.write("root.star", "VALUE = 1\n")?;
    let root_path = fixture.path("root.star");
    let graph_file = fixture.path("graph.json");
    let log = fixture.path("host-argv.txt");
    let checker = host_fixture(&fixture)?;
    let checker_name = utf8_path(&checker)?;
    let root_name = utf8_path(&root_path)?;
    let graph = star_graph_json(&root_path, "VALUE = 1\n", &[], &[])?;
    let original: serde_json::Value = serde_json::from_str(&graph)?;

    let mut empty = original.clone();
    empty["host_functions"] = serde_json::json!([]);
    fixture.write("graph.json", &serde_json::to_string(&empty)?)?;
    let clear = Command::new(env!("CARGO_BIN_EXE_sty"))
        .current_dir(fixture.root.path())
        .env("STY_TEST_ARGV_LOG", &log)
        .env("STY_TEST_GRAPH", &graph_file)
        .args(["check", "--host-checker", checker_name, root_name])
        .output()?;
    assert!(clear.status.success(), "{}", stderr(&clear));
    assert_eq!(
        fs::read_to_string(&log)?,
        format!("--sty-graph-v3\n--source\n{root_name}\nmanifest:\n")
    );

    for drift in [
        "missing inventory",
        "null inventory",
        "missing params",
        "unknown function entry",
        "unknown param entry",
        "duplicate function",
        "unknown parameter mode",
        "unknown parameter type",
        "unknown return type",
        "unknown availability",
    ] {
        let mut changed = original.clone();
        match drift {
            "missing inventory" => {
                let object = changed
                    .as_object_mut()
                    .ok_or_else(|| anyhow::anyhow!("graph fixture is not an object"))?;
                object.remove("host_functions");
            }
            "null inventory" => changed["host_functions"] = serde_json::Value::Null,
            "missing params" => {
                let object = changed["host_functions"][0]
                    .as_object_mut()
                    .ok_or_else(|| anyhow::anyhow!("function fixture is not an object"))?;
                object.remove("params");
            }
            "unknown function entry" => changed["host_functions"][0]["extra"] = true.into(),
            "unknown param entry" => {
                changed["host_functions"][0]["params"][0]["extra"] = true.into();
            }
            "duplicate function" => {
                let function = changed["host_functions"][0].clone();
                changed["host_functions"] = serde_json::json!([function.clone(), function]);
            }
            "unknown parameter mode" => {
                changed["host_functions"][0]["params"][0]["mode"] = "flexible".into();
            }
            "unknown parameter type" => {
                changed["host_functions"][0]["params"][0]["type"] = "record".into();
            }
            "unknown return type" => changed["host_functions"][0]["returns"] = "record".into(),
            "unknown availability" => {
                changed["host_functions"][0]["availability"] = "global".into();
            }
            _ => anyhow::bail!("unexpected inventory drift {drift}"),
        }
        fixture.write("graph.json", &serde_json::to_string(&changed)?)?;
        fs::write(&log, "")?;
        let output = Command::new(env!("CARGO_BIN_EXE_sty"))
            .current_dir(fixture.root.path())
            .env("STY_TEST_ARGV_LOG", &log)
            .env("STY_TEST_GRAPH", &graph_file)
            .args(["check", "--host-checker", checker_name, root_name])
            .output()?;
        assert_eq!(
            output.status.code(),
            Some(2),
            "{drift}: {}",
            stderr(&output)
        );
        assert!(output.stdout.is_empty(), "{drift}: source JSON leaked");
    }
    Ok(())
}
