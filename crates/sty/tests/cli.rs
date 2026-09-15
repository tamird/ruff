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
    assert!(stderr(&bad_executable).contains("cannot start host checker"));
    Ok(())
}

#[cfg(unix)]
#[test]
fn host_child_receives_exact_argv_env_output_and_exit_code() -> anyhow::Result<()> {
    use std::os::unix::fs::PermissionsExt;

    let fixture = Fixture::unmarked()?;
    fixture.write("@notes.star", "VALUE = 1\n")?;
    fixture.write("source/local module=west.star", "VALUE = 2\n")?;
    fixture.write(
        "host-checker",
        concat!(
            "#!/bin/sh\n",
            "printf '%s\\n' \"$@\" > \"$STY_TEST_ARGV_LOG\"\n",
            "printf 'manifest:%s\\n' \"$RUNFILES_MANIFEST_FILE\" >> \"$STY_TEST_ARGV_LOG\"\n",
            "printf 'host stdout\\n'\n",
            "printf 'host stderr\\n' >&2\n",
            "exit 37\n",
        ),
    )?;
    let checker = fixture.path("host-checker");
    let mut permissions = fs::metadata(&checker)?.permissions();
    permissions.set_mode(0o755);
    fs::set_permissions(&checker, permissions)?;
    let log = fixture.path("host-argv.txt");
    let absolute_input = fixture.path("source/../source/local module=west.star");
    let named_input = format!("local={}", absolute_input.display());
    let missing_input = "unused=missing data=west.json";
    let output = Command::new(env!("CARGO_BIN_EXE_sty"))
        .current_dir(fixture.root.path())
        .env("STY_TEST_ARGV_LOG", &log)
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
    let cwd = fixture.root.path().canonicalize()?;
    let expected = format!(
        "--sty-check-v1\n--source\n{}\n--input\n{named_input}\n--input\nunused={}\nmanifest:host-manifest.txt\n",
        cwd.join("@notes.star").display(),
        cwd.join("missing data=west.json").display(),
    );
    assert_eq!(fs::read_to_string(log)?, expected);

    let double_slash_source = format!("/{}", fixture.path("@notes.star").display());
    let double_log = fixture.path("double-slash-argv.txt");
    let double = Command::new(env!("CARGO_BIN_EXE_sty"))
        .current_dir(fixture.root.path())
        .env("STY_TEST_ARGV_LOG", &double_log)
        .env("RUNFILES_MANIFEST_FILE", "host-manifest.txt")
        .arg("check")
        .arg("--host-checker")
        .arg(&checker)
        .arg(&double_slash_source)
        .output()?;
    assert_eq!(double.status.code(), Some(37), "{}", stderr(&double));
    assert_eq!(
        fs::read_to_string(double_log)?,
        format!("--sty-check-v1\n--source\n{double_slash_source}\nmanifest:host-manifest.txt\n")
    );
    Ok(())
}
