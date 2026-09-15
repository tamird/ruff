use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

use tempfile::TempDir;

struct Fixture {
    root: TempDir,
}

impl Fixture {
    fn new() -> anyhow::Result<Self> {
        let root = tempfile::tempdir()?;
        let fixture = Self { root };
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
