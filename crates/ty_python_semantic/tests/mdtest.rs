use anyhow::anyhow;
use camino::{Utf8Path, Utf8PathBuf};

const MDTEST_ROOT: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/resources/mdtest");
const LINT_DOC_ROOT: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/resources/lint_docs");

thread_local! {
    // Restrict each fixture's Rayon work to one thread so concurrent tests do not compete for the
    // same resources. When fixtures share a process, the harness reuses worker threads, so cache
    // one pool per worker.
    static RAYON_POOL: rayon::ThreadPool = rayon::ThreadPoolBuilder::new()
        .num_threads(1)
        .build()
        .unwrap();
}

/// See `crates/ty_test/README.md` for documentation on these tests.
#[expect(clippy::needless_pass_by_value)]
fn mdtest(fixture_path: &Utf8Path, content: String) -> datatest_stable::Result<()> {
    run(
        fixture_path,
        &content,
        MDTEST_ROOT,
        ty_test::RunOptions::default(),
    )
}

#[expect(clippy::needless_pass_by_value)]
fn lint_doc(fixture_path: &Utf8Path, content: String) -> datatest_stable::Result<()> {
    let rule_name = fixture_path
        .file_stem()
        .ok_or_else(|| anyhow!("Expected fixture path to have a file stem"))?;
    let rule = ty_python_semantic::default_lint_registry()
        .get(rule_name)
        .map_err(|err| anyhow!("Expected `{rule_name}` to name a lint rule: {err}"))?;

    run(
        fixture_path,
        &content,
        LINT_DOC_ROOT,
        ty_test::RunOptions {
            default_error_rule: Some(rule.name.as_str()),
        },
    )
}

fn run(
    fixture_path: &Utf8Path,
    content: &str,
    resource_root: &str,
    options: ty_test::RunOptions,
) -> datatest_stable::Result<()> {
    let short_title = fixture_path
        .file_name()
        .ok_or_else(|| anyhow!("Expected fixture path to have a file name"))?;

    let crate_dir = Utf8Path::new(env!("CARGO_MANIFEST_DIR"));
    let relative_fixture_path = fixture_path.strip_prefix(crate_dir)?;
    let absolute_crate_dir = std::path::absolute(crate_dir)?;
    let absolute_crate_dir = Utf8PathBuf::from_path_buf(absolute_crate_dir)
        .map_err(|path| anyhow!("Crate directory is not UTF-8: {}", path.display()))?;
    let snapshot_path = absolute_crate_dir
        .join("resources")
        .join("mdtest")
        .join("snapshots");
    let absolute_fixture_path = absolute_crate_dir.join(relative_fixture_path);
    let workspace_relative_fixture_path =
        Utf8Path::new("crates/ty_python_semantic").join(relative_fixture_path);

    let test_name = fixture_path
        .strip_prefix(resource_root)
        .unwrap_or(fixture_path)
        .as_str();

    RAYON_POOL.with(|pool| {
        pool.install(|| {
            ty_test::run(
                &absolute_fixture_path,
                &workspace_relative_fixture_path,
                content,
                &snapshot_path,
                short_title,
                test_name,
                options,
            )
        })
    })?;

    Ok(())
}

datatest_stable::harness! {
    { test = mdtest, root = MDTEST_ROOT, pattern = r"\.md$" },
    { test = lint_doc, root = LINT_DOC_ROOT, pattern = r"\.md$" },
}
