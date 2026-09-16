//! Standalone Bazel `.bzl` and host-owned `.star` checking.

use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::sync::Arc;

use anyhow::{Context, Result, anyhow};
use clap::{Args, Parser, Subcommand};
use ruff_db::Db;
use ruff_db::files::{FileRootKind, Files};
use ruff_db::system::{OsSystem, System, SystemPath, SystemPathBuf};
use ruff_db::vendored::VendoredFileSystem;
use ty_starlark::bazel::{BazelRepository, find_bazel_repository, resolve_bazel_target};
use ty_starlark::graph::check_bazel_graph;
use ty_starlark::source::BazelSource;

mod diagnostics;
mod editor_system;
mod host;
mod server;

use diagnostics::{bazel_diagnostics, graph_message};

#[salsa::db]
#[derive(Clone)]
struct StyDb {
    storage: salsa::Storage<Self>,
    files: Files,
    system: Arc<dyn System>,
    vendored: VendoredFileSystem,
}

impl StyDb {
    fn new(cwd: &SystemPath) -> Self {
        Self {
            storage: salsa::Storage::default(),
            files: Files::default(),
            system: Arc::new(OsSystem::new(cwd)),
            vendored: VendoredFileSystem::default(),
        }
    }

    fn with_system(system: Arc<dyn System>) -> Self {
        Self {
            storage: salsa::Storage::default(),
            files: Files::default(),
            system,
            vendored: VendoredFileSystem::default(),
        }
    }
}

#[salsa::db]
impl Db for StyDb {
    fn files(&self) -> &Files {
        &self.files
    }

    fn system(&self) -> &dyn System {
        &*self.system
    }

    fn vendored(&self) -> &VendoredFileSystem {
        &self.vendored
    }
}

#[salsa::db]
impl salsa::Database for StyDb {}

#[derive(Parser)]
#[command(name = "sty", about = "Check Bazel .bzl or host-owned .star sources")]
struct Cli {
    #[command(subcommand)]
    command: Command,
}

#[derive(Subcommand)]
enum Command {
    /// Check main-repository `.bzl` labels or one `.star` with its host.
    Check(CheckCommand),
    /// Serve editor diagnostics for Starlark files.
    Server,
}

#[derive(Args)]
struct CheckCommand {
    /// A marked main repository; otherwise use the nearest marker above cwd.
    #[arg(long, value_name = "ROOT")]
    workspace: Option<PathBuf>,

    /// Executable host providing a versioned `.star` source graph.
    #[arg(long, value_name = "EXE")]
    host_checker: Option<PathBuf>,

    /// A named host input as NAME=PATH; the host decides when to read it.
    #[arg(long = "input", value_name = "NAME=PATH")]
    inputs: Vec<String>,

    /// Bazel labels, or one `.star` path when --host-checker is supplied.
    #[arg(value_name = "LABEL_OR_PATH")]
    labels: Vec<String>,
}

fn main() {
    let status = match run() {
        Ok(status) => status,
        Err(error) => {
            let _ = writeln!(io::stderr().lock(), "sty failed: {error:#}");
            2
        }
    };
    std::process::exit(status);
}

fn run() -> Result<i32> {
    let Cli { command } = Cli::parse();
    let cwd = absolute_cwd()?;
    let Command::Check(options) = command else {
        server::run_stdio(&cwd)?;
        return Ok(0);
    };
    if let Some(checker) = options.host_checker.as_ref() {
        return host::run_host(&cwd, checker, &options);
    }
    if !options.inputs.is_empty() {
        return Err(anyhow!("--input requires --host-checker"));
    }
    if options.labels.is_empty() {
        return Err(anyhow!("check requires at least one Bazel label"));
    }
    if options.labels.iter().any(|label| is_star_path(label)) {
        return Err(anyhow!(
            ".star files require --host-checker with a file path"
        ));
    }
    let healthy = run_bazel(&cwd, options)?;
    Ok(i32::from(!healthy))
}

fn absolute_host_path(path: &str, cwd: &SystemPath) -> SystemPathBuf {
    let path = SystemPath::new(path);
    if path.is_absolute() {
        path.to_path_buf()
    } else {
        SystemPath::absolute(path, cwd)
    }
}

fn is_star_path(path: &str) -> bool {
    Path::new(path)
        .extension()
        .is_some_and(|extension| extension == "star")
}

fn run_bazel(cwd: &SystemPath, options: CheckCommand) -> Result<bool> {
    let db = StyDb::new(cwd);
    let root = if let Some(workspace) = options.workspace {
        let workspace = SystemPathBuf::from_path_buf(workspace)
            .map_err(|path| anyhow!("workspace path is not UTF-8: {path:?}"))?;
        let path = SystemPath::absolute(&workspace, cwd);
        SystemPathBuf::from_path_buf(
            path.as_std_path()
                .canonicalize()
                .with_context(|| format!("cannot open selected Bazel workspace {path}"))?,
        )
        .map_err(|path| anyhow!("workspace path is not UTF-8: {path:?}"))?
    } else {
        find_bazel_repository(&db, cwd)
            .ok_or_else(|| anyhow!("no Bazel repository marker above current directory {cwd}"))?
    };
    db.files().try_add_root(&db, &root, FileRootKind::Project);
    let repository = BazelRepository::new(&db, root);
    let selections: Vec<BazelSource<'_>> = options
        .labels
        .iter()
        .map(|label| {
            let relative = label.starts_with(':').then_some(cwd);
            resolve_bazel_target(&db, repository, relative, label)
                .with_context(|| format!("cannot select Bazel label {label}"))
        })
        .collect::<Result<_>>()?;
    let graph = check_bazel_graph(&db, &selections).map_err(|failure| {
        anyhow!(
            "cannot check selected Bazel sources: {}",
            graph_message(failure.reason())
        )
    })?;
    let diagnostics = bazel_diagnostics(&graph);
    diagnostics::report(&db, &diagnostics).context("cannot write Sty diagnostics")?;
    Ok(diagnostics.is_empty())
}

fn absolute_cwd() -> Result<SystemPathBuf> {
    let path = std::env::current_dir().context("cannot read current directory")?;
    let path = path
        .canonicalize()
        .context("cannot resolve current directory")?;
    SystemPathBuf::from_path_buf(path)
        .map_err(|path| anyhow!("current directory is not UTF-8: {path:?}"))
}
