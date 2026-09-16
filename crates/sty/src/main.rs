//! Standalone Bazel `.bzl` and host-owned `.star` checking.

use std::collections::HashMap;
use std::io::{self, Write};
use std::path::{Path, PathBuf};

use anyhow::{Context, Result, anyhow};
use clap::{Args, Parser, Subcommand};
use ruff_db::Db;
use ruff_db::files::{File, FileRootKind, Files};
use ruff_db::source::{SourceText, source_text};
use ruff_db::system::{OsSystem, System, SystemPath, SystemPathBuf};
use ruff_db::vendored::VendoredFileSystem;
use ruff_source_file::LineIndex;
use ruff_text_size::TextRange;
use ty_starlark::bazel::{BazelRepository, find_bazel_repository, resolve_bazel_target};
use ty_starlark::graph::{BazelCheckedGraph, check_bazel_graph};
use ty_starlark::source::BazelSource;

mod host;
mod problems;

use problems::{bazel_problems, graph_message};

#[salsa::db]
#[derive(Clone)]
struct StyDb {
    storage: salsa::Storage<Self>,
    files: Files,
    system: OsSystem,
    vendored: VendoredFileSystem,
}

impl StyDb {
    fn new(cwd: &SystemPath) -> Self {
        Self {
            storage: salsa::Storage::default(),
            files: Files::default(),
            system: OsSystem::new(cwd),
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
        &self.system
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
    let Cli {
        command: Command::Check(options),
    } = Cli::parse();
    let cwd = absolute_cwd()?;
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
    Reporter::new(&db)
        .report(&graph)
        .context("cannot write Sty diagnostics")
}

fn absolute_cwd() -> Result<SystemPathBuf> {
    let path = std::env::current_dir().context("cannot read current directory")?;
    let path = path
        .canonicalize()
        .context("cannot resolve current directory")?;
    SystemPathBuf::from_path_buf(path)
        .map_err(|path| anyhow!("current directory is not UTF-8: {path:?}"))
}

struct Reporter<'db> {
    db: &'db dyn Db,
    lines: HashMap<File, (SourceText, LineIndex)>,
}

impl<'db> Reporter<'db> {
    fn new(db: &'db dyn Db) -> Self {
        Self {
            db,
            lines: HashMap::new(),
        }
    }

    fn report(&mut self, graph: &BazelCheckedGraph) -> io::Result<bool> {
        let stderr = io::stderr();
        let mut output = stderr.lock();
        let problems = bazel_problems(graph);
        for problem in &problems {
            writeln!(
                output,
                "{}: error: {}",
                self.location(problem.file, problem.range),
                problem.message
            )?;
            if let Some(related) = &problem.related {
                writeln!(
                    output,
                    "  {} {}",
                    related.label,
                    self.location(related.file, related.range)
                )?;
            }
        }
        Ok(problems.is_empty())
    }

    fn location(&mut self, file: File, range: Option<TextRange>) -> String {
        let path = file.path(self.db).to_string();
        let Some(range) = range else {
            return path;
        };
        let (text, index) = self.lines.entry(file).or_insert_with(|| {
            let text = source_text(self.db, file);
            let index = LineIndex::from_source_text(text.as_str());
            (text, index)
        });
        if text.read_error().is_none() && range.start().to_usize() <= text.as_str().len() {
            let position = index.line_column(range.start(), text.as_str());
            format!("{path}:{}:{}", position.line.get(), position.column.get())
        } else {
            format!("{path}:byte{}", range.start().to_usize())
        }
    }
}
