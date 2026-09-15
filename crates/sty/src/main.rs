//! Standalone Bazel `.bzl` checking with a source-owned Starlark database.

use std::collections::HashMap;
use std::io::{self, Write};
use std::path::PathBuf;
use std::process::ExitCode;

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
use ty_starlark::checker::{BazelCheckError, BazelCheckProblem};
use ty_starlark::graph::{
    BazelCheckedGraph, BazelGraphError, BazelGraphFailure, BazelGraphOutcome,
    BazelResolvedImportError, check_bazel_graph,
};
use ty_starlark::loads::{BazelLoadPlanError, BazelLoadPlanFailure};
use ty_starlark::overlay::{
    BazelTypedCallProblem, BazelVerificationError, BazelVerificationFailure,
};
use ty_starlark::preflight::BazelPreflightError;
use ty_starlark::source::BazelSource;
use ty_starlark::stub::BazelStubError;

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
#[command(name = "sty", about = "Check selected Bazel Starlark sources")]
struct Cli {
    #[command(subcommand)]
    command: Command,
}

#[derive(Subcommand)]
enum Command {
    /// Check one or more main-repository `.bzl` labels.
    Check(CheckCommand),
}

#[derive(Args)]
struct CheckCommand {
    /// A marked main repository; otherwise use the nearest marker above cwd.
    #[arg(long, value_name = "ROOT")]
    workspace: Option<PathBuf>,

    /// `//pkg:file.bzl`, `@@//pkg:file.bzl`, or `:file.bzl` from cwd's BUILD package.
    #[arg(required = true, value_name = "LABEL")]
    labels: Vec<String>,
}

fn main() -> ExitCode {
    match run() {
        Ok(false) => ExitCode::from(1),
        Ok(true) => ExitCode::SUCCESS,
        Err(error) => {
            let _ = writeln!(io::stderr().lock(), "sty failed: {error:#}");
            ExitCode::from(2)
        }
    }
}

fn run() -> Result<bool> {
    let Cli {
        command: Command::Check(options),
    } = Cli::parse();
    let cwd = absolute_cwd()?;
    let db = StyDb::new(&cwd);
    let root = if let Some(workspace) = options.workspace {
        let workspace = SystemPathBuf::from_path_buf(workspace)
            .map_err(|path| anyhow!("workspace path is not UTF-8: {path:?}"))?;
        let path = SystemPath::absolute(&workspace, &cwd);
        SystemPathBuf::from_path_buf(
            path.as_std_path()
                .canonicalize()
                .with_context(|| format!("cannot open selected Bazel workspace {path}"))?,
        )
        .map_err(|path| anyhow!("workspace path is not UTF-8: {path:?}"))?
    } else {
        find_bazel_repository(&db, &cwd)
            .ok_or_else(|| anyhow!("no Bazel repository marker above current directory {cwd}"))?
    };
    db.files().try_add_root(&db, &root, FileRootKind::Project);
    let repository = BazelRepository::new(&db, root);
    let selections: Vec<BazelSource<'_>> = options
        .labels
        .iter()
        .map(|label| {
            let relative = label.starts_with(':').then_some(cwd.as_path());
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
        let mut success = true;
        for node in graph.nodes() {
            match node.outcome() {
                BazelGraphOutcome::Checked(module) => {
                    for problem in module.problems() {
                        success = false;
                        self.arity(&mut output, problem)?;
                    }
                    for problem in module.typed_problems() {
                        success = false;
                        self.typed(&mut output, problem)?;
                    }
                }
                BazelGraphOutcome::Opaque(failure) => {
                    success = false;
                    self.opaque(&mut output, failure)?;
                }
            }
        }
        Ok(success)
    }

    fn arity(&mut self, output: &mut impl Write, problem: &BazelCheckProblem) -> io::Result<()> {
        let location = self.location(problem.file(), Some(problem.range()));
        let description = match problem.reason() {
            BazelCheckError::InvalidArity {
                callee,
                minimum,
                maximum,
                actual,
            } if minimum == maximum => {
                let noun = if *minimum == 1 {
                    "argument"
                } else {
                    "arguments"
                };
                format!("function '{callee}' expects {minimum} positional {noun}, got {actual}")
            }
            other @ BazelCheckError::InvalidArity { .. } => other.to_string(),
        };
        writeln!(output, "{location}: error: {description}")?;
        writeln!(
            output,
            "  declared at {}",
            self.location(
                problem.declaration_file(),
                Some(problem.declaration_range())
            )
        )
    }

    fn typed(
        &mut self,
        output: &mut impl Write,
        problem: &BazelTypedCallProblem,
    ) -> io::Result<()> {
        writeln!(
            output,
            "{}: error: {}",
            self.location(problem.file(), Some(problem.range())),
            problem.reason()
        )?;
        writeln!(
            output,
            "  declared at {}",
            self.location(problem.related_file(), Some(problem.related_range()))
        )
    }

    fn opaque(&mut self, output: &mut impl Write, failure: &BazelGraphFailure) -> io::Result<()> {
        writeln!(
            output,
            "{}: error: {}",
            self.location(failure.file(), failure.range()),
            graph_message(failure.reason())
        )?;
        if let Some(file) = failure.related_file() {
            writeln!(
                output,
                "  related: {}",
                self.location(file, failure.related_range())
            )?;
        } else if let Some(range) = related_load_range(failure.reason()) {
            writeln!(
                output,
                "  first bound at {}",
                self.location(failure.file(), Some(range))
            )?;
        }
        Ok(())
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

fn related_load_range(reason: &BazelGraphError) -> Option<TextRange> {
    match reason {
        BazelGraphError::LoadPlan(plan) => plan.related_range(),
        BazelGraphError::Import(failure) => match failure.reason() {
            BazelResolvedImportError::Plan(plan) => plan.related_range(),
            _ => None,
        },
        BazelGraphError::Source(failure) => match failure.reason() {
            BazelVerificationError::Source(preflight) => match preflight.reason() {
                BazelPreflightError::LoadPlan(plan) => plan.related_range(),
                _ => None,
            },
            _ => None,
        },
        _ => None,
    }
}

fn graph_message(reason: &BazelGraphError) -> String {
    match reason {
        BazelGraphError::LoadPlan(plan) => load_message(plan),
        BazelGraphError::Import(failure) => match failure.reason() {
            BazelResolvedImportError::Plan(plan) => load_message(plan),
            BazelResolvedImportError::TargetOpaque(verification) => {
                verification_message(verification)
            }
            other => other.to_string(),
        },
        BazelGraphError::Source(failure) => verification_message(failure),
        other => other.to_string(),
    }
}

fn load_message(failure: &BazelLoadPlanFailure) -> String {
    match failure.reason() {
        BazelLoadPlanError::Admission(admission) => admission.reason().to_string(),
        other => other.to_string(),
    }
}

fn verification_message(failure: &BazelVerificationFailure) -> String {
    match failure.reason() {
        BazelVerificationError::Source(preflight) => match preflight.reason() {
            BazelPreflightError::Admission(admission) => admission.reason().to_string(),
            BazelPreflightError::LoadPlan(plan) => load_message(plan),
            other => other.to_string(),
        },
        BazelVerificationError::Stub(stub) => match stub.reason() {
            BazelStubError::Source(preflight) => preflight.reason().to_string(),
            other => {
                let message = other.to_string();
                stub.path()
                    .map_or(message.clone(), |path| format!("{message}: {path}"))
            }
        },
        other => other.to_string(),
    }
}
