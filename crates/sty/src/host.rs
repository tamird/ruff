//! The versioned process boundary for host-owned `.star` sources.

use std::collections::HashMap;
use std::collections::hash_map::Entry;
use std::io::{self, Write};
use std::path::PathBuf;
use std::process::{Command as ChildCommand, Stdio};

use anyhow::{Context, Result, anyhow};
use ruff_db::Db;
use ruff_db::files::{File, system_path_to_file};
use ruff_db::system::{SystemPath, SystemPathBuf};
use ruff_source_file::LineIndex;
use ruff_text_size::{TextRange, TextSize};
use serde::Deserialize;
use ty_starlark::star::{
    StarAnalysis, StarCheck, StarDirectLoad, StarFailure, StarFailureReason, StarHostFunction,
    StarHostParam, StarHostProfile, StarIntrinsic, StarLoadBinding, StarModule, StarResolvedGraph,
    StarSource, StarSpecialForm, check_star_graph,
};

use super::{CheckCommand, StyDb, absolute_host_path, is_star_path};

pub(super) fn run_host(cwd: &SystemPath, checker: &PathBuf, options: &CheckCommand) -> Result<i32> {
    let invocation = HostInvocation::new(cwd, options)?;
    // The graph's stdout contains complete source snapshots. Capture it for
    // analysis, inherit stderr, and never print the JSON on parse failures.
    let output = invocation
        .command(checker, "--sty-graph-v3")
        .stderr(Stdio::inherit())
        .output()
        .with_context(|| format!("cannot start host graph producer {}", checker.display()))?;
    if !output.status.success() {
        return Ok(output.status.code().unwrap_or(1));
    }
    let captured: CapturedGraph = serde_json::from_slice(&output.stdout)
        .context("host graph returned invalid versioned JSON")?;
    let db = StyDb::new(cwd);
    let graph = captured.into_star_graph(&db, &invocation.source)?;
    let outcome = check_star_graph(&graph);
    let reporter = SnapshotReporter::new(&db, &graph);
    match outcome {
        StarCheck::Partial(analysis) => {
            reporter.report_problems(&analysis)?;
            if !analysis.problems().is_empty()
                || !analysis.native_problems().is_empty()
                || !analysis.native_call_problems().is_empty()
                || !analysis.native_availability_problems().is_empty()
            {
                return Ok(1);
            }
        }
        StarCheck::Opaque(failure) => {
            reporter.report_failure(&failure)?;
            return Ok(if is_graph_identity_failure(failure.reason()) {
                2
            } else {
                1
            });
        }
    }

    // A clear bounded source pass still requires the host's native parser,
    // loader, annotation checks, and data-dependent runtime checks. Native
    // v1 rereads files, so this process protocol does not attest a common
    // filesystem revision across the two separate invocations.
    let status = invocation
        .command(checker, "--sty-check-v1")
        .status()
        .with_context(|| format!("cannot start host checker {}", checker.display()))?;
    Ok(status.code().unwrap_or(1))
}

fn is_graph_identity_failure(reason: &StarFailureReason) -> bool {
    match reason {
        StarFailureReason::Profile => true,
        StarFailureReason::DuplicateModule => true,
        StarFailureReason::ConflictingSnapshot => true,
        StarFailureReason::UnresolvedModule => true,
        StarFailureReason::LoadCycle => true,
        StarFailureReason::LoadMismatch => true,
        StarFailureReason::PrivateImport => true,
        StarFailureReason::Parser(_) => false,
        StarFailureReason::PythonVersion(_) => false,
        StarFailureReason::NonModule => false,
    }
}

struct HostInvocation {
    source: SystemPathBuf,
    inputs: Vec<String>,
}

impl HostInvocation {
    fn new(cwd: &SystemPath, options: &CheckCommand) -> Result<Self> {
        let CheckCommand {
            workspace,
            host_checker: _,
            inputs,
            labels,
        } = options;
        if workspace.is_some() {
            return Err(anyhow!("--workspace applies only to Bazel .bzl labels"));
        }
        let [source] = labels.as_slice() else {
            return Err(anyhow!(
                "host checking requires exactly one .star file path"
            ));
        };
        if source.starts_with(':')
            || (source.starts_with("//") && source.contains(':'))
            || (source.starts_with('@') && source.contains("//"))
        {
            return Err(anyhow!(
                "host checking requires a file path, not a Bazel label"
            ));
        }
        if !is_star_path(source) {
            return Err(anyhow!("host checking requires a .star file path"));
        }
        let source = absolute_host_path(source, cwd);
        let mut resolved_inputs = Vec::with_capacity(inputs.len());
        for input in inputs {
            let (name, path) = input
                .split_once('=')
                .ok_or_else(|| anyhow!("host input must have NAME=PATH form: {input}"))?;
            if name.is_empty() || path.is_empty() {
                return Err(anyhow!("host input needs nonempty NAME and PATH: {input}"));
            }
            let path = absolute_host_path(path, cwd);
            resolved_inputs.push(format!("{name}={path}"));
        }
        Ok(Self {
            source,
            inputs: resolved_inputs,
        })
    }

    fn command(&self, checker: &PathBuf, profile: &str) -> ChildCommand {
        let HostInvocation { source, inputs } = self;
        let mut command = ChildCommand::new(checker);
        command
            .arg(profile)
            .arg("--source")
            .arg(source.as_std_path());
        for input in inputs {
            command.arg("--input").arg(input);
        }
        command
    }
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct CapturedGraph {
    version: String,
    profile: String,
    root: CapturedSource,
    modules: Vec<CapturedModule>,
    special_forms: Vec<CapturedSpecialForm>,
    intrinsics: Vec<CapturedIntrinsic>,
    host_functions: Option<Vec<CapturedHostFunction>>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct CapturedSource {
    path: String,
    source: String,
    loads: Vec<CapturedLoad>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct CapturedModule {
    id: String,
    path: String,
    source: String,
    loads: Vec<CapturedLoad>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct CapturedLoad {
    module_id: String,
    start: u32,
    end: u32,
    symbols: Vec<CapturedSymbol>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct CapturedSymbol {
    local: String,
    source: String,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct CapturedSpecialForm {
    name: String,
    kind: String,
    validator: String,
    field_types: String,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct CapturedIntrinsic {
    name: String,
    kind: String,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct CapturedHostFunction {
    name: String,
    params: Vec<CapturedHostParam>,
    returns: String,
    availability: String,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct CapturedHostParam {
    name: String,
    mode: String,
    required: bool,
    #[serde(rename = "type")]
    ty: String,
}

impl CapturedGraph {
    fn into_star_graph(self, db: &dyn Db, selected: &SystemPath) -> Result<StarResolvedGraph> {
        let CapturedGraph {
            version,
            profile,
            root,
            modules,
            special_forms,
            intrinsics,
            host_functions,
        } = self;
        if version != "sty-star-graph-v3" {
            return Err(anyhow!(
                "host --sty-graph-v3 returned graph version {version:?}"
            ));
        }
        let host_functions = host_functions
            .ok_or_else(|| anyhow!("host graph v3 omitted host_functions inventory"))?;
        let CapturedSource {
            path,
            source,
            loads,
        } = root;
        if path != selected.as_str() {
            return Err(anyhow!(
                "host graph root path {path:?} differs from selected .star source {selected:?}"
            ));
        }
        let root = captured_source(db, &path, source, loads)?;
        let mut resolved_modules = Vec::with_capacity(modules.len());
        for module in modules {
            let CapturedModule {
                id,
                path,
                source,
                loads,
            } = module;
            let source = captured_source(db, &path, source, loads)?;
            resolved_modules.push(StarModule { id, source });
        }
        let forms = special_forms
            .into_iter()
            .map(|form| {
                let CapturedSpecialForm {
                    name,
                    kind,
                    validator,
                    field_types,
                } = form;
                StarSpecialForm {
                    name,
                    kind,
                    validator,
                    field_types,
                }
            })
            .collect();
        let intrinsics = intrinsics
            .into_iter()
            .map(|intrinsic| {
                let CapturedIntrinsic { name, kind } = intrinsic;
                StarIntrinsic { name, kind }
            })
            .collect();
        let host_functions = host_functions
            .into_iter()
            .map(|function| {
                let CapturedHostFunction {
                    name,
                    params,
                    returns,
                    availability,
                } = function;
                let params = params
                    .into_iter()
                    .map(|param| {
                        let CapturedHostParam {
                            name,
                            mode,
                            required,
                            ty,
                        } = param;
                        StarHostParam {
                            name,
                            mode,
                            required,
                            ty,
                        }
                    })
                    .collect();
                StarHostFunction {
                    name,
                    params,
                    returns,
                    availability,
                }
            })
            .collect();
        Ok(StarResolvedGraph {
            version,
            profile: StarHostProfile {
                name: profile,
                special_forms: forms,
                intrinsics,
                host_functions,
            },
            root,
            modules: resolved_modules.into_boxed_slice(),
        })
    }
}

fn captured_source(
    db: &dyn Db,
    path: &str,
    text: String,
    loads: Vec<CapturedLoad>,
) -> Result<StarSource> {
    let _: u32 = text
        .len()
        .try_into()
        .with_context(|| format!("captured .star source exceeds span limits: {path}"))?;
    let system_path = SystemPath::new(path);
    if !system_path.is_absolute() {
        return Err(anyhow!("host graph .star path is not absolute: {path:?}"));
    }
    let file = system_path_to_file(db, system_path)
        .with_context(|| format!("cannot find captured .star source {path}"))?;
    let mut resolved_loads = Vec::with_capacity(loads.len());
    for load in loads {
        let CapturedLoad {
            module_id,
            start,
            end,
            symbols,
        } = load;
        let start_byte = usize::try_from(start)?;
        let end_byte = usize::try_from(end)?;
        let range = start_byte..end_byte;
        if range.is_empty() || text.get(range).is_none() {
            return Err(anyhow!(
                "host graph has an invalid UTF-8 load span in {path}: {start}..{end}"
            ));
        }
        let bindings = symbols
            .into_iter()
            .map(|symbol| {
                let CapturedSymbol { local, source } = symbol;
                StarLoadBinding { local, source }
            })
            .collect();
        resolved_loads.push(StarDirectLoad {
            module_id,
            label_range: TextRange::new(TextSize::new(start), TextSize::new(end)),
            bindings,
        });
    }
    Ok(StarSource {
        file,
        text,
        loads: resolved_loads.into_boxed_slice(),
    })
}

struct SnapshotReporter<'db, 'graph> {
    db: &'db dyn Db,
    lines: HashMap<File, (&'graph str, LineIndex)>,
}

impl<'db, 'graph> SnapshotReporter<'db, 'graph> {
    fn new(db: &'db dyn Db, graph: &'graph StarResolvedGraph) -> Self {
        let StarResolvedGraph {
            version: _,
            profile: _,
            root,
            modules,
        } = graph;
        let mut lines = HashMap::new();
        for source in std::iter::once(root).chain(modules.iter().map(|module| &module.source)) {
            match lines.entry(source.file) {
                Entry::Occupied(_) => {
                    // check_star_graph rejects differing text for this File
                    // before exposing any source range from either snapshot.
                }
                Entry::Vacant(entry) => {
                    let text = source.text.as_str();
                    entry.insert((text, LineIndex::from_source_text(text)));
                }
            }
        }
        Self { db, lines }
    }

    fn report_problems(&self, analysis: &StarAnalysis) -> Result<()> {
        let stderr = io::stderr();
        let mut output = stderr.lock();
        for problem in analysis.problems() {
            let primary = self.location(problem.file(), Some(problem.range()))?;
            writeln!(output, "{primary}: error: {problem}")?;
            let declaration =
                self.location(problem.related_file(), Some(problem.related_range()))?;
            writeln!(output, "  {} at {declaration}", problem.related_label())?;
        }
        for problem in analysis.native_problems() {
            let primary = self.location(problem.file(), Some(problem.range()))?;
            writeln!(output, "{primary}: error: {problem}")?;
            writeln!(output, "  host signature: {}", problem.signature())?;
        }
        for problem in analysis.native_call_problems() {
            let primary = self.location(problem.file(), Some(problem.range()))?;
            writeln!(output, "{primary}: error: {problem}")?;
            writeln!(output, "  host signature: {}", problem.signature())?;
        }
        for problem in analysis.native_availability_problems() {
            let primary = self.location(problem.file(), Some(problem.range()))?;
            writeln!(output, "{primary}: error: {problem}")?;
            writeln!(output, "  host availability: {}", problem.availability())?;
        }
        Ok(())
    }

    fn report_failure(&self, failure: &StarFailure) -> Result<()> {
        let primary = self.location(failure.file(), failure.range())?;
        writeln!(
            io::stderr().lock(),
            "{primary}: error: {}",
            failure.reason()
        )?;
        Ok(())
    }

    fn location(&self, file: File, range: Option<TextRange>) -> Result<String> {
        let SnapshotReporter { db, lines } = self;
        let path = file.path(*db).to_string();
        let Some(range) = range else {
            return Ok(path);
        };
        let (text, index) = lines
            .get(&file)
            .ok_or_else(|| anyhow!("captured .star source has no text for {path}"))?;
        let bytes = range.start().to_usize()..range.end().to_usize();
        if text.get(bytes).is_none() {
            return Err(anyhow!(
                "captured .star source has an invalid UTF-8 diagnostic span in {path}: {range:?}"
            ));
        }
        let position = index.line_column(range.start(), text);
        Ok(format!(
            "{path}:{}:{}",
            position.line.get(),
            position.column.get()
        ))
    }
}
