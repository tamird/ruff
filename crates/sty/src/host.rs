//! The versioned process boundary for host-owned `.star` sources.

use std::path::PathBuf;
use std::process::{Command as ChildCommand, Stdio};

use anyhow::{Context, Result, anyhow};
use ruff_db::Db;
use ruff_db::files::system_path_to_file;
use ruff_db::system::{SystemPath, SystemPathBuf};
use ruff_text_size::{TextRange, TextSize};
use serde::Deserialize;
use ty_starlark::star::{
    StarCheck, StarDirectLoad, StarFailureReason, StarHostFunction, StarHostParam, StarHostProfile,
    StarIntrinsic, StarLoadBinding, StarModule, StarResolvedGraph, StarSource, StarSpecialForm,
    check_star_graph,
};

use super::{CheckCommand, StyDb, absolute_host_path, is_star_path};
use crate::diagnostics;

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
    let diagnostics = diagnostics::star_diagnostics(&db, &graph, &outcome)?;
    diagnostics::report(&db, &diagnostics)?;
    if let StarCheck::Opaque(failure) = &outcome {
        return Ok(if is_graph_identity_failure(failure.reason()) {
            2
        } else {
            1
        });
    }
    if !diagnostics.is_empty() {
        return Ok(1);
    }

    // The v3 graph already contains the source snapshots and host facts used
    // by this bounded static pass. A native host check evaluates top-level
    // code and may need catalogs; callers run it separately when required.
    Ok(0)
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
pub(super) struct CapturedGraph {
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
    pub(super) fn sources(&self) -> impl Iterator<Item = (&str, &str)> {
        std::iter::once((self.root.path.as_str(), self.root.source.as_str())).chain(
            self.modules
                .iter()
                .map(|module| (module.path.as_str(), module.source.as_str())),
        )
    }

    pub(super) fn into_star_graph(
        self,
        db: &dyn Db,
        selected: &SystemPath,
    ) -> Result<StarResolvedGraph> {
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
