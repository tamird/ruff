//! Validates host-captured sources and supplies their facts to Ty inference.

use std::collections::hash_map::Entry;
use std::collections::{HashMap, HashSet};

use ruff_db::Db;
use ruff_db::diagnostic::Diagnostic;
use ruff_db::files::File;
use ruff_python_ast::{self as ast, Expr, PythonVersion, Stmt, name::Name};
use ruff_python_parser::{Mode, ParseError, ParseOptions, UnsupportedSyntaxError, parse_unchecked};
use ruff_source_file::SourceFileBuilder;
use ruff_text_size::{Ranged, TextRange};
use salsa::Setter;
use ty_python_core::ProgramFile;
use ty_python_core::starlark::{
    StarlarkAvailability, StarlarkEnvironment, StarlarkGlobalDeclaration, StarlarkGlobalKind,
    StarlarkLoad, StarlarkModule, StarlarkModuleRole, StarlarkParameter, StarlarkParameterMode,
    StarlarkType,
};

use crate::analysis::{Analysis, AnalysisDb, StarlarkProfile};

/// Direct bindings already resolved by the host's actual loader.
#[derive(Debug)]
pub struct StarLoadBinding {
    pub local: String,
    pub source: String,
}

/// The label range includes the quotes around the module-ID literal.
#[derive(Debug)]
pub struct StarDirectLoad {
    pub module_id: String,
    pub label_range: TextRange,
    pub bindings: Box<[StarLoadBinding]>,
}

/// The text is the exact UTF-8 snapshot parsed by the host, not a later read.
#[derive(Debug)]
pub struct StarSource {
    pub file: File,
    pub text: String,
    pub loads: Box<[StarDirectLoad]>,
}

#[derive(Debug)]
pub struct StarModule {
    pub id: String,
    pub source: StarSource,
}

/// Producer-provided names and behavior of recognized record constructor forms.
#[derive(Debug)]
pub struct StarSpecialForm {
    pub name: String,
    pub kind: String,
    pub validator: String,
    pub field_types: String,
}

/// Producer-attested semantics of a native Starlark global.
#[derive(Debug)]
pub struct StarIntrinsic {
    pub name: String,
    pub kind: String,
}

#[derive(Debug)]
pub struct StarHostProfile {
    pub name: String,
    pub special_forms: Box<[StarSpecialForm]>,
    pub intrinsics: Box<[StarIntrinsic]>,
    pub host_functions: Box<[StarHostFunction]>,
}

/// Producer-attested native callable signature and its evaluator availability.
#[derive(Debug)]
pub struct StarHostFunction {
    pub name: String,
    pub params: Box<[StarHostParam]>,
    pub returns: String,
    pub availability: String,
}

#[derive(Debug)]
pub struct StarHostParam {
    pub name: String,
    pub mode: String,
    pub required: bool,
    pub ty: String,
}

/// Host-owned source snapshots, resolved loads, and native declarations.
#[derive(Debug)]
pub struct StarResolvedGraph {
    pub version: String,
    pub profile: StarHostProfile,
    pub root: StarSource,
    pub modules: Box<[StarModule]>,
}

/// Admission failures remain distinct from ordinary semantic diagnostics.
#[derive(Debug)]
pub enum StarCheck {
    Checked(Vec<Diagnostic>),
    Opaque(StarFailure),
}

struct AdmittedGraph<'graph> {
    declarations: Box<[StarlarkGlobalDeclaration]>,
    load_ranges: Box<[Box<[TextRange]>]>,
    by_id: HashMap<&'graph str, usize>,
}

/// Checks captured text without executing source or consulting a Python project.
pub fn check_star_graph(db: &dyn Db, graph: &StarResolvedGraph) -> anyhow::Result<StarCheck> {
    analyze_star_graph(db, graph).map(|(result, _)| result)
}

/// Retains admitted source and host facts for subsequent editor queries.
pub fn analyze_star_graph(
    db: &dyn Db,
    graph: &StarResolvedGraph,
) -> anyhow::Result<(StarCheck, Option<Analysis>)> {
    let admitted = match admit_graph(graph) {
        Ok(admitted) => admitted,
        Err(failure) => return Ok((StarCheck::Opaque(failure), None)),
    };
    let AdmittedGraph {
        declarations,
        load_ranges,
        by_id,
    } = admitted;
    let mut analysis = AnalysisDb::new(StarlarkProfile::Hosted)?;
    let environment = StarlarkEnvironment::new(&analysis, declarations);
    let mut files = HashMap::new();
    let mut modules = Vec::with_capacity(graph.modules.len() + 1);
    for (source, name, role) in graph
        .modules
        .iter()
        .map(|module| {
            (
                &module.source,
                module.id.as_str(),
                StarlarkModuleRole::Loaded,
            )
        })
        .chain(std::iter::once((
            &graph.root,
            "<root>",
            StarlarkModuleRole::Root,
        )))
    {
        let file = match files.entry(source.file) {
            Entry::Occupied(entry) => *entry.get(),
            Entry::Vacant(entry) => {
                let captured =
                    SourceFileBuilder::new(source.file.path(db).as_str(), source.text.as_str())
                        .finish();
                let file = analysis.add_source(captured)?;
                *entry.insert(file)
            }
        };
        modules.push(StarlarkModule::new(
            &analysis,
            file,
            Name::new(name),
            Box::default(),
            Box::default(),
            Some(environment),
            role,
        ));
    }
    for ((module, ranges), source) in modules.iter().zip(load_ranges).zip(
        graph
            .modules
            .iter()
            .map(|module| &module.source)
            .chain(std::iter::once(&graph.root)),
    ) {
        let loads = source
            .loads
            .iter()
            .zip(ranges)
            .map(|(load, range)| StarlarkLoad {
                range,
                module: modules[by_id[load.module_id.as_str()]],
            })
            .collect();
        module.set_loads(&mut analysis).to(loads);
    }
    let program = analysis.program();
    let mut diagnostics = Vec::new();
    for &module in &modules {
        diagnostics.extend(ty_python_semantic::check_file_unwrap(
            &analysis,
            ProgramFile::new_starlark(&analysis, module, program),
        ));
    }
    analysis.freeze(&mut diagnostics)?;
    Ok((
        StarCheck::Checked(diagnostics),
        Some(Analysis::new(analysis, modules, Vec::new())),
    ))
}

fn admit_graph(graph: &StarResolvedGraph) -> Result<AdmittedGraph<'_>, StarFailure> {
    let StarResolvedGraph {
        version,
        profile,
        root,
        modules,
    } = graph;
    let declarations = supported_forms(version, profile)
        .ok_or_else(|| StarFailure::at(root.file, None, StarFailureReason::Profile))?;
    let mut snapshots = HashMap::new();
    for source in std::iter::once(root).chain(modules.iter().map(|module| &module.source)) {
        match snapshots.entry(source.file) {
            Entry::Occupied(entry) => {
                if *entry.get() != source.text.as_str() {
                    return Err(StarFailure::at(
                        source.file,
                        None,
                        StarFailureReason::ConflictingSnapshot,
                    ));
                }
            }
            Entry::Vacant(entry) => {
                entry.insert(source.text.as_str());
            }
        }
    }
    let mut by_id = HashMap::new();
    for (index, module) in modules.iter().enumerate() {
        match by_id.entry(module.id.as_str()) {
            Entry::Occupied(_) => {
                return Err(StarFailure::at(
                    module.source.file,
                    None,
                    StarFailureReason::DuplicateModule,
                ));
            }
            Entry::Vacant(entry) => {
                entry.insert(index);
            }
        }
    }
    let mut load_ranges = Vec::with_capacity(modules.len() + 1);
    for source in modules
        .iter()
        .map(|module| &module.source)
        .chain(std::iter::once(root))
    {
        load_ranges.push(parse_star_source(source)?);
        for load in &source.loads {
            if !by_id.contains_key(load.module_id.as_str()) {
                return Err(StarFailure::at(
                    source.file,
                    Some(load.label_range),
                    StarFailureReason::UnresolvedModule,
                ));
            }
            if load
                .bindings
                .iter()
                .any(|binding| binding.source.starts_with('_'))
            {
                return Err(StarFailure::at(
                    source.file,
                    Some(load.label_range),
                    StarFailureReason::PrivateImport,
                ));
            }
        }
    }
    validate_load_dag(modules, &by_id)?;
    Ok(AdmittedGraph {
        declarations,
        load_ranges: load_ranges.into_boxed_slice(),
        by_id,
    })
}

#[derive(Debug)]
pub struct StarFailure {
    file: File,
    range: Option<TextRange>,
    reason: StarFailureReason,
}

impl StarFailure {
    pub fn file(&self) -> File {
        self.file
    }

    pub fn range(&self) -> Option<TextRange> {
        self.range
    }

    pub fn reason(&self) -> &StarFailureReason {
        &self.reason
    }

    fn at(file: File, range: Option<TextRange>, reason: StarFailureReason) -> Self {
        Self {
            file,
            range,
            reason,
        }
    }
}

#[derive(Debug, thiserror::Error)]
pub enum StarFailureReason {
    #[error("the host graph has an unsupported version or special-form profile")]
    Profile,
    #[error("the host graph contains duplicate logical module IDs")]
    DuplicateModule,
    #[error("the host graph assigns conflicting source snapshots to one file")]
    ConflictingSnapshot,
    #[error("the host graph references an unresolved module")]
    UnresolvedModule,
    #[error("the host graph contains a cycle of Starlark loads")]
    LoadCycle,
    #[error("a parsed Starlark load differs from the captured host load graph")]
    LoadMismatch,
    #[error("a load requests a private Starlark binding")]
    PrivateImport,
    #[error("the shared Python parser cannot check this Starlark source: {0}")]
    Parser(ParseError),
    #[error("the shared Python parser cannot check this Starlark source: {0}")]
    PythonVersion(UnsupportedSyntaxError),
    #[error("the shared parser returned a non-module source")]
    NonModule,
}

fn validate_load_dag(
    modules: &[StarModule],
    by_id: &HashMap<&str, usize>,
) -> Result<(), StarFailure> {
    let mut dependencies = vec![0usize; modules.len()];
    let mut dependents = vec![Vec::new(); modules.len()];
    for (index, module) in modules.iter().enumerate() {
        for load in &module.source.loads {
            let Some(&target) = by_id.get(load.module_id.as_str()) else {
                return Err(StarFailure::at(
                    module.source.file,
                    Some(load.label_range),
                    StarFailureReason::UnresolvedModule,
                ));
            };
            dependencies[index] += 1;
            dependents[target].push(index);
        }
    }
    let mut ready: Vec<_> = dependencies
        .iter()
        .enumerate()
        .filter_map(|(index, count)| (*count == 0).then_some(index))
        .collect();
    let mut visited = 0;
    while let Some(target) = ready.pop() {
        visited += 1;
        for &importer in &dependents[target] {
            dependencies[importer] -= 1;
            if dependencies[importer] == 0 {
                ready.push(importer);
            }
        }
    }
    if visited != modules.len() {
        let Some((index, _)) = dependencies
            .iter()
            .enumerate()
            .find(|(_, count)| **count > 0)
        else {
            return Ok(());
        };
        let source = &modules[index].source;
        return Err(StarFailure::at(
            source.file,
            source.loads.first().map(|load| load.label_range),
            StarFailureReason::LoadCycle,
        ));
    }
    Ok(())
}

fn supported_forms(
    version: &str,
    profile: &StarHostProfile,
) -> Option<Box<[StarlarkGlobalDeclaration]>> {
    let StarHostProfile {
        name,
        special_forms,
        intrinsics,
        host_functions,
    } = profile;
    if version != "sty-star-graph-v3"
        || name.is_empty()
        || special_forms.is_empty()
        || intrinsics.len() != 2
    {
        return None;
    }
    let mut names = HashSet::new();
    let mut declarations = Vec::new();
    for intrinsic in intrinsics {
        let StarIntrinsic { name, kind } = intrinsic;
        let kind = match (name.as_str(), kind.as_str()) {
            ("field", "field_first_type_optional_default") => StarlarkGlobalKind::Field,
            ("struct", "struct_named_members") => StarlarkGlobalKind::Struct,
            _ => return None,
        };
        if !names.insert(name.as_str()) {
            return None;
        }
        declarations.push(StarlarkGlobalDeclaration {
            name: Name::new(name),
            kind,
        });
    }
    for form in special_forms {
        let StarSpecialForm {
            name,
            kind,
            validator,
            field_types,
        } = form;
        if name.is_empty()
            || field_types != "named_keyword_type_expressions"
            || !names.insert(name.as_str())
        {
            return None;
        }
        let kind = match (kind.as_str(), validator.as_str()) {
            ("builtin_record", "none") => StarlarkGlobalKind::Record,
            ("record_with_validator", "first_positional_callable") => {
                StarlarkGlobalKind::RecordWithValidator
            }
            _ => return None,
        };
        declarations.push(StarlarkGlobalDeclaration {
            name: Name::new(name),
            kind,
        });
    }
    for function in host_functions {
        let StarHostFunction {
            name,
            params,
            returns,
            availability,
        } = function;
        if name.is_empty() || !names.insert(name.as_str()) {
            return None;
        }
        let return_type = host_type(returns)?;
        let availability = match availability.as_str() {
            "any_module" => StarlarkAvailability::AnyModule,
            "loaded_module_initialization" => StarlarkAvailability::LoadedModuleInitialization,
            _ => return None,
        };
        let mut parameters = Vec::with_capacity(params.len());
        let mut parameter_names = HashSet::new();
        let mut previous_mode = 0;
        let mut optional_positional = false;
        for parameter in params {
            let StarHostParam {
                name,
                mode,
                required,
                ty,
            } = parameter;
            let (order, mode) = match mode.as_str() {
                "pos_only" => (0, StarlarkParameterMode::PositionalOnly),
                "pos_or_named" => (1, StarlarkParameterMode::PositionalOrKeyword),
                "named_only" => (2, StarlarkParameterMode::KeywordOnly),
                _ => return None,
            };
            if name.is_empty()
                || !parameter_names.insert(name.as_str())
                || order < previous_mode
                || order != 2 && optional_positional && *required
            {
                return None;
            }
            let ty = host_type(ty)?;
            if order != 2 && !*required {
                optional_positional = true;
            }
            previous_mode = order;
            parameters.push(StarlarkParameter {
                name: Name::new(name),
                mode,
                ty,
                required: *required,
            });
        }
        declarations.push(StarlarkGlobalDeclaration {
            name: Name::new(name),
            kind: StarlarkGlobalKind::Native {
                parameters: parameters.into_boxed_slice(),
                return_type,
                availability,
            },
        });
    }
    Some(declarations.into_boxed_slice())
}

fn host_type(ty: &str) -> Option<StarlarkType> {
    Some(match ty {
        "any" => StarlarkType::Any,
        "bool" => StarlarkType::Bool,
        "int" => StarlarkType::Int,
        "str" => StarlarkType::Str,
        "callable" => StarlarkType::Callable,
        "unknown" => StarlarkType::Unknown,
        _ => return None,
    })
}

fn parse_star_source(source: &StarSource) -> Result<Box<[TextRange]>, StarFailure> {
    let StarSource { file, text, loads } = source;
    // The host profile enables type syntax and top-level statements. Ruff's
    // fixed shared parser admits only their overlapping syntax, never Python
    // project configuration or the Bazel source admission profile.
    let options = ParseOptions::from(Mode::Module).with_target_version(PythonVersion::PY310);
    let parsed = parse_unchecked(text, options);
    let Some(parsed) = parsed.try_into_module() else {
        return Err(StarFailure::at(*file, None, StarFailureReason::NonModule));
    };
    let parser_error = parsed
        .errors()
        .iter()
        .min_by_key(|error| error.range().start());
    let version_error = parsed
        .unsupported_syntax_errors()
        .iter()
        .min_by_key(|error| error.range().start());
    if let Some(error) = parser_error
        && version_error.is_none_or(|other| error.range().start() <= other.range().start())
    {
        return Err(StarFailure::at(
            *file,
            Some(error.range()),
            StarFailureReason::Parser(error.clone()),
        ));
    }
    if let Some(error) = version_error {
        return Err(StarFailure::at(
            *file,
            Some(error.range()),
            StarFailureReason::PythonVersion(error.clone()),
        ));
    }
    let ranges = validate_direct_loads(*file, parsed.suite(), loads)?;
    let mut aliases = HashSet::new();
    for load in loads {
        for binding in &load.bindings {
            if !aliases.insert(binding.local.as_str()) {
                return Err(StarFailure::at(
                    *file,
                    Some(load.label_range),
                    StarFailureReason::LoadMismatch,
                ));
            }
        }
    }
    Ok(ranges)
}
fn validate_direct_loads(
    file: File,
    suite: &[Stmt],
    declared: &[StarDirectLoad],
) -> Result<Box<[TextRange]>, StarFailure> {
    let mut observed = Vec::new();
    for statement in suite {
        let Stmt::Expr(expr_stmt) = statement else {
            continue;
        };
        let Expr::Call(call) = expr_stmt.value.as_ref() else {
            continue;
        };
        let Expr::Name(callee) = call.func.as_ref() else {
            continue;
        };
        if callee.id != "load" {
            continue;
        }
        let Some(Expr::StringLiteral(module)) = call.arguments.args.first() else {
            return Err(StarFailure::at(
                file,
                Some(call.range()),
                StarFailureReason::LoadMismatch,
            ));
        };
        let mut bindings = Vec::new();
        for binding in call.arguments.iter_source_order().skip(1) {
            let (source, local) = match binding {
                ast::ArgOrKeyword::Arg(Expr::StringLiteral(name)) => {
                    (name.value.to_str(), name.value.to_str())
                }
                ast::ArgOrKeyword::Keyword(keyword) => {
                    let Expr::StringLiteral(name) = &keyword.value else {
                        return Err(StarFailure::at(
                            file,
                            Some(keyword.range()),
                            StarFailureReason::LoadMismatch,
                        ));
                    };
                    let Some(alias) = &keyword.arg else {
                        return Err(StarFailure::at(
                            file,
                            Some(keyword.range()),
                            StarFailureReason::LoadMismatch,
                        ));
                    };
                    (name.value.to_str(), alias.as_str())
                }
                ast::ArgOrKeyword::Arg(other) => {
                    return Err(StarFailure::at(
                        file,
                        Some(other.range()),
                        StarFailureReason::LoadMismatch,
                    ));
                }
            };
            bindings.push((local.to_string(), source.to_string()));
        }
        observed.push((
            module.value.to_str().to_string(),
            module.range(),
            bindings,
            call.range(),
        ));
    }
    if observed.len() != declared.len() {
        return Err(StarFailure::at(file, None, StarFailureReason::LoadMismatch));
    }
    for ((module_id, range, bindings, _call_range), load) in observed.iter().zip(declared) {
        let StarDirectLoad {
            module_id: declared_id,
            label_range,
            bindings: declared_bindings,
        } = load;
        if module_id != declared_id
            || range != label_range
            || bindings.len() != declared_bindings.len()
            || bindings
                .iter()
                .zip(declared_bindings)
                .any(|((local, source), declared)| {
                    local != &declared.local || source != &declared.source
                })
        {
            return Err(StarFailure::at(
                file,
                Some(*label_range),
                StarFailureReason::LoadMismatch,
            ));
        }
    }
    Ok(observed.into_iter().map(|(_, _, _, range)| range).collect())
}

#[cfg(test)]
mod tests;
