//! Bazel load discovery and admission followed by shared Ty analysis.

use std::collections::{HashMap, HashSet, VecDeque, hash_map::Entry};

use ruff_db::Db;
use ruff_db::diagnostic::{Annotation, Diagnostic, DiagnosticId, Severity, Span};
use ruff_db::files::{File, FileRange};
use ruff_db::source::source_text;
use ruff_python_ast::name::Name;
use ruff_source_file::SourceFileBuilder;
use ruff_text_size::{Ranged, TextRange};
use salsa::Setter;
use ty_python_core::ProgramFile;
use ty_python_core::starlark::{
    StarlarkEnvironment, StarlarkGlobalDeclaration, StarlarkGlobalKind, StarlarkLoad,
    StarlarkModule, StarlarkModuleRole,
};

use crate::analysis::{Analysis, AnalysisDb, StarlarkProfile};
use crate::bazel::{BazelLoadError, resolve_bazel_load};
use crate::loads::{
    BazelLoadPlan, BazelLoadPlanError, BazelLoadPlanFailure, plan_bazel_loads, recover_bazel_loads,
};
use crate::source::{BazelSource, BazelSourceKind};
use crate::stub::{
    BazelStubAdmission, BazelStubDeclarations, BazelStubError, BazelStubFailure, admit_bazel_stub,
};

#[derive(Clone, Debug)]
pub struct BazelGraphFailure {
    file: File,
    range: Option<TextRange>,
    related: Option<(File, Option<TextRange>)>,
    reason: BazelGraphError,
}

impl BazelGraphFailure {
    fn at(file: File, range: Option<TextRange>, reason: BazelGraphError) -> Self {
        Self {
            file,
            range,
            related: None,
            reason,
        }
    }

    fn related(mut self, file: File, range: Option<TextRange>) -> Self {
        self.related = Some((file, range));
        self
    }

    fn analysis(file: File, error: &anyhow::Error) -> Self {
        Self::at(file, None, BazelGraphError::Analysis(error.to_string()))
    }

    fn message(&self) -> String {
        match &self.reason {
            BazelGraphError::LoadPlan(failure) => match failure.reason() {
                BazelLoadPlanError::Admission(admission) => admission.reason().to_string(),
                reason => reason.to_string(),
            },
            BazelGraphError::Stub(failure) => match failure.reason() {
                BazelStubError::Source(admission) => admission.reason().to_string(),
                reason => {
                    let message = reason.to_string();
                    if failure.file().is_none()
                        && let Some(path) = failure.path()
                    {
                        format!("{message}: {path}")
                    } else {
                        message
                    }
                }
            },
            reason => reason.to_string(),
        }
    }

    pub fn diagnostic(&self) -> Diagnostic {
        let mut diagnostic = Diagnostic::new(
            DiagnosticId::lint("unsupported-starlark"),
            Severity::Error,
            self.message(),
        );
        diagnostic.annotate(Annotation::primary(
            Span::from(self.file).with_optional_range(self.range),
        ));
        if let Some((file, range)) = self.related {
            diagnostic.annotate(
                Annotation::secondary(Span::from(file).with_optional_range(range))
                    .message("related source"),
            );
        } else if let BazelGraphError::LoadPlan(failure) = &self.reason
            && let Some(range) = failure.related_range()
        {
            diagnostic.annotate(
                Annotation::secondary(Span::from(self.file).with_range(range))
                    .message("first bound at"),
            );
        }
        diagnostic
    }
}

impl std::fmt::Display for BazelGraphFailure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.message())
    }
}
impl std::error::Error for BazelGraphFailure {}

#[derive(Clone, Debug, thiserror::Error)]
enum BazelGraphError {
    #[error("selected Bazel sources belong to different main repositories")]
    MixedRepositories,
    #[error("the Bazel load plan is opaque")]
    LoadPlan(Box<BazelLoadPlanFailure>),
    #[error("cannot resolve the Bazel load target: {0}")]
    Resolution(BazelLoadError),
    #[error("the loaded runtime target is opaque")]
    Dependency,
    #[error("the sibling .bzl.pyi declaration cannot be applied")]
    Stub(Box<BazelStubFailure>),
    #[error("Bazel load graph contains a cycle")]
    Cycle,
    #[error("cannot prepare Starlark analysis: {0}")]
    Analysis(String),
}

struct PendingGraphNode<'db> {
    file: File,
    source: BazelSource<'db>,
    edges: Vec<BazelGraphEdge>,
    declarations: Option<&'db BazelStubDeclarations>,
    failure: Option<BazelGraphFailure>,
}

struct BazelGraphEdge {
    target: usize,
    range: TextRange,
    label_range: TextRange,
}

/// All source, sibling-stub, package and repository reads use the outer database's
/// tracked filesystem. Each invocation checks a captured graph; diagnostics from
/// Ty own their snapshots before its analysis database is released.
pub fn check_bazel_graph<'db>(
    db: &'db dyn Db,
    selections: &[BazelSource<'db>],
) -> Result<Vec<Diagnostic>, BazelGraphFailure> {
    analyze_bazel_graph(db, selections).map(|(diagnostics, _)| diagnostics)
}

/// Strict diagnostics together with the admitted graph used to produce them.
pub fn analyze_bazel_graph<'db>(
    db: &'db dyn Db,
    selections: &[BazelSource<'db>],
) -> Result<(Vec<Diagnostic>, Option<Analysis>), BazelGraphFailure> {
    build_graph(db, selections, false)
}

/// A partial graph for editor queries only. No recovery diagnostics are exposed.
pub fn recover_bazel_graph<'db>(
    db: &'db dyn Db,
    selections: &[BazelSource<'db>],
) -> Result<Option<Analysis>, BazelGraphFailure> {
    build_graph(db, selections, true).map(|(_, analysis)| analysis)
}

fn build_graph<'db>(
    db: &'db dyn Db,
    selections: &[BazelSource<'db>],
    recovery: bool,
) -> Result<(Vec<Diagnostic>, Option<Analysis>), BazelGraphFailure> {
    let Some(first) = selections.first() else {
        return Ok((Vec::new(), None));
    };
    let first_file = first.selected_file(db);
    let repository = first.selected_repository(db);
    for source in selections.iter().skip(1) {
        if source.selected_repository(db) != repository {
            return Err(BazelGraphFailure::at(
                source.selected_file(db),
                None,
                BazelGraphError::MixedRepositories,
            ));
        }
    }
    let selected: HashSet<_> = selections
        .iter()
        .map(|source| source.selected_file(db))
        .collect();
    let mut pending = Vec::new();
    let mut index = HashMap::new();
    let mut discover = VecDeque::new();
    for source in selections {
        let file = source.selected_file(db);
        if let Entry::Vacant(entry) = index.entry(file) {
            entry.insert(pending.len());
            pending.push(PendingGraphNode {
                source: *source,
                file,
                edges: Vec::new(),
                declarations: None,
                failure: None,
            });
            discover.push_back(pending.len() - 1);
        }
    }
    while let Some(node_index) = discover.pop_front() {
        let file = pending[node_index].file;
        let source = pending[node_index].source;
        let mut edges = Vec::new();
        let mut failure = None;
        let recovered;
        let plan = if recovery {
            recovered = recover_bazel_loads(db, source);
            &recovered
        } else {
            plan_bazel_loads(db, source)
        };
        match plan {
            BazelLoadPlan::NoLoads => {}
            BazelLoadPlan::Opaque(problem) => {
                failure = Some(BazelGraphFailure::at(
                    problem.file(),
                    problem.range(),
                    BazelGraphError::LoadPlan(Box::new(problem.clone())),
                ));
            }
            BazelLoadPlan::Pending(loads) => {
                for load in loads.as_ref() {
                    let target = match resolve_bazel_load(db, repository, file, load.label()) {
                        Ok(target) => target,
                        Err(error) => {
                            if recovery {
                                continue;
                            }
                            failure = Some(BazelGraphFailure::at(
                                file,
                                Some(load.label_range()),
                                BazelGraphError::Resolution(error),
                            ));
                            break;
                        }
                    };
                    let target_file = target.selected_file(db);
                    let target_index = match index.entry(target_file) {
                        Entry::Occupied(entry) => *entry.get(),
                        Entry::Vacant(entry) => {
                            let next = pending.len();
                            entry.insert(next);
                            pending.push(PendingGraphNode {
                                source: target,
                                file: target_file,
                                edges: Vec::new(),
                                declarations: None,
                                failure: None,
                            });
                            discover.push_back(next);
                            next
                        }
                    };
                    edges.push(BazelGraphEdge {
                        target: target_index,
                        range: load.range(),
                        label_range: load.label_range(),
                    });
                }
            }
        }
        if failure.is_none() && source.kind(db) == BazelSourceKind::Extension {
            match admit_bazel_stub(db, source) {
                BazelStubAdmission::Absent => {}
                BazelStubAdmission::Admitted(declarations) => {
                    pending[node_index].declarations = Some(declarations);
                }
                BazelStubAdmission::Opaque(problem) => {
                    if !recovery {
                        let mut error = BazelGraphFailure::at(
                            problem.file().unwrap_or(file),
                            problem.range(),
                            BazelGraphError::Stub(Box::new(problem.clone())),
                        );
                        if let Some(related) = problem.related() {
                            error = error.related(related.file(), Some(related.range()));
                        }
                        failure = Some(error);
                    }
                }
            }
        }
        if failure.is_some() {
            edges.clear();
        }
        pending[node_index].edges = edges;
        pending[node_index].failure = failure;
    }

    let mut reverse = vec![Vec::new(); pending.len()];
    let mut unresolved: Vec<_> = pending.iter().map(|node| node.edges.len()).collect();
    for (importer, node) in pending.iter().enumerate() {
        for edge in &node.edges {
            reverse[edge.target].push(importer);
        }
    }
    let mut outcomes: Vec<Option<Result<(), BazelGraphFailure>>> =
        (0..pending.len()).map(|_| None).collect();
    let mut ready: VecDeque<_> = unresolved
        .iter()
        .enumerate()
        .filter_map(|(index, remaining)| (*remaining == 0).then_some(index))
        .collect();
    peel_nodes(
        &pending,
        &reverse,
        &mut unresolved,
        &mut outcomes,
        &mut ready,
    );
    if outcomes.iter().any(Option::is_none) {
        let membership = cycle_membership(&pending, &reverse, &outcomes);
        for (node_index, component) in membership.iter().enumerate() {
            let Some(component) = component else {
                continue;
            };
            let node = &pending[node_index];
            let range = node
                .edges
                .iter()
                .find(|edge| membership[edge.target] == Some(*component))
                .map(|edge| edge.label_range);
            complete_node(
                node_index,
                Err(BazelGraphFailure::at(
                    node.file,
                    range,
                    BazelGraphError::Cycle,
                )),
                &reverse,
                &mut unresolved,
                &mut outcomes,
                &mut ready,
            );
        }
        peel_nodes(
            &pending,
            &reverse,
            &mut unresolved,
            &mut outcomes,
            &mut ready,
        );
    }

    if recovery {
        // Invalid dependencies prevent checking, but do not erase a valid
        // importer's local names from editor queries.
        for (node, outcome) in pending.iter().zip(&mut outcomes) {
            if node.failure.is_none() {
                *outcome = Some(Ok(()));
            }
        }
    }
    let mut analysis = AnalysisDb::new(StarlarkProfile::Bazel)
        .map_err(|error| BazelGraphFailure::analysis(first_file, &error))?;
    let mut inputs = Vec::new();
    for (index, node) in pending.iter().enumerate() {
        if !matches!(outcomes[index], Some(Ok(()))) {
            continue;
        }
        let source = source_text(db, node.file);
        let file = analysis
            .add_source(
                SourceFileBuilder::new(node.file.path(db).as_str(), source.as_str()).finish(),
            )
            .map_err(|error| BazelGraphFailure::analysis(node.file, &error))?;
        let mut annotations = Box::default();
        if let Some(declarations) = node.declarations {
            let original = declarations.file();
            let text = source_text(db, original);
            let stub = analysis
                .add_source(
                    SourceFileBuilder::new(original.path(db).as_str(), text.as_str()).finish(),
                )
                .map_err(|error| BazelGraphFailure::analysis(original, &error))?;
            annotations = declarations.annotations().to_vec().into_boxed_slice();
            for function in &mut annotations {
                for parameter in &mut function.parameters {
                    parameter.annotation.origin =
                        FileRange::new(stub, parameter.annotation.origin.range());
                }
                if let Some(annotation) = &mut function.returns {
                    annotation.origin = FileRange::new(stub, annotation.origin.range());
                }
            }
        }
        inputs.push((index, file, annotations));
    }
    let struct_global = StarlarkGlobalDeclaration {
        name: Name::new("struct"),
        kind: StarlarkGlobalKind::Struct,
    };
    let extension_environment = StarlarkEnvironment::new(
        &analysis,
        Box::new([struct_global, bazel_builtin("select")]),
    );
    let mut build_globals = vec![bazel_builtin("select")];
    for name in ["glob", "package", "exports_files", "filegroup", "genrule"] {
        build_globals.push(bazel_builtin(name));
    }
    let build_environment = StarlarkEnvironment::new(&analysis, build_globals.into_boxed_slice());
    let mut modules = vec![None; pending.len()];
    for (index, file, annotations) in inputs {
        let node = &pending[index];
        let role = if selected.contains(&node.file) {
            StarlarkModuleRole::Root
        } else {
            StarlarkModuleRole::Loaded
        };
        modules[index] = Some(StarlarkModule::new(
            &analysis,
            file,
            Name::new(node.file.path(db).as_str()),
            Box::default(),
            annotations,
            Some(match node.source.kind(db) {
                BazelSourceKind::Build => build_environment,
                BazelSourceKind::Extension => extension_environment,
            }),
            role,
        ));
    }
    for (index, module) in modules.iter().enumerate() {
        let Some(module) = module else {
            continue;
        };
        let loads = pending[index]
            .edges
            .iter()
            .filter(|edge| !recovery || modules[edge.target].is_some())
            .map(|edge| {
                let target = modules[edge.target].ok_or_else(|| {
                    BazelGraphFailure::analysis(
                        pending[index].file,
                        &anyhow::anyhow!("admitted load has no semantic module"),
                    )
                })?;
                Ok(StarlarkLoad {
                    range: edge.range,
                    module: target,
                })
            })
            .collect::<Result<_, BazelGraphFailure>>()?;
        module.set_loads(&mut analysis).to(loads);
    }
    let program = analysis.program();
    let mut checked = Vec::new();
    let mut admission = Vec::new();
    for (index, node) in pending.iter().enumerate() {
        match &outcomes[index] {
            Some(Ok(())) => {
                let module = modules[index].ok_or_else(|| {
                    BazelGraphFailure::analysis(
                        node.file,
                        &anyhow::anyhow!("admitted source has no semantic module"),
                    )
                })?;
                if !recovery {
                    checked.extend(ty_python_semantic::check_file_unwrap(
                        &analysis,
                        ProgramFile::new_starlark(&analysis, module, program),
                    ));
                }
            }
            Some(Err(failure)) => admission.push(failure.diagnostic()),
            None => {
                return Err(BazelGraphFailure::analysis(
                    node.file,
                    &anyhow::anyhow!("load graph admission did not complete"),
                ));
            }
        }
    }
    // Only semantic annotations belong to the inner database. Admission errors
    // still refer to outer files, so freeze semantic results before combining them.
    analysis
        .freeze(&mut checked)
        .map_err(|error| BazelGraphFailure::analysis(first_file, &error))?;
    checked.extend(admission);
    let build_files = pending
        .iter()
        .zip(&modules)
        .filter_map(|(node, module)| {
            (node.source.kind(db) == BazelSourceKind::Build)
                .then(|| module.map(|module| module.file(&analysis)))
                .flatten()
        })
        .collect();
    let modules = modules.into_iter().flatten().collect();
    Ok((checked, Some(Analysis::new(analysis, modules, build_files))))
}

fn bazel_builtin(name: &str) -> StarlarkGlobalDeclaration {
    StarlarkGlobalDeclaration {
        name: Name::new(name),
        kind: StarlarkGlobalKind::Builtin {
            symbol: Name::new(name),
        },
    }
}

fn peel_nodes(
    pending: &[PendingGraphNode<'_>],
    reverse: &[Vec<usize>],
    unresolved: &mut [usize],
    outcomes: &mut [Option<Result<(), BazelGraphFailure>>],
    ready: &mut VecDeque<usize>,
) {
    while let Some(index) = ready.pop_front() {
        if outcomes[index].is_some() {
            continue;
        }
        let node = &pending[index];
        let mut failure = node.failure.clone();
        if failure.is_none() {
            for edge in &node.edges {
                if let Some(Err(problem)) = &outcomes[edge.target] {
                    failure = Some(
                        BazelGraphFailure::at(
                            node.file,
                            Some(edge.label_range),
                            BazelGraphError::Dependency,
                        )
                        .related(problem.file, problem.range),
                    );
                    break;
                }
            }
        }
        complete_node(
            index,
            failure.map_or(Ok(()), Err),
            reverse,
            unresolved,
            outcomes,
            ready,
        );
    }
}

fn complete_node(
    index: usize,
    outcome: Result<(), BazelGraphFailure>,
    reverse: &[Vec<usize>],
    unresolved: &mut [usize],
    outcomes: &mut [Option<Result<(), BazelGraphFailure>>],
    ready: &mut VecDeque<usize>,
) {
    outcomes[index] = Some(outcome);
    for &importer in &reverse[index] {
        unresolved[importer] -= 1;
        if unresolved[importer] == 0 && outcomes[importer].is_none() {
            ready.push_back(importer);
        }
    }
}

/// Iterative Kosaraju pass over residual nodes. Only actual SCCs become
/// cycles; the Kahn peel then marks their importers as opaque dependencies.
fn cycle_membership(
    pending: &[PendingGraphNode<'_>],
    reverse: &[Vec<usize>],
    outcomes: &[Option<Result<(), BazelGraphFailure>>],
) -> Vec<Option<usize>> {
    let active: Vec<_> = outcomes.iter().map(Option::is_none).collect();
    let mut visited = vec![false; pending.len()];
    let mut finished = Vec::new();
    for start in 0..pending.len() {
        if !active[start] || visited[start] {
            continue;
        }
        visited[start] = true;
        let mut stack = vec![(start, 0)];
        while let Some((current, next_edge)) = stack.last_mut() {
            if let Some(edge) = pending[*current].edges.get(*next_edge) {
                *next_edge += 1;
                if active[edge.target] && !visited[edge.target] {
                    visited[edge.target] = true;
                    stack.push((edge.target, 0));
                }
            } else {
                finished.push(*current);
                stack.pop();
            }
        }
    }
    visited.fill(false);
    let mut membership = vec![None; pending.len()];
    for start in finished.into_iter().rev() {
        if visited[start] {
            continue;
        }
        let mut component = Vec::new();
        let mut stack = vec![start];
        visited[start] = true;
        while let Some(node) = stack.pop() {
            component.push(node);
            for &importer in &reverse[node] {
                if active[importer] && !visited[importer] {
                    visited[importer] = true;
                    stack.push(importer);
                }
            }
        }
        let cyclic =
            component.len() > 1 || pending[start].edges.iter().any(|edge| edge.target == start);
        if cyclic {
            let id = start;
            for member in component {
                membership[member] = Some(id);
            }
        }
    }
    membership
}

#[cfg(test)]
mod tests;
