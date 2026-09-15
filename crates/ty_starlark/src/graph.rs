//! Source-first checks across the selected main Bazel repository.
//!
//! Discover runtime sources once, then check targets before importers. Cycles
//! never enter recursive Salsa queries, and an opaque target cannot supply a
//! typed file-block binding even when it has a Ty-only sibling stub.

use std::collections::{HashMap, VecDeque, hash_map::Entry};

use ruff_db::Db;
use ruff_db::files::File;
use ruff_text_size::TextRange;

use crate::bazel::{BazelLoadError, resolve_bazel_load};
use crate::imports::bind_resolved_imports_with;
pub use crate::imports::{BazelResolvedImportError, BazelResolvedImportFailure};
use crate::loads::{BazelLoadPlan, BazelLoadPlanFailure, plan_bazel_loads};
use crate::overlay::{
    BazelVerificationFailure, BazelVerifiedModule, BazelVerifiedSource, verify_bazel_source,
    verify_resolved_importer,
};
use crate::source::BazelSource;

/// One invocation can check several selected `.bzl` sources in one repository.
/// Discovered dependencies are included so their original problems are visible.
#[derive(Debug)]
pub struct BazelCheckedGraph {
    selected: Box<[File]>,
    nodes: Box<[BazelGraphNode]>,
    index: HashMap<File, usize>,
}

impl BazelCheckedGraph {
    pub fn selected(&self) -> &[File] {
        &self.selected
    }

    pub fn nodes(&self) -> &[BazelGraphNode] {
        &self.nodes
    }

    pub fn node(&self, file: File) -> Option<&BazelGraphNode> {
        self.index
            .get(&file)
            .and_then(|index| self.nodes.get(*index))
    }
}

#[derive(Debug)]
pub struct BazelGraphNode {
    file: File,
    outcome: BazelGraphOutcome,
}

impl BazelGraphNode {
    pub fn file(&self) -> File {
        self.file
    }

    pub fn outcome(&self) -> &BazelGraphOutcome {
        &self.outcome
    }
}

#[derive(Debug)]
pub enum BazelGraphOutcome {
    Checked(BazelVerifiedModule),
    Opaque(BazelGraphFailure),
}

/// The importer owns its own load error; a failed target remains separately
/// available at `BazelCheckedGraph::node` without copying an entire failure
/// chain for every dependent file.
#[derive(Clone, Debug, get_size2::GetSize)]
pub struct BazelGraphFailure {
    file: File,
    range: Option<TextRange>,
    related_file: Option<File>,
    related_range: Option<TextRange>,
    reason: BazelGraphError,
}

impl BazelGraphFailure {
    fn at(file: File, range: Option<TextRange>, reason: BazelGraphError) -> Self {
        Self {
            file,
            range,
            related_file: None,
            related_range: None,
            reason,
        }
    }

    fn related(mut self, file: File, range: Option<TextRange>) -> Self {
        self.related_file = Some(file);
        self.related_range = range;
        self
    }

    fn verification(runtime_file: File, failure: &BazelVerificationFailure) -> Self {
        let mut result = Self::at(
            failure.file().unwrap_or(runtime_file),
            failure.range(),
            BazelGraphError::Source(Box::new(failure.clone())),
        );
        if let Some(file) = failure.related_file() {
            result = result.related(file, failure.related_range());
        }
        result
    }

    pub fn file(&self) -> File {
        self.file
    }

    pub fn range(&self) -> Option<TextRange> {
        self.range
    }

    pub fn related_file(&self) -> Option<File> {
        self.related_file
    }

    pub fn related_range(&self) -> Option<TextRange> {
        self.related_range
    }

    pub fn reason(&self) -> &BazelGraphError {
        &self.reason
    }
}

#[derive(Clone, Debug, get_size2::GetSize, thiserror::Error)]
pub enum BazelGraphError {
    #[error("selected .bzl sources belong to different main repositories")]
    MixedRepositories,
    #[error("the Bazel load plan is opaque")]
    LoadPlan(Box<BazelLoadPlanFailure>),
    #[error("cannot resolve the Bazel load target: {0}")]
    Resolution(BazelLoadError),
    #[error("the loaded runtime target is opaque")]
    Dependency(File),
    #[error("the checked Bazel load cannot bind a public runtime export")]
    Import(Box<BazelResolvedImportFailure>),
    #[error("the selected Bazel runtime source is opaque")]
    Source(Box<BazelVerificationFailure>),
    #[error("Bazel load graph contains a cycle")]
    Cycle,
}

struct PendingGraphNode<'db> {
    source: BazelSource<'db>,
    file: File,
    edges: Vec<BazelGraphEdge>,
    failure: Option<BazelGraphFailure>,
}

struct BazelGraphEdge {
    target: usize,
    label_range: TextRange,
}

/// Resolve repository-local loads and verify whole-source exports once per
/// runtime File in this immutable DB read. Ruff's tracked source, `FileStatus`,
/// package and marker queries are read anew on each graph invocation, so
/// source/BUILD/stub edits are observed by the next check in the same DB.
pub fn check_bazel_graph<'db>(
    db: &'db dyn Db,
    selections: &[BazelSource<'db>],
) -> Result<BazelCheckedGraph, BazelGraphFailure> {
    let Some(first) = selections.first() else {
        return Ok(BazelCheckedGraph {
            selected: Box::new([]),
            nodes: Box::new([]),
            index: HashMap::new(),
        });
    };
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
    let selected: Box<_> = selections
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
        match plan_bazel_loads(db, source) {
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
                            failure = Some(BazelGraphFailure::at(
                                file,
                                Some(load.label_range()),
                                BazelGraphError::Resolution(error),
                            ));
                            edges.clear();
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
                                failure: None,
                            });
                            discover.push_back(next);
                            next
                        }
                    };
                    edges.push(BazelGraphEdge {
                        target: target_index,
                        label_range: load.label_range(),
                    });
                }
            }
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
    let mut outcomes: Vec<Option<BazelGraphOutcome>> = (0..pending.len()).map(|_| None).collect();
    let mut ready: VecDeque<_> = unresolved
        .iter()
        .enumerate()
        .filter_map(|(index, remaining)| (*remaining == 0).then_some(index))
        .collect();
    peel_checked_nodes(
        db,
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
            let file = pending[node_index].file;
            let range = pending[node_index]
                .edges
                .iter()
                .find(|edge| membership[edge.target] == Some(*component))
                .map(|edge| edge.label_range);
            complete_node(
                node_index,
                BazelGraphOutcome::Opaque(BazelGraphFailure::at(
                    file,
                    range,
                    BazelGraphError::Cycle,
                )),
                &reverse,
                &mut unresolved,
                &mut outcomes,
                &mut ready,
            );
        }
        peel_checked_nodes(
            db,
            &pending,
            &reverse,
            &mut unresolved,
            &mut outcomes,
            &mut ready,
        );
    }

    let nodes = pending
        .into_iter()
        .zip(outcomes)
        .map(|(node, outcome)| BazelGraphNode {
            file: node.file,
            outcome: outcome.unwrap_or_else(|| {
                // A failed SCC classification may only reduce precision.
                BazelGraphOutcome::Opaque(BazelGraphFailure::at(
                    node.file,
                    node.edges.first().map(|edge| edge.label_range),
                    BazelGraphError::Cycle,
                ))
            }),
        })
        .collect();
    Ok(BazelCheckedGraph {
        selected,
        nodes,
        index,
    })
}

fn peel_checked_nodes(
    db: &dyn Db,
    pending: &[PendingGraphNode<'_>],
    reverse: &[Vec<usize>],
    unresolved: &mut [usize],
    outcomes: &mut [Option<BazelGraphOutcome>],
    ready: &mut VecDeque<usize>,
) {
    while let Some(node_index) = ready.pop_front() {
        if outcomes[node_index].is_some() {
            continue;
        }
        let outcome = check_node(db, &pending[node_index], pending, outcomes);
        complete_node(node_index, outcome, reverse, unresolved, outcomes, ready);
    }
}

fn complete_node(
    index: usize,
    outcome: BazelGraphOutcome,
    reverse: &[Vec<usize>],
    unresolved: &mut [usize],
    outcomes: &mut [Option<BazelGraphOutcome>],
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

fn check_node<'db>(
    db: &'db dyn Db,
    node: &PendingGraphNode<'db>,
    pending: &[PendingGraphNode<'db>],
    outcomes: &[Option<BazelGraphOutcome>],
) -> BazelGraphOutcome {
    let file = node.file;
    if let Some(failure) = &node.failure {
        return BazelGraphOutcome::Opaque(failure.clone());
    }
    if node.edges.is_empty() {
        return match verify_bazel_source(db, node.source) {
            BazelVerifiedSource::Checked(module) => BazelGraphOutcome::Checked(module.clone()),
            BazelVerifiedSource::Opaque(failure) => {
                BazelGraphOutcome::Opaque(BazelGraphFailure::verification(file, failure))
            }
        };
    }
    for edge in &node.edges {
        if let Some(BazelGraphOutcome::Opaque(failure)) = outcomes[edge.target].as_ref() {
            return BazelGraphOutcome::Opaque(
                BazelGraphFailure::at(
                    file,
                    Some(edge.label_range),
                    BazelGraphError::Dependency(pending[edge.target].file),
                )
                .related(failure.file(), failure.range()),
            );
        }
    }
    let checked: HashMap<_, _> = node
        .edges
        .iter()
        .filter_map(|edge| match &outcomes[edge.target] {
            Some(BazelGraphOutcome::Checked(module)) => Some((pending[edge.target].file, module)),
            _ => None,
        })
        .collect();
    let imports = match bind_resolved_imports_with(db, node.source, |source| {
        checked
            .get(&source.selected_file(db))
            .copied()
            .ok_or(BazelResolvedImportError::UnverifiedTarget)
    }) {
        Ok(imports) => imports,
        Err(failure) => {
            return BazelGraphOutcome::Opaque(
                BazelGraphFailure::at(
                    failure.file(),
                    failure.range(),
                    BazelGraphError::Import(Box::new(failure.clone())),
                )
                .related(
                    failure.related_file().unwrap_or(file),
                    failure.related_range(),
                ),
            );
        }
    };
    match verify_resolved_importer(db, node.source, &imports) {
        BazelVerifiedSource::Checked(module) => BazelGraphOutcome::Checked(module),
        BazelVerifiedSource::Opaque(failure) => {
            BazelGraphOutcome::Opaque(BazelGraphFailure::verification(file, &failure))
        }
    }
}

/// Iterative Kosaraju pass over residual nodes. Only actual SCCs become
/// cycles; the Kahn peel then marks their importers as opaque dependencies.
fn cycle_membership(
    pending: &[PendingGraphNode<'_>],
    reverse: &[Vec<usize>],
    outcomes: &[Option<BazelGraphOutcome>],
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
