//! Source-owned Bazel problems shared by the command and editor reporters.

use ruff_db::files::File;
use ruff_text_size::TextRange;
use ty_starlark::checker::{BazelCheckError, BazelCheckProblem};
use ty_starlark::graph::{
    BazelCheckedGraph, BazelGraphError, BazelGraphFailure, BazelGraphOutcome,
    BazelResolvedImportError,
};
use ty_starlark::loads::{BazelLoadPlanError, BazelLoadPlanFailure};
use ty_starlark::overlay::{
    BazelTypedCallProblem, BazelVerificationError, BazelVerificationFailure,
};
use ty_starlark::preflight::BazelPreflightError;
use ty_starlark::stub::BazelStubError;

pub(crate) struct SourceProblem {
    pub file: File,
    pub range: Option<TextRange>,
    pub message: String,
    pub related: Option<RelatedSource>,
}

pub(crate) struct RelatedSource {
    pub file: File,
    pub range: Option<TextRange>,
    pub label: &'static str,
}

impl SourceProblem {
    fn arity(problem: &BazelCheckProblem) -> Self {
        let message = match problem.reason() {
            BazelCheckError::InvalidArity {
                callee,
                minimum,
                maximum,
                actual,
            } => {
                if minimum == maximum {
                    let noun = if *minimum == 1 {
                        "argument"
                    } else {
                        "arguments"
                    };
                    format!("function '{callee}' expects {minimum} positional {noun}, got {actual}")
                } else {
                    problem.reason().to_string()
                }
            }
        };
        Self {
            file: problem.file(),
            range: Some(problem.range()),
            message,
            related: Some(RelatedSource {
                file: problem.declaration_file(),
                range: Some(problem.declaration_range()),
                label: "declared at",
            }),
        }
    }

    fn typed(problem: &BazelTypedCallProblem) -> Self {
        Self {
            file: problem.file(),
            range: Some(problem.range()),
            message: problem.reason().to_string(),
            related: Some(RelatedSource {
                file: problem.related_file(),
                range: Some(problem.related_range()),
                label: "declared at",
            }),
        }
    }

    pub(crate) fn opaque(failure: &BazelGraphFailure) -> Self {
        let related = if let Some(file) = failure.related_file() {
            Some(RelatedSource {
                file,
                range: failure.related_range(),
                label: "related:",
            })
        } else {
            related_load_range(failure.reason()).map(|range| RelatedSource {
                file: failure.file(),
                range: Some(range),
                label: "first bound at",
            })
        };
        Self {
            file: failure.file(),
            range: failure.range(),
            message: graph_message(failure.reason()),
            related,
        }
    }
}

pub(crate) fn bazel_problems(graph: &BazelCheckedGraph) -> Vec<SourceProblem> {
    let mut problems = Vec::new();
    for node in graph.nodes() {
        match node.outcome() {
            BazelGraphOutcome::Checked(module) => {
                problems.extend(module.problems().iter().map(SourceProblem::arity));
                problems.extend(module.typed_problems().iter().map(SourceProblem::typed));
            }
            BazelGraphOutcome::Opaque(failure) => problems.push(SourceProblem::opaque(failure)),
        }
    }
    problems
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

pub(crate) fn graph_message(reason: &BazelGraphError) -> String {
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
