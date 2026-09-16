//! Diagnostics shared by the command and editor reporters.

use std::collections::HashMap;
use std::collections::hash_map::Entry;
use std::io::{self, Write};

use anyhow::{Result, anyhow};
use ruff_db::Db;
use ruff_db::diagnostic::{
    Annotation, Diagnostic, DiagnosticId, DisplayDiagnosticConfig, DisplayDiagnostics, Severity,
    Span,
};
use ruff_db::files::File;
use ruff_source_file::{SourceFile, SourceFileBuilder};
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
use ty_starlark::star::{StarCheck, StarResolvedGraph};
use ty_starlark::stub::BazelStubError;

pub(crate) fn report(db: &dyn Db, diagnostics: &[Diagnostic]) -> io::Result<()> {
    write!(
        io::stderr().lock(),
        "{}",
        DisplayDiagnostics::new(&db, &DisplayDiagnosticConfig::new("sty"), diagnostics)
    )
}

fn diagnostic(id: &'static str, message: impl std::fmt::Display, span: Span) -> Diagnostic {
    let mut diagnostic = Diagnostic::new(DiagnosticId::lint(id), Severity::Error, message);
    diagnostic.annotate(Annotation::primary(span));
    diagnostic
}

fn arity(problem: &BazelCheckProblem) -> Diagnostic {
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
    let mut diagnostic = diagnostic(
        "invalid-argument-count",
        message,
        Span::from(problem.file()).with_range(problem.range()),
    );
    diagnostic.annotate(
        Annotation::secondary(
            Span::from(problem.declaration_file()).with_range(problem.declaration_range()),
        )
        .message("declared at"),
    );
    diagnostic
}

fn typed(problem: &BazelTypedCallProblem) -> Diagnostic {
    let mut diagnostic = diagnostic(
        "invalid-argument-type",
        problem.reason(),
        Span::from(problem.file()).with_range(problem.range()),
    );
    diagnostic.annotate(
        Annotation::secondary(
            Span::from(problem.related_file()).with_range(problem.related_range()),
        )
        .message("declared at"),
    );
    diagnostic
}

pub(crate) fn bazel_failure(failure: &BazelGraphFailure) -> Diagnostic {
    let mut diagnostic = diagnostic(
        "unsupported-starlark",
        graph_message(failure.reason()),
        Span::from(failure.file()).with_optional_range(failure.range()),
    );
    let related = if let Some(file) = failure.related_file() {
        Some(
            Annotation::secondary(Span::from(file).with_optional_range(failure.related_range()))
                .message("related source"),
        )
    } else {
        related_load_range(failure.reason()).map(|range| {
            Annotation::secondary(Span::from(failure.file()).with_range(range))
                .message("first bound at")
        })
    };
    if let Some(related) = related {
        diagnostic.annotate(related);
    }
    diagnostic
}

pub(crate) fn bazel_diagnostics(graph: &BazelCheckedGraph) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();
    for node in graph.nodes() {
        match node.outcome() {
            BazelGraphOutcome::Checked(module) => {
                diagnostics.extend(module.problems().iter().map(arity));
                diagnostics.extend(module.typed_problems().iter().map(typed));
            }
            BazelGraphOutcome::Opaque(failure) => diagnostics.push(bazel_failure(failure)),
        }
    }
    diagnostics
}

/// Host diagnostics own their source snapshots. Rendering never reopens the
/// corresponding disk file, whose text may differ from the checked graph.
pub(crate) fn star_diagnostics(
    db: &dyn Db,
    graph: &StarResolvedGraph,
    check: &StarCheck,
) -> Result<Vec<Diagnostic>> {
    let failure = match check {
        StarCheck::Checked(checked) => return Ok(checked.clone()),
        StarCheck::Opaque(failure) => failure,
    };
    let mut sources: HashMap<File, (&str, Option<SourceFile>)> = HashMap::new();
    for source in
        std::iter::once(&graph.root).chain(graph.modules.iter().map(|module| &module.source))
    {
        match sources.entry(source.file) {
            Entry::Vacant(entry) => {
                entry.insert((source.text.as_str(), None));
            }
            Entry::Occupied(entry) => {
                if entry.get().0 != source.text {
                    return Err(anyhow!(
                        "host supplied conflicting source snapshots for {}",
                        source.file.path(db)
                    ));
                }
            }
        }
    }
    let mut span = |file, range: Option<TextRange>| -> Result<Span> {
        let (text, captured) = sources
            .get_mut(&file)
            .ok_or_else(|| anyhow!("host source graph omitted a diagnostic source"))?;
        if let Some(range) = range
            && text
                .get(range.start().to_usize()..range.end().to_usize())
                .is_none()
        {
            return Err(anyhow!(
                "host source graph supplied an invalid diagnostic span"
            ));
        }
        let captured = captured
            .get_or_insert_with(|| SourceFileBuilder::new(file.path(db).as_str(), *text).finish());
        Ok(Span::from(captured.clone()).with_optional_range(range))
    };
    let mut diagnostics = Vec::new();
    let primary = span(failure.file(), failure.range())?;
    diagnostics.push(diagnostic(
        "unsupported-starlark",
        failure.reason(),
        primary.clone(),
    ));
    if graph.root.file != failure.file() {
        let root = span(graph.root.file, None)?;
        let mut blocked = diagnostic(
            "unsupported-starlark",
            format!(
                "cannot check the .star root because a loaded source is opaque: {}",
                failure.reason()
            ),
            root,
        );
        blocked.annotate(Annotation::secondary(primary).message("loaded source is opaque"));
        diagnostics.push(blocked);
    }
    Ok(diagnostics)
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
