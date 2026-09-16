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
use ty_starlark::star::{StarCheck, StarResolvedGraph};

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
