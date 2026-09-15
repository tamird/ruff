//! Admission of Bazel `.bzl` source through Ruff's shared Python parser.
//!
//! Starlark and Python have different grammars. The checker may inspect a
//! parsed source only when this module has admitted the entire file.

use ruff_db::Db;
use ruff_db::diagnostic::{Annotation, Diagnostic, DiagnosticId, Severity, Span};
use ruff_db::files::File;
use ruff_db::source::{SourceTextError, source_text};
use ruff_python_ast::visitor::Visitor;
use ruff_python_ast::{self as ast, CmpOp, Expr, ModModule, Number, PythonVersion, Stmt};
use ruff_python_parser::{
    Mode, ParseError, ParseOptions, Parsed, UnsupportedSyntaxError, parse_unchecked,
};
use ruff_text_size::{Ranged, TextRange};

use crate::bazel::{BazelLoadError, BazelRepository, validate_bazel_source};

/// A source file selected inside a particular main Bazel repository.
#[salsa::interned(heap_size = ruff_memory_usage::heap_size)]
pub struct BazelSource<'db> {
    repository: BazelRepository<'db>,
    file: File,
}

impl get_size2::GetSize for BazelSource<'_> {}

/// A full parse accepted within this admission gate's supported syntax subset.
/// A later checker must still validate loads, exports, and host type options.
#[derive(Debug, get_size2::GetSize)]
pub struct AdmittedBazelSource {
    parsed: Parsed<ModModule>,
}

impl AdmittedBazelSource {
    pub fn suite(&self) -> &[Stmt] {
        self.parsed.suite()
    }
}

/// No syntax information from an opaque source may be used for inference.
#[derive(Debug, get_size2::GetSize)]
pub enum BazelSourceAdmission {
    Admitted(AdmittedBazelSource),
    Opaque(BazelAdmissionFailure),
}

/// The first concrete reason an entire Bazel `.bzl` source cannot be checked.
#[derive(Debug, get_size2::GetSize)]
pub struct BazelAdmissionFailure {
    file: File,
    range: Option<TextRange>,
    reason: BazelAdmissionError,
}

impl BazelAdmissionFailure {
    pub fn file(&self) -> File {
        self.file
    }

    pub fn range(&self) -> Option<TextRange> {
        self.range
    }

    pub fn reason(&self) -> &BazelAdmissionError {
        &self.reason
    }

    /// Read failures and known Bazel-invalid syntax have stable diagnostic IDs.
    /// The selecting host reports ownership failures and shared-parser limits.
    pub fn diagnostic(&self) -> Option<Diagnostic> {
        let id = match &self.reason {
            BazelAdmissionError::InvalidSource(_) => return None,
            BazelAdmissionError::Read(_) => DiagnosticId::Io,
            BazelAdmissionError::PythonParser(_) => return None,
            BazelAdmissionError::PythonVersion(_) => return None,
            BazelAdmissionError::BazelSyntax(_) => DiagnosticId::InvalidSyntax,
        };
        let mut diagnostic = Diagnostic::new(id, Severity::Error, &self.reason);
        let span = Span::from(self.file).with_optional_range(self.range);
        diagnostic.annotate(Annotation::primary(span));
        Some(diagnostic)
    }
}

#[derive(Debug, get_size2::GetSize, thiserror::Error)]
pub enum BazelAdmissionError {
    #[error("cannot select this Bazel .bzl source: {0}")]
    InvalidSource(BazelLoadError),
    #[error("cannot read this Bazel .bzl source: {0}")]
    Read(SourceTextError),
    #[error("the shared Python parser cannot check this Starlark source: {0}")]
    PythonParser(ParseError),
    #[error("the shared Python parser cannot check this Starlark source: {0}")]
    PythonVersion(UnsupportedSyntaxError),
    #[error("Bazel .bzl files do not support {0}")]
    BazelSyntax(&'static str),
}

/// Parse and admit the whole selected `.bzl` source, or expose only its failure.
///
/// Admission does not follow loads or assert that the Python parser accepts all
/// valid Starlark source. Syntax rejection is a safety decision independent of
/// any future lint level or diagnostic suppression.
#[salsa::tracked(returns(ref), no_eq, heap_size=ruff_memory_usage::heap_size, lru=200)]
pub fn admit_bazel_source(db: &dyn Db, source: BazelSource<'_>) -> BazelSourceAdmission {
    let file = *source.file(db);
    if let Err(error) = validate_bazel_source(db, *source.repository(db), file) {
        return BazelSourceAdmission::Opaque(BazelAdmissionFailure {
            file,
            range: None,
            reason: BazelAdmissionError::InvalidSource(error),
        });
    }

    let text = source_text(db, file);
    if let Some(error) = text.read_error() {
        return BazelSourceAdmission::Opaque(BazelAdmissionFailure {
            file,
            range: None,
            reason: BazelAdmissionError::Read(error.clone()),
        });
    }

    // Starlark's supported syntax is host-specific. The fixed module and
    // version options deliberately never come from a Python project.
    let options = ParseOptions::from(Mode::Module).with_target_version(PythonVersion::PY310);
    let parsed = parse_unchecked(text.as_str(), options);
    let Some(parsed) = parsed.try_into_module() else {
        return BazelSourceAdmission::Opaque(BazelAdmissionFailure {
            file,
            range: None,
            reason: BazelAdmissionError::BazelSyntax("a non-module parse result"),
        });
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
        return BazelSourceAdmission::Opaque(BazelAdmissionFailure {
            file,
            range: Some(error.range()),
            reason: BazelAdmissionError::PythonParser(error.clone()),
        });
    }
    if let Some(error) = version_error {
        return BazelSourceAdmission::Opaque(BazelAdmissionFailure {
            file,
            range: Some(error.range()),
            reason: BazelAdmissionError::PythonVersion(error.clone()),
        });
    }

    let mut syntax = BazelSyntax::new(text.as_str());
    syntax.visit_body(parsed.suite());
    if let Some((range, description)) = syntax.first_failure {
        return BazelSourceAdmission::Opaque(BazelAdmissionFailure {
            file,
            range: Some(range),
            reason: BazelAdmissionError::BazelSyntax(description),
        });
    }

    BazelSourceAdmission::Admitted(AdmittedBazelSource { parsed })
}

/// Detect the Python forms that Bazel 9 excludes even when Ruff parses them.
/// Bazel's dialect and top-level control-flow restrictions are documented at
/// <https://bazel.build/versions/9.0.0/rules/language>. The reserved `load`
/// statement and its top-level placement are documented at
/// <https://bazel.build/versions/9.0.0/concepts/build-files>.
struct BazelSyntax<'source> {
    text: &'source str,
    first_failure: Option<(TextRange, &'static str)>,
    statement_depth: usize,
    allow_load: bool,
    first_root_statement: bool,
    top_level_load: Option<(TextRange, TextRange)>,
}

impl<'source> BazelSyntax<'source> {
    fn new(text: &'source str) -> Self {
        Self {
            text,
            first_failure: None,
            statement_depth: 0,
            allow_load: true,
            first_root_statement: true,
            top_level_load: None,
        }
    }
    fn reject(&mut self, range: TextRange, description: &'static str) {
        if self
            .first_failure
            .is_none_or(|(existing, _)| range.start() < existing.start())
        {
            self.first_failure = Some((range, description));
        }
    }

    fn ends_with_comma(&self, range: TextRange) -> bool {
        range
            .end()
            .to_usize()
            .checked_sub(1)
            .and_then(|offset| self.text.as_bytes().get(offset))
            == Some(&b',')
    }
}

impl<'a> Visitor<'a> for BazelSyntax<'_> {
    fn visit_stmt(&mut self, statement: &'a Stmt) {
        if self.statement_depth == 0 {
            if let Stmt::Expr(expr) = statement
                && let Expr::Call(call) = expr.value.as_ref()
                && let Expr::Name(name) = call.func.as_ref()
                && name.id == "load"
            {
                if !self.allow_load {
                    self.reject(
                        call.range(),
                        "load statements after other top-level statements",
                    );
                }
                self.top_level_load = Some((call.range(), name.range()));
            } else if !self.first_root_statement || !is_docstring(statement) {
                self.allow_load = false;
            }
            self.first_root_statement = false;
        }
        let description = match statement {
            Stmt::If(_) => (self.statement_depth == 0).then_some("top-level if statements"),
            Stmt::For(loop_stmt) => {
                if self.statement_depth == 0 {
                    Some("top-level for statements")
                } else if !loop_stmt.orelse.is_empty() {
                    Some("for-else statements")
                } else {
                    None
                }
            }
            Stmt::ClassDef(_) => Some("class definitions"),
            Stmt::Import(_) => Some("Python import statements"),
            Stmt::ImportFrom(_) => Some("Python import statements"),
            Stmt::While(_) => Some("while statements"),
            Stmt::Try(_) => Some("Python exceptions"),
            Stmt::Raise(_) => Some("Python exceptions"),
            Stmt::Global(_) => Some("Python scope declarations"),
            Stmt::Nonlocal(_) => Some("Python scope declarations"),
            Stmt::Delete(_) => Some("delete statements"),
            Stmt::With(_) => Some("with statements"),
            Stmt::Match(_) => Some("match statements"),
            Stmt::Assert(_) => Some("assert statements"),
            Stmt::TypeAlias(_) => Some("Python type aliases"),
            Stmt::AnnAssign(_) => Some("annotated variable assignments"),
            Stmt::IpyEscapeCommand(_) => Some("IPython commands"),
            Stmt::FunctionDef(function) => {
                if function.name.as_str() == "load" {
                    self.reject(function.name.range(), "rebinding the reserved load name");
                }
                for parameter in &function.parameters {
                    if parameter.name() == "load" {
                        self.reject(parameter.name().range(), "rebinding the reserved load name");
                    }
                }
                if function.is_async {
                    Some("async functions")
                } else if !function.decorator_list.is_empty() {
                    Some("decorated functions")
                } else {
                    None
                }
            }
            _ => None,
        };
        if let Some(description) = description {
            self.reject(statement.range(), description);
        }
        self.statement_depth += 1;
        ast::visitor::walk_stmt(self, statement);
        self.statement_depth -= 1;
        if self.statement_depth == 0 {
            self.top_level_load = None;
        }
    }

    fn visit_expr(&mut self, expression: &'a Expr) {
        let description = match expression {
            Expr::Name(name) => {
                if name.id != "load"
                    || self
                        .top_level_load
                        .is_some_and(|(_, range)| range == name.range())
                {
                    None
                } else if name.ctx == ast::ExprContext::Store {
                    Some("rebinding the reserved load name")
                } else {
                    Some("using the reserved load name as an identifier")
                }
            }
            Expr::Call(call) => {
                if call
                    .arguments
                    .keywords
                    .iter()
                    .any(|keyword| keyword.arg.as_ref().is_some_and(|name| name == "load"))
                {
                    Some("the reserved load name as a keyword argument")
                } else if is_load_call(call) {
                    if !self
                        .top_level_load
                        .is_some_and(|(range, _)| range == call.range())
                    {
                        Some("load statements outside the top-level load prefix")
                    } else if !valid_load_arguments(call) {
                        Some("load arguments other than literal strings")
                    } else {
                        None
                    }
                } else {
                    None
                }
            }
            Expr::Lambda(lambda) => {
                if lambda.parameters.as_ref().is_some_and(|parameters| {
                    parameters
                        .iter()
                        .any(|parameter| parameter.name() == "load")
                }) {
                    Some("rebinding the reserved load name")
                } else {
                    None
                }
            }
            Expr::Named(_) => Some("named assignment expressions"),
            Expr::Tuple(tuple) if !tuple.parenthesized => {
                if tuple.elts.len() == 1 {
                    Some("unparenthesized singleton tuples")
                } else if self.ends_with_comma(tuple.range()) {
                    Some("unparenthesized tuples with trailing commas")
                } else {
                    None
                }
            }
            Expr::Set(_) => Some("set expressions"),
            Expr::SetComp(_) => Some("set expressions"),
            Expr::Generator(_) => Some("generator expressions"),
            Expr::Await(_) => Some("await expressions"),
            Expr::Yield(_) => Some("yield expressions"),
            Expr::YieldFrom(_) => Some("yield expressions"),
            Expr::FString(_) => Some("Python interpolated strings"),
            Expr::TString(_) => Some("Python interpolated strings"),
            Expr::EllipsisLiteral(_) => Some("Python ellipsis literals"),
            Expr::IpyEscapeCommand(_) => Some("IPython commands"),
            Expr::StringLiteral(string) => (string.value.is_implicit_concatenated()
                || string.value.is_unicode())
            .then_some("implicitly concatenated or Unicode-prefixed strings"),
            Expr::NumberLiteral(number) => match &number.value {
                Number::Int(_) => None,
                Number::Float(_) => Some("float literals"),
                Number::Complex { real: _, imag: _ } => Some("complex literals"),
            },
            Expr::Compare(compare) => {
                if compare.ops.len() > 1 {
                    Some("chained comparisons")
                } else if compare
                    .ops
                    .iter()
                    .any(|op| matches!(op, CmpOp::Is | CmpOp::IsNot))
                {
                    Some("Python identity comparisons")
                } else {
                    None
                }
            }
            _ => None,
        };
        if let Some(description) = description {
            self.reject(expression.range(), description);
        }
        ast::visitor::walk_expr(self, expression);
    }
}

fn is_docstring(statement: &Stmt) -> bool {
    matches!(statement, Stmt::Expr(expr) if matches!(expr.value.as_ref(), Expr::StringLiteral(_)))
}

fn is_load_call(call: &ast::ExprCall) -> bool {
    matches!(call.func.as_ref(), Expr::Name(name) if name.id == "load")
}

fn valid_load_arguments(call: &ast::ExprCall) -> bool {
    let args = &call.arguments.args;
    let keywords = &call.arguments.keywords;
    args.len() + keywords.len() >= 2
        && args.first().is_some_and(plain_string)
        && args.iter().skip(1).all(plain_string)
        && keywords
            .iter()
            .all(|keyword| keyword.arg.is_some() && plain_string(&keyword.value))
}

fn plain_string(expression: &Expr) -> bool {
    matches!(expression, Expr::StringLiteral(string) if !string.value.is_implicit_concatenated() && !string.value.is_unicode())
}

#[cfg(test)]
mod tests;
