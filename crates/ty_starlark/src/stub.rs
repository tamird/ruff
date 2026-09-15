//! Ty-only declarations for a stable, unannotated Bazel `.bzl` source.
//!
//! Bazel does not load `.bzl.pyi` files. A declaration never creates a runtime
//! binding or proves its result; the runtime source must pass its own preflight
//! before this module exposes a sibling's declarations.

use std::collections::HashSet;

use ruff_db::Db;
use ruff_db::files::{File, FileError, system_path_to_file};
use ruff_db::source::{SourceTextError, source_text};
use ruff_db::system::{SystemPath, SystemPathBuf};
use ruff_python_ast::{self as ast, Expr, PySourceType, PythonVersion, Stmt};
use ruff_python_parser::{ParseError, ParseOptions, UnsupportedSyntaxError, parse_unchecked};
use ruff_text_size::{Ranged, TextRange};

use crate::checker::BazelScalar;
use crate::preflight::{BazelPreflight, BazelPreflightFailure, preflight_bazel_source};
use crate::source::BazelSource;

/// Absence means Ruff's tracked status has no resolvable regular sibling;
/// inaccessible paths and unresolved links can appear absent. An existing
/// regular file with unreadable or uncheckable contents is opaque.
#[derive(Debug, get_size2::GetSize)]
pub enum BazelStubAdmission {
    Absent,
    Admitted(BazelStubDeclarations),
    Opaque(BazelStubFailure),
}

/// Declaration syntax only: no return value has been verified against source.
#[derive(Debug, get_size2::GetSize)]
pub struct BazelStubDeclarations {
    file: File,
    functions: Box<[BazelStubFunction]>,
}

impl BazelStubDeclarations {
    pub fn file(&self) -> File {
        self.file
    }

    pub fn functions(&self) -> &[BazelStubFunction] {
        &self.functions
    }

    pub fn function(&self, name: &str) -> Option<&BazelStubFunction> {
        self.functions.iter().find(|function| function.name == name)
    }
}

#[derive(Debug, get_size2::GetSize)]
pub struct BazelStubFunction {
    name: String,
    range: TextRange,
    parameters: Box<[BazelStubParameter]>,
    result: BazelScalar,
    result_range: TextRange,
}

impl BazelStubFunction {
    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn range(&self) -> TextRange {
        self.range
    }

    pub fn parameters(&self) -> &[BazelStubParameter] {
        &self.parameters
    }

    pub fn result(&self) -> BazelScalar {
        self.result
    }

    pub fn result_range(&self) -> TextRange {
        self.result_range
    }
}

#[derive(Debug, get_size2::GetSize)]
pub struct BazelStubParameter {
    name: String,
    name_range: TextRange,
    annotation_range: TextRange,
    scalar: BazelScalar,
    has_default: bool,
}

impl BazelStubParameter {
    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn name_range(&self) -> TextRange {
        self.name_range
    }

    pub fn annotation_range(&self) -> TextRange {
        self.annotation_range
    }

    pub fn scalar(&self) -> BazelScalar {
        self.scalar
    }

    pub fn has_default(&self) -> bool {
        self.has_default
    }
}

/// Source failures have a source File; a directory sibling retains its path.
#[derive(Clone, Debug, get_size2::GetSize)]
pub struct BazelStubFailure {
    file: Option<File>,
    path: Option<SystemPathBuf>,
    range: Option<TextRange>,
    reason: BazelStubError,
}

impl BazelStubFailure {
    pub fn file(&self) -> Option<File> {
        self.file
    }

    pub fn path(&self) -> Option<&SystemPath> {
        self.path.as_deref()
    }

    pub fn range(&self) -> Option<TextRange> {
        self.range
    }

    pub fn reason(&self) -> &BazelStubError {
        &self.reason
    }
}

#[derive(Clone, Debug, get_size2::GetSize, thiserror::Error)]
pub enum BazelStubError {
    #[error("the selected Bazel source is opaque")]
    Source(BazelPreflightFailure),
    #[error("the selected Bazel source has no system path")]
    InvalidSourcePath,
    #[error("the sibling .bzl.pyi path is a directory")]
    IsDirectory,
    #[error("cannot read the sibling .bzl.pyi stub: {0}")]
    Read(SourceTextError),
    #[error("cannot parse the sibling .bzl.pyi stub: {0}")]
    Parser(ParseError),
    #[error("cannot parse the sibling .bzl.pyi stub: {0}")]
    PythonVersion(UnsupportedSyntaxError),
    #[error("cannot check {0} in this Ty-only .bzl.pyi subset")]
    Unsupported(&'static str),
    #[error("duplicate .bzl.pyi declaration '{0}'")]
    DuplicateFunction(String),
    #[error("duplicate .bzl.pyi parameter '{0}'")]
    DuplicateParameter(String),
}

/// Admit only the exact sibling of a selected runtime file, independent of a
/// Python project or environment. Every failure keeps the whole stub opaque.
#[salsa::tracked(returns(ref), no_eq, heap_size=ruff_memory_usage::heap_size, lru=200)]
pub fn admit_bazel_stub(db: &dyn Db, source: BazelSource<'_>) -> BazelStubAdmission {
    let source_file = source.selected_file(db);
    let source_path = source_file.path(db).as_system_path();
    match preflight_bazel_source(db, source) {
        BazelPreflight::Opaque(failure) => {
            return BazelStubAdmission::Opaque(BazelStubFailure {
                file: Some(source_file),
                path: source_path.map(SystemPath::to_path_buf),
                range: failure.range(),
                reason: BazelStubError::Source(failure.clone()),
            });
        }
        BazelPreflight::Ready => {}
    }
    parse_bazel_stub_sibling(db, source_file)
}

/// Parse sibling syntax only. The source-only admission query and graph-aware
/// verifier must each check the current runtime before trusting declarations.
pub(crate) fn parse_bazel_stub_sibling(db: &dyn Db, source_file: File) -> BazelStubAdmission {
    let source_path = source_file.path(db).as_system_path();
    let Some(source_path) = source_path else {
        // The source validator normally rejects virtual and vendored files.
        return BazelStubAdmission::Opaque(BazelStubFailure {
            file: Some(source_file),
            path: None,
            range: None,
            reason: BazelStubError::InvalidSourcePath,
        });
    };
    let stub_path = SystemPathBuf::from(format!("{}.pyi", source_path.as_str()));
    // Track the exact sibling even when absent so creation/removal invalidates
    // the cached admission result.
    let stub_file = match system_path_to_file(db, &stub_path) {
        Ok(file) => file,
        Err(FileError::IsADirectory) => {
            return opaque(None, stub_path, None, BazelStubError::IsDirectory);
        }
        Err(FileError::NotFound) => return BazelStubAdmission::Absent,
    };

    let text = source_text(db, stub_file);
    if let Some(error) = text.read_error() {
        return opaque(
            Some(stub_file),
            stub_path,
            None,
            BazelStubError::Read(error.clone()),
        );
    }
    let options = ParseOptions::from(PySourceType::Stub).with_target_version(PythonVersion::PY310);
    let parsed = parse_unchecked(text.as_str(), options);
    let Some(parsed) = parsed.try_into_module() else {
        return opaque(
            Some(stub_file),
            stub_path,
            None,
            BazelStubError::Unsupported("a non-module parser result"),
        );
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
        return opaque(
            Some(stub_file),
            stub_path,
            Some(error.range()),
            BazelStubError::Parser(error.clone()),
        );
    }
    if let Some(error) = version_error {
        return opaque(
            Some(stub_file),
            stub_path,
            Some(error.range()),
            BazelStubError::PythonVersion(error.clone()),
        );
    }

    let mut seen = HashSet::new();
    let mut functions = Vec::new();
    for (index, statement) in parsed.suite().iter().enumerate() {
        if index == 0 && is_docstring(statement) {
            continue;
        }
        let Stmt::FunctionDef(function) = statement else {
            return opaque(
                Some(stub_file),
                stub_path,
                Some(statement.range()),
                BazelStubError::Unsupported("non-function stub declarations"),
            );
        };
        if !seen.insert(function.name.as_str()) {
            return opaque(
                Some(stub_file),
                stub_path,
                Some(function.name.range()),
                BazelStubError::DuplicateFunction(function.name.to_string()),
            );
        }
        match parse_function(function) {
            Ok(function) => functions.push(function),
            Err((range, reason)) => {
                return opaque(Some(stub_file), stub_path, Some(range), reason);
            }
        }
    }
    BazelStubAdmission::Admitted(BazelStubDeclarations {
        file: stub_file,
        functions: functions.into_boxed_slice(),
    })
}

fn opaque(
    file: Option<File>,
    path: SystemPathBuf,
    range: Option<TextRange>,
    reason: BazelStubError,
) -> BazelStubAdmission {
    BazelStubAdmission::Opaque(BazelStubFailure {
        file,
        path: Some(path),
        range,
        reason,
    })
}

fn is_docstring(statement: &Stmt) -> bool {
    matches!(statement, Stmt::Expr(expr) if matches!(expr.value.as_ref(), Expr::StringLiteral(_)))
}

fn parse_function(
    function: &ast::StmtFunctionDef,
) -> Result<BazelStubFunction, (TextRange, BazelStubError)> {
    if function.is_async
        || !function.decorator_list.is_empty()
        || function.type_params.is_some()
        || !function.parameters.posonlyargs.is_empty()
        || function.parameters.vararg.is_some()
        || !function.parameters.kwonlyargs.is_empty()
        || function.parameters.kwarg.is_some()
    {
        return Err((
            function.range(),
            BazelStubError::Unsupported("decorated, generic, or non-positional functions"),
        ));
    }
    let declaration_body = match function.body.as_slice() {
        [Stmt::Pass(_)] => true,
        [Stmt::Expr(expr)] => matches!(expr.value.as_ref(), Expr::EllipsisLiteral(_)),
        _ => false,
    };
    if !declaration_body {
        return Err((
            function
                .body
                .first()
                .map_or(function.range(), Ranged::range),
            BazelStubError::Unsupported("function bodies other than pass or ..."),
        ));
    }
    let mut parameters = Vec::new();
    let mut seen = HashSet::new();
    for parameter in &function.parameters.args {
        if !seen.insert(parameter.name().as_str()) {
            return Err((
                parameter.name().range(),
                BazelStubError::DuplicateParameter(parameter.name().to_string()),
            ));
        }
        let Some(annotation) = parameter.annotation() else {
            return Err((
                parameter.name().range(),
                BazelStubError::Unsupported("parameters without primitive annotations"),
            ));
        };
        let Some(scalar) = primitive(annotation) else {
            return Err((
                annotation.range(),
                BazelStubError::Unsupported("non-primitive parameter annotations"),
            ));
        };
        if let Some(default) = parameter.default()
            && !matches!(default, Expr::EllipsisLiteral(_))
        {
            return Err((
                default.range(),
                BazelStubError::Unsupported("defaults other than the ... stub marker"),
            ));
        }
        parameters.push(BazelStubParameter {
            name: parameter.name().to_string(),
            name_range: parameter.name().range(),
            annotation_range: annotation.range(),
            scalar,
            has_default: parameter.default().is_some(),
        });
    }
    let Some(annotation) = &function.returns else {
        return Err((
            function.name.range(),
            BazelStubError::Unsupported("functions without primitive return annotations"),
        ));
    };
    let Some(result) = primitive(annotation) else {
        return Err((
            annotation.range(),
            BazelStubError::Unsupported("non-primitive return annotations"),
        ));
    };
    Ok(BazelStubFunction {
        name: function.name.to_string(),
        range: function.name.range(),
        parameters: parameters.into_boxed_slice(),
        result,
        result_range: annotation.range(),
    })
}

fn primitive(annotation: &Expr) -> Option<BazelScalar> {
    match annotation {
        Expr::Name(name) => match name.id.as_str() {
            "int" => Some(BazelScalar::Int),
            "str" => Some(BazelScalar::Str),
            "bool" => Some(BazelScalar::Bool),
            _ => None,
        },
        Expr::NoneLiteral(_) => Some(BazelScalar::None),
        _ => None,
    }
}

#[cfg(test)]
mod tests;
