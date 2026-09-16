//! Ty-only declarations for a stable, unannotated Bazel `.bzl` source.
//!
//! Bazel does not load `.bzl.pyi` files. A declaration never creates a runtime
//! binding. Match declarations to admitted source functions and pass their
//! types and locations to Ty, which checks the original bodies and defaults.

use std::collections::HashSet;

use ruff_db::Db;
use ruff_db::files::{File, FileError, FileRange, system_path_to_file};
use ruff_db::source::{SourceTextError, source_text};
use ruff_db::system::{SystemPath, SystemPathBuf};
use ruff_python_ast::{self as ast, Expr, PySourceType, PythonVersion, Stmt};
use ruff_python_parser::{ParseError, ParseOptions, UnsupportedSyntaxError, parse_unchecked};
use ruff_text_size::{Ranged, TextRange};

use ty_python_core::starlark::{
    StarlarkAnnotation, StarlarkFunctionAnnotations, StarlarkParameterAnnotation, StarlarkType,
};

use crate::source::{BazelAdmissionFailure, BazelSource, BazelSourceAdmission, admit_bazel_source};

/// Absence means Ruff's tracked status has no resolvable regular sibling;
/// inaccessible paths and unresolved links can appear absent. An existing
/// regular file with unreadable or uncheckable contents is opaque.
#[derive(Debug, get_size2::GetSize)]
pub enum BazelStubAdmission {
    Absent,
    Admitted(BazelStubDeclarations),
    Opaque(BazelStubFailure),
}

/// Matched annotations retain original source ranges and companion locations.
#[derive(Debug, get_size2::GetSize)]
pub struct BazelStubDeclarations {
    file: File,
    annotations: Box<[StarlarkFunctionAnnotations]>,
}

impl BazelStubDeclarations {
    pub(crate) fn file(&self) -> File {
        self.file
    }
    pub(crate) fn annotations(&self) -> &[StarlarkFunctionAnnotations] {
        &self.annotations
    }
}

struct BazelStubFunction {
    name: String,
    range: TextRange,
    parameters: Box<[BazelStubParameter]>,
    result: StarlarkType,
    result_range: TextRange,
}

struct BazelStubParameter {
    name: String,
    name_range: TextRange,
    annotation_range: TextRange,
    scalar: StarlarkType,
    has_default: bool,
}

/// Source failures have a source File; a directory sibling retains its path.
#[derive(Clone, Debug, get_size2::GetSize)]
pub struct BazelStubFailure {
    file: Option<File>,
    path: Option<SystemPathBuf>,
    range: Option<TextRange>,
    reason: BazelStubError,
    #[get_size(ignore)] // FileRange owns no heap storage.
    related: Option<FileRange>,
}

impl BazelStubFailure {
    pub fn related(&self) -> Option<FileRange> {
        self.related
    }

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
    Source(BazelAdmissionFailure),
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
    #[error(".bzl.pyi declaration '{0}' does not name a public source function")]
    MissingFunction(String),
    #[error(".bzl.pyi signature for '{0}' has different parameter kinds or count")]
    ParameterShape(String),
    #[error(".bzl.pyi parameter '{declared}' does not match source parameter '{runtime}'")]
    ParameterName { declared: String, runtime: String },
    #[error(".bzl.pyi parameter '{0}' disagrees with the source default's presence")]
    DefaultPresence(String),
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
    let suite = match admit_bazel_source(db, source) {
        BazelSourceAdmission::Opaque(failure) => {
            return BazelStubAdmission::Opaque(BazelStubFailure {
                file: Some(source_file),
                path: source_path.map(SystemPath::to_path_buf),
                range: failure.range(),
                reason: BazelStubError::Source(failure.clone()),
                related: None,
            });
        }
        BazelSourceAdmission::Admitted(admitted) => admitted.suite(),
    };
    parse_bazel_stub_sibling(db, source_file, suite)
}

fn parse_bazel_stub_sibling(db: &dyn Db, source_file: File, suite: &[Stmt]) -> BazelStubAdmission {
    let source_path = source_file.path(db).as_system_path();
    let Some(source_path) = source_path else {
        // The source validator normally rejects virtual and vendored files.
        return BazelStubAdmission::Opaque(BazelStubFailure {
            file: Some(source_file),
            path: None,
            range: None,
            reason: BazelStubError::InvalidSourcePath,
            related: None,
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
    let mut annotations = Vec::with_capacity(functions.len());
    for declaration in functions {
        match match_function(source_file, suite, stub_file, &declaration) {
            Ok(annotation) => annotations.push(annotation),
            Err((range, related, reason)) => {
                return BazelStubAdmission::Opaque(BazelStubFailure {
                    file: Some(stub_file),
                    path: Some(stub_path),
                    range: Some(range),
                    reason,
                    related,
                });
            }
        }
    }
    BazelStubAdmission::Admitted(BazelStubDeclarations {
        file: stub_file,
        annotations: annotations.into_boxed_slice(),
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
        related: None,
    })
}

/// Declaration matching is structural. Ty owns value compatibility and body checks.
fn match_function(
    source_file: File,
    suite: &[Stmt],
    stub_file: File,
    declaration: &BazelStubFunction,
) -> Result<StarlarkFunctionAnnotations, (TextRange, Option<FileRange>, BazelStubError)> {
    let function = suite
        .iter()
        .filter_map(Stmt::as_function_def_stmt)
        .find(|function| {
            function.name.as_str() == declaration.name && !declaration.name.starts_with('_')
        })
        .ok_or_else(|| {
            (
                declaration.range,
                None,
                BazelStubError::MissingFunction(declaration.name.clone()),
            )
        })?;
    let parameters = &function.parameters;
    if !parameters.posonlyargs.is_empty()
        || parameters.vararg.is_some()
        || !parameters.kwonlyargs.is_empty()
        || parameters.kwarg.is_some()
        || parameters.args.len() != declaration.parameters.len()
    {
        return Err((
            declaration.range,
            Some(FileRange::new(source_file, function.name.range())),
            BazelStubError::ParameterShape(declaration.name.clone()),
        ));
    }
    let mut annotations = Vec::with_capacity(declaration.parameters.len());
    for (actual, declared) in parameters.args.iter().zip(&declaration.parameters) {
        let related = Some(FileRange::new(source_file, actual.parameter.range()));
        if actual.name().as_str() != declared.name {
            return Err((
                declared.name_range,
                related,
                BazelStubError::ParameterName {
                    declared: declared.name.clone(),
                    runtime: actual.name().to_string(),
                },
            ));
        }
        if actual.default().is_some() != declared.has_default {
            return Err((
                declared.name_range,
                related,
                BazelStubError::DefaultPresence(declared.name.clone()),
            ));
        }
        annotations.push(StarlarkParameterAnnotation {
            parameter: actual.parameter.range(),
            annotation: StarlarkAnnotation {
                ty: declared.scalar,
                origin: FileRange::new(stub_file, declared.annotation_range),
            },
        });
    }
    Ok(StarlarkFunctionAnnotations {
        function: function.range(),
        parameters: annotations.into_boxed_slice(),
        returns: Some(StarlarkAnnotation {
            ty: declaration.result,
            origin: FileRange::new(stub_file, declaration.result_range),
        }),
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

fn primitive(annotation: &Expr) -> Option<StarlarkType> {
    match annotation {
        Expr::Name(name) => match name.id.as_str() {
            "int" => Some(StarlarkType::Int),
            "str" => Some(StarlarkType::Str),
            "bool" => Some(StarlarkType::Bool),
            _ => None,
        },
        Expr::NoneLiteral(_) => Some(StarlarkType::None),
        _ => None,
    }
}

#[cfg(test)]
mod tests;
