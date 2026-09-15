//! Runtime-backed exports with optional proven Ty-only stub declarations.
//!
//! The stable Bazel source remains unannotated. A sibling `.bzl.pyi` can
//! describe parameters only when its declaration agrees with the actual
//! source function and its scalar result follows from that function's body.

use std::collections::HashMap;

use ruff_db::Db;
use ruff_db::files::File;
use ruff_python_ast::{self as ast, Stmt};
use ruff_text_size::{Ranged, TextRange};

use crate::checker::{
    BazelCheckProblem, BazelCheckedSource, BazelExpectedFunction, BazelExpectedParameter,
    BazelExport, BazelExportKind, BazelFunction, BazelFunctionProver, BazelModuleSummary,
    BazelScalar, BazelSourceMatcher, BazelUsageReport, summarize_bazel_source,
};
use crate::preflight::BazelPreflightFailure;
use crate::source::BazelSource;
use crate::stub::{
    BazelStubAdmission, BazelStubDeclarations, BazelStubFailure, BazelStubFunction,
    BazelStubParameter, admit_bazel_stub,
};

/// A checked runtime may have an absent stub. A failed present stub is opaque.
#[derive(Debug, get_size2::GetSize)]
pub enum BazelVerifiedSource {
    Checked(BazelVerifiedModule),
    Opaque(BazelVerificationFailure),
}

/// The source file is always authoritative, even for an annotated export.
#[derive(Debug, get_size2::GetSize)]
pub struct BazelVerifiedModule {
    source_file: File,
    stub_file: Option<File>,
    exports: Box<[BazelVerifiedExport]>,
    problems: Box<[BazelCheckProblem]>,
    typed_problems: Box<[BazelTypedCallProblem]>,
}

impl BazelVerifiedModule {
    pub fn source_file(&self) -> File {
        self.source_file
    }

    pub fn stub_file(&self) -> Option<File> {
        self.stub_file
    }

    pub fn exports(&self) -> &[BazelVerifiedExport] {
        &self.exports
    }

    pub fn export(&self, name: &str) -> Option<&BazelVerifiedExport> {
        self.exports.iter().find(|export| export.name == name)
    }

    /// The original source check reports each invalid arity once, including
    /// calls in unused functions. Stub proof does not repeat these problems.
    pub fn problems(&self) -> &[BazelCheckProblem] {
        &self.problems
    }

    /// Known incorrect scalar calls in every reachable source function body.
    /// An Unknown argument remains unproved but is not a type diagnostic.
    /// Function-valued names also remain Unknown in this primitive profile.
    pub fn typed_problems(&self) -> &[BazelTypedCallProblem] {
        &self.typed_problems
    }
}

/// The source argument is primary; the sibling stub annotation is related.
#[derive(Debug, get_size2::GetSize)]
pub struct BazelTypedCallProblem {
    file: File,
    range: TextRange,
    related_file: File,
    related_range: TextRange,
    reason: BazelTypedCallError,
}

impl BazelTypedCallProblem {
    pub fn file(&self) -> File {
        self.file
    }

    pub fn range(&self) -> TextRange {
        self.range
    }

    pub fn related_file(&self) -> File {
        self.related_file
    }

    pub fn related_range(&self) -> TextRange {
        self.related_range
    }

    pub fn reason(&self) -> &BazelTypedCallError {
        &self.reason
    }
}

#[derive(Debug, get_size2::GetSize, thiserror::Error)]
pub enum BazelTypedCallError {
    #[error("function '{callee}' can receive {actual} here; expected {expected}")]
    InvalidArgumentType {
        callee: String,
        actual: BazelScalar,
        expected: BazelScalar,
    },
}

#[derive(Debug, get_size2::GetSize)]
pub struct BazelVerifiedExport {
    name: String,
    source_file: File,
    source_range: TextRange,
    kind: BazelVerifiedExportKind,
}

impl BazelVerifiedExport {
    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn source_file(&self) -> File {
        self.source_file
    }

    pub fn source_range(&self) -> TextRange {
        self.source_range
    }

    pub fn kind(&self) -> &BazelVerifiedExportKind {
        &self.kind
    }
}

#[derive(Debug, get_size2::GetSize)]
pub enum BazelVerifiedExportKind {
    Scalar(BazelScalar),
    Function(BazelVerifiedFunction),
}

#[derive(Debug, get_size2::GetSize)]
pub struct BazelVerifiedFunction {
    parameters: Box<[BazelVerifiedParameter]>,
    result: BazelScalar,
    stub_file: Option<File>,
    stub_result_range: Option<TextRange>,
    body_may_fail: bool,
}

impl BazelVerifiedFunction {
    pub fn parameters(&self) -> &[BazelVerifiedParameter] {
        &self.parameters
    }

    pub fn result(&self) -> BazelScalar {
        self.result
    }

    /// Missing declarations leave source-only parameters unknown.
    pub fn stub_file(&self) -> Option<File> {
        self.stub_file
    }

    pub fn stub_result_range(&self) -> Option<TextRange> {
        self.stub_result_range
    }

    /// A runtime failure or an unsafe typed call prevents trusting this
    /// source-only result; an unsafe call need not crash the Bazel host.
    pub fn body_may_fail(&self) -> bool {
        self.body_may_fail
    }
}

#[derive(Debug, get_size2::GetSize)]
pub struct BazelVerifiedParameter {
    name: String,
    source_range: TextRange,
    scalar: BazelScalar,
    has_default: bool,
    stub_annotation_range: Option<TextRange>,
}

impl BazelVerifiedParameter {
    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn source_range(&self) -> TextRange {
        self.source_range
    }

    pub fn scalar(&self) -> BazelScalar {
        self.scalar
    }

    pub fn has_default(&self) -> bool {
        self.has_default
    }

    /// The owning stub File is on the enclosing verified function.
    pub fn stub_annotation_range(&self) -> Option<TextRange> {
        self.stub_annotation_range
    }
}

/// The first failed proof owns both its source and optional stub ranges.
#[derive(Clone, Debug, get_size2::GetSize)]
pub struct BazelVerificationFailure {
    file: Option<File>,
    range: Option<TextRange>,
    related_file: Option<File>,
    related_range: Option<TextRange>,
    reason: BazelVerificationError,
}

impl BazelVerificationFailure {
    pub fn file(&self) -> Option<File> {
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

    pub fn reason(&self) -> &BazelVerificationError {
        &self.reason
    }
}

#[derive(Clone, Debug, get_size2::GetSize, thiserror::Error)]
pub enum BazelVerificationError {
    #[error("the selected Bazel runtime source is opaque")]
    Source(Box<BazelPreflightFailure>),
    #[error("the sibling Ty-only stub is opaque")]
    Stub(Box<BazelStubFailure>),
    #[error("stub function '{0}' has no exported runtime function")]
    MissingFunction(String),
    #[error("stub function '{name}' has {declared} parameters; runtime has {runtime}")]
    Arity {
        name: String,
        declared: usize,
        runtime: usize,
    },
    #[error("stub parameter '{declared}' differs from runtime '{runtime}'")]
    ParameterName { declared: String, runtime: String },
    #[error("stub parameter '{0}' disagrees with runtime default presence")]
    DefaultPresence(String),
    #[error("runtime default of '{name}' is not a modeled scalar")]
    UnmodeledDefault { name: String },
    #[error("runtime default of '{name}' is {actual}; stub declares {expected}")]
    DefaultType {
        name: String,
        actual: BazelScalar,
        expected: BazelScalar,
    },
    #[error("runtime body of '{0}' can fail for its declared arguments")]
    UnsafeBody(String),
    #[error("runtime call to '{callee}' passes {actual}; stub expects {expected}")]
    InternalArgument {
        callee: String,
        actual: BazelScalar,
        expected: BazelScalar,
    },
    #[error("runtime call to '{callee}' has an unproved argument; stub expects {expected}")]
    UnprovedArgument {
        callee: String,
        expected: BazelScalar,
    },
    #[error("Sty reached its Bazel function analysis limit")]
    AnalysisLimit,
    #[error("runtime result of '{name}' is unproved as {expected}")]
    UnprovedReturn { name: String, expected: BazelScalar },
    #[error("runtime result of '{name}' is {actual}; stub declares {expected}")]
    ReturnType {
        name: String,
        actual: BazelScalar,
        expected: BazelScalar,
    },
}

/// Check all runtime exports before admitting a sibling stub. Primitive
/// precision requires a body-backed proof under its declared argument kinds.
///
/// This evaluator accepts straight-line scalar bodies only. A single kind
/// represents every value of that kind because preflight rejects branches,
/// arithmetic, host calls, and mutation. Extending those source forms requires
/// a corresponding proof model before treating any stub result as trusted.
#[salsa::tracked(returns(ref), no_eq, heap_size=ruff_memory_usage::heap_size, lru=200)]
pub fn verify_bazel_source(db: &dyn Db, source: BazelSource<'_>) -> BazelVerifiedSource {
    let summary = match summarize_bazel_source(db, source) {
        BazelCheckedSource::Checked(summary) => summary,
        BazelCheckedSource::Opaque(failure) => {
            return BazelVerifiedSource::Opaque(BazelVerificationFailure {
                file: Some(failure.file()),
                range: failure.range(),
                related_file: None,
                related_range: None,
                reason: BazelVerificationError::Source(Box::new(failure.clone())),
            });
        }
    };
    let admission = admit_bazel_stub(db, source);
    let declarations = match admission {
        BazelStubAdmission::Absent => None,
        BazelStubAdmission::Admitted(declarations) => Some(declarations),
        BazelStubAdmission::Opaque(failure) => {
            return BazelVerifiedSource::Opaque(BazelVerificationFailure {
                file: failure.file(),
                range: failure.range(),
                related_file: None,
                related_range: None,
                reason: BazelVerificationError::Stub(Box::new(failure.clone())),
            });
        }
    };
    let Some(declarations) = declarations else {
        return BazelVerifiedSource::Checked(verified_module(summary, None, None));
    };
    let matcher = match BazelSourceMatcher::new(db, source) {
        Ok(matcher) => matcher,
        Err(failure) => {
            return BazelVerifiedSource::Opaque(BazelVerificationFailure {
                file: Some(failure.file()),
                range: failure.range(),
                related_file: None,
                related_range: None,
                reason: BazelVerificationError::Source(Box::new(failure)),
            });
        }
    };
    // The source and stub have already rejected duplicate names. Index their
    // resident exports once instead of rescanning for every declaration.
    let exports: HashMap<_, _> = summary
        .exports()
        .iter()
        .map(|export| (export.name(), export))
        .collect();
    let mut matched = Vec::new();
    for declaration in declarations.functions() {
        match match_function(&exports, declarations.file(), declaration, &matcher) {
            Ok(function) => matched.push(function),
            Err(failure) => return BazelVerifiedSource::Opaque(failure),
        }
    }
    // Only fully matched public source functions may constrain a call. The
    // matcher has not evaluated a body, so no stale result predates this map.
    let expected = matched
        .iter()
        .map(|matched| matched.declaration)
        .map(|function| BazelExpectedFunction {
            name: function.name().to_string(),
            parameters: function
                .parameters()
                .iter()
                .map(|parameter| BazelExpectedParameter {
                    scalar: parameter.scalar(),
                    file: declarations.file(),
                    range: parameter.annotation_range(),
                })
                .collect(),
        })
        .collect();
    let mut prover = matcher.into_prover(expected);
    for function in &matched {
        if let Err(failure) = prove_function(function, declarations.file(), &mut prover) {
            return BazelVerifiedSource::Opaque(failure);
        }
    }
    let usage = match prover.check_all_bodies() {
        Ok(usage) => usage,
        Err(range) => {
            return BazelVerifiedSource::Opaque(failed(
                source.selected_file(db),
                range,
                None,
                BazelVerificationError::AnalysisLimit,
            ));
        }
    };
    BazelVerifiedSource::Checked(verified_module(summary, Some(declarations), Some(&usage)))
}

fn verified_module(
    summary: &BazelModuleSummary,
    declarations: Option<&BazelStubDeclarations>,
    usage: Option<&BazelUsageReport>,
) -> BazelVerifiedModule {
    let stub_file = declarations.map(BazelStubDeclarations::file);
    let stub_functions: Option<HashMap<_, _>> = declarations.map(|stub| {
        stub.functions()
            .iter()
            .map(|function| (function.name(), function))
            .collect()
    });
    let exports = summary
        .exports()
        .iter()
        .map(|export| {
            let kind = match export.kind() {
                BazelExportKind::Scalar(scalar) => BazelVerifiedExportKind::Scalar(*scalar),
                BazelExportKind::Function(function) => {
                    let declaration = stub_functions
                        .as_ref()
                        .and_then(|functions| functions.get(export.name()))
                        .copied();
                    let unsafe_source_only = declaration.is_none()
                        && usage
                            .is_some_and(|usage| usage.unsafe_functions.contains(export.name()));
                    let parameters = function
                        .parameters()
                        .iter()
                        .enumerate()
                        .map(|(index, source)| {
                            let stub = declaration.and_then(|stub| stub.parameters().get(index));
                            BazelVerifiedParameter {
                                name: source.name().to_string(),
                                source_range: source.range(),
                                scalar: stub
                                    .map_or(BazelScalar::Unknown, BazelStubParameter::scalar),
                                has_default: source.has_default(),
                                stub_annotation_range: stub
                                    .map(BazelStubParameter::annotation_range),
                            }
                        })
                        .collect();
                    BazelVerifiedExportKind::Function(BazelVerifiedFunction {
                        parameters,
                        result: if unsafe_source_only {
                            BazelScalar::Unknown
                        } else {
                            declaration.map_or(function.result(), BazelStubFunction::result)
                        },
                        stub_file: if declaration.is_some() {
                            stub_file
                        } else {
                            None
                        },
                        stub_result_range: declaration.map(BazelStubFunction::result_range),
                        body_may_fail: function.body_may_fail() || unsafe_source_only,
                    })
                }
            };
            BazelVerifiedExport {
                name: export.name().to_string(),
                source_file: export.file(),
                source_range: export.range(),
                kind,
            }
        })
        .collect();
    BazelVerifiedModule {
        source_file: summary.file(),
        stub_file,
        exports,
        problems: summary.problems().to_vec().into_boxed_slice(),
        typed_problems: usage
            .into_iter()
            .flat_map(|usage| &usage.problems)
            .map(|problem| BazelTypedCallProblem {
                file: problem.source_file,
                range: problem.source_range,
                related_file: problem.stub_file,
                related_range: problem.stub_range,
                reason: BazelTypedCallError::InvalidArgumentType {
                    callee: problem.callee.clone(),
                    actual: problem.actual,
                    expected: problem.expected,
                },
            })
            .collect(),
    }
}

struct MatchedFunction<'summary, 'source, 'stub> {
    export: &'summary BazelExport,
    function: &'summary BazelFunction,
    runtime: &'source ast::StmtFunctionDef,
    declaration: &'stub BazelStubFunction,
}

fn match_function<'summary, 'source, 'stub>(
    exports: &HashMap<&str, &'summary BazelExport>,
    stub_file: File,
    declaration: &'stub BazelStubFunction,
    matcher: &BazelSourceMatcher<'source>,
) -> Result<MatchedFunction<'summary, 'source, 'stub>, BazelVerificationFailure> {
    let Some(export) = exports.get(declaration.name()).copied() else {
        return Err(failed(
            stub_file,
            declaration.range(),
            None,
            BazelVerificationError::MissingFunction(declaration.name().to_string()),
        ));
    };
    let BazelExportKind::Function(function) = export.kind() else {
        return Err(failed(
            stub_file,
            declaration.range(),
            Some((export.file(), export.range())),
            BazelVerificationError::MissingFunction(declaration.name().to_string()),
        ));
    };
    let Some(runtime) = matcher.function(declaration.name()) else {
        return Err(failed(
            stub_file,
            declaration.range(),
            Some((export.file(), export.range())),
            BazelVerificationError::MissingFunction(declaration.name().to_string()),
        ));
    };
    if function.parameters().len() != declaration.parameters().len() {
        return Err(failed(
            stub_file,
            declaration.range(),
            Some((export.file(), runtime.name.range())),
            BazelVerificationError::Arity {
                name: declaration.name().to_string(),
                declared: declaration.parameters().len(),
                runtime: function.parameters().len(),
            },
        ));
    }
    for (actual, stub) in runtime.parameters.args.iter().zip(declaration.parameters()) {
        if actual.name().as_str() != stub.name() {
            return Err(failed(
                stub_file,
                stub.name_range(),
                Some((export.file(), actual.name().range())),
                BazelVerificationError::ParameterName {
                    declared: stub.name().to_string(),
                    runtime: actual.name().to_string(),
                },
            ));
        }
        if actual.default().is_some() != stub.has_default() {
            return Err(failed(
                stub_file,
                stub.name_range(),
                Some((export.file(), actual.range())),
                BazelVerificationError::DefaultPresence(stub.name().to_string()),
            ));
        }
        if let Some(default) = actual.default() {
            let Some(scalar) = matcher.default_scalar(default) else {
                return Err(failed(
                    export.file(),
                    default.range(),
                    Some((stub_file, stub.annotation_range())),
                    BazelVerificationError::UnmodeledDefault {
                        name: stub.name().to_string(),
                    },
                ));
            };
            if scalar != stub.scalar() {
                return Err(failed(
                    export.file(),
                    default.range(),
                    Some((stub_file, stub.annotation_range())),
                    BazelVerificationError::DefaultType {
                        name: stub.name().to_string(),
                        actual: scalar,
                        expected: stub.scalar(),
                    },
                ));
            }
        }
    }
    Ok(MatchedFunction {
        export,
        function,
        runtime,
        declaration,
    })
}

fn prove_function(
    matched: &MatchedFunction<'_, '_, '_>,
    stub_file: File,
    prover: &mut BazelFunctionProver<'_>,
) -> Result<(), BazelVerificationFailure> {
    let MatchedFunction {
        export,
        function,
        runtime,
        declaration,
    } = matched;
    if function.body_may_fail() {
        return Err(failed(
            export.file(),
            runtime.name.range(),
            Some((stub_file, declaration.result_range())),
            BazelVerificationError::UnsafeBody(declaration.name().to_string()),
        ));
    }
    let inputs = declaration
        .parameters()
        .iter()
        .map(BazelStubParameter::scalar)
        .collect::<Vec<_>>();
    let Some(proof) = prover.prove(declaration.name(), &inputs) else {
        return Err(failed(
            stub_file,
            declaration.range(),
            Some((export.file(), runtime.name.range())),
            BazelVerificationError::MissingFunction(declaration.name().to_string()),
        ));
    };
    if let Some(mismatch) = proof.mismatch {
        let reason = if mismatch.actual == BazelScalar::Unknown {
            BazelVerificationError::UnprovedArgument {
                callee: mismatch.callee,
                expected: mismatch.expected,
            }
        } else {
            BazelVerificationError::InternalArgument {
                callee: mismatch.callee,
                actual: mismatch.actual,
                expected: mismatch.expected,
            }
        };
        return Err(failed(
            mismatch.source_file,
            mismatch.source_range,
            Some((mismatch.stub_file, mismatch.stub_range)),
            reason,
        ));
    }
    if let Some(range) = proof.exhausted_at {
        return Err(failed(
            export.file(),
            range,
            Some((stub_file, declaration.result_range())),
            BazelVerificationError::AnalysisLimit,
        ));
    }
    if proof.may_fail {
        return Err(failed(
            export.file(),
            result_range(runtime),
            Some((stub_file, declaration.result_range())),
            BazelVerificationError::UnsafeBody(declaration.name().to_string()),
        ));
    }
    if proof.result == BazelScalar::Unknown {
        return Err(failed(
            export.file(),
            result_range(runtime),
            Some((stub_file, declaration.result_range())),
            BazelVerificationError::UnprovedReturn {
                name: declaration.name().to_string(),
                expected: declaration.result(),
            },
        ));
    }
    if proof.result != declaration.result() {
        return Err(failed(
            export.file(),
            result_range(runtime),
            Some((stub_file, declaration.result_range())),
            BazelVerificationError::ReturnType {
                name: declaration.name().to_string(),
                actual: proof.result,
                expected: declaration.result(),
            },
        ));
    }
    Ok(())
}

fn result_range(function: &ast::StmtFunctionDef) -> TextRange {
    function
        .body
        .iter()
        .find_map(|statement| match statement {
            Stmt::Return(return_stmt) => Some(
                return_stmt
                    .value
                    .as_deref()
                    .map_or(return_stmt.range(), Ranged::range),
            ),
            _ => None,
        })
        .unwrap_or_else(|| {
            function
                .body
                .last()
                .map_or(function.name.range(), Ranged::range)
        })
}

fn failed(
    file: File,
    range: TextRange,
    related: Option<(File, TextRange)>,
    reason: BazelVerificationError,
) -> BazelVerificationFailure {
    let (related_file, related_range) = match related {
        Some((file, range)) => (Some(file), Some(range)),
        None => (None, None),
    };
    BazelVerificationFailure {
        file: Some(file),
        range: Some(range),
        related_file,
        related_range,
        reason,
    }
}

#[cfg(test)]
mod tests;
