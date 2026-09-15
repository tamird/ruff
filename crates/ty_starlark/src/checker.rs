//! Scalar summaries of stable, unannotated Bazel sources.
//!
//! The source preflight owns whole-file admission. This module only infers
//! results justified by the initialized file and bodies of its own functions.
//! A separate stub proof can constrain call arguments, but all results here
//! remain backed by the runtime source and its own defaults.

use std::collections::{HashMap, HashSet};
use std::fmt;

use ruff_db::Db;
use ruff_db::files::File;
use ruff_python_ast::{self as ast, Expr, Number, Stmt};
use ruff_text_size::{Ranged, TextRange};

use crate::imports::{BazelResolvedFunction, BazelResolvedImports, BazelResolvedValue};
use crate::preflight::{BazelPreflightFailure, preflighted_import_suite, preflighted_suite};
use crate::source::BazelSource;

/// An opaque source has no checked exports, regardless of apparent bindings.
#[derive(Debug, get_size2::GetSize)]
pub enum BazelCheckedSource {
    Checked(BazelModuleSummary),
    Opaque(BazelPreflightFailure),
}

#[derive(Debug, get_size2::GetSize)]
pub struct BazelModuleSummary {
    file: File,
    exports: Box<[BazelExport]>,
    problems: Box<[BazelCheckProblem]>,
}

impl BazelModuleSummary {
    pub fn file(&self) -> File {
        self.file
    }

    /// Only names Bazel permits another file to load are exported.
    pub fn exports(&self) -> &[BazelExport] {
        &self.exports
    }

    pub fn export(&self, name: &str) -> Option<&BazelExport> {
        self.exports.iter().find(|export| export.name == name)
    }

    /// Call problems are independent of whether an unused function is called.
    pub fn problems(&self) -> &[BazelCheckProblem] {
        &self.problems
    }
}

#[derive(Debug, get_size2::GetSize)]
pub struct BazelExport {
    name: String,
    file: File,
    range: TextRange,
    kind: BazelExportKind,
}

impl BazelExport {
    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn file(&self) -> File {
        self.file
    }

    pub fn range(&self) -> TextRange {
        self.range
    }

    pub fn kind(&self) -> &BazelExportKind {
        &self.kind
    }
}

#[derive(Debug, get_size2::GetSize)]
pub enum BazelExportKind {
    Scalar(BazelScalar),
    Function(BazelFunction),
}

/// Scalar precision derived from the runtime source, without stub types.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq, get_size2::GetSize)]
pub enum BazelScalar {
    Int,
    Str,
    Bool,
    None,
    Unknown,
}

impl fmt::Display for BazelScalar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BazelScalar::Int => f.write_str("int"),
            BazelScalar::Str => f.write_str("str"),
            BazelScalar::Bool => f.write_str("bool"),
            BazelScalar::None => f.write_str("None"),
            BazelScalar::Unknown => f.write_str("unknown"),
        }
    }
}

#[derive(Debug, get_size2::GetSize)]
pub struct BazelFunction {
    parameters: Box<[BazelParameter]>,
    result: BazelScalar,
    body_may_fail: bool,
}

impl BazelFunction {
    pub fn parameters(&self) -> &[BazelParameter] {
        &self.parameters
    }

    pub fn required_positional(&self) -> usize {
        self.parameters
            .iter()
            .filter(|parameter| !parameter.has_default)
            .count()
    }

    pub fn total_positional(&self) -> usize {
        self.parameters.len()
    }

    pub fn result(&self) -> BazelScalar {
        self.result
    }

    /// A future stub cannot supply return precision to an unsafe runtime body.
    pub fn body_may_fail(&self) -> bool {
        self.body_may_fail
    }
}

#[derive(Debug, get_size2::GetSize)]
pub struct BazelParameter {
    name: String,
    range: TextRange,
    has_default: bool,
}

impl BazelParameter {
    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn range(&self) -> TextRange {
        self.range
    }

    pub fn has_default(&self) -> bool {
        self.has_default
    }
}

#[derive(Clone, Debug, get_size2::GetSize)]
pub struct BazelCheckProblem {
    file: File,
    range: TextRange,
    declaration_file: File,
    declaration_range: TextRange,
    reason: BazelCheckError,
}

impl BazelCheckProblem {
    pub fn file(&self) -> File {
        self.file
    }

    pub fn range(&self) -> TextRange {
        self.range
    }

    /// The function declaration may live in a different loaded source.
    pub fn declaration_file(&self) -> File {
        self.declaration_file
    }

    pub fn declaration_range(&self) -> TextRange {
        self.declaration_range
    }

    pub fn reason(&self) -> &BazelCheckError {
        &self.reason
    }
}

#[derive(Clone, Debug, get_size2::GetSize, thiserror::Error)]
pub enum BazelCheckError {
    #[error(
        "function '{callee}' accepts {minimum} to {maximum} positional arguments, got {actual}"
    )]
    InvalidArity {
        callee: String,
        minimum: usize,
        maximum: usize,
        actual: usize,
    },
}

/// Summarize scalar exports only after whole-file source preflight is Ready.
#[salsa::tracked(returns(ref), no_eq, heap_size=ruff_memory_usage::heap_size, lru=200)]
pub fn summarize_bazel_source(db: &dyn Db, source: BazelSource<'_>) -> BazelCheckedSource {
    let suite = match preflighted_suite(db, source) {
        Ok(suite) => suite,
        Err(failure) => return BazelCheckedSource::Opaque(failure),
    };
    summarize_suite(source.selected_file(db), suite, None)
}

/// Graph checked file-block bindings use the same source-owned scalar engine.
/// The public source-only query still returns Opaque for every Pending load.
pub(crate) fn summarize_verified_imports<'db>(
    db: &'db dyn Db,
    source: BazelSource<'db>,
    imports: &BazelResolvedImports<'db>,
) -> BazelCheckedSource {
    let suite = match preflighted_import_suite(db, source, imports) {
        Ok(suite) => suite,
        Err(failure) => return BazelCheckedSource::Opaque(failure),
    };
    summarize_suite(source.selected_file(db), suite, Some(imports))
}

fn summarize_suite<'source>(
    file: File,
    suite: &'source [Stmt],
    imports: Option<&'source BazelResolvedImports<'_>>,
) -> BazelCheckedSource {
    match ModuleBuilder::new(file, suite, imports) {
        Ok(mut builder) => match builder.validate_calls(suite) {
            Ok(()) => BazelCheckedSource::Checked(builder.finish(suite)),
            Err(failure) => BazelCheckedSource::Opaque(failure),
        },
        Err(failure) => BazelCheckedSource::Opaque(failure),
    }
}

/// A recursive or dynamically invalid call cannot establish a return type.
#[derive(Clone, Copy, Debug)]
struct BodyValue {
    scalar: BazelScalar,
    may_fail: bool,
    typed_hazard: bool,
    uncertain_import: bool,
}

/// A checked stub can constrain callers without substituting a declared
/// result for a source-backed result.
#[derive(Clone, Debug)]
pub(crate) struct BazelExpectedParameter {
    pub(crate) scalar: BazelScalar,
    pub(crate) file: File,
    pub(crate) range: TextRange,
}

#[derive(Debug)]
pub(crate) struct BazelExpectedFunction {
    pub(crate) name: String,
    pub(crate) parameters: Box<[BazelExpectedParameter]>,
}

#[derive(Clone, Debug)]
pub(crate) struct BazelTypedMismatch {
    pub(crate) callee: String,
    pub(crate) actual: BazelScalar,
    pub(crate) expected: BazelScalar,
    pub(crate) source_file: File,
    pub(crate) source_range: TextRange,
    pub(crate) stub_file: File,
    pub(crate) stub_range: TextRange,
}

#[derive(Eq, Hash, PartialEq)]
struct BazelUsageSite {
    source_file: File,
    source_range: TextRange,
    stub_file: File,
    stub_range: TextRange,
    actual: BazelScalar,
    expected: BazelScalar,
}

/// Inspect declaration shapes without evaluating any function result.
pub(crate) struct BazelSourceMatcher<'source> {
    builder: ModuleBuilder<'source>,
    suite: &'source [Stmt],
}

pub(crate) struct BazelFunctionProver<'source> {
    builder: ModuleBuilder<'source>,
    suite: &'source [Stmt],
}

pub(crate) struct BazelBodyProof {
    pub(crate) result: BazelScalar,
    pub(crate) may_fail: bool,
    pub(crate) exhausted_at: Option<TextRange>,
    pub(crate) mismatch: Option<BazelTypedMismatch>,
}

/// Known mismatches and source-only functions whose typed calls are unsafe.
pub(crate) struct BazelUsageReport {
    pub(crate) problems: Box<[BazelTypedMismatch]>,
    pub(crate) unsafe_functions: HashSet<String>,
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
enum BazelCallMode {
    #[default]
    Proof,
    Usage,
}

impl<'source> BazelSourceMatcher<'source> {
    pub(crate) fn new(
        db: &'source dyn Db,
        source: BazelSource<'_>,
    ) -> Result<Self, BazelPreflightFailure> {
        // Even a Ready source can become opaque during whole-file scalar
        // analysis. No reusable prover may bypass that second gate.
        if let BazelCheckedSource::Opaque(failure) = summarize_bazel_source(db, source) {
            return Err(failure.clone());
        }
        let suite = preflighted_suite(db, source)?;
        let builder = ModuleBuilder::new(source.selected_file(db), suite, None)?;
        Ok(Self { builder, suite })
    }

    /// A graph summary grants access to imported syntax only after that
    /// source has passed the same full-file scalar and name validation.
    pub(crate) fn new_resolved<'repo>(
        db: &'repo dyn Db,
        source: BazelSource<'repo>,
        imports: &'source BazelResolvedImports<'repo>,
        summary: &BazelModuleSummary,
    ) -> Result<Self, BazelPreflightFailure>
    where
        'repo: 'source,
    {
        let file = source.selected_file(db);
        if summary.file() != file {
            return Err(BazelPreflightFailure::unresolved(
                file,
                imports.first_range(),
            ));
        }
        let suite = preflighted_import_suite(db, source, imports)?;
        let builder = ModuleBuilder::new(file, suite, Some(imports))?;
        Ok(Self { builder, suite })
    }

    /// Syntax from this getter is accessible only after full source preflight.
    pub(crate) fn function(&self, name: &str) -> Option<&'source ast::StmtFunctionDef> {
        self.builder.functions.get(name).copied()
    }

    pub(crate) fn default_scalar(&self, expression: &Expr) -> Option<BazelScalar> {
        eager_scalar(expression, &self.builder.scalars)
    }

    /// The caller has matched every stub declaration to this source first.
    /// No function result exists yet, so profiles precede all context caches.
    pub(crate) fn into_prover(
        self,
        expected: Vec<BazelExpectedFunction>,
    ) -> BazelFunctionProver<'source> {
        let mut builder = self.builder;
        builder.imported_types_ready = true;
        builder.expected_calls = expected
            .into_iter()
            .map(|function| (function.name, function.parameters))
            .collect();
        BazelFunctionProver {
            builder,
            suite: self.suite,
        }
    }
}

impl<'source> BazelFunctionProver<'source> {
    pub(crate) fn function(&self, name: &str) -> Option<&'source ast::StmtFunctionDef> {
        self.builder.functions.get(name).copied()
    }

    pub(crate) fn prove(&mut self, name: &str, inputs: &[BazelScalar]) -> Option<BazelBodyProof> {
        let function = self.function(name)?;
        let result = self.builder.function_result(function.name.as_str(), inputs);
        Some(BazelBodyProof {
            result: result.scalar,
            may_fail: result.may_fail,
            exhausted_at: self.builder.exhausted_at,
            mismatch: self.builder.typed_mismatch.clone(),
        })
    }

    /// After declared returns are proved, recheck every body in source order.
    /// Unknown inputs remain indeterminate for diagnostics but can taint an
    /// unconstrained source-only export. Proof and usage have separate caches.
    pub(crate) fn check_all_bodies(mut self) -> Result<BazelUsageReport, TextRange> {
        self.builder.mode = BazelCallMode::Usage;
        self.builder.results.clear();
        self.builder.specialized_contexts = 0;
        self.builder.exhausted_at = None;
        self.builder.typed_mismatch = None;
        for statement in self.suite {
            if let Stmt::FunctionDef(function) = statement {
                let inputs = vec![BazelScalar::Unknown; function.parameters.args.len()];
                self.builder
                    .function_result(function.name.as_str(), &inputs);
                if let Some(range) = self.builder.exhausted_at {
                    return Err(range);
                }
            }
        }
        self.builder
            .typed_usage
            .sort_by_key(|problem| problem.source_range.start());
        Ok(BazelUsageReport {
            problems: self.builder.typed_usage.into_boxed_slice(),
            unsafe_functions: self.builder.unsafe_functions,
        })
    }
}

impl BodyValue {
    fn scalar(scalar: BazelScalar) -> Self {
        Self {
            scalar,
            may_fail: false,
            typed_hazard: false,
            uncertain_import: false,
        }
    }

    fn invalid_call() -> Self {
        Self {
            scalar: BazelScalar::Unknown,
            may_fail: true,
            typed_hazard: false,
            uncertain_import: false,
        }
    }
}

/// Finished results depend on the values supplied to this invocation.
#[derive(Eq, Hash, PartialEq)]
struct CallContext<'source> {
    name: &'source str,
    inputs: Box<[BazelScalar]>,
}

const MAX_SPECIALIZED_CONTEXTS: usize = 1024;
const MAX_ACTIVE_FUNCTIONS: usize = 128;

struct ModuleBuilder<'source> {
    file: File,
    scalars: HashMap<&'source str, BazelScalar>,
    functions: HashMap<&'source str, &'source ast::StmtFunctionDef>,
    imported_functions: HashMap<&'source str, &'source BazelResolvedFunction>,
    imported_types_ready: bool,
    results: HashMap<CallContext<'source>, BodyValue>,
    specialized_contexts: usize,
    active_functions: HashSet<&'source str>,
    invalid_call_sites: HashSet<TextRange>,
    exhausted_at: Option<TextRange>,
    expected_calls: HashMap<String, Box<[BazelExpectedParameter]>>,
    mode: BazelCallMode,
    typed_mismatch: Option<BazelTypedMismatch>,
    typed_usage_sites: HashSet<BazelUsageSite>,
    typed_usage: Vec<BazelTypedMismatch>,
    unsafe_functions: HashSet<String>,
    problems: Vec<BazelCheckProblem>,
}

impl<'source> ModuleBuilder<'source> {
    fn new(
        file: File,
        suite: &'source [Stmt],
        imports: Option<&'source BazelResolvedImports<'_>>,
    ) -> Result<Self, BazelPreflightFailure> {
        let mut scalars = HashMap::new();
        let mut functions = HashMap::new();
        let mut imported_functions = HashMap::new();
        for binding in imports.iter().flat_map(|imports| imports.bindings()) {
            match binding.value() {
                BazelResolvedValue::Scalar(scalar) => {
                    scalars.insert(binding.local_name(), *scalar);
                }
                BazelResolvedValue::Function(function) => {
                    imported_functions.insert(binding.local_name(), function);
                }
            }
        }
        for (index, statement) in suite.iter().enumerate() {
            match statement {
                Stmt::Assign(assign) => {
                    let [Expr::Name(name)] = assign.targets.as_slice() else {
                        return Err(BazelPreflightFailure::unsupported(
                            file,
                            assign.range(),
                            "complex module assignments",
                        ));
                    };
                    let Some(scalar) = eager_scalar(&assign.value, &scalars) else {
                        return Err(BazelPreflightFailure::unsupported(
                            file,
                            assign.value.range(),
                            "unmodeled eager scalar values",
                        ));
                    };
                    scalars.insert(name.id.as_str(), scalar);
                }
                Stmt::FunctionDef(function) => {
                    functions.insert(function.name.as_str(), function);
                }
                Stmt::Expr(expr)
                    if let Expr::Call(call) = expr.value.as_ref()
                        && imports
                            .is_some_and(|imports| imports.load_at(call.range()).is_some()) => {}
                Stmt::Expr(_) => {
                    if index != 0 {
                        return Err(BazelPreflightFailure::unsupported(
                            file,
                            statement.range(),
                            "unexpected source statements",
                        ));
                    }
                }
                Stmt::Pass(_) => {}
                _ => {
                    return Err(BazelPreflightFailure::unsupported(
                        file,
                        statement.range(),
                        "unexpected source statements",
                    ));
                }
            }
        }
        Ok(Self {
            file,
            scalars,
            functions,
            imported_functions,
            imported_types_ready: false,
            results: HashMap::new(),
            specialized_contexts: 0,
            active_functions: HashSet::new(),
            invalid_call_sites: HashSet::new(),
            exhausted_at: None,
            expected_calls: HashMap::new(),
            mode: BazelCallMode::Proof,
            typed_mismatch: None,
            typed_usage_sites: HashSet::new(),
            typed_usage: Vec::new(),
            unsafe_functions: HashSet::new(),
            problems: Vec::new(),
        })
    }

    /// Check every body, including functions that no other source function calls.
    fn validate_calls(&mut self, suite: &'source [Stmt]) -> Result<(), BazelPreflightFailure> {
        for statement in suite {
            if let Stmt::FunctionDef(function) = statement {
                let inputs = vec![BazelScalar::Unknown; function.parameters.args.len()];
                self.function_result(function.name.as_str(), &inputs);
                if let Some(range) = self.exhausted_at {
                    return Err(BazelPreflightFailure::analysis_limit(self.file, range));
                }
            }
        }
        Ok(())
    }

    fn function_result(&mut self, name: &'source str, inputs: &[BazelScalar]) -> BodyValue {
        // Bazel rejects reentering the same function even with new arguments.
        // Check the active function before consulting an earlier cached result.
        if self.active_functions.contains(name) {
            return BodyValue::invalid_call();
        }
        let Some(function) = self.functions.get(name).copied() else {
            return BodyValue::invalid_call();
        };
        if inputs.len() != function.parameters.args.len() {
            return BodyValue::invalid_call();
        }
        let context = CallContext {
            name,
            inputs: inputs.to_vec().into_boxed_slice(),
        };
        if let Some(result) = self.results.get(&context) {
            return *result;
        }
        // Mandatory all-Unknown validation scales with the number of
        // declarations. Only additional concrete-input contexts consume the
        // specialization budget.
        let specialized = inputs.iter().any(|input| *input != BazelScalar::Unknown);
        if (specialized && self.specialized_contexts >= MAX_SPECIALIZED_CONTEXTS)
            || self.active_functions.len() >= MAX_ACTIVE_FUNCTIONS
        {
            self.exhausted_at.get_or_insert(function.name.range());
            return BodyValue::invalid_call();
        }
        if specialized {
            self.specialized_contexts += 1;
        }
        self.active_functions.insert(name);

        // Unspecified exported parameters start Unknown. A particular call
        // supplies its own inputs, with source defaults filled only when omitted.
        let mut locals = HashMap::new();
        for (parameter, input) in function.parameters.args.iter().zip(inputs) {
            locals.insert(parameter.name().as_str(), *input);
        }

        let mut may_fail = false;
        let mut typed_hazard = false;
        let mut uncertain_import = false;
        let mut scalar = BazelScalar::None;
        for statement in &function.body {
            match statement {
                Stmt::Assign(assign) => {
                    let [Expr::Name(name)] = assign.targets.as_slice() else {
                        may_fail = true;
                        break;
                    };
                    let value = self.body_expr(&assign.value, &locals);
                    may_fail |= value.may_fail;
                    typed_hazard |= value.typed_hazard;
                    uncertain_import |= value.uncertain_import;
                    locals.insert(name.id.as_str(), value.scalar);
                }
                Stmt::Return(return_stmt) => {
                    let value = return_stmt
                        .value
                        .as_deref()
                        .map_or(BodyValue::scalar(BazelScalar::None), |expression| {
                            self.body_expr(expression, &locals)
                        });
                    may_fail |= value.may_fail;
                    typed_hazard |= value.typed_hazard;
                    uncertain_import |= value.uncertain_import;
                    scalar = value.scalar;
                    break;
                }
                Stmt::Pass(_) => {}
                _ => {
                    may_fail = true;
                    break;
                }
            }
        }
        let result = BodyValue {
            scalar: if may_fail || typed_hazard || uncertain_import {
                BazelScalar::Unknown
            } else {
                scalar
            },
            may_fail: may_fail || typed_hazard,
            typed_hazard,
            uncertain_import,
        };
        if typed_hazard && self.mode == BazelCallMode::Usage {
            self.unsafe_functions.insert(name.to_string());
        }
        self.active_functions.remove(name);
        self.results.insert(context, result);
        result
    }

    fn body_expr(
        &mut self,
        expression: &'source Expr,
        locals: &HashMap<&'source str, BazelScalar>,
    ) -> BodyValue {
        if let Some(scalar) = literal_scalar(expression) {
            return BodyValue::scalar(scalar);
        }
        match expression {
            Expr::Name(name) => BodyValue::scalar(
                locals
                    .get(name.id.as_str())
                    .or_else(|| self.scalars.get(name.id.as_str()))
                    .copied()
                    .unwrap_or(BazelScalar::Unknown),
            ),
            Expr::Call(call) => {
                // Each argument is evaluated even when the callee ignores it.
                let mut may_fail = false;
                let mut typed_hazard = false;
                let mut uncertain_import = false;
                let mut inputs = Vec::with_capacity(call.arguments.args.len());
                for argument in &call.arguments.args {
                    let input = self.body_expr(argument, locals);
                    may_fail |= input.may_fail;
                    typed_hazard |= input.typed_hazard;
                    uncertain_import |= input.uncertain_import;
                    inputs.push(input.scalar);
                }
                let Expr::Name(callee) = call.func.as_ref() else {
                    return BodyValue::invalid_call();
                };
                let local = self.functions.get(callee.id.as_str()).copied();
                let imported = self.imported_functions.get(callee.id.as_str()).copied();
                let (minimum, maximum, declaration_file, declaration_range) =
                    if let Some(function) = local {
                        let parameters = &function.parameters.args;
                        (
                            parameters
                                .iter()
                                .filter(|parameter| parameter.default().is_none())
                                .count(),
                            parameters.len(),
                            self.file,
                            function.name.range(),
                        )
                    } else if let Some(function) = imported {
                        (
                            function
                                .parameters()
                                .iter()
                                .filter(|parameter| !parameter.has_default())
                                .count(),
                            function.parameters().len(),
                            function.source_file(),
                            function.source_range(),
                        )
                    } else {
                        return BodyValue::invalid_call();
                    };
                let actual = call.arguments.args.len();
                if actual < minimum || actual > maximum {
                    if self.invalid_call_sites.insert(call.range()) {
                        self.problems.push(BazelCheckProblem {
                            file: self.file,
                            range: call.range(),
                            declaration_file,
                            declaration_range,
                            reason: BazelCheckError::InvalidArity {
                                callee: callee.id.to_string(),
                                minimum,
                                maximum,
                                actual,
                            },
                        });
                    }
                    return BodyValue::invalid_call();
                }
                if let Some(function) = local {
                    for parameter in function.parameters.args.iter().skip(actual) {
                        let Some(default) = parameter.default() else {
                            return BodyValue::invalid_call();
                        };
                        let Some(default) = eager_scalar(default, &self.scalars) else {
                            return BodyValue::invalid_call();
                        };
                        inputs.push(default);
                    }
                }
                if let Some(expected) = self.expected_calls.get(callee.id.as_str()).cloned() {
                    // All expected shapes were matched against runtime arity
                    // before the profile was installed. Omitted defaults use
                    // their actual source value in `inputs` above.
                    for (index, (input, parameter)) in
                        inputs.iter().zip(expected.iter()).enumerate()
                    {
                        let source_range = call
                            .arguments
                            .args
                            .get(index)
                            .map_or(call.range(), Ranged::range);
                        if self.check_typed_input(
                            callee.id.as_str(),
                            source_range,
                            *input,
                            parameter.scalar,
                            parameter.file,
                            parameter.range,
                        ) {
                            if self.mode == BazelCallMode::Proof {
                                return BodyValue::invalid_call();
                            }
                            typed_hazard = true;
                        }
                    }
                }
                if let Some(function) = imported {
                    for (index, (input, parameter)) in
                        inputs.iter().zip(function.parameters().iter()).enumerate()
                    {
                        let Some(stub_file) = parameter.stub_file() else {
                            continue;
                        };
                        if *input == parameter.scalar() {
                            continue;
                        }
                        if !self.imported_types_ready {
                            // A generic runtime summary has no declaration
                            // for the caller's input. It cannot claim the
                            // target's stubbed result, but the call is not
                            // unconditionally a runtime failure.
                            return BodyValue {
                                scalar: BazelScalar::Unknown,
                                may_fail: may_fail || function.body_may_fail(),
                                typed_hazard,
                                uncertain_import: true,
                            };
                        }
                        let source_range = call
                            .arguments
                            .args
                            .get(index)
                            .map_or(call.range(), Ranged::range);
                        let Some(stub_range) = parameter.stub_range() else {
                            return BodyValue::invalid_call();
                        };
                        if self.check_typed_input(
                            callee.id.as_str(),
                            source_range,
                            *input,
                            parameter.scalar(),
                            stub_file,
                            stub_range,
                        ) {
                            if self.mode == BazelCallMode::Proof {
                                return BodyValue::invalid_call();
                            }
                            typed_hazard = true;
                        }
                    }
                }
                if typed_hazard {
                    // A declared result cannot be trusted after an invalid
                    // or indeterminate typed argument, including imports.
                    return BodyValue {
                        scalar: BazelScalar::Unknown,
                        may_fail: true,
                        typed_hazard: true,
                        uncertain_import,
                    };
                }
                let result = if let Some(function) = imported {
                    BodyValue {
                        scalar: function.result(),
                        may_fail: function.body_may_fail(),
                        typed_hazard: false,
                        uncertain_import: false,
                    }
                } else {
                    self.function_result(callee.id.as_str(), &inputs)
                };
                may_fail |= result.may_fail;
                typed_hazard |= result.typed_hazard;
                uncertain_import |= result.uncertain_import;
                BodyValue {
                    scalar: if may_fail || typed_hazard || uncertain_import {
                        BazelScalar::Unknown
                    } else {
                        result.scalar
                    },
                    may_fail: may_fail || typed_hazard,
                    typed_hazard,
                    uncertain_import,
                }
            }
            _ => BodyValue::invalid_call(),
        }
    }

    fn check_typed_input(
        &mut self,
        callee: &str,
        source_range: TextRange,
        actual: BazelScalar,
        expected: BazelScalar,
        stub_file: File,
        stub_range: TextRange,
    ) -> bool {
        if actual == expected || expected == BazelScalar::Unknown {
            return false;
        }
        let mismatch = BazelTypedMismatch {
            callee: callee.to_string(),
            actual,
            expected,
            source_file: self.file,
            source_range,
            stub_file,
            stub_range,
        };
        if self.mode == BazelCallMode::Proof {
            self.typed_mismatch.get_or_insert(mismatch);
            return true;
        }
        if actual != BazelScalar::Unknown
            && self.typed_usage_sites.insert(BazelUsageSite {
                source_file: mismatch.source_file,
                source_range: mismatch.source_range,
                stub_file: mismatch.stub_file,
                stub_range: mismatch.stub_range,
                actual: mismatch.actual,
                expected: mismatch.expected,
            })
        {
            self.typed_usage.push(mismatch);
        }
        true
    }

    fn finish(self, suite: &'source [Stmt]) -> BazelModuleSummary {
        let Self {
            file,
            scalars,
            functions: _,
            imported_functions: _,
            imported_types_ready: _,
            results,
            specialized_contexts: _,
            active_functions: _,
            invalid_call_sites: _,
            exhausted_at: _,
            expected_calls: _,
            mode: _,
            typed_mismatch: _,
            typed_usage_sites: _,
            typed_usage: _,
            unsafe_functions: _,
            mut problems,
        } = self;
        let mut exports = Vec::new();
        for statement in suite {
            match statement {
                Stmt::Assign(assign) => {
                    if let [Expr::Name(name)] = assign.targets.as_slice() {
                        if name.id.as_str().starts_with('_') {
                            continue;
                        }
                        exports.push(BazelExport {
                            name: name.id.to_string(),
                            file,
                            range: name.range(),
                            kind: BazelExportKind::Scalar(
                                scalars
                                    .get(name.id.as_str())
                                    .copied()
                                    .unwrap_or(BazelScalar::Unknown),
                            ),
                        });
                    }
                }
                Stmt::FunctionDef(function) => {
                    if function.name.as_str().starts_with('_') {
                        continue;
                    }
                    let parameters = function
                        .parameters
                        .args
                        .iter()
                        .map(|parameter| BazelParameter {
                            name: parameter.name().to_string(),
                            range: parameter.name().range(),
                            has_default: parameter.default().is_some(),
                        })
                        .collect();
                    let context = CallContext {
                        name: function.name.as_str(),
                        inputs: vec![BazelScalar::Unknown; function.parameters.args.len()]
                            .into_boxed_slice(),
                    };
                    let (result, body_may_fail) = match results.get(&context) {
                        Some(result) => (result.scalar, result.may_fail),
                        None => (BazelScalar::Unknown, true),
                    };
                    exports.push(BazelExport {
                        name: function.name.to_string(),
                        file,
                        range: function.name.range(),
                        kind: BazelExportKind::Function(BazelFunction {
                            parameters,
                            result,
                            body_may_fail,
                        }),
                    });
                }
                _ => {}
            }
        }
        problems.sort_by_key(|problem| problem.range.start());
        BazelModuleSummary {
            file,
            exports: exports.into_boxed_slice(),
            problems: problems.into_boxed_slice(),
        }
    }
}

fn eager_scalar(
    expression: &Expr,
    initialized: &HashMap<&str, BazelScalar>,
) -> Option<BazelScalar> {
    match expression {
        Expr::Name(name) => initialized.get(name.id.as_str()).copied(),
        _ => literal_scalar(expression),
    }
}

fn literal_scalar(expression: &Expr) -> Option<BazelScalar> {
    match expression {
        Expr::NoneLiteral(_) => Some(BazelScalar::None),
        Expr::BooleanLiteral(_) => Some(BazelScalar::Bool),
        Expr::StringLiteral(_) => Some(BazelScalar::Str),
        Expr::NumberLiteral(number) => integer_scalar(number),
        Expr::UnaryOp(unary) => {
            let Expr::NumberLiteral(number) = unary.operand.as_ref() else {
                return None;
            };
            match unary.op {
                ast::UnaryOp::UAdd => integer_scalar(number),
                ast::UnaryOp::USub => integer_scalar(number),
                ast::UnaryOp::Invert => None,
                ast::UnaryOp::Not => None,
            }
        }
        _ => None,
    }
}

fn integer_scalar(number: &ast::ExprNumberLiteral) -> Option<BazelScalar> {
    match &number.value {
        Number::Int(value) => value.as_i32().map(|_| BazelScalar::Int),
        Number::Float(_) => None,
        Number::Complex { real: _, imag: _ } => None,
    }
}

#[cfg(test)]
mod tests;
