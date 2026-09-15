//! Scalar summaries of stable, unannotated Bazel sources.
//!
//! The source preflight owns whole-file admission. This module only infers
//! results justified by the initialized file and bodies of its own functions.
//! A sibling stub or an explicit host profile is required for parameter types.

use std::collections::{HashMap, HashSet};

use ruff_db::Db;
use ruff_db::files::File;
use ruff_python_ast::{self as ast, Expr, Number, Stmt};
use ruff_text_size::{Ranged, TextRange};

use crate::preflight::{BazelPreflightFailure, preflighted_suite};
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

#[derive(Debug, get_size2::GetSize)]
pub struct BazelCheckProblem {
    file: File,
    range: TextRange,
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

    pub fn declaration_range(&self) -> TextRange {
        self.declaration_range
    }

    pub fn reason(&self) -> &BazelCheckError {
        &self.reason
    }
}

#[derive(Debug, get_size2::GetSize, thiserror::Error)]
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
    let file = source.selected_file(db);
    match ModuleBuilder::new(file, suite) {
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
}

impl BodyValue {
    fn scalar(scalar: BazelScalar) -> Self {
        Self {
            scalar,
            may_fail: false,
        }
    }

    fn invalid_call() -> Self {
        Self {
            scalar: BazelScalar::Unknown,
            may_fail: true,
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
    results: HashMap<CallContext<'source>, BodyValue>,
    specialized_contexts: usize,
    active_functions: HashSet<&'source str>,
    invalid_call_sites: HashSet<TextRange>,
    exhausted_at: Option<TextRange>,
    problems: Vec<BazelCheckProblem>,
}

impl<'source> ModuleBuilder<'source> {
    fn new(file: File, suite: &'source [Stmt]) -> Result<Self, BazelPreflightFailure> {
        let mut scalars = HashMap::new();
        let mut functions = HashMap::new();
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
            results: HashMap::new(),
            specialized_contexts: 0,
            active_functions: HashSet::new(),
            invalid_call_sites: HashSet::new(),
            exhausted_at: None,
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
            scalar: if may_fail {
                BazelScalar::Unknown
            } else {
                scalar
            },
            may_fail,
        };
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
                let mut inputs = Vec::with_capacity(call.arguments.args.len());
                for argument in &call.arguments.args {
                    let input = self.body_expr(argument, locals);
                    may_fail |= input.may_fail;
                    inputs.push(input.scalar);
                }
                let Expr::Name(callee) = call.func.as_ref() else {
                    return BodyValue::invalid_call();
                };
                let Some(function) = self.functions.get(callee.id.as_str()).copied() else {
                    return BodyValue::invalid_call();
                };
                let parameters = &function.parameters.args;
                let minimum = parameters
                    .iter()
                    .filter(|parameter| parameter.default().is_none())
                    .count();
                let maximum = parameters.len();
                let actual = call.arguments.args.len();
                if actual < minimum || actual > maximum {
                    if self.invalid_call_sites.insert(call.range()) {
                        self.problems.push(BazelCheckProblem {
                            file: self.file,
                            range: call.range(),
                            declaration_range: function.name.range(),
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
                for parameter in parameters.iter().skip(actual) {
                    let Some(default) = parameter.default() else {
                        return BodyValue::invalid_call();
                    };
                    let Some(default) = eager_scalar(default, &self.scalars) else {
                        return BodyValue::invalid_call();
                    };
                    inputs.push(default);
                }
                let result = self.function_result(callee.id.as_str(), &inputs);
                may_fail |= result.may_fail;
                BodyValue {
                    scalar: if may_fail {
                        BazelScalar::Unknown
                    } else {
                        result.scalar
                    },
                    may_fail,
                }
            }
            _ => BodyValue::invalid_call(),
        }
    }

    fn finish(self, suite: &'source [Stmt]) -> BazelModuleSummary {
        let Self {
            file,
            scalars,
            functions: _,
            results,
            specialized_contexts: _,
            active_functions: _,
            invalid_call_sites: _,
            exhausted_at: _,
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
