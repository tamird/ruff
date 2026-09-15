//! Whole-file name and eager-initialization checks for stable Bazel sources.
//!
//! This bounded gate admits simple, unannotated functions and scalar module
//! bindings. Unmodeled code makes the entire source opaque before any checker
//! may use its declarations.

use std::collections::HashSet;

use ruff_db::Db;
use ruff_db::diagnostic::Diagnostic;
use ruff_db::files::File;
use ruff_python_ast::{self as ast, Expr, Number, Stmt};
use ruff_text_size::{Ranged, TextRange};

use crate::imports::{BazelResolvedImports, BazelResolvedValue};
use crate::loads::{
    BazelCandidateLoad, BazelLoadPlan, BazelLoadPlanError, BazelLoadPlanFailure, plan_bazel_loads,
};
use crate::source::{BazelAdmissionFailure, BazelSource, BazelSourceAdmission, admit_bazel_source};

/// A later checker may summarize only a whole file in this stable Bazel subset.
#[derive(Debug, get_size2::GetSize)]
pub enum BazelPreflight {
    Ready,
    Opaque(BazelPreflightFailure),
}

/// The first reason this entire source cannot contribute checked exports.
#[derive(Clone, Debug, get_size2::GetSize)]
pub struct BazelPreflightFailure {
    file: File,
    range: Option<TextRange>,
    reason: BazelPreflightError,
}

impl BazelPreflightFailure {
    fn from_admission(file: File, failure: &BazelAdmissionFailure) -> Self {
        Self {
            file,
            range: failure.range(),
            reason: BazelPreflightError::Admission(failure.clone()),
        }
    }

    pub(crate) fn unsupported(file: File, range: TextRange, form: &'static str) -> Self {
        Self {
            file,
            range: Some(range),
            reason: BazelPreflightError::Unsupported(form),
        }
    }

    pub(crate) fn analysis_limit(file: File, range: TextRange) -> Self {
        Self {
            file,
            range: Some(range),
            reason: BazelPreflightError::AnalysisLimit,
        }
    }

    pub(crate) fn unresolved(file: File, range: Option<TextRange>) -> Self {
        Self {
            file,
            range,
            reason: BazelPreflightError::UnresolvedLoad,
        }
    }

    pub fn file(&self) -> File {
        self.file
    }

    pub fn range(&self) -> Option<TextRange> {
        self.range
    }

    pub fn reason(&self) -> &BazelPreflightError {
        &self.reason
    }

    /// Source-admission diagnostics retain their original file and range.
    /// The selecting host reports name and profile failures separately.
    pub fn admission_diagnostic(&self) -> Option<Diagnostic> {
        match &self.reason {
            BazelPreflightError::Admission(failure) => failure.diagnostic(),
            BazelPreflightError::LoadPlan(failure) => match failure.reason() {
                BazelLoadPlanError::Admission(admission) => admission.diagnostic(),
                _ => None,
            },
            _ => None,
        }
    }
}

#[derive(Clone, Debug, get_size2::GetSize, thiserror::Error)]
pub enum BazelPreflightError {
    #[error("the selected Bazel source cannot be admitted")]
    Admission(BazelAdmissionFailure),
    #[error("the Bazel load statement contains invalid file bindings")]
    LoadPlan(Box<BazelLoadPlanFailure>),
    #[error("Bazel load statements must be resolved before checking this source")]
    UnresolvedLoad,
    #[error("name '{0}' has no binding modeled by this source preflight")]
    UnknownName(String),
    #[error("duplicate module binding '{0}'")]
    DuplicateGlobal(String),
    #[error("duplicate parameter '{0}'")]
    DuplicateParameter(String),
    #[error("local '{0}' is read before assignment")]
    UninitializedLocal(String),
    #[error("module name '{0}' is used before initialization")]
    UninitializedModule(String),
    #[error("inline type annotations require an experimental Bazel profile")]
    InlineAnnotation,
    #[error("Sty reached its Bazel function analysis limit")]
    AnalysisLimit,
    #[error("cannot check {0} in this stable Bazel subset")]
    Unsupported(&'static str),
}

/// Validate all source names and eager expressions before trusting any export.
///
/// Starlark resolves names in unused functions when loading a module.
/// Function bodies can refer to later globals, but module initializers and
/// parameter defaults evaluate in source order. This stable profile rejects
/// inline annotations; a typed Bazel host requires an explicit profile.
#[salsa::tracked(returns(ref), no_eq, heap_size=ruff_memory_usage::heap_size, lru=200)]
pub fn preflight_bazel_source(db: &dyn Db, source: BazelSource<'_>) -> BazelPreflight {
    let file = source.selected_file(db);
    let suite = match admit_bazel_source(db, source) {
        BazelSourceAdmission::Admitted(source) => source.suite(),
        BazelSourceAdmission::Opaque(failure) => {
            return BazelPreflight::Opaque(BazelPreflightFailure::from_admission(file, failure));
        }
    };
    match plan_bazel_loads(db, source) {
        BazelLoadPlan::NoLoads => {}
        BazelLoadPlan::Pending(loads) => {
            return BazelPreflight::Opaque(BazelPreflightFailure {
                file,
                range: loads.first().map(BazelCandidateLoad::range),
                reason: BazelPreflightError::UnresolvedLoad,
            });
        }
        BazelLoadPlan::Opaque(failure) => {
            return BazelPreflight::Opaque(BazelPreflightFailure {
                file: failure.file(),
                range: failure.range(),
                reason: BazelPreflightError::LoadPlan(Box::new(failure.clone())),
            });
        }
    }
    match Names::new(suite, None).check_module(suite, None) {
        Ok(()) => BazelPreflight::Ready,
        Err(problem) => BazelPreflight::Opaque(BazelPreflightFailure {
            file,
            range: Some(problem.range),
            reason: problem.reason,
        }),
    }
}

/// The only AST entry point for the scalar checker: admit the entire source
/// only after its names and eager initializers have passed preflight.
pub(crate) fn preflighted_suite<'db>(
    db: &'db dyn Db,
    source: BazelSource<'_>,
) -> Result<&'db [Stmt], BazelPreflightFailure> {
    match preflight_bazel_source(db, source) {
        BazelPreflight::Opaque(failure) => Err(failure.clone()),
        BazelPreflight::Ready => match admit_bazel_source(db, source) {
            BazelSourceAdmission::Admitted(admitted) => Ok(admitted.suite()),
            // Even if these queries were separately invalidated, do not
            // expose syntax from a source whose admission has since failed.
            BazelSourceAdmission::Opaque(failure) => Err(BazelPreflightFailure::from_admission(
                source.selected_file(db),
                failure,
            )),
        },
    }
}

/// Reuse the whole-source name gate with file-block imports whose label,
/// source export, selected repository and target have already been checked.
/// This private route never changes the Pending result of the public query.
pub(crate) fn preflighted_import_suite<'db>(
    db: &'db dyn Db,
    source: BazelSource<'db>,
    imports: &BazelResolvedImports<'db>,
) -> Result<&'db [Stmt], BazelPreflightFailure> {
    let file = source.selected_file(db);
    let suite = match admit_bazel_source(db, source) {
        BazelSourceAdmission::Admitted(admitted) => admitted.suite(),
        BazelSourceAdmission::Opaque(failure) => {
            return Err(BazelPreflightFailure::from_admission(file, failure));
        }
    };
    let plan = plan_bazel_loads(db, source);
    if let BazelLoadPlan::Opaque(failure) = plan {
        return Err(BazelPreflightFailure {
            file: failure.file(),
            range: failure.range(),
            reason: BazelPreflightError::LoadPlan(Box::new(failure.clone())),
        });
    }
    if !imports.matches_source(db, source) || !imports.matches_plan(plan) {
        return Err(BazelPreflightFailure {
            file,
            range: match plan {
                BazelLoadPlan::Pending(loads) => loads.first().map(BazelCandidateLoad::range),
                _ => imports.first_range(),
            },
            reason: BazelPreflightError::UnresolvedLoad,
        });
    }
    Names::new(suite, Some(imports))
        .check_module(suite, Some(imports))
        .map_err(|problem| BazelPreflightFailure {
            file,
            range: Some(problem.range),
            reason: problem.reason,
        })?;
    Ok(suite)
}

struct Problem {
    range: TextRange,
    reason: BazelPreflightError,
}

impl Problem {
    fn at(range: TextRange, reason: BazelPreflightError) -> Self {
        Self { range, reason }
    }

    fn unsupported(range: TextRange, form: &'static str) -> Self {
        Self::at(range, BazelPreflightError::Unsupported(form))
    }
}

struct Names<'source> {
    module_bindings: HashSet<&'source str>,
    module_functions: HashSet<&'source str>,
    initialized: HashSet<&'source str>,
    initialized_scalars: HashSet<&'source str>,
}

impl<'source> Names<'source> {
    /// Module bindings cover the entire file before inspecting function bodies.
    /// <https://github.com/bazelbuild/starlark/blob/master/spec.md>
    fn new(suite: &'source [Stmt], imports: Option<&'source BazelResolvedImports<'_>>) -> Self {
        let mut module_bindings = HashSet::new();
        let mut module_functions = HashSet::new();
        for statement in suite {
            match statement {
                Stmt::FunctionDef(function) => {
                    module_bindings.insert(function.name.as_str());
                    module_functions.insert(function.name.as_str());
                }
                Stmt::Assign(assign) => {
                    if let [Expr::Name(name)] = assign.targets.as_slice() {
                        module_bindings.insert(name.id.as_str());
                    }
                }
                _ => {}
            }
        }
        for import in imports.iter().flat_map(|imports| imports.bindings()) {
            module_bindings.insert(import.local_name());
            if matches!(import.value(), BazelResolvedValue::Function(_)) {
                module_functions.insert(import.local_name());
            }
        }
        Self {
            module_bindings,
            module_functions,
            initialized: HashSet::new(),
            initialized_scalars: HashSet::new(),
        }
    }

    fn check_module(
        mut self,
        suite: &'source [Stmt],
        imports: Option<&'source BazelResolvedImports<'_>>,
    ) -> Result<(), Problem> {
        for (index, statement) in suite.iter().enumerate() {
            match statement {
                Stmt::Assign(assign) => {
                    let [Expr::Name(name)] = assign.targets.as_slice() else {
                        return Err(Problem::unsupported(
                            assign.range(),
                            "complex module assignments",
                        ));
                    };
                    if self.initialized.contains(name.id.as_str()) {
                        return Err(Problem::at(
                            name.range(),
                            BazelPreflightError::DuplicateGlobal(name.id.to_string()),
                        ));
                    }
                    self.check_eager_expr(&assign.value)?;
                    self.initialized.insert(name.id.as_str());
                    self.initialized_scalars.insert(name.id.as_str());
                }
                Stmt::FunctionDef(function) => {
                    if self.initialized.contains(function.name.as_str()) {
                        return Err(Problem::at(
                            function.name.range(),
                            BazelPreflightError::DuplicateGlobal(function.name.to_string()),
                        ));
                    }
                    self.check_function(function)?;
                    self.initialized.insert(function.name.as_str());
                }
                Stmt::Expr(expr) if index == 0 && is_docstring(statement) => {}
                Stmt::Expr(expr)
                    if let Expr::Call(call) = expr.value.as_ref()
                        && let Some(bindings) =
                            imports.and_then(|imports| imports.load_at(call.range())) =>
                {
                    for binding in bindings {
                        self.initialized.insert(binding.local_name());
                        if matches!(binding.value(), BazelResolvedValue::Scalar(_)) {
                            self.initialized_scalars.insert(binding.local_name());
                        }
                    }
                }
                Stmt::Pass(_) => {}
                Stmt::Expr(_) => {
                    return Err(Problem::unsupported(
                        statement.range(),
                        "module expression statements or unresolved loads",
                    ));
                }
                _ => {
                    return Err(Problem::unsupported(
                        statement.range(),
                        "other module statements",
                    ));
                }
            }
        }
        Ok(())
    }

    fn check_function(&self, function: &'source ast::StmtFunctionDef) -> Result<(), Problem> {
        let parameters = &function.parameters;
        if !parameters.posonlyargs.is_empty()
            || parameters.vararg.is_some()
            || !parameters.kwonlyargs.is_empty()
            || parameters.kwarg.is_some()
        {
            return Err(Problem::unsupported(
                parameters.range(),
                "non-positional function parameters",
            ));
        }
        let mut seen_parameters = HashSet::new();
        for parameter in &parameters.args {
            if !seen_parameters.insert(parameter.name().as_str()) {
                return Err(Problem::at(
                    parameter.name().range(),
                    BazelPreflightError::DuplicateParameter(parameter.name().to_string()),
                ));
            }
            if let Some(annotation) = parameter.annotation() {
                return Err(Problem::at(
                    annotation.range(),
                    BazelPreflightError::InlineAnnotation,
                ));
            }
            if let Some(default) = parameter.default() {
                self.check_eager_expr(default)?;
            }
        }
        if let Some(annotation) = &function.returns {
            return Err(Problem::at(
                annotation.range(),
                BazelPreflightError::InlineAnnotation,
            ));
        }

        // A later local assignment shadows a global throughout the function.
        // An early read is a dynamic error even if the global is initialized.
        let mut locals = seen_parameters.clone();
        for statement in &function.body {
            if let Stmt::Assign(assign) = statement
                && let [Expr::Name(name)] = assign.targets.as_slice()
            {
                locals.insert(name.id.as_str());
            }
        }
        let mut assigned = seen_parameters;
        for statement in &function.body {
            match statement {
                Stmt::Assign(assign) => {
                    let [Expr::Name(name)] = assign.targets.as_slice() else {
                        return Err(Problem::unsupported(
                            assign.range(),
                            "complex local assignments",
                        ));
                    };
                    self.check_body_expr(&assign.value, &locals, &assigned)?;
                    assigned.insert(name.id.as_str());
                }
                Stmt::Return(return_stmt) => {
                    if let Some(value) = &return_stmt.value {
                        self.check_body_expr(value, &locals, &assigned)?;
                    }
                }
                Stmt::Pass(_) => {}
                _ => {
                    return Err(Problem::unsupported(
                        statement.range(),
                        "function control flow or side effects",
                    ));
                }
            }
        }
        Ok(())
    }

    fn check_eager_expr(&self, expression: &Expr) -> Result<(), Problem> {
        if check_scalar_literal(expression)? {
            return Ok(());
        }
        match expression {
            Expr::Name(name) => {
                if self.initialized_scalars.contains(name.id.as_str()) {
                    Ok(())
                } else if self.module_bindings.contains(name.id.as_str())
                    && !self.initialized.contains(name.id.as_str())
                {
                    Err(Problem::at(
                        name.range(),
                        BazelPreflightError::UninitializedModule(name.id.to_string()),
                    ))
                } else if self.initialized.contains(name.id.as_str()) {
                    Err(Problem::unsupported(
                        name.range(),
                        "non-scalar module values during initialization",
                    ))
                } else {
                    Err(Problem::at(
                        name.range(),
                        BazelPreflightError::UnknownName(name.id.to_string()),
                    ))
                }
            }
            _ => Err(Problem::unsupported(
                expression.range(),
                "dynamic module initializers or defaults",
            )),
        }
    }

    fn check_body_expr(
        &self,
        expression: &Expr,
        locals: &HashSet<&str>,
        assigned: &HashSet<&str>,
    ) -> Result<(), Problem> {
        if check_scalar_literal(expression)? {
            return Ok(());
        }
        match expression {
            Expr::Name(name) => {
                if locals.contains(name.id.as_str()) {
                    if assigned.contains(name.id.as_str()) {
                        Ok(())
                    } else {
                        Err(Problem::at(
                            name.range(),
                            BazelPreflightError::UninitializedLocal(name.id.to_string()),
                        ))
                    }
                } else if self.module_bindings.contains(name.id.as_str()) {
                    Ok(())
                } else {
                    Err(Problem::at(
                        name.range(),
                        BazelPreflightError::UnknownName(name.id.to_string()),
                    ))
                }
            }
            Expr::Call(call) => {
                let Expr::Name(function) = call.func.as_ref() else {
                    return Err(Problem::unsupported(
                        call.range(),
                        "dynamic function targets",
                    ));
                };
                self.check_body_expr(&call.func, locals, assigned)?;
                if locals.contains(function.id.as_str())
                    || !self.module_functions.contains(function.id.as_str())
                {
                    return Err(Problem::unsupported(
                        function.range(),
                        "calls without declared module functions",
                    ));
                }
                if !call.arguments.keywords.is_empty()
                    || call.arguments.args.iter().any(Expr::is_starred_expr)
                {
                    return Err(Problem::unsupported(
                        call.arguments.range(),
                        "keyword or variadic function calls",
                    ));
                }
                for argument in &call.arguments.args {
                    self.check_body_expr(argument, locals, assigned)?;
                }
                Ok(())
            }
            _ => Err(Problem::unsupported(
                expression.range(),
                "unmodeled function expressions",
            )),
        }
    }
}

fn is_docstring(statement: &Stmt) -> bool {
    matches!(statement, Stmt::Expr(expr) if matches!(expr.value.as_ref(), Expr::StringLiteral(_)))
}

/// A scalar literal is safe to evaluate eagerly without host calls.
/// Require the parsed operand to fit in 32 bits; the host's handling of a
/// larger positive operand under unary minus has not been verified.
fn check_scalar_literal(expression: &Expr) -> Result<bool, Problem> {
    match expression {
        Expr::NoneLiteral(_) | Expr::BooleanLiteral(_) | Expr::StringLiteral(_) => Ok(true),
        Expr::NumberLiteral(number) => {
            if let Number::Int(value) = &number.value {
                if value.as_i32().is_some() {
                    Ok(true)
                } else {
                    Err(Problem::unsupported(
                        number.range(),
                        "integer literal outside supported range",
                    ))
                }
            } else {
                Ok(false)
            }
        }
        Expr::UnaryOp(unary) => {
            if let Expr::NumberLiteral(number) = unary.operand.as_ref()
                && let Number::Int(value) = &number.value
                && matches!(unary.op, ast::UnaryOp::USub | ast::UnaryOp::UAdd)
            {
                if value.as_i32().is_some() {
                    Ok(true)
                } else {
                    Err(Problem::unsupported(
                        unary.range(),
                        "integer literal outside supported range",
                    ))
                }
            } else {
                Ok(false)
            }
        }
        _ => Ok(false),
    }
}

#[cfg(test)]
mod tests;
