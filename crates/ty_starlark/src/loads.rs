//! Admission and unresolved labels for leading Bazel `.bzl` loads.
//!
//! This plan validates binders and records labels without following imports. A
//! pending plan must be resolved before semantic analysis.

use std::collections::{HashMap, HashSet, hash_map::Entry};

use ruff_db::Db;
use ruff_db::files::File;
use ruff_python_ast::{self as ast, Expr, Stmt};
use ruff_text_size::{Ranged, TextRange};

use crate::source::{
    BazelAdmissionFailure, BazelSource, BazelSourceAdmission, admit_bazel_source,
    is_bazel_9_identifier, visit_target_names,
};

/// A source without imports, a source requiring resolution, or an opaque file.
#[derive(Debug, get_size2::GetSize)]
pub enum BazelLoadPlan {
    NoLoads,
    Pending(Box<[BazelCandidateLoad]>),
    Opaque(BazelLoadPlanFailure),
}

/// A validated load statement, before its label is resolved.
#[derive(Debug, get_size2::GetSize)]
pub struct BazelCandidateLoad {
    range: TextRange,
    label: String,
    label_range: TextRange,
}

impl BazelCandidateLoad {
    pub fn range(&self) -> TextRange {
        self.range
    }

    pub fn label(&self) -> &str {
        &self.label
    }

    pub fn label_range(&self) -> TextRange {
        self.label_range
    }
}

/// The first unsafe binding or whole-source admission error in the importer.
#[derive(Clone, Debug, get_size2::GetSize)]
pub struct BazelLoadPlanFailure {
    file: File,
    range: Option<TextRange>,
    related_range: Option<TextRange>,
    reason: BazelLoadPlanError,
}

impl BazelLoadPlanFailure {
    fn from_admission(file: File, admission: &BazelAdmissionFailure) -> Self {
        Self {
            file,
            range: admission.range(),
            related_range: None,
            reason: BazelLoadPlanError::Admission(Box::new(admission.clone())),
        }
    }

    fn at(file: File, range: TextRange, reason: BazelLoadPlanError) -> Self {
        Self {
            file,
            range: Some(range),
            related_range: None,
            reason,
        }
    }

    fn with_related(mut self, range: TextRange) -> Self {
        self.related_range = Some(range);
        self
    }

    pub fn file(&self) -> File {
        self.file
    }

    pub fn range(&self) -> Option<TextRange> {
        self.range
    }

    pub fn related_range(&self) -> Option<TextRange> {
        self.related_range
    }

    pub fn reason(&self) -> &BazelLoadPlanError {
        &self.reason
    }
}

#[derive(Clone, Debug, get_size2::GetSize, thiserror::Error)]
pub enum BazelLoadPlanError {
    #[error("the importing Bazel source cannot be admitted")]
    Admission(Box<BazelAdmissionFailure>),
    #[error("load statement has unmodeled argument syntax")]
    InvalidArguments,
    #[error("loaded symbol '{0}' is not a Bazel 9 identifier")]
    InvalidSourceSymbol(String),
    #[error("loaded symbol '{0}' is private and cannot be imported")]
    PrivateSourceSymbol(String),
    #[error("load alias '{0}' is not a Bazel 9 identifier")]
    InvalidLocalName(String),
    #[error("load binds local name '{0}' more than once")]
    DuplicateLocalName(String),
    #[error("load local name '{0}' conflicts with a module binding")]
    ModuleNameCollision(String),
}

/// Inspect only a whole-file admitted Bazel source, without trusting imports.
///
/// The graph checker resolves every pending edge. Ty then checks that the
/// target exports the requested public binding.
/// <https://github.com/bazelbuild/starlark/blob/master/spec.md#load-statements>
/// <https://github.com/bazelbuild/bazel/blob/9.0.0/src/main/java/net/starlark/java/syntax/Resolver.java>
#[salsa::tracked(returns(ref), no_eq, heap_size=ruff_memory_usage::heap_size, lru=200)]
pub fn plan_bazel_loads(db: &dyn Db, source: BazelSource<'_>) -> BazelLoadPlan {
    let file = source.selected_file(db);
    let suite = match admit_bazel_source(db, source) {
        BazelSourceAdmission::Admitted(admitted) => admitted.suite(),
        BazelSourceAdmission::Opaque(failure) => {
            return BazelLoadPlan::Opaque(BazelLoadPlanFailure::from_admission(file, failure));
        }
    };

    let calls: Vec<_> = suite.iter().filter_map(leading_load_call).collect();
    if calls.is_empty() {
        return BazelLoadPlan::NoLoads;
    }

    let mut globals = HashSet::new();
    for statement in suite {
        match statement {
            Stmt::FunctionDef(function) => {
                globals.insert(function.name.as_str());
            }
            Stmt::Assign(assign) => {
                for target in &assign.targets {
                    visit_target_names(target, &mut |name| {
                        globals.insert(name.id.as_str());
                    });
                }
            }
            Stmt::AugAssign(assign) => visit_target_names(&assign.target, &mut |name| {
                globals.insert(name.id.as_str());
            }),
            _ => {}
        }
    }

    let mut aliases = HashMap::new();
    let mut loads = Vec::with_capacity(calls.len());
    for call in calls {
        let Some(Expr::StringLiteral(module)) = call.arguments.args.first() else {
            return BazelLoadPlan::Opaque(BazelLoadPlanFailure::at(
                file,
                call.range(),
                BazelLoadPlanError::InvalidArguments,
            ));
        };
        for argument in call.arguments.iter_source_order().skip(1) {
            let (source, alias) = match argument {
                ast::ArgOrKeyword::Arg(Expr::StringLiteral(string)) => (string, None),
                ast::ArgOrKeyword::Keyword(keyword) => {
                    let Expr::StringLiteral(string) = &keyword.value else {
                        return BazelLoadPlan::Opaque(BazelLoadPlanFailure::at(
                            file,
                            keyword.range(),
                            BazelLoadPlanError::InvalidArguments,
                        ));
                    };
                    (string, keyword.arg.as_ref())
                }
                ast::ArgOrKeyword::Arg(other) => {
                    return BazelLoadPlan::Opaque(BazelLoadPlanFailure::at(
                        file,
                        other.range(),
                        BazelLoadPlanError::InvalidArguments,
                    ));
                }
            };
            let source_name = source.value.to_str();
            let source_range = source.range();
            if !is_bazel_9_identifier(source_name) || is_bazel_9_keyword(source_name) {
                return BazelLoadPlan::Opaque(BazelLoadPlanFailure::at(
                    file,
                    source_range,
                    BazelLoadPlanError::InvalidSourceSymbol(source_name.to_string()),
                ));
            }
            if source_name.starts_with('_') {
                return BazelLoadPlan::Opaque(BazelLoadPlanFailure::at(
                    file,
                    source_range,
                    BazelLoadPlanError::PrivateSourceSymbol(source_name.to_string()),
                ));
            }
            let (local_name, local_range) = match alias {
                Some(name) => (name.as_str(), name.range()),
                None => (source_name, source_range),
            };
            if !is_bazel_9_identifier(local_name) || is_bazel_9_keyword(local_name) {
                return BazelLoadPlan::Opaque(BazelLoadPlanFailure::at(
                    file,
                    local_range,
                    BazelLoadPlanError::InvalidLocalName(local_name.to_string()),
                ));
            }
            if globals.contains(local_name) {
                return BazelLoadPlan::Opaque(BazelLoadPlanFailure::at(
                    file,
                    local_range,
                    BazelLoadPlanError::ModuleNameCollision(local_name.to_string()),
                ));
            }
            match aliases.entry(local_name) {
                Entry::Occupied(previous) => {
                    let failure = BazelLoadPlanFailure::at(
                        file,
                        local_range,
                        BazelLoadPlanError::DuplicateLocalName(local_name.to_string()),
                    )
                    .with_related(*previous.get());
                    return BazelLoadPlan::Opaque(failure);
                }
                Entry::Vacant(entry) => {
                    entry.insert(local_range);
                }
            }
        }
        loads.push(BazelCandidateLoad {
            range: call.range(),
            label: module.value.to_str().to_string(),
            label_range: module.range(),
        });
    }
    BazelLoadPlan::Pending(loads.into_boxed_slice())
}

fn leading_load_call(statement: &Stmt) -> Option<&ast::ExprCall> {
    let Stmt::Expr(expression) = statement else {
        return None;
    };
    let Expr::Call(call) = expression.value.as_ref() else {
        return None;
    };
    matches!(call.func.as_ref(), Expr::Name(name) if name.id == "load").then_some(call)
}

/// Keywords recognized by the pinned Bazel 9 `.bzl` Java lexer.
/// <https://github.com/bazelbuild/bazel/blob/9.0.0/src/main/java/net/starlark/java/syntax/Lexer.java>
fn is_bazel_9_keyword(name: &str) -> bool {
    matches!(
        name,
        "and"
            | "as"
            | "assert"
            | "break"
            | "class"
            | "continue"
            | "def"
            | "del"
            | "elif"
            | "else"
            | "except"
            | "finally"
            | "for"
            | "from"
            | "global"
            | "if"
            | "import"
            | "in"
            | "is"
            | "lambda"
            | "load"
            | "nonlocal"
            | "not"
            | "or"
            | "pass"
            | "raise"
            | "return"
            | "try"
            | "while"
            | "with"
            | "yield"
    )
}

#[cfg(test)]
mod tests;
