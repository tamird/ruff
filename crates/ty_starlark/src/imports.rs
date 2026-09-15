//! File-block bindings backed by checked main-repository `.bzl` sources.
//!
//! A parsed `load` only proposes a binding. A resolved binding requires the
//! actual runtime target and its public source-backed export to be checked.

use std::collections::HashMap;

use ruff_db::Db;
use ruff_db::files::File;
use ruff_text_size::TextRange;

use crate::bazel::{BazelLoadError, BazelRepository, resolve_bazel_load};
use crate::checker::BazelScalar;
use crate::loads::{BazelLoadPlan, BazelLoadPlanFailure, plan_bazel_loads};
use crate::overlay::{
    BazelVerificationFailure, BazelVerifiedExport, BazelVerifiedExportKind, BazelVerifiedModule,
};
#[cfg(test)]
use crate::overlay::{BazelVerifiedSource, verify_bazel_source};
use crate::source::BazelSource;

/// Imports belong to one selected repository and one real runtime source.
/// Holding this handle keeps the context within its immutable database read.
pub(crate) struct BazelResolvedImports<'db> {
    repository: BazelRepository<'db>,
    source_file: File,
    loads: Box<[BazelResolvedLoad]>,
    load_indices: HashMap<TextRange, usize>,
}

struct BazelResolvedLoad {
    range: TextRange,
    label: String,
    label_range: TextRange,
    bindings: Box<[BazelResolvedBinding]>,
}

pub(crate) struct BazelResolvedBinding {
    source_name: String,
    source_range: TextRange,
    local_name: String,
    local_range: TextRange,
    value: BazelResolvedValue,
}

pub(crate) enum BazelResolvedValue {
    Scalar(BazelScalar),
    Function(BazelResolvedFunction),
}

pub(crate) struct BazelResolvedFunction {
    source_file: File,
    source_range: TextRange,
    parameters: Box<[BazelResolvedParameter]>,
    result: BazelScalar,
    body_may_fail: bool,
}

pub(crate) struct BazelResolvedParameter {
    scalar: BazelScalar,
    has_default: bool,
    stub_file: Option<File>,
    stub_range: Option<TextRange>,
}

impl<'db> BazelResolvedImports<'db> {
    pub(crate) fn matches_source(&self, db: &'db dyn Db, source: BazelSource<'db>) -> bool {
        self.source_file == source.selected_file(db)
            && self.repository == source.selected_repository(db)
    }

    pub(crate) fn matches_plan(&self, plan: &BazelLoadPlan) -> bool {
        let BazelLoadPlan::Pending(candidates) = plan else {
            return false;
        };
        candidates.len() == self.loads.len()
            && candidates
                .iter()
                .zip(&self.loads)
                .all(|(candidate, resolved)| {
                    candidate.range() == resolved.range
                        && candidate.label() == resolved.label
                        && candidate.label_range() == resolved.label_range
                        && candidate.bindings().len() == resolved.bindings.len()
                        && candidate.bindings().iter().zip(&resolved.bindings).all(
                            |(binding, checked)| {
                                binding.source_name() == checked.source_name
                                    && binding.source_range() == checked.source_range
                                    && binding.local_name() == checked.local_name
                                    && binding.local_range() == checked.local_range
                            },
                        )
                })
    }

    pub(crate) fn load_at(&self, range: TextRange) -> Option<&[BazelResolvedBinding]> {
        self.load_indices
            .get(&range)
            .and_then(|index| self.loads.get(*index))
            .map(|load| load.bindings.as_ref())
    }

    pub(crate) fn bindings(&self) -> impl Iterator<Item = &BazelResolvedBinding> {
        self.loads.iter().flat_map(|load| load.bindings.iter())
    }

    pub(crate) fn first_range(&self) -> Option<TextRange> {
        self.loads.first().map(|load| load.range)
    }
}

impl BazelResolvedBinding {
    pub(crate) fn local_name(&self) -> &str {
        &self.local_name
    }

    pub(crate) fn value(&self) -> &BazelResolvedValue {
        &self.value
    }
}

impl BazelResolvedFunction {
    pub(crate) fn source_file(&self) -> File {
        self.source_file
    }

    pub(crate) fn source_range(&self) -> TextRange {
        self.source_range
    }

    pub(crate) fn parameters(&self) -> &[BazelResolvedParameter] {
        &self.parameters
    }

    pub(crate) fn result(&self) -> BazelScalar {
        self.result
    }

    pub(crate) fn body_may_fail(&self) -> bool {
        self.body_may_fail
    }
}

impl BazelResolvedParameter {
    pub(crate) fn scalar(&self) -> BazelScalar {
        self.scalar
    }

    pub(crate) fn has_default(&self) -> bool {
        self.has_default
    }

    pub(crate) fn stub_file(&self) -> Option<File> {
        self.stub_file
    }

    pub(crate) fn stub_range(&self) -> Option<TextRange> {
        self.stub_range
    }
}

/// The importer owns the first unsafe label or quoted requested symbol.
#[derive(Clone, Debug, get_size2::GetSize)]
pub struct BazelResolvedImportFailure {
    file: File,
    range: Option<TextRange>,
    related_file: Option<File>,
    related_range: Option<TextRange>,
    reason: BazelResolvedImportError,
}

impl BazelResolvedImportFailure {
    fn at(file: File, range: Option<TextRange>, reason: BazelResolvedImportError) -> Self {
        Self {
            file,
            range,
            related_file: None,
            related_range: None,
            reason,
        }
    }

    fn with_related(mut self, file: File, range: Option<TextRange>) -> Self {
        self.related_file = Some(file);
        self.related_range = range;
        self
    }

    pub fn file(&self) -> File {
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

    pub fn reason(&self) -> &BazelResolvedImportError {
        &self.reason
    }
}

#[derive(Clone, Debug, get_size2::GetSize, thiserror::Error)]
pub enum BazelResolvedImportError {
    #[error("the importing Bazel source has no valid pending loads")]
    Plan(Box<BazelLoadPlanFailure>),
    #[error("the importing Bazel source has no pending loads")]
    NoLoads,
    #[error("cannot resolve the Bazel load target: {0}")]
    Target(BazelLoadError),
    #[error("the loaded runtime target is opaque")]
    TargetOpaque(Box<BazelVerificationFailure>),
    #[error("the loaded runtime target has not been checked in this graph")]
    UnverifiedTarget,
    #[error("the loaded runtime target does not match its checked source")]
    TargetMismatch,
    #[error("loaded target has no public runtime export '{0}'")]
    MissingExport(String),
}

/// Single-edge test helper: re-read the current tracked verifier for each
/// graph-independent target. Production uses the full graph's current nodes.
#[cfg(test)]
pub(crate) fn resolve_verified_imports<'db>(
    db: &'db dyn Db,
    source: BazelSource<'db>,
) -> Result<BazelResolvedImports<'db>, BazelResolvedImportFailure> {
    bind_resolved_imports_with(db, source, |target| match verify_bazel_source(db, target) {
        BazelVerifiedSource::Checked(module) => Ok(module),
        BazelVerifiedSource::Opaque(failure) => Err(BazelResolvedImportError::TargetOpaque(
            Box::new(failure.clone()),
        )),
    })
}

/// The graph supplies only already-checked targets from its current
/// dependency-first evaluation, after rejecting cycles and opaque nodes.
pub(crate) fn bind_resolved_imports_with<'db, 'verified>(
    db: &'db dyn Db,
    source: BazelSource<'db>,
    mut verified_target: impl FnMut(
        BazelSource<'db>,
    )
        -> Result<&'verified BazelVerifiedModule, BazelResolvedImportError>,
) -> Result<BazelResolvedImports<'db>, BazelResolvedImportFailure> {
    let file = source.selected_file(db);
    let repository = source.selected_repository(db);
    let candidates = match plan_bazel_loads(db, source) {
        BazelLoadPlan::Pending(candidates) => candidates,
        BazelLoadPlan::NoLoads => {
            return Err(BazelResolvedImportFailure::at(
                file,
                None,
                BazelResolvedImportError::NoLoads,
            ));
        }
        BazelLoadPlan::Opaque(failure) => {
            return Err(BazelResolvedImportFailure::at(
                failure.file(),
                failure.range(),
                BazelResolvedImportError::Plan(Box::new(failure.clone())),
            ));
        }
    };
    let mut indexes: HashMap<File, HashMap<&str, &BazelVerifiedExport>> = HashMap::new();
    let mut loads = Vec::with_capacity(candidates.len());
    for candidate in candidates.as_ref() {
        let target =
            resolve_bazel_load(db, repository, file, candidate.label()).map_err(|error| {
                BazelResolvedImportFailure::at(
                    file,
                    Some(candidate.label_range()),
                    BazelResolvedImportError::Target(error),
                )
            })?;
        let target_file = target.selected_file(db);
        let module = verified_target(target).map_err(|reason| {
            let related = match &reason {
                BazelResolvedImportError::TargetOpaque(failure) => {
                    (failure.file().unwrap_or(target_file), failure.range())
                }
                _ => (target_file, None),
            };
            BazelResolvedImportFailure::at(file, Some(candidate.label_range()), reason)
                .with_related(related.0, related.1)
        })?;
        if module.source_file() != target_file {
            return Err(BazelResolvedImportFailure::at(
                file,
                Some(candidate.label_range()),
                BazelResolvedImportError::TargetMismatch,
            )
            .with_related(module.source_file(), None));
        }
        let exports = indexes.entry(target_file).or_insert_with(|| {
            module
                .exports()
                .iter()
                .map(|export| (export.name(), export))
                .collect()
        });
        let mut bindings = Vec::with_capacity(candidate.bindings().len());
        for proposed in candidate.bindings() {
            let Some(export) = exports.get(proposed.source_name()) else {
                return Err(BazelResolvedImportFailure::at(
                    file,
                    Some(proposed.source_range()),
                    BazelResolvedImportError::MissingExport(proposed.source_name().to_string()),
                )
                .with_related(target_file, None));
            };
            let value = match export.kind() {
                BazelVerifiedExportKind::Scalar(scalar) => BazelResolvedValue::Scalar(*scalar),
                BazelVerifiedExportKind::Function(function) => {
                    BazelResolvedValue::Function(BazelResolvedFunction {
                        source_file: export.source_file(),
                        source_range: export.source_range(),
                        parameters: function
                            .parameters()
                            .iter()
                            .map(|parameter| BazelResolvedParameter {
                                scalar: parameter.scalar(),
                                has_default: parameter.has_default(),
                                stub_file: function.stub_file(),
                                stub_range: parameter.stub_annotation_range(),
                            })
                            .collect(),
                        result: function.result(),
                        body_may_fail: function.body_may_fail(),
                    })
                }
            };
            bindings.push(BazelResolvedBinding {
                source_name: proposed.source_name().to_string(),
                source_range: proposed.source_range(),
                local_name: proposed.local_name().to_string(),
                local_range: proposed.local_range(),
                value,
            });
        }
        loads.push(BazelResolvedLoad {
            range: candidate.range(),
            label: candidate.label().to_string(),
            label_range: candidate.label_range(),
            bindings: bindings.into_boxed_slice(),
        });
    }
    let load_indices = loads
        .iter()
        .enumerate()
        .map(|(index, load)| (load.range, index))
        .collect();
    Ok(BazelResolvedImports {
        repository,
        source_file: file,
        loads: loads.into_boxed_slice(),
        load_indices,
    })
}

#[cfg(test)]
mod tests;
