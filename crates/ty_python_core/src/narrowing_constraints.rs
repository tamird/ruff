use crate::ast_ids::ScopedUseId;
use crate::scope::FileScopeId;
use crate::use_def::BindingsSnapshotId;

pub use ty_flow::narrowing_constraints::{
    InteriorNode, NarrowingConstraints, NarrowingConstraintsBuilder, ScopedNarrowingConstraint,
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ConstraintKey {
    NarrowingConstraint(ScopedNarrowingConstraint),
    NestedScope(FileScopeId),
    UseId(ScopedUseId),
    Snapshot(BindingsSnapshotId),
}
