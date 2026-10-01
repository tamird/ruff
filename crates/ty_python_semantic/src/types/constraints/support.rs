//! Tracks the support of each constraint and interior node in a BDD.
//!
//! The support of a constraint is the set of typevars mentioned anywhere in the constraint
//! (either the subject, or anywhere in the lower or upper bound).
//!
//! The support of a node is the union of the supports of every constraint reachable from that
//! node.

use std::ops::{BitOrAssign, ControlFlow, Sub};

use crate::types::constraints::{
    Constraint, ConstraintId, ConstraintSetStorage, NodeId, SolutionLimits, TypeVarId,
    solutions::Validations,
};
use crate::types::typevar::TypeVarSet;
use crate::{Db, ProgramEnvironment};

use ruff_index::newtype_index;
use rustc_hash::FxHashMap;
use smallvec::SmallVec;

#[newtype_index]
#[derive(get_size2::GetSize)]
pub(super) struct SupportId;

#[derive(Clone, Debug, Default, Eq, Hash, PartialEq, get_size2::GetSize, salsa::SalsaValue)]
pub(super) struct Support {
    chunks: SmallVec<[usize; 2]>,
    has_skipped_lazy_attributes: bool,
}

const CHUNK_SIZE: usize = usize::BITS as usize;

impl Support {
    /// Collects free variables, including dependencies in quantified declarations.
    /// Binder locals contribute to ordinary support but cannot supply ambient assumptions.
    pub(super) fn free_variables<'db, L: SolutionLimits>(
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        storage: &mut ConstraintSetStorage<'db>,
        node: NodeId,
        limits: &mut L,
    ) -> ControlFlow<L::Break, Self> {
        fn collect<'db, L: SolutionLimits>(
            db: &'db dyn Db,
            env: &ProgramEnvironment<'db>,
            storage: &mut ConstraintSetStorage<'db>,
            node: NodeId,
            limits: &mut L,
            completed: &mut FxHashMap<NodeId, Support>,
        ) -> ControlFlow<L::Break, Support> {
            if node.is_terminal() {
                return ControlFlow::Continue(Support::default());
            }
            if let Some(support) = completed.get(&node) {
                return ControlFlow::Continue(support.clone());
            }
            limits.visit_node()?;
            let interior = storage.interior_node_data(node);
            let mut support = match storage.constraint_data(interior.constraint).clone() {
                Constraint::Atomic(_) => storage.constraint_support(interior.constraint).clone(),
                Constraint::Existential(existential) => {
                    let mut support =
                        collect(db, env, storage, existential.body, limits, completed)?;
                    let declarations =
                        Validations::from_locals(db, env, storage, &existential.locals);
                    for constraint in declarations.constraints() {
                        support |= storage.constraint_support(constraint.into_inner());
                    }
                    &support - &existential.locals
                }
            };
            for child in [interior.if_true, interior.if_uncertain, interior.if_false] {
                support |= &collect(db, env, storage, child, limits, completed)?;
            }
            completed.insert(node, support.clone());
            ControlFlow::Continue(support)
        }

        collect(db, env, storage, node, limits, &mut FxHashMap::default())
    }

    pub(super) fn from_typevars(typevars: impl IntoIterator<Item = TypeVarId>) -> Self {
        let mut result = Self::default();
        for typevar in typevars {
            result.insert(typevar);
        }
        result
    }

    pub(super) fn from_typevar_set<'db>(
        db: &'db dyn Db,
        storage: &mut ConstraintSetStorage<'db>,
        typevars: TypeVarSet<'db>,
    ) -> Self {
        let mut result = Self::default();
        for typevar in typevars.iter(db) {
            let typevar = storage.intern_typevar(db, typevar);
            result.insert(typevar);
        }
        result
    }

    /// Adds a typevar to this support.
    pub(super) fn insert(&mut self, typevar: TypeVarId) {
        let index = typevar.index();
        let chunks_needed = (index + 1).div_ceil(CHUNK_SIZE);
        if self.chunks.len() < chunks_needed {
            self.chunks.resize(chunks_needed, 0);
        }

        let chunk_index = index / CHUNK_SIZE;
        let bit_index_within_chunk = index % CHUNK_SIZE;
        let bit_mask_within_chunk = 1 << bit_index_within_chunk;
        self.chunks[chunk_index] |= bit_mask_within_chunk;
    }

    /// Removes and returns an arbitrary typevar from this support.
    pub(super) fn pop(&mut self) -> Option<TypeVarId> {
        let (idx, first_nonempty_chunk) = self
            .chunks
            .iter_mut()
            .enumerate()
            .find(|(_, chunk)| **chunk != 0)?;
        let first_set_bit_in_chunk = first_nonempty_chunk.trailing_zeros() as usize;
        debug_assert!(
            first_set_bit_in_chunk != CHUNK_SIZE,
            "nonempty chunk should not be empty"
        );

        // Clear out the bit we just found, and then return it
        *first_nonempty_chunk ^= 1 << first_set_bit_in_chunk;
        Some(TypeVarId::from_usize(
            CHUNK_SIZE * idx + first_set_bit_in_chunk,
        ))
    }

    fn iter_chunks(&self) -> impl Iterator<Item = usize> + '_ {
        self.chunks.iter().copied()
    }

    /// Returns an iterator of all of the typevars in this support.
    pub(super) fn iter(&self) -> impl Iterator<Item = TypeVarId> + '_ {
        // Iterate through all of the chunks
        let mut next_chunk_start = 0;
        self.iter_chunks().flat_map(move |mut chunk| {
            // Figure out the starting index of this chunk
            let chunk_start = next_chunk_start;
            next_chunk_start += CHUNK_SIZE;

            // Iterate through the set bits in this chunk
            std::iter::from_fn(move || {
                // Find the lowest set bit, if there is one
                let index = chunk.trailing_zeros() as usize;
                if index == CHUNK_SIZE {
                    return None;
                }

                // Clear out the bit we just found.
                chunk ^= 1 << index;

                // And then return it, converted into a TypeVarId
                Some(TypeVarId::from_usize(chunk_start + index))
            })
        })
    }

    /// Returns whether this support contains any typevars that are not in `other`.
    fn contains_more_than(&self, other: &Self) -> bool {
        let lhs = self.iter_chunks();
        let rhs = std::iter::chain(other.iter_chunks(), std::iter::repeat(0));
        std::iter::zip(lhs, rhs).any(|(lhs, rhs)| (lhs & !rhs) != 0)
    }

    /// Returns whether this support contains any type variables in common with `other`.
    pub(super) fn overlaps_with(&self, other: &Self) -> bool {
        let lhs = self.iter_chunks();
        let rhs = other.iter_chunks();
        std::iter::zip(lhs, rhs).any(|(lhs, rhs)| (lhs & rhs) != 0)
    }

    /// Records that lazy type attributes may contain additional type variables.
    pub(super) fn mark_incomplete(&mut self) {
        self.has_skipped_lazy_attributes = true;
    }

    /// Returns whether all type attributes were inspected while collecting this support.
    pub(super) fn is_complete(&self) -> bool {
        !self.has_skipped_lazy_attributes
    }

    /// Closes this support over a set of constraints.
    ///
    /// We perform a fixed-point loop, where we find the constraints that mention any of the
    /// typevars in the support, and add any _other_ typevars they mention. (That might add
    /// additional typevars that cause more constraints to become eligible, and so on.)
    #[expect(clippy::needless_pass_by_value)]
    pub(super) fn close_over_constraints(
        &mut self,
        storage: &ConstraintSetStorage<'_>,
        constraints: impl Iterator<Item = ConstraintId> + Clone,
    ) {
        loop {
            let mut any_added = false;
            for constraint in constraints.clone() {
                let constraint_support = storage.constraint_support(constraint);
                if constraint_support.overlaps_with(self)
                    && constraint_support.contains_more_than(self)
                {
                    any_added = true;
                    *self |= constraint_support;
                }
            }

            if !any_added {
                return;
            }
        }
    }
}

impl BitOrAssign<&Self> for Support {
    fn bitor_assign(&mut self, rhs: &Self) {
        if self.chunks.len() < rhs.chunks.len() {
            self.chunks.resize(rhs.chunks.len(), 0);
        }
        for (lhs, rhs) in std::iter::zip(&mut self.chunks, &rhs.chunks) {
            *lhs |= *rhs;
        }
        self.has_skipped_lazy_attributes |= rhs.has_skipped_lazy_attributes;
    }
}

impl BitOrAssign<Option<&Self>> for Support {
    fn bitor_assign(&mut self, rhs: Option<&Self>) {
        if let Some(rhs) = rhs {
            *self |= rhs;
        }
    }
}

impl Sub<&Support> for &Support {
    type Output = Support;

    fn sub(self, rhs: &Support) -> Support {
        let mut result = self.clone();
        for (lhs, rhs) in std::iter::zip(&mut result.chunks, &rhs.chunks) {
            *lhs &= !(*rhs);
        }
        result
    }
}
