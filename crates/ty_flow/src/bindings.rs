//! Reaching bindings for one place, independent of its language or inferred types.

use itertools::{EitherOrBoth, Itertools};
use ruff_index::newtype_index;
use smallvec::{SmallVec, smallvec};

use crate::narrowing_constraints::{NarrowingConstraintsBuilder, ScopedNarrowingConstraint};
use crate::reachability_constraints::{
    ReachabilityConstraintsBuilder, ScopedReachabilityConstraintId,
};

/// An index into a scope's use-def history. A combined definition can have separate declaration
/// and binding entries when they take effect at different points in control flow.
#[newtype_index]
#[derive(Ord, PartialOrd, get_size2::GetSize)]
pub struct ScopedDefinitionId;

impl ScopedDefinitionId {
    /// A special ID that is used to describe an implicit start-of-scope state. When
    /// we see that this definition is live, we know that the place is (possibly)
    /// unbound or undeclared at a given usage site.
    /// Callers must reserve index zero for this state in their definition arena.
    pub const UNBOUND: ScopedDefinitionId = ScopedDefinitionId::from_u32(0);

    pub fn is_unbound(self) -> bool {
        self == Self::UNBOUND
    }
}

/// What happens to any preexisting definitions when a new binding of the same place is added.
/// `AreShadowed` is how normal assignments behave, but we model some features (loop headers,
/// `nonlocal` writes from nested scopes) as "synthetic" bindings that don't shadow other bindings.
#[derive(Clone, Copy, Debug)]
pub enum PreviousDefinitions {
    AreShadowed,
    AreKept,
}

/// What will happen to a definition if/when a when a new binding of the same place is added later.
/// `ShadowThisOne` is how normal assignments behave, and it's also how some "synthetic" bindings
/// behave (loop headers), but there are other synthetic bindings (nested `nonlocal` writes) that
/// cannot be shadowed.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, get_size2::GetSize)]
pub enum FutureDefinitions {
    ShadowThisOne,
    DontShadowThisOne,
}

impl PreviousDefinitions {
    pub fn are_shadowed(self) -> bool {
        matches!(self, PreviousDefinitions::AreShadowed)
    }
}

/// Live bindings for a single place at some point in control flow. Each live binding comes
/// with a set of narrowing constraints and a reachability constraint.
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash, get_size2::GetSize)]
pub struct Bindings {
    /// A list of live bindings for this place, sorted by their `ScopedDefinitionId`
    live_bindings: SmallVec<[LiveBinding; 2]>,
}

impl Bindings {
    pub fn is_always_unbound(&self) -> bool {
        let [binding] = self.live_bindings.as_slice() else {
            return false;
        };
        binding.binding() == ScopedDefinitionId::UNBOUND
            && binding.narrowing_constraint == ScopedNarrowingConstraint::ALWAYS_TRUE
            && binding.reachability_constraint == ScopedReachabilityConstraintId::ALWAYS_TRUE
            && binding.can_be_shadowed() == FutureDefinitions::ShadowThisOne
    }

    pub fn finish(
        &mut self,
        narrowing_constraints: &mut NarrowingConstraintsBuilder,
        reachability_constraints: &mut ReachabilityConstraintsBuilder,
    ) {
        self.live_bindings.shrink_to_fit();
        for binding in &self.live_bindings {
            reachability_constraints.mark_used(binding.reachability_constraint);
            narrowing_constraints.mark_used(binding.narrowing_constraint);
        }
    }
}

/// One of the live bindings for a single place at some point in control flow.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, get_size2::GetSize)]
pub struct LiveBinding {
    binding: PackedDefinitionId,
    narrowing_constraint: ScopedNarrowingConstraint,
    reachability_constraint: ScopedReachabilityConstraintId,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, get_size2::GetSize)]
struct PackedDefinitionId(u32);

impl PackedDefinitionId {
    // Scope-local definition IDs cannot practically use the high bit, so retain the shadowing
    // policy there instead of adding a byte plus padding to every `LiveBinding`.
    const DONT_SHADOW: u32 = 1 << 31;
    const DEFINITION_MASK: u32 = !Self::DONT_SHADOW;

    fn new(binding: ScopedDefinitionId, can_be_shadowed: FutureDefinitions) -> Self {
        let binding = binding.as_u32();
        assert_eq!(
            binding & Self::DONT_SHADOW,
            0,
            "scopes cannot contain more than 2^31 definitions"
        );
        Self(
            binding
                | match can_be_shadowed {
                    FutureDefinitions::ShadowThisOne => 0,
                    FutureDefinitions::DontShadowThisOne => Self::DONT_SHADOW,
                },
        )
    }

    const fn definition(self) -> ScopedDefinitionId {
        ScopedDefinitionId::from_u32(self.0 & Self::DEFINITION_MASK)
    }

    const fn can_be_shadowed(self) -> FutureDefinitions {
        if self.0 & Self::DONT_SHADOW == 0 {
            FutureDefinitions::ShadowThisOne
        } else {
            FutureDefinitions::DontShadowThisOne
        }
    }
}

impl LiveBinding {
    fn new(
        binding: ScopedDefinitionId,
        narrowing_constraint: ScopedNarrowingConstraint,
        reachability_constraint: ScopedReachabilityConstraintId,
        can_be_shadowed: FutureDefinitions,
    ) -> Self {
        Self {
            binding: PackedDefinitionId::new(binding, can_be_shadowed),
            narrowing_constraint,
            reachability_constraint,
        }
    }

    pub const fn binding(&self) -> ScopedDefinitionId {
        self.binding.definition()
    }

    pub const fn narrowing_constraint(&self) -> ScopedNarrowingConstraint {
        self.narrowing_constraint
    }

    pub const fn reachability_constraint(&self) -> ScopedReachabilityConstraintId {
        self.reachability_constraint
    }

    const fn can_be_shadowed(&self) -> FutureDefinitions {
        self.binding.can_be_shadowed()
    }
}

static_assertions::assert_eq_size!(LiveBinding, [u32; 3]);

pub type LiveBindingsIterator<'a> = std::slice::Iter<'a, LiveBinding>;

impl Bindings {
    pub fn unbound(reachability_constraint: ScopedReachabilityConstraintId) -> Self {
        let initial_binding = LiveBinding::new(
            ScopedDefinitionId::UNBOUND,
            ScopedNarrowingConstraint::ALWAYS_TRUE,
            reachability_constraint,
            FutureDefinitions::ShadowThisOne,
        );
        Self {
            live_bindings: smallvec![initial_binding],
        }
    }

    /// Record a newly encountered binding for this place.
    ///
    /// Allocate definition IDs in increasing order. The new ID must be greater than
    /// every retained ID, so that subsequent merges can consume sorted bindings.
    pub fn record_binding(
        &mut self,
        binding: ScopedDefinitionId,
        reachability_constraint: ScopedReachabilityConstraintId,
        previous_definitions: PreviousDefinitions,
        can_be_shadowed: FutureDefinitions,
    ) {
        // If the new binding is a shadowing type, it replaces previous live bindings in this path
        // (unless they're marked as not shadowable), and has no constraints.
        if previous_definitions.are_shadowed() {
            self.live_bindings
                .retain(|b| b.can_be_shadowed() == FutureDefinitions::DontShadowThisOne);
        }
        debug_assert!(
            self.live_bindings
                .last()
                .is_none_or(|last| last.binding() < binding)
        );
        self.live_bindings.push(LiveBinding::new(
            binding,
            ScopedNarrowingConstraint::ALWAYS_TRUE,
            reachability_constraint,
            can_be_shadowed,
        ));
    }

    /// Add given constraint to all live bindings.
    pub fn record_narrowing_constraint(
        &mut self,
        narrowing_constraints: &mut NarrowingConstraintsBuilder,
        constraint: ScopedNarrowingConstraint,
    ) {
        for binding in &mut self.live_bindings {
            binding.narrowing_constraint =
                narrowing_constraints.add_and_constraint(binding.narrowing_constraint, constraint);
        }
    }

    /// Narrow only bindings selected by their definition IDs.
    pub fn record_narrowing_constraint_for_bindings(
        &mut self,
        narrowing_constraints: &mut NarrowingConstraintsBuilder,
        constraint: ScopedNarrowingConstraint,
        bindings: &(impl Iterator<Item = ScopedDefinitionId> + Clone),
    ) {
        for binding in &mut self.live_bindings {
            if bindings.clone().any(|id| id == binding.binding()) {
                binding.narrowing_constraint = narrowing_constraints
                    .add_and_constraint(binding.narrowing_constraint, constraint);
            }
        }
    }

    /// Add given reachability constraint to all live bindings.
    pub fn record_reachability_constraint(
        &mut self,
        reachability_constraints: &mut ReachabilityConstraintsBuilder,
        constraint: ScopedReachabilityConstraintId,
    ) {
        for binding in &mut self.live_bindings {
            binding.reachability_constraint = reachability_constraints
                .add_and_constraint(binding.reachability_constraint, constraint);
        }
    }

    /// Iterate over currently live bindings for this place
    pub fn iter(&self) -> LiveBindingsIterator<'_> {
        self.live_bindings.iter()
    }

    pub fn as_slice(&self) -> &[LiveBinding] {
        &self.live_bindings
    }

    pub fn merge(
        &mut self,
        b: Self,
        narrowing_constraints: &mut NarrowingConstraintsBuilder,
        reachability_constraints: &mut ReachabilityConstraintsBuilder,
    ) {
        let a = std::mem::take(self);

        // Invariant: merge_join_by consumes the two iterators in sorted order, which ensures that
        // the merged `live_bindings` vec remains sorted. If a definition is found in both `a` and
        // `b`, we combine its boolean narrowing constraints and its ternary reachability
        // constraints. If a definition is found in only one path, it is used as-is.
        let a = a.live_bindings.into_iter();
        let b = b.live_bindings.into_iter();
        for zipped in a.merge_join_by(b, |a, b| a.binding().cmp(&b.binding())) {
            match zipped {
                EitherOrBoth::Both(a, b) => {
                    // If the same definition is visible through both paths, we OR the narrowing
                    // constraints: the type should be narrowed by whichever path was taken.
                    let narrowing_constraint = narrowing_constraints
                        .add_or_constraint(a.narrowing_constraint, b.narrowing_constraint);

                    // For reachability constraints, we also merge using a ternary OR operation:
                    let reachability_constraint = reachability_constraints
                        .add_or_constraint(a.reachability_constraint, b.reachability_constraint);

                    debug_assert_eq!(a.can_be_shadowed(), b.can_be_shadowed());
                    self.live_bindings.push(LiveBinding::new(
                        a.binding(),
                        narrowing_constraint,
                        reachability_constraint,
                        a.can_be_shadowed(),
                    ));
                }

                EitherOrBoth::Left(binding) | EitherOrBoth::Right(binding) => {
                    self.live_bindings.push(binding);
                }
            }
        }
    }
}

impl<'a> IntoIterator for &'a Bindings {
    type Item = &'a LiveBinding;
    type IntoIter = LiveBindingsIterator<'a>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::predicate::ScopedPredicateId;

    #[test]
    fn joins_preserve_the_paths_on_which_a_binding_is_live() {
        let mut reachability = ReachabilityConstraintsBuilder::default();
        let mut narrowing = NarrowingConstraintsBuilder::default();
        let condition = reachability.add_atom(ScopedPredicateId::from_u32(0));
        let otherwise = reachability.add_not_constraint(condition);
        let mut positive = Bindings::unbound(condition);
        positive.record_binding(
            ScopedDefinitionId::from_u32(1),
            condition,
            PreviousDefinitions::AreShadowed,
            FutureDefinitions::ShadowThisOne,
        );
        let negative = Bindings::unbound(otherwise);
        positive.merge(negative, &mut narrowing, &mut reachability);
        let [unbound, assigned] = positive.as_slice() else {
            panic!("expected the unbound and assigned paths: {positive:?}");
        };
        assert!(unbound.binding().is_unbound());
        assert_eq!(unbound.reachability_constraint(), otherwise);
        assert_eq!(assigned.binding(), ScopedDefinitionId::from_u32(1));
        assert_eq!(assigned.reachability_constraint(), condition);

        // Rejoining the same definition keeps one binding and combines its paths.
        let mut other = Bindings::unbound(condition);
        other.merge(positive, &mut narrowing, &mut reachability);
        assert_eq!(other.as_slice().len(), 2);
        assert_eq!(
            other.as_slice()[0].reachability_constraint(),
            ScopedReachabilityConstraintId::ALWAYS_TRUE
        );
        other.finish(&mut narrowing, &mut reachability);
        let store = reachability.build();
        assert_eq!(
            store.get_interior_node(condition).atom(),
            ScopedPredicateId::from_u32(0)
        );
    }

    #[test]
    fn retained_synthetic_bindings_survive_shadowing() {
        let mut bindings = Bindings::unbound(ScopedReachabilityConstraintId::ALWAYS_TRUE);
        bindings.record_binding(
            ScopedDefinitionId::from_u32(1),
            ScopedReachabilityConstraintId::ALWAYS_TRUE,
            PreviousDefinitions::AreKept,
            FutureDefinitions::DontShadowThisOne,
        );
        bindings.record_binding(
            ScopedDefinitionId::from_u32(2),
            ScopedReachabilityConstraintId::ALWAYS_TRUE,
            PreviousDefinitions::AreShadowed,
            FutureDefinitions::ShadowThisOne,
        );
        let ids: Vec<_> = bindings
            .iter()
            .map(|binding| binding.binding().as_u32())
            .collect();
        assert_eq!(ids, [1, 2]);
    }
}
