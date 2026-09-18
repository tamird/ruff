//! Track live bindings per place, applicable constraints per binding, and live declarations.
//!
//! These data structures operate entirely on scope-local newtype-indices for definitions and
//! constraints, referring to their location in the `all_definitions` and `all_constraints`
//! indexvecs in [`super::UseDefMapBuilder`].
//!
//! We need to track arbitrary associations between bindings and constraints, not just a single set
//! of currently dominating constraints (where "dominating" means "control flow must have passed
//! through it to reach this point"), because we can have dominating constraints that apply to some
//! bindings but not others, as in this code:
//!
//! ```python
//! x = 1 if flag else None
//! if x is not None:
//!     if flag2:
//!         x = 2 if flag else None
//!     x
//! ```
//!
//! The `x is not None` constraint dominates the final use of `x`, but it applies only to the first
//! binding of `x`, not the second, so `None` is a possible value for `x`.
//!
//! And we can't just track, for each binding, an index into a list of dominating constraints,
//! either, because we can have bindings which are still visible, but subject to constraints that
//! are no longer dominating, as in this code:
//!
//! ```python
//! x = 0
//! if flag1:
//!     x = 1 if flag2 else None
//!     assert x is not None
//! x
//! ```
//!
//! From the point of view of the final use of `x`, the `x is not None` constraint no longer
//! dominates, but it does dominate the `x = 1 if flag2 else None` binding, so we have to keep
//! track of that.
//!
//! The data structures use `IndexVec` arenas to store all data compactly and contiguously, while
//! supporting very cheap clones.
//!
//! Tracking live declarations is simpler, since narrowing constraints are not involved, but
//! otherwise very similar to tracking live bindings.
//!
//! We also store tagged entries for member and wildcard imports, whose source might be `Final`.
//! Semantic indexing cannot determine whether the imported value is actually `Final`, so type
//! inference checks these entries later. Imports are bindings, not type declarations, but an
//! inherited `Final` constrains later assignments even after an ordinary assignment replaces the
//! imported value binding. Reusing declaration flow preserves this metadata and gives it the same
//! reachability and branch-merging behavior without another flow channel. These entries neither
//! establish nor shadow a declared type, and the use-def map exposes them through separate
//! imported-`Final` queries.

use itertools::{EitherOrBoth, Itertools};
use smallvec::{SmallVec, smallvec};

use crate::ReachabilityConstraintsBuilder;
use crate::narrowing_constraints::{NarrowingConstraintsBuilder, ScopedNarrowingConstraint};
use crate::reachability_constraints::ScopedReachabilityConstraintId;

pub use ty_flow::bindings::ScopedDefinitionId;
/// Live declarations for a single place at some point in control flow, with their
/// corresponding reachability constraints.
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash, get_size2::GetSize)]
pub(super) struct Declarations {
    /// A list of live declarations for this place, sorted by their `ScopedDefinitionId`.
    live_declarations: SmallVec<[LiveDeclaration; 2]>,
}

/// One of the live declarations for a single place at some point in control flow.
#[derive(Clone, Debug, PartialEq, Eq, Hash, get_size2::GetSize)]
pub(super) struct LiveDeclaration {
    declaration: PackedDeclarationId,
    pub(super) reachability_constraint: ScopedReachabilityConstraintId,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, get_size2::GetSize)]
struct PackedDeclarationId(u32);

impl PackedDeclarationId {
    // Use the high bit to distinguish imported qualifiers without increasing the size of every
    // declaration. Scope-local IDs retain 31 bits.
    const IMPORTED_QUALIFIER: u32 = 1 << 31;
    const DEFINITION_MASK: u32 = !Self::IMPORTED_QUALIFIER;

    fn new(declaration: ScopedDefinitionId, is_imported_qualifier: bool) -> Self {
        let declaration = declaration.as_u32();
        assert_eq!(
            declaration & Self::IMPORTED_QUALIFIER,
            0,
            "scopes cannot contain more than 2^31 definitions"
        );

        let qualifier_bit = if is_imported_qualifier {
            Self::IMPORTED_QUALIFIER
        } else {
            0
        };

        Self(declaration | qualifier_bit)
    }

    const fn definition(self) -> ScopedDefinitionId {
        ScopedDefinitionId::from_u32(self.0 & Self::DEFINITION_MASK)
    }

    const fn is_imported_qualifier(self) -> bool {
        self.0 & Self::IMPORTED_QUALIFIER != 0
    }
}

impl LiveDeclaration {
    fn new(
        declaration: ScopedDefinitionId,
        reachability_constraint: ScopedReachabilityConstraintId,
        is_imported_qualifier: bool,
    ) -> Self {
        Self {
            declaration: PackedDeclarationId::new(declaration, is_imported_qualifier),
            reachability_constraint,
        }
    }

    pub(super) const fn declaration(&self) -> ScopedDefinitionId {
        self.declaration.definition()
    }

    pub(super) const fn is_imported_qualifier(&self) -> bool {
        self.declaration.is_imported_qualifier()
    }
}

static_assertions::assert_eq_size!(LiveDeclaration, [u32; 2]);

pub(super) type LiveDeclarationsIterator<'a> = std::slice::Iter<'a, LiveDeclaration>;

pub(crate) use ty_flow::bindings::{FutureDefinitions, PreviousDefinitions};

impl Declarations {
    pub(super) fn undeclared_reachability_constraint(
        &self,
    ) -> Option<ScopedReachabilityConstraintId> {
        let [declaration] = self.live_declarations.as_slice() else {
            return None;
        };

        (declaration.declaration() == ScopedDefinitionId::UNBOUND)
            .then_some(declaration.reachability_constraint)
    }

    pub(super) fn is_always_undeclared(&self) -> bool {
        self.undeclared_reachability_constraint()
            == Some(ScopedReachabilityConstraintId::ALWAYS_TRUE)
    }

    pub(super) fn undeclared(reachability_constraint: ScopedReachabilityConstraintId) -> Self {
        let initial_declaration =
            LiveDeclaration::new(ScopedDefinitionId::UNBOUND, reachability_constraint, false);
        Self {
            live_declarations: smallvec![initial_declaration],
        }
    }

    /// Record a newly-encountered declaration for this place.
    pub(super) fn record_declaration(
        &mut self,
        declaration: ScopedDefinitionId,
        reachability_constraint: ScopedReachabilityConstraintId,
        previous_definitions: PreviousDefinitions,
    ) {
        if previous_definitions.are_shadowed() {
            // A real declaration replaces all earlier declarations, including imported qualifiers.
            self.live_declarations.clear();
        }
        self.live_declarations.push(LiveDeclaration::new(
            declaration,
            reachability_constraint,
            false,
        ));
    }

    /// Record an import that may contribute qualifiers without declaring a type.
    ///
    /// Imports replace earlier imported qualifiers, but keep real declarations and the undeclared
    /// sentinel so that an existing annotation or the absence of one remains visible.
    pub(super) fn record_imported_qualifier(
        &mut self,
        declaration: ScopedDefinitionId,
        reachability_constraint: ScopedReachabilityConstraintId,
        previous_definitions: PreviousDefinitions,
    ) {
        if previous_definitions.are_shadowed() {
            self.clear_imported_qualifiers();
        }

        self.live_declarations.push(LiveDeclaration::new(
            declaration,
            reachability_constraint,
            true,
        ));
    }

    fn clear_imported_qualifiers(&mut self) {
        self.live_declarations
            .retain(|declaration| !declaration.is_imported_qualifier());
    }

    /// Add given reachability constraint to all live declarations.
    fn record_reachability_constraint(
        &mut self,
        reachability_constraints: &mut ReachabilityConstraintsBuilder,
        constraint: ScopedReachabilityConstraintId,
    ) {
        for declaration in &mut self.live_declarations {
            declaration.reachability_constraint = reachability_constraints
                .add_and_constraint(declaration.reachability_constraint, constraint);
        }
    }

    /// Return an iterator over live declarations for this place.
    pub(super) fn iter(&self) -> LiveDeclarationsIterator<'_> {
        self.live_declarations.iter()
    }

    pub(super) fn as_slice(&self) -> &[LiveDeclaration] {
        &self.live_declarations
    }

    fn merge(&mut self, b: Self, reachability_constraints: &mut ReachabilityConstraintsBuilder) {
        let a = std::mem::take(self);

        // Invariant: merge_join_by consumes the two iterators in sorted order, which ensures that
        // the merged `live_declarations` vec remains sorted. If a definition is found in both `a`
        // and `b`, we combine its reachability constraints. If a definition is found in only one
        // path, it is used as-is.
        let a = a.live_declarations.into_iter();
        let b = b.live_declarations.into_iter();
        for zipped in a.merge_join_by(b, |a, b| a.declaration().cmp(&b.declaration())) {
            match zipped {
                EitherOrBoth::Both(a, b) => {
                    let reachability_constraint = reachability_constraints
                        .add_or_constraint(a.reachability_constraint, b.reachability_constraint);
                    debug_assert_eq!(a.is_imported_qualifier(), b.is_imported_qualifier());
                    self.live_declarations.push(LiveDeclaration {
                        reachability_constraint,
                        ..a
                    });
                }

                EitherOrBoth::Left(declaration) | EitherOrBoth::Right(declaration) => {
                    self.live_declarations.push(declaration);
                }
            }
        }
    }
}

/// A snapshot of a place state that can be used to resolve a reference in a nested scope.
/// If there are bindings in a (non-class) scope, they are stored in `Bindings`.
/// Even if it's a class scope (class variables are not visible to nested scopes) or there are no
/// bindings, the current narrowing constraint is necessary for narrowing, so it's stored in
/// `Constraint`.
#[derive(Clone, Debug, PartialEq, Eq, Hash, get_size2::GetSize)]
pub(super) enum EnclosingSnapshot {
    Constraint(ScopedNarrowingConstraint),
    Bindings(Bindings),
}

/// Python's class-scope state in addition to the shared reaching bindings.
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash, get_size2::GetSize)]
pub(super) struct Bindings {
    // Class locals are hidden from nested scopes, but their unbound narrowing
    // remains visible even after a local assignment shadows that binding.
    unbound_narrowing_constraint: Option<ScopedNarrowingConstraint>,
    live_bindings: ty_flow::bindings::Bindings,
}

pub use ty_flow::bindings::LiveBinding;
pub(super) use ty_flow::bindings::LiveBindingsIterator;

impl Bindings {
    pub(super) fn is_always_unbound(&self) -> bool {
        self.unbound_narrowing_constraint.is_none() && self.live_bindings.is_always_unbound()
    }

    pub(super) fn unbound_narrowing_constraint(&self) -> ScopedNarrowingConstraint {
        self.unbound_narrowing_constraint
            .unwrap_or(self.live_bindings.as_slice()[0].narrowing_constraint())
    }

    pub(super) fn unbound(reachability: ScopedReachabilityConstraintId) -> Self {
        Self {
            unbound_narrowing_constraint: None,
            live_bindings: ty_flow::bindings::Bindings::unbound(reachability),
        }
    }

    pub(super) fn record_binding(
        &mut self,
        binding: ScopedDefinitionId,
        reachability: ScopedReachabilityConstraintId,
        is_class_scope: bool,
        is_place_name: bool,
        previous_definitions: PreviousDefinitions,
        can_be_shadowed: FutureDefinitions,
    ) {
        if is_class_scope
            && is_place_name
            && let Some(binding) = self.live_bindings.as_slice().first()
            && binding.binding().is_unbound()
        {
            self.unbound_narrowing_constraint = Some(binding.narrowing_constraint());
        }
        self.live_bindings.record_binding(
            binding,
            reachability,
            previous_definitions,
            can_be_shadowed,
        );
    }

    pub(super) fn merge(
        &mut self,
        b: Self,
        narrowing: &mut NarrowingConstraintsBuilder,
        reachability: &mut ReachabilityConstraintsBuilder,
    ) {
        self.unbound_narrowing_constraint = self
            .unbound_narrowing_constraint
            .zip(b.unbound_narrowing_constraint)
            .map(|(a, b)| narrowing.add_or_constraint(a, b));
        self.live_bindings
            .merge(b.live_bindings, narrowing, reachability);
    }

    pub(super) fn finish(
        &mut self,
        narrowing: &mut NarrowingConstraintsBuilder,
        reachability: &mut ReachabilityConstraintsBuilder,
    ) {
        self.live_bindings.finish(narrowing, reachability);
    }

    pub(super) fn iter(&self) -> LiveBindingsIterator<'_> {
        self.live_bindings.iter()
    }

    pub(super) fn as_slice(&self) -> &[LiveBinding] {
        self.live_bindings.as_slice()
    }

    fn record_narrowing_constraint(
        &mut self,
        narrowing: &mut NarrowingConstraintsBuilder,
        constraint: ScopedNarrowingConstraint,
    ) {
        self.live_bindings
            .record_narrowing_constraint(narrowing, constraint);
    }

    fn record_reachability_constraint(
        &mut self,
        reachability: &mut ReachabilityConstraintsBuilder,
        constraint: ScopedReachabilityConstraintId,
    ) {
        self.live_bindings
            .record_reachability_constraint(reachability, constraint);
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, get_size2::GetSize)]
pub(crate) struct PlaceState {
    declarations: Declarations,
    bindings: Bindings,
}

impl PlaceState {
    /// Return a new [`PlaceState`] representing an unbound, undeclared place.
    pub(super) fn undefined(reachability: ScopedReachabilityConstraintId) -> Self {
        Self {
            declarations: Declarations::undeclared(reachability),
            bindings: Bindings::unbound(reachability),
        }
    }

    /// Record a newly-encountered binding for this place.
    pub(super) fn record_binding(
        &mut self,
        binding_id: ScopedDefinitionId,
        reachability_constraint: ScopedReachabilityConstraintId,
        is_class_scope: bool,
        is_place_name: bool,
        previous_definitions: PreviousDefinitions,
        can_be_shadowed: FutureDefinitions,
    ) {
        debug_assert_ne!(binding_id, ScopedDefinitionId::UNBOUND);
        self.bindings.record_binding(
            binding_id,
            reachability_constraint,
            is_class_scope,
            is_place_name,
            previous_definitions,
            can_be_shadowed,
        );
    }

    /// Add given constraint to all live bindings.
    pub(super) fn record_narrowing_constraint(
        &mut self,
        narrowing_constraints: &mut NarrowingConstraintsBuilder,
        constraint: ScopedNarrowingConstraint,
    ) {
        self.bindings
            .record_narrowing_constraint(narrowing_constraints, constraint);
    }

    /// Add the given constraint to live bindings that were also present at an earlier use.
    pub(super) fn record_narrowing_constraint_for_bindings_at_use(
        &mut self,
        narrowing_constraints: &mut NarrowingConstraintsBuilder,
        constraint: ScopedNarrowingConstraint,
        bindings_at_use: &Bindings,
    ) {
        self.bindings
            .live_bindings
            .record_narrowing_constraint_for_bindings(
                narrowing_constraints,
                constraint,
                &bindings_at_use.iter().map(LiveBinding::binding),
            );
    }

    /// Add the given constraint to live bindings selected by definition ID.
    pub(super) fn record_narrowing_constraint_for_bindings(
        &mut self,
        narrowing_constraints: &mut NarrowingConstraintsBuilder,
        constraint: ScopedNarrowingConstraint,
        bindings: &[ScopedDefinitionId],
    ) {
        self.bindings
            .live_bindings
            .record_narrowing_constraint_for_bindings(
                narrowing_constraints,
                constraint,
                &bindings.iter().copied(),
            );
    }

    /// Add given reachability constraint to all live bindings.
    pub(super) fn record_reachability_constraint(
        &mut self,
        reachability_constraints: &mut ReachabilityConstraintsBuilder,
        constraint: ScopedReachabilityConstraintId,
    ) {
        self.bindings
            .record_reachability_constraint(reachability_constraints, constraint);
        self.declarations
            .record_reachability_constraint(reachability_constraints, constraint);
    }

    /// Record a newly-encountered declaration of this place.
    pub(super) fn record_declaration(
        &mut self,
        declaration_id: ScopedDefinitionId,
        reachability_constraint: ScopedReachabilityConstraintId,
    ) {
        self.declarations.record_declaration(
            declaration_id,
            reachability_constraint,
            PreviousDefinitions::AreShadowed,
        );
    }

    /// Record an import that may contribute qualifiers independently of a declared type.
    pub(super) fn record_imported_qualifier(
        &mut self,
        declaration_id: ScopedDefinitionId,
        reachability_constraint: ScopedReachabilityConstraintId,
    ) {
        self.declarations.record_imported_qualifier(
            declaration_id,
            reachability_constraint,
            PreviousDefinitions::AreShadowed,
        );
    }

    pub(super) fn clear_imported_qualifiers(&mut self) {
        self.declarations.clear_imported_qualifiers();
    }

    /// Merge another [`PlaceState`] into this one.
    pub(super) fn merge(
        &mut self,
        b: PlaceState,
        narrowing_constraints: &mut NarrowingConstraintsBuilder,
        reachability_constraints: &mut ReachabilityConstraintsBuilder,
    ) {
        self.bindings
            .merge(b.bindings, narrowing_constraints, reachability_constraints);
        self.declarations
            .merge(b.declarations, reachability_constraints);
    }

    pub(super) fn bindings(&self) -> &Bindings {
        &self.bindings
    }

    pub(super) fn declarations(&self) -> &Declarations {
        &self.declarations
    }

    pub(super) fn into_parts(self) -> (Bindings, Declarations) {
        (self.bindings, self.declarations)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ruff_index::Idx;

    use crate::predicate::ScopedPredicateId;

    #[track_caller]
    fn assert_bindings(place: &PlaceState, expected: &[(u32, ScopedNarrowingConstraint)]) {
        let actual: Vec<(u32, ScopedNarrowingConstraint)> = place
            .bindings()
            .iter()
            .map(|live_binding| {
                (
                    live_binding.binding().as_u32(),
                    live_binding.narrowing_constraint(),
                )
            })
            .collect();
        assert_eq!(actual, expected);
    }

    #[track_caller]
    fn assert_declarations(place: &PlaceState, expected: &[&str]) {
        let actual = place
            .declarations()
            .iter()
            .map(|live_declaration| {
                let declaration = live_declaration.declaration();
                if declaration == ScopedDefinitionId::UNBOUND {
                    "undeclared".into()
                } else if live_declaration.is_imported_qualifier() {
                    format!("{} (imported qualifier)", declaration.as_u32())
                } else {
                    declaration.as_u32().to_string()
                }
            })
            .collect::<Vec<_>>();
        assert_eq!(actual, expected);
    }

    #[test]
    fn unbound() {
        let sym = PlaceState::undefined(ScopedReachabilityConstraintId::ALWAYS_TRUE);

        assert_bindings(&sym, &[(0, ScopedNarrowingConstraint::ALWAYS_TRUE)]);
    }

    #[test]
    fn with() {
        let mut sym = PlaceState::undefined(ScopedReachabilityConstraintId::ALWAYS_TRUE);
        sym.record_binding(
            ScopedDefinitionId::from_u32(1),
            ScopedReachabilityConstraintId::ALWAYS_TRUE,
            false,
            true,
            PreviousDefinitions::AreShadowed,
            FutureDefinitions::ShadowThisOne,
        );

        assert_bindings(&sym, &[(1, ScopedNarrowingConstraint::ALWAYS_TRUE)]);
    }

    #[test]
    fn future_definitions_can_opt_out_of_shadowing() {
        let mut sym = PlaceState::undefined(ScopedReachabilityConstraintId::ALWAYS_TRUE);
        sym.record_binding(
            ScopedDefinitionId::from_u32(1),
            ScopedReachabilityConstraintId::ALWAYS_TRUE,
            false,
            true,
            PreviousDefinitions::AreKept,
            FutureDefinitions::DontShadowThisOne,
        );
        sym.record_binding(
            ScopedDefinitionId::from_u32(2),
            ScopedReachabilityConstraintId::ALWAYS_TRUE,
            false,
            true,
            PreviousDefinitions::AreShadowed,
            FutureDefinitions::ShadowThisOne,
        );

        assert_bindings(
            &sym,
            &[
                (1, ScopedNarrowingConstraint::ALWAYS_TRUE),
                (2, ScopedNarrowingConstraint::ALWAYS_TRUE),
            ],
        );

        sym.record_binding(
            ScopedDefinitionId::from_u32(3),
            ScopedReachabilityConstraintId::ALWAYS_TRUE,
            false,
            true,
            PreviousDefinitions::AreShadowed,
            FutureDefinitions::ShadowThisOne,
        );

        assert_bindings(
            &sym,
            &[
                (1, ScopedNarrowingConstraint::ALWAYS_TRUE),
                (3, ScopedNarrowingConstraint::ALWAYS_TRUE),
            ],
        );
    }

    #[test]
    fn record_constraint() {
        let mut narrowing_constraints = NarrowingConstraintsBuilder::default();
        let mut sym = PlaceState::undefined(ScopedReachabilityConstraintId::ALWAYS_TRUE);
        sym.record_binding(
            ScopedDefinitionId::from_u32(1),
            ScopedReachabilityConstraintId::ALWAYS_TRUE,
            false,
            true,
            PreviousDefinitions::AreShadowed,
            FutureDefinitions::ShadowThisOne,
        );
        let atom = narrowing_constraints.add_atom(ScopedPredicateId::new(0));
        sym.record_narrowing_constraint(&mut narrowing_constraints, atom);

        assert_bindings(&sym, &[(1, atom)]);
    }

    #[test]
    fn merge() {
        let mut narrowing_constraints = NarrowingConstraintsBuilder::default();
        let mut reachability_constraints = ReachabilityConstraintsBuilder::default();

        // merging the same definition with the same constraint keeps the constraint
        let mut sym1a = PlaceState::undefined(ScopedReachabilityConstraintId::ALWAYS_TRUE);
        sym1a.record_binding(
            ScopedDefinitionId::from_u32(1),
            ScopedReachabilityConstraintId::ALWAYS_TRUE,
            false,
            true,
            PreviousDefinitions::AreShadowed,
            FutureDefinitions::ShadowThisOne,
        );
        let atom0 = narrowing_constraints.add_atom(ScopedPredicateId::new(0));
        sym1a.record_narrowing_constraint(&mut narrowing_constraints, atom0);

        let mut sym1b = PlaceState::undefined(ScopedReachabilityConstraintId::ALWAYS_TRUE);
        sym1b.record_binding(
            ScopedDefinitionId::from_u32(1),
            ScopedReachabilityConstraintId::ALWAYS_TRUE,
            false,
            true,
            PreviousDefinitions::AreShadowed,
            FutureDefinitions::ShadowThisOne,
        );
        sym1b.record_narrowing_constraint(&mut narrowing_constraints, atom0);

        sym1a.merge(
            sym1b,
            &mut narrowing_constraints,
            &mut reachability_constraints,
        );
        let mut sym1 = sym1a;
        // Same constraint on both sides → OR(atom0, atom0) = atom0
        assert_bindings(&sym1, &[(1, atom0)]);

        // merging the same definition with differing constraints produces OR (not empty)
        let mut sym2a = PlaceState::undefined(ScopedReachabilityConstraintId::ALWAYS_TRUE);
        sym2a.record_binding(
            ScopedDefinitionId::from_u32(2),
            ScopedReachabilityConstraintId::ALWAYS_TRUE,
            false,
            true,
            PreviousDefinitions::AreShadowed,
            FutureDefinitions::ShadowThisOne,
        );
        let atom1 = narrowing_constraints.add_atom(ScopedPredicateId::new(1));
        sym2a.record_narrowing_constraint(&mut narrowing_constraints, atom1);

        let mut sym1b = PlaceState::undefined(ScopedReachabilityConstraintId::ALWAYS_TRUE);
        sym1b.record_binding(
            ScopedDefinitionId::from_u32(2),
            ScopedReachabilityConstraintId::ALWAYS_TRUE,
            false,
            true,
            PreviousDefinitions::AreShadowed,
            FutureDefinitions::ShadowThisOne,
        );
        let atom2 = narrowing_constraints.add_atom(ScopedPredicateId::new(2));
        sym1b.record_narrowing_constraint(&mut narrowing_constraints, atom2);

        sym2a.merge(
            sym1b,
            &mut narrowing_constraints,
            &mut reachability_constraints,
        );
        let sym2 = sym2a;
        // Different constraints: OR(atom1, atom2) produces a new TDD node (not a terminal)
        let merged_constraint = sym2
            .bindings()
            .iter()
            .next()
            .unwrap()
            .narrowing_constraint();
        assert_ne!(merged_constraint, ScopedNarrowingConstraint::ALWAYS_TRUE);
        assert_ne!(merged_constraint, ScopedNarrowingConstraint::ALWAYS_FALSE);
        assert_ne!(merged_constraint, atom1);
        assert_ne!(merged_constraint, atom2);

        // merging a constrained definition with unbound keeps both
        let mut sym3a = PlaceState::undefined(ScopedReachabilityConstraintId::ALWAYS_TRUE);
        sym3a.record_binding(
            ScopedDefinitionId::from_u32(3),
            ScopedReachabilityConstraintId::ALWAYS_TRUE,
            false,
            true,
            PreviousDefinitions::AreShadowed,
            FutureDefinitions::ShadowThisOne,
        );
        let atom3 = narrowing_constraints.add_atom(ScopedPredicateId::new(3));
        sym3a.record_narrowing_constraint(&mut narrowing_constraints, atom3);

        let sym2b = PlaceState::undefined(ScopedReachabilityConstraintId::ALWAYS_TRUE);

        sym3a.merge(
            sym2b,
            &mut narrowing_constraints,
            &mut reachability_constraints,
        );
        let sym3 = sym3a;
        let bindings: Vec<_> = sym3
            .bindings()
            .iter()
            .map(|b| (b.binding().as_u32(), b.narrowing_constraint()))
            .collect();
        assert_eq!(bindings.len(), 2);
        assert_eq!(bindings[0].0, 0); // unbound
        assert_eq!(bindings[1].0, 3);
        assert_eq!(bindings[1].1, atom3);

        // merging different definitions keeps them each with their existing constraints
        sym1.merge(
            sym3,
            &mut narrowing_constraints,
            &mut reachability_constraints,
        );
        let sym = sym1;
        let bindings: Vec<_> = sym
            .bindings()
            .iter()
            .map(|b| (b.binding().as_u32(), b.narrowing_constraint()))
            .collect();
        assert_eq!(bindings.len(), 3);
        assert_eq!(bindings[0].0, 0); // unbound
        assert_eq!(bindings[1].0, 1);
        assert_eq!(bindings[1].1, atom0);
        assert_eq!(bindings[2].0, 3);
        assert_eq!(bindings[2].1, atom3);
    }

    #[test]
    fn no_declaration() {
        let sym = PlaceState::undefined(ScopedReachabilityConstraintId::ALWAYS_TRUE);

        assert_declarations(&sym, &["undeclared"]);
    }

    #[test]
    fn record_declaration() {
        let mut sym = PlaceState::undefined(ScopedReachabilityConstraintId::ALWAYS_TRUE);
        sym.record_declaration(
            ScopedDefinitionId::from_u32(1),
            ScopedReachabilityConstraintId::ALWAYS_TRUE,
        );

        assert_declarations(&sym, &["1"]);
    }

    #[test]
    fn record_declaration_override() {
        let mut sym = PlaceState::undefined(ScopedReachabilityConstraintId::ALWAYS_TRUE);
        sym.record_declaration(
            ScopedDefinitionId::from_u32(1),
            ScopedReachabilityConstraintId::ALWAYS_TRUE,
        );
        sym.record_declaration(
            ScopedDefinitionId::from_u32(2),
            ScopedReachabilityConstraintId::ALWAYS_TRUE,
        );

        assert_declarations(&sym, &["2"]);
    }

    #[test]
    fn imported_qualifier_preserves_existing_declaration() {
        let mut sym = PlaceState::undefined(ScopedReachabilityConstraintId::ALWAYS_TRUE);
        sym.record_declaration(
            ScopedDefinitionId::from_u32(1),
            ScopedReachabilityConstraintId::ALWAYS_TRUE,
        );
        sym.record_imported_qualifier(
            ScopedDefinitionId::from_u32(2),
            ScopedReachabilityConstraintId::ALWAYS_TRUE,
        );

        assert_declarations(&sym, &["1", "2 (imported qualifier)"]);

        sym.record_imported_qualifier(
            ScopedDefinitionId::from_u32(3),
            ScopedReachabilityConstraintId::ALWAYS_TRUE,
        );

        assert_declarations(&sym, &["1", "3 (imported qualifier)"]);

        sym.clear_imported_qualifiers();

        assert_declarations(&sym, &["1"]);
    }

    #[test]
    fn imported_qualifier_merge_preserves_alternative_declaration() {
        let mut narrowing_constraints = NarrowingConstraintsBuilder::default();
        let mut reachability_constraints = ReachabilityConstraintsBuilder::default();
        let mut imported = PlaceState::undefined(ScopedReachabilityConstraintId::ALWAYS_TRUE);
        imported.record_imported_qualifier(
            ScopedDefinitionId::from_u32(1),
            ScopedReachabilityConstraintId::ALWAYS_TRUE,
        );

        let mut declared = PlaceState::undefined(ScopedReachabilityConstraintId::ALWAYS_TRUE);
        declared.record_declaration(
            ScopedDefinitionId::from_u32(2),
            ScopedReachabilityConstraintId::ALWAYS_TRUE,
        );

        imported.merge(
            declared,
            &mut narrowing_constraints,
            &mut reachability_constraints,
        );

        assert_declarations(&imported, &["undeclared", "1 (imported qualifier)", "2"]);
    }

    #[test]
    fn record_declaration_merge() {
        let mut narrowing_constraints = NarrowingConstraintsBuilder::default();
        let mut reachability_constraints = ReachabilityConstraintsBuilder::default();
        let mut sym = PlaceState::undefined(ScopedReachabilityConstraintId::ALWAYS_TRUE);
        sym.record_declaration(
            ScopedDefinitionId::from_u32(1),
            ScopedReachabilityConstraintId::ALWAYS_TRUE,
        );

        let mut sym2 = PlaceState::undefined(ScopedReachabilityConstraintId::ALWAYS_TRUE);
        sym2.record_declaration(
            ScopedDefinitionId::from_u32(2),
            ScopedReachabilityConstraintId::ALWAYS_TRUE,
        );

        sym.merge(
            sym2,
            &mut narrowing_constraints,
            &mut reachability_constraints,
        );

        assert_declarations(&sym, &["1", "2"]);
    }

    #[test]
    fn record_declaration_merge_partial_undeclared() {
        let mut narrowing_constraints = NarrowingConstraintsBuilder::default();
        let mut reachability_constraints = ReachabilityConstraintsBuilder::default();
        let mut sym = PlaceState::undefined(ScopedReachabilityConstraintId::ALWAYS_TRUE);
        sym.record_declaration(
            ScopedDefinitionId::from_u32(1),
            ScopedReachabilityConstraintId::ALWAYS_TRUE,
        );

        let sym2 = PlaceState::undefined(ScopedReachabilityConstraintId::ALWAYS_TRUE);

        sym.merge(
            sym2,
            &mut narrowing_constraints,
            &mut reachability_constraints,
        );

        assert_declarations(&sym, &["undeclared", "1"]);
    }
}
