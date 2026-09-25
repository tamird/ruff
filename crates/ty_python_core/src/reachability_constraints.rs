//! # Core data structures for recording reachability constraints.
//!
//! See [`crate::reachability_constraints`] for more details.

use std::cmp::Ordering;
use std::hash::Hash;

use ruff_index::Idx;
use rustc_hash::{FxHashMap, FxHashSet};

use crate::Truthiness;
use crate::interned_nodes::InternedNodes;
use crate::narrowing_constraints::{NarrowingConstraintsBuilder, ScopedNarrowingConstraint};
use crate::predicate::ScopedPredicateId;
use crate::rank::{RankBitBox, RankBitBoxVec};

/// A ternary formula that defines under what conditions a binding is visible. (A ternary formula
/// is just like a boolean formula, but with `Ambiguous` as a third potential result. See the
/// module documentation for more details.)
///
/// The primitive atoms of the formula are [`super::predicate::Predicate`]s, which express some
/// property of the runtime state of the code that we are analyzing.
///
/// We assume that each atom has a stable value each time that the formula is evaluated. An atom
/// that resolves to `Ambiguous` might be true or false, and we can't tell which — but within that
/// evaluation, we assume that the atom has the _same_ unknown value each time it appears. That
/// allows us to perform simplifications like `A ∨ !A → true` and `A ∧ !A → false`.
///
/// That means that when you are constructing a formula, you might need to create distinct atoms
/// for a particular [`super::predicate::Predicate`], if your formula needs to consider how a
/// particular runtime property might be different at different points in the execution of the
/// program.
///
/// reachability constraints are normalized, so equivalent constraints are guaranteed to have equal
/// IDs.
#[derive(Clone, Copy, Eq, Hash, PartialEq, get_size2::GetSize, salsa::SalsaValue)]
pub struct ScopedReachabilityConstraintId(u32);

impl std::fmt::Debug for ScopedReachabilityConstraintId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut f = f.debug_tuple("ScopedReachabilityConstraintId");
        match *self {
            // We use format_args instead of rendering the strings directly so that we don't get
            // any quotes in the output: ScopedReachabilityConstraintId(AlwaysTrue) instead of
            // ScopedReachabilityConstraintId("AlwaysTrue").
            ALWAYS_TRUE => f.field(&format_args!("AlwaysTrue")),
            AMBIGUOUS => f.field(&format_args!("Ambiguous")),
            ALWAYS_FALSE => f.field(&format_args!("AlwaysFalse")),
            _ => f.field(&self.0),
        };
        f.finish()
    }
}

// Internal details:
//
// There are 3 terminals, with hard-coded constraint IDs: true, ambiguous, and false.
//
// _Atoms_ are the underlying Predicates, which are the variables that are evaluated by the
// ternary function.
//
// _Interior nodes_ provide the TDD structure for the formula. Interior nodes are stored in an
// arena Vec, with the constraint ID providing an index into the arena.

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq, get_size2::GetSize)]
pub struct InteriorNode {
    /// A "variable" that is evaluated as part of a TDD ternary function. For reachability
    /// constraints, this is a `Predicate` that represents some runtime property of the Python
    /// code that we are evaluating.
    atom: ScopedPredicateId,
    if_true: ScopedReachabilityConstraintId,
    if_ambiguous: ScopedReachabilityConstraintId,
    if_false: ScopedReachabilityConstraintId,
}

impl InteriorNode {
    pub const fn atom(self) -> ScopedPredicateId {
        self.atom
    }

    pub const fn if_true(self) -> ScopedReachabilityConstraintId {
        self.if_true
    }

    pub const fn if_ambiguous(self) -> ScopedReachabilityConstraintId {
        self.if_ambiguous
    }

    pub const fn if_false(self) -> ScopedReachabilityConstraintId {
        self.if_false
    }
}

impl ScopedReachabilityConstraintId {
    /// A special ID that is used for an "always true" / "always visible" constraint.
    pub const ALWAYS_TRUE: ScopedReachabilityConstraintId =
        ScopedReachabilityConstraintId(0xffff_ffff);

    /// A special ID that is used for an ambiguous constraint.
    pub const AMBIGUOUS: ScopedReachabilityConstraintId =
        ScopedReachabilityConstraintId(0xffff_fffe);

    /// A special ID that is used for an "always false" / "never visible" constraint.
    pub const ALWAYS_FALSE: ScopedReachabilityConstraintId =
        ScopedReachabilityConstraintId(0xffff_fffd);

    pub(crate) fn is_terminal(self) -> bool {
        self.0 >= SMALLEST_TERMINAL.0
    }

    fn as_u32(self) -> u32 {
        self.0
    }
}

impl Idx for ScopedReachabilityConstraintId {
    #[inline]
    fn new(value: usize) -> Self {
        assert!(value <= (SMALLEST_TERMINAL.0 as usize));
        #[expect(clippy::cast_possible_truncation)]
        Self(value as u32)
    }

    #[inline]
    fn index(self) -> usize {
        debug_assert!(!self.is_terminal());
        self.0 as usize
    }
}

// Rebind some constants locally so that we don't need as many qualifiers below.
const ALWAYS_TRUE: ScopedReachabilityConstraintId = ScopedReachabilityConstraintId::ALWAYS_TRUE;
const AMBIGUOUS: ScopedReachabilityConstraintId = ScopedReachabilityConstraintId::AMBIGUOUS;
const ALWAYS_FALSE: ScopedReachabilityConstraintId = ScopedReachabilityConstraintId::ALWAYS_FALSE;
const SMALLEST_TERMINAL: ScopedReachabilityConstraintId = ALWAYS_FALSE;

/// Maximum number of interior TDD nodes per scope. When exceeded, new constraint
/// operations return `AMBIGUOUS` to prevent exponential blowup on pathological inputs
/// (e.g., a 5000-line while loop with hundreds of if-branches). This can lead to less precise
/// reachability analysis and type narrowing.
const MAX_INTERIOR_NODES: usize = 512 * 1024;

/// A predicate's known outcome, or a proven stable value with a query-local identity.
#[derive(Clone, Copy)]
pub enum ReachabilityAtom<K> {
    Known(Truthiness),
    Symbolic { key: K, is_positive: bool },
}

/// A collection of reachability constraints for a given scope.
#[derive(Debug, PartialEq, Eq, get_size2::GetSize)]
pub struct ReachabilityConstraints {
    /// The interior TDD nodes that were marked as used when being built.
    used_interiors: Box<[InteriorNode]>,
    /// A bit vector indicating which interior TDD nodes were marked as used. This is indexed by
    /// the node's [`ScopedReachabilityConstraintId`]. The rank of the corresponding bit gives the
    /// index of that node in the `used_interiors` vector.
    ///
    /// If all interior nodes were retained, the original ID can be used directly instead.
    used_indices: Option<RankBitBox>,
}

impl ReachabilityConstraints {
    /// Look up an interior node by its constraint ID.
    pub fn get_interior_node(&self, id: ScopedReachabilityConstraintId) -> InteriorNode {
        debug_assert!(!id.is_terminal());
        let raw_index = id.as_u32() as usize;
        if let Some(used_indices) = &self.used_indices {
            debug_assert!(
                used_indices.get_bit(raw_index).unwrap_or(false),
                "all used reachability constraints should have been marked as used",
            );
            let index = used_indices.rank(raw_index) as usize;
            self.used_interiors[index]
        } else {
            self.used_interiors[raw_index]
        }
    }

    /// Prove that two paths in the same transfer cannot both occur at runtime.
    ///
    /// Like `narrowing_gate`, this follows concrete predicate outcomes and treats an ambiguous
    /// terminal as a possible path. Interior ambiguous edges describe static knowledge, rather
    /// than a third runtime outcome. Callers must not identify atoms from different loop
    /// iterations. Exhausting the pair budget declines the proof.
    pub fn runtime_paths_are_disjoint(
        &self,
        left: ScopedReachabilityConstraintId,
        right: ScopedReachabilityConstraintId,
        max_pairs: usize,
    ) -> bool {
        let mut pending = vec![(left, right)];
        let mut visited = FxHashSet::default();
        while let Some((left, right)) = pending.pop() {
            if left == ALWAYS_FALSE || right == ALWAYS_FALSE {
                continue;
            }
            if left.is_terminal() && right.is_terminal() {
                return false;
            }
            let pair = if left.as_u32() < right.as_u32() {
                (left, right)
            } else {
                (right, left)
            };
            if !visited.insert(pair) {
                continue;
            }
            if visited.len() > max_pairs {
                return false;
            }
            let left_node = (!left.is_terminal()).then(|| self.get_interior_node(left));
            let right_node = (!right.is_terminal()).then(|| self.get_interior_node(right));
            let atom = left_node
                .map(InteriorNode::atom)
                .into_iter()
                .chain(right_node.map(InteriorNode::atom))
                .max()
                .expect("at least one path has an interior node");
            let branches = |id, node: Option<InteriorNode>| {
                if let Some(InteriorNode {
                    atom: candidate,
                    if_true,
                    if_ambiguous: _,
                    if_false,
                }) = node
                    && candidate == atom
                {
                    (if_true, if_false)
                } else {
                    (id, id)
                }
            };
            let (left_true, left_false) = branches(left, left_node);
            let (right_true, right_false) = branches(right, right_node);
            pending.push((left_true, right_true));
            pending.push((left_false, right_false));
        }
        true
    }

    /// Project a demanded constraint after semantic analysis has identified stable values.
    ///
    /// Unknown predicates follow their ordinary ambiguous edge. Only proven identities remain
    /// symbolic; their ordered ternary reconstruction can eliminate repeated or negated tests.
    /// Both the projection memo and the new graph belong to this evaluation alone.
    pub fn project<K: Copy + Eq + Hash>(
        &self,
        root: ScopedReachabilityConstraintId,
        mut evaluate: impl FnMut(ScopedPredicateId) -> ReachabilityAtom<K>,
    ) -> Truthiness {
        enum Action {
            Visit(ScopedReachabilityConstraintId),
            Select(
                ScopedReachabilityConstraintId,
                ScopedReachabilityConstraintId,
            ),
            Concrete(ScopedReachabilityConstraintId, ScopedPredicateId, bool),
            Symbolic(ScopedReachabilityConstraintId, ScopedPredicateId, bool),
        }
        let mut projected = FxHashMap::default();
        let mut values = FxHashMap::default();
        let mut outcomes = FxHashMap::default();
        let mut conditions = FxHashMap::default();
        let mut graph = ReachabilityConstraintsBuilder::default();
        let mut actions = vec![Action::Visit(root)];
        let converted = |id: ScopedReachabilityConstraintId,
                         projected: &FxHashMap<
            ScopedReachabilityConstraintId,
            ScopedReachabilityConstraintId,
        >| { if id.is_terminal() { id } else { projected[&id] } };
        while let Some(action) = actions.pop() {
            match action {
                Action::Visit(id) => {
                    if id.is_terminal() || projected.contains_key(&id) {
                        continue;
                    }
                    let InteriorNode {
                        atom,
                        if_true,
                        if_ambiguous,
                        if_false,
                    } = self.get_interior_node(id);
                    let outcome = *outcomes.entry(atom).or_insert_with(|| evaluate(atom));
                    match outcome {
                        ReachabilityAtom::Known(truthiness) => {
                            let child = match truthiness {
                                Truthiness::AlwaysTrue => if_true,
                                Truthiness::Ambiguous => if_ambiguous,
                                Truthiness::AlwaysFalse => if_false,
                            };
                            actions.push(Action::Select(id, child));
                            actions.push(Action::Visit(child));
                        }
                        ReachabilityAtom::Symbolic { key, is_positive } => {
                            // Keep the first source atom's ordering; only its identity is reused.
                            let atom = *values.entry(key).or_insert(atom);
                            actions.push(Action::Concrete(id, atom, is_positive));
                            actions.push(Action::Visit(if_false));
                            actions.push(Action::Visit(if_true));
                        }
                    }
                }
                Action::Select(id, child) => {
                    projected.insert(id, converted(child, &projected));
                }
                Action::Concrete(id, atom, is_positive) => {
                    let InteriorNode {
                        atom: _,
                        if_true,
                        if_ambiguous,
                        if_false,
                    } = self.get_interior_node(id);
                    let if_true = converted(if_true, &projected);
                    let if_false = converted(if_false, &projected);
                    // Like the ordinary TDD operations, equal concrete outcomes discard the
                    // ambiguous branch. Avoid demanding predicates that cannot affect the result.
                    if if_true == if_false {
                        projected.insert(id, if_true);
                    } else {
                        actions.push(Action::Symbolic(id, atom, is_positive));
                        actions.push(Action::Visit(if_ambiguous));
                    }
                }
                Action::Symbolic(id, atom, is_positive) => {
                    let InteriorNode {
                        atom: _,
                        if_true,
                        if_ambiguous,
                        if_false,
                    } = self.get_interior_node(id);
                    let if_true = converted(if_true, &projected);
                    let if_ambiguous = converted(if_ambiguous, &projected);
                    let if_false = converted(if_false, &projected);
                    let (if_true, if_false) = if is_positive {
                        (if_true, if_false)
                    } else {
                        (if_false, if_true)
                    };
                    let result = graph.add_conditional(
                        atom,
                        if_true,
                        if_ambiguous,
                        if_false,
                        &mut conditions,
                    );
                    projected.insert(id, result);
                }
            }
        }
        let mut id = converted(root, &projected);
        while !id.is_terminal() {
            let InteriorNode {
                atom: _,
                if_true: _,
                if_ambiguous,
                if_false: _,
            } = graph.interiors[id];
            id = if_ambiguous;
        }
        match id {
            ALWAYS_TRUE => Truthiness::AlwaysTrue,
            ALWAYS_FALSE => Truthiness::AlwaysFalse,
            _ => Truthiness::Ambiguous,
        }
    }

    pub fn used_interiors(&self) -> &[InteriorNode] {
        &self.used_interiors
    }
}

#[derive(Debug, Default)]
pub struct ReachabilityConstraintsBuilder {
    interiors: InternedNodes<ScopedReachabilityConstraintId, InteriorNode>,
    interior_used: RankBitBoxVec,
    not_cache: FxHashMap<ScopedReachabilityConstraintId, ScopedReachabilityConstraintId>,
    and_cache: FxHashMap<
        (
            ScopedReachabilityConstraintId,
            ScopedReachabilityConstraintId,
        ),
        ScopedReachabilityConstraintId,
    >,
    or_cache: FxHashMap<
        (
            ScopedReachabilityConstraintId,
            ScopedReachabilityConstraintId,
        ),
        ScopedReachabilityConstraintId,
    >,
}

impl ReachabilityConstraintsBuilder {
    /// Returns whether new constraint combinations may lose precision at the arena limit.
    pub(crate) fn is_saturated(&self) -> bool {
        self.interiors.len() >= MAX_INTERIOR_NODES
    }

    pub(crate) fn build(self) -> ReachabilityConstraints {
        if self.interior_used.first_zero().is_none() {
            ReachabilityConstraints {
                used_interiors: self.interiors.into_nodes_boxed_slice(),
                used_indices: None,
            }
        } else {
            let used_interiors = self
                .interiors
                .into_node_iterator()
                .zip(&self.interior_used)
                .filter_map(|(interior, used)| used.then_some(interior))
                .collect();
            let used_indices = RankBitBox::from_bits(self.interior_used);
            ReachabilityConstraints {
                used_interiors,
                used_indices: Some(used_indices),
            }
        }
    }

    /// Marks that a particular TDD node is used. This lets us throw away interior nodes that were
    /// only calculated for intermediate values, and which don't need to be included in the final
    /// built result.
    pub(crate) fn mark_used(&mut self, node: ScopedReachabilityConstraintId) {
        if !node.is_terminal() && !self.interior_used[node.index()] {
            self.interior_used.set(node.index(), true);
            let node = self.interiors[node];
            self.mark_used(node.if_true);
            self.mark_used(node.if_ambiguous);
            self.mark_used(node.if_false);
        }
    }

    /// Converts a reachability formula into a narrowing gate.
    ///
    /// An ambiguous reachability leaf cannot exclude a control-flow path, so its
    /// narrowing gate is `ALWAYS_TRUE`, preserving any existing narrowing.
    /// Interior ambiguous branches are omitted because narrowing follows the
    /// runtime-true or runtime-false path of each predicate.
    pub(crate) fn narrowing_gate(
        &self,
        root: ScopedReachabilityConstraintId,
        narrowing_constraints: &mut NarrowingConstraintsBuilder,
    ) -> ScopedNarrowingConstraint {
        enum Action {
            Visit(ScopedReachabilityConstraintId),
            Finish(ScopedReachabilityConstraintId),
        }

        let terminal = |id| match id {
            ScopedReachabilityConstraintId::ALWAYS_TRUE
            | ScopedReachabilityConstraintId::AMBIGUOUS => {
                Some(ScopedNarrowingConstraint::ALWAYS_TRUE)
            }
            ScopedReachabilityConstraintId::ALWAYS_FALSE => {
                Some(ScopedNarrowingConstraint::ALWAYS_FALSE)
            }
            _ => None,
        };

        if let Some(root) = terminal(root) {
            return root;
        }

        let root_node = self.interiors[root];
        if let (Some(if_true), Some(if_false)) =
            (terminal(root_node.if_true), terminal(root_node.if_false))
        {
            return narrowing_constraints.add_conditional(root_node.atom, if_true, if_false);
        }

        let mut converted = FxHashMap::default();
        let mut actions = vec![Action::Visit(root)];

        while let Some(action) = actions.pop() {
            match action {
                Action::Visit(id) => {
                    if terminal(id).is_some() || converted.contains_key(&id) {
                        continue;
                    }

                    let node = self.interiors[id];
                    actions.push(Action::Finish(id));
                    actions.push(Action::Visit(node.if_false));
                    actions.push(Action::Visit(node.if_true));
                }
                Action::Finish(id) => {
                    let node = self.interiors[id];
                    let if_true =
                        terminal(node.if_true).unwrap_or_else(|| converted[&node.if_true]);
                    let if_false =
                        terminal(node.if_false).unwrap_or_else(|| converted[&node.if_false]);
                    let result =
                        narrowing_constraints.add_conditional(node.atom, if_true, if_false);
                    converted.insert(id, result);
                }
            }
        }

        converted[&root]
    }

    /// Implements the ordering that determines which level a TDD node appears at.
    ///
    /// Each interior node checks the value of a single variable (for us, a `Predicate`).
    /// TDDs are ordered such that every path from the root of the graph to the leaves must
    /// check each variable at most once, and must check each variable in the same order.
    ///
    /// We can choose any ordering that we want, as long as it's consistent — with the
    /// caveat that terminal nodes must always be last in the ordering, since they are the
    /// leaf nodes of the graph.
    ///
    /// We currently compare interior nodes by looking at the Salsa IDs of each variable's
    /// `Predicate`, since this is already available and easy to compare. We also _reverse_
    /// the comparison of those Salsa IDs. The Salsa IDs are assigned roughly sequentially
    /// while traversing the source code. Reversing the comparison means `Predicate`s that
    /// appear later in the source will tend to be placed "higher" (closer to the root) in
    /// the TDD graph. We have found empirically that this leads to smaller TDD graphs [1],
    /// since there are often repeated combinations of `Predicate`s from earlier in the
    /// file.
    ///
    /// [1]: https://github.com/astral-sh/ruff/pull/20098
    fn cmp_atoms(
        &self,
        a: ScopedReachabilityConstraintId,
        b: ScopedReachabilityConstraintId,
    ) -> Ordering {
        if a == b || (a.is_terminal() && b.is_terminal()) {
            Ordering::Equal
        } else if a.is_terminal() {
            Ordering::Greater
        } else if b.is_terminal() {
            Ordering::Less
        } else {
            // See https://github.com/astral-sh/ruff/pull/20098 for an explanation of why this
            // ordering is reversed.
            self.interiors[a]
                .atom
                .cmp(&self.interiors[b].atom)
                .reverse()
        }
    }

    /// Adds an interior node, ensuring that we always use the same reachability constraint ID for
    /// equal nodes.
    fn add_interior(&mut self, node: InteriorNode) -> ScopedReachabilityConstraintId {
        // If the true and false branches lead to the same node, we can override the ambiguous
        // branch to go there too. And this node is then redundant and can be reduced.
        if node.if_true == node.if_false {
            return node.if_true;
        }

        let (id, inserted) = self.interiors.intern(node);
        if inserted {
            self.interior_used.push(false);
        }
        id
    }

    /// Reconstruct a ternary test after atoms have been substituted. Child atoms may now
    /// precede or equal `atom`, so cofactor them before using the ordinary node interner.
    fn add_conditional(
        &mut self,
        atom: ScopedPredicateId,
        if_true: ScopedReachabilityConstraintId,
        if_ambiguous: ScopedReachabilityConstraintId,
        if_false: ScopedReachabilityConstraintId,
        cache: &mut FxHashMap<InteriorNode, ScopedReachabilityConstraintId>,
    ) -> ScopedReachabilityConstraintId {
        if if_true == if_false {
            return if_true;
        }
        let key = InteriorNode {
            atom,
            if_true,
            if_ambiguous,
            if_false,
        };
        if let Some(result) = cache.get(&key) {
            return *result;
        }
        if self.is_saturated() {
            return AMBIGUOUS;
        }
        let first = [if_true, if_ambiguous, if_false]
            .into_iter()
            .filter(|id| !id.is_terminal())
            .map(|id| {
                let InteriorNode {
                    atom,
                    if_true: _,
                    if_ambiguous: _,
                    if_false: _,
                } = self.interiors[id];
                atom
            })
            .fold(atom, std::cmp::max);
        let cofactor = |graph: &Self, id: ScopedReachabilityConstraintId, branch| {
            if id.is_terminal() {
                return id;
            }
            let InteriorNode {
                atom,
                if_true,
                if_ambiguous,
                if_false,
            } = graph.interiors[id];
            if atom != first {
                return id;
            }
            match branch {
                Truthiness::AlwaysTrue => if_true,
                Truthiness::Ambiguous => if_ambiguous,
                Truthiness::AlwaysFalse => if_false,
            }
        };
        let result = if first == atom {
            self.add_interior(InteriorNode {
                atom,
                if_true: cofactor(self, if_true, Truthiness::AlwaysTrue),
                if_ambiguous: cofactor(self, if_ambiguous, Truthiness::Ambiguous),
                if_false: cofactor(self, if_false, Truthiness::AlwaysFalse),
            })
        } else {
            let mut branch = |outcome| {
                self.add_conditional(
                    atom,
                    cofactor(self, if_true, outcome),
                    cofactor(self, if_ambiguous, outcome),
                    cofactor(self, if_false, outcome),
                    cache,
                )
            };
            let if_true = branch(Truthiness::AlwaysTrue);
            let if_false = branch(Truthiness::AlwaysFalse);
            let if_ambiguous = if if_true == if_false {
                if_true
            } else {
                branch(Truthiness::Ambiguous)
            };
            self.add_interior(InteriorNode {
                atom: first,
                if_true,
                if_ambiguous,
                if_false,
            })
        };
        cache.insert(key, result);
        result
    }

    /// Adds a new reachability constraint that checks a single [`super::predicate::Predicate`].
    ///
    /// [`ScopedPredicateId`]s are the “variables” that are evaluated by a TDD. A TDD variable has
    /// the same value no matter how many times it appears in the ternary formula that the TDD
    /// represents.
    ///
    /// However, we sometimes have to model how a `Predicate` can have a different runtime
    /// value at different points in the execution of the program. To handle this, you can take
    /// advantage of the fact that the [`super::predicate::Predicates`] arena does not deduplicate
    /// `Predicate`s. You can add a `Predicate` multiple times, yielding different
    /// `ScopedPredicateId`s, which you can then create separate TDD atoms for.
    pub(crate) fn add_atom(
        &mut self,
        predicate: ScopedPredicateId,
    ) -> ScopedReachabilityConstraintId {
        if predicate == ScopedPredicateId::ALWAYS_FALSE {
            ALWAYS_FALSE
        } else if predicate == ScopedPredicateId::ALWAYS_TRUE {
            ALWAYS_TRUE
        } else {
            self.add_interior(InteriorNode {
                atom: predicate,
                if_true: ALWAYS_TRUE,
                if_ambiguous: AMBIGUOUS,
                if_false: ALWAYS_FALSE,
            })
        }
    }

    /// Adds a new reachability constraint that is the ternary NOT of an existing one.
    pub(crate) fn add_not_constraint(
        &mut self,
        a: ScopedReachabilityConstraintId,
    ) -> ScopedReachabilityConstraintId {
        if a == ALWAYS_TRUE {
            return ALWAYS_FALSE;
        } else if a == AMBIGUOUS {
            return AMBIGUOUS;
        } else if a == ALWAYS_FALSE {
            return ALWAYS_TRUE;
        }

        if let Some(cached) = self.not_cache.get(&a) {
            return *cached;
        }

        if self.interiors.len() >= MAX_INTERIOR_NODES {
            return AMBIGUOUS;
        }

        let a_node = self.interiors[a];
        let if_true = self.add_not_constraint(a_node.if_true);
        let if_ambiguous = self.add_not_constraint(a_node.if_ambiguous);
        let if_false = self.add_not_constraint(a_node.if_false);
        let result = self.add_interior(InteriorNode {
            atom: a_node.atom,
            if_true,
            if_ambiguous,
            if_false,
        });
        self.not_cache.insert(a, result);
        result
    }

    /// Adds a new reachability constraint that is the ternary OR of two existing ones.
    pub(crate) fn add_or_constraint(
        &mut self,
        a: ScopedReachabilityConstraintId,
        b: ScopedReachabilityConstraintId,
    ) -> ScopedReachabilityConstraintId {
        match (a, b) {
            (ALWAYS_TRUE, _) | (_, ALWAYS_TRUE) => return ALWAYS_TRUE,
            (ALWAYS_FALSE, other) | (other, ALWAYS_FALSE) => return other,
            _ if a == b => return a,
            _ => {}
        }

        // OR is commutative, which lets us halve the cache requirements
        let (a, b) = if b.0 < a.0 { (b, a) } else { (a, b) };
        if let Some(cached) = self.or_cache.get(&(a, b)) {
            return *cached;
        }

        if self.interiors.len() >= MAX_INTERIOR_NODES {
            return AMBIGUOUS;
        }

        let (atom, if_true, if_ambiguous, if_false) = match self.cmp_atoms(a, b) {
            Ordering::Equal => {
                let a_node = self.interiors[a];
                let b_node = self.interiors[b];
                let if_true = self.add_or_constraint(a_node.if_true, b_node.if_true);
                let if_false = self.add_or_constraint(a_node.if_false, b_node.if_false);
                let if_ambiguous = if if_true == if_false {
                    if_true
                } else {
                    self.add_or_constraint(a_node.if_ambiguous, b_node.if_ambiguous)
                };
                (a_node.atom, if_true, if_ambiguous, if_false)
            }
            Ordering::Less => {
                let a_node = self.interiors[a];
                let if_true = self.add_or_constraint(a_node.if_true, b);
                let if_false = self.add_or_constraint(a_node.if_false, b);
                let if_ambiguous = if if_true == if_false {
                    if_true
                } else {
                    self.add_or_constraint(a_node.if_ambiguous, b)
                };
                (a_node.atom, if_true, if_ambiguous, if_false)
            }
            Ordering::Greater => {
                let b_node = self.interiors[b];
                let if_true = self.add_or_constraint(a, b_node.if_true);
                let if_false = self.add_or_constraint(a, b_node.if_false);
                let if_ambiguous = if if_true == if_false {
                    if_true
                } else {
                    self.add_or_constraint(a, b_node.if_ambiguous)
                };
                (b_node.atom, if_true, if_ambiguous, if_false)
            }
        };

        let result = self.add_interior(InteriorNode {
            atom,
            if_true,
            if_ambiguous,
            if_false,
        });
        self.or_cache.insert((a, b), result);
        result
    }

    /// Adds a new reachability constraint that is the ternary AND of two existing ones.
    pub(crate) fn add_and_constraint(
        &mut self,
        a: ScopedReachabilityConstraintId,
        b: ScopedReachabilityConstraintId,
    ) -> ScopedReachabilityConstraintId {
        match (a, b) {
            (ALWAYS_FALSE, _) | (_, ALWAYS_FALSE) => return ALWAYS_FALSE,
            (ALWAYS_TRUE, other) | (other, ALWAYS_TRUE) => return other,
            _ if a == b => return a,
            _ => {}
        }

        // AND is commutative, which lets us halve the cache requirements
        let (a, b) = if b.0 < a.0 { (b, a) } else { (a, b) };
        if let Some(cached) = self.and_cache.get(&(a, b)) {
            return *cached;
        }

        if self.interiors.len() >= MAX_INTERIOR_NODES {
            return AMBIGUOUS;
        }

        let (atom, if_true, if_ambiguous, if_false) = match self.cmp_atoms(a, b) {
            Ordering::Equal => {
                let a_node = self.interiors[a];
                let b_node = self.interiors[b];
                let if_true = self.add_and_constraint(a_node.if_true, b_node.if_true);
                let if_false = self.add_and_constraint(a_node.if_false, b_node.if_false);
                let if_ambiguous = if if_true == if_false {
                    if_true
                } else {
                    self.add_and_constraint(a_node.if_ambiguous, b_node.if_ambiguous)
                };
                (a_node.atom, if_true, if_ambiguous, if_false)
            }
            Ordering::Less => {
                let a_node = self.interiors[a];
                let if_true = self.add_and_constraint(a_node.if_true, b);
                let if_false = self.add_and_constraint(a_node.if_false, b);
                let if_ambiguous = if if_true == if_false {
                    if_true
                } else {
                    self.add_and_constraint(a_node.if_ambiguous, b)
                };
                (a_node.atom, if_true, if_ambiguous, if_false)
            }
            Ordering::Greater => {
                let b_node = self.interiors[b];
                let if_true = self.add_and_constraint(a, b_node.if_true);
                let if_false = self.add_and_constraint(a, b_node.if_false);
                let if_ambiguous = if if_true == if_false {
                    if_true
                } else {
                    self.add_and_constraint(a, b_node.if_ambiguous)
                };
                (b_node.atom, if_true, if_ambiguous, if_false)
            }
        };

        let result = self.add_interior(InteriorNode {
            atom,
            if_true,
            if_ambiguous,
            if_false,
        });
        self.and_cache.insert((a, b), result);
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn runtime_paths_preserve_unknowns_and_conflicting_outcomes() {
        let mut graph = ReachabilityConstraintsBuilder::default();
        let first = graph.add_atom(ScopedPredicateId::new(0));
        let second = graph.add_atom(ScopedPredicateId::new(1));
        let not_first = graph.add_not_constraint(first);
        let disjunction = graph.add_or_constraint(first, second);
        let neither = graph.add_not_constraint(disjunction);
        for root in [first, second, not_first, disjunction, neither] {
            graph.mark_used(root);
        }
        let graph = graph.build();
        assert!(graph.runtime_paths_are_disjoint(first, not_first, 10));
        assert!(graph.runtime_paths_are_disjoint(neither, disjunction, 10));
        assert!(!graph.runtime_paths_are_disjoint(first, second, 10));
        assert!(!graph.runtime_paths_are_disjoint(first, AMBIGUOUS, 10));
        assert!(!graph.runtime_paths_are_disjoint(AMBIGUOUS, AMBIGUOUS, 10));
        assert!(graph.runtime_paths_are_disjoint(ALWAYS_FALSE, AMBIGUOUS, 0));
        assert!(!graph.runtime_paths_are_disjoint(first, not_first, 0));
    }

    #[test]
    fn projection_correlates_repeated_and_negated_values() {
        for (disjunction, second_positive, expected) in [
            (false, true, Truthiness::AlwaysFalse),
            (true, false, Truthiness::AlwaysTrue),
        ] {
            let mut graph = ReachabilityConstraintsBuilder::default();
            let first = ScopedPredicateId::new(0);
            let second = ScopedPredicateId::new(1);
            let a = graph.add_atom(first);
            let b = graph.add_atom(second);
            let root = if disjunction {
                graph.add_or_constraint(a, b)
            } else {
                let not_b = graph.add_not_constraint(b);
                graph.add_and_constraint(a, not_b)
            };
            graph.mark_used(root);
            let graph = graph.build();
            assert_eq!(
                graph.project(root, |id| ReachabilityAtom::Symbolic {
                    key: 0,
                    is_positive: id == first || second_positive,
                }),
                expected
            );
        }
    }

    #[test]
    fn conditional_projection_orders_and_cofactors_all_children() {
        let mut graph = ReachabilityConstraintsBuilder::default();
        let mut cache = FxHashMap::default();
        let first = ScopedPredicateId::new(0);
        let second = ScopedPredicateId::new(1);
        let a = graph.add_atom(first);
        let b = graph.add_atom(second);
        let not_a = graph.add_not_constraint(a);
        // Both concrete outcomes of the repeated value lead to true.
        assert_eq!(
            graph.add_conditional(first, a, AMBIGUOUS, not_a, &mut cache),
            ALWAYS_TRUE
        );
        // The substituted child precedes its parent in the diagram's ordering. Its ambiguous
        // cofactor differs from an ordinary Boolean conditional and must be preserved.
        let filter = graph.add_interior(InteriorNode {
            atom: first,
            if_true: ALWAYS_TRUE,
            if_ambiguous: ALWAYS_FALSE,
            if_false: ALWAYS_FALSE,
        });
        let expected = graph.add_and_constraint(filter, b);
        let result = graph.add_conditional(first, b, ALWAYS_FALSE, ALWAYS_FALSE, &mut cache);
        assert_eq!(result, expected);
        let InteriorNode {
            atom,
            if_true: _,
            if_ambiguous: _,
            if_false: _,
        } = graph.interiors[result];
        assert_eq!(atom, second);
    }

    #[test]
    fn projection_preserves_existing_ambiguity() {
        let graph = ReachabilityConstraintsBuilder::default().build();
        assert_eq!(
            graph.project::<usize>(AMBIGUOUS, |_| unreachable!("terminal has no predicate")),
            Truthiness::Ambiguous
        );
        let mut graph = ReachabilityConstraintsBuilder::default();
        let root = graph.add_interior(InteriorNode {
            atom: ScopedPredicateId::new(0),
            if_true: ALWAYS_TRUE,
            if_ambiguous: ALWAYS_FALSE,
            if_false: ALWAYS_FALSE,
        });
        graph.mark_used(root);
        assert_eq!(
            graph.build().project(root, |_| ReachabilityAtom::Symbolic {
                key: 0,
                is_positive: true
            }),
            Truthiness::AlwaysFalse
        );
    }

    #[test]
    fn projection_skips_redundant_ambiguous_branch() {
        let mut graph = ReachabilityConstraintsBuilder::default();
        let first = ScopedPredicateId::new(0);
        let second = ScopedPredicateId::new(1);
        let unused = ScopedPredicateId::new(2);
        let parent = ScopedPredicateId::new(3);
        let if_true = graph.add_atom(first);
        let if_false = graph.add_atom(second);
        let if_ambiguous = graph.add_atom(unused);
        let root = graph.add_interior(InteriorNode {
            atom: parent,
            if_true,
            if_ambiguous,
            if_false,
        });
        graph.mark_used(root);
        assert_eq!(
            graph.build().project(root, |id| {
                assert_ne!(id, unused, "equal outcomes do not demand this predicate");
                if id == parent {
                    ReachabilityAtom::Symbolic {
                        key: 0,
                        is_positive: true,
                    }
                } else {
                    ReachabilityAtom::Known(Truthiness::AlwaysTrue)
                }
            }),
            Truthiness::AlwaysTrue
        );
    }

    #[test]
    fn repeated_operations_remain_stable_at_capacity() {
        let mut constraints = ReachabilityConstraintsBuilder::default();
        let a = constraints.add_atom(ScopedPredicateId::new(0));
        let not_a = constraints.add_not_constraint(a);
        let b = constraints.add_atom(ScopedPredicateId::new(1));
        let c = constraints.add_atom(ScopedPredicateId::new(2));
        let disjunction = constraints.add_or_constraint(a, c);
        let mut conditionals = FxHashMap::default();
        let conditional = constraints.add_conditional(
            ScopedPredicateId::new(3),
            b,
            AMBIGUOUS,
            c,
            &mut conditionals,
        );
        assert_ne!(conditional, AMBIGUOUS);
        while constraints.interiors.len() < MAX_INTERIOR_NODES - 1 {
            constraints.add_atom(ScopedPredicateId::new(constraints.interiors.len() + 10));
        }

        // The first conjunction reaches the cap. Its completed result remains cached
        // for later callers with identical operands.
        let conjunction = constraints.add_and_constraint(a, b);
        assert!(constraints.interiors.len() >= MAX_INTERIOR_NODES);
        assert_ne!(conjunction, AMBIGUOUS);
        assert_eq!(constraints.add_and_constraint(a, b), conjunction);
        assert_eq!(constraints.add_or_constraint(a, c), disjunction);
        assert_eq!(constraints.add_and_constraint(a, c), AMBIGUOUS);
        assert_eq!(constraints.add_or_constraint(b, c), AMBIGUOUS);
        assert_eq!(
            constraints.add_conditional(
                ScopedPredicateId::new(3),
                b,
                AMBIGUOUS,
                c,
                &mut conditionals,
            ),
            conditional
        );
        assert_eq!(
            constraints.add_conditional(ScopedPredicateId::new(3), a, b, c, &mut conditionals,),
            AMBIGUOUS
        );
        let saturated = constraints.add_and_constraint(a, c);
        constraints.mark_used(a);
        constraints.mark_used(not_a);
        let constraints = constraints.build();
        assert!(constraints.runtime_paths_are_disjoint(a, not_a, 10));
        assert!(!constraints.runtime_paths_are_disjoint(a, saturated, 10));
    }
}
