//! [`PathAssignments`] and friends

use std::cmp::Ordering;
use std::collections::VecDeque;
use std::fmt::Debug;
use std::ops::{ControlFlow, Range};

use indexmap::map::Entry;
use itertools::Itertools;
use rustc_hash::{FxHashMap, FxHashSet};

use ruff_index::{IndexVec, newtype_index};

use crate::types::constraints::sequents::{CachedSequent, Sequent, SequentGroup, SequentMap};
use crate::types::constraints::support::Support;
use crate::types::constraints::variables::AtomicConstraint;
use crate::types::constraints::variables::AtomicConstraint::{
    ConcreteEquivalence, ConcreteLower, ConcreteUpper, TypeVarEquivalence, TypeVarRange,
};
use crate::types::constraints::{
    Assignment, AtomicConstraintId, ConstraintSetStorage, Node, NodeId, PathVisitor, SourceOrderId,
    TypeVarId,
};
use crate::{Db, FxIndexMap, FxIndexSet, ProgramEnvironment};

type PathSequent = Sequent<AtomicConstraintId, u16, (NodeId, Option<SourceOrderId>)>;

/// The position of an assignment in insertion order.
#[newtype_index]
struct AssignmentIndex;

/// The collection of constraints that we know to be true or false at a certain point when
/// traversing a BDD.
///
/// An important part of this traversal is that not all of those constraints come directly from the
/// BDD, since constraints are not independent. In particular, there can be "implications", which
/// record e.g. when two constraints both being true imply another:
/// `A ≤ list[B] ∧ B ≤ int → A ≤ list[int]`. If we see `A ≤ list[B]` and `B ≤ int` in a BDD path,
/// we can _assume_ that `A ≤ list[int]` also holds, even if it doesn't actually appear in the BDD.
///
/// Unfortunately, there are certain implications that are technically true, but not helpful;
/// for instance, because they cause us to endlessly expand a constraint by substituting a bound
/// into itself.
///
/// We use a "fuel" mechanism to prevent these kinds of situations, without having to play
/// whack-a-mole to implement detection patterns for all of the pathological patterns. Each
/// derived constraint costs at least one unit of fuel. Nested typevars increase that cost according
/// to their depth, as does any constructor depth introduced relative to the antecedents. Measuring
/// structural growth instead of absolute depth ensures that propagating an existing complex
/// concrete bound remains cheap, while repeatedly wrapping that bound continues to consume path
/// fuel after no nested typevars remain.
///
/// We track this fuel in two ways: First, there is a global limit on the total amount of work we
/// are willing to do for a particular BDD path traversal. Second, there is a more focused
/// "per-path" limit, which records how far removed a derived constraint is from a constraint that
/// actually appears in the BDD. If either of those limits are exceeded, we ignore the derived
/// constraint that we are currently considering.
#[derive(Debug)]
pub(crate) struct PathAssignments {
    /// All of the rules that we know for inferring derived constraints on the current path.
    sequents: Vec<PathSequent>,
    /// The sequents that can fire when a particular assignment is added to the path.
    sequent_triggers: FxHashMap<Assignment<AtomicConstraintId>, Vec<usize>>,
    /// Whole relations activated by atomic antecedents on this path.
    relations: FxIndexMap<usize, u16>,
    visiting_relations: FxHashSet<usize>,
    /// Atomic edges inside a derived relation continue the antecedents' fuel chain.
    origin_fuel: AssignmentFuel,
    /// Each assignment's source constraint and greatest remaining per-path fuel.
    pub(super) assignments: FxIndexMap<Assignment<AtomicConstraintId>, (AtomicConstraintId, u16)>,
    /// Constraints that have been _replaced_ with other constraints on this path, because a
    /// sequent substituted an exact type for some typevar.
    substituted_constraints: FxIndexSet<AtomicConstraintId>,
    /// The typevars that are bound by a quantifier on this path.
    pub(super) quantified_typevars: Support,
    /// Positions in `assignments`, cleared when their branch is left. Fuel stays in the map so
    /// replenishment and rollback do not need to update these indices.
    positive_assignment_indices: IndexVec<AtomicConstraintId, Option<AssignmentIndex>>,
    negative_assignment_indices: IndexVec<AtomicConstraintId, Option<AssignmentIndex>>,
    /// Previous fuel values, keyed by assignment index, for rolling back replenishments when
    /// leaving a BDD branch. Keeping the maximum in `assignments` makes fuel lookups constant-time.
    fuel_undo: Vec<(usize, u16)>,
    /// The amount of global fuel that remains across all assignments and paths.
    remaining_overall_fuel: u16,
    /// Constraints that we have discovered, mapped to whether we have processed them yet. (This
    /// ensures a stable order for all of the derived constraints that we create, while still
    /// letting us create them lazily.)
    discovered: FxIndexMap<AtomicConstraintId, bool>,
    /// Constraint pairs that we have already checked and added to `sequents`.
    elaborated_pairs: FxHashSet<(AtomicConstraintId, AtomicConstraintId)>,

    /// Consequents grouped by the discovery call that introduced their sequents.
    single_replay_consequents: FxHashMap<AtomicConstraintId, Vec<AtomicConstraintId>>,
    pair_replay_consequents:
        FxHashMap<(AtomicConstraintId, AtomicConstraintId), Vec<AtomicConstraintId>>,

    /// Type variables that only involve concrete constraints and so do not participate in sequent
    /// discovery.
    independent_typevars: FxHashSet<TypeVarId>,

    /// Derived assignments that have been queued up to be added to the current path.
    assignment_queue: VecDeque<(Assignment<AtomicConstraintId>, AssignmentFuel)>,

    /// The next chunk of derived assignments that have been queued up to add to the current path.
    /// If we derive the same assignment multiple times, we keep the derivation that lets us make
    /// the most additional progress (more remaining fuel for this derivation chain, less overall
    /// fuel consumed).
    new_assignments: FxIndexMap<Assignment<AtomicConstraintId>, AssignmentFuel>,
}

/// The total amount of fuel that we are willing to spend for this path traversal. This was
/// chosen empirically, to balance performance with accurate ecosystem diagnostics.
const OVERALL_FUEL_BUDGET: u16 = 256;

/// Whether two constraints with disjoint, complete supports can still derive sequents.
///
/// A concrete lower/upper, lower/equality, or upper/equality pair can relate its type variables
/// through a shared concrete pivot. Every other pair requires a shared type variable.
fn can_interact_without_shared_typevars(
    left: AtomicConstraint<'_>,
    right: AtomicConstraint<'_>,
) -> bool {
    match (left, right) {
        (ConcreteLower(_), ConcreteUpper(_) | ConcreteEquivalence(_))
        | (ConcreteUpper(_) | ConcreteEquivalence(_), ConcreteLower(_))
        | (ConcreteUpper(_), ConcreteEquivalence(_))
        | (ConcreteEquivalence(_), ConcreteUpper(_)) => true,
        (
            ConcreteLower(_)
            | ConcreteUpper(_)
            | ConcreteEquivalence(_)
            | TypeVarRange(_)
            | TypeVarEquivalence(_),
            ConcreteLower(_)
            | ConcreteUpper(_)
            | ConcreteEquivalence(_)
            | TypeVarRange(_)
            | TypeVarEquivalence(_),
        ) => false,
    }
}

/// The maximum number of "trips through the sequent map" that we are willing to take for a
/// derived constraint. This records how far removed we are from a constraint that comes
/// directly from the BDD.
const PATH_FUEL_BUDGET: u16 = 8;

/// The fuel cost of deriving a particular assignment during BDD path walking.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct AssignmentFuel {
    /// The amount of fuel consumed when deriving the assignment, or None if this assignment came
    /// directly from the BDD
    consumed: Option<u16>,
    /// The amount of fuel remaining on the derivation path after deriving this assignment
    remaining: u16,
}

impl AssignmentFuel {
    fn origin() -> AssignmentFuel {
        AssignmentFuel {
            consumed: None,
            remaining: PATH_FUEL_BUDGET,
        }
    }

    fn derived(consumed: u16, remaining: u16) -> AssignmentFuel {
        AssignmentFuel {
            consumed: Some(consumed),
            remaining,
        }
    }

    fn is_derived(self) -> bool {
        self.consumed.is_some()
    }
}

impl PartialOrd for AssignmentFuel {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for AssignmentFuel {
    fn cmp(&self, other: &Self) -> Ordering {
        let self_key = (self.remaining, std::cmp::Reverse(self.consumed));
        let other_key = (other.remaining, std::cmp::Reverse(other.consumed));
        self_key.cmp(&other_key)
    }
}

impl Default for PathAssignments {
    fn default() -> Self {
        Self {
            sequents: Vec::default(),
            sequent_triggers: FxHashMap::default(),
            relations: FxIndexMap::default(),
            visiting_relations: FxHashSet::default(),
            origin_fuel: AssignmentFuel::origin(),
            assignments: FxIndexMap::default(),
            substituted_constraints: FxIndexSet::default(),
            quantified_typevars: Support::default(),
            positive_assignment_indices: IndexVec::default(),
            negative_assignment_indices: IndexVec::default(),
            fuel_undo: Vec::default(),
            remaining_overall_fuel: OVERALL_FUEL_BUDGET,
            discovered: FxIndexMap::default(),
            elaborated_pairs: FxHashSet::default(),
            single_replay_consequents: FxHashMap::default(),
            pair_replay_consequents: FxHashMap::default(),
            independent_typevars: FxHashSet::default(),
            assignment_queue: VecDeque::default(),
            new_assignments: FxIndexMap::default(),
        }
    }
}

impl PathAssignments {
    /// Orders projected facts by replaying the rules already discovered during this walk.
    ///
    /// Projection emits derived facts in TDD branch order. Retaining that order can prevent
    /// recursive relations from converging when an equivalent diagram is rebuilt in a different
    /// arena. Start with the original source order and visit each rule's consequences in order,
    /// including intermediate facts that are themselves projected away. This only replays cached
    /// rules; it does not derive more facts or change the walk's assignments and fuel.
    pub(super) fn projection_source_order(
        &self,
        storage: &mut ConstraintSetStorage<'_>,
        original_source_order: Option<SourceOrderId>,
        derived_source_order: Option<SourceOrderId>,
    ) -> Option<SourceOrderId> {
        let emitted = storage.calculate_source_orders(derived_source_order);
        if emitted.is_empty() {
            return None;
        }
        let mut ordered = storage.calculate_source_orders(original_source_order);
        ordered.retain(|constraint| self.discovered.contains_key(constraint));
        let mut index = 0;
        // Once all emitted facts have positions, later appends cannot change their relative order.
        while !emitted.is_subset(&ordered)
            && let Some(constraint) = ordered.get_index(index).copied()
        {
            if self.discovered.get(&constraint) == Some(&true) {
                if let Some(consequents) = self.single_replay_consequents.get(&constraint) {
                    ordered.extend(
                        consequents
                            .iter()
                            .copied()
                            .filter(|constraint| self.discovered.contains_key(constraint)),
                    );
                }
            }
            for earlier_index in 0..index {
                let earlier = ordered[earlier_index];
                // Pair rules are not commutative. Replay the orientation used by this walk,
                // which can differ from the order in which the replay reaches its inputs.
                let pair = [(earlier, constraint), (constraint, earlier)]
                    .into_iter()
                    .find(|pair| self.elaborated_pairs.contains(pair));
                if let Some(consequents) =
                    pair.and_then(|pair| self.pair_replay_consequents.get(&pair))
                {
                    ordered.extend(
                        consequents
                            .iter()
                            .copied()
                            .filter(|constraint| self.discovered.contains_key(constraint)),
                    );
                }
            }
            index += 1;
        }
        debug_assert!(emitted.is_subset(&ordered));
        ordered
            .into_iter()
            .filter(|constraint| emitted.contains(constraint))
            .fold(None, |source_order, constraint| {
                let next = storage.atomic_constraint_source_order(constraint);
                storage.ordered_source_order(source_order, Some(next))
            })
    }

    pub(super) fn new(
        constraints: impl IntoIterator<Item = AtomicConstraintId>,
        independent_typevars: FxHashSet<TypeVarId>,
    ) -> Self {
        let discovered = constraints
            .into_iter()
            .map(|constraint| (constraint, false))
            .collect();
        Self {
            sequents: Vec::default(),
            sequent_triggers: FxHashMap::default(),
            relations: FxIndexMap::default(),
            visiting_relations: FxHashSet::default(),
            origin_fuel: AssignmentFuel::origin(),
            assignments: FxIndexMap::default(),
            substituted_constraints: FxIndexSet::default(),
            quantified_typevars: Support::default(),
            positive_assignment_indices: IndexVec::default(),
            negative_assignment_indices: IndexVec::default(),
            fuel_undo: Vec::default(),
            discovered,
            elaborated_pairs: FxHashSet::default(),
            single_replay_consequents: FxHashMap::default(),
            pair_replay_consequents: FxHashMap::default(),
            independent_typevars,
            remaining_overall_fuel: OVERALL_FUEL_BUDGET,
            assignment_queue: VecDeque::default(),
            new_assignments: FxIndexMap::default(),
        }
    }

    pub(super) fn visit<'db, V>(
        &mut self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        storage: &mut ConstraintSetStorage<'db>,
        node: NodeId,
        visitor: &mut V,
    ) -> ControlFlow<V::Break, V::Result>
    where
        V: PathVisitor,
    {
        visitor.visit_node()?;
        match node.node() {
            Node::AlwaysTrue => visitor.visit_satisfied(db, storage, self),
            Node::AlwaysFalse => visitor.visit_unsatisfied(db, storage, self),

            Node::Interior(interior) => {
                let interior_value = visitor.enter_interior(db, storage, interior)?;
                let interior = storage.interior_node_data(node);
                let Some(constraint) = interior.constraint.as_atomic(storage) else {
                    panic!("cannot visit non-atomic constraint");
                };

                let if_true = self.walk_edge(
                    db,
                    env,
                    storage,
                    constraint.when_true(),
                    |storage, path, new_range, found_conflict| {
                        let subtree = if found_conflict {
                            visitor.visit_impossible(db, storage, path)
                        } else {
                            path.visit(db, env, storage, interior.if_true, visitor)
                        };
                        match subtree {
                            ControlFlow::Continue(subtree) => visitor.visit_edge(
                                db,
                                storage,
                                &interior_value,
                                subtree,
                                path,
                                new_range,
                            ),
                            ControlFlow::Break(b) => ControlFlow::Break(b),
                        }
                    },
                )?;

                let if_uncertain = self.walk_edge(
                    db,
                    env,
                    storage,
                    constraint.when_unconstrained(),
                    |storage, path, new_range, found_conflict| {
                        let subtree = if found_conflict {
                            visitor.visit_impossible(db, storage, path)
                        } else {
                            path.visit(db, env, storage, interior.if_uncertain, visitor)
                        };
                        match subtree {
                            ControlFlow::Continue(subtree) => visitor.visit_edge(
                                db,
                                storage,
                                &interior_value,
                                subtree,
                                path,
                                new_range,
                            ),
                            ControlFlow::Break(b) => ControlFlow::Break(b),
                        }
                    },
                )?;

                let if_false = self.walk_edge(
                    db,
                    env,
                    storage,
                    constraint.when_false(),
                    |storage, path, new_range, found_conflict| {
                        let subtree = if found_conflict {
                            visitor.visit_impossible(db, storage, path)
                        } else {
                            path.visit(db, env, storage, interior.if_false, visitor)
                        };
                        match subtree {
                            ControlFlow::Continue(subtree) => visitor.visit_edge(
                                db,
                                storage,
                                &interior_value,
                                subtree,
                                path,
                                new_range,
                            ),
                            ControlFlow::Break(b) => ControlFlow::Break(b),
                        }
                    },
                )?;

                visitor.leave_interior(
                    db,
                    storage,
                    &interior_value,
                    if_true,
                    if_uncertain,
                    if_false,
                )
            }
        }
    }

    /// Walks one of the outgoing edges of an internal BDD node. `assignment` describes the
    /// constraint that the BDD node checks, and whether we are following the `if_true` or
    /// `if_false` edge.
    ///
    /// This new assignment might cause this path to become impossible — for instance, if we were
    /// already assuming (from an earlier edge in the path) a constraint that is disjoint with this
    /// one. We might also be able to infer _other_ assignments that do not appear in the BDD
    /// directly, but which are implied from a combination of constraints that we _have_ seen.
    ///
    /// To handle all of this, you provide a callback. If the path has become impossible, we will
    /// return `None` _without invoking the callback_. If the path does not contain any
    /// contradictions, we will invoke the callback and return its result (wrapped in `Some`).
    ///
    /// Your callback will also be provided a slice of all of the constraints that we were able to
    /// infer from `assignment` combined with the information we already knew. (For borrow-check
    /// reasons, we provide this as a [`Range`]; use that range to index into `self.assignments` to
    /// get the list of all of the assignments that we learned from this edge.)
    ///
    /// You will presumably end up making a recursive call of some kind to keep progressing through
    /// the BDD. You should make this call from inside of your callback, so that as you get further
    /// down into the BDD structure, we remember all of the information that we have learned from
    /// the path we're on.
    pub(super) fn walk_edge<'db, R>(
        &mut self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        storage: &mut ConstraintSetStorage<'db>,
        assignment: Assignment<AtomicConstraintId>,
        f: impl FnOnce(&mut ConstraintSetStorage<'db>, &mut Self, Range<usize>, bool) -> R,
    ) -> R {
        // Record a snapshot of the assignments that we already knew held — both so that we can
        // pass along the range of which assignments are new, and so that we can reset back to this
        // point before returning.
        let start = self.assignments.len();
        let relations_start = self.relations.len();
        let substituted_constraints_start = self.substituted_constraints.len();
        let fuel_undo_start = self.fuel_undo.len();
        let previous_remaining_overall_fuel = self.remaining_overall_fuel;

        // Add the new assignment and anything we can derive from it.
        tracing::trace!(
            target: "ty_python_semantic::types::constraints::PathAssignment",
            before = %format_args!(
                "[{}]",
                self.assignments[..start].iter().map(|(assignment, _)| {
                    assignment.into_inner().display(db, env, storage)
                }).format(", "),
            ),
            edge = %assignment.into_inner().display(db, env, storage),
            "walk edge",
        );
        debug_assert!(self.assignment_queue.is_empty());
        self.assignment_queue
            .push_back((assignment, self.origin_fuel));
        let source_constraint = assignment.constraint();
        let found_conflict = self
            .drain_assignment_queue(db, env, storage, source_constraint)
            .is_err();
        if !found_conflict {
            tracing::trace!(
                target: "ty_python_semantic::types::constraints::PathAssignment",
                new = %format_args!(
                    "[{}]",
                    self.assignments[start..].iter().map(|(assignment, _)| {
                        assignment.into_inner().display(db, env, storage)
                    }).format(", "),
                ),
                "new assignments",
            );
        }
        // Otherwise invoke the callback to keep traversing the BDD. The callback will likely
        // traverse additional edges, which might add more to our `assignments` set. But even
        // if that happens, `start..end` will mark the assignments that were added by the
        // `add_assignment` call above — that is, the new assignment for this edge along with
        // the derived information we inferred from it.
        let end = self.assignments.len();
        let result = f(storage, self, start..end, found_conflict);

        // Reset back to where we were before following this edge, so that the caller can reuse a
        // single instance for the entire BDD traversal.
        self.assignment_queue.clear();
        // A branch can replenish an assignment more than once. Restore in reverse order while
        // every referenced assignment still exists.
        for (index, previous_fuel) in self.fuel_undo.drain(fuel_undo_start..).rev() {
            self.assignments[index].1 = previous_fuel;
        }
        for assignment in self.assignments[start..].keys() {
            match *assignment {
                Assignment::Positive(constraint) => {
                    self.positive_assignment_indices[constraint] = None;
                }
                Assignment::Negative(constraint) => {
                    self.negative_assignment_indices[constraint] = None;
                }
                Assignment::Unconstrained(_) => {}
            }
        }
        self.assignments.truncate(start);
        self.relations.truncate(relations_start);
        self.substituted_constraints
            .truncate(substituted_constraints_start);
        self.remaining_overall_fuel = previous_remaining_overall_fuel;
        result
    }

    pub(super) fn pending_relation(&self) -> Option<(usize, NodeId, Option<SourceOrderId>)> {
        self.relations.keys().find_map(|index| {
            if self.visiting_relations.contains(index) {
                return None;
            }
            let Sequent::PairRelation {
                ante1: _,
                ante2: _,
                post: (node, source_order),
                fuel_cost: _,
            } = self.sequents[*index]
            else {
                unreachable!("only whole relations are activated");
            };
            Some((*index, node, source_order))
        })
    }

    pub(super) fn with_relation<R>(
        &mut self,
        index: usize,
        f: impl FnOnce(&mut Self, AssignmentFuel) -> R,
    ) -> R {
        let previous_fuel = self.origin_fuel;
        self.origin_fuel = AssignmentFuel::derived(0, self.relations[&index]);
        self.visiting_relations.insert(index);
        let result = f(self, previous_fuel);
        self.visiting_relations.remove(&index);
        self.origin_fuel = previous_fuel;
        result
    }

    pub(super) fn with_origin_fuel<R>(
        &mut self,
        fuel: AssignmentFuel,
        f: impl FnOnce(&mut Self) -> R,
    ) -> R {
        let previous_fuel = self.origin_fuel;
        self.origin_fuel = fuel;
        let result = f(self);
        self.origin_fuel = previous_fuel;
        result
    }

    pub(super) fn with_quantified_typevars<R>(
        &mut self,
        quantified_typevars: &Support,
        f: impl FnOnce(&mut Self) -> R,
    ) -> R {
        let previous_quantified_typevars = self.quantified_typevars.clone();
        self.quantified_typevars |= quantified_typevars;
        let result = f(self);
        self.quantified_typevars = previous_quantified_typevars;
        result
    }

    pub(super) fn positive_constraints(
        &self,
    ) -> impl Iterator<Item = (AtomicConstraintId, AtomicConstraintId)> + '_ {
        self.assignments.iter().filter_map(
            |(assignment, (source_constraint, _))| match assignment {
                Assignment::Positive(constraint) => Some((*constraint, *source_constraint)),
                Assignment::Negative(_) | Assignment::Unconstrained(_) => None,
            },
        )
    }

    pub(super) fn constraint_is_substituted(&self, constraint: AtomicConstraintId) -> bool {
        self.substituted_constraints.contains(&constraint)
    }

    fn assignment_holds(&self, assignment: Assignment<AtomicConstraintId>) -> bool {
        self.assignment_index(assignment).is_some()
    }

    fn assignment_index(&self, assignment: Assignment<AtomicConstraintId>) -> Option<usize> {
        let indices = match assignment {
            Assignment::Positive(_) => &self.positive_assignment_indices,
            Assignment::Negative(_) => &self.negative_assignment_indices,
            Assignment::Unconstrained(_) => {
                return self.assignments.get_index_of(&assignment);
            }
        };
        indices
            .get(assignment.constraint())
            .copied()
            .flatten()
            .map(AssignmentIndex::as_usize)
    }

    fn record_assignment_index(
        &mut self,
        assignment: Assignment<AtomicConstraintId>,
        index: usize,
    ) {
        let indices = match assignment {
            Assignment::Positive(_) => &mut self.positive_assignment_indices,
            Assignment::Negative(_) => &mut self.negative_assignment_indices,
            Assignment::Unconstrained(_) => return,
        };
        let constraint = assignment.constraint();
        if indices.len() <= constraint.into_inner().as_usize() {
            indices.resize(constraint.into_inner().as_usize() + 1, None);
        }
        indices[constraint] = Some(AssignmentIndex::from_usize(index));
    }

    fn contains_constraint(&self, constraint: AtomicConstraintId) -> bool {
        self.assignment_holds(constraint.when_true())
            || self.assignment_holds(constraint.when_false())
            || self.assignment_holds(constraint.when_unconstrained())
    }

    /// Returns the greatest remaining fuel for any derivation of `assignment` on this path.
    fn max_remaining_fuel_for(&self, assignment: Assignment<AtomicConstraintId>) -> Option<u16> {
        self.assignment_index(assignment)
            .map(|index| self.assignments[index].1)
    }

    fn add_sequents<'db>(
        &mut self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        storage: &mut ConstraintSetStorage<'db>,
        map: &SequentMap<'db>,
    ) -> Range<usize> {
        fn intern_sequents<'db>(
            db: &'db dyn Db,
            env: &ProgramEnvironment<'db>,
            storage: &mut ConstraintSetStorage<'db>,
            sequents: &[CachedSequent<'db>],
            dest: &mut Vec<PathSequent>,
            triggers: &mut FxHashMap<Assignment<AtomicConstraintId>, Vec<usize>>,
        ) {
            for sequent in sequents {
                let sequent_index = dest.len();
                let mut add_trigger = |assignment| {
                    triggers.entry(assignment).or_default().push(sequent_index);
                };

                let sequent = match sequent {
                    Sequent::PairRelation {
                        ante1,
                        ante2,
                        post: (post, provenance),
                        fuel_cost: (),
                    } => {
                        let ante1 = storage.intern_atomic_constraint(db, env, *ante1);
                        let ante2 = storage.intern_atomic_constraint(db, env, *ante2);
                        add_trigger(ante1.when_true());
                        add_trigger(ante2.when_true());
                        let post = storage.load_with_provenance(db, env, post, Some(*provenance));
                        let (ante1_depth, _) =
                            storage.cached_constraint_bound_depth(db, env, ante1);
                        let (ante2_depth, _) =
                            storage.cached_constraint_bound_depth(db, env, ante2);
                        let fuel_cost = storage
                            .calculate_source_orders(post.1)
                            .into_iter()
                            .map(|constraint| {
                                storage.sequent_fuel_cost(
                                    db,
                                    env,
                                    constraint,
                                    ante1_depth.max(ante2_depth),
                                )
                            })
                            .max()
                            .unwrap_or(1);
                        Sequent::PairRelation {
                            ante1,
                            ante2,
                            post,
                            fuel_cost,
                        }
                    }
                    Sequent::SingleTautology { ante } => {
                        let ante = storage.intern_atomic_constraint(db, env, *ante);
                        add_trigger(ante.when_false());
                        Sequent::SingleTautology { ante }
                    }
                    Sequent::PairEquivalence { left, right } => {
                        let left = storage.intern_atomic_constraint(db, env, *left);
                        let right = storage.intern_atomic_constraint(db, env, *right);
                        add_trigger(left.when_true());
                        add_trigger(left.when_false());
                        add_trigger(right.when_true());
                        add_trigger(right.when_false());
                        Sequent::PairEquivalence { left, right }
                    }
                    Sequent::PairImpossibility { ante1, ante2 } => {
                        let ante1 = storage.intern_atomic_constraint(db, env, *ante1);
                        let ante2 = storage.intern_atomic_constraint(db, env, *ante2);
                        add_trigger(ante1.when_true());
                        add_trigger(ante2.when_true());
                        Sequent::PairImpossibility { ante1, ante2 }
                    }
                    Sequent::TripleImpossibility {
                        ante1,
                        ante2,
                        ante3,
                    } => {
                        let ante1 = storage.intern_atomic_constraint(db, env, *ante1);
                        let ante2 = storage.intern_atomic_constraint(db, env, *ante2);
                        let ante3 = storage.intern_atomic_constraint(db, env, *ante3);
                        add_trigger(ante1.when_true());
                        add_trigger(ante2.when_true());
                        add_trigger(ante3.when_true());
                        Sequent::TripleImpossibility {
                            ante1,
                            ante2,
                            ante3,
                        }
                    }
                    Sequent::PairImplication {
                        ante1,
                        ante2,
                        post,
                        is_substitution,
                        ..
                    } => {
                        let ante1 = storage.intern_atomic_constraint(db, env, *ante1);
                        let ante2 = storage.intern_atomic_constraint(db, env, *ante2);
                        let post = storage.intern_atomic_constraint(db, env, *post);
                        add_trigger(ante1.when_true());
                        add_trigger(ante2.when_true());
                        add_trigger(post.when_false());
                        let (ante1_depth, _) =
                            storage.cached_constraint_bound_depth(db, env, ante1);
                        let (ante2_depth, _) =
                            storage.cached_constraint_bound_depth(db, env, ante2);
                        let fuel_cost =
                            storage.sequent_fuel_cost(db, env, post, ante1_depth.max(ante2_depth));
                        Sequent::PairImplication {
                            ante1,
                            ante2,
                            post,
                            fuel_cost,
                            is_substitution: *is_substitution,
                        }
                    }
                    Sequent::SingleImplication { ante, post, .. } => {
                        let ante = storage.intern_atomic_constraint(db, env, *ante);
                        let post = storage.intern_atomic_constraint(db, env, *post);
                        add_trigger(ante.when_true());
                        // A sibling can negate a consequence rolled back after its rule was
                        // discovered. Recheck the still-held antecedent in that branch.
                        add_trigger(post.when_false());
                        let (ante_depth, _) = storage.cached_constraint_bound_depth(db, env, ante);
                        let fuel_cost = storage.sequent_fuel_cost(db, env, post, ante_depth);
                        Sequent::SingleImplication {
                            ante,
                            post,
                            fuel_cost,
                        }
                    }
                };

                dest.push(sequent);
            }
        }

        let start = self.sequents.len();
        for group in &map.sequents {
            match group {
                SequentGroup::Ungrouped(sequents) => {
                    intern_sequents(
                        db,
                        env,
                        storage,
                        sequents,
                        &mut self.sequents,
                        &mut self.sequent_triggers,
                    );
                }
                SequentGroup::Grouped {
                    equivalence,
                    leftwards,
                    rightwards,
                } => {
                    let (first, _) = equivalence.in_builder(db, storage);
                    let (first, second) = if first.is_same_typevar_as(db, equivalence.left) {
                        (leftwards, rightwards)
                    } else {
                        (rightwards, leftwards)
                    };
                    intern_sequents(
                        db,
                        env,
                        storage,
                        first,
                        &mut self.sequents,
                        &mut self.sequent_triggers,
                    );
                    intern_sequents(
                        db,
                        env,
                        storage,
                        second,
                        &mut self.sequents,
                        &mut self.sequent_triggers,
                    );
                }
            }
        }
        let end = self.sequents.len();
        start..end
    }

    /// Update our sequent map to ensure that it holds all of the sequents that involve the given
    /// constraint. We do not calculate the new sequents directly. Instead, we call
    /// [`SequentMap::for_constraint`] and [`for_constraint_pair`][SequentMap::for_constraint_pair]
    /// to calculate _and cache_ the constraints, so that if we walk another constraint set
    /// containing this constraint, we reuse the work to calculate its sequents.
    fn discover_constraint<'db>(
        &mut self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        storage: &mut ConstraintSetStorage<'db>,
        constraint: AtomicConstraintId,
    ) {
        // If we've already processed this constraint, we can skip it.
        let (constraint_index, existing) = self.discovered.insert_full(constraint, true);
        let already_processed = existing.is_some_and(|existing| existing);
        if already_processed {
            return;
        }

        let constraint_data = storage.atomic_constraint_data(constraint);
        if let Some(map) = SequentMap::for_constraint(db, env, constraint_data) {
            let added = self.add_sequents(db, env, storage, map);

            // `projection_source_order` depends on knowing the order that sequents were discovered for
            // each constraint. Since we are salsa-caching sequent derivation, we don't have easy
            // access to that in ConstraintSetStorage, so we need to maintain a local view of that
            // information here.
            self.single_replay_consequents.insert(
                constraint,
                self.sequents[added]
                    .iter()
                    .filter_map(|sequent| match sequent {
                        Sequent::SingleImplication { post, .. }
                        | Sequent::PairImplication { post, .. } => Some(*post),
                        _ => None,
                    })
                    .collect(),
            );
        }

        for existing_index in 0..self.discovered.len() {
            let (existing, _) = self
                .discovered
                .get_index(existing_index)
                .expect("element should be present");
            if *existing == constraint {
                continue;
            }

            let existing_data = storage.atomic_constraint_data(*existing);
            let existing_support = storage.constraint_support(existing.into_inner());
            let constraint_support = storage.constraint_support(constraint.into_inner());

            if existing_support.is_complete()
                && constraint_support.is_complete()
                && !existing_support.overlaps_with(constraint_support)
            {
                // Independent typevars must be checked for disjoint or invalid constraints, but
                // are otherwise already constrained and do not participate in sequent discovery.
                let independent = existing_support
                    .iter()
                    .chain(constraint_support.iter())
                    .any(|typevar| self.independent_typevars.contains(&typevar));

                if independent
                    || !can_interact_without_shared_typevars(existing_data, constraint_data)
                {
                    continue;
                }
            }

            let (a, a_data, b, b_data) = if existing_index < constraint_index {
                (*existing, existing_data, constraint, constraint_data)
            } else {
                (constraint, constraint_data, *existing, existing_data)
            };
            if self.elaborated_pairs.contains(&(a, b)) {
                // We've already elaborated this pair of constraints.
                continue;
            }

            let Some(map) = SequentMap::for_constraint_pair(db, env, a_data, b_data) else {
                continue;
            };
            self.elaborated_pairs.insert((a, b));
            let added = self.add_sequents(db, env, storage, map);

            // `projection_source_order` depends on knowing the order that sequents were discovered for
            // each constraint. Since we are salsa-caching sequent derivation, we don't have easy
            // access to that in ConstraintSetStorage, so we need to maintain a local view of that
            // information here.
            self.pair_replay_consequents.insert(
                (a, b),
                self.sequents[added]
                    .iter()
                    .filter_map(|sequent| match sequent {
                        Sequent::SingleImplication { post, .. }
                        | Sequent::PairImplication { post, .. } => Some(*post),
                        _ => None,
                    })
                    .collect(),
            );
        }
    }

    fn drain_assignment_queue<'db>(
        &mut self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        storage: &mut ConstraintSetStorage<'db>,
        source_constraint: AtomicConstraintId,
    ) -> Result<(), PathAssignmentConflict> {
        while let Some((assignment, fuel)) = self.assignment_queue.pop_front() {
            self.add_assignment(db, env, storage, assignment, source_constraint, fuel)?;
        }
        Ok(())
    }

    /// Adds a new assignment, along with any derived information that we can infer from the new
    /// assignment combined with the assignments we've already seen. If any of this causes the path
    /// to become invalid, due to a contradiction, returns a [`PathAssignmentConflict`] error.
    fn add_assignment<'db>(
        &mut self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        storage: &mut ConstraintSetStorage<'db>,
        assignment: Assignment<AtomicConstraintId>,
        source_constraint: AtomicConstraintId,
        fuel: AssignmentFuel,
    ) -> Result<(), PathAssignmentConflict> {
        if matches!(assignment, Assignment::Unconstrained(_)) {
            // An `Unconstrained` assignment means "this constraint can go either way". If there is
            // already any assignment for this constraint (positive, negative, or unconstrained),
            // the existing assignment is at least as informative, and we skip.
            if self.contains_constraint(assignment.constraint()) {
                return Ok(());
            }

            // Since we don't know whether the assignment's constraint holds or not, we cannot
            // derive any additional information from the sequent map. We still want to record the
            // assignment, but as an optimization we can return early without actually querying the
            // sequent map.
            self.assignments
                .insert(assignment, (source_constraint, fuel.remaining));
            return Ok(());
        }

        // First add this assignment. If it causes a conflict, return that as an error.
        if self.assignment_holds(assignment.negated()) {
            tracing::trace!(
                target: "ty_python_semantic::types::constraints::PathAssignment",
                assignment = %assignment.into_inner().display(db, env, storage),
                facts = %format_args!(
                    "[{}]",
                    self.assignments.iter().map(|(assignment, _)| {
                        assignment.into_inner().display(db, env, storage)
                    }).format(", "),
                ),
                "found contradiction",
            );
            return Err(PathAssignmentConflict);
        }

        match self.assignments.entry(assignment) {
            Entry::Vacant(entry) => {
                if let Some(fuel_cost) = fuel.consumed {
                    self.remaining_overall_fuel =
                        match self.remaining_overall_fuel.checked_sub(fuel_cost) {
                            Some(updated_fuel) => updated_fuel,
                            None => return Ok(()),
                        };
                }
                let index = entry.index();
                entry.insert((source_constraint, fuel.remaining));
                self.record_assignment_index(assignment, index);
            }

            Entry::Occupied(mut entry) => {
                let index = entry.index();
                let (existing_source_constraint, existing_fuel) = entry.get_mut();

                // If a constraint appears both as an "origin" constraint (it actually appears in
                // the BDD structure) and as a "derived" constraint (we infer it from other
                // constraints), we should prefer the origin source constraint, regardless of which
                // order we encounter the various constraints in the BDD.
                if !fuel.is_derived() {
                    *existing_source_constraint = source_constraint;
                }

                // We've already seen this assignment, and in theory have already queried the
                // sequent map for its consequents, which should let us return early.
                //
                // However, a new derivation chain can replenish the fuel for this assignment,
                // giving it more chances to participate in multi-step sequent chains. That means
                // there might be some consequents that were skipped previously due to a lack of
                // fuel, that can be added now because of the replinished fuel budget.

                // There is another derivation of this assignment that already provides at least as
                // much fuel as this constraint. That means replenishing the fuel won't have any
                // effect.
                if *existing_fuel >= fuel.remaining {
                    return Ok(());
                }

                self.fuel_undo.push((index, *existing_fuel));
                *existing_fuel = fuel.remaining;
            }
        }

        // Then use our sequents to add additional facts that we know to be true.
        //
        // TODO: This is very naive at the moment, partly for expediency, and partly because we
        // don't anticipate the sequent maps to be very large. We might consider avoiding the
        // brute-force search.

        self.new_assignments.clear();
        let previous_sequents_len = self.sequents.len();
        let previous_triggers_len = self.sequent_triggers.get(&assignment).map_or(0, Vec::len);
        self.discover_constraint(db, env, storage, assignment.constraint());
        let sequents_len = self.sequents.len();

        // Recheck cached rules when an antecedent is added or an implication's consequence
        // is negated after a sibling branch rolled back its derived assignment.
        for index in 0..previous_triggers_len {
            let sequent_index = self.sequent_triggers[&assignment][index];
            let sequent = self.sequents[sequent_index];
            self.check_sequent(db, env, storage, sequent_index, sequent)?;
        }

        // Sequent elaboration can produce rules whose antecedents do not include the constraint
        // that caused us to discover them. Check every newly discovered sequent once against the
        // complete set of assignments on the current path.
        for sequent_index in previous_sequents_len..sequents_len {
            let sequent = self.sequents[sequent_index];
            self.check_sequent(db, env, storage, sequent_index, sequent)?;
        }

        // If we were able to derive any new assignments from this one, add them to the processing
        // queue.
        self.assignment_queue.extend(self.new_assignments.drain(..));

        Ok(())
    }

    fn enqueue_assignment(
        &mut self,
        assignment: Assignment<AtomicConstraintId>,
        new_fuel: AssignmentFuel,
    ) {
        self.new_assignments
            .entry(assignment)
            .and_modify(|existing_fuel| {
                *existing_fuel = std::cmp::max(*existing_fuel, new_fuel);
            })
            .or_insert(new_fuel);
    }

    fn check_sequent<'db>(
        &mut self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        storage: &mut ConstraintSetStorage<'db>,
        sequent_index: usize,
        sequent: PathSequent,
    ) -> Result<(), PathAssignmentConflict> {
        match sequent {
            Sequent::PairRelation {
                ante1,
                ante2,
                fuel_cost,
                post: _,
            } => {
                let Some(left) = self.max_remaining_fuel_for(ante1.when_true()) else {
                    return Ok(());
                };
                let Some(right) = self.max_remaining_fuel_for(ante2.when_true()) else {
                    return Ok(());
                };
                if let Entry::Vacant(entry) = self.relations.entry(sequent_index)
                    && let Some(remaining) = left.min(right).checked_sub(fuel_cost)
                    && let Some(overall) = self.remaining_overall_fuel.checked_sub(fuel_cost)
                {
                    self.remaining_overall_fuel = overall;
                    entry.insert(remaining);
                }
                Ok(())
            }
            Sequent::PairEquivalence { left, right } => {
                if (self.assignment_holds(left.when_true())
                    && self.assignment_holds(right.when_false()))
                    || (self.assignment_holds(left.when_false())
                        && self.assignment_holds(right.when_true()))
                {
                    Err(PathAssignmentConflict)
                } else {
                    Ok(())
                }
            }
            Sequent::SingleTautology { ante } => {
                self.check_single_tautology(db, env, storage, ante)
            }
            Sequent::PairImpossibility { ante1, ante2 } => {
                self.check_pair_impossibility(db, env, storage, ante1, ante2)
            }
            Sequent::TripleImpossibility {
                ante1,
                ante2,
                ante3,
            } => self.check_triple_impossibility(db, env, storage, ante1, ante2, ante3),
            Sequent::PairImplication {
                ante1,
                ante2,
                post,
                is_substitution,
                fuel_cost,
            } => {
                self.check_pair_implication(
                    db,
                    storage,
                    ante1,
                    ante2,
                    post,
                    is_substitution,
                    fuel_cost,
                );
                Ok(())
            }
            Sequent::SingleImplication {
                ante,
                post,
                fuel_cost,
            } => {
                self.check_single_implication(db, storage, ante, post, fuel_cost);
                Ok(())
            }
        }
    }

    fn check_single_tautology<'db>(
        &mut self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        storage: &mut ConstraintSetStorage<'db>,
        ante: AtomicConstraintId,
    ) -> Result<(), PathAssignmentConflict> {
        if self.assignment_holds(ante.when_false()) {
            // The sequent map says (ante1) is always true, and the current path asserts that
            // it's false.
            tracing::trace!(
                target: "ty_python_semantic::types::constraints::PathAssignment",
                ante = %ante.into_inner().display(db, env, storage),
                facts = %format_args!(
                    "[{}]",
                    self.assignments.iter().map(|(assignment, _)| {
                        assignment.into_inner().display(db, env, storage)
                    }).format(", "),
                ),
                "found contradiction",
            );
            return Err(PathAssignmentConflict);
        }

        Ok(())
    }

    fn check_pair_impossibility<'db>(
        &mut self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        storage: &mut ConstraintSetStorage<'db>,
        ante1: AtomicConstraintId,
        ante2: AtomicConstraintId,
    ) -> Result<(), PathAssignmentConflict> {
        if self.assignment_holds(ante1.when_true()) && self.assignment_holds(ante2.when_true()) {
            // The sequent map says (ante1 ∧ ante2) is an impossible combination, and the
            // current path asserts that both are true.
            tracing::trace!(
                target: "ty_python_semantic::types::constraints::PathAssignment",
                ante1 = %ante1.into_inner().display(db, env, storage),
                ante2 = %ante2.into_inner().display(db, env, storage),
                facts = %format_args!(
                    "[{}]",
                    self.assignments.iter().map(|(assignment, _)| {
                        assignment.into_inner().display(db, env, storage)
                    }).format(", "),
                ),
                "found contradiction",
            );
            return Err(PathAssignmentConflict);
        }

        Ok(())
    }

    fn check_triple_impossibility<'db>(
        &mut self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        storage: &mut ConstraintSetStorage<'db>,
        ante1: AtomicConstraintId,
        ante2: AtomicConstraintId,
        ante3: AtomicConstraintId,
    ) -> Result<(), PathAssignmentConflict> {
        if self.assignment_holds(ante1.when_true())
            && self.assignment_holds(ante2.when_true())
            && self.assignment_holds(ante3.when_true())
        {
            // The sequent map says (ante1 ∧ ante2 ∧ ante3) is an impossible combination, and the
            // current path asserts that all three are true.
            tracing::trace!(
                target: "ty_python_semantic::types::constraints::PathAssignment",
                ante1 = %ante1.into_inner().display(db, env, storage),
                ante2 = %ante2.into_inner().display(db, env, storage),
                ante3 = %ante3.into_inner().display(db, env, storage),
                facts = %format_args!(
                    "[{}]",
                    self.assignments.iter().map(|(assignment, _)| {
                        assignment.into_inner().display(db, env, storage)
                    }).format(", "),
                ),
                "found contradiction",
            );
            return Err(PathAssignmentConflict);
        }

        Ok(())
    }

    #[expect(clippy::too_many_arguments)]
    fn check_pair_implication<'db>(
        &mut self,
        db: &'db dyn Db,
        storage: &ConstraintSetStorage<'db>,
        ante1: AtomicConstraintId,
        ante2: AtomicConstraintId,
        post: AtomicConstraintId,
        is_substitution: bool,
        fuel_cost: u16,
    ) {
        let constraint = storage.atomic_constraint_data(post);
        if constraint.is_reflexive_typevar_relation(db) {
            return;
        }
        let Some(ante1_fuel) = self.max_remaining_fuel_for(ante1.when_true()) else {
            return;
        };
        let Some(ante2_fuel) = self.max_remaining_fuel_for(ante2.when_true()) else {
            return;
        };
        if is_substitution && !self.substituted_constraints.contains(&post) {
            self.substituted_constraints.insert(ante1);
        }
        let available_fuel = ante1_fuel.min(ante2_fuel);
        if let Some(post_fuel) = available_fuel.checked_sub(fuel_cost) {
            self.enqueue_assignment(
                post.when_true(),
                AssignmentFuel::derived(fuel_cost, post_fuel),
            );
        }
    }

    fn check_single_implication<'db>(
        &mut self,
        db: &'db dyn Db,
        storage: &ConstraintSetStorage<'db>,
        ante: AtomicConstraintId,
        post: AtomicConstraintId,
        fuel_cost: u16,
    ) {
        let constraint = storage.atomic_constraint_data(post);
        if constraint.is_reflexive_typevar_relation(db) {
            return;
        }
        let Some(available_fuel) = self.max_remaining_fuel_for(ante.when_true()) else {
            return;
        };
        if let Some(post_fuel) = available_fuel.checked_sub(fuel_cost) {
            self.enqueue_assignment(
                post.when_true(),
                AssignmentFuel::derived(fuel_cost, post_fuel),
            );
        }
    }
}

#[derive(Debug)]
struct PathAssignmentConflict;

#[cfg(test)]
mod tests {
    use std::assert_matches;

    use super::super::sequents::{Sequent, SequentGroup, SequentMap};
    use super::super::solutions::{Polarity, SolutionWalker};
    use super::super::*;

    use crate::db::tests::{TestDb, setup_db};
    use crate::types::{BoundTypeVarInstance, KnownClass, TypeVarVariance};
    use ruff_python_ast::name::Name;

    fn create_typevar<'db>(db: &'db TestDb, name: &'static str) -> BoundTypeVarInstance<'db> {
        BoundTypeVarInstance::synthetic(
            db,
            &db.program_environment(),
            Name::new_static(name),
            TypeVarVariance::Invariant,
        )
    }

    fn create_constraint<'db, 'c>(
        db: &'db TestDb,
        builder: &'c ConstraintSetBuilder<'db>,
        bound_typevar: BoundTypeVarInstance<'db>,
        bound: KnownClass,
    ) -> ConstraintSet<'db, 'c> {
        let env = db.program_environment();
        let ty = bound.to_instance(db, &env);
        ConstraintSet::constrain_typevar_equivalence_bound(db, &env, builder, bound_typevar, ty)
    }

    #[test]
    fn equivalent_provenance_conflicts_preserve_evidence() {
        let db = setup_db();
        let db = &db;
        let env = db.program_environment();
        let t = create_typevar(db, "T");
        let builder = ConstraintSetBuilder::new();
        let integer = KnownClass::Int.to_instance(db, &env);
        let u = Type::TypeVar(create_typevar(db, "U"));
        let cases = [
            create_constraint(db, &builder, t, KnownClass::Int),
            ConstraintSet::constrain_typevar_lower_bound(db, &env, &builder, t, integer),
            ConstraintSet::constrain_typevar_upper_bound(db, &env, &builder, t, integer),
            ConstraintSet::constrain_typevar_upper_bound(db, &env, &builder, t, u),
            ConstraintSet::constrain_typevar_equivalence_bound(db, &env, &builder, t, u),
        ];
        let different = [
            create_constraint(db, &builder, t, KnownClass::Str),
            create_constraint(db, &builder, create_typevar(db, "V"), KnownClass::Int),
        ];
        let mut storage = builder.storage.borrow_mut();
        let different = different.map(|set| {
            storage
                .interior_node_data(set.node)
                .constraint
                .expect_atomic(&storage)
        });
        for case in cases {
            let original = storage
                .interior_node_data(case.node)
                .constraint
                .expect_atomic(&storage);
            let atom = storage.atomic_constraint_data(original);
            let [validity, mixed, evidence] = [
                ConstraintProvenance::Validity,
                ConstraintProvenance::Mixed,
                ConstraintProvenance::Evidence,
            ]
            .map(|provenance| {
                storage.intern_atomic_constraint(db, &env, atom.with_provenance(provenance))
            });
            for first in [validity, mixed, evidence] {
                for second in [validity, mixed, evidence] {
                    let mut path = PathAssignments::new([first, second], FxHashSet::default());
                    path.walk_edge(
                        db,
                        &env,
                        &mut storage,
                        first.when_true(),
                        |storage, path, _, conflict| {
                            assert!(!conflict);
                            // Truth agrees across provenance, but a declaration alone must not become
                            // new inference evidence.
                            assert_eq!(path.assignment_holds(second.when_true()), first == second);
                            for other in different {
                                path.walk_edge(
                                    db,
                                    &env,
                                    storage,
                                    other.when_false(),
                                    |_, _, _, conflict| {
                                        assert!(!conflict);
                                    },
                                );
                            }
                            path.walk_edge(
                                db,
                                &env,
                                storage,
                                second.when_false(),
                                |_, _, _, conflict| {
                                    assert!(conflict);
                                },
                            );
                        },
                    );
                    // Leaving the positive branch removes the conflicting assignment.
                    path.walk_edge(
                        db,
                        &env,
                        &mut storage,
                        second.when_false(),
                        |storage, path, _, conflict| {
                            assert!(!conflict);
                            path.walk_edge(
                                db,
                                &env,
                                storage,
                                first.when_true(),
                                |_, _, _, conflict| {
                                    assert!(conflict);
                                },
                            );
                        },
                    );
                }
            }
        }
    }

    #[test]
    fn negated_consequent_rechecks_a_cached_implication() {
        let db = setup_db();
        let db = &db;
        let env = db.program_environment();
        let t = create_typevar(db, "T");
        let builder = ConstraintSetBuilder::new();
        let exact = create_constraint(db, &builder, t, KnownClass::Object);
        let lower = ConstraintSet::constrain_typevar_lower_bound(
            db,
            &env,
            &builder,
            t,
            KnownClass::Str.to_instance(db, &env),
        );
        let mut storage = builder.storage.borrow_mut();
        let exact = storage
            .interior_node_data(exact.node)
            .constraint
            .expect_atomic(&storage);
        let lower = storage
            .interior_node_data(lower.node)
            .constraint
            .expect_atomic(&storage);
        let mut path = PathAssignments::default();
        path.walk_edge(
            db,
            &env,
            &mut storage,
            exact.when_true(),
            |storage, path, _, conflict| {
                assert!(!conflict);
                // This branch discovers `T = object => str <= T`. Its consequence is then
                // rolled back while the implication remains cached for sibling branches.
                path.walk_edge(db, &env, storage, lower.when_true(), |_, _, _, conflict| {
                    assert!(!conflict)
                });
                path.walk_edge(
                    db,
                    &env,
                    storage,
                    lower.when_false(),
                    |_, _, _, conflict| assert!(conflict),
                );
            },
        );
        // Without the antecedent, the same negative edge is satisfiable.
        path.walk_edge(
            db,
            &env,
            &mut storage,
            lower.when_false(),
            |_, _, _, conflict| assert!(!conflict),
        );
    }

    #[test]
    fn negated_consequent_rechecks_a_cached_pair_implication() {
        let db = setup_db();
        let db = &db;
        let env = db.program_environment();
        let builder = ConstraintSetBuilder::new();
        let left = create_constraint(db, &builder, create_typevar(db, "T"), KnownClass::Int);
        let right = create_constraint(db, &builder, create_typevar(db, "U"), KnownClass::Str);
        let post = create_constraint(db, &builder, create_typevar(db, "V"), KnownClass::Bytes);
        let mut storage = builder.storage.borrow_mut();
        let [left, right, post] = [left, right, post].map(|set| {
            storage
                .interior_node_data(set.node)
                .constraint
                .expect_atomic(&storage)
        });
        let mut map = SequentMap::default();
        map.sequents.push(SequentGroup::Ungrouped(Box::new([
            Sequent::PairImplication {
                ante1: storage.atomic_constraint_data(left),
                ante2: storage.atomic_constraint_data(right),
                post: storage.atomic_constraint_data(post),
                fuel_cost: (),
                is_substitution: false,
            },
        ])));
        let mut path = PathAssignments::default();
        path.walk_edge(
            db,
            &env,
            &mut storage,
            left.when_true(),
            |storage, path, _, conflict| {
                assert!(!conflict);
                path.walk_edge(
                    db,
                    &env,
                    storage,
                    right.when_true(),
                    |storage, path, _, conflict| {
                        assert!(!conflict);
                        path.walk_edge(
                            db,
                            &env,
                            storage,
                            post.when_true(),
                            |storage, path, _, conflict| {
                                assert!(!conflict);
                                path.add_sequents(db, &env, storage, &map);
                            },
                        );
                        path.walk_edge(
                            db,
                            &env,
                            storage,
                            post.when_false(),
                            |_, _, _, conflict| assert!(conflict),
                        );
                    },
                );
                // Removing either antecedent makes the negative consequence satisfiable.
                path.walk_edge(db, &env, storage, post.when_false(), |_, _, _, conflict| {
                    assert!(!conflict)
                });
            },
        );
        path.walk_edge(
            db,
            &env,
            &mut storage,
            right.when_true(),
            |storage, path, _, conflict| {
                assert!(!conflict);
                path.walk_edge(db, &env, storage, post.when_false(), |_, _, _, conflict| {
                    assert!(!conflict)
                });
            },
        );
    }

    #[test]
    fn derived_relations_preserve_witnesses_and_domains() {
        let db = setup_db();
        let db = &db;
        let env = db.program_environment();
        let string = KnownClass::Str.to_instance(db, &env);
        let integer = KnownClass::Int.to_instance(db, &env);
        let left = create_typevar(db, "Left");
        let right = create_typevar(db, "Right");
        let result = create_typevar(db, "Result");
        let list_string = KnownClass::List.to_specialized_instance(db, &env, &[string]);
        let list_integer = KnownClass::List.to_specialized_instance(db, &env, &[integer]);
        for (domain, expected, negative, valid) in [
            (string, list_string, false, true),
            (string, list_integer, false, false),
            (integer, list_string, false, false),
            (integer, list_string, true, true),
            (string, list_string, true, false),
        ] {
            let local = create_typevar(db, "Local").map_bound_or_constraints(db, |_| {
                Some(TypeVarBoundOrConstraints::UpperBound(domain))
            });
            let relation = ConstraintSetBuilder::new().into_owned(|builder| {
                let list_local =
                    KnownClass::List.to_specialized_instance(db, &env, &[Type::TypeVar(local)]);
                let body =
                    create_constraint(db, builder, local, KnownClass::Str).and(db, builder, || {
                        ConstraintSet::constrain_typevar_equivalence_bound(
                            db, &env, builder, result, list_local,
                        )
                    });
                let relation = body.reduce_inferable(
                    db,
                    &env,
                    builder,
                    TypeVarSet::from_typevars(db, [local]),
                );
                if negative {
                    relation.negate(db, builder)
                } else {
                    relation
                }
            });
            let builder = ConstraintSetBuilder::new();
            let lhs = create_constraint(db, &builder, left, KnownClass::Str);
            let rhs = create_constraint(db, &builder, right, KnownClass::Int);
            let set = lhs.and(db, &builder, || rhs).and(db, &builder, || {
                ConstraintSet::constrain_typevar_equivalence_bound(
                    db, &env, &builder, result, expected,
                )
            });
            let mut storage = builder.storage.borrow_mut();
            let ante1 = storage
                .interior_node_data(lhs.node)
                .constraint
                .expect_atomic(&storage);
            let ante2 = storage
                .interior_node_data(rhs.node)
                .constraint
                .expect_atomic(&storage);
            let mut map = SequentMap::default();
            map.sequents
                .push(SequentGroup::Ungrouped(Box::new([Sequent::PairRelation {
                    ante1: storage.atomic_constraint_data(ante1),
                    ante2: storage.atomic_constraint_data(ante2),
                    post: (relation, ConstraintProvenance::Evidence),
                    fuel_cost: (),
                }])));
            let mut path = set
                .node
                .path_assignments(db, &env, &mut storage, set.source_order);
            path.add_sequents(db, &env, &mut storage, &map);
            let inferable = TypeVarSet::from_typevars(db, [left, right, result]);
            let support = Support::from_typevar_set(db, &mut storage, inferable);
            // Reusing the path exercises activation rollback, including negatively walked roots.
            for polarity in [Polarity::Positive, Polarity::Negative] {
                let node = if polarity == Polarity::Positive {
                    set.node
                } else {
                    set.node.negate(&mut storage)
                };
                let orders = storage.calculate_source_orders(set.source_order);
                let mut walker = SolutionWalker::new(
                    db,
                    &mut storage,
                    orders,
                    inferable,
                    UnboundedSolutionLimits,
                    node,
                );
                let ControlFlow::Continue(()) = walker.visit_node(
                    db,
                    &env,
                    &mut storage,
                    &mut path,
                    Some(&support),
                    polarity,
                    node,
                );
                let candidates = walker.finish();
                assert_eq!(
                    !matches!(candidates, CandidateSolutions::Unsatisfiable),
                    valid,
                    "domain={domain:?}, expected={expected:?}, negative={negative}, polarity={polarity:?}"
                );
                let selection = ConstraintSetBuilder::new();
                let solved = candidates.solve(db, &env, &selection);
                if valid {
                    assert_matches!(solved, Solutions::Constrained(SolutionPaths::Complete(solutions)) if
                        solutions.iter().any(|solution| {
                            solution.is_valid() && solution.solved_typevars.iter().any(|binding| {
                                binding.bound_typevar == result && binding.solution == expected
                            })
                        })
                    );
                } else {
                    assert!(matches!(solved, Solutions::Unsatisfiable(_)));
                }
                assert!(path.assignments.is_empty());
                assert!(path.relations.is_empty());
                assert!(path.visiting_relations.is_empty());
            }
        }
    }

    #[test]
    fn derived_relation_evidence_matches_explicit_relation() {
        let db = setup_db();
        let db = &db;
        let env = db.program_environment();
        let left = create_typevar(db, "Left");
        let right = create_typevar(db, "Right");
        let local = create_typevar(db, "Local");
        let result = create_typevar(db, "Result");
        let string = KnownClass::Str.to_instance(db, &env);
        let gradual = UnionType::from_elements(db, &env, [Type::any(), string]);
        let inferable = TypeVarSet::from_typevars(db, [result]);
        let relation = ConstraintSetBuilder::new().into_owned(|builder| {
            create_constraint(db, builder, local, KnownClass::Str)
                .and(db, builder, || {
                    ConstraintSet::constrain_typevar_lower_bound(db, &env, builder, result, gradual)
                })
                .reduce_inferable(db, &env, builder, TypeVarSet::from_typevars(db, [local]))
        });
        for reverse in [false, true] {
            for reload in [false, true] {
                let builder = ConstraintSetBuilder::new();
                let lhs = create_constraint(db, &builder, left, KnownClass::Str);
                let rhs = create_constraint(db, &builder, right, KnownClass::Int);
                let antecedents = lhs.and(db, &builder, || rhs);
                let later = ConstraintSet::constrain_typevar_upper_bound(
                    db, &env, &builder, result, string,
                );
                let explicit = builder.load(db, &env, &relation);
                let explicit = if reverse {
                    later
                        .and(db, &builder, || explicit)
                        .and(db, &builder, || antecedents)
                } else {
                    antecedents
                        .and(db, &builder, || explicit)
                        .and(db, &builder, || later)
                };
                let expected = explicit.solutions(db, &env, inferable).unwrap();
                assert!(matches!(
                    expected,
                    Solutions::Constrained(SolutionPaths::Complete(_))
                ));
                let implicit = if reverse {
                    later.and(db, &builder, || antecedents)
                } else {
                    antecedents.and(db, &builder, || later)
                };
                let implicit = if reload {
                    let owned = match implicit.node.node() {
                        Node::Interior(root) => OwnedConstraintSetBuilder::snapshot(
                            &builder.storage.borrow(),
                            root,
                            implicit.source_order.unwrap(),
                        ),
                        Node::AlwaysTrue | Node::AlwaysFalse => {
                            unreachable!("test relation is nonterminal")
                        }
                    };
                    builder.load(db, &env, &owned)
                } else {
                    implicit
                };
                let mut storage = builder.storage.borrow_mut();
                let ante1 = storage
                    .interior_node_data(lhs.node)
                    .constraint
                    .expect_atomic(&storage);
                let ante2 = storage
                    .interior_node_data(rhs.node)
                    .constraint
                    .expect_atomic(&storage);
                let mut map = SequentMap::default();
                map.sequents
                    .push(SequentGroup::Ungrouped(Box::new([Sequent::PairRelation {
                        ante1: storage.atomic_constraint_data(ante1),
                        ante2: storage.atomic_constraint_data(ante2),
                        post: (relation.clone(), ConstraintProvenance::Evidence),
                        fuel_cost: (),
                    }])));
                let mut path =
                    implicit
                        .node
                        .path_assignments(db, &env, &mut storage, implicit.source_order);
                path.add_sequents(db, &env, &mut storage, &map);
                let support = Support::from_typevar_set(db, &mut storage, inferable);
                let orders = storage.calculate_source_orders(implicit.source_order);
                let mut walker = SolutionWalker::new(
                    db,
                    &mut storage,
                    orders,
                    inferable,
                    UnboundedSolutionLimits,
                    implicit.node,
                );
                let ControlFlow::Continue(()) = walker.visit_node(
                    db,
                    &env,
                    &mut storage,
                    &mut path,
                    Some(&support),
                    Polarity::Positive,
                    implicit.node,
                );
                let candidates = walker.finish();
                drop(storage);
                assert_eq!(
                    candidates.solve(db, &env, &builder),
                    expected,
                    "reverse={reverse}, reload={reload}"
                );
            }
        }
    }

    #[test]
    fn eager_and_lazy_negation_are_equivalent() {
        let db = setup_db();
        let db = &db;
        let env = db.program_environment();
        let t = create_typevar(db, "T");
        let u = create_typevar(db, "U");
        let builder = ConstraintSetBuilder::new();

        let t_int = create_constraint(db, &builder, t, KnownClass::Int);
        let t_bool = create_constraint(db, &builder, t, KnownClass::Bool);
        let u_str = create_constraint(db, &builder, u, KnownClass::Str);
        let u_int = create_constraint(db, &builder, u, KnownClass::Int);

        let lhs = t_int.or(db, &builder, || u_str);
        let rhs = t_bool.or(db, &builder, || u_int);
        let intersection = lhs.and(db, &builder, || rhs);
        let tautology = lhs.or(db, &builder, || lhs.negate(db, &builder));

        let t_bool_upper = ConstraintSet::constrain_typevar_upper_bound(
            db,
            &env,
            &builder,
            t,
            KnownClass::Bool.to_instance(db, &env),
        );
        let t_int_upper = ConstraintSet::constrain_typevar_upper_bound(
            db,
            &env,
            &builder,
            t,
            KnownClass::Int.to_instance(db, &env),
        );
        let implication = t_bool_upper
            .negate(db, &builder)
            .or(db, &builder, || t_int_upper);

        for set in [lhs, rhs, intersection, tautology, implication] {
            assert_eq!(
                set.is_always_satisfied(db, &env),
                set.negate(db, &builder).is_never_satisfied(db, &env)
            );
        }
    }

    #[test]
    fn path_assignments_follow_constraint_source_order() {
        let db = setup_db();
        let db = &db;
        let env = db.program_environment();
        let t = create_typevar(db, "T");
        let u = create_typevar(db, "U");
        let builder = ConstraintSetBuilder::new();
        let t_int = create_constraint(db, &builder, t, KnownClass::Int);
        let u_str = create_constraint(db, &builder, u, KnownClass::Str);

        // Construct the set in the opposite order from constraint creation. This ensures the
        // initializer follows the sidecar rather than either TDD traversal or constraint IDs.
        let set = u_str.and(db, &builder, || t_int);
        let mut storage = builder.storage.borrow_mut();
        let path = set
            .node
            .path_assignments(db, &env, &mut storage, set.source_order);
        let expected = [u_str.node, t_int.node].map(|node| {
            storage
                .interior_node_data(node)
                .constraint
                .expect_atomic(&storage)
        });
        let actual: Vec<_> = path.discovered.keys().copied().collect();

        assert_eq!(actual, expected);
    }

    #[test]
    fn solution_walker_break_restores_path_assignments() {
        let db = setup_db();
        let db = &db;
        let env = db.program_environment();
        let t = create_typevar(db, "T");
        let builder = ConstraintSetBuilder::new();
        let t_int = create_constraint(db, &builder, t, KnownClass::Int);
        let t_str = create_constraint(db, &builder, t, KnownClass::Str);
        let set = t_int.or(db, &builder, || t_str);
        let source_orders = builder
            .storage
            .borrow()
            .calculate_source_orders(set.source_order);
        let inferable = TypeVarSet::from_typevars(db, [t]);
        let expected = CandidateSolutions::compute(
            db,
            &env,
            &mut builder.storage.borrow_mut(),
            set.node,
            inferable,
            set.source_order,
        );

        // Both limits interrupt an edge with path-local assignments: the visit limit stops
        // below the root, and the path limit stops after collecting the first alternative.
        for (remaining_paths, remaining_visits, error) in [
            (usize::MAX, 1, ProjectionError::TraversalBudgetExceeded),
            (1, usize::MAX, ProjectionError::PathBudgetExceeded),
        ] {
            let mut storage = builder.storage.borrow_mut();
            let mut path = set
                .node
                .path_assignments(db, &env, &mut storage, set.source_order);
            let limits = BoundedSolutionLimits {
                remaining_paths,
                remaining_visits,
            };
            let mut walker = SolutionWalker::new(
                db,
                &mut storage,
                source_orders.clone(),
                inferable,
                limits,
                set.node,
            );
            assert_eq!(
                walker.visit_node(
                    db,
                    &env,
                    &mut storage,
                    &mut path,
                    None,
                    Polarity::Positive,
                    set.node
                ),
                ControlFlow::Break(error)
            );
            drop(walker);

            let limits = UnboundedSolutionLimits;
            let mut walker = SolutionWalker::new(
                db,
                &mut storage,
                source_orders.clone(),
                inferable,
                limits,
                set.node,
            );
            let ControlFlow::Continue(()) = walker.visit_node(
                db,
                &env,
                &mut storage,
                &mut path,
                None,
                Polarity::Positive,
                set.node,
            );
            assert_eq!(walker.finish(), expected);
        }
    }
}
