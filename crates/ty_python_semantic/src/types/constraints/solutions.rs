use std::cell::{Cell, RefCell};
use std::marker::PhantomData;
use std::ops::{ControlFlow, Range};

use arrayvec::ArrayVec;
use indexmap::map::Slice;
use rustc_hash::{FxHashMap, FxHashSet};
use smallvec::SmallVec;

use crate::types::constraints::PathBoundSolution;
use crate::types::constraints::paths::PathAssignments;
use crate::types::constraints::projection::{ProjectionTypeBudget, SolutionBudget};
use crate::types::constraints::support::Support;
use crate::types::constraints::variables::{
    AtomicConstraint, Constraint, ConstraintProvenance, UnsatisfiableBound,
};
use crate::types::constraints::{
    ALWAYS_FALSE, ALWAYS_TRUE, Assignment, AtomicConstraintId, CandidateResidual,
    CandidateSolution, CandidateSolutions, CandidateTypeVarSolution, CandidateTypeVarSolver,
    ConstraintFailureEvidence, ConstraintId, ConstraintSet, ConstraintSetBuilder,
    ConstraintSetStorage, InteriorNodeData, Node, NodeId, OwnedConstraintSet,
    OwnedConstraintSetBuilder, SolutionLimits, SolutionValidity, SolutionViolation,
    SolutionViolationKind, SourceOrderId, TypeVarSolution, UnboundedSolutionLimits,
};
use crate::types::typevar::{TypeVarBoundOrConstraints, TypeVarConstraints, TypeVarSet};
use crate::types::{BoundTypeVarIdentity, BoundTypeVarInstance, Type, any_over_type};
use crate::{Db, FxIndexMap, FxIndexSet, ProgramEnvironment};

/// A callback used by [`visit_node_and_then`][SolutionWalker::visit_node_and_then] to determine
/// whether we've already processed a node in an equivalent situation. If so, we don't need to
/// reproduce whatever results we calculated previously, and can return early.
///
/// If you are performing a BDD walk where you always want to process every node, use the
/// [`never_cache`] callback.
///
/// The "in an equivalent situation" part is important. We will often encounter the same BDD node
/// multiple times when walking a BDD, and how we interpret that node will depend on which other
/// nodes we've already processed on this path, and what partial solution we've calculated so far
/// for those other nodes. When constructing a cache key, you should take into account both `path`
/// and `node`.
///
/// Returns `true` if this is the first time we've seen this node in this situation, and should
/// process it. Returns `false` if this is _not_ the first time we've seen them, and can reuse any
/// cached results.
type CheckCache<'a, 'db, L, B> = dyn Fn(
        &mut SolutionWalker<'db, L>,
        &mut ConstraintSetStorage<'db>,
        &mut PathAssignments,
        Polarity,
        NodeId,
    ) -> ControlFlow<B, bool>
    + 'a;

/// A [`CheckCache`] callback that never caches anything, and always processes every node
/// encountered when walking a BDD.
fn never_cache<'db, L, B>(
    _this: &mut SolutionWalker<'db, L>,
    _storage: &mut ConstraintSetStorage<'db>,
    _path: &mut PathAssignments,
    _polarity: Polarity,
    _node: NodeId,
) -> ControlFlow<B, bool> {
    ControlFlow::Continue(true)
}

/// A callback used by [`visit_node_and_then`][SolutionWalker::visit_node_and_then] to determine
/// whether the current node can affect the partial solution that we've calculated so far for the
/// current path. If not, we don't need to descend into the node's subtree, and can return early.
///
/// If you are performing a BDD walk where you always want to process every node, use the
/// [`never_prune`] callback.
///
/// The current node and its descendents have a fixed set of constraints and typevars that they
/// check. (We track this in the node's _support_, so that we don't have to calculate it on the
/// fly.) If those typevars are not inferable, and there are no cross-typevar relationships between
/// them and any other inferable typevars, then this node's subtree cannot possibly affect the
/// current solution. There is one exception: if there is no possible way to satisfy the current
/// node, that contradiction does "carry through" and invalidate the current solution.
///
/// Together, this gives three possible outcomes:
///
/// - We can skip this node's subtree, because the current solution is valid, and the subtree
///   cannot affect that solution. ([`PathIs::Satisfied`])
/// - We can skip this node's subtree, because the subtree is unsatisfiable, and the so the overall
///   solution is invalid. ([`PathIs::Unsatisfied`])
/// - The node's subtree can affect the current solution, and so we have to descend into the
///   subtree to determine which extensions of the current solution are valid.
///   ([`PathIs::Uncertain`])
type PrunePath<'a, 'db, L, B> = dyn Fn(
        &mut SolutionWalker<'db, L>,
        &mut ConstraintSetStorage<'db>,
        &mut PathAssignments,
        Polarity,
        NodeId,
    ) -> ControlFlow<B, PathIs>
    + 'a;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum PathIs {
    /// The current path is already satisfied, and the current node (and its descendants) cannot
    /// affect the solution.
    Satisfied,
    /// The current path is currently satisfied, but all paths from the current node introduce
    /// contradictions that make it unsatisfied.
    Unsatisfied,
    /// This subtree contains no certified path, but some branches remain unresolved.
    Incomplete,
    /// The current path is currently satisfied, but the current node can influence the solutions
    /// that we report, and so we must walk its outgoing edges in full.
    Uncertain,
}

/// A [`PrunePath`] callback that never prunes anything, and always processes the descendants of
/// every node encountered when walking a BDD.
fn never_prune<'db, L, B>(
    _this: &mut SolutionWalker<'db, L>,
    _storage: &mut ConstraintSetStorage<'db>,
    _paths: &mut PathAssignments,
    _polarity: Polarity,
    _node: NodeId,
) -> ControlFlow<B, PathIs> {
    ControlFlow::Continue(PathIs::Uncertain)
}

/// A callback that is invoked by [`visit_node_and_then`][SolutionWalker::visit_node_and_then]
/// whenever a satisfied path to the `true` terminal is found.
type ProcessSatisfied<'a, 'db, L, B> = dyn Fn(
        &mut SolutionWalker<'db, L>,
        &mut ConstraintSetStorage<'db>,
        &mut PathAssignments,
    ) -> ControlFlow<B>
    + 'a;

/// Whether [`SolutionWalker`] walks a BDD or its negation. (We can walk the negation of a BDD
/// lazily, which is more efficient than actually constructing the negation and then walking it
/// normally.)
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) enum Polarity {
    Positive,
    Negative,
}

type ExploredNodeKey = (
    Polarity,
    NodeId,
    Box<[(Assignment<AtomicConstraintId>, AtomicConstraintId)]>,
);

/// Whether a path was proved satisfiable, refuted, or requires a proof we cannot complete.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Satisfiability {
    Satisfiable,
    Unsatisfiable,
    Incomplete,
}

enum Break<B> {
    Limits(B),
    EarlyBreak,
}

impl<B> Break<B> {
    #[track_caller]
    fn expect_limits(self) -> B {
        match self {
            Break::Limits(b) => b,
            Break::EarlyBreak => panic!("EarlyBreak should not leak"),
        }
    }
}

pub(super) struct SolutionWalker<'db, L> {
    source_orders: FxIndexSet<AtomicConstraintId>,
    /// The relation before non-inferable variables are projected away. Used to recover the
    /// original upper bounds for diagnostics, since projected paths can contain derived bounds
    /// that obscure the original evidence.
    original_node: NodeId,
    inferable: TypeVarSet<'db>,
    inferable_support: Support,
    limits: L,

    positive_locals: Support,
    /// Typevars whose declarations are checked by the root validation pass. Derived
    /// relations can introduce additional scoped locals after this pass is prepared.
    validation_support: Option<Support>,
    negative_scopes: Vec<ConstraintId>,

    declared_constraint_solutions: FxHashMap<BoundTypeVarIdentity<'db>, Type<'db>>,

    /// Nodes that we have already explored. We can't cache this only on the node ID, since the
    /// constraints that are in scope when we encounter the node can affect how we interpret its
    /// downstream edges. But we also don't want to consider _all_ of the constraints on the path;
    /// we only want to consider the ones that are relevant to the node and its descendants.
    explored_nodes: FxHashSet<ExploredNodeKey>,

    /// Candidate solutions for each satisfiable path in the BDD.
    ///
    /// We will check these solutions against the declared upper bounds (TODO and constraints) of
    /// all relevant typevars (both inferable and non-inferable). Note that we will still create a
    /// candidate solution for satisfiable paths that do _not_ satisfy the upper bounds and
    /// constraints. Those paths will have a [`validity`][CandidateSolution::validity] of
    /// [`Invalid`][SolutionValidity::Invalid].
    pending: Vec<PendingCandidateSolution<'db>>,
    /// Some branches could not be certified or refuted. Their absence from `pending` must
    /// not be mistaken for a complete enumeration of the solutions.
    incomplete: bool,
    /// Boolean proof needs logical domain alternatives. Candidate collection instead leaves
    /// finite-domain preference and gradual families to post-body validation.
    proving_satisfiability: bool,
    /// Cumulative temporary witness types in this walk, including nested queries and
    /// backtracking. Projections separately account for types retained in their result.
    witness_budget: ProjectionTypeBudget,

    _phantom: PhantomData<&'db ()>,
}

struct PendingCandidateSolution<'db> {
    /// The candidate solution for a satisfiable path in the BDD
    candidate: CandidateSolution<'db>,

    /// The `source_orders` of the constraints in the path that this candidate solution was created
    /// from. We retain this so that our final result is sorted in a stable order.
    source_orders: Vec<usize>,
}

impl<'db, L: SolutionLimits> SolutionWalker<'db, L> {
    pub(super) fn new(
        db: &'db dyn Db,
        storage: &mut ConstraintSetStorage<'db>,
        source_orders: FxIndexSet<AtomicConstraintId>,
        inferable: TypeVarSet<'db>,
        limits: L,
        original_node: NodeId,
    ) -> Self {
        let inferable_support = Support::from_typevar_set(db, storage, inferable);
        Self {
            source_orders,
            original_node,
            inferable,
            inferable_support,
            limits,
            positive_locals: Support::default(),
            validation_support: None,
            negative_scopes: Vec::new(),
            declared_constraint_solutions: FxHashMap::default(),
            explored_nodes: FxHashSet::default(),
            pending: Vec::default(),
            incomplete: false,
            proving_satisfiability: false,
            witness_budget: ProjectionTypeBudget::new(SolutionBudget::default().type_terms),
            _phantom: PhantomData,
        }
    }

    /// Returns an iterator of the positive and negative constraints on the current path
    fn constrained_assignments(
        path: &PathAssignments,
    ) -> impl Iterator<Item = AtomicConstraintId> + Clone {
        path.assignments
            .iter()
            .filter_map(|(assignment, _)| assignment.as_constrained())
    }

    /// Returns an iterator of the constraints on the current path that mention any typevar in the
    /// given support
    fn constrained_assignments_mentioning(
        storage: &ConstraintSetStorage<'db>,
        path: &PathAssignments,
        support: &Support,
    ) -> impl Iterator<Item = (Assignment<AtomicConstraintId>, AtomicConstraintId)> {
        path.assignments
            .iter()
            .filter_map(|(assignment, (source_constraint, _))| {
                let constraint = assignment.as_constrained()?;
                let constraint_support = storage.constraint_support(constraint.into_inner());
                constraint_support
                    .overlaps_with(support)
                    .then_some((*assignment, *source_constraint))
            })
    }
}

impl<'db> SolutionWalker<'db, UnboundedSolutionLimits> {
    pub(super) fn is_never_satisfied(
        &mut self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        storage: &mut ConstraintSetStorage<'db>,
        path: &mut PathAssignments,
        polarity: Polarity,
        node: NodeId,
    ) -> bool {
        let ControlFlow::Continue(satisfiable) =
            self.node_is_satisfiable_on_path(db, env, storage, path, polarity, node, None);
        satisfiable == Satisfiability::Unsatisfiable
    }
}

impl<'db, L: SolutionLimits> SolutionWalker<'db, L> {
    /// Visit a BDD node and all of its descendants. We will add pending candidate solutions for
    /// any satisfiable path we discover from the node.
    #[expect(clippy::too_many_arguments)]
    pub(super) fn visit_node(
        &mut self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        storage: &mut ConstraintSetStorage<'db>,
        path: &mut PathAssignments,
        all_typevars: Option<&Support>,
        polarity: Polarity,
        node: NodeId,
    ) -> ControlFlow<L::Break> {
        self.validation_support = all_typevars.cloned();
        let validations = all_typevars
            .map(|all_typevars| Validations::from_support(db, env, storage, all_typevars));
        let validations = validations.as_ref();
        self.visit_node_and_then(
            db,
            env,
            storage,
            path,
            polarity,
            node,
            &|this, storage, path, polarity, node| {
                // See if we've already visited this node on an "equivalent" path, where we only
                // consider the typevars that can affect the solutions we'd find if we were to
                // continue walking down the node.
                let mut relevant_typevars = this.inferable_support.clone();
                let node_support = storage.node_support(node);
                if let Some(node_support) = node_support {
                    relevant_typevars |= node_support;
                }
                relevant_typevars.close_over_constraints(
                    storage,
                    Self::constrained_assignments(path)
                        .chain(validations.into_iter().flat_map(Validations::constraints))
                        .map(AtomicConstraintId::into_inner),
                );
                let mut relevant_path: Box<[_]> =
                    Self::constrained_assignments_mentioning(storage, path, &relevant_typevars)
                        .collect();
                relevant_path.sort_unstable_by_key(|(assignment, _)| {
                    assignment.constraint().into_inner().ordering()
                });
                // Quantified bodies and validation subwalks use `never_cache`.
                debug_assert!(this.positive_locals.iter().next().is_none());
                debug_assert!(this.negative_scopes.is_empty());
                let key = (polarity, node, relevant_path);
                ControlFlow::Continue(this.explored_nodes.insert(key))
            },
            &|this, storage, path, polarity, node| {
                // Next see if anything in this node can affect the solution we've already
                // calculated on the current path.
                let mut visible_typevars = this.inferable_support.clone();
                visible_typevars.close_over_constraints(
                    storage,
                    Self::constrained_assignments(path)
                        .chain(validations.into_iter().flat_map(Validations::constraints))
                        .map(AtomicConstraintId::into_inner),
                );
                if let Some(node_support) = storage.node_support(node)
                    && visible_typevars.overlaps_with(node_support)
                {
                    return ControlFlow::Continue(PathIs::Uncertain);
                }

                // This node cannot affect the solution we've found. Make sure that the node has
                // _at least one_ satisfiable path, without walking them all. As long as it does,
                // we can report the solution we have so far as-is.
                match this
                    .node_is_satisfiable_on_path(
                        db,
                        env,
                        storage,
                        path,
                        polarity,
                        node,
                        validations,
                    )
                    .map_break(Break::Limits)?
                {
                    Satisfiability::Satisfiable => ControlFlow::Continue(PathIs::Satisfied),
                    Satisfiability::Unsatisfiable => ControlFlow::Continue(PathIs::Unsatisfied),
                    Satisfiability::Incomplete => ControlFlow::Continue(PathIs::Incomplete),
                }
            },
            &|this, storage, path| {
                let satisfied = Cell::new(false);
                this.validate_satisfied_path(
                    db,
                    env,
                    storage,
                    path,
                    validations,
                    &|this, storage, path| {
                        if this.found_satisfied_path(db, env, storage, path)? {
                            satisfied.set(true);
                        }
                        ControlFlow::Continue(())
                    },
                )?;

                // If this path is not satisfied, we want to identify which particular upper
                // bounds or constraints were violated. To do that, we have to re-check this
                // path against each one individually.
                if let Some(validations) = validations
                    && !satisfied.into_inner()
                {
                    let upper_bounds = validations.upper_bounds.as_slice();
                    let constrained = validations.constrained.as_slice();
                    this.attribute_typevar_failures(
                        db,
                        env,
                        storage,
                        path,
                        upper_bounds,
                        constrained,
                    )?;
                }

                ControlFlow::Continue(())
            },
        )
        .map_break(Break::expect_limits)
    }

    /// Visit a BDD node and all of its descendants, invoking the `process_satisfied` callback for
    /// any satisfiable path that is discovered.
    #[expect(clippy::too_many_arguments)]
    fn visit_node_and_then(
        &mut self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        storage: &mut ConstraintSetStorage<'db>,
        path: &mut PathAssignments,
        polarity: Polarity,
        node: NodeId,
        check_cache: &CheckCache<'_, 'db, L, Break<L::Break>>,
        prune_path: &PrunePath<'_, 'db, L, Break<L::Break>>,
        process_satisfied: &ProcessSatisfied<'_, 'db, L, Break<L::Break>>,
    ) -> ControlFlow<Break<L::Break>> {
        self.limits.visit_node().map_break(Break::Limits)?;
        if let (Polarity::Positive, ALWAYS_FALSE) | (Polarity::Negative, ALWAYS_TRUE) =
            (polarity, node)
        {
            return ControlFlow::Continue(());
        }

        // Atomic antecedents can imply a whole quantified relation. Visit it before
        // pruning, memoization, or terminal success, retaining its witnesses through the
        // original continuation. The consequence holds positively under either polarity.
        if let Some((index, relation, source_order)) = path.pending_relation() {
            self.source_orders
                .extend(storage.calculate_source_orders(source_order));
            return path.with_relation(index, |path, previous_fuel| {
                self.visit_node_and_then(
                    db,
                    env,
                    storage,
                    path,
                    Polarity::Positive,
                    relation,
                    &never_cache,
                    &never_prune,
                    &|this, storage, path| {
                        path.with_origin_fuel(previous_fuel, |path| {
                            this.visit_node_and_then(
                                db,
                                env,
                                storage,
                                path,
                                polarity,
                                node,
                                &never_cache,
                                &never_prune,
                                process_satisfied,
                            )
                        })
                    },
                )
            });
        }

        if !check_cache(self, storage, path, polarity, node)? {
            return ControlFlow::Continue(());
        }

        // If the current node is ALWAYS_TRUE, we can immediately report the current solution.
        if let (Polarity::Positive, ALWAYS_TRUE) | (Polarity::Negative, ALWAYS_FALSE) =
            (polarity, node)
        {
            return process_satisfied(self, storage, path);
        }

        match prune_path(self, storage, path, polarity, node)? {
            PathIs::Satisfied => return process_satisfied(self, storage, path),
            PathIs::Unsatisfied => return ControlFlow::Continue(()),
            PathIs::Incomplete => {
                self.incomplete = true;
                return ControlFlow::Continue(());
            }
            PathIs::Uncertain => {}
        }

        // At this point we actually have to walk the outgoing edges of this node.
        let interior = storage.interior_node_data(node);
        let constraint_id = interior.constraint;
        let constraint = storage.constraint_data(constraint_id);
        match constraint {
            Constraint::Atomic(_) => self.visit_atomic_constraint(
                db,
                env,
                storage,
                path,
                polarity,
                interior,
                AtomicConstraintId(constraint_id),
                check_cache,
                prune_path,
                process_satisfied,
            ),
            Constraint::Existential(existential) => {
                let locals = existential.locals.clone();
                let body = existential.body;
                path.with_quantified_typevars(&locals, |path| {
                    self.visit_existential_constraint(
                        db,
                        env,
                        storage,
                        path,
                        polarity,
                        interior,
                        body,
                        check_cache,
                        prune_path,
                        process_satisfied,
                    )
                })
            }
        }
    }

    #[expect(clippy::too_many_arguments)]
    fn visit_atomic_constraint(
        &mut self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        storage: &mut ConstraintSetStorage<'db>,
        path: &mut PathAssignments,
        polarity: Polarity,
        interior: InteriorNodeData,
        constraint: AtomicConstraintId,
        check_cache: &CheckCache<'_, 'db, L, Break<L::Break>>,
        prune_path: &PrunePath<'_, 'db, L, Break<L::Break>>,
        process_satisfied: &ProcessSatisfied<'_, 'db, L, Break<L::Break>>,
    ) -> ControlFlow<Break<L::Break>> {
        let edges: ArrayVec<(Assignment<AtomicConstraintId>, NodeId), 3> =
            if polarity == Polarity::Positive {
                ArrayVec::from_iter([
                    (constraint.when_true(), interior.if_true),
                    (constraint.when_unconstrained(), interior.if_uncertain),
                    (constraint.when_false(), interior.if_false),
                ])
            } else {
                ArrayVec::from_iter([
                    (
                        constraint.when_true(),
                        interior.if_true.or(storage, interior.if_uncertain),
                    ),
                    (
                        constraint.when_false(),
                        interior.if_false.or(storage, interior.if_uncertain),
                    ),
                ])
            };
        for (assignment, child) in edges {
            self.visit_atomic_edge(
                db,
                env,
                storage,
                path,
                polarity,
                assignment,
                child,
                check_cache,
                prune_path,
                process_satisfied,
            )?;
        }
        ControlFlow::Continue(())
    }

    /// Returns whether there is _any_ satisfiable path in `node`, assuming that the assignments in
    /// `path` already hold. Avoids walking the entire subtree if possible, by returning early once
    /// we find the first satisfied path.
    #[expect(clippy::too_many_arguments)]
    pub(super) fn node_is_satisfiable_on_path(
        &mut self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        storage: &mut ConstraintSetStorage<'db>,
        path: &mut PathAssignments,
        polarity: Polarity,
        node: NodeId,
        validations: Option<&Validations<'db>>,
    ) -> ControlFlow<L::Break, Satisfiability> {
        // A certified witness settles this query even if another branch was incomplete.
        // Keep that local answer separate from completeness of the outer candidate family.
        let previous_proving = std::mem::replace(&mut self.proving_satisfiability, true);
        let previous_incomplete = std::mem::take(&mut self.incomplete);
        let result = self.visit_node_and_then(
            db,
            env,
            storage,
            path,
            polarity,
            node,
            &never_cache,
            &never_prune,
            &|this, storage, path| {
                this.validate_satisfied_path(
                    db,
                    env,
                    storage,
                    path,
                    validations,
                    &|this, storage, path| {
                        if this
                            .pending_candidate_solution(
                                db,
                                env,
                                storage,
                                path,
                                this.inferable,
                                &path.quantified_typevars,
                                None,
                            )
                            .is_some()
                        {
                            // break when we find the first solution
                            ControlFlow::Break(Break::EarlyBreak)
                        } else {
                            ControlFlow::Continue(())
                        }
                    },
                )
            },
        );
        self.proving_satisfiability = previous_proving;
        self.finish_satisfiability_query(previous_incomplete, result)
    }

    fn finish_satisfiability_query(
        &mut self,
        previous_incomplete: bool,
        result: ControlFlow<Break<L::Break>>,
    ) -> ControlFlow<L::Break, Satisfiability> {
        let incomplete = std::mem::replace(&mut self.incomplete, previous_incomplete);
        match result {
            ControlFlow::Break(Break::Limits(b)) => ControlFlow::Break(b),
            ControlFlow::Break(Break::EarlyBreak) => {
                ControlFlow::Continue(Satisfiability::Satisfiable)
            }
            ControlFlow::Continue(()) => ControlFlow::Continue(if incomplete {
                Satisfiability::Incomplete
            } else {
                Satisfiability::Unsatisfiable
            }),
        }
    }

    /// Visits one of the outgoing edges from a BDD node.
    ///
    /// (This is a helper method used by [`visit_node_and_then`][Self::visit_node_and_then]. You
    /// will probably not need to call this directly.)
    #[expect(clippy::too_many_arguments)]
    fn visit_atomic_edge(
        &mut self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        storage: &mut ConstraintSetStorage<'db>,
        path: &mut PathAssignments,
        polarity: Polarity,
        assignment: Assignment<AtomicConstraintId>,
        child: NodeId,
        check_cache: &CheckCache<'_, 'db, L, Break<L::Break>>,
        prune_path: &PrunePath<'_, 'db, L, Break<L::Break>>,
        process_satisfied: &ProcessSatisfied<'_, 'db, L, Break<L::Break>>,
    ) -> ControlFlow<Break<L::Break>> {
        // Don't bother adding the assignment and checking the sequent map if the edge takes us to
        // the ALWAYS_FALSE terminal.
        if let (Polarity::Positive, ALWAYS_FALSE) | (Polarity::Negative, ALWAYS_TRUE) =
            (polarity, child)
        {
            return ControlFlow::Continue(());
        }

        path.walk_edge(
            db,
            env,
            storage,
            assignment,
            |storage, path, _new_range, found_conflict| {
                if !found_conflict {
                    self.visit_node_and_then(
                        db,
                        env,
                        storage,
                        path,
                        polarity,
                        child,
                        check_cache,
                        prune_path,
                        process_satisfied,
                    )?;
                }
                ControlFlow::Continue(())
            },
        )
    }

    #[expect(clippy::too_many_arguments)]
    fn visit_existential_constraint(
        &mut self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        storage: &mut ConstraintSetStorage<'db>,
        path: &mut PathAssignments,
        polarity: Polarity,
        interior: InteriorNodeData,
        existential_body: NodeId,
        check_cache: &CheckCache<'_, 'db, L, Break<L::Break>>,
        prune_path: &PrunePath<'_, 'db, L, Break<L::Break>>,
        process_satisfied: &ProcessSatisfied<'_, 'db, L, Break<L::Break>>,
    ) -> ControlFlow<Break<L::Break>> {
        let (if_holds, if_not_holds) = match polarity {
            Polarity::Positive => (interior.if_true, interior.if_false),
            Polarity::Negative => (
                interior.if_true.or(storage, interior.if_uncertain),
                interior.if_false.or(storage, interior.if_uncertain),
            ),
        };

        // Walk the outgoing edge that depends on the existential holding. If we find any candidate
        // solutions, walk the existential's body to make sure there are valid existential
        // solutions that are compatible with that candidate solution.
        self.visit_node_and_then(
            db,
            env,
            storage,
            path,
            polarity,
            if_holds,
            check_cache,
            prune_path,
            &|this, storage, path| {
                // Note that we never negate existential's body, even when we are walking the
                // negation of the existential _node_.
                let Constraint::Existential(existential) =
                    storage.constraint_data(interior.constraint)
                else {
                    unreachable!("existential visitor requires an existential constraint");
                };
                let locals = existential.locals.clone();
                let new_locals = this
                    .validation_support
                    .as_ref()
                    .map_or_else(|| locals.clone(), |validated| &locals - validated);
                let validations = Validations::from_locals(db, env, storage, &new_locals);
                let previous = this.positive_locals.clone();
                this.positive_locals |= &locals;
                let visit_body = |this: &mut Self,
                                  storage: &mut ConstraintSetStorage<'db>,
                                  path: &mut PathAssignments| {
                    this.visit_node_and_then(
                        db,
                        env,
                        storage,
                        path,
                        Polarity::Positive,
                        existential_body,
                        &never_cache,
                        prune_path,
                        &|this, storage, path| {
                            this.validate_satisfied_path(
                                db,
                                env,
                                storage,
                                path,
                                Some(&validations),
                                process_satisfied,
                            )
                        },
                    )
                };
                let result = if this.proving_satisfiability {
                    let domains = Validations::from_locals(db, env, storage, &locals);
                    this.visit_domains_and_then(
                        db,
                        env,
                        storage,
                        path,
                        domains.upper_bounds.as_slice(),
                        domains.constrained.as_slice(),
                        &visit_body,
                    )
                } else {
                    visit_body(this, storage, path)
                };
                this.positive_locals = previous;
                result
            },
        )?;

        // Under positive polarity, the existential's `if_uncertain` edge holds regardless of
        // whether the quantifier itself holds, so we don't need to check the body.
        if polarity == Polarity::Positive {
            self.visit_node_and_then(
                db,
                env,
                storage,
                path,
                polarity,
                interior.if_uncertain,
                check_cache,
                prune_path,
                process_satisfied,
            )?;
        }

        // Last, walk the outgoing edge that depends on the existential _not_ holding. For each
        // candidate solution, we check whether the existential's body has any solutions _given
        // that candidate solution_.
        self.visit_node_and_then(
            db,
            env,
            storage,
            path,
            polarity,
            if_not_holds,
            check_cache,
            prune_path,
            &|this, storage, path| {
                let previous_proving = std::mem::replace(&mut this.proving_satisfiability, true);
                let result = this.existential_holds_on_path(
                    db,
                    env,
                    storage,
                    path,
                    interior.constraint,
                    existential_body,
                );
                this.proving_satisfiability = previous_proving;
                match result.map_break(Break::Limits)? {
                    Satisfiability::Satisfiable => return ControlFlow::Continue(()),
                    Satisfiability::Incomplete => {
                        this.incomplete = true;
                        return ControlFlow::Continue(());
                    }
                    Satisfiability::Unsatisfiable => {}
                }
                this.negative_scopes.push(interior.constraint);
                let result = process_satisfied(this, storage, path);
                this.negative_scopes.pop();
                result
            },
        )
    }

    /// Proves that a quantified body holds throughout the current outer path, or that it
    /// cannot hold anywhere on that path. A conditional witness proves neither statement.
    fn existential_holds_on_path(
        &mut self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        storage: &mut ConstraintSetStorage<'db>,
        path: &mut PathAssignments,
        constraint: ConstraintId,
        body: NodeId,
    ) -> ControlFlow<L::Break, Satisfiability> {
        let Constraint::Existential(existential) = storage.constraint_data(constraint) else {
            unreachable!("existential proof requires a quantified constraint");
        };
        let locals = existential.locals.clone();
        let validations = Validations::from_locals(db, env, storage, &locals);
        let mut support = storage.constraint_support(constraint).clone();
        for constraint in validations.constraints() {
            support |= storage.constraint_support(constraint.into_inner());
        }
        let free = &support - &locals;
        if free.is_complete() && free.iter().next().is_none() {
            let previous_incomplete = std::mem::take(&mut self.incomplete);
            let result = self.visit_domains_and_then(
                db,
                env,
                storage,
                path,
                validations.upper_bounds.as_slice(),
                validations.constrained.as_slice(),
                &|this, storage, path| match this
                    .node_is_satisfiable_on_path(
                        db,
                        env,
                        storage,
                        path,
                        Polarity::Positive,
                        body,
                        Some(&validations),
                    )
                    .map_break(Break::Limits)?
                {
                    Satisfiability::Satisfiable => ControlFlow::Break(Break::EarlyBreak),
                    Satisfiability::Unsatisfiable => ControlFlow::Continue(()),
                    Satisfiability::Incomplete => {
                        this.incomplete = true;
                        ControlFlow::Continue(())
                    }
                },
            );
            return self.finish_satisfiability_query(previous_incomplete, result);
        }

        let previous_locals = self.positive_locals.clone();
        self.positive_locals |= &locals;
        let negative_scopes_from = self.negative_scopes.len();
        let previous_incomplete = std::mem::take(&mut self.incomplete);
        let witnesses = RefCell::new(Vec::new());
        let result = self.visit_domains_and_then(
            db,
            env,
            storage,
            path,
            validations.upper_bounds.as_slice(),
            validations.constrained.as_slice(),
            &|this, storage, path| {
                this.visit_node_and_then(
                    db,
                    env,
                    storage,
                    path,
                    Polarity::Positive,
                    body,
                    &never_cache,
                    &never_prune,
                    &|this, storage, path| {
                        this.validate_satisfied_path(
                            db,
                            env,
                            storage,
                            path,
                            Some(&validations),
                            &|this, storage, path| {
                                let locals = &this.positive_locals - &previous_locals;
                                let locals = TypeVarSet::from_typevars(
                                    db,
                                    locals.iter().map(|id| storage.typevar_data(id)),
                                );
                                let Some(pending) = this.pending_candidate_solution(
                                    db,
                                    env,
                                    storage,
                                    path,
                                    locals,
                                    &Support::default(),
                                    None,
                                ) else {
                                    return ControlFlow::Continue(());
                                };
                                this.limits.satisfied_path().map_break(Break::Limits)?;
                                let relation =
                                    this.signed_path(storage, path, negative_scopes_from);
                                witnesses
                                    .borrow_mut()
                                    .push((pending.candidate, locals, relation));
                                ControlFlow::Continue(())
                            },
                        )
                    },
                )
            },
        );
        self.positive_locals = previous_locals;
        let incomplete = std::mem::replace(&mut self.incomplete, previous_incomplete);
        result.map_break(Break::expect_limits)?;
        let witnesses = witnesses.into_inner();
        if witnesses.is_empty() {
            return ControlFlow::Continue(if incomplete {
                Satisfiability::Incomplete
            } else {
                Satisfiability::Unsatisfiable
            });
        }

        // These are sufficient conditions for whole witnesses, not independent local bounds.
        // Their union may cover the outer path even when no single witness covers it alone.
        let mut covered = ALWAYS_FALSE;
        let has_type_endpoint = |variable: BoundTypeVarInstance<'db>| {
            !variable.is_paramspec(db) && !variable.is_typevartuple(db)
        };
        for (candidate, locals, (node, source_order)) in witnesses {
            // Reuse normal bound selection and specialization in the same arenas. A witness
            // can mention rigid outer variables, but only scoped locals may be substituted.
            let builder = ConstraintSetBuilder {
                storage: RefCell::new(std::mem::take(storage)),
            };
            let replay = (|| {
                let selected: Option<Vec<_>> = candidate
                    .typevars
                    .iter()
                    .filter(|bound| bound.bound_typevar.is_inferable(db, locals))
                    .map(|bound| {
                        match CandidateSolutions::default_solve(db, env, &builder, bound) {
                            PathBoundSolution::Solved(solution) => Some(TypeVarSolution {
                                bound_typevar: bound.bound_typevar,
                                solution,
                            }),
                            PathBoundSolution::Unsolved => {
                                // Inference needs evidence; a proof may try the logical endpoint.
                                // Signature and tuple packs need a witness in their own domain.
                                has_type_endpoint(bound.bound_typevar).then(|| TypeVarSolution {
                                    bound_typevar: bound.bound_typevar,
                                    solution: bound.effective_lower(db, env),
                                })
                            }
                            PathBoundSolution::Unsatisfiable => None,
                            PathBoundSolution::BudgetExceeded { fallback: _ } => None,
                        }
                    })
                    .collect();
                let mut selected = selected?;
                for local in locals.iter(db) {
                    if has_type_endpoint(local)
                        && !selected
                            .iter()
                            .any(|binding| binding.bound_typevar.is_same_typevar_as(db, local))
                    {
                        selected.push(TypeVarSolution {
                            bound_typevar: local,
                            solution: Type::Never,
                        });
                    }
                }
                let relation = ConstraintSet::from_node(&builder, node, source_order);
                let (replay, _) = CandidateResidual::specialize_witness(
                    db,
                    env,
                    relation,
                    locals,
                    locals,
                    &selected,
                    &mut self.witness_budget,
                )
                .ok()??;
                Some((replay.node, replay.source_order))
            })();
            *storage = builder.storage.into_inner();
            let Some((replay, source_order)) = replay else {
                continue;
            };
            self.source_orders
                .extend(storage.calculate_source_orders(source_order));
            covered = covered.or(storage, replay);
            let outcome = self.node_is_satisfiable_on_path(
                db,
                env,
                storage,
                path,
                Polarity::Negative,
                covered,
                None,
            )?;
            if outcome == Satisfiability::Unsatisfiable {
                return ControlFlow::Continue(Satisfiability::Satisfiable);
            }
        }
        // Refuting these choices does not refute every possible witness.
        ControlFlow::Continue(Satisfiability::Incomplete)
    }

    fn with_declared_constraint_solution<R>(
        &mut self,
        db: &'db dyn Db,
        bound_typevar: BoundTypeVarInstance<'db>,
        declared_constraint_solution: Type<'db>,
        f: impl FnOnce(&mut Self) -> R,
    ) -> R {
        let identity = bound_typevar.identity(db);
        self.declared_constraint_solutions
            .insert(identity, declared_constraint_solution);
        let result = f(self);
        self.declared_constraint_solutions.remove(&identity);
        result
    }

    /// Quantifier domains are logical assumptions while walking the body. Candidate validation
    /// separately chooses promoted constraints or preserves inference families after the body.
    #[expect(clippy::too_many_arguments)]
    fn visit_domains_and_then(
        &mut self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        storage: &mut ConstraintSetStorage<'db>,
        path: &mut PathAssignments,
        upper_bounds: &Slice<BoundTypeVarInstance<'db>, UpperBound>,
        constrained: &Slice<BoundTypeVarInstance<'db>, Constrained<'db>>,
        process_satisfied: &ProcessSatisfied<'_, 'db, L, Break<L::Break>>,
    ) -> ControlFlow<Break<L::Break>> {
        if let Some(((_, bound), remaining)) = upper_bounds.split_first() {
            let Some(constraints) = bound.constraints.as_deref() else {
                return ControlFlow::Continue(());
            };
            return self.visit_constraints_and_then(
                db,
                env,
                storage,
                path,
                constraints,
                &|this, storage, path| {
                    this.visit_domains_and_then(
                        db,
                        env,
                        storage,
                        path,
                        remaining,
                        constrained,
                        process_satisfied,
                    )
                },
            );
        }
        let Some(((_, domain), remaining)) = constrained.split_first() else {
            return process_satisfied(self, storage, path);
        };
        for declared in &domain.declared_constraints {
            let Some(constraints) = declared.constraints.as_deref() else {
                continue;
            };
            self.visit_constraints_and_then(
                db,
                env,
                storage,
                path,
                constraints,
                &|this, storage, path| {
                    this.visit_domains_and_then(
                        db,
                        env,
                        storage,
                        path,
                        upper_bounds,
                        remaining,
                        process_satisfied,
                    )
                },
            )?;
        }
        ControlFlow::Continue(())
    }

    fn visit_constraints_and_then(
        &mut self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        storage: &mut ConstraintSetStorage<'db>,
        path: &mut PathAssignments,
        constraints: &[AtomicConstraintId],
        process_satisfied: &ProcessSatisfied<'_, 'db, L, Break<L::Break>>,
    ) -> ControlFlow<Break<L::Break>> {
        let Some((constraint, constraints)) = constraints.split_first() else {
            return self.visit_node_and_then(
                db,
                env,
                storage,
                path,
                Polarity::Positive,
                ALWAYS_TRUE,
                &never_cache,
                &never_prune,
                process_satisfied,
            );
        };
        self.source_orders.insert(*constraint);
        path.walk_edge(
            db,
            env,
            storage,
            constraint.when_true(),
            |storage, path, _new_range, found_conflict| {
                if !found_conflict {
                    self.visit_constraints_and_then(
                        db,
                        env,
                        storage,
                        path,
                        constraints,
                        process_satisfied,
                    )?;
                }
                ControlFlow::Continue(())
            },
        )
    }

    fn candidate_evidence(
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        storage: &mut ConstraintSetStorage<'db>,
        constraints: impl Iterator<Item = AtomicConstraintId>,
        bound_typevar: BoundTypeVarInstance<'db>,
    ) -> Option<CandidateTypeVarSolution<'db>> {
        let mut evidence = CandidateTypeVarSolver::default();
        for constraint in constraints {
            let constraint = storage.atomic_constraint_data(constraint);
            if constraint.provides_bound_for(db, bound_typevar)
                && constraint.provenance() == ConstraintProvenance::Evidence
            {
                evidence.add_constraint(db, bound_typevar, constraint);
            }
        }
        evidence.finish(db, env, storage, bound_typevar)
    }

    fn evidence_satisfies_declared_constraint(
        &self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        storage: &mut ConstraintSetStorage<'db>,
        evidence: &CandidateTypeVarSolution<'db>,
        constrained_ty: Type<'db>,
    ) -> bool {
        let constraint_lower = constrained_ty.bottom_materialization(db, env);
        let constraint_upper = constrained_ty.top_materialization(db, env);
        let (when_lower, when_lower_source_order) = match evidence.evidence_lower {
            Some(lower) => storage.load(
                db,
                env,
                &lower.when_assignable_to_owned(db, env, constraint_upper, self.inferable),
            ),
            None => (ALWAYS_TRUE, None),
        };
        let (when_upper, when_upper_source_order) = evidence.upper.iter_evidence().fold(
            (ALWAYS_TRUE, None),
            |(when, when_source_order), upper| {
                let (when_upper, when_upper_source_order) = storage.load(
                    db,
                    env,
                    &constraint_lower.when_assignable_to_owned(db, env, upper, self.inferable),
                );
                let when = when.and(storage, when_upper);
                let when_source_order =
                    storage.ordered_source_order(when_source_order, when_upper_source_order);
                (when, when_source_order)
            },
        );
        let when = when_lower.and(storage, when_upper);
        let when_source_order =
            storage.ordered_source_order(when_lower_source_order, when_upper_source_order);
        !when.is_never_satisfied(db, env, storage, when_source_order)
    }

    /// Finds evidence that excludes every declared constraint without relying on both sides of
    /// the inferred range together. A conflict between otherwise valid bounds is not itself a
    /// violation of the type variable's declaration.
    fn constraint_failure_evidence(
        &mut self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        storage: &mut ConstraintSetStorage<'db>,
        evidence: &CandidateTypeVarSolution<'db>,
        constrained: &Constrained<'db>,
    ) -> ControlFlow<Break<L::Break>, Option<ConstraintFailureEvidence<'db>>> {
        if let Some(lower) = evidence.inference_lower(db, env)
            && constrained.declared_constraints.iter().all(|declared| {
                let when = lower.when_assignable_to_owned(
                    db,
                    env,
                    declared.constrained_ty.top_materialization(db, env),
                    self.inferable,
                );
                let (when, source_order) = storage.load(db, env, &when);
                when.is_never_satisfied(db, env, storage, source_order)
            })
        {
            return ControlFlow::Continue(Some(ConstraintFailureEvidence::Lower(lower)));
        }

        // The projected path may contain derived constraints such as `T <= Never`, and source
        // order also contains constraints from other alternatives. Only collect individual bounds
        // from the original relation when it is a single conjunction: then each positive edge
        // necessarily applies to the whole relation. As in `NodeId::is_single_conjunction`, both
        // a second live branch and an uncertain branch rule out that interpretation. Charge this
        // scan to the traversal budget because diagnostic collection can occur on many paths.
        let bound_typevar = evidence.bound_typevar;
        let mut upper_bounds = Vec::new();
        let mut current = self.original_node;
        loop {
            self.limits.visit_node().map_break(Break::Limits)?;
            let interior = match current.node() {
                Node::AlwaysTrue => break,
                Node::AlwaysFalse => {
                    upper_bounds.clear();
                    break;
                }
                Node::Interior(_) => storage.interior_node_data(current),
            };
            if interior.if_uncertain != ALWAYS_FALSE
                || (interior.if_true != ALWAYS_FALSE && interior.if_false != ALWAYS_FALSE)
            {
                upper_bounds.clear();
                break;
            }
            if interior.if_true == ALWAYS_FALSE {
                current = interior.if_false;
                continue;
            }
            current = interior.if_true;
            let Some(constraint_id) = interior.constraint.as_atomic(storage) else {
                continue;
            };
            let constraint = storage.atomic_constraint_data(constraint_id);
            if constraint.provenance() != ConstraintProvenance::Evidence {
                continue;
            }
            if let Some(upper) = constraint.upper_bound_for(db, bound_typevar) {
                let order = self
                    .source_orders
                    .get_index_of(&constraint_id)
                    .unwrap_or(usize::MAX);
                upper_bounds.push((order, upper));
            }
        }
        upper_bounds.sort_by_key(|(order, _)| *order);
        let mut unique = FxIndexSet::default();
        unique.extend(upper_bounds.into_iter().map(|(_, upper)| upper));
        let has_never = unique.shift_remove(&Type::Never);
        let upper_bounds: Box<[_]> = unique.into_iter().collect();

        let excludes_every_constraint =
            |storage: &mut ConstraintSetStorage<'db>, bounds: &[Type<'db>]| {
                !bounds.is_empty()
                    && constrained.declared_constraints.iter().all(|declared| {
                        let mut when = ALWAYS_TRUE;
                        let mut source_order = None;
                        for upper in bounds {
                            let relation = declared
                                .constrained_ty
                                .bottom_materialization(db, env)
                                .when_assignable_to_owned(db, env, *upper, self.inferable);
                            let (next, next_order) = storage.load(db, env, &relation);
                            when = when.and(storage, next);
                            source_order = storage.ordered_source_order(source_order, next_order);
                        }
                        when.is_never_satisfied(db, env, storage, source_order)
                    })
            };
        if excludes_every_constraint(storage, &upper_bounds) {
            return ControlFlow::Continue(Some(ConstraintFailureEvidence::Upper(upper_bounds)));
        }
        if has_never && excludes_every_constraint(storage, &[Type::Never]) {
            return ControlFlow::Continue(Some(ConstraintFailureEvidence::Upper(Box::new([
                Type::Never,
            ]))));
        }
        // The solver can still establish an upper-bound failure after projection, even when the
        // original relation has alternatives or no longer contains the individual clauses.
        let inferred_upper: Vec<_> = evidence.upper.iter_evidence().collect();
        ControlFlow::Continue(
            excludes_every_constraint(storage, &inferred_upper)
                .then_some(ConstraintFailureEvidence::UpperUnknown),
        )
    }

    /// Having found a satisfiable path in the BDD, validates that path against the declared upper
    /// bound (TODO and constraints) of all relevant typevars.
    fn validate_satisfied_path(
        &mut self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        storage: &mut ConstraintSetStorage<'db>,
        path: &mut PathAssignments,
        validations: Option<&Validations<'db>>,
        process_satisfied: &ProcessSatisfied<'_, 'db, L, Break<L::Break>>,
    ) -> ControlFlow<Break<L::Break>> {
        let Some(validations) = validations else {
            return process_satisfied(self, storage, path);
        };

        // We have a path that represents a valid solution to the constraint set. Check if the
        // solution satisfies all of the typevars' declared upper bounds (TODO and constraints).
        let upper_bounds = validations.upper_bounds.as_slice();
        let constrained = validations.constrained.as_slice();
        self.validate_upper_bound(
            db,
            env,
            storage,
            path,
            upper_bounds,
            constrained,
            process_satisfied,
        )
    }

    #[expect(clippy::too_many_arguments)]
    fn validate_upper_bound(
        &mut self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        storage: &mut ConstraintSetStorage<'db>,
        path: &mut PathAssignments,
        upper_bounds: &Slice<BoundTypeVarInstance<'db>, UpperBound>,
        constrained: &Slice<BoundTypeVarInstance<'db>, Constrained<'db>>,
        process_satisfied: &ProcessSatisfied<'_, 'db, L, Break<L::Break>>,
    ) -> ControlFlow<Break<L::Break>> {
        let Some(((_, upper_bound), upper_bounds)) = upper_bounds.split_first() else {
            // We've checked all typevars that have an upper bound. Next check the typevars with
            // declared constraints.
            return self.validate_constrained(
                db,
                env,
                storage,
                path,
                constrained,
                process_satisfied,
            );
        };

        let Some(constraints) = upper_bound.constraints.as_deref() else {
            // This upper bound is entirely unsatisfiable.
            return ControlFlow::Continue(());
        };

        // Verify that we can add all of the upper bound's constraints to the current path without
        // making it unsatisfiable. If we can, make a recursive call to check the next typevar with
        // an upper bound.
        self.visit_constraints_and_then(
            db,
            env,
            storage,
            path,
            constraints,
            &|this, storage, path| {
                this.validate_upper_bound(
                    db,
                    env,
                    storage,
                    path,
                    upper_bounds,
                    constrained,
                    process_satisfied,
                )
            },
        )
    }

    fn validate_constrained(
        &mut self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        storage: &mut ConstraintSetStorage<'db>,
        path: &mut PathAssignments,
        constrained: &Slice<BoundTypeVarInstance<'db>, Constrained<'db>>,
        process_satisfied: &ProcessSatisfied<'_, 'db, L, Break<L::Break>>,
    ) -> ControlFlow<Break<L::Break>> {
        let Some(((&bound_typevar, constrained_typevar), constrained)) = constrained.split_first()
        else {
            // We've checked all constrained typevars, and we now know that the candidate solution
            // is valid.
            return process_satisfied(self, storage, path);
        };

        // Constrained typevars are more complex than bounded typevars, since they introduce a
        // disjunction; and because they are _equivalence_ bounds, not _upper_ bounds. As long as
        // the candidate solution satisfies _at least one_ of the declared constraints, the
        // solution is valid.
        //
        // Naively, that means we would just check each of the declared constraints separately,
        // adding the respective equivalence bound to the current path. Because the constraint
        // gives an equivalence bound, this will "tighten" the solution to be exactly the declared
        // constraint, as long as the solution satisfies that constraint. If more than one declared
        // constraint is valid, we first prune them with a "tightest constraint wins" heuristic. If
        // there are still multiple valid declared constraints, it would be the caller's
        // responsibility to decide whether to report that as an ambiguous solve, or to do
        // something useful with the different possible solutions.
        //
        // However, if the candidate solution maps this typevar to a dynamic type, or to another
        // typevar, and that solution satisfies more than one declared constraint, then we _don't_
        // want to report separate tightened solutions for each compatible constraint. Rather, we
        // want to report the dynamic type or typevar itself as the solution.

        // First see if we should return a "family" solution. If multiple declared constraints are
        // satisfied, _and_ the solution is either dynamic or another typevar, then we can consider
        // using the solution as-is, rather than trying to force it to be exactly equal to one of
        // those constraints. (We call this a "family" solution since it's a single solution that
        // satisfies a family of compatible declared constraints.)
        //
        // Note that a fixed caller typevar can only be preserved when its constraints are a subset
        // of this typevar's constraints. A bounded typevar may specialize below its bound, so it
        // must be promoted to an individual declared constraint instead.
        let Some(evidence) = Self::candidate_evidence(
            db,
            env,
            storage,
            path.positive_constraints()
                .map(|(constraint, _)| constraint),
            bound_typevar,
        ) else {
            // If the evidence is not satisfiable, then we can return early; none of the
            // constraints can possibly be satisfied.
            return ControlFlow::Continue(());
        };
        let has_no_evidence = evidence.evidence_lower.is_none() && !evidence.upper.has_evidence();
        let is_preservable_typevar = |ty| {
            let Type::TypeVar(typevar) = ty else {
                return false;
            };
            typevar.is_inferable(db, self.inferable)
                || typevar
                    .typevar(db)
                    .constraints(db, env)
                    .is_some_and(|actual_constraints| {
                        actual_constraints.iter().all(|actual| {
                            constrained_typevar
                                .declared_constraints
                                .iter()
                                .any(|declared| {
                                    actual.is_equivalent_to(db, env, declared.constrained_ty)
                                })
                        })
                    })
        };
        let contains_preservable_typevar =
            |ty| any_over_type(db, env, ty, false, is_preservable_typevar);
        let has_bare_preservable_typevar_evidence =
            evidence.evidence_lower.is_some_and(is_preservable_typevar)
                || evidence
                    .as_single_upper_bound(db, env)
                    .is_some_and(is_preservable_typevar);
        let has_non_concrete_evidence = has_no_evidence
            || evidence.has_only_non_concrete_evidence == Some(true)
            || has_bare_preservable_typevar_evidence;

        if has_non_concrete_evidence {
            let has_preservable_typevar_evidence = evidence
                .evidence_lower
                .is_some_and(contains_preservable_typevar)
                || evidence
                    .as_single_upper_bound(db, env)
                    .is_some_and(contains_preservable_typevar);

            let mut potentially_satisfied_constraint_count = 0;
            for declared_constraint in &constrained_typevar.declared_constraints {
                let Some(constraints) = declared_constraint.constraints.as_deref() else {
                    continue;
                };

                let satisfied = Cell::new(false);
                self.visit_constraints_and_then(
                    db,
                    env,
                    storage,
                    path,
                    constraints,
                    &|_this, _storage, _path| {
                        // We don't need to use pending_candidate_solution here to verify that the
                        // solution is actually valid, because we can accept false positives. We
                        // will catch the failure when we fall through to the full family solution
                        // check below.
                        satisfied.set(true);
                        ControlFlow::Continue(())
                    },
                )?;

                if satisfied.into_inner() {
                    potentially_satisfied_constraint_count += 1;
                }
            }

            if potentially_satisfied_constraint_count > 1 {
                // We're eligible to return a family solution, but first we need to find it! First
                // check any remaining constrained typevars with _no_ validity assignment for this
                // typevar.
                let previously_pending = self.pending.len();
                let has_family_solution = Cell::new(false);
                let individual_solution_is_required = Cell::new(false);
                self.validate_constrained(
                    db,
                    env,
                    storage,
                    path,
                    constrained,
                    &|this, storage, path| {
                        // Check which declared constraints are compatible with this complete
                        // solution for the remaining constrained typevars. Note that we _don't_
                        // update the candidate solution for those declared constraints — we want
                        // to return the family solution, after all. We just want to make sure that
                        // the individual declared constraints don't _invalidate_ that solution.
                        let mut satisfied_constraint_count = 0;
                        for declared_constraint in &constrained_typevar.declared_constraints {
                            let satisfied = Cell::new(false);
                            if let Some(constraints) = declared_constraint.constraints.as_deref() {
                                this.visit_constraints_and_then(
                                    db,
                                    env,
                                    storage,
                                    path,
                                    constraints,
                                    &|this, storage, path| {
                                        if !has_preservable_typevar_evidence
                                            && !this.evidence_satisfies_declared_constraint(
                                                db,
                                                env,
                                                storage,
                                                &evidence,
                                                declared_constraint.constrained_ty,
                                            )
                                        {
                                            return ControlFlow::Continue(());
                                        }
                                        let solution = this.pending_candidate_solution(
                                            db,
                                            env,
                                            storage,
                                            path,
                                            this.inferable,
                                            &path.quantified_typevars,
                                            None,
                                        );
                                        if solution.is_some() {
                                            satisfied.set(true);
                                        }
                                        ControlFlow::Continue(())
                                    },
                                )?;
                            }
                            if satisfied.into_inner() {
                                satisfied_constraint_count += 1;
                            }
                        }

                        match satisfied_constraint_count {
                            0 => {
                                // This family solution does not satisfy _any_ of the declared
                                // constraints. It definitely cannot be used as a solution, and
                                // also does not affect whether any other potential family
                                // solutions can be used.
                                ControlFlow::Continue(())
                            }
                            1 => {
                                // This family solution satisfies exactly one declared constraint.
                                // Family solutions are only used when the can consolidate more
                                // than one declared constraint. That means we don't want to use
                                // this family solution _or any other_. We'll create one or more
                                // individual solutions below.
                                individual_solution_is_required.set(true);
                                ControlFlow::Continue(())
                            }
                            _ => {
                                // This solution satisfies more than one declared constraint, so
                                // it's one of the eligible family solutions that we can report.
                                has_family_solution.set(true);
                                process_satisfied(this, storage, path)
                            }
                        }
                    },
                )?;

                // If we found at least one valid family solution, we can go ahead and return them.
                // If any potential family solution only matched a single declared constraint, we
                // need to fall through and find individual solutions
                // If every valid assignment for the remaining typevars admitted a family
                // solution, there is no need to also record the individual constraints.
                if has_family_solution.into_inner() && !individual_solution_is_required.into_inner()
                {
                    return ControlFlow::Continue(());
                }

                // If any family solution only matched a single declared constraint; or if we
                // didn't find any family solutions at all, we have to fall through and look for
                // individual solutions. Before proceeding, we remove any potential family
                // solutions we might have found during our search.
                self.pending.truncate(previously_pending);
            }
        }

        // We cannot return only family solutions, so also check which individual declared
        // constraints can be used in the solution.
        let previously_pending = self.pending.len();
        let has_lower_bound_evidence = path.positive_constraints().any(|(constraint, _)| {
            let constraint = storage.atomic_constraint_data(constraint);
            constraint.lower_bound_for(db, bound_typevar).is_some()
        });

        // A constraint preferred over every potentially valid alternative will also be preferred
        // over any subset of those alternatives. Try it first so that a successful branch can
        // discard the dominated alternatives before they multiply with later typevars.
        let preferred =
            constrained_typevar.preferred_constraint(db, env, has_lower_bound_evidence, |idx| {
                constrained_typevar.declared_constraints[idx]
                    .constraints
                    .is_some()
            });
        if let Some(preferred) = preferred
            && self.validate_single_declared_constraint(
                db,
                env,
                storage,
                path,
                bound_typevar,
                &evidence,
                &constrained_typevar.declared_constraints[preferred],
                constrained,
                process_satisfied,
            )?
        {
            return ControlFlow::Continue(());
        }

        let constraint_count = constrained_typevar.declared_constraints.len();
        let mut constraint_satisfied = SmallVec::<[bool; 4]>::with_capacity(constraint_count);
        let mut constraint_solutions =
            SmallVec::<[Range<usize>; 4]>::with_capacity(constraint_count);
        for (idx, declared_constraint) in
            constrained_typevar.declared_constraints.iter().enumerate()
        {
            let start = self.pending.len();
            if preferred == Some(idx) {
                // We already checked this one above.
                constraint_satisfied.push(false);
                constraint_solutions.push(start..start);
                continue;
            }

            let satisfied = self.validate_single_declared_constraint(
                db,
                env,
                storage,
                path,
                bound_typevar,
                &evidence,
                declared_constraint,
                constrained,
                process_satisfied,
            )?;
            let end = self.pending.len();
            constraint_satisfied.push(satisfied);
            constraint_solutions.push(start..end);
        }

        // Fast path: If exactly one constraint was satisfied, we can return its solutions
        // immediately. If _no_ constraints were satisfied, we can return its _lack_ of solutions
        // immediately.
        let satisfied_constraint_count = constraint_satisfied
            .iter()
            .filter(|satisfied| **satisfied)
            .count();
        if satisfied_constraint_count <= 1 {
            return ControlFlow::Continue(());
        }

        // At this point, we know that more than one constraint was satisfied. Check to see if any
        // one of them is preferred over all of the others. If so, we prefer that single solution.
        let preferred =
            constrained_typevar.preferred_constraint(db, env, has_lower_bound_evidence, |idx| {
                constraint_satisfied[idx]
            });

        // If there was a single preferred constraint, remove the solutions from the other
        // constraints. Otherwise keep them all, and let the caller decide how to handle the
        // ambiguity.
        if let Some(best) = preferred {
            let solutions = &constraint_solutions[best];
            self.pending.truncate(solutions.end);
            self.pending.drain(previously_pending..solutions.start);
        }

        ControlFlow::Continue(())
    }

    #[expect(clippy::too_many_arguments)]
    fn validate_single_declared_constraint(
        &mut self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        storage: &mut ConstraintSetStorage<'db>,
        path: &mut PathAssignments,
        bound_typevar: BoundTypeVarInstance<'db>,
        evidence: &CandidateTypeVarSolution<'db>,
        declared_constraint: &DeclaredConstraint<'db>,
        constrained: &Slice<BoundTypeVarInstance<'db>, Constrained<'db>>,
        process_satisfied: &ProcessSatisfied<'_, 'db, L, Break<L::Break>>,
    ) -> ControlFlow<Break<L::Break>, bool> {
        let satisfied = Cell::new(false);
        if let Some(constraints) = declared_constraint.constraints.as_deref() {
            self.with_declared_constraint_solution(
                db,
                bound_typevar,
                declared_constraint.constrained_ty,
                |this| {
                    this.visit_constraints_and_then(
                        db,
                        env,
                        storage,
                        path,
                        constraints,
                        &|this, storage, path| {
                            // Selecting a concrete constraint must not specialize a caller's fixed
                            // typevar: `S & str <= int` may hold for some `S`, but not for every `S`.
                            if !this.evidence_satisfies_declared_constraint(
                                db,
                                env,
                                storage,
                                evidence,
                                declared_constraint.constrained_ty,
                            ) {
                                return ControlFlow::Continue(());
                            }

                            // The candidate solution satisfies this declared constraint, but we still
                            // need to check any remaining constrained typevars.
                            this.validate_constrained(
                                db,
                                env,
                                storage,
                                path,
                                constrained,
                                &|this, storage, path| {
                                    satisfied.set(true);
                                    process_satisfied(this, storage, path)
                                },
                            )
                        },
                    )
                },
            )?;
        }
        ControlFlow::Continue(satisfied.into_inner())
    }

    /// Create a pending candidate solution for the current path.
    ///
    /// This method is fallible because a path to the `true` terminal might still be unsatisfiable,
    /// if it introduces conflicting bounds for a typevar. (The sequent map _should_ detect most
    /// cases of conflicting bounds, but we have some final last-minute checks here to catch cases
    /// that the sequent map can't handle yet.)
    ///
    /// TODO(dcreager): I consider this a bug in the sequent map, which should be addressed in its
    /// own right, since there are many other methods that assume that a path to `true` terminal
    /// indicates satisfiability.
    #[expect(clippy::too_many_arguments)]
    fn pending_candidate_solution(
        &self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        storage: &mut ConstraintSetStorage<'db>,
        path: &PathAssignments,
        inferable: TypeVarSet<'db>,
        hidden: &Support,
        typevar_violations: Option<
            &FxHashMap<BoundTypeVarInstance<'db>, SolutionViolationKind<'db>>,
        >,
    ) -> Option<PendingCandidateSolution<'db>> {
        // Sort the constraints in each path by their `source_order`s, to ensure that we construct
        // any unions or intersections in our type mappings in a stable order. Constraints might
        // come out of `PathAssignments` with identical `source_order`s, but if they do, those
        // "tied" constraints will still be ordered in a stable way. So we need a stable sort to
        // retain that stable per-tie ordering.
        let mut typevars: Vec<_> = path
            .positive_constraints()
            // Ignore any constraints that were replaced with other constraints on this path due to
            // substituting an exact type for some typevar.
            .filter(|(constraint, _)| !path.constraint_is_substituted(*constraint))
            // Ignore any constraints that reference a quantified-away typevar. Those are local to
            // the existential's body, and should not leak outside. The sequent map should have
            // propagated any information about how the quantified-away typevars related to the
            // inferable typevars.
            .filter(|(constraint, _)| {
                let constraint_support = storage.constraint_support(constraint.into_inner());
                !hidden.overlaps_with(constraint_support)
            })
            .map(|(constraint, source_constraint)| {
                let source_order = self
                    .source_orders
                    .get_index_of(&source_constraint)
                    .expect("every TDD constraint should have a source order");
                (constraint, source_order)
            })
            .collect();
        typevars.sort_by_key(|(_, source_order)| *source_order);
        let source_orders = typevars
            .iter()
            .map(|(_, source_order)| *source_order)
            .collect();

        // Then collect the combined lower and upper bounds for each typevar.
        let mut mappings: FxIndexMap<BoundTypeVarInstance<'db>, CandidateTypeVarSolver<'db>> =
            FxIndexMap::default();

        for (constraint, _) in typevars {
            let constraint = storage.atomic_constraint_data(constraint);
            match constraint {
                AtomicConstraint::ConcreteLower(lower) => {
                    if lower.typevar.is_inferable(db, inferable) {
                        let solver = mappings.entry(lower.typevar).or_default();
                        solver.add_constraint(db, lower.typevar, constraint);
                    }
                }
                AtomicConstraint::ConcreteUpper(upper) => {
                    if upper.typevar.is_inferable(db, inferable) {
                        let solver = mappings.entry(upper.typevar).or_default();
                        solver.add_constraint(db, upper.typevar, constraint);
                    }
                }
                AtomicConstraint::ConcreteEquivalence(equivalence) => {
                    if equivalence.typevar.is_inferable(db, inferable) {
                        let solver = mappings.entry(equivalence.typevar).or_default();
                        solver.add_constraint(db, equivalence.typevar, constraint);
                    }
                }
                AtomicConstraint::TypeVarRange(bound) => {
                    // A direct relationship between an inferable and non-inferable typevar must
                    // contribute bounds for both endpoints. Contextual inference relies on the
                    // reverse, non-inferable binding to preserve relationships to outer typevars.
                    if bound.left.is_inferable(db, inferable)
                        || bound.right.is_inferable(db, inferable)
                    {
                        let solver = mappings.entry(bound.left).or_default();
                        solver.add_constraint(db, bound.left, constraint);
                        let solver = mappings.entry(bound.right).or_default();
                        solver.add_constraint(db, bound.right, constraint);
                    }
                }
                AtomicConstraint::TypeVarEquivalence(bound) => {
                    // A direct relationship between an inferable and non-inferable typevar must
                    // contribute bounds for both endpoints. Contextual inference relies on the
                    // reverse, non-inferable binding to preserve relationships to outer typevars.
                    let (left, right) = bound.in_builder(db, storage);
                    if left.is_inferable(db, inferable) || right.is_inferable(db, inferable) {
                        let solver = mappings.entry(left).or_default();
                        solver.add_constraint(db, left, constraint);
                        let solver = mappings.entry(right).or_default();
                        solver.add_constraint(db, right, constraint);
                    }
                }
            }
        }

        let mut violations = Vec::new();
        let typevars: Option<Box<[_]>> = mappings
            .into_iter()
            .map(|(bound_typevar, solver)| {
                let mut solution = solver.finish(db, env, storage, bound_typevar)?;
                let argument = match self
                    .declared_constraint_solutions
                    .get(&bound_typevar.identity(db))
                {
                    Some(&ty) => {
                        solution.selected_declared_constraint = Some(ty);
                        Some(ty)
                    }
                    None => solution.inference_lower(db, env),
                };

                if let Some(typevar_violations) = typevar_violations
                    && let Some(kind) = typevar_violations.get(&bound_typevar)
                {
                    violations.push(SolutionViolation {
                        bound_typevar,
                        variance: solution.variance(),
                        kind: match kind {
                            SolutionViolationKind::UpperBound(_) => {
                                SolutionViolationKind::UpperBound(argument)
                            }
                            kind @ SolutionViolationKind::Constraints { .. } => kind.clone(),
                        },
                    });
                }

                Some(solution)
            })
            .collect();
        let typevars = typevars?;

        let validity = match typevar_violations {
            None => SolutionValidity::Valid,
            Some(_) if violations.is_empty() => return None,
            Some(_) => SolutionValidity::Invalid(violations.into_boxed_slice()),
        };
        let candidate = CandidateSolution {
            typevars,
            validity,
            residual: None,
        };
        let pending = PendingCandidateSolution {
            candidate,
            source_orders,
        };
        Some(pending)
    }

    fn signed_path(
        &self,
        storage: &mut ConstraintSetStorage<'db>,
        path: &PathAssignments,
        negative_scopes_from: usize,
    ) -> (NodeId, Option<SourceOrderId>) {
        let mut node = ALWAYS_TRUE;
        let mut source_order = None;
        let mut assignments: Vec<_> = path.assignments.iter().collect();
        // Keep the same evidence order as the independent candidate bounds, including
        // stable ordering between assignments derived from the same source constraint.
        assignments.sort_by_key(|(_, (source_constraint, _))| {
            self.source_orders
                .get_index_of(source_constraint)
                .expect("every TDD constraint should have a source order")
        });
        for (&assignment, _) in assignments {
            let (condition, order) = match assignment {
                Assignment::Positive(id) => Node::new_constraint(storage, id.into_inner()),
                Assignment::Negative(id) => {
                    let (condition, order) = Node::new_constraint(storage, id.into_inner());
                    (condition.negate(storage), order)
                }
                Assignment::Unconstrained(_) => continue,
            };
            node = node.and(storage, condition);
            source_order = storage.ordered_source_order(source_order, order);
        }
        for scope in &self.negative_scopes[negative_scopes_from..] {
            let (condition, order) = Node::new_constraint(storage, *scope);
            let condition = condition.negate(storage);
            node = node.and(storage, condition);
            source_order = storage.ordered_source_order(source_order, order);
        }
        (node, source_order)
    }

    fn found_satisfied_path(
        &mut self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        storage: &mut ConstraintSetStorage<'db>,
        path: &PathAssignments,
    ) -> ControlFlow<Break<L::Break>, bool> {
        let Some(mut pending) = self.pending_candidate_solution(
            db,
            env,
            storage,
            path,
            self.inferable,
            &path.quantified_typevars,
            None,
        ) else {
            return ControlFlow::Continue(false);
        };
        self.limits.satisfied_path().map_break(Break::Limits)?;
        if self.positive_locals.iter().next().is_some() {
            let (node, source_order) = self.signed_path(storage, path, 0);
            let relation = match node.node() {
                Node::Interior(root) => OwnedConstraintSetBuilder::snapshot(
                    storage,
                    root,
                    source_order.expect("nonterminal path has source order"),
                ),
                Node::AlwaysTrue | Node::AlwaysFalse => OwnedConstraintSet {
                    node,
                    source_order: None,
                    inner: None,
                },
            };
            pending.candidate.residual = Some(CandidateResidual {
                relation,
                locals: TypeVarSet::from_typevars(
                    db,
                    self.positive_locals
                        .iter()
                        .map(|id| storage.typevar_data(id)),
                ),
                inferable: self.inferable,
            });
        }
        self.pending.push(pending);
        ControlFlow::Continue(true)
    }

    /// Having already determined that a satisfiable path violates the declared upper bounds (TODO
    /// and constraints) of the relevant typevars, determines _which particular_ upper bounds or
    /// constraints were violated. Adds an [`Invalid`][SolutionValidity::Invalid] candidate
    /// solution for the path recording those violations, so that a later stage can transform them
    /// into useful diagnostics.
    fn attribute_typevar_failures(
        &mut self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        storage: &mut ConstraintSetStorage<'db>,
        path: &mut PathAssignments,
        upper_bounds: &Slice<BoundTypeVarInstance<'db>, UpperBound>,
        constrained: &Slice<BoundTypeVarInstance<'db>, Constrained<'db>>,
    ) -> ControlFlow<Break<L::Break>> {
        let mut violations = FxHashMap::default();

        for (bound_typevar, upper_bound) in upper_bounds {
            let satisfied = Cell::new(false);
            if let Some(constraints) = upper_bound.constraints.as_deref() {
                self.visit_constraints_and_then(
                    db,
                    env,
                    storage,
                    path,
                    constraints,
                    &|this, storage, path| {
                        let pending = this.pending_candidate_solution(
                            db,
                            env,
                            storage,
                            path,
                            this.inferable,
                            &path.quantified_typevars,
                            None,
                        );
                        if pending.is_some() {
                            satisfied.set(true);
                        }
                        ControlFlow::Continue(())
                    },
                )?;
            }
            if !satisfied.into_inner() {
                violations.insert(*bound_typevar, SolutionViolationKind::UpperBound(None));
            }
        }

        // Construct diagnostic lower bounds in the same stable source order as normal solutions.
        let mut inference_constraints: Vec<_> = path.positive_constraints().collect();
        inference_constraints.sort_by_key(|(_, source)| self.source_orders.get_index_of(source));
        for (bound_typevar, constrained_typevar) in constrained {
            let Some(evidence) = Self::candidate_evidence(
                db,
                env,
                storage,
                inference_constraints
                    .iter()
                    .map(|(constraint, _)| *constraint),
                *bound_typevar,
            ) else {
                continue;
            };

            let satisfied = Cell::new(false);
            for declared_constraint in &constrained_typevar.declared_constraints {
                if let Some(constraints) = declared_constraint.constraints.as_deref() {
                    self.visit_constraints_and_then(
                        db,
                        env,
                        storage,
                        path,
                        constraints,
                        &|this, storage, path| {
                            if !this.evidence_satisfies_declared_constraint(
                                db,
                                env,
                                storage,
                                &evidence,
                                declared_constraint.constrained_ty,
                            ) {
                                return ControlFlow::Continue(());
                            }
                            let pending = this.pending_candidate_solution(
                                db,
                                env,
                                storage,
                                path,
                                this.inferable,
                                &path.quantified_typevars,
                                None,
                            );
                            if pending.is_some() {
                                satisfied.set(true);
                            }
                            ControlFlow::Continue(())
                        },
                    )?;
                }
            }
            if !satisfied.into_inner()
                && let Some(evidence) = self.constraint_failure_evidence(
                    db,
                    env,
                    storage,
                    &evidence,
                    constrained_typevar,
                )?
            {
                violations.insert(
                    *bound_typevar,
                    SolutionViolationKind::Constraints {
                        constraints: constrained_typevar.typevar_constraints,
                        evidence,
                    },
                );
            }
        }

        // Complete validation failed, but no single declaration explains why. The declarations
        // are only inconsistent in combination, so there is no attributable candidate to retain.
        if violations.is_empty() {
            return ControlFlow::Continue(());
        }

        if let Some(pending) = self.pending_candidate_solution(
            db,
            env,
            storage,
            path,
            self.inferable,
            &path.quantified_typevars,
            Some(&violations),
        ) {
            self.limits.satisfied_path().map_break(Break::Limits)?;
            self.pending.push(pending);
        }
        ControlFlow::Continue(())
    }

    pub(super) fn finish(mut self) -> CandidateSolutions<'db> {
        if self.pending.is_empty() && !self.incomplete {
            return CandidateSolutions::Unsatisfiable;
        }
        if let [single] = self.pending.as_slice()
            && single.candidate.typevars.is_empty()
            && single.candidate.residual.is_none()
            && !self.incomplete
        {
            return CandidateSolutions::Unconstrained;
        }

        self.pending.sort_by(|pending1, pending2| {
            let source_orders1 = pending1.source_orders.iter().copied();
            let source_orders2 = pending2.source_orders.iter().copied();
            source_orders1.cmp(source_orders2)
        });

        let result = self
            .pending
            .drain(..)
            .map(|pending| pending.candidate)
            .collect();
        CandidateSolutions::Constrained {
            inferable: self.inferable,
            paths: result,
            incomplete: self.incomplete,
        }
    }
}

/// Validations that must be verified for each candidate solution.
#[derive(Default)]
pub(super) struct Validations<'db> {
    upper_bounds: FxIndexMap<BoundTypeVarInstance<'db>, UpperBound>,
    constrained: FxIndexMap<BoundTypeVarInstance<'db>, Constrained<'db>>,
}

type ValidationConstraints = Option<SmallVec<[AtomicConstraintId; 4]>>;

struct UpperBound {
    constraints: ValidationConstraints,
}

struct Constrained<'db> {
    typevar_constraints: TypeVarConstraints<'db>,
    declared_constraints: SmallVec<[DeclaredConstraint<'db>; 4]>,
}

struct DeclaredConstraint<'db> {
    constraints: ValidationConstraints,
    constrained_ty: Type<'db>,
}

impl<'db> Validations<'db> {
    fn constraints(&self) -> impl Iterator<Item = AtomicConstraintId> + Clone {
        self.upper_bounds
            .values()
            .map(|bound| &bound.constraints)
            .chain(
                self.constrained
                    .values()
                    .flat_map(|bound| &bound.declared_constraints)
                    .map(|bound| &bound.constraints),
            )
            .flat_map(|constraints| constraints.iter().flatten().copied())
    }

    /// A binder owns only its locals' declarations. Types mentioned by those declarations remain
    /// free, and their declarations follow the outer query's validation policy.
    fn from_locals(
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        storage: &mut ConstraintSetStorage<'db>,
        locals: &Support,
    ) -> Self {
        let mut result = Self::default();
        let mut dependencies = Support::default();
        let mut seen = locals.clone();
        for local in locals.iter() {
            let bound_typevar = storage.typevar_data(local);
            result.add_typevar(
                db,
                env,
                storage,
                &mut dependencies,
                &mut seen,
                bound_typevar,
            );
        }
        result
    }

    fn from_support(
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        storage: &mut ConstraintSetStorage<'db>,
        all_typevars: &Support,
    ) -> Self {
        let mut result = Self::default();
        let mut typevar_queue = all_typevars.clone();
        let mut seen_typevars = Support::default();
        while let Some(typevar) = typevar_queue.pop() {
            seen_typevars.insert(typevar);
            let bound_typevar = storage.typevar_data(typevar);
            result.add_typevar(
                db,
                env,
                storage,
                &mut typevar_queue,
                &mut seen_typevars,
                bound_typevar,
            );
        }
        result
    }

    fn add_typevar(
        &mut self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        storage: &mut ConstraintSetStorage<'db>,
        typevar_queue: &mut Support,
        seen_typevars: &mut Support,
        bound_typevar: BoundTypeVarInstance<'db>,
    ) {
        let bound_or_constraints = bound_typevar.typevar(db).bound_or_constraints(db, env);
        match bound_or_constraints {
            Some(TypeVarBoundOrConstraints::UpperBound(bound)) => self.add_upper_bound(
                db,
                env,
                storage,
                typevar_queue,
                seen_typevars,
                bound_typevar,
                bound,
            ),
            Some(TypeVarBoundOrConstraints::Constraints(declared_constraints)) => self
                .add_constrained(
                    db,
                    env,
                    storage,
                    typevar_queue,
                    seen_typevars,
                    bound_typevar,
                    declared_constraints,
                ),
            None => {}
        }
    }

    fn intern_typevar_constraints(
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        storage: &mut ConstraintSetStorage<'db>,
        typevar_queue: &mut Support,
        seen_typevars: &mut Support,
        constraints: impl Iterator<Item = Result<AtomicConstraint<'db>, UnsatisfiableBound>>,
    ) -> ValidationConstraints {
        let constraints: ValidationConstraints = constraints
            .map(Result::ok)
            .map(|constraint| {
                constraint.map(|constraint| storage.intern_atomic_constraint(db, env, constraint))
            })
            .collect();

        // Outer-query validation also follows declarations of typevars mentioned in these bounds.
        // Binder validation only checks its owned locals and leaves this dependency queue unused.
        // TODO: Consider calculating dependencies at construction time.
        for constraint in constraints.iter().flatten() {
            let constraint_support = storage.constraint_support(constraint.into_inner());
            let new_typevars = constraint_support - &*seen_typevars;
            *typevar_queue |= &new_typevars;
        }

        constraints
    }

    #[expect(clippy::too_many_arguments)]
    fn add_upper_bound(
        &mut self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        storage: &mut ConstraintSetStorage<'db>,
        typevar_queue: &mut Support,
        seen_typevars: &mut Support,
        bound_typevar: BoundTypeVarInstance<'db>,
        bound: Type<'db>,
    ) {
        self.upper_bounds.entry(bound_typevar).or_insert_with(|| {
            let constraints = AtomicConstraint::new_upper_bound(
                db,
                env,
                ConstraintProvenance::Validity,
                bound_typevar,
                bound,
            );
            let constraints = Self::intern_typevar_constraints(
                db,
                env,
                storage,
                typevar_queue,
                seen_typevars,
                constraints,
            );
            UpperBound { constraints }
        });
    }

    #[expect(clippy::too_many_arguments)]
    fn add_constrained(
        &mut self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        storage: &mut ConstraintSetStorage<'db>,
        typevar_queue: &mut Support,
        seen_typevars: &mut Support,
        bound_typevar: BoundTypeVarInstance<'db>,
        declared_constraints: TypeVarConstraints<'db>,
    ) {
        self.constrained.entry(bound_typevar).or_insert_with(|| {
            let validations = declared_constraints
                .elements(db)
                .iter()
                .map(|&constrained_ty| {
                    let constraints = AtomicConstraint::new_equivalence_bound(
                        db,
                        env,
                        ConstraintProvenance::Validity,
                        bound_typevar,
                        constrained_ty,
                    );
                    let constraints = Self::intern_typevar_constraints(
                        db,
                        env,
                        storage,
                        typevar_queue,
                        seen_typevars,
                        constraints,
                    );
                    DeclaredConstraint {
                        constraints,
                        constrained_ty,
                    }
                })
                .collect();
            Constrained {
                typevar_constraints: declared_constraints,
                declared_constraints: validations,
            }
        });
    }
}

impl<'db> Constrained<'db> {
    fn preferred_constraint(
        &self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        has_lower_bound_evidence: bool,
        is_eligible: impl Fn(usize) -> bool,
    ) -> Option<usize> {
        'candidate: for (candidate_idx, declared_constraint) in
            self.declared_constraints.iter().enumerate()
        {
            if !is_eligible(candidate_idx) {
                continue;
            }

            let candidate = declared_constraint.constrained_ty;
            for (other_idx, other_constraint) in self.declared_constraints.iter().enumerate() {
                if candidate_idx == other_idx || !is_eligible(other_idx) {
                    continue;
                }

                let other = other_constraint.constrained_ty;
                let candidate_assignable_to_other = candidate.is_assignable_to(db, env, other);
                let other_assignable_to_candidate = other.is_assignable_to(db, env, candidate);

                // Lower-bound evidence asks for the narrowest compatible declared constraint
                // above the lower bound. With only upper-bound evidence, ask for the widest
                // compatible declared constraint below the upper bound. If the candidates are
                // assignable in both directions, prefer a fully static constraint over a gradual
                // one. Equivalent constraints preserve declaration order.
                let candidate_is_at_least_as_good =
                    match (candidate_assignable_to_other, other_assignable_to_candidate) {
                        (false, false) => false,
                        (true, false) => has_lower_bound_evidence,
                        (false, true) => !has_lower_bound_evidence,
                        (true, true) => {
                            candidate.is_fully_static(db, env) || !other.is_fully_static(db, env)
                        }
                    };
                if !candidate_is_at_least_as_good {
                    continue 'candidate;
                }
            }

            return Some(candidate_idx);
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::db::tests::setup_db;
    use crate::types::TypeVarVariance;
    use crate::types::constraints::{SolutionPaths, Solutions};
    use ruff_python_ast::name::Name;

    #[test]
    fn existential_proof_budget_is_shared_across_queries() {
        let db = setup_db();
        let db = &db;
        let env = db.program_environment();
        let [local, free] = ["Local", "Free"].map(|name| {
            BoundTypeVarInstance::synthetic(
                db,
                &env,
                Name::new_static(name),
                TypeVarVariance::Invariant,
            )
        });
        let builder = ConstraintSetBuilder::new();
        let scoped = ConstraintSet::constrain_typevar_equivalence_bound(
            db,
            &env,
            &builder,
            local,
            Type::TypeVar(free),
        )
        .reduce_inferable(db, &env, &builder, TypeVarSet::from_typevars(db, [local]));
        let negative = scoped.negate(db, &builder);
        let mut storage = builder.storage.borrow_mut();
        let source_orders = storage.calculate_source_orders(negative.source_order);
        let mut walker = SolutionWalker::new(
            db,
            &mut storage,
            source_orders,
            TypeVarSet::None,
            UnboundedSolutionLimits,
            negative.node,
        );
        // Local=Free is a complete witness under every outer specialization. Proving it
        // again must consume the same temporary-type budget, rather than replenish it.
        walker.witness_budget = ProjectionTypeBudget::new(1);
        for expected in [Satisfiability::Unsatisfiable, Satisfiability::Incomplete] {
            let mut path =
                negative
                    .node
                    .path_assignments(db, &env, &mut storage, negative.source_order);
            let ControlFlow::Continue(actual) = walker.node_is_satisfiable_on_path(
                db,
                &env,
                &mut storage,
                &mut path,
                Polarity::Positive,
                negative.node,
                None,
            );
            assert_eq!(actual, expected);
        }
        // An unresolved sibling does not obscure an independently certified solution.
        let mut path = PathAssignments::default();
        let ControlFlow::Continue(actual) = walker.node_is_satisfiable_on_path(
            db,
            &env,
            &mut storage,
            &mut path,
            Polarity::Positive,
            ALWAYS_TRUE,
            None,
        );
        assert_eq!(actual, Satisfiability::Satisfiable);
        let mut path =
            negative
                .node
                .path_assignments(db, &env, &mut storage, negative.source_order);
        let ControlFlow::Continue(()) = walker.visit_node(
            db,
            &env,
            &mut storage,
            &mut path,
            None,
            Polarity::Positive,
            negative.node,
        );
        let candidates = walker.finish();
        drop(storage);
        assert_eq!(
            candidates.solve(db, &env, &builder),
            Solutions::Constrained(SolutionPaths::Incomplete(vec![]))
        );
    }
}
