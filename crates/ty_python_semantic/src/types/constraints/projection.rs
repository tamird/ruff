//! Bounded projections of correlated constraint solutions.

use rustc_hash::{FxHashMap, FxHashSet};
use std::ops::ControlFlow;

use super::{
    ALWAYS_FALSE, ALWAYS_TRUE, BoundedSolutionLimits, CandidateSolutions, CandidateTypeVarSolution,
    ConstraintId, ConstraintSet, PathBoundSolution, SolutionLimits, Solutions, TypeVarSolution,
};
use crate::types::typevar::TypeVarSet;
use crate::types::{
    ApplySpecialization, ApplyTypeMappingVisitor, GenericContext, Type, TypeContext, TypeMapping,
    TypeVarVariance,
};
use crate::{Db, ProgramEnvironment};

/// Limits for one projection, including preprocessing, path collection, and its result.
#[derive(Clone, Copy, Debug)]
pub(crate) struct SolutionBudget {
    /// Satisfied paths collected before per-variable solution selection can reject them.
    pub(crate) paths: usize,
    /// Interior and terminal visits, shared by preprocessing, path collection, and validation.
    pub(crate) visits: usize,
    /// Set-theoretic terms contributed to the result, including terms exposed by aliases.
    /// Also bounds storage when retaining alternatives.
    pub(crate) type_terms: usize,
}

impl Default for SolutionBudget {
    fn default() -> Self {
        // Allow long, simple conjunctions and sizable existing unions without allowing their
        // alternatives to expand into an equally large family of specializations.
        Self {
            paths: 4_096,
            visits: 32_768,
            type_terms: 8_192,
        }
    }
}

/// Why an exact projection could not be completed.
///
/// None of these outcomes proves that the constraint set is unsatisfiable. In particular, a
/// caller must not use the prefix visited before a limit was reached as the complete answer.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum ProjectionError {
    PathBudgetExceeded,
    TraversalBudgetExceeded,
    TypeBudgetExceeded,
    IncompleteSolution,
}

/// An exact projection of all retained solution paths.
#[derive(Debug, Eq, PartialEq)]
pub(crate) enum SolutionProjection<T> {
    Unsatisfiable,
    Unconstrained,
    Constrained(T),
}

/// A shared limit on the type terms consumed while constructing a projection.
///
/// Union projections charge each contribution before adding it. An intersection projection must
/// additionally use `IntersectionType::bounded_from_elements`, since distributing intersections
/// over unions can multiply, rather than add, the number of terms.
pub(crate) struct ProjectionTypeBudget {
    remaining: usize,
}

impl ProjectionTypeBudget {
    pub(super) fn new(remaining: usize) -> Self {
        Self { remaining }
    }

    pub(crate) fn charge_items(&mut self, count: usize) -> Result<(), ProjectionError> {
        self.remaining = self
            .remaining
            .checked_sub(count)
            .ok_or(ProjectionError::TypeBudgetExceeded)?;
        Ok(())
    }

    /// Charges the set-theoretic terms that a type constructor may flatten or inspect. Aliases
    /// are included so a large union cannot evade the limit by being hidden behind a name.
    pub(crate) fn charge_type<'db>(
        &mut self,
        db: &'db dyn Db,
        ty: Type<'db>,
    ) -> Result<(), ProjectionError> {
        self.charge_type_inner(db, ty, &mut FxHashSet::default())
    }

    fn charge_type_inner<'db>(
        &mut self,
        db: &'db dyn Db,
        ty: Type<'db>,
        seen_aliases: &mut FxHashSet<Type<'db>>,
    ) -> Result<(), ProjectionError> {
        self.charge_items(1)?;
        match ty {
            Type::Union(union) => {
                for element in union.elements(db) {
                    self.charge_type_inner(db, *element, seen_aliases)?;
                }
            }
            Type::Intersection(intersection) => {
                for element in intersection
                    .iter_positive(db)
                    .chain(intersection.iter_negative(db))
                {
                    self.charge_type_inner(db, element, seen_aliases)?;
                }
            }
            Type::TypeAlias(alias) if seen_aliases.insert(ty) => {
                self.charge_type_inner(db, alias.value_type(db), seen_aliases)?;
            }
            _ => {}
        }
        Ok(())
    }
}

impl<'db> ConstraintSet<'db, '_> {
    /// Computes default solutions for each BDD path within the default projection budget.
    pub(crate) fn solutions(
        self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        inferable: TypeVarSet<'db>,
    ) -> Result<Solutions<'db>, ProjectionError> {
        let builder = self.builder;
        self.solutions_with(
            db,
            env,
            inferable,
            SolutionBudget::default(),
            |_variance, path_bound| CandidateSolutions::default_solve(db, env, builder, path_bound),
        )
    }

    pub(super) fn bounded_path_bounds(
        self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        inferable: TypeVarSet<'db>,
        budget: SolutionBudget,
    ) -> Result<(CandidateSolutions<'db>, BoundedSolutionLimits), ProjectionError> {
        let mut limits = BoundedSolutionLimits {
            remaining_paths: budget.paths,
            remaining_visits: budget.visits,
        };
        let paths = CandidateSolutions::compute_with_limits(
            db,
            env,
            &mut self.builder.storage.borrow_mut(),
            self.node,
            inferable,
            self.source_order,
            &mut limits,
        );
        match paths {
            ControlFlow::Continue(paths) => Ok((paths, limits)),
            ControlFlow::Break(error) => Err(error),
        }
    }

    /// Projects a solution into a specialization and proves it against the complete relation.
    /// Unspecialized variables stay rigid. Path discovery and proof share one traversal budget;
    /// the projection callback charges its constructed result against the shared type budget.
    /// An unproved witness or exhausted search is incomplete. `None` proves the relation
    /// unsatisfiable.
    pub(crate) fn find_verified_specialization(
        self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        inferable: TypeVarSet<'db>,
        budget: SolutionBudget,
        mut project: impl FnMut(
            &[TypeVarSolution<'db>],
            &mut ProjectionTypeBudget,
        ) -> Result<Option<Vec<TypeVarSolution<'db>>>, ProjectionError>,
        fallback: Vec<TypeVarSolution<'db>>,
    ) -> Result<Option<Vec<TypeVarSolution<'db>>>, ProjectionError> {
        let (path_bounds, mut limits) = self.bounded_path_bounds(db, env, inferable, budget)?;
        let (inferable, paths, incomplete) = match path_bounds {
            CandidateSolutions::Unsatisfiable => return Ok(None),
            CandidateSolutions::Unconstrained => return Err(ProjectionError::IncompleteSolution),
            CandidateSolutions::Constrained {
                inferable,
                paths,
                incomplete,
            } => (inferable, paths, incomplete),
        };
        if incomplete {
            return Err(ProjectionError::IncompleteSolution);
        }

        let mut type_budget = ProjectionTypeBudget::new(budget.type_terms);
        let verify = |bindings: &[TypeVarSolution<'db>],
                      limits: &mut BoundedSolutionLimits,
                      type_budget: &mut ProjectionTypeBudget| {
            for binding in bindings {
                if let Err(error) = type_budget.charge_type(db, binding.solution) {
                    return ControlFlow::Break(error);
                }
            }
            self.prove_specialization(db, env, bindings, limits, type_budget)
        };

        for path in paths {
            let solution = CandidateSolutions::solve_path_with(
                db,
                env,
                inferable,
                &path,
                &mut limits,
                &mut type_budget,
                &mut |_, bound| CandidateSolutions::default_solve(db, env, self.builder, bound),
            );
            let Some((solution, incomplete)) = (match solution {
                ControlFlow::Continue(solution) => solution,
                ControlFlow::Break(error) => return Err(error),
            }) else {
                continue;
            };
            if incomplete {
                return Err(ProjectionError::IncompleteSolution);
            }
            if !solution.is_valid() {
                continue;
            }
            let Some(bindings) = project(&solution.solved_typevars, &mut type_budget)? else {
                continue;
            };
            match verify(&bindings, &mut limits, &mut type_budget) {
                ControlFlow::Continue(true) => return Ok(Some(bindings)),
                ControlFlow::Continue(false) => {}
                ControlFlow::Break(error) => return Err(error),
            }
        }
        match verify(&fallback, &mut limits, &mut type_budget) {
            ControlFlow::Continue(true) => Ok(Some(fallback)),
            ControlFlow::Continue(false) => Err(ProjectionError::IncompleteSolution),
            ControlFlow::Break(error) => Err(error),
        }
    }

    /// Proves a sufficient condition for a specialization directly on the original decision
    /// graph. The traversal budget bounds original node visits and the number of mapped atoms.
    /// Mapping uses ordinary type relation evaluation. Each mapped result is inspected only at
    /// its root; unresolved correlations and quantified atoms remain unproved.
    fn prove_specialization(
        self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        bindings: &[TypeVarSolution<'db>],
        limits: &mut BoundedSolutionLimits,
        type_budget: &mut ProjectionTypeBudget,
    ) -> ControlFlow<ProjectionError, bool> {
        let context = GenericContext::from_typevar_instances(
            db,
            env,
            bindings.iter().map(|binding| binding.bound_typevar),
        );
        let types: Vec<_> = bindings.iter().map(|binding| binding.solution).collect();
        let mapping = TypeMapping::ApplySpecialization(ApplySpecialization::Partial {
            generic_context: context,
            types: &types,
            skip: None,
        });
        let visitor = ApplyTypeMappingVisitor::new(env);
        let mut proven = FxHashMap::from_iter([(ALWAYS_TRUE, true), (ALWAYS_FALSE, false)]);
        let mut atomic_proofs: FxHashMap<(ConstraintId, bool), bool> = FxHashMap::default();
        let mut pending = vec![(self.node, false)];
        while let Some((node, expanded)) = pending.pop() {
            if proven.contains_key(&node) {
                continue;
            }
            let interior = self.builder.storage.borrow().interior_node_data(node);
            if !expanded {
                limits.visit_node()?;
                pending.push((node, true));
                pending.extend(
                    [interior.if_false, interior.if_true, interior.if_uncertain]
                        .into_iter()
                        .map(|child| (child, false)),
                );
                continue;
            }
            let holds = if proven[&interior.if_uncertain] {
                true
            } else {
                match (proven[&interior.if_true], proven[&interior.if_false]) {
                    (true, true) => true,
                    (false, false) => false,
                    (true, false) | (false, true) => {
                        // The chosen child suffices only if the opposite condition is impossible.
                        let value = proven[&interior.if_true];
                        match atomic_proofs.entry((interior.constraint, value)) {
                            std::collections::hash_map::Entry::Occupied(entry) => *entry.get(),
                            std::collections::hash_map::Entry::Vacant(entry) => {
                                let Some(atomic) = self
                                    .builder
                                    .storage
                                    .borrow()
                                    .constraint_data(interior.constraint)
                                    .as_atomic()
                                else {
                                    proven.insert(node, false);
                                    continue;
                                };
                                for ty in atomic.types() {
                                    if let Err(error) = type_budget.charge_type(db, ty) {
                                        return ControlFlow::Break(error);
                                    }
                                }
                                let mapped =
                                    atomic.mapped(db, &mapping, TypeContext::default(), &visitor);
                                *entry.insert(mapped.proves_value_from_root(db, env, value))
                            }
                        }
                    }
                }
            };
            proven.insert(node, holds);
        }
        ControlFlow::Continue(proven[&self.node])
    }

    /// Computes solutions using a caller-provided selector within the given projection budget.
    ///
    /// The selector receives the typevar's variance and explicit lower and upper bounds. Its
    /// outcome distinguishes missing evidence, invalid paths, and exhausted solution budgets.
    /// The caller is responsible for combining the resulting paths (typically via union).
    ///
    /// Per-variable or hidden-witness type-budget exhaustion marks the path family as
    /// [`SolutionPaths::Incomplete`](super::SolutionPaths::Incomplete). Paths with a scoped
    /// witness discard bindings that could not be validated; other paths retain fallback
    /// bindings. Exhausting the traversal, path, or exported-type budget returns an error.
    pub(crate) fn solutions_with(
        self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        inferable: TypeVarSet<'db>,
        budget: SolutionBudget,
        choose: impl FnMut(TypeVarVariance, &CandidateTypeVarSolution<'db>) -> PathBoundSolution<'db>,
    ) -> Result<Solutions<'db>, ProjectionError> {
        let (path_bounds, mut limits) = self.bounded_path_bounds(db, env, inferable, budget)?;
        let mut type_budget = ProjectionTypeBudget::new(budget.type_terms);
        match path_bounds.try_solve_with(
            db,
            env,
            &mut limits,
            &mut type_budget,
            choose,
            |solution, type_budget| {
                let mut charge = || {
                    for violation in solution.violations() {
                        for evidence in violation.evidence_types() {
                            type_budget.charge_type(db, *evidence)?;
                        }
                    }
                    for binding in &solution.solved_typevars {
                        type_budget.charge_type(db, binding.solution)?;
                    }
                    Ok(())
                };
                match charge() {
                    Ok(()) => ControlFlow::Continue(()),
                    Err(error) => ControlFlow::Break(error),
                }
            },
        ) {
            ControlFlow::Continue(solutions) => Ok(solutions),
            ControlFlow::Break(error) => Err(error),
        }
    }

    /// Reconstructs independent bound hints only to diagnose an already rejected full call.
    /// These choices do not establish a joint witness and are always marked incomplete.
    pub(crate) fn diagnostic_solutions(
        self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        inferable: TypeVarSet<'db>,
    ) -> Result<Solutions<'db>, ProjectionError> {
        let budget = SolutionBudget::default();
        let (candidates, mut limits) = self.bounded_path_bounds(db, env, inferable, budget)?;
        let mut type_budget = ProjectionTypeBudget::new(budget.type_terms);
        match candidates.try_collect_solutions(
            &mut type_budget,
            |inferable, candidate, _budget| {
                let selected = CandidateSolutions::select_bindings(
                    db,
                    env,
                    inferable,
                    candidate,
                    &mut limits,
                    &mut |_, bound| {
                        CandidateSolutions::preliminary_solve(db, env, self.builder, bound)
                    },
                )?;
                ControlFlow::Continue(selected.map(|(solution, _)| (solution, true)))
            },
            |solution, type_budget| {
                for binding in &solution.solved_typevars {
                    if let Err(error) = type_budget.charge_type(db, binding.solution) {
                        return ControlFlow::Break(error);
                    }
                }
                ControlFlow::Continue(())
            },
        ) {
            ControlFlow::Continue(solutions) => Ok(solutions),
            ControlFlow::Break(error) => Err(error),
        }
    }

    /// Folds complete, correlated solutions without first allocating every solved path.
    ///
    /// Raw paths are collected within the traversal limits and sorted in the same source order
    /// as [`Self::solutions_with`]. The storage borrow is released before invoking either
    /// callback, so they can safely use the constraint builder. Each call to `fold` receives the
    /// complete bindings for one retained path, including an empty slice for a valid path on
    /// which no variable was solved.
    ///
    /// The accumulator is returned only if the entire projection succeeds. `fold` must charge
    /// newly accumulated types to its supplied budget and use bounded constructors for operations
    /// that can expand them. It should combine alternatives commutatively when their order is not
    /// meaningful to its consumer. Existing limitations in solution extraction still apply; this
    /// API does not make an order-sensitive selector or fold order-independent.
    #[expect(clippy::too_many_arguments)]
    pub(crate) fn try_fold_solutions<T>(
        self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        inferable: TypeVarSet<'db>,
        budget: SolutionBudget,
        choose: impl FnMut(TypeVarVariance, &CandidateTypeVarSolution<'db>) -> PathBoundSolution<'db>,
        initial: T,
        fold: impl FnMut(
            T,
            &[TypeVarSolution<'db>],
            &mut ProjectionTypeBudget,
        ) -> Result<T, ProjectionError>,
    ) -> Result<SolutionProjection<T>, ProjectionError> {
        let (path_bounds, mut limits) = self.bounded_path_bounds(db, env, inferable, budget)?;

        path_bounds.try_fold_with(
            db,
            env,
            &mut limits,
            choose,
            initial,
            &mut ProjectionTypeBudget::new(budget.type_terms),
            fold,
        )
    }
}

impl<'db> CandidateSolutions<'db> {
    #[expect(clippy::too_many_arguments)]
    fn try_fold_with<T>(
        &self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        limits: &mut BoundedSolutionLimits,
        mut choose: impl FnMut(
            TypeVarVariance,
            &CandidateTypeVarSolution<'db>,
        ) -> PathBoundSolution<'db>,
        mut accumulated: T,
        budget: &mut ProjectionTypeBudget,
        mut fold: impl FnMut(
            T,
            &[TypeVarSolution<'db>],
            &mut ProjectionTypeBudget,
        ) -> Result<T, ProjectionError>,
    ) -> Result<SolutionProjection<T>, ProjectionError> {
        let (inferable, candidates) = match self {
            Self::Unsatisfiable => return Ok(SolutionProjection::Unsatisfiable),
            Self::Unconstrained => return Ok(SolutionProjection::Unconstrained),
            Self::Constrained {
                inferable,
                paths,
                incomplete,
            } => {
                if *incomplete {
                    return Err(ProjectionError::IncompleteSolution);
                }
                (*inferable, paths)
            }
        };

        let mut retained = false;
        for candidate in candidates {
            let Some((solution, incomplete)) = (match Self::solve_path_with(
                db,
                env,
                inferable,
                candidate,
                limits,
                budget,
                &mut choose,
            ) {
                ControlFlow::Continue(solution) => solution,
                ControlFlow::Break(error) => return Err(error),
            }) else {
                continue;
            };
            if !solution.is_valid() {
                continue;
            }
            if incomplete {
                return Err(ProjectionError::IncompleteSolution);
            }
            accumulated = fold(accumulated, &solution.solved_typevars, budget)?;
            retained = true;
        }

        Ok(if retained {
            SolutionProjection::Constrained(accumulated)
        } else {
            SolutionProjection::Unsatisfiable
        })
    }
}

#[cfg(test)]
mod tests;
