//! Bounded projections of correlated constraint solutions.

use rustc_hash::{FxHashMap, FxHashSet};
use std::ops::ControlFlow;

use super::{
    ALWAYS_FALSE, ALWAYS_TRUE, BoundedSolutionLimits, CandidateSearch, CandidateSolutions, CandidateTypeVarSolution,
    ConstraintId, ConstraintProvenance, ConstraintSet, PathBoundSolution, ReportDiagnostics,
    SolutionLimits, Solutions, TypeVarSolution,
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

/// Work shared by collection and every witness completion for one inference request.
pub(crate) struct ProjectionBudget {
    limits: BoundedSolutionLimits,
    types: ProjectionTypeBudget,
}

impl ProjectionBudget {
    #[cfg(test)]
    pub(crate) fn remaining_visits(&self) -> usize {
        self.limits.remaining_visits
    }

    pub(crate) fn new(budget: SolutionBudget) -> Self {
        let SolutionBudget {
            paths,
            visits,
            type_terms,
        } = budget;
        Self {
            limits: BoundedSolutionLimits {
                remaining_paths: paths,
                remaining_visits: visits,
            },
            types: ProjectionTypeBudget::new(type_terms),
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
    pub(crate) fn new(remaining: usize) -> Self {
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

impl<'db> CandidateSolutions<'db> {
    pub(super) fn solve_with_limits(
        &self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        limits: &mut BoundedSolutionLimits,
        type_budget: &mut ProjectionTypeBudget,
        choose: impl FnMut(TypeVarVariance, &CandidateTypeVarSolution<'db>) -> PathBoundSolution<'db>,
    ) -> Result<Solutions<'db>, ProjectionError> {
        match self.try_solve_with(
            db,
            env,
            limits,
            type_budget,
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
}

/// The variable domain and candidate bindings for one specialization search.
pub(crate) struct SpecializationCandidates<'a, 'db> {
    pub(crate) inferable: TypeVarSet<'db>,
    pub(crate) fixed: &'a [TypeVarSolution<'db>],
    pub(crate) fallback: Vec<TypeVarSolution<'db>>,
}

impl<'db> ConstraintSet<'db, '_> {
    /// Computes default solutions for each BDD path within the default projection budget.
    /// Constraints on non-inferable typevars are not necessarily retained in the solutions.
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
            ReportDiagnostics::Yes,
            |_variance, path_bound| CandidateSolutions::default_solve(db, env, builder, path_bound),
        )
    }

    pub(super) fn bounded_path_bounds(
        self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        inferable: TypeVarSet<'db>,
        budget: SolutionBudget,
        search: CandidateSearch,
    ) -> Result<(CandidateSolutions<'db>, BoundedSolutionLimits), ProjectionError> {
        let mut limits = BoundedSolutionLimits {
            remaining_paths: budget.paths,
            remaining_visits: budget.visits,
        };
        let paths =
            self.path_bounds_with_limits(db, env, inferable, &mut limits, search)?;
        Ok((paths, limits))
    }

    fn path_bounds_with_limits(
        self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        inferable: TypeVarSet<'db>,
        limits: &mut BoundedSolutionLimits,
        search: CandidateSearch,
    ) -> Result<CandidateSolutions<'db>, ProjectionError> {
        let paths = CandidateSolutions::compute_with_limits(
            db,
            env,
            &mut self.builder.storage.borrow_mut(),
            self.node,
            inferable,
            self.source_order,
            limits,
            super::variables::UnspecializedTypeVarPolicy::Ignore,
            search,
        );
        match paths {
            ControlFlow::Continue(paths) => Ok(paths),
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
        candidates: SpecializationCandidates<'_, 'db>,
        resources: &mut ProjectionBudget,
        mut project: impl FnMut(
            &[TypeVarSolution<'db>],
            &mut ProjectionTypeBudget,
        ) -> Result<Option<Vec<TypeVarSolution<'db>>>, ProjectionError>,
    ) -> Result<Option<Vec<TypeVarSolution<'db>>>, ProjectionError> {
        let SpecializationCandidates {
            inferable,
            fixed,
            fallback,
        } = candidates;
        let ProjectionBudget {
            limits,
            types: type_budget,
        } = resources;
        // Selected caller bindings constrain discovery as well as the final proof.
        // Without these bounds, dropping a selected variable from `inferable` would
        // make its original relation rigid before its selected value was applied.
        let mut selected = self;
        for binding in fixed {
            type_budget.charge_type(db, binding.solution)?;
            match limits.visit_node() {
                ControlFlow::Continue(()) => {}
                ControlFlow::Break(error) => return Err(error),
            }
            selected.intersect(
                db,
                self.builder,
                Self::constrain_typevar_equivalence_bound(
                    db,
                    env,
                    self.builder,
                    ConstraintProvenance::INFERRED,
                    binding.bound_typevar,
                    binding.solution,
                ),
            );
        }
        let inferable = inferable.merge(
            db,
            TypeVarSet::from_typevars(db, fixed.iter().map(|binding| binding.bound_typevar)),
        );
        let path_bounds =
            selected.path_bounds_with_limits(db, env, inferable, limits, CandidateSearch::All(ReportDiagnostics::No))?;
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
                limits,
                type_budget,
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
            let Some(bindings) = project(&solution.solved_typevars, type_budget)? else {
                continue;
            };
            match verify(&bindings, limits, type_budget) {
                ControlFlow::Continue(true) => return Ok(Some(bindings)),
                ControlFlow::Continue(false) => {}
                ControlFlow::Break(error) => return Err(error),
            }
        }
        match verify(&fallback, limits, type_budget) {
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
    /// Constraints on non-inferable typevars are not necessarily retained in the solutions.
    /// The selector must preserve the typevar's declared bound: path validation does not
    /// revalidate an arbitrary type selected afterward.
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
        report_diagnostics: ReportDiagnostics,
        choose: impl FnMut(TypeVarVariance, &CandidateTypeVarSolution<'db>) -> PathBoundSolution<'db>,
    ) -> Result<Solutions<'db>, ProjectionError> {
        self.solutions_with_shared_budget(
            db,
            env,
            inferable,
            &mut ProjectionBudget::new(budget),
            report_diagnostics,
            choose,
        )
    }

    pub(crate) fn solutions_with_shared_budget(
        self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        inferable: TypeVarSet<'db>,
        resources: &mut ProjectionBudget,
        report_diagnostics: ReportDiagnostics,
        choose: impl FnMut(TypeVarVariance, &CandidateTypeVarSolution<'db>) -> PathBoundSolution<'db>,
    ) -> Result<Solutions<'db>, ProjectionError> {
        let ProjectionBudget { limits, types: type_budget } = resources;
        let path_bounds = self.path_bounds_with_limits(
            db, env, inferable, limits, CandidateSearch::All(report_diagnostics),
        )?;
        path_bounds.solve_with_limits(db, env, limits, type_budget, choose)
    }

    /// Folds complete, correlated solutions without first allocating every solved path.
    ///
    /// Raw paths are collected within the traversal limits and sorted in the same source order
    /// as [`Self::solutions_with`]. The storage borrow is released before invoking either
    /// callback, so they can safely use the constraint builder. Each call to `fold` receives the
    /// complete bindings for one retained path, including an empty slice for a valid path on
    /// which no variable was solved. As with [`Self::solutions_with`], the selector must preserve
    /// each typevar's declared bound.
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
        let (path_bounds, mut limits) =
            self.bounded_path_bounds(db, env, inferable, budget, CandidateSearch::All(ReportDiagnostics::Yes))?;

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
