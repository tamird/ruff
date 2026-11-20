use ruff_python_ast as ast;
use ty_python_core::place::PlaceExpr;
use ty_python_core::place_table;
use ty_python_core::scope::ScopeId;

use crate::types::call::Bindings;
use crate::types::call::bind::TypeGuardArgument;
use crate::types::narrow::NarrowingConstraint;
use crate::types::{IntersectionBuilder, MaterializationKind, Type};
use crate::{Db, ProgramEnvironment};

pub(super) fn bind_type_guard_return_type<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    scope: ScopeId<'db>,
    return_ty: Type<'db>,
    bindings: &Bindings<'db>,
    arguments: &ast::Arguments,
    expression_type: impl FnOnce(&ast::Expr) -> Option<Type<'db>>,
) -> Type<'db> {
    let narrowed_argument_index = || {
        bindings
            .single_element()
            .and_then(|binding| {
                binding
                    .signature_type
                    .as_function_literal()
                    .or_else(|| binding.callable_type.as_function_literal())
                    .map(|function| {
                        usize::from(
                            function.has_implicit_receiver(db) && binding.bound_type.is_none(),
                        )
                    })
            })
            .unwrap_or(0)
    };

    let find_narrowed_argument = || {
        // Use the call binding to find the argument that maps to the first parameter a type
        // guard can narrow. This supports keyword arguments without falling back to a later
        // parameter when the target is defaulted.
        let matched_narrowed_argument_index = bindings
            .single_element()
            .map_or(TypeGuardArgument::Unmapped, |binding| {
                binding.type_guard_argument_index(db)
            });

        let argument = match matched_narrowed_argument_index {
            TypeGuardArgument::Index(argument_index) => {
                arguments.iter_source_order().nth(argument_index)
            }
            // The target parameter was omitted, so there is no expression to narrow.
            TypeGuardArgument::NoTarget => None,
            // Preserve positional behavior when there isn't a unique callable binding whose
            // parameter mapping we can use.
            TypeGuardArgument::Unmapped => arguments
                .args
                .get(narrowed_argument_index())
                .map(ast::ArgOrKeyword::from),
        };
        let argument = argument?;
        if argument.is_variadic() {
            return None;
        }

        Some((
            argument.value(),
            matches!(matched_narrowed_argument_index, TypeGuardArgument::Index(_)),
        ))
    };
    let find_narrowed_place = |argument: &ast::Expr| {
        let place_expr = PlaceExpr::try_from_expr(argument)?;
        place_table(db, scope).place_id(&place_expr)
    };

    match return_ty {
        Type::Intersection(intersection) => {
            let Some(guard) = intersection.positive(db).iter().find_map(|ty| match ty {
                Type::TypeIs(guard) => (!guard.is_bound(db)).then_some(*guard),
                _ => None,
            }) else {
                return return_ty;
            };
            if bindings
                .single_element()
                .and_then(|binding| binding.common_type_is_return(db, env))
                != Some(Type::TypeIs(guard))
            {
                return return_ty;
            }
            let bound = bind_type_guard_return_type(
                db,
                env,
                scope,
                Type::TypeIs(guard),
                bindings,
                arguments,
                expression_type,
            );
            let mut result = IntersectionBuilder::new(db, env);
            for positive in intersection.positive(db) {
                result.add_positive_in_place(if *positive == Type::TypeIs(guard) {
                    bound
                } else {
                    *positive
                });
            }
            for negative in intersection.negative(db) {
                result.add_negative_in_place(*negative);
            }
            result.build()
        }
        Type::TypeIs(type_is) => {
            let Some((argument, has_parameter_mapping)) = find_narrowed_argument() else {
                return return_ty;
            };
            // A generic identity function can forward a TypeIs result without testing its
            // own argument. Only a predicate's declared return establishes that relationship.
            let has_type_is_return = bindings.single_element().is_some_and(|binding| {
                binding.matching_overloads().all(|(_, overload)| {
                    match overload.signature.return_type() {
                        Type::TypeIs(annotation) => !annotation.is_bound(db),
                        _ => false,
                    }
                })
            });
            let target = type_is.return_type(db);
            // Bottom-materialized guards can exclude both outcomes, so an empty positive
            // domain does not establish false. Non-completing arguments also remain unchanged.
            if has_parameter_mapping
                && has_type_is_return
                && !type_is.is_bound(db)
                && type_is.materialization_kind(db) != Some(MaterializationKind::Bottom)
                && let Some(actual) = expression_type(argument)
                && !actual.has_indeterminate_inference(db, env)
                && !target.has_indeterminate_inference(db, env)
                && !actual.is_equivalent_to(db, env, Type::Never)
            {
                let positive_target = match type_is.materialization_kind(db) {
                    Some(kind) => target.materialization(db, env, kind),
                    None => target,
                };
                let positive = NarrowingConstraint::type_test(
                    db,
                    env,
                    positive_target,
                    true,
                    db.analysis_settings(scope.file(db))
                        .strict_generic_narrowing,
                );
                let narrowed = NarrowingConstraint::intersection(actual)
                    .merge_constraint_and(positive)
                    .evaluate_constraint_type(db, env);
                if narrowed.is_never() {
                    return Type::bool_literal(false);
                }
            }
            match find_narrowed_place(argument) {
                Some(place) => type_is.bind(db, scope, place),
                None => return_ty,
            }
        }
        Type::TypeGuard(type_guard) => {
            match find_narrowed_argument().and_then(|(argument, _)| find_narrowed_place(argument)) {
                Some(place) => type_guard.bind(db, scope, place),
                None => return_ty,
            }
        }
        _ => return_ty,
    }
}
