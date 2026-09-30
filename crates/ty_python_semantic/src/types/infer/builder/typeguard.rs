use ruff_python_ast as ast;
use ty_python_core::place::PlaceExpr;
use ty_python_core::place_table;
use ty_python_core::scope::ScopeId;

use crate::types::Type;
use crate::types::call::{Binding, Bindings};
use crate::types::narrow::NarrowingConstraint;
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
        let matched_narrowed_argument_index = bindings.single_element().and_then(|binding| {
            let has_implicit_receiver = binding
                .signature_type
                .as_function_literal()
                .or_else(|| binding.callable_type.as_function_literal())
                .is_some_and(|function| function.has_implicit_receiver(db));
            let bound_argument_offset = usize::from(binding.bound_type.is_some());
            let narrowed_parameter_index =
                usize::from(bound_argument_offset > 0 || has_implicit_receiver);
            let narrowed_argument_index = |overload: &Binding<'db>| {
                overload
                    .argument_matches()
                    .iter()
                    .enumerate()
                    .skip(bound_argument_offset)
                    .find_map(|(argument_index, matched_argument)| {
                        matched_argument
                            .parameters
                            .iter()
                            .any(|parameter| parameter.index == narrowed_parameter_index)
                            .then_some(argument_index - bound_argument_offset)
                    })
            };
            let mut matching_overloads = binding.matching_overloads();
            let (_, first_overload) = matching_overloads.next()?;
            let first_argument_index = narrowed_argument_index(first_overload);

            Some(
                if matching_overloads
                    .all(|(_, overload)| narrowed_argument_index(overload) == first_argument_index)
                {
                    first_argument_index
                } else {
                    None
                },
            )
        });

        let argument = match matched_narrowed_argument_index {
            Some(Some(argument_index)) => arguments.iter_source_order().nth(argument_index),
            // The target parameter was omitted, so there is no expression to narrow.
            Some(None) => None,
            // Preserve positional behavior when there isn't a unique callable binding whose
            // parameter mapping we can use.
            None => arguments
                .args
                .get(narrowed_argument_index())
                .map(ast::ArgOrKeyword::from),
        }?;
        if argument.is_variadic() {
            return None;
        }

        Some((
            argument.value(),
            matches!(matched_narrowed_argument_index, Some(Some(_))),
        ))
    };
    let find_narrowed_place = |argument: &ast::Expr| {
        let place_expr = PlaceExpr::try_from_expr(argument)?;
        place_table(db, scope).place_id(&place_expr)
    };

    match return_ty {
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
            // Materialized guards and non-completing arguments do not denote an ordinary
            // false result. Classify only the argument selected by the call binding.
            if has_parameter_mapping
                && has_type_is_return
                && !type_is.is_bound(db)
                && type_is.materialization_kind(db).is_none()
                && let Some(actual) = expression_type(argument)
                && !actual.has_indeterminate_inference(db, env)
                && !target.has_indeterminate_inference(db, env)
                && !actual.is_equivalent_to(db, env, Type::Never)
            {
                let positive = NarrowingConstraint::type_test(
                    db,
                    env,
                    target,
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
