use ruff_python_ast as ast;
use ty_python_core::place::PlaceExpr;
use ty_python_core::place_table;
use ty_python_core::scope::ScopeId;

use crate::Db;
use crate::types::Type;
use crate::types::call::Bindings;
use crate::types::call::bind::TypeGuardArgument;

pub(super) fn bind_type_guard_return_type<'db>(
    db: &'db dyn Db,
    scope: ScopeId<'db>,
    return_ty: Type<'db>,
    bindings: &Bindings<'db>,
    arguments: &ast::Arguments,
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

    let find_narrowed_place = || {
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
            TypeGuardArgument::NoTarget => None,
            // Preserve positional behavior when there isn't a unique callable binding whose
            // parameter mapping we can use.
            TypeGuardArgument::Unmapped => arguments
                .args
                .get(narrowed_argument_index())
                .map(ast::ArgOrKeyword::from),
        }?;
        if argument.is_variadic() {
            return None;
        }

        let place_expr = PlaceExpr::try_from_expr(argument.value())?;
        place_table(db, scope).place_id(&place_expr)
    };

    match return_ty {
        Type::TypeIs(type_is) => match find_narrowed_place() {
            Some(place) => type_is.bind(db, scope, place),
            None => return_ty,
        },
        Type::TypeGuard(type_guard) => match find_narrowed_place() {
            Some(place) => type_guard.bind(db, scope, place),
            None => return_ty,
        },
        _ => return_ty,
    }
}
