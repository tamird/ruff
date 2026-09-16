//! Types for declarations attested by a Starlark host.

use ty_python_core::starlark::{
    StarlarkEnvironment, StarlarkGlobalDeclaration, StarlarkGlobalKind, StarlarkParameter,
    StarlarkParameterMode, StarlarkType,
};
use ty_python_core::{Program, ProgramFile};

use crate::{Db, ProgramEnvironment};

use super::{CallableType, KnownClass, KnownInstanceType, Parameter, Parameters, Signature, Type};

/// A host declaration retains its identity through aliases and ordinary call binding.
///
/// The program is part of the identity because the same portable declaration can
/// be checked against different builtin profiles in one database.
#[salsa::interned(debug, heap_size=ruff_memory_usage::heap_size)]
pub struct StarlarkGlobal<'db> {
    #[returns(copy)]
    pub environment: StarlarkEnvironment,
    #[returns(copy)]
    pub index: usize,
    #[returns(copy)]
    pub program: Program<'db>,
}

impl get_size2::GetSize for StarlarkGlobal<'_> {}

#[salsa::tracked]
impl<'db> StarlarkGlobal<'db> {
    pub(crate) fn declaration(self, db: &'db dyn Db) -> Option<&'db StarlarkGlobalDeclaration> {
        self.environment(db).globals(db).get(self.index(db))
    }

    pub(crate) fn lookup(db: &'db dyn Db, file: ProgramFile<'db>, name: &str) -> Option<Type<'db>> {
        let environment = file.starlark_module(db)?.environment(db)?;
        let index = environment
            .globals(db)
            .iter()
            .position(|global| global.name == name)?;
        Some(Type::KnownInstance(KnownInstanceType::StarlarkGlobal(
            Self::new(db, environment, index, file.program(db)),
        )))
    }

    #[salsa::tracked(returns(copy))]
    pub(crate) fn callable(self, db: &'db dyn Db) -> CallableType<'db> {
        let env = ProgramEnvironment::from_program(self.program(db));
        let Some(declaration) = self.declaration(db) else {
            return CallableType::single(db, Signature::unknown());
        };
        let StarlarkGlobalDeclaration { name: _, kind } = declaration;
        let signature = match kind {
            StarlarkGlobalKind::Native {
                parameters,
                return_type,
                availability: _,
            } => {
                let parameters = parameters
                    .iter()
                    .map(|parameter| {
                        let StarlarkParameter {
                            name,
                            mode,
                            ty,
                            required,
                        } = parameter;
                        let parameter = match mode {
                            StarlarkParameterMode::PositionalOnly => {
                                Parameter::positional_only(Some(name.clone()))
                            }
                            StarlarkParameterMode::PositionalOrKeyword => {
                                Parameter::positional_or_keyword(name.clone())
                            }
                            StarlarkParameterMode::KeywordOnly => {
                                Parameter::keyword_only(name.clone())
                            }
                        }
                        .with_annotated_type(resolve_type(db, &env, *ty));
                        if *required {
                            parameter
                        } else {
                            // The host attests presence, not the value of the default.
                            parameter.with_default_type(Type::unknown())
                        }
                    })
                    .collect::<Vec<_>>();
                Signature::new(
                    Parameters::standard(parameters),
                    resolve_type(db, &env, *return_type),
                )
            }
        };
        CallableType::single(db, signature)
    }
}

fn resolve_type<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    ty: StarlarkType,
) -> Type<'db> {
    match ty {
        StarlarkType::Any => Type::any(),
        StarlarkType::Bool => KnownClass::Bool.to_instance(db, env),
        StarlarkType::Int => KnownClass::Int.to_instance(db, env),
        StarlarkType::Str => KnownClass::Str.to_instance(db, env),
        StarlarkType::Callable => Type::single_callable(db, Signature::unknown()),
        StarlarkType::Unknown => Type::unknown(),
    }
}

#[cfg(test)]
mod tests {
    use ruff_python_ast::name::Name;
    use ty_python_core::TestProgramDb;
    use ty_python_core::starlark::StarlarkAvailability;

    use super::*;
    use crate::db::tests::TestDbBuilder;
    use crate::types::UnionType;

    #[test]
    fn declaration_identity_preserves_capabilities_without_runtime_identity() -> anyhow::Result<()>
    {
        let db = TestDbBuilder::new().build()?;
        let environment = StarlarkEnvironment::new(
            &db,
            ["first", "second"]
                .map(|name| StarlarkGlobalDeclaration {
                    name: Name::new(name),
                    kind: StarlarkGlobalKind::Native {
                        parameters: Box::default(),
                        return_type: StarlarkType::Str,
                        availability: StarlarkAvailability::AnyModule,
                    },
                })
                .into(),
        );
        let env = ProgramEnvironment::from_program(db.program());
        let first = Type::KnownInstance(KnownInstanceType::StarlarkGlobal(StarlarkGlobal::new(
            &db,
            environment,
            0,
            db.program(),
        )));
        let second = Type::KnownInstance(KnownInstanceType::StarlarkGlobal(StarlarkGlobal::new(
            &db,
            environment,
            1,
            db.program(),
        )));
        assert!(!first.is_disjoint_from(&db, &env, second));
        assert!(!first.is_subtype_of(&db, &env, second));
        assert!(!second.is_subtype_of(&db, &env, first));
        let union = UnionType::from_two_elements(&db, &env, first, second);
        let Type::Union(union) = union else {
            anyhow::bail!("distinct native origins were collapsed: {union:?}")
        };
        assert_eq!(union.elements(&db).len(), 2);
        let str_type = KnownClass::Str.to_instance(&db, &env);
        assert_eq!(first.str(&db, &env), str_type);
        assert_eq!(first.repr(&db, &env), str_type);
        assert!(!first.is_assignable_to(&db, &env, KnownClass::Int.to_instance(&db, &env)));
        Ok(())
    }
}
