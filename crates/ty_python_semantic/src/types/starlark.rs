//! Types for declarations attested by a Starlark host.

use ruff_db::diagnostic::Span;
use ruff_python_ast::name::Name;
use ty_python_core::starlark::{
    StarlarkEnvironment, StarlarkGlobalDeclaration, StarlarkGlobalKind, StarlarkParameter,
    StarlarkParameterMode, StarlarkType,
};
use ty_python_core::{Program, ProgramFile};

use crate::{Db, ProgramEnvironment};

use super::{
    ApplyTypeMappingVisitor, CallableType, KnownClass, KnownInstanceType, Parameter, Parameters,
    Signature, SubclassOfType, Type, TypeContext, TypeMapping,
};

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
            StarlarkGlobalKind::Record => Signature::new(
                Parameters::standard([Parameter::keyword_variadic(Name::new("fields"))
                    .with_annotated_type(Type::any())]),
                SubclassOfType::subclass_of_unknown(),
            ),
            StarlarkGlobalKind::RecordWithValidator => Signature::new(
                Parameters::standard([
                    Parameter::positional_only(Some(Name::new("validator")))
                        .with_annotated_type(Type::single_callable(db, Signature::unknown())),
                    Parameter::keyword_variadic(Name::new("fields"))
                        .with_annotated_type(Type::any()),
                ]),
                SubclassOfType::subclass_of_unknown(),
            ),
            StarlarkGlobalKind::Field => Signature::new(
                Parameters::standard([
                    Parameter::positional_only(Some(Name::new("type")))
                        .with_annotated_type(Type::any()),
                    Parameter::positional_or_keyword(Name::new("default"))
                        .with_annotated_type(Type::any())
                        .with_default_type(Type::unknown()),
                ]),
                Type::unknown(),
            ),
            StarlarkGlobalKind::Struct => Signature::new(
                Parameters::standard([Parameter::keyword_variadic(Name::new("fields"))
                    .with_annotated_type(Type::any())]),
                Type::unknown(),
            ),
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

/// The typed descriptor returned by the host's `field(type, default)` form.
#[salsa::interned(debug, heap_size=ruff_memory_usage::heap_size)]
pub struct StarlarkField<'db> {
    #[returns(copy)]
    pub annotation: Type<'db>,
    #[returns(copy)]
    pub default: Option<Type<'db>>,
    #[returns(ref)]
    pub origin: Span,
}

impl get_size2::GetSize for StarlarkField<'_> {}

impl<'db> StarlarkField<'db> {
    pub(super) fn recursive_type_normalized_impl(
        self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        div: Type<'db>,
        nested: bool,
    ) -> Option<Self> {
        let normalize = |ty: Type<'db>| {
            let ty = ty.recursive_type_normalized_impl(db, env, div, true);
            if nested { ty } else { Some(ty.unwrap_or(div)) }
        };
        let annotation = normalize(self.annotation(db))?;
        let default = match self.default(db) {
            Some(default) => Some(normalize(default)?),
            None => None,
        };
        Some(Self::new(db, annotation, default, self.origin(db)))
    }

    pub(super) fn apply_type_mapping_impl(
        self,
        db: &'db dyn Db,
        mapping: &TypeMapping<'_, 'db>,
        tcx: TypeContext<'db>,
        visitor: &ApplyTypeMappingVisitor<'_, 'db>,
    ) -> Self {
        Self::new(
            db,
            self.annotation(db)
                .apply_type_mapping_impl(db, mapping, tcx, visitor),
            self.default(db)
                .map(|ty| ty.apply_type_mapping_impl(db, mapping, tcx, visitor)),
            self.origin(db),
        )
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

/// Project an aggregate source annotation into Ty's existing unpacked tuple
/// parameter representation. This applies only to Starlark source functions;
/// Python declarations of host functions retain Python parameter conventions.
pub(super) fn variadic_positional_annotation<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    annotation: Type<'db>,
) -> Option<Type<'db>> {
    let annotation = annotation.resolve_type_alias(db);
    if annotation.is_dynamic() || annotation.exact_tuple_instance_spec(db).is_some() {
        Some(annotation)
    } else if annotation.is_object() {
        Some(Type::homogeneous_tuple(db, env, Type::unknown()))
    } else {
        None
    }
}

/// Project a dictionary aggregate into the value type consumed by ordinary
/// keyword binding. Correlated unions of dictionaries cannot be projected this
/// way: independently accepting either value type would lose the correlation.
pub(super) fn variadic_keyword_annotation<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    annotation: Type<'db>,
) -> Option<Type<'db>> {
    let annotation = annotation.resolve_type_alias(db);
    if annotation.is_dynamic() {
        return Some(annotation);
    }
    if annotation.is_object() {
        return Some(Type::unknown());
    }
    let specialization = annotation.known_specialization(db, env, KnownClass::Dict)?;
    let [key, value] = specialization.types(db) else {
        return None;
    };
    KnownClass::Str
        .to_instance(db, env)
        .is_assignable_to(db, env, *key)
        .then_some(*value)
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
