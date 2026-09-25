//! Declarations and annotations supplied by applications embedding the semantic database.
//!
//! Applications resolve their own module names and native APIs. Source exports retain their
//! program-file identity so type inference and navigation use the same ordinary definitions.

use ruff_db::diagnostic::Diagnostic;
use ruff_db::files::FileRange;
use ruff_python_ast::name::Name;
use ruff_python_ast::{self as ast, HasNodeIndex, NodeIndex};
use ty_python_core::ProgramFile;
use ty_python_core::semantic_index;

use crate::Db;
use crate::ProgramEnvironment;
use crate::place::{Place, PlaceAndQualifiers};
use crate::types::CheckedCall;
use crate::types::ClassLiteral;
use crate::types::class::{DynamicClassAnchor, DynamicClassLiteral, DynamicClassScopeOffset};
use crate::types::{IntersectionBuilder, MemberLookupPolicy, Type, TypeQualifiers};

mod data;
pub use data::ProvidedData;

/// A return contract supplied by an embedding application.
#[derive(Clone, Copy, Debug)]
pub struct ProvidedReturnType<'db> {
    pub ty: Type<'db>,
    /// The contract's declaration, used in secondary diagnostic annotations.
    pub source: Option<FileRange>,
}

/// Instance storage supplied by a class factory. Callable values here do not bind as methods.
#[derive(Clone, Debug, Eq, PartialEq, Hash, get_size2::GetSize, salsa::SalsaValue, Default)]
pub struct ProvidedInstanceFields<'db> {
    pub fields: Box<[ProvidedField<'db>]>,
    pub has_dynamic_fields: bool,
    pub implications: Box<[ProvidedFieldImplication<'db>]>,
    pub data: Option<ProvidedData>,
}

/// A relation between immutable stored fields on the same supplied instance.
///
/// If the relative attribute path `guard` is truthy, `target` satisfies `ty`. Both paths
/// must be nonempty and traverse guaranteed immutable storage. A false guard supplies no
/// inverse relation. The embedding application guarantees the relation at runtime.
#[derive(Clone, Debug, Eq, PartialEq, Hash, get_size2::GetSize, salsa::SalsaValue)]
pub struct ProvidedFieldImplication<'db> {
    pub guard: Box<[Name]>,
    pub target: Box<[Name]>,
    pub ty: Type<'db>,
}

/// A stored instance field and the source declaration that defines it, when available.
#[derive(Clone, Debug, Eq, PartialEq, Hash, get_size2::GetSize, salsa::SalsaValue)]
pub struct ProvidedField<'db> {
    pub name: Name,
    pub ty: Type<'db>,
    pub source: Option<FileRange>,
}

/// A source-created nominal class using Ty's ordinary member lookup and constructor analysis.
pub struct ProvidedClass<'db> {
    pub name: Name,
    pub bases: Box<[Type<'db>]>,
    pub class_members: Box<[(Name, Type<'db>)]>,
    pub instance_fields: ProvidedInstanceFields<'db>,
}

impl<'db> ProvidedClass<'db> {
    pub(crate) fn into_type_at_call(
        self,
        db: &'db dyn Db,
        file: ProgramFile<'db>,
        call: &ast::ExprCall,
    ) -> Option<Type<'db>> {
        let index = semantic_index(db, file);
        let file_scope = index.try_expression_scope_id(&ast::ExprRef::Call(call))?;
        let scope = file_scope.to_scope_id(db, file);
        let scope_index = scope.node(db).node_index().unwrap_or(NodeIndex::from(0));
        let call_index = call.node_index().load().as_u32()?;
        let scope_index = scope_index.as_u32()?;
        let offset = call_index.checked_sub(scope_index)?;
        Some(
            self.into_type(db, |explicit_bases| DynamicClassAnchor::ScopeOffset {
                scope,
                offset: DynamicClassScopeOffset::Node(offset),
                explicit_bases,
            }),
        )
    }

    fn into_type(
        self,
        db: &'db dyn Db,
        anchor: impl FnOnce(Box<[Type<'db>]>) -> DynamicClassAnchor<'db>,
    ) -> Type<'db> {
        let Self {
            name,
            bases,
            class_members,
            instance_fields,
        } = self;
        DynamicClassLiteral::new(
            db,
            name,
            anchor(bases),
            class_members,
            false,
            None,
            Some(instance_fields),
        )
        .into()
    }
}

/// The namespace in which a builtin name is being used.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum BuiltinUsage {
    Runtime,
    Annotation,
}

/// The source of an application-supplied binding or builtin.
#[derive(Clone, Debug)]
pub enum ProvidedBindingValue<'db> {
    /// A native declaration without an implementation in a source file.
    Value(Type<'db>),
    /// The public value of a source symbol at the end of its module.
    Export { file: ProgramFile<'db>, name: Name },
    /// The name is unavailable. For builtin lookup, this suppresses Python builtin fallback.
    Unresolved,
}

impl<'db> ProvidedBindingValue<'db> {
    /// Resolves the supplied declaration through the same export lookup used by inference.
    pub fn resolve_type(self, db: &'db dyn Db) -> Option<Type<'db>> {
        crate::place::provided_binding_value(db, self)
            .place
            .ignore_possibly_undefined()
    }
}

/// Resolution of a supplied source binding, including errors reported by its loader.
#[derive(Clone, Debug)]
pub struct ProvidedBindingResolution<'db> {
    pub value: ProvidedBindingValue<'db>,
    pub diagnostics: Vec<Diagnostic>,
}

impl<'db> From<ProvidedBindingValue<'db>> for ProvidedBindingResolution<'db> {
    fn from(value: ProvidedBindingValue<'db>) -> Self {
        Self {
            value,
            diagnostics: Vec::new(),
        }
    }
}

impl<'db> CheckedCall<'_, 'db> {
    /// Creates a class whose nominal identity is anchored to this call in the original source.
    pub fn class_type(&self, db: &'db dyn Db, class: ProvidedClass<'db>) -> Type<'db> {
        class.into_type(db, |bases| self.class_anchor(bases))
    }
}

impl<'db> Type<'db> {
    /// Apply supplied positive field relations while retaining every unproved union arm.
    pub(super) fn with_truthy_field_implications(
        self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        reversed_guard: &[&str],
    ) -> Option<Self> {
        let mut result = self;
        match self {
            Self::Union(union) => {
                result = union.map(db, env, |arm| {
                    arm.with_truthy_field_implications(db, env, reversed_guard)
                        .unwrap_or(*arm)
                });
            }
            Self::Intersection(intersection) => {
                for owner in intersection.positive(db) {
                    result =
                        result.with_nominal_field_implications(db, env, *owner, reversed_guard);
                }
            }
            Self::NominalInstance(_) => {
                result = self.with_nominal_field_implications(db, env, self, reversed_guard);
            }
            _ => {}
        }
        (result != self).then_some(result)
    }

    fn with_nominal_field_implications(
        self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        owner: Self,
        reversed_guard: &[&str],
    ) -> Self {
        let Self::NominalInstance(instance) = owner else {
            return self;
        };
        let ClassLiteral::Dynamic(class) = instance.class_literal(db, env) else {
            return self;
        };
        let Some(ProvidedInstanceFields {
            fields: _,
            has_dynamic_fields: _,
            implications,
            data: _,
        }) = class.instance_fields(db)
        else {
            return self;
        };
        let mut result = self;
        for ProvidedFieldImplication { guard, target, ty } in implications {
            if !guard
                .iter()
                .rev()
                .map(Name::as_str)
                .eq(reversed_guard.iter().copied())
                || !owner.has_immutable_field_path(db, env, guard)
                || !owner.has_immutable_field_path(db, env, target)
            {
                continue;
            }
            // A completed query can retain unresolved cycle markers in its restriction.
            // Recursively expanding aliases also lack the finite proof used here.
            if crate::types::visitor::any_over_type_expanding_aliases(db, env, *ty, |nested| {
                matches!(nested, Self::Divergent(_))
            }) {
                continue;
            }
            let mut restriction = *ty;
            for name in target.iter().rev() {
                restriction =
                    Self::protocol_with_readonly_members(db, env, [(name.as_str(), restriction)]);
            }
            result = IntersectionBuilder::new(db, env)
                .positive_elements([result, restriction])
                .build();
        }
        result
    }

    pub(super) fn has_immutable_field_path(
        self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        path: &[Name],
    ) -> bool {
        if path.is_empty() {
            return false;
        }
        let mut receiver = self;
        for name in path {
            receiver = receiver.resolve_type_alias(db);
            // Qualifiers on joined alternatives do not prove storage for every alternative.
            if !receiver.is_nominal_instance() {
                return false;
            }
            let PlaceAndQualifiers { place, qualifiers } = receiver.instance_member(db, env, name);
            let Place::Defined(storage) = place else {
                return false;
            };
            if !storage.is_definitely_defined()
                || !qualifiers
                    .contains(TypeQualifiers::FINAL | TypeQualifiers::GUARANTEED_INSTANCE_STORAGE)
            {
                return false;
            }
            // The storage flag is consumed by descriptor lookup. Validate its precedence here,
            // using the same class-side lookup and descriptor classifier as ordinary access.
            if let Some(class_member) = receiver
                .class_member(db, env, name)
                .place
                .ignore_possibly_undefined()
                && !class_member.is_definitely_non_data_descriptor(db, env)
            {
                return false;
            }
            let policy = MemberLookupPolicy::MRO_NO_OBJECT_FALLBACK
                | MemberLookupPolicy::META_CLASS_NO_TYPE_FALLBACK;
            if !receiver
                .class_member_with_policy(db, env, "__getattribute__", policy)
                .place
                .is_undefined()
            {
                return false;
            }
            receiver = storage.ty;
        }
        true
    }

    /// Attaches immutable application data to a synthesized callable.
    /// Returns `None` for types that are not represented by callable signatures.
    ///
    /// This metadata does not participate in callable relations. Union simplification may
    /// discard distinct metadata on otherwise equivalent signatures. Use it for presentation,
    /// not for factory identity or other semantic distinctions.
    pub fn with_callable_data(self, db: &'db dyn Db, data: ProvidedData) -> Option<Self> {
        let Self::Callable(callable) = self else {
            return None;
        };
        Some(Self::Callable(callable.with_provided_data(db, data)))
    }

    /// Returns immutable application data attached to a synthesized callable, instance, or class.
    pub fn provided_data(
        self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
    ) -> Option<&'db ProvidedData> {
        let class = match self {
            Self::Callable(callable) => return callable.provided_data(db).as_ref(),
            Self::ClassLiteral(class) => class,
            Self::NominalInstance(instance) => instance.class_literal(db, env),
            _ => return None,
        };
        let ClassLiteral::Dynamic(class) = class else {
            return None;
        };
        class.instance_fields(db).as_ref()?.data.as_ref()
    }
}

#[cfg(test)]
mod source_tests;
#[cfg(test)]
mod tests;
