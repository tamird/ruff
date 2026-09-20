//! Declarations and annotations supplied by applications embedding the semantic database.
//!
//! Applications resolve their own module names and native APIs. Source exports retain their
//! program-file identity so type inference and navigation use the same ordinary definitions.

use ruff_db::diagnostic::Diagnostic;
use ruff_python_ast::name::Name;
use ty_python_core::ProgramFile;

use crate::Db;
use crate::ProgramEnvironment;
use crate::types::class::DynamicClassLiteral;
use crate::types::{CheckedCall, ClassLiteral, Type};

mod data;
pub use data::ProvidedData;

/// Instance storage supplied by a class factory. Callable values here do not bind as methods.
#[derive(Clone, Debug, Eq, PartialEq, Hash, get_size2::GetSize, salsa::SalsaValue, Default)]
pub struct ProvidedInstanceFields<'db> {
    pub fields: Box<[(Name, Type<'db>)]>,
    pub has_dynamic_fields: bool,
    pub data: Option<ProvidedData>,
}

/// A source-created nominal class using Ty's ordinary member lookup and constructor analysis.
pub struct ProvidedClass<'db> {
    pub name: Name,
    pub bases: Box<[Type<'db>]>,
    pub class_members: Box<[(Name, Type<'db>)]>,
    pub instance_fields: ProvidedInstanceFields<'db>,
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
        let ProvidedClass {
            name,
            bases,
            class_members,
            instance_fields,
        } = class;
        DynamicClassLiteral::new(
            db,
            name,
            self.class_anchor(bases),
            class_members,
            false,
            None,
            Some(instance_fields),
        )
        .into()
    }
}

impl<'db> Type<'db> {
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
