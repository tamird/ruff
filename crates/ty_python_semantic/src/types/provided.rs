//! Declarations and annotations supplied by applications embedding the semantic database.
//!
//! Applications resolve their own module names and native APIs. Source exports retain their
//! program-file identity so type inference and navigation use the same ordinary definitions.

use itertools::Either;
use ruff_db::diagnostic::Diagnostic;
use ruff_db::files::FileRange;
use ruff_db::parsed::parsed_module;
use ruff_python_ast::name::Name;
use ruff_python_ast::{self as ast, HasNodeIndex, NodeIndex};
use ruff_text_size::TextRange;
use ty_python_core::ProgramFile;
use ty_python_core::definition::{Definition, DefinitionKind};
use ty_python_core::scope::ScopeId;
use ty_python_core::semantic_index;

use crate::Db;
use crate::ProgramEnvironment;
use crate::place::{Place, PlaceAndQualifiers};
use crate::types::CheckedCall;
use crate::types::ClassLiteral;
use crate::types::class::{DynamicClassAnchor, DynamicClassLiteral, DynamicClassScopeOffset};
use crate::types::{
    ClassType, IntersectionBuilder, KnownClass, MemberLookupPolicy, Signature, Type, TypeQualifiers,
};

impl KnownClass {
    pub(crate) fn allocation_class<'db>(
        self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
    ) -> Option<ClassLiteral<'db>> {
        self.provided_allocation_class(db, env)
            .or_else(|| self.try_to_class_literal(db, env).map(ClassLiteral::Static))
    }

    /// Returns the checked allocation declaration supplied for this builtin collection.
    /// Its sole base preserves the builtin's generic parameters and operations.
    pub fn provided_allocation_class<'db>(
        self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
    ) -> Option<ClassLiteral<'db>> {
        if !matches!(self, Self::Dict | Self::List | Self::Set) {
            return None;
        }
        let builtin = self.try_to_class_literal(db, env)?;
        let declaration = db.provided_allocation_class(env.program(db), self)?;
        let Type::ClassLiteral(allocation) = declaration.resolve_type(db)? else {
            return None;
        };
        checked_allocation_class(db, builtin.into(), allocation)
    }
}

impl<'db> ClassType<'db> {
    pub(crate) fn provided_allocation(
        self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
    ) -> Option<Self> {
        let known = self.known(db)?;
        let allocation = known.provided_allocation_class(db, env)?;
        Some(match self {
            Self::NonGeneric(_) => Self::NonGeneric(allocation),
            Self::Generic(alias) => {
                let specialization = alias.specialization(db);
                allocation.apply_specialization(db, |context| {
                    context
                        .specialize_recursive(
                            db,
                            specialization.types(db).iter().copied().map(Some),
                        )
                        .with_materialization_kind(db, specialization.materialization_kind(db))
                })
            }
        })
    }
}

#[salsa::tracked(returns(copy))]
fn checked_allocation_class<'db>(
    db: &'db dyn Db,
    builtin: ClassLiteral<'db>,
    allocation: ClassLiteral<'db>,
) -> Option<ClassLiteral<'db>> {
    let class = allocation.as_static()?;
    if !class.is_final(db) || class.has_explicit_metaclass(db) {
        return None;
    }
    let env = ProgramEnvironment::from_scope(class.body_scope(db));
    let context = allocation.generic_context(db)?;
    let builtin_context = builtin.generic_context(db)?;
    if context.variables(db).any(|variable| {
        variable.is_paramspec(db)
            || variable.default_type(db).is_some()
            || variable
                .typevar(db)
                .bound_or_constraints(db, &env)
                .is_some()
    }) {
        return None;
    }
    if context
        .variables(db)
        .zip(builtin_context.variables(db))
        .any(|(allocation, original)| allocation.variance(db) != original.variance(db))
    {
        return None;
    }
    let [Type::GenericAlias(base)] = class.explicit_bases(db) else {
        return None;
    };
    if ClassLiteral::Static(base.origin(db)) != builtin
        || !base
            .specialization(db)
            .types(db)
            .iter()
            .copied()
            .eq(context.variables(db).map(Type::TypeVar))
    {
        return None;
    }
    let module = parsed_module(db, class.program_file(db).python_file(db)).load(db);
    let declaration = class.body_scope(db).node(db).expect_class().node(&module);
    if declaration.decorator_list.len() != 1
        || !declaration.body.iter().all(|statement| match statement {
            ast::Stmt::Pass(_) => true,
            ast::Stmt::Expr(expression) => matches!(
                expression.value.as_ref(),
                ast::Expr::EllipsisLiteral(_) | ast::Expr::StringLiteral(_)
            ),
            _ => false,
        })
    {
        return None;
    }
    Some(allocation)
}

mod data;
pub use data::ProvidedData;

/// Instance storage supplied by a class factory. Callable values here do not bind as methods.
#[derive(Clone, Debug, Eq, PartialEq, Hash, get_size2::GetSize, salsa::SalsaValue, Default)]
pub struct ProvidedInstanceFields<'db> {
    pub fields: Box<[ProvidedField<'db>]>,
    pub has_dynamic_fields: bool,
    pub implications: Box<[ProvidedFieldImplication<'db>]>,
    pub data: Option<ProvidedData>,
}

/// Immutable fields supplied eagerly or resolved from a source declaration on demand.
///
/// Deferred metadata contains no inferred types, so a nominal class can be created before
/// its fields refer back to that class or another recursively declared class.
#[derive(Clone, Debug, Eq, PartialEq, Hash, get_size2::GetSize, salsa::SalsaValue)]
pub enum ProvidedInstanceFieldsSource<'db> {
    Eager(ProvidedInstanceFields<'db>),
    Deferred(ProvidedData),
}

impl<'db> From<ProvidedInstanceFields<'db>> for ProvidedInstanceFieldsSource<'db> {
    fn from(fields: ProvidedInstanceFields<'db>) -> Self {
        Self::Eager(fields)
    }
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
    pub instance_fields: ProvidedInstanceFieldsSource<'db>,
}

impl<'db> ProvidedClass<'db> {
    pub(crate) fn into_type_at_call(
        self,
        db: &'db dyn Db,
        file: ProgramFile<'db>,
        call: &ast::ExprCall,
    ) -> Option<Type<'db>> {
        self.into_type_at_expression(db, file, ast::ExprRef::Call(call))
    }

    /// Creates a nominal class anchored to an expression from `file`'s canonical AST.
    /// Returns `None` when the expression has no indexed scope.
    pub fn into_type_at_expression(
        self,
        db: &'db dyn Db,
        file: ProgramFile<'db>,
        expression: ast::ExprRef<'_>,
    ) -> Option<Type<'db>> {
        let index = semantic_index(db, file);
        let file_scope = index.try_expression_scope_id(&expression)?;
        let scope = file_scope.to_scope_id(db, file);
        self.into_type_at_scope_node(db, scope, expression.node_index().load())
    }

    /// Creates a nominal class anchored to a source function or class declaration.
    /// Returns `None` for other definition kinds.
    pub fn into_type_at_definition(
        self,
        db: &'db dyn Db,
        definition: Definition<'db>,
    ) -> Option<Type<'db>> {
        let node = provided_class_definition_node(db, definition)?;
        self.into_type_at_scope_node(db, definition.scope(db), node)
    }

    fn into_type_at_scope_node(
        self,
        db: &'db dyn Db,
        scope: ScopeId<'db>,
        node: NodeIndex,
    ) -> Option<Type<'db>> {
        let scope_index = scope.node(db).node_index().unwrap_or(NodeIndex::from(0));
        let node_index = node.as_u32()?;
        let scope_index = scope_index.as_u32()?;
        let offset = node_index.checked_sub(scope_index)?;
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

#[salsa::tracked(returns(copy))]
fn provided_class_definition_node<'db>(
    db: &'db dyn Db,
    definition: Definition<'db>,
) -> Option<NodeIndex> {
    match definition.kind(db) {
        DefinitionKind::Function(function) => {
            let module = parsed_module(db, definition.program_file(db).python_file(db)).load(db);
            Some(function.node(&module).node_index().load())
        }
        DefinitionKind::Class(class) => Some(class.index()),
        _ => None,
    }
}

/// The namespace in which a builtin name is being used.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum BuiltinUsage {
    Runtime,
    Annotation,
}

/// A resolved type application in the current annotation inference pass.
pub struct ProvidedTypeApplication<'a, 'db> {
    pub expression: &'a ast::ExprSubscript,
    pub value_type: Type<'db>,
    pub definition: Option<Definition<'db>>,
}

/// The expected values returned by an unannotated callback body and their declaration source.
#[derive(Clone, Copy, Debug)]
pub struct ProvidedReturnType<'db> {
    pub ty: Type<'db>,
    pub source: FileRange,
}

/// Whether a supplied getter can provide a particular attribute on its receiver.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum ProvidedGetattrPresence {
    #[default]
    Present,
    PossiblyMissing,
    Absent,
}

/// Presence, value, and storage facts for a supplied getter's attribute.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct ProvidedGetattrResult<'db> {
    pub presence: ProvidedGetattrPresence,
    /// Replaces the checked getter result when the attribute can be present.
    /// `None` preserves ordinary return inference; absent attributes have no value.
    pub return_type: Option<Type<'db>>,
    /// The attribute is always present in immutable instance storage. Reading it cannot
    /// raise `AttributeError` or return a different value on a subsequent access.
    ///
    /// This is stronger than a readonly property or a getter's return annotation. It is
    /// honored only when every viable binding of a valid call supplies a `Present` result
    /// with this guarantee. Ordinary members shadowing the getter, and custom
    /// `__getattribute__` methods intercepting the access, still take precedence.
    pub immutable_storage: bool,
}

impl From<ProvidedGetattrPresence> for ProvidedGetattrResult<'_> {
    fn from(presence: ProvidedGetattrPresence) -> Self {
        Self {
            presence,
            return_type: None,
            immutable_storage: false,
        }
    }
}

/// Ordinary inference of children of an application-defined type expression.
///
/// Child expressions must belong to the supplied application. Inference preserves the
/// current lexical scope, type parameters, deferred annotation state, and IDE expression types.
pub trait TypeExpressionContext<'db> {
    fn program_file(&self) -> ProgramFile<'db>;

    /// Infers a child as a runtime value rather than a type expression.
    fn infer_value_expression(&mut self, expression: &ast::Expr) -> Type<'db>;

    /// Infers a type expression, rejecting declaration qualifiers such as `Final`.
    fn infer_type_expression(&mut self, expression: &ast::Expr) -> Type<'db>;

    /// Infers a declaration annotation, retaining qualifiers for the application to validate.
    fn infer_annotation_expression(
        &mut self,
        expression: &ast::Expr,
    ) -> (Type<'db>, TypeQualifiers);

    /// Specializes a signature's result using the application's explicit type arguments.
    ///
    /// Type argument inference, defaults, and validation follow ordinary generic applications.
    fn infer_specialized_return_type(
        &mut self,
        subscript: &ast::ExprSubscript,
        signature: &Signature<'db>,
    ) -> Type<'db>;

    /// Records the type of application-owned syntax that does not use ordinary child inference.
    fn store_expression_type(&mut self, expression: &ast::Expr, ty: Type<'db>);

    /// Reports an invalid type form using the current diagnostic rules and suppressions.
    fn report_invalid_type_form(&mut self, range: TextRange, message: &str);
}

/// The source of an application-supplied binding or builtin.
#[derive(Clone, Debug)]
pub enum ProvidedBindingValue<'db> {
    /// A native declaration without an implementation in a source file.
    Value(Type<'db>),
    /// The public value of a source symbol at the end of its module.
    Export {
        file: ProgramFile<'db>,
        name: Name,
        /// An application-owned value for the resolved export. The source still determines
        /// whether the name is defined and supplies its definition for navigation.
        value: Option<Type<'db>>,
    },
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

/// Result refinement and diagnostics supplied after ordinary call checking.
///
/// Hosted diagnostics are added to ordinary argument diagnostics; `return_type`
/// optionally refines the inferred result.
#[derive(Default)]
pub struct ProvidedCallResult<'db> {
    pub return_type: Option<Type<'db>>,
    pub diagnostics: Vec<Diagnostic>,
}

impl<'db> From<Option<Type<'db>>> for ProvidedCallResult<'db> {
    fn from(return_type: Option<Type<'db>>) -> Self {
        Self {
            return_type,
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
            let constituents = match receiver {
                Type::NominalInstance(_) => Either::Left(std::iter::once(&receiver)),
                Type::Intersection(intersection) => Either::Right(intersection.positive(db).iter()),
                _ => return false,
            };
            let mut immutable_storage = false;
            for constituent in constituents {
                // Structural properties constrain the field's type, but do not describe
                // runtime descriptors or prove storage themselves.
                match constituent {
                    Type::ProtocolInstance(_) => continue,
                    Type::NominalInstance(_) => {}
                    _ => return false,
                }
                let PlaceAndQualifiers { place, qualifiers } =
                    constituent.instance_member(db, env, name);
                let stored = place.is_definitely_bound()
                    && qualifiers.contains(
                        TypeQualifiers::FINAL | TypeQualifiers::GUARANTEED_INSTANCE_STORAGE,
                    );
                if !stored && !place.is_undefined() {
                    // A mutable instance declaration can shadow the supplied getter.
                    return false;
                }
                if !constituent.permits_instance_storage(db, env, name, stored) {
                    return false;
                }
                // An intersection's required protocol member can prevent ordinary lookup
                // from reaching __getattr__. Ask the nominal carrier using the same checked
                // getter resolution, preserving the full receiver for schema specialization.
                immutable_storage |= stored
                    || constituent
                        .getattr_result_with_storage(
                            db,
                            env,
                            name,
                            MemberLookupPolicy::default(),
                            Some(receiver),
                        )
                        .1;
            }
            if !immutable_storage {
                return false;
            }
            // Keep constraints contributed by every component for the next path segment.
            let Ok(member) = receiver.member_lookup_with_policy_and_receiver(
                db,
                env,
                name,
                MemberLookupPolicy::RUNTIME_ATTRIBUTE,
                None,
            ) else {
                return false;
            };
            let Place::Defined(member) = member.member(db).place else {
                return false;
            };
            if !member.is_definitely_defined() {
                return false;
            }
            receiver = member.ty;
        }
        true
    }

    /// Validates stored-field precedence before descriptor lookup consumes its qualifiers.
    fn permits_instance_storage(
        self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        name: &Name,
        stored: bool,
    ) -> bool {
        if let Some(class_member) = self
            .class_member(db, env, name)
            .place
            .ignore_possibly_undefined()
            && (!stored || !class_member.is_definitely_non_data_descriptor(db, env))
        {
            return false;
        }
        let policy = MemberLookupPolicy::MRO_NO_OBJECT_FALLBACK
            | MemberLookupPolicy::META_CLASS_NO_TYPE_FALLBACK;
        self.class_member_with_policy(db, env, "__getattribute__", policy)
            .place
            .is_undefined()
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
    ///
    /// An intersection preserves data from its positive constituents when all data-bearing
    /// constituents agree.
    pub fn provided_data(
        self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
    ) -> Option<&'db ProvidedData> {
        let class = match self {
            Self::Callable(callable) => return callable.provided_data(db).as_ref(),
            Self::Intersection(intersection) => {
                let mut data = intersection
                    .positive(db)
                    .iter()
                    .filter_map(|ty| ty.provided_data(db, env));
                let first = data.next()?;
                return data.all(|other| other == first).then_some(first);
            }
            Self::ClassLiteral(class) => class,
            Self::NominalInstance(instance) => instance.class_literal(db, env),
            _ => return None,
        };
        let ClassLiteral::Dynamic(class) = class else {
            return None;
        };
        let source = class.instance_fields_source(db).as_ref()?;
        match source {
            ProvidedInstanceFieldsSource::Eager(fields) => fields.data.as_ref(),
            ProvidedInstanceFieldsSource::Deferred(data) => Some(data),
        }
    }
}

#[cfg(test)]
mod source_tests;
#[cfg(test)]
mod tests;
