//! Opt-in checking of a named function body under one declared overload.
//!
//! Domains support fixed parameters and normalized keyword rows in simple function bodies.
//! Unsupported syntax must be rejected before inference: capture, loop, and comprehension
//! queries do not yet carry a body domain.

use itertools::Itertools;
use ruff_db::parsed::parsed_module;
use ruff_python_ast as ast;
use ty_python_core::ast_ids::HasScopedUseId;
use ty_python_core::definition::{Definition, DefinitionKind, ParameterDefinitionNodeKind};
use ty_python_core::scope::ScopeId;
use ty_python_core::semantic_index;
use ty_python_core::statement::StatementInner;

use super::{
    DefinitionInference, ExpressionInference, FunctionType, InferExpression, InferScope,
    ScopeInference, StatementInferenceInner, TypeContext, infer_definition_region,
    infer_definition_types, infer_expression_region, infer_scope_region, infer_statement_region,
};
use crate::semantic_model::HasType;
use crate::types::call::Argument;
use crate::types::constraints::ConstraintSetBuilder;
use crate::types::function::{KnownFunction, OverloadLiteral};
use crate::types::generics::Specialization;
use crate::types::signatures::{
    ParameterConsistency, PreparedOverloadImplementation, ReturnCallableTypeVarScope,
    ReturnTypeConsistency, keyword_arguments_type,
};
use crate::types::string_annotation::SourceAnnotation;
use crate::types::{
    CallArguments, KnownClass, MemberLookupPolicy, ParameterKind, Signature, Type,
    TypeCheckDiagnostics, UnionType,
};
use crate::{Db, ProgramEnvironment, SemanticModel};

/// Why a declared overload cannot be used to check its implementation body.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BodyDomainError {
    /// The function or body requires domain propagation that is not implemented.
    Unsupported,
    /// Ordinary overload implementation consistency rejects this domain.
    Inconsistent,
}

/// Check a supported implementation body under one of its declared overloads.
///
/// This is additional checking, not a replacement for ordinary function or overload checking.
/// It preserves the public callable type. A source function may adopt an entire signature from
/// an external declaration; in that case the overload index refers to that declaration's family.
/// Fixed parameters and normalized keyword rows support assignments, calls, conditionals, and
/// builtin collection copies. Mutating methods require a directly allocated local receiver.
/// Keyword captures retain source write types and projected read facts; transferring the raw
/// capture through aliases, storage, or returns remains unsupported. Fresh copies are supported.
/// Generic implementations require complete specialization from fixed overload inputs.
/// The same substitution applies to source declarations and already inferred default types;
/// their ordinary inference and shared runtime identity are unchanged. Generic domains require
/// inhabited input evidence for every fixed source slot. Nongeneric omitted slots retain their
/// ordinary source default types. Optional positional-only domains remain unsupported because their omitted
/// inputs can be correlated. An unsupported domain never means success.
/// Supported domains can retain authored gradual input types: completing these additional
/// checks does not establish that every operation in the body has a fully static contract.
pub fn check_overload_body<'db>(
    db: &'db dyn Db,
    function: FunctionType<'db>,
    overload_index: usize,
) -> Result<TypeCheckDiagnostics, BodyDomainError> {
    let domain = prepare_body_domain(db, function, overload_index)?;
    let inference = infer_body_scope(db, domain);
    let mut diagnostics = TypeCheckDiagnostics::default();
    if let Some(inferred) = inference.diagnostics() {
        diagnostics.extend(inferred);
    }
    Ok(diagnostics)
}

pub(crate) fn overload_body_diagnostics<'db>(
    db: &'db dyn Db,
    function: FunctionType<'db>,
) -> impl Iterator<Item = TypeCheckDiagnostics> + 'db {
    let count = overload_family(db, function).map_or(0, |(overloads, _)| overloads.len());
    // Unsupported domains have no additional proof. Each remaining domain is still checked.
    (0..count).filter_map(move |index| check_overload_body(db, function, index).ok())
}

/// Identity and entry bindings validated by `prepare_body_domain`.
#[salsa::interned(debug, heap_size=ruff_memory_usage::heap_size)]
pub(crate) struct FunctionBodyDomain<'db> {
    #[returns(copy)]
    pub(super) implementation: OverloadLiteral<'db>,
    #[returns(copy)]
    pub(super) overload: OverloadLiteral<'db>,
    #[returns(ref)]
    parameters: Box<[(Definition<'db>, Type<'db>)]>,
    #[returns(copy)]
    pub(crate) return_type: Type<'db>,
    #[returns(copy)]
    specialization: Option<Specialization<'db>>,
}

impl<'db> FunctionBodyDomain<'db> {
    pub(crate) fn scope(self, db: &'db dyn Db) -> ScopeId<'db> {
        self.implementation(db).body_scope(db)
    }

    pub(crate) fn parameter_type(
        self,
        db: &'db dyn Db,
        definition: Definition<'db>,
    ) -> Option<Type<'db>> {
        self.parameters(db)
            .iter()
            .find_map(|(parameter, ty)| (*parameter == definition).then_some(*ty))
    }

    pub(super) fn parameter_binding_type(
        self,
        db: &'db dyn Db,
        definition: Definition<'db>,
    ) -> Option<Type<'db>> {
        // Keyword capture entries describe current contents. The dictionary itself retains
        // its source writable type; Contents owns the projected fields and their invalidation.
        if matches!(
            definition.kind(db),
            DefinitionKind::Parameter(ParameterDefinitionNodeKind::VariadicKeywordParameter(_))
        ) {
            return None;
        }
        self.parameter_type(db, definition)
    }

    pub(super) fn specialize_type(self, db: &'db dyn Db, ty: Type<'db>) -> Type<'db> {
        ty.apply_optional_specialization(db, self.specialization(db))
    }
}

fn overload_family<'db>(
    db: &'db dyn Db,
    function: FunctionType<'db>,
) -> Result<(&'db [OverloadLiteral<'db>], OverloadLiteral<'db>), BodyDomainError> {
    let (mut overloads, implementation) = function.overloads_and_implementation(db);
    let implementation = implementation.ok_or(BodyDomainError::Unsupported)?;
    if overloads.is_empty() {
        let file = implementation.definition(db).program_file(db);
        let module = parsed_module(db, file.python_file(db)).load(db);
        let node = implementation
            .body_scope(db)
            .node(db)
            .expect_function()
            .node(&module);
        let donor = SourceAnnotation::external_function_definition(db, file, node)
            .ok_or(BodyDomainError::Unsupported)?;
        let donor_function = infer_definition_types(db, donor)
            .function_type(donor)
            .ok_or(BodyDomainError::Unsupported)?;
        let (donor_overloads, donor_implementation) =
            donor_function.overloads_and_implementation(db);
        if donor_implementation.is_none_or(|implementation| implementation.definition(db) != donor)
        {
            return Err(BodyDomainError::Unsupported);
        }
        overloads = donor_overloads;
    }
    Ok((overloads, implementation))
}

fn prepare_body_domain<'db>(
    db: &'db dyn Db,
    function: FunctionType<'db>,
    overload_index: usize,
) -> Result<FunctionBodyDomain<'db>, BodyDomainError> {
    let (overloads, implementation) = overload_family(db, function)?;
    let implementation_definition = implementation.definition(db);
    if !implementation_definition.file_scope(db).is_global() {
        return Err(BodyDomainError::Unsupported);
    }
    let file = implementation_definition.program_file(db);
    let module = parsed_module(db, file.python_file(db)).load(db);
    let node = implementation
        .body_scope(db)
        .node(db)
        .expect_function()
        .node(&module);
    if node.is_async || !node.decorator_list.is_empty() || node.parameters.vararg.is_some() {
        return Err(BodyDomainError::Unsupported);
    }
    let overload = *overloads
        .get(overload_index)
        .ok_or(BodyDomainError::Unsupported)?;
    let overload_module = parsed_module(db, overload.definition(db).python_file(db)).load(db);
    let overload_node = overload
        .body_scope(db)
        .node(db)
        .expect_function()
        .node(&overload_module);
    if overload_node.decorator_list.len() != 1 || overload_node.parameters.vararg.is_some() {
        return Err(BodyDomainError::Unsupported);
    }
    let implementation_signature =
        implementation.raw_signature(db, ReturnCallableTypeVarScope::Lexical);
    let overload_signature = overload.raw_signature(db, ReturnCallableTypeVarScope::Lexical);
    let env = ProgramEnvironment::from_file(file);
    let supported_signature = |signature: &crate::types::Signature<'db>| {
        !matches!(
            signature.return_ty.resolve_type_alias(db),
            Type::TypeIs(_) | Type::TypeGuard(_)
        ) && signature.parameters().is_standard()
            && signature.return_ty.is_fully_static(db, &env)
            && !signature.return_ty.has_indeterminate_inference(db, &env)
            && signature.parameters().iter().all(|parameter| {
                !parameter
                    .annotated_type()
                    .has_indeterminate_inference(db, &env)
                    && matches!(
                        parameter.kind(),
                        ParameterKind::PositionalOnly {
                            name: _,
                            default_type: _
                        } | ParameterKind::PositionalOrKeyword {
                            name: _,
                            default_type: _
                        } | ParameterKind::KeywordOnly {
                            name: _,
                            default_type: _
                        } | ParameterKind::KeywordVariadic { name: _ }
                    )
            })
    };
    if !supported_signature(&implementation_signature) || !supported_signature(&overload_signature)
    {
        return Err(BodyDomainError::Unsupported);
    }
    if overload_signature
        .parameters()
        .iter()
        .any(|parameter| parameter.is_positional_only() && parameter.has_default())
    {
        return Err(BodyDomainError::Unsupported);
    }
    let PreparedOverloadImplementation {
        signature: implementation_signature,
        specialization,
    } = implementation_signature
        .prepare_overload_implementation(db, &env, &overload_signature)
        .ok_or(BodyDomainError::Unsupported)?;
    if !matches!(
        implementation_signature.implementation_parameters_consistency_with(
            db,
            &env,
            &overload_signature
        ),
        ParameterConsistency::Consistent
    ) || !matches!(
        implementation_signature.implementation_return_type_consistency_with(
            db,
            &env,
            &overload_signature
        ),
        ReturnTypeConsistency::Consistent
    ) {
        return Err(BodyDomainError::Inconsistent);
    }
    let parameters = project_body_parameters(
        db,
        &env,
        implementation.body_scope(db),
        &node.parameters,
        &implementation_signature,
        &overload_signature,
        specialization,
    )?;
    if !supported_body(db, function, node, &implementation_signature, &parameters) {
        return Err(BodyDomainError::Unsupported);
    }
    Ok(FunctionBodyDomain::new(
        db,
        implementation,
        overload,
        parameters,
        overload_signature.return_ty,
        specialization,
    ))
}

/// Project a call domain into source bindings using the ordinary argument matcher.
fn project_body_parameters<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    scope: ScopeId<'db>,
    source_parameters: &ast::Parameters,
    implementation: &Signature<'db>,
    overload: &Signature<'db>,
    specialization: Option<Specialization<'db>>,
) -> Result<Box<[(Definition<'db>, Type<'db>)]>, BodyDomainError> {
    let bind = |keywords: bool| {
        let arguments: Option<CallArguments<'_, 'db>> = overload
            .parameters()
            .iter()
            .map(|parameter| {
                let (argument, ty) = match parameter.kind() {
                    ParameterKind::PositionalOnly {
                        name: _,
                        default_type: _,
                    } => (Argument::Positional, parameter.annotated_type()),
                    ParameterKind::PositionalOrKeyword {
                        name,
                        default_type: _,
                    } => {
                        if keywords {
                            (Argument::Keyword(name.as_str()), parameter.annotated_type())
                        } else {
                            (Argument::Positional, parameter.annotated_type())
                        }
                    }
                    ParameterKind::KeywordOnly {
                        name,
                        default_type: _,
                    } => (Argument::Keyword(name.as_str()), parameter.annotated_type()),
                    ParameterKind::Variadic { name: _ } => return None,
                    ParameterKind::KeywordVariadic { name: _ } => (
                        Argument::Keywords,
                        KnownClass::Dict.to_specialized_instance(
                            db,
                            env,
                            &[
                                KnownClass::Str.to_instance(db, env),
                                parameter.annotated_type(),
                            ],
                        ),
                    ),
                };
                Some((argument, Some(ty)))
            })
            .collect();
        let arguments = arguments.ok_or(BodyDomainError::Unsupported)?;
        let constraints = ConstraintSetBuilder::new();
        let bindings = Type::single_callable(db, implementation.clone())
            .bindings(db, env)
            .match_parameters(db, env, &arguments)
            .check_types(
                db,
                env,
                &constraints,
                &arguments,
                TypeContext::default(),
                &[],
            )
            .map_err(|_| BodyDomainError::Unsupported)?;
        let callable = bindings
            .iter_flat()
            .exactly_one()
            .map_err(|_| BodyDomainError::Unsupported)?;
        let [binding] = callable.overloads() else {
            return Err(BodyDomainError::Unsupported);
        };
        let mapping = (0..overload.parameters().len())
            .map(|index| {
                let matched = binding.matched_argument_for_call_argument(false, index)?;
                let mut owners = matched.parameters.iter().map(|parameter| {
                    implementation.parameters()[parameter.index].source_parameter_index()
                });
                let owner = owners.next()??;
                owners.all(|next| next == Some(owner)).then_some(owner)
            })
            .collect::<Option<Vec<_>>>()
            .ok_or(BodyDomainError::Unsupported)?;
        Ok((mapping, binding.parameter_types().to_vec()))
    };
    let (positional, supplied) = bind(false)?;
    let (keywords, _) = bind(true)?;
    // A positional prefix and a named argument bind independently. Agreement at both endpoints
    // establishes the same source ownership for every mixed call mode. Keep this projection
    // invariant explicit even after the full signature coverage check.
    if positional != keywords {
        return Err(BodyDomainError::Unsupported);
    }
    let index = semantic_index(db, scope.program_file(db));
    let kwargs_definition = source_parameters
        .kwarg
        .as_deref()
        .map(|parameter| index.expect_single_definition(parameter));
    let mut may_be_omitted = vec![true; source_parameters.len()];
    for (parameter, index) in overload.parameters().iter().zip(&positional) {
        may_be_omitted[*index] = parameter.has_default();
    }
    source_parameters
        .iter()
        .enumerate()
        .zip_eq(may_be_omitted)
        .map(|((source_index, source_parameter), omitted)| {
            let definition = index.expect_single_definition(source_parameter.as_parameter());
            if Some(definition) == kwargs_definition {
                let entry = keyword_arguments_type(
                    db,
                    env,
                    overload.parameters().iter().zip(&positional).filter_map(
                        |(parameter, owner)| (*owner == source_index).then_some(parameter),
                    ),
                )
                .ok_or(BodyDomainError::Unsupported)?;
                if entry.has_indeterminate_inference(db, env) {
                    return Err(BodyDomainError::Unsupported);
                }
                return Ok((definition, entry));
            }
            // A residual keyword domain can also reach an optional fixed source slot. That
            // needs omission-aware projection beyond the fixed argument endpoints used here.
            if overload
                .parameters()
                .iter()
                .zip(&positional)
                .any(|(parameter, owner)| *owner == source_index && parameter.is_keyword_variadic())
            {
                return Err(BodyDomainError::Unsupported);
            }
            let (parameter_index, parameter) = implementation
                .parameters()
                .iter()
                .enumerate()
                .filter(|(_, parameter)| parameter.source_parameter_index() == Some(source_index))
                .exactly_one()
                .map_err(|_| BodyDomainError::Unsupported)?;
            let supplied = supplied[parameter_index];
            // Generic omitted inputs need a projection distinct from the fixed input evidence
            // used to specialize the implementation. Do not use a default to invent that evidence.
            if (specialization.is_some() || !overload.is_non_generic())
                && supplied.is_none_or(|ty| ty.is_never())
            {
                return Err(BodyDomainError::Unsupported);
            }
            if parameter.definition() != Some(definition) || definition.scope(db) != scope {
                return Err(BodyDomainError::Unsupported);
            }
            let entry = if omitted {
                // This is the original source default, inferred once in its ordinary definition
                // context. Donor defaults only describe optionality; they are not runtime values.
                let default = parameter
                    .default_type(db)
                    .ok_or(BodyDomainError::Unsupported)?;
                // Substitute only the already inferred type view. The ordinary default query
                // and its shared runtime value retain their original identity and evidence.
                let default = default.apply_optional_specialization(db, specialization);
                if !default.is_fully_static(db, env) || default.has_indeterminate_inference(db, env)
                {
                    return Err(BodyDomainError::Unsupported);
                }
                supplied.map_or(default, |supplied| {
                    UnionType::from_two_elements(db, env, supplied, default)
                })
            } else {
                supplied.ok_or(BodyDomainError::Unsupported)?
            };
            if entry.has_indeterminate_inference(db, env) {
                return Err(BodyDomainError::Unsupported);
            }
            Ok((definition, entry))
        })
        .collect()
}

fn supported_body(
    db: &dyn Db,
    function: FunctionType<'_>,
    node: &ast::StmtFunctionDef,
    signature: &crate::types::Signature<'_>,
    entries: &[(Definition<'_>, Type<'_>)],
) -> bool {
    fn all_reaching_assignments(
        db: &dyn Db,
        function: FunctionType<'_>,
        name: &ast::ExprName,
        mut accepts: impl FnMut(&ast::Expr) -> bool,
    ) -> bool {
        let file = function.program_file(db);
        let index = semantic_index(db, file);
        let scope = function.literal(db).last_definition.body_scope(db);
        let module = parsed_module(db, file.python_file(db)).load(db);
        let mut bindings = index
            .use_def_map(scope.file_scope_id(db))
            .bindings_at_use(name.scoped_use_id(db, file))
            .peekable();
        bindings.peek().is_some()
            && bindings.all(|binding| {
                let Some(definition) = binding.binding.definition() else {
                    return false;
                };
                if definition.scope(db) != scope {
                    return false;
                }
                let value = match definition.kind(db) {
                    DefinitionKind::Assignment(assignment) => {
                        if !assignment.is_single_target(&module) {
                            return false;
                        }
                        assignment.value(&module)
                    }
                    DefinitionKind::AnnotatedAssignment(assignment) => {
                        let Some(value) = assignment.value(&module) else {
                            return false;
                        };
                        value
                    }
                    _ => return false,
                };
                accepts(value)
            })
    }

    // A projected parameter is an entry fact, not a narrower write declaration. Mutating
    // methods are admitted only on direct allocations, so aliases of captured kwargs cannot
    // accidentally turn their projected fields into source assignment restrictions.
    fn fresh_receiver(
        db: &dyn Db,
        function: FunctionType<'_>,
        receiver: &ast::Expr,
        class: KnownClass,
    ) -> bool {
        let ast::Expr::Name(name) = receiver else {
            return false;
        };
        let model = SemanticModel::new(db, function.program_file(db));
        all_reaching_assignments(db, function, name, |value| match value {
            ast::Expr::List(_) => class == KnownClass::List,
            ast::Expr::Dict(_) => class == KnownClass::Dict,
            ast::Expr::Call(call) => match call.func.inferred_type(&model) {
                Some(Type::ClassLiteral(callee)) => callee.is_known(db, class),
                _ => false,
            },
            _ => false,
        })
    }

    fn nonlocal_callee(db: &dyn Db, function: FunctionType<'_>, value: &ast::Expr) -> bool {
        let model = SemanticModel::new(db, function.program_file(db));
        match value.inferred_type(&model) {
            Some(Type::ClassLiteral(class)) => [KnownClass::List, KnownClass::Dict]
                .into_iter()
                .any(|known| class.is_known(db, known)),
            Some(Type::FunctionLiteral(callee)) => {
                callee != function
                    && !matches!(
                        callee.known(db),
                        Some(KnownFunction::NewClass | KnownFunction::NamedTuple)
                    )
            }
            Some(ty) => callable_entry(db, &model.program_environment(), ty),
            None => false,
        }
    }

    fn assigned_callee(
        db: &dyn Db,
        function: FunctionType<'_>,
        locals: &[&str],
        value: &ast::Expr,
    ) -> bool {
        match value {
            ast::Expr::Name(name) => {
                !locals.contains(&name.id.as_str()) && nonlocal_callee(db, function, value)
            }
            ast::Expr::If(conditional) => {
                assigned_callee(db, function, locals, &conditional.body)
                    && assigned_callee(db, function, locals, &conditional.orelse)
            }
            _ => false,
        }
    }

    fn collection_method(
        db: &dyn Db,
        function: FunctionType<'_>,
        attribute: &ast::ExprAttribute,
    ) -> bool {
        let model = SemanticModel::new(db, function.program_file(db));
        let (class, mutates) = match attribute.attr.id.as_str() {
            "get" => (KnownClass::Dict, false),
            "pop" => (KnownClass::Dict, true),
            "append" => (KnownClass::List, true),
            _ => return false,
        };
        if mutates && !fresh_receiver(db, function, &attribute.value, class) {
            return false;
        }
        if !mutates
            && attribute
                .value
                .inferred_type(&model)
                .is_some_and(|ty| matches!(ty.resolve_type_alias(db), Type::TypedDict(_)))
        {
            // TypedDict get is checked by the ordinary specialized call owner.
            return true;
        }
        let Some(Type::BoundMethod(method)) = attribute.inferred_type(&model) else {
            return false;
        };
        let env = ProgramEnvironment::from_file(function.program_file(db));
        let Some(Type::BoundMethod(declared)) = class
            .to_instance(db, &env)
            .member_lookup_with_policy(
                db,
                &env,
                attribute.attr.id.as_str(),
                MemberLookupPolicy::NO_INSTANCE_FALLBACK,
            )
            .place
            .ignore_possibly_undefined()
        else {
            return false;
        };
        match (method.function(db), declared.function(db)) {
            (Some(method), Some(declared)) => method.definition(db) == declared.definition(db),
            _ => false,
        }
    }

    fn expression(
        db: &dyn Db,
        function: FunctionType<'_>,
        locals: &[&str],
        callees: &[&str],
        value: &ast::Expr,
    ) -> bool {
        match value {
            ast::Expr::Name(_) => true,
            ast::Expr::NumberLiteral(_) => true,
            ast::Expr::StringLiteral(_) => true,
            ast::Expr::BytesLiteral(_) => true,
            ast::Expr::BooleanLiteral(_) => true,
            ast::Expr::NoneLiteral(_) => true,
            ast::Expr::Attribute(attribute) => {
                attribute.ctx == ast::ExprContext::Load
                    && expression(db, function, locals, callees, &attribute.value)
            }
            ast::Expr::Compare(compare) => compare
                .operands
                .iter()
                .all(|operand| expression(db, function, locals, callees, operand)),
            ast::Expr::BoolOp(boolean) => boolean
                .values
                .iter()
                .all(|value| expression(db, function, locals, callees, value)),
            ast::Expr::UnaryOp(unary) => {
                unary.op == ast::UnaryOp::Not
                    && expression(db, function, locals, callees, &unary.operand)
            }
            ast::Expr::If(conditional) => {
                [&conditional.test, &conditional.body, &conditional.orelse]
                    .into_iter()
                    .all(|value| expression(db, function, locals, callees, value))
            }
            ast::Expr::List(list) => list
                .elts
                .iter()
                .all(|value| expression(db, function, locals, callees, value)),
            ast::Expr::Tuple(tuple) => tuple
                .elts
                .iter()
                .all(|value| expression(db, function, locals, callees, value)),
            ast::Expr::Dict(dictionary) => dictionary.items.iter().all(|item| {
                item.key
                    .as_ref()
                    .is_none_or(|key| expression(db, function, locals, callees, key))
                    && expression(db, function, locals, callees, &item.value)
            }),
            ast::Expr::Subscript(subscript) => {
                expression(db, function, locals, callees, &subscript.value)
                    && expression(db, function, locals, callees, &subscript.slice)
            }
            ast::Expr::BinOp(binary) => {
                expression(db, function, locals, callees, &binary.left)
                    && expression(db, function, locals, callees, &binary.right)
            }
            ast::Expr::Call(call) => {
                match call.func.as_ref() {
                    ast::Expr::Name(name) => {
                        if name.id == *function.name(db) {
                            return false;
                        }
                        if locals.contains(&name.id.as_str()) {
                            if !callees.contains(&name.id.as_str())
                                && !all_reaching_assignments(db, function, name, |value| {
                                    assigned_callee(db, function, locals, value)
                                })
                            {
                                return false;
                            }
                        } else if !nonlocal_callee(db, function, &call.func) {
                            return false;
                        }
                    }
                    ast::Expr::Attribute(attribute) => {
                        if !expression(db, function, locals, callees, &attribute.value)
                            || !collection_method(db, function, attribute)
                        {
                            return false;
                        }
                    }
                    _ => return false,
                }
                call.arguments
                    .args
                    .iter()
                    .all(|argument| expression(db, function, locals, callees, argument))
                    && call
                        .arguments
                        .keywords
                        .iter()
                        .all(|argument| expression(db, function, locals, callees, &argument.value))
            }
            _ => false,
        }
    }
    fn statements(
        db: &dyn Db,
        function: FunctionType<'_>,
        locals: &[&str],
        callees: &[&str],
        body: &[ast::Stmt],
    ) -> bool {
        let supported = |value: &ast::Expr| expression(db, function, locals, callees, value);
        body.iter().all(|statement| match statement {
            ast::Stmt::Return(statement) => statement.value.as_deref().is_none_or(supported),
            ast::Stmt::If(statement) => {
                supported(&statement.test)
                    && statements(db, function, locals, callees, &statement.body)
                    && statement.elif_else_clauses.iter().all(|clause| {
                        clause.test.as_ref().is_none_or(supported)
                            && statements(db, function, locals, callees, &clause.body)
                    })
            }
            ast::Stmt::Assign(assignment) => {
                let [ast::Expr::Name(name)] = assignment.targets.as_slice() else {
                    return false;
                };
                if let Some(annotation) =
                    SourceAnnotation::new(db, function.program_file(db), name, None)
                {
                    if let Some(expression) = annotation.expression() {
                        let definition = semantic_index(db, function.program_file(db))
                            .expect_single_definition(name);
                        if infer_definition_types(db, definition)
                            .try_expression_type(expression)
                            .is_some_and(|ty| ty.is_typealias_special_form())
                        {
                            return false;
                        }
                    } else if matches!(
                        annotation,
                        SourceAnnotation::External {
                            annotation: _,
                            range: _
                        }
                    ) && annotation.external_declaration(db).is_none()
                    {
                        return false;
                    }
                }
                supported(&assignment.value)
            }
            ast::Stmt::AnnAssign(assignment) => {
                assignment.target.is_name_expr()
                    && !SemanticModel::new(db, function.program_file(db))
                        .is_type_alias_annotation(&assignment.annotation)
                    && assignment.value.as_deref().is_some_and(supported)
            }
            ast::Stmt::Expr(statement) => supported(&statement.value),
            ast::Stmt::Pass(_) => true,
            _ => false,
        })
    }
    fn callable_entry<'db>(db: &'db dyn Db, env: &ProgramEnvironment<'db>, ty: Type<'db>) -> bool {
        match ty.resolve_type_alias(db) {
            Type::Callable(_) | Type::ProtocolInstance(_) | Type::Dynamic(_) => true,
            Type::NominalInstance(_) => ty.try_upcast_to_callable(db, env).is_some(),
            Type::Union(union) => union
                .elements(db)
                .iter()
                .all(|ty| callable_entry(db, env, *ty)),
            _ => false,
        }
    }
    let env = ProgramEnvironment::from_file(function.program_file(db));
    let index = semantic_index(db, function.program_file(db));
    let scope = function
        .literal(db)
        .last_definition
        .body_scope(db)
        .file_scope_id(db);
    let places = index.place_table(scope);
    let use_def = index.use_def_map(scope);
    let locals: Vec<_> = places
        .symbols()
        .filter(|symbol| symbol.is_local())
        .map(|symbol| symbol.name().as_str())
        .collect();
    // The scope inventory includes writes in every branch, even after an early return. Keeping
    // callable parameters unreassigned excludes declaration factories without a second AST walk.
    let callees: Vec<_> = signature
        .parameters()
        .iter()
        .filter_map(|parameter| {
            let definition = parameter.definition()?;
            let (_, ty) = entries.iter().find(|(entry, _)| *entry == definition)?;
            if !callable_entry(db, &env, *ty)
                || use_def.definitions_with_usage().any(|(_, other, _)| {
                    other != definition && other.place(db) == definition.place(db)
                })
            {
                return None;
            }
            parameter.name().map(ast::name::Name::as_str)
        })
        .collect();
    statements(db, function, &locals, &callees, &node.body)
        && node.parameters.kwarg.as_deref().is_none_or(|kwargs| {
            !crate::types::dictionary::contents::has_value_exposure(
                db,
                index.expect_single_definition(kwargs),
            )
        })
}

#[salsa::tracked(returns(ref), heap_size=ruff_memory_usage::heap_size)]
fn infer_body_scope<'db>(db: &'db dyn Db, domain: FunctionBodyDomain<'db>) -> ScopeInference<'db> {
    infer_scope_region(
        db,
        InferScope::new(db, domain.scope(db), TypeContext::default()),
        Some(domain),
    )
}

#[salsa::tracked(
    returns(ref),
    cycle_initial=|db, id, definition: Definition<'db>, _| DefinitionInference::cycle_initial(db, definition, Type::divergent(id)),
    cycle_fn=|db, cycle, previous: &DefinitionInference<'db>, inference: DefinitionInference<'db>, definition: Definition<'db>, _| inference.cycle_normalized(db, previous, cycle, definition),
    heap_size=ruff_memory_usage::heap_size
)]
pub(super) fn infer_body_definition<'db>(
    db: &'db dyn Db,
    definition: Definition<'db>,
    domain: FunctionBodyDomain<'db>,
) -> DefinitionInference<'db> {
    infer_definition_region(db, definition, Some(domain))
}

#[salsa::tracked(
    returns(ref),
    cycle_initial=|db, id, input: InferExpression<'db>, _| super::expression_cycle_initial(db, id, input),
    cycle_fn=|db, cycle, previous: &ExpressionInference<'db>, inference: ExpressionInference<'db>, input: InferExpression<'db>, _| {
        let (expression, _) = input.into_inner(db);
        inference.cycle_normalized(db, &ProgramEnvironment::from_scope(expression.scope(db)), previous, cycle)
    },
    heap_size=ruff_memory_usage::heap_size
)]
pub(super) fn infer_body_expression<'db>(
    db: &'db dyn Db,
    input: InferExpression<'db>,
    domain: FunctionBodyDomain<'db>,
) -> ExpressionInference<'db> {
    infer_expression_region(db, input, Some(domain))
}

#[salsa::tracked(
    returns(ref),
    cycle_initial=|db, id, statement: StatementInner<'db>, _| StatementInferenceInner::cycle_initial(statement.scope(db), Type::divergent(id)),
    cycle_fn=|db, cycle, previous: &StatementInferenceInner<'db>, inference: StatementInferenceInner<'db>, statement: StatementInner<'db>, _| {
        inference.cycle_normalized(db, &ProgramEnvironment::from_file(statement.program_file(db)), previous, cycle)
    },
    heap_size=ruff_memory_usage::heap_size
)]
pub(super) fn infer_body_statement<'db>(
    db: &'db dyn Db,
    statement: StatementInner<'db>,
    domain: FunctionBodyDomain<'db>,
) -> StatementInferenceInner<'db> {
    infer_statement_region(db, statement, Some(domain))
}

#[cfg(test)]
mod tests {
    use std::fmt::Write as _;

    use ruff_db::diagnostic::{
        DiagnosticFormat, DisplayDiagnosticConfig, DisplayDiagnostics, SubDiagnostic,
    };
    use ruff_db::files::system_path_to_file;
    use ruff_db::system::DbWithWritableSystem;
    use ty_python_core::ProgramFile;

    use super::*;
    use crate::db::tests::{TestDb, setup_db};
    use crate::types::check_types_with_overload_bodies;
    use crate::types::infer::infer_complete_scope_types;

    fn function(db: &TestDb) -> FunctionType<'_> {
        let file = system_path_to_file(db, "/src/body.py").unwrap();
        let file = ProgramFile::new(db, file, db.program_environment().program(db));
        crate::place::global_symbol(db, file, "f")
            .place
            .expect_type()
            .expect_function_literal()
    }

    fn returned_type<'db>(
        db: &'db TestDb,
        function: FunctionType<'db>,
        domain: Option<FunctionBodyDomain<'db>>,
    ) -> Type<'db> {
        let scope = function.literal(db).last_definition.body_scope(db);
        let module = parsed_module(db, scope.program_file(db).python_file(db)).load(db);
        let function = scope.node(db).expect_function().node(&module);
        let Some(ast::Stmt::Return(statement)) = function.body.last() else {
            panic!("expected a final return statement");
        };
        let value = statement.value.as_deref().unwrap();
        let inference = domain.map_or_else(
            || infer_complete_scope_types(db, scope),
            |domain| infer_body_scope(db, domain),
        );
        inference.expression_type(value)
    }

    #[test]
    fn body_domains_preserve_copied_keyword_contents() -> anyhow::Result<()> {
        let mut db = setup_db();
        let source = indoc::indoc! {r#"
            from typing import Callable, Protocol, overload
            from typing_extensions import TypedDict, Unpack
            class Integers(TypedDict, closed=True):
                value: int
                marker: str
            class Strings(TypedDict, closed=True):
                value: str
                marker: str
            class Rule[T](Protocol):
                def __call__(self, *, data: T, marker: str) -> None: ...
            @overload
            def f(rule: Rule[int], **kwargs: Unpack[Integers]) -> None: ...
            @overload
            def f(rule: Rule[str], **kwargs: Unpack[Strings]) -> None: ...
            def f(rule: Callable[..., None], **kwargs: object) -> None:
                forwarded = dict(kwargs)
                forwarded.pop('value', None)
                rule(data=kwargs['value'], **forwarded)
        "#};
        for (before, after, wrong) in [
            ("dict(kwargs)", "dict(kwargs)", false),
            ("dict(kwargs)", "dict(kwargs, marker=42)", true),
            ("pop('value', None)", "pop('marker', None)", true),
            ("kwargs['value']", "kwargs['marker']", true),
            ("dict(kwargs)", "dict(kwargs)", false),
        ] {
            db.write_file("/src/body.py", source.replace(before, after))?;
            let f = function(&db);
            let ordinary = crate::types::check_types(&db, f.program_file(&db));
            let signature = f.last_definition_signature(&db).clone();
            for index in [0, 1, 0] {
                let diagnostics = check_overload_body(&db, f, index).unwrap();
                let fails = wrong && (after != "kwargs['marker']" || index == 0);
                assert_eq!(
                    !diagnostics.is_empty(),
                    fails,
                    "{after} domain {index}: {diagnostics:#?}"
                );
                assert_eq!(f.last_definition_signature(&db), &signature);
                assert_eq!(
                    crate::types::check_types(&db, f.program_file(&db)),
                    ordinary
                );
            }
        }
        let events = db.take_salsa_events();
        assert!(
            ruff_db::testing::find_will_execute_event_by_name(
                &db,
                "body_definition_contents",
                None,
                &events
            )
            .is_some()
        );
        Ok(())
    }

    #[test]
    fn body_domains_keep_conditional_dictionary_removal() -> anyhow::Result<()> {
        let mut db = setup_db();
        db.write_dedented(
            "/src/body.py",
            r#"
            from typing import Literal, overload
            from typing_extensions import TypedDict, Unpack
            class Row(TypedDict, closed=True):
                marker: str
            def consume(*, marker: str) -> None: ...
            @overload
            def f(remove: Literal[False], **kwargs: Unpack[Row]) -> None: ...
            @overload
            def f(remove: Literal[True], **kwargs: Unpack[Row]) -> None: ...
            def f(remove: bool, **kwargs: object) -> None:
                forwarded = dict(kwargs)
                if remove:
                    forwarded.pop('marker', None)
                consume(**forwarded)
        "#,
        )?;
        let f = function(&db);
        for index in [0, 1, 0] {
            let diagnostics = check_overload_body(&db, f, index).unwrap();
            assert_eq!(
                diagnostics.diagnostics().len(),
                index,
                "{index}: {diagnostics:#?}"
            );
            if index == 1 {
                assert_eq!(
                    diagnostics.diagnostics()[0].id().as_str(),
                    "missing-argument"
                );
            }
        }
        Ok(())
    }

    #[test]
    fn body_domains_check_generic_collection_forwarding() -> anyhow::Result<()> {
        let mut db = setup_db();
        let source = indoc::indoc! {r#"
            from typing import Literal, Protocol, overload
            type Input = list[str] | tuple[str, ...]
            type Tags[T: str] = list[T | Literal['manual']]
            class TagsRule[T: str](Protocol):
                def __call__(self, *args, tags: Tags[T], **kwargs) -> object: ...
            class DataRule[D, T: str](Protocol):
                def __call__(self, *args, data: D, tags: Tags[T], **kwargs) -> object: ...
            class Finish:
                def __call__(self, *, name: str) -> None: ...
            finish: Finish
            @overload
            def f[D: Input, Over: str](rule: DataRule[D, Over], *, name: str, inner_data: D, tags: list[Over] = ...) -> None: ...
            @overload
            def f[Over: str](rule: DataRule[list[Over], Over], *, name: str, tags: list[Over] = ...) -> None: ...
            def f[Impl: str](rule: TagsRule[Impl], *, name: str, inner_data: Input = [], tags: list[Impl] = []) -> None:
                inner_tags: Tags[Impl] = list(tags)
                if 'manual' not in tags:
                    inner_tags.append('manual')
                rule(name=name + '_', data=inner_data, tags=inner_tags)
                finish(name=name)
        "#};
        for (before, after, wrong) in [
            ("data=inner_data", "data=inner_data", false),
            ("data=inner_data", "data=tags", true),
            ("data=inner_data", "data=[]", true),
            ("data=inner_data", "data=42", true),
            ("append('manual')", "append(42)", true),
            ("finish(name=name)", "finish(name=42)", true),
            ("data=inner_data", "data=inner_data", false),
        ] {
            db.write_file("/src/body.py", source.replace(before, after))?;
            let f = function(&db);
            let ordinary = crate::types::check_types(&db, f.program_file(&db));
            let signature = f.last_definition_signature(&db).clone();
            let diagnostics = check_overload_body(&db, f, 0).unwrap();
            assert_eq!(!diagnostics.is_empty(), wrong, "{after}: {diagnostics:#?}");
            assert_eq!(
                check_overload_body(&db, f, 1),
                Err(BodyDomainError::Unsupported)
            );
            assert_eq!(
                crate::types::check_types(&db, f.program_file(&db)),
                ordinary
            );
            assert_eq!(f.last_definition_signature(&db), &signature);
        }
        Ok(())
    }

    #[test]
    fn body_domains_decline_mutating_captured_rows() -> anyhow::Result<()> {
        let mut db = setup_db();
        for body in [
            "kwargs.pop('value', None)",
            "alias = kwargs\n    alias.pop('value', None)",
            "copy = dict(kwargs)\n    copy = kwargs\n    copy.pop('value', None)",
            "kwargs['value'] = 'replacement'",
        ] {
            db.write_file(
                "/src/body.py",
                indoc::formatdoc! {"
                from typing import overload
                @overload
                def f(*, value: int) -> None: ...
                @overload
                def f(*, value: str) -> None: ...
                def f(**kwargs: object) -> None:
                    {body}
            "},
            )?;
            assert_eq!(
                check_overload_body(&db, function(&db), 0),
                Err(BodyDomainError::Unsupported),
                "{body}"
            );
        }
        Ok(())
    }

    #[test]
    fn body_domains_project_optional_data_into_copied_kwargs() -> anyhow::Result<()> {
        let mut db = setup_db();
        let source = indoc::indoc! {r#"
            from typing import Literal, Protocol, overload
            from typing_extensions import Never, NotRequired, TypedDict, Unpack
            type Input = list[str] | tuple[str, ...]
            class Forwarded(TypedDict, closed=True):
                marker: str
            class OptionalData(TypedDict, closed=True):
                marker: str
                inner_data: NotRequired[Input]
            class NoData(TypedDict, closed=True):
                marker: str
                inner_data: NotRequired[Never]
            class TagsRule[T: str](Protocol):
                def __call__(self, *args, tags: list[T], **kwargs) -> object: ...
            class DataRule[D, T: str](Protocol):
                def __call__(self, *, data: D, tags: list[T], marker: str) -> object: ...
            @overload
            def f[D: Input, T: str](rule: DataRule[D, T], *, inner_data: D, tags: list[T], **kwargs: Unpack[Forwarded]) -> None: ...
            @overload
            def f[T: str](rule: DataRule[list[T], T], *, tags: list[T], **kwargs: Unpack[NoData]) -> None: ...
            def f[T: str](rule: TagsRule[T], *, tags: list[T], **kwargs: Unpack[OptionalData]) -> None:
                forwarded = dict(kwargs)
                forwarded.pop('inner_data', None)
                rule(data=(kwargs['inner_data'] if 'inner_data' in kwargs else []), tags=tags, **forwarded)
        "#};
        for (before, after, failing_domains) in [
            ("else []", "else []", [false, false]),
            ("else []", "else [42]", [false, true]),
            ("kwargs['inner_data']", "tags", [true, false]),
            ("dict(kwargs)", "dict(kwargs, marker=42)", [true, true]),
            ("else []", "else []", [false, false]),
        ] {
            db.write_file("/src/body.py", source.replace(before, after))?;
            let f = function(&db);
            let ordinary = crate::types::check_types(&db, f.program_file(&db));
            if before == after {
                assert!(ordinary.is_empty(), "{ordinary:#?}");
            }
            for index in [0, 1, 0] {
                let diagnostics = check_overload_body(&db, f, index).unwrap();
                assert_eq!(
                    !diagnostics.is_empty(),
                    failing_domains[index],
                    "{after} domain {index}: {diagnostics:#?}"
                );
                assert_eq!(
                    crate::types::check_types(&db, f.program_file(&db)),
                    ordinary
                );
            }
        }
        Ok(())
    }

    #[test]
    fn body_domains_check_legacy_collection_forwarding() -> anyhow::Result<()> {
        let mut db = setup_db();
        db.write_dedented(
            "/src/body.py",
            "
            from typing import Protocol, TypeVar, overload
            T = TypeVar('T')
            class Rule(Protocol[T]):
                def __call__(self, *, data: list[T]) -> None: ...
            @overload
            def f(rule: Rule[int], values: list[int]) -> None: ...
            @overload
            def f(rule: Rule[str], values: list[str]) -> None: ...
            def f(rule: Rule[T], values: list[T]) -> None:
                copied: list[T] = list(values)
                rule(data=copied)
        ",
        )?;
        let f = function(&db);
        for index in [0, 1, 0] {
            let diagnostics = check_overload_body(&db, f, index).unwrap();
            assert!(diagnostics.is_empty(), "{diagnostics:#?}");
        }
        Ok(())
    }

    #[test]
    fn body_domains_decline_overridden_collection_operations() -> anyhow::Result<()> {
        let mut db = setup_db();
        for (setup, body) in [
            (
                "class Custom(dict):\n    def pop(self, *args): ...\ndict = Custom",
                "copied = dict()\n    copied.pop('value')",
            ),
            (
                "class Custom(list):\n    def append(self, value): ...\nlist = Custom",
                "copied = list()\n    copied.append(1)",
            ),
            (
                "from collections import namedtuple\nfactory = namedtuple",
                "Alias = factory('Alias', ['value'])",
            ),
        ] {
            db.write_file("/src/body.py", format!("from typing import overload\n{setup}\n@overload\ndef f(value: int) -> None: ...\n@overload\ndef f(value: str) -> None: ...\ndef f(value: int | str) -> None:\n    {body}\n"))?;
            assert_eq!(
                check_overload_body(&db, function(&db), 0),
                Err(BodyDomainError::Unsupported),
                "{body}"
            );
        }
        Ok(())
    }

    #[test]
    fn body_domains_preserve_literal_dictionary_bindings() -> anyhow::Result<()> {
        let mut db = setup_db();
        let source = indoc::indoc! {"
            from typing import overload
            @overload
            def f(value: int) -> int: ...
            @overload
            def f(value: str) -> str: ...
            def f(value: int | str) -> int | str:
                copied = {'value': value}
                return copied['value']
        "};
        for value in ["value", "42", "value"] {
            db.write_file(
                "/src/body.py",
                source.replace("{'value': value}", &format!("{{'value': {value}}}")),
            )?;
            let f = function(&db);
            for index in [0, 1, 0] {
                let diagnostics = check_overload_body(&db, f, index).unwrap();
                assert_eq!(
                    diagnostics.diagnostics().len(),
                    usize::from(value == "42" && index == 1),
                    "{value} domain {index}: {diagnostics:#?}"
                );
            }
        }
        Ok(())
    }

    #[test]
    fn body_domains_isolate_successful_subscript_constraints() -> anyhow::Result<()> {
        let mut db = setup_db();
        let source = indoc::indoc! {"
            from typing import overload
            @overload
            def f(value: dict[str, int] | None) -> dict[str, int]: ...
            @overload
            def f(value: dict[str, str] | None) -> dict[str, str]: ...
            def f(value: dict[str, int] | dict[str, str] | None) -> object:
                value['key']
                return value
        "};
        for wrong in [false, true, false] {
            db.write_file(
                "/src/body.py",
                if wrong {
                    source.replace("-> dict[str, str]: ...", "-> dict[str, int]: ...")
                } else {
                    source.to_owned()
                },
            )?;
            let f = function(&db);
            let ordinary = crate::types::check_types(&db, f.program_file(&db));
            for index in [0, 1, 0] {
                let diagnostics = check_overload_body(&db, f, index).unwrap();
                // The possible None receiver retains its normal indexing diagnostic; a
                // successful read excludes it from the subsequent return in each domain.
                assert_eq!(
                    diagnostics
                        .diagnostics()
                        .iter()
                        .filter(|diagnostic| diagnostic.id().as_str() == "invalid-return-type")
                        .count(),
                    usize::from(wrong && index == 1),
                    "domain {index}: {diagnostics:#?}"
                );
                assert_eq!(
                    crate::types::check_types(&db, f.program_file(&db)),
                    ordinary
                );
            }
        }
        let events = db.take_salsa_events();
        assert!(
            ruff_db::testing::find_will_execute_event_by_name(
                &db,
                "successful_body_subscript_constraints",
                None,
                &events
            )
            .is_some()
        );
        Ok(())
    }

    #[test]
    fn body_domains_preserve_keyword_write_contracts_through_calls() -> anyhow::Result<()> {
        let mut db = setup_db();
        for (body, supported) in [
            ("consume(kwargs)", true),
            ("copied: Source = dict(kwargs)\n    consume(copied)", true),
            ("copied = dict(kwargs)\n    consume_dict(copied)", true),
            ("alias = kwargs\n    consume(alias)", false),
            ("consume_nested((kwargs,))", false),
        ] {
            db.write_file(
                "/src/body.py",
                indoc::formatdoc! {"
                from typing import overload
                from typing_extensions import TypedDict, NotRequired, Unpack
                class Source(TypedDict, closed=True):
                    value: NotRequired[object]
                def consume(row: Source) -> None:
                    row['value'] = 'text'
                def consume_dict(row: dict[str, object]) -> None:
                    row['value'] = 'text'
                def consume_nested(rows: tuple[Source]) -> None:
                    rows[0]['value'] = 'text'
                @overload
                def f(*, value: int) -> None: ...
                @overload
                def f() -> None: ...
                def f(**kwargs: Unpack[Source]) -> None:
                    {body}
            "},
            )?;
            let f = function(&db);
            let ordinary = crate::types::check_types(&db, f.program_file(&db));
            assert!(ordinary.is_empty(), "{ordinary:#?}");
            for index in [0, 1, 0] {
                let result = check_overload_body(&db, f, index);
                if supported {
                    let diagnostics = result.unwrap();
                    assert!(diagnostics.is_empty(), "{body}: {diagnostics:#?}");
                } else {
                    assert_eq!(result, Err(BodyDomainError::Unsupported), "{body}");
                }
            }
        }
        Ok(())
    }

    #[test]
    fn body_domains_invalidate_keyword_read_facts_after_escape() -> anyhow::Result<()> {
        let mut db = setup_db();
        let source = indoc::indoc! {"
            from typing import overload
            from typing_extensions import TypedDict, NotRequired, Unpack
            class Source(TypedDict, extra_items=object):
                value: NotRequired[object]
            def consume(row: Source) -> None:
                row['value'] = 'text'
            @overload
            def f(*, value: int) -> int: ...
            @overload
            def f(*, value: str) -> str: ...
            def f(**kwargs: Unpack[Source]) -> object:
                pass
                key = 'value'
                return kwargs[key]
        "};
        for (mutation, wrong) in [
            ("pass", false),
            ("consume(kwargs)", true),
            ("copied: Source = dict(kwargs)\n    consume(copied)", false),
            ("pass", false),
        ] {
            for read in ["kwargs[key]", "kwargs.get(key)"] {
                db.write_file(
                    "/src/body.py",
                    source
                        .replace("    pass", &format!("    {mutation}"))
                        .replace("kwargs[key]", read),
                )?;
                let f = function(&db);
                let ordinary = crate::types::check_types(&db, f.program_file(&db));
                assert!(ordinary.is_empty(), "{ordinary:#?}");
                for index in [0, 1, 0] {
                    let diagnostics = check_overload_body(&db, f, index).unwrap();
                    assert_eq!(
                        !diagnostics.is_empty(),
                        wrong,
                        "{mutation}; {read}, {index}: {diagnostics:#?}"
                    );
                    assert!(
                        diagnostics
                            .diagnostics()
                            .iter()
                            .all(|diagnostic| diagnostic.id().as_str() == "invalid-return-type")
                    );
                    assert_eq!(
                        crate::types::check_types(&db, f.program_file(&db)),
                        ordinary
                    );
                }
            }
        }
        Ok(())
    }

    #[test]
    fn body_domains_decline_raw_keyword_returns() -> anyhow::Result<()> {
        let mut db = setup_db();
        for body in [
            "return kwargs",
            "alias = kwargs\n    return alias",
            "return (kwargs,)",
        ] {
            db.write_file(
                "/src/body.py",
                indoc::formatdoc! {"
                from typing import overload
                from typing_extensions import TypedDict, NotRequired, Unpack
                class Source(TypedDict, closed=True):
                    value: NotRequired[object]
                class Narrow(TypedDict, closed=True):
                    value: int
                @overload
                def f(*, value: int) -> Narrow: ...
                @overload
                def f() -> Source: ...
                def f(**kwargs: Unpack[Source]) -> object:
                    {body}
            "},
            )?;
            let f = function(&db);
            assert!(crate::types::check_types(&db, f.program_file(&db)).is_empty());
            for index in [0, 1] {
                assert_eq!(
                    check_overload_body(&db, f, index),
                    Err(BodyDomainError::Unsupported),
                    "{body}"
                );
            }
        }
        Ok(())
    }

    #[test]
    fn body_domains_do_not_report_specialized_redundancy() -> anyhow::Result<()> {
        let mut db = setup_db();
        let source = indoc::indoc! {"
            from typing import overload
            @overload
            def f(always: None, value: None) -> None: ...
            @overload
            def f(always: None, value: str) -> str: ...
            def f(always: None, value: None | str) -> None | str:
                if not value:
                    return value
                return value
        "};
        for (body, expected) in [
            ("return value", &[][..]),
            ("return 'bad'", &["invalid-return-type"][..]),
        ] {
            db.write_file("/src/body.py", source.replacen("return value", body, 1))?;
            let f = function(&db);
            let diagnostics = check_overload_body(&db, f, 0).unwrap();
            let ids: Vec<_> = diagnostics
                .diagnostics()
                .iter()
                .map(|d| d.id().as_str())
                .collect();
            assert_eq!(ids, expected, "{diagnostics:#?}");
        }
        // Ordinary conditions still warn, and specializing inputs cannot consume an ignore.
        for (condition, expected) in [
            ("if always:", "redundant-condition"),
            (
                "if not value:  # ty: ignore[redundant-condition]",
                "unused-ignore-comment",
            ),
        ] {
            db.write_file("/src/body.py", source.replace("if not value:", condition))?;
            let f = function(&db);
            let diagnostics = check_types_with_overload_bodies(&db, f.program_file(&db), [], [f]);
            let ids: Vec<_> = diagnostics.iter().map(|d| d.id().as_str()).collect();
            assert_eq!(ids, [expected], "{diagnostics:#?}");
        }
        Ok(())
    }

    #[test]
    fn body_domain_projects_keyword_rows() -> anyhow::Result<()> {
        let mut db = setup_db();
        let source = indoc::indoc! {"
            from typing import overload
            from typing_extensions import NotRequired, TypedDict, Unpack
            class First(TypedDict, closed=True):
                value: int
                note: NotRequired[str]
            class Second(TypedDict, closed=True):
                value: str
            @overload
            def f(**kwargs: Unpack[First]) -> First: ...
            @overload
            def f(**kwargs: Unpack[Second]) -> Second: ...
            def f(**kwargs: object) -> object:
                return dict(kwargs)
        "};
        for result in ["dict(kwargs)", "42", "dict(kwargs)"] {
            db.write_file(
                "/src/body.py",
                source.replace("return dict(kwargs)", &format!("return {result}")),
            )?;
            let f = function(&db);
            let signature = f.last_definition_signature(&db).clone();
            let ordinary = crate::types::check_types(&db, f.program_file(&db));
            for index in [0, 1, 0] {
                let domain = prepare_body_domain(&db, f, index).unwrap();
                let [(definition, entry)] = domain.parameters(&db).as_ref() else {
                    panic!("expected one source kwargs binding");
                };
                assert_eq!(definition.scope(&db), domain.scope(&db));
                let env = ProgramEnvironment::from_scope(domain.scope(&db));
                assert!(
                    entry.is_equivalent_to(&db, &env, domain.return_type(&db)),
                    "{}",
                    entry.display(&db, &env)
                );
                let diagnostics = check_overload_body(&db, f, index).unwrap();
                assert_eq!(
                    diagnostics.diagnostics().len(),
                    usize::from(result == "42"),
                    "{diagnostics:#?}"
                );
                if result == "42" {
                    assert_eq!(
                        diagnostics.diagnostics()[0].id().as_str(),
                        "invalid-return-type"
                    );
                } else {
                    assert!(returned_type(&db, f, Some(domain)).is_equivalent_to(
                        &db,
                        &ProgramEnvironment::from_scope(domain.scope(&db)),
                        *entry
                    ));
                }
                assert_eq!(f.last_definition_signature(&db), &signature);
                assert_eq!(
                    crate::types::check_types(&db, f.program_file(&db)),
                    ordinary
                );
            }
        }
        Ok(())
    }

    #[test]
    fn body_domain_captures_fixed_keywords() -> anyhow::Result<()> {
        let mut db = setup_db();
        for (row, type_parameters) in [
            ("Row[T](TypedDict, closed=True)", "[T]"),
            ("Row(TypedDict, Generic[T], closed=True)", ""),
        ] {
            for annotation in [": object", ""] {
                db.write_file(
                    "/src/body.py",
                    indoc::formatdoc! {"
                from typing import Generic, TypeVar, overload
                from typing_extensions import NotRequired, TypedDict
                T = TypeVar('T')
                class {row}:
                    value: T
                    note: NotRequired[str]
                class Empty(TypedDict, closed=True):
                    pass
                @overload
                def f{type_parameters}(owner: int, /, *, value: T, note: str = '') -> Row[T]: ...
                @overload
                def f(owner: str, /) -> Empty: ...
                def f(owner: object, /, **kwargs{annotation}) -> object:
                    return dict(kwargs)
            "},
                )?;
                let f = function(&db);
                for index in [0, 1, 0] {
                    let domain = prepare_body_domain(&db, f, index).unwrap();
                    let [(_, _), (definition, entry)] = domain.parameters(&db).as_ref() else {
                        panic!("expected owner and kwargs source bindings");
                    };
                    assert_eq!(definition.scope(&db), domain.scope(&db));
                    let env = ProgramEnvironment::from_scope(domain.scope(&db));
                    assert!(
                        entry.is_equivalent_to(&db, &env, domain.return_type(&db)),
                        "{}",
                        entry.display(&db, &env)
                    );
                    assert!(returned_type(&db, f, Some(domain)).is_equivalent_to(
                        &db,
                        &ProgramEnvironment::from_scope(domain.scope(&db)),
                        *entry
                    ));
                    let diagnostics = check_overload_body(&db, f, index).unwrap();
                    assert!(diagnostics.is_empty(), "{diagnostics:#?}");
                }
            }
        }
        Ok(())
    }

    #[test]
    fn body_domain_keyword_entries_retain_source_declarations() -> anyhow::Result<()> {
        let mut db = setup_db();
        db.write_file(
            "/src/body.py",
            indoc::indoc! {"
            from typing import overload
            from typing_extensions import NotRequired, TypedDict, Unpack
            class Source(TypedDict, closed=True):
                value: NotRequired[object]
            class Required(TypedDict, closed=True):
                value: int
            class Empty(TypedDict, closed=True):
                pass
            @overload
            def f(*, value: int) -> Required: ...
            @overload
            def f() -> Empty: ...
            def f(**kwargs: Unpack[Source]) -> object:
                return dict(kwargs)
        "},
        )?;
        let f = function(&db);
        for index in [0, 1, 0] {
            let domain = prepare_body_domain(&db, f, index).unwrap();
            let [(definition, entry)] = domain.parameters(&db).as_ref() else {
                panic!("expected the original kwargs definition");
            };
            let ordinary_declaration =
                infer_definition_types(&db, *definition).inferred_declaration(*definition);
            assert_eq!(
                infer_body_definition(&db, *definition, domain).inferred_declaration(*definition),
                ordinary_declaration
            );
            assert!(returned_type(&db, f, Some(domain)).is_equivalent_to(
                &db,
                &ProgramEnvironment::from_scope(domain.scope(&db)),
                *entry
            ));
            let diagnostics = check_overload_body(&db, f, index).unwrap();
            assert!(diagnostics.is_empty(), "{diagnostics:#?}");
        }
        Ok(())
    }

    #[test]
    fn body_domain_keyword_residual_excludes_fixed_defaults() -> anyhow::Result<()> {
        let mut db = setup_db();
        db.write_file(
            "/src/body.py",
            indoc::indoc! {"
            from typing import Literal, overload
            @overload
            def f(mode: Literal[0], /, *, fixed: str = 'donor', **kwargs: int) -> str: ...
            @overload
            def f(mode: Literal[1], /, *, fixed: str = 'donor', **kwargs: str) -> str: ...
            def f(mode: int, /, *, fixed: str = 'source', **kwargs: object) -> str:
                return fixed
        "},
        )?;
        let f = function(&db);
        for index in [0, 1] {
            let domain = prepare_body_domain(&db, f, index).unwrap();
            let env = ProgramEnvironment::from_scope(domain.scope(&db));
            assert_eq!(
                returned_type(&db, f, Some(domain)),
                KnownClass::Str.to_instance(&db, &env)
            );
            let diagnostics = check_overload_body(&db, f, index).unwrap();
            assert!(diagnostics.is_empty(), "{diagnostics:#?}");
        }
        Ok(())
    }

    #[test]
    fn body_domain_declines_keyword_mutations() -> anyhow::Result<()> {
        let mut db = setup_db();
        db.write_dedented(
            "/src/body.py",
            "
            from typing import overload
            from typing_extensions import NotRequired, TypedDict, Unpack
            class Source(TypedDict, closed=True):
                value: NotRequired[object]
            @overload
            def f(*, value: int) -> None: ...
            @overload
            def f() -> None: ...
            def f(**kwargs: Unpack[Source]) -> None:
                kwargs['value'] = 'allowed by the source declaration'
        ",
        )?;
        let f = function(&db);
        assert!(crate::types::check_types(&db, f.program_file(&db)).is_empty());
        // The fresh entry can have a narrower field than the original mutable declaration.
        // Direct writes remain outside admission; copied dictionaries use ordinary write checks.
        for index in [0, 1] {
            assert_eq!(
                check_overload_body(&db, f, index).unwrap_err(),
                BodyDomainError::Unsupported
            );
        }
        db.write_dedented(
            "/src/body.py",
            "
            from typing import overload
            @overload
            def f(*, value: int) -> None: ...
            @overload
            def f() -> None: ...
            def f(**kwargs: object) -> None:
                kwargs = 42
        ",
        )?;
        for index in [0, 1] {
            let diagnostics = check_overload_body(&db, function(&db), index).unwrap();
            assert_eq!(diagnostics.diagnostics().len(), 1, "{diagnostics:#?}");
            assert_eq!(
                diagnostics.diagnostics()[0].id().as_str(),
                "invalid-assignment"
            );
        }
        Ok(())
    }

    #[test]
    fn body_domain_preserves_keyword_residuals() -> anyhow::Result<()> {
        let mut db = setup_db();
        for residual in ["int", "Any", "Unknown"] {
            db.write_file(
                "/src/body.py",
                indoc::formatdoc! {"
                from typing import Any, Literal, overload
                from ty_extensions import Unknown
                @overload
                def f(mode: Literal[0], /, **kwargs: {residual}) -> dict[str, {residual}]: ...
                @overload
                def f(mode: Literal[1], /, **kwargs: str) -> dict[str, str]: ...
                def f(mode: int, /, **kwargs: object) -> object:
                    return kwargs
            "},
            )?;
            let f = function(&db);
            let signature = f.last_definition_signature(&db).clone();
            for index in [0, 1, 0] {
                // Gradual return promises are intentionally unsupported. Observe the projected
                // entry directly in those cases without claiming a completed body check.
                let overload = &f.overloads_and_implementation(&db).0[index];
                let implementation = f.literal(&db).last_definition;
                let scope = implementation.body_scope(&db);
                let module = parsed_module(&db, scope.program_file(&db).python_file(&db)).load(&db);
                let node = scope.node(&db).expect_function().node(&module);
                let env = ProgramEnvironment::from_scope(scope);
                let projected = project_body_parameters(
                    &db,
                    &env,
                    scope,
                    &node.parameters,
                    &signature,
                    &overload.raw_signature(&db, ReturnCallableTypeVarScope::Lexical),
                    None,
                )
                .unwrap();
                let [(_, _), (_, entry)] = projected.as_ref() else {
                    panic!("expected mode and kwargs source bindings");
                };
                assert_eq!(
                    *entry,
                    overload
                        .raw_signature(&db, ReturnCallableTypeVarScope::Lexical)
                        .return_ty
                );
                if residual == "int" || index == 1 {
                    assert_eq!(
                        check_overload_body(&db, f, index),
                        Err(BodyDomainError::Unsupported)
                    );
                }
            }
        }
        Ok(())
    }

    #[test]
    fn body_domain_declines_residual_fixed_slot_ownership() -> anyhow::Result<()> {
        let mut db = setup_db();
        db.write_file(
            "/src/body.py",
            indoc::indoc! {"
            from typing import Literal, overload
            @overload
            def f(mode: Literal[0], /, **kwargs: int) -> object: ...
            @overload
            def f(mode: Literal[1], /, **kwargs: int) -> object: ...
            def f(mode: int, /, value: int = 0, **kwargs: int) -> object:
                return kwargs
        "},
        )?;
        for index in [0, 1] {
            assert_eq!(
                check_overload_body(&db, function(&db), index),
                Err(BodyDomainError::Unsupported)
            );
        }
        Ok(())
    }

    #[test]
    fn body_domain_checks_generic_callback_keywords() -> anyhow::Result<()> {
        let mut db = setup_db();
        let source = indoc::indoc! {r#"
            from typing import Protocol, overload
            class TagsRule[T: str](Protocol):
                def __call__(self, *args, tags: list[T], **kwargs) -> object: ...
            class DataRule[D, T: str](Protocol):
                def __call__(self, *args, data: D, tags: list[T], **kwargs) -> object: ...
            @overload
            def f[D: list[str] | tuple[str, ...], Over: str](rule: DataRule[D, Over], data: D, tags: list[Over]) -> None: ...
            @overload
            def f(rule: DataRule[int, str], data: int, tags: list[str]) -> None: ...
            def f[Impl: str](rule: TagsRule[Impl], data: list[str] | tuple[str, ...] | int, tags: list[Impl]) -> None:
                copied: list[Impl] = tags
                rule(data=data, tags=copied)
        "#};
        for value in ["data", "tags", "42", "data"] {
            db.write_file(
                "/src/body.py",
                source.replace("rule(data=data", &format!("rule(data={value}")),
            )?;
            let f = function(&db);
            let signature = f.last_definition_signature(&db).clone();
            let ordinary = crate::types::check_types(&db, f.program_file(&db));
            assert!(ordinary.is_empty(), "{ordinary:#?}");
            for index in [0, 1, 0] {
                let diagnostics = check_overload_body(&db, f, index).unwrap();
                let wrong = value == "tags" || value == "42" && index == 0;
                assert_eq!(
                    diagnostics.diagnostics().len(),
                    usize::from(wrong),
                    "{value} domain {index}: {diagnostics:#?}"
                );
                if wrong {
                    assert_eq!(
                        diagnostics.diagnostics()[0].id().as_str(),
                        "invalid-argument-type"
                    );
                }
                assert_eq!(f.last_definition_signature(&db), &signature);
                assert_eq!(
                    crate::types::check_types(&db, f.program_file(&db)),
                    ordinary
                );
            }
        }
        Ok(())
    }

    #[test]
    fn body_domain_checks_legacy_callback_correlation() -> anyhow::Result<()> {
        let mut db = setup_db();
        for argument in ["value", "wrong"] {
            db.write_file(
                "/src/body.py",
                indoc::formatdoc! {"
                from typing import Callable, TypeVar, overload
                D = TypeVar('D')
                @overload
                def f(rule: Callable[[D], None], value: D, wrong: str) -> None: ...
                @overload
                def f(rule: Callable[[int], None], value: int, wrong: int) -> None: ...
                def f(rule: Callable[..., None], value: object, wrong: object) -> None:
                    rule({argument})
            "},
            )?;
            let f = function(&db);
            let domain = prepare_body_domain(&db, f, 0).unwrap();
            let definition = domain.parameters(&db)[0].0;
            assert_eq!(
                infer_body_definition(&db, definition, domain)
                    .inferred_declaration(definition)
                    .declared()
                    .unwrap()
                    .inner_type(),
                f.last_definition_signature(&db).parameters()[0].annotated_type(),
            );
            let diagnostics = check_overload_body(&db, f, 0).unwrap();
            assert_eq!(
                diagnostics.diagnostics().len(),
                usize::from(argument == "wrong"),
                "{diagnostics:#?}"
            );
            if argument == "wrong" {
                assert_eq!(
                    diagnostics.diagnostics()[0].id().as_str(),
                    "invalid-argument-type"
                );
            }
        }
        Ok(())
    }

    #[test]
    fn body_domain_call_ranges_isolate_terminal_callbacks() -> anyhow::Result<()> {
        let mut db = setup_db();
        let calls = "    callback()\n".repeat(64);
        db.write_file("/src/body.py", format!("from typing import Callable, NoReturn as Never, overload\n@overload\ndef f(callback: Callable[[], Never], value: int) -> int: ...\n@overload\ndef f(callback: Callable[[], None], value: str) -> str: ...\ndef f(callback: Callable[[], None], value: int | str) -> int | str:\n{calls}    return 42\n"))?;
        let f = function(&db);
        let ordinary = crate::types::check_types(&db, f.program_file(&db));
        assert!(ordinary.is_empty(), "{ordinary:#?}");
        for index in [0, 1, 0] {
            let diagnostics = check_overload_body(&db, f, index).unwrap();
            assert_eq!(diagnostics.diagnostics().len(), index, "{diagnostics:#?}");
            if index == 1 {
                assert_eq!(
                    diagnostics.diagnostics()[0].id().as_str(),
                    "invalid-return-type"
                );
            }
            assert_eq!(
                crate::types::check_types(&db, f.program_file(&db)),
                ordinary
            );
        }
        let events = db.take_salsa_events();
        for query in [
            "analyze_body_non_terminal_call",
            "analyze_body_non_terminal_call_range",
        ] {
            assert!(
                ruff_db::testing::find_will_execute_event_by_name(&db, query, None, &events)
                    .is_some(),
                "{query}"
            );
        }
        Ok(())
    }

    #[test]
    fn body_domain_preserves_gradual_inputs_and_declines_gradual_defaults() -> anyhow::Result<()> {
        let mut db = setup_db();
        for annotation in ["Any", "Unknown"] {
            db.write_file(
                "/src/body.py",
                indoc::formatdoc! {"
                from typing import Any, overload
                from ty_extensions._internal import Unknown
                @overload
                def f(value: {annotation}) -> object: ...
                @overload
                def f(value: int) -> int: ...
                def f(value: object) -> object:
                    return value
            "},
            )?;
            let f = function(&db);
            let domain = prepare_body_domain(&db, f, 0).unwrap();
            assert_eq!(
                returned_type(&db, f, Some(domain))
                    .display(&db, &db.program_environment())
                    .to_string(),
                annotation
            );
            assert!(check_overload_body(&db, f, 0).unwrap().is_empty());
            db.write_file(
                "/src/body.py",
                indoc::formatdoc! {"
                from typing import Any, overload
                from ty_extensions._internal import Unknown
                default: {annotation}
                @overload
                def f(value: {annotation} = ...) -> object: ...
                @overload
                def f(value: int) -> int: ...
                def f(value: object = default) -> object:
                    return value
            "},
            )?;
            assert_eq!(
                check_overload_body(&db, function(&db), 0).unwrap_err(),
                BodyDomainError::Unsupported
            );
        }
        Ok(())
    }

    #[test]
    fn body_domains_combine_calls_and_conditions() -> anyhow::Result<()> {
        let mut db = setup_db();
        for body in [
            "    callback()\n    if flag:\n        return 1\n    return 0",
            "    return callback() == 1",
            "    return 1 if not flag or 0 < callback() < 2 else 0",
        ] {
            db.write_file("/src/body.py", format!("from typing import Callable, Literal, overload\n@overload\ndef f(callback: Callable[[], int], flag: Literal[True]) -> int: ...\n@overload\ndef f(callback: Callable[[], int], flag: Literal[False]) -> int: ...\ndef f(callback: Callable[[], int], flag: bool) -> int:\n{body}\n"))?;
            let f = function(&db);
            for index in [0, 1, 0] {
                let diagnostics = check_overload_body(&db, f, index).unwrap();
                assert!(diagnostics.is_empty(), "{body}: {diagnostics:#?}");
            }
        }
        Ok(())
    }

    #[test]
    fn body_domains_evaluate_chained_comparisons() -> anyhow::Result<()> {
        let mut db = setup_db();
        for body in [
            "if 0 < value < 2:\n        return 'small'\n    return 1",
            "return 'small' if 0 < value < 2 else 1",
        ] {
            db.write_file("/src/body.py", format!("from typing import Literal, overload\n@overload\ndef f(value: Literal[1]) -> str: ...\n@overload\ndef f(value: Literal[3]) -> int: ...\ndef f(value: int) -> int | str:\n    {body}\n"))?;
            let f = function(&db);
            let ordinary = crate::types::check_types(&db, f.program_file(&db));
            assert!(ordinary.is_empty(), "{ordinary:#?}");
            for index in [0, 1, 0] {
                let diagnostics = check_overload_body(&db, f, index).unwrap();
                assert!(diagnostics.is_empty(), "{body}: {diagnostics:#?}");
                assert_eq!(
                    crate::types::check_types(&db, f.program_file(&db)),
                    ordinary
                );
            }
        }
        Ok(())
    }

    #[test]
    fn body_domains_preserve_dictionary_aliases() -> anyhow::Result<()> {
        let mut db = setup_db();
        db.write_dedented(
            "/src/body.py",
            "
            from typing import overload
            @overload
            def f(value: dict[str, int]) -> dict[str, int]: ...
            @overload
            def f(value: dict[str, str]) -> dict[str, str]: ...
            def f(value: dict[str, int] | dict[str, str]) -> dict[str, int] | dict[str, str]:
                copied = value
                return copied
        ",
        )?;
        let f = function(&db);
        for index in [0, 1, 0] {
            let domain = prepare_body_domain(&db, f, index).unwrap();
            assert_eq!(returned_type(&db, f, Some(domain)), domain.return_type(&db));
        }
        Ok(())
    }

    #[test]
    fn body_domains_narrow_saved_predicates() -> anyhow::Result<()> {
        let mut db = setup_db();
        let source = indoc::indoc! {"
            from typing import Literal, overload
            @overload
            def f(value: int | None, other: Literal[False]) -> int: ...
            @overload
            def f(value: int | None, other: Literal[True]) -> int | None: ...
            def f(value: int | None, other: bool) -> int | None:
                check = False
                if not other:
                    check = value is None
                if check:
                    return 0
                return value
        "};
        db.write_file("/src/body.py", source)?;
        let f = function(&db);
        let ordinary = returned_type(&db, f, None);
        for index in [0, 1, 0] {
            let domain = prepare_body_domain(&db, f, index).unwrap();
            let diagnostics = check_overload_body(&db, f, index).unwrap();
            assert!(diagnostics.is_empty(), "{index}: {diagnostics:#?}");
            assert_eq!(returned_type(&db, f, Some(domain)), domain.return_type(&db));
            assert_eq!(returned_type(&db, f, None), ordinary);
        }
        db.write_file("/src/body.py", source.replace("if not other:", "if other:"))?;
        let diagnostics = check_overload_body(&db, function(&db), 0).unwrap();
        assert_eq!(diagnostics.diagnostics().len(), 1, "{diagnostics:#?}");
        assert_eq!(
            diagnostics.diagnostics()[0].id().as_str(),
            "invalid-return-type"
        );
        Ok(())
    }

    #[test]
    fn body_domains_narrow_after_terminal_calls() -> anyhow::Result<()> {
        let mut db = setup_db();
        db.write_dedented(
            "/src/body.py",
            "
            from typing import Callable, overload
            from typing_extensions import Never
            @overload
            def f(callback: Callable[[], Never], value: int | None) -> int: ...
            @overload
            def f(callback: Callable[[], None], value: int | None) -> int | None: ...
            def f(callback: Callable[[], None], value: int | None) -> int | None:
                if value is None:
                    callback()
                return value
        ",
        )?;
        let f = function(&db);
        let ordinary = returned_type(&db, f, None);
        for index in [0, 1, 0] {
            let domain = prepare_body_domain(&db, f, index).unwrap();
            let diagnostics = check_overload_body(&db, f, index).unwrap();
            assert!(diagnostics.is_empty(), "{index}: {diagnostics:#?}");
            assert_eq!(returned_type(&db, f, Some(domain)), domain.return_type(&db));
            assert_eq!(returned_type(&db, f, None), ordinary);
        }
        Ok(())
    }

    #[test]
    fn body_domains_isolate_projected_narrowing_checkpoints() -> anyhow::Result<()> {
        let mut db = setup_db();
        let mut guards = String::new();
        let mut pads = String::new();
        for index in 0..64 {
            writeln!(
                guards,
                "        if pad{index} and value is not None:\n            return None"
            )?;
            write!(pads, ", pad{index}: bool")?;
        }
        let source = format!(
            "from typing import Literal, overload\n@overload\ndef f(value: int | None, other: Literal[False]{pads}) -> None: ...\n@overload\ndef f(value: int | None, other: Literal[True]{pads}) -> int | None: ...\ndef f(value: int | None, other: bool{pads}) -> int | None:\n    if other or value is None:\n{guards}        return value\n    return None\n"
        );
        db.write_file("/src/body.py", &source)?;
        let f = function(&db);
        let ordinary = crate::types::check_types(&db, f.program_file(&db));
        assert!(ordinary.is_empty(), "{ordinary:#?}");
        for index in [0, 1, 0] {
            let diagnostics = check_overload_body(&db, f, index).unwrap();
            assert!(diagnostics.is_empty(), "{index}: {diagnostics:#?}");
            assert_eq!(
                crate::types::check_types(&db, f.program_file(&db)),
                ordinary
            );
        }
        let events = db.take_salsa_events();
        for query in [
            "all_body_narrowing_constraints_for_expression",
            "evaluate_body_projected_narrowing_checkpoint",
        ] {
            assert!(
                ruff_db::testing::find_will_execute_event_by_name(&db, query, None, &events)
                    .is_some(),
                "{query}"
            );
        }
        // The value parameter has the same base type in both domains. A cached None projection
        // from the first domain must not satisfy this false promise in the second domain.
        db.write_file(
            "/src/body.py",
            source.replace(") -> int | None: ...", ") -> None: ..."),
        )?;
        let f = function(&db);
        assert!(check_overload_body(&db, f, 0).unwrap().is_empty());
        let diagnostics = check_overload_body(&db, f, 1).unwrap();
        assert_eq!(diagnostics.diagnostics().len(), 1, "{diagnostics:#?}");
        assert_eq!(
            diagnostics.diagnostics()[0].id().as_str(),
            "invalid-return-type"
        );
        Ok(())
    }

    #[test]
    fn body_domain_declines_local_factories_and_reassigned_callees() -> anyhow::Result<()> {
        let mut db = setup_db();
        for (annotation, body) in [
            (
                "Callable[..., object]",
                "factory = NewType\n    Alias = factory('Alias', str)",
            ),
            (
                "Callable[..., object]",
                "callback = NewType\n    Alias = callback('Alias', str)",
            ),
            (
                "Callable[..., object]",
                "if flag:\n        callback = NewType\n    Alias = callback('Alias', str)",
            ),
            (
                "Callable[..., object]",
                "if flag:\n        factory = NewType\n        Alias = factory('Alias', str)",
            ),
            (
                "Callable[..., object]",
                "if flag:\n        new_class = callback\n    Alias = new_class('Alias')",
            ),
            ("type[NewType]", "Alias = callback('Alias', str)"),
            ("Callable[..., object]", "Alias = new_class('Alias')"),
            (
                "Callable[..., object]",
                "Alias = namedtuple('Alias', 'field')",
            ),
        ] {
            db.write_file("/src/body.py", format!("from typing import Callable, Literal, NewType, overload\nfrom types import new_class\nfrom collections import namedtuple\n@overload\ndef f(callback: {annotation}, flag: Literal[True]) -> None: ...\n@overload\ndef f(callback: {annotation}, flag: Literal[False]) -> None: ...\ndef f(callback: {annotation}, flag: bool) -> None:\n    {body}\n"))?;
            assert_eq!(
                check_overload_body(&db, function(&db), 0).unwrap_err(),
                BodyDomainError::Unsupported
            );
        }
        Ok(())
    }

    #[test]
    fn generic_body_domains_specialize_declarations() -> anyhow::Result<()> {
        let mut db = setup_db();
        for legacy in [false, true] {
            let (variables, overload_binder, implementation_binder) = if legacy {
                (
                    "Over = TypeVar('Over', bound=str)\nImpl = TypeVar('Impl')",
                    "",
                    "",
                )
            } else {
                ("", "[Over: str]", "[Impl]")
            };
            for (future, annotation) in [
                ("", "Impl"),
                ("", "'Impl'"),
                ("from __future__ import annotations", "Impl"),
            ] {
                let source = indoc::formatdoc! {"
                    {future}
                    from typing import TypeVar, overload
                    {variables}
                    @overload
                    def f{overload_binder}(value: Over) -> Over: ...
                    @overload
                    def f(value: int) -> int: ...
                    def f{implementation_binder}(value: Impl) -> Impl:
                        copied: {annotation} = value
                        return copied
                    integer = f(1)
                    text = f('ok')
                "};
                db.write_file("/src/body.py", &source)?;
                let f = function(&db);
                let signature = f.last_definition_signature(&db).clone();
                let ordinary_return = returned_type(&db, f, None);
                let ordinary = crate::types::check_types(&db, f.program_file(&db));
                assert!(ordinary.is_empty(), "{ordinary:#?}");
                for index in [0, 1, 0] {
                    let domain = prepare_body_domain(&db, f, index).unwrap();
                    assert!(domain.specialization(&db).is_some());
                    assert_eq!(returned_type(&db, f, Some(domain)), domain.return_type(&db));
                    let diagnostics = check_overload_body(&db, f, index).unwrap();
                    assert!(diagnostics.is_empty(), "{diagnostics:#?}");
                    assert_eq!(returned_type(&db, f, None), ordinary_return);
                    assert_eq!(f.last_definition_signature(&db), &signature);
                    assert_eq!(
                        crate::types::check_types(&db, f.program_file(&db)),
                        ordinary
                    );
                }
                for (name, expected) in [("integer", "int"), ("text", "Literal[\"ok\"]")] {
                    let ty = crate::place::global_symbol(&db, f.program_file(&db), name)
                        .place
                        .expect_type();
                    assert_eq!(
                        ty.display(&db, &db.program_environment()).to_string(),
                        expected
                    );
                }
                for target in ["copied", "value"] {
                    db.write_file(
                        "/src/body.py",
                        source.replace(
                            "return copied",
                            &format!("{target} = 42\n    return copied"),
                        ),
                    )?;
                    let f = function(&db);
                    assert!(check_overload_body(&db, f, 1).unwrap().is_empty());
                    let diagnostics = check_overload_body(&db, f, 0).unwrap().into_diagnostics();
                    assert_eq!(diagnostics.len(), 1, "{diagnostics:#?}");
                    assert_eq!(diagnostics[0].id().as_str(), "invalid-assignment");
                }
            }
        }
        Ok(())
    }

    #[test]
    fn generic_body_domains_decline_unrepresented_inputs_and_aliases() -> anyhow::Result<()> {
        let mut db = setup_db();
        for extra in ["", ", *, extra: Never = ..."] {
            db.write_file(
                "/src/body.py",
                indoc::formatdoc! {"
                from typing import overload
                from typing_extensions import Never
                @overload
                def f[Over: str](value: Over{extra}) -> Over: ...
                @overload
                def f(value: int, *, extra: int = ...) -> int: ...
                def f[Impl](value: Impl, *, extra: int = 1) -> Impl:
                    return value
            "},
            )?;
            assert_eq!(
                check_overload_body(&db, function(&db), 0).unwrap_err(),
                BodyDomainError::Unsupported
            );
            assert!(
                check_overload_body(&db, function(&db), 1)
                    .unwrap()
                    .is_empty()
            );
        }
        for statement in [
            "Alias: TA = str",
            "type Alias = str",
            "Alias = NewType('Alias', str)",
            "Alias = TypeAliasType('Alias', str)",
        ] {
            db.write_file(
                "/src/body.py",
                indoc::formatdoc! {"
                from typing import overload, TypeAlias as TA, NewType
                from typing_extensions import TypeAliasType
                @overload
                def f(value: str) -> str: ...
                @overload
                def f(value: int) -> int: ...
                def f[Impl](value: Impl) -> Impl:
                    {statement}
                    return value
            "},
            )?;
            assert_eq!(
                check_overload_body(&db, function(&db), 0).unwrap_err(),
                BodyDomainError::Unsupported,
                "{statement}"
            );
        }
        Ok(())
    }

    #[test]
    fn generic_body_domains_map_source_default_views() -> anyhow::Result<()> {
        let mut db = setup_db();
        db.write_dedented(
            "/src/body.py",
            "
            from typing import overload
            @overload
            def f[Over: str](value: Over, data: list[Over] = ...) -> list[Over]: ...
            @overload
            def f(value: int, data: list[int] = ...) -> list[int]: ...
            def f[Impl](value: Impl, data: list[Impl] = []) -> list[Impl]:
                copied: list[Impl] = data
                return copied
        ",
        )?;
        let f = function(&db);
        let signature = f.last_definition_signature(&db).clone();
        let raw_default = signature.parameters()[1].default_type(&db).unwrap();
        assert_eq!(
            raw_default
                .display(&db, &db.program_environment())
                .to_string(),
            "list[Impl@f]"
        );
        for index in [0, 1, 0] {
            let domain = prepare_body_domain(&db, f, index).unwrap();
            assert_eq!(returned_type(&db, f, Some(domain)), domain.return_type(&db));
            let diagnostics = check_overload_body(&db, f, index).unwrap();
            assert!(diagnostics.is_empty(), "{diagnostics:#?}");
            assert_eq!(
                signature.parameters()[1].default_type(&db),
                Some(raw_default)
            );
            assert_eq!(f.last_definition_signature(&db), &signature);
        }
        Ok(())
    }

    #[test]
    fn body_domains_project_required_and_omitted_arguments() -> anyhow::Result<()> {
        let mut db = setup_db();
        for positional_only in [false, true] {
            let separator = if positional_only { ", /" } else { "" };
            db.write_file(
                "/src/body.py",
                indoc::formatdoc! {"
                from typing import overload
                @overload
                def f() -> int: ...
                @overload
                def f(value: str{separator}) -> str: ...
                def f(value: int | str = 1{separator}) -> int | str:
                    copied = value
                    return copied
                omitted = f()
                supplied = f('ok')
            "},
            )?;
            let f = function(&db);
            let file = f.program_file(&db);
            let signature = f.last_definition_signature(&db).clone();
            let default = signature.parameters()[0].default_type(&db).unwrap();
            for index in [0, 1, 0] {
                let domain = prepare_body_domain(&db, f, index).unwrap();
                let expected = if index == 0 {
                    default
                } else {
                    crate::types::KnownClass::Str.to_instance(&db, &db.program_environment())
                };
                assert_eq!(returned_type(&db, f, Some(domain)), expected);
                assert!(check_overload_body(&db, f, index).unwrap().is_empty());
                assert!(crate::types::check_types(&db, file).is_empty());
                assert_eq!(f.last_definition_signature(&db), &signature);
                for (name, expected) in [("omitted", "int"), ("supplied", "str")] {
                    let ty = crate::place::global_symbol(&db, file, name)
                        .place
                        .expect_type();
                    assert_eq!(
                        ty.display(&db, &db.program_environment()).to_string(),
                        expected
                    );
                }
            }
        }
        Ok(())
    }

    #[test]
    fn body_domains_include_source_default_for_optional_slots() -> anyhow::Result<()> {
        let mut db = setup_db();
        db.write_dedented(
            "/src/body.py",
            "
            from typing import Literal, overload
            @overload
            def f(flag: Literal[False] = ...) -> str: ...
            @overload
            def f(flag: Literal[True]) -> int: ...
            def f(flag: bool = True) -> int | str:
                if flag:
                    return 1
                return 'no'
        ",
        )?;
        let f = function(&db);
        assert!(crate::types::check_types(&db, f.program_file(&db)).is_empty());
        assert!(check_overload_body(&db, f, 1).unwrap().is_empty());
        let diagnostics = check_overload_body(&db, f, 0).unwrap().into_diagnostics();
        assert_eq!(diagnostics.len(), 1, "{diagnostics:#?}");
        assert_eq!(diagnostics[0].id().as_str(), "invalid-return-type");
        Ok(())
    }

    #[test]
    fn body_domains_project_reordered_keyword_slots() -> anyhow::Result<()> {
        let mut db = setup_db();
        db.write_dedented(
            "/src/body.py",
            "
            from typing import Literal, overload
            @overload
            def f() -> int: ...
            @overload
            def f(*, value: str, flag: Literal[False] = ...) -> str: ...
            def f(*, flag: bool = False, value: int | str = 1) -> int | str:
                if flag:
                    return 1
                return value
        ",
        )?;
        let f = function(&db);
        for index in [1, 0, 1] {
            let diagnostics = check_overload_body(&db, f, index).unwrap();
            assert!(diagnostics.is_empty(), "{diagnostics:#?}");
        }
        assert!(crate::types::check_types(&db, f.program_file(&db)).is_empty());
        Ok(())
    }

    #[test]
    fn body_domains_keep_shared_default_types() -> anyhow::Result<()> {
        let mut db = setup_db();
        let source = indoc::indoc! {r#"
            from typing import overload
            shared: list[int] = [1]
            @overload
            def f() -> list[str]: ...
            @overload
            def f(value: list[str]) -> list[str]: ...
            def f(value: list[int] | list[str] = shared) -> list[int] | list[str]:
                return value
        "#};
        db.write_file("/src/body.py", source)?;
        let f = function(&db);
        let domain = prepare_body_domain(&db, f, 0).unwrap();
        let shared = crate::place::global_symbol(&db, f.program_file(&db), "shared")
            .place
            .expect_type();
        assert_eq!(returned_type(&db, f, Some(domain)), shared);
        assert!(check_overload_body(&db, f, 1).unwrap().is_empty());
        let diagnostics = check_overload_body(&db, f, 0).unwrap().into_diagnostics();
        assert_eq!(diagnostics.len(), 1, "{diagnostics:#?}");
        assert_eq!(diagnostics[0].id().as_str(), "invalid-return-type");
        db.write_file(
            "/src/body.py",
            source.replace("shared: list[int] = [1]", "shared: list[str] = ['ok']"),
        )?;
        assert!(
            check_overload_body(&db, function(&db), 0)
                .unwrap()
                .is_empty()
        );
        Ok(())
    }

    #[test]
    fn body_domains_decline_correlated_omission_and_call_modes() -> anyhow::Result<()> {
        let mut db = setup_db();
        for (source, error) in [
            (
                indoc::indoc! {r#"
            from typing import Literal, overload
            @overload
            def f(a: Literal[True] = ..., b: str = ..., /) -> int: ...
            @overload
            def f(a: Literal[False], b: int, /) -> int: ...
            def f(a: bool = False, b: int | str = 0, /) -> int | str:
                if a:
                    return 1
                return b
        "#},
                BodyDomainError::Unsupported,
            ),
            (
                indoc::indoc! {r#"
            from typing import overload
            @overload
            def f(a: int) -> int: ...
            @overload
            def f(a: str) -> str: ...
            def f(b: int | str = 0, a: int | str = 0) -> int | str:
                return a
        "#},
                BodyDomainError::Inconsistent,
            ),
        ] {
            db.write_file("/src/body.py", source)?;
            assert_eq!(
                check_overload_body(&db, function(&db), 0).unwrap_err(),
                error
            );
        }
        // Signature coverage already declines this family. Projection must also avoid selecting
        // just the positional call's bindings if coverage later admits both calling conventions.
        let f = function(&db);
        let (overloads, implementation) = overload_family(&db, f).unwrap();
        let scope = implementation.body_scope(&db);
        let module = parsed_module(&db, scope.program_file(&db).python_file(&db)).load(&db);
        let node = scope.node(&db).expect_function().node(&module);
        assert_eq!(
            project_body_parameters(
                &db,
                &db.program_environment(),
                scope,
                &node.parameters,
                &implementation.raw_signature(&db, ReturnCallableTypeVarScope::Lexical),
                &overloads[0].raw_signature(&db, ReturnCallableTypeVarScope::Lexical),
                None,
            )
            .unwrap_err(),
            BodyDomainError::Unsupported,
        );
        Ok(())
    }

    #[test]
    fn body_domains_do_not_prove_gradual_defaults() -> anyhow::Result<()> {
        let mut db = setup_db();
        for definition in [
            "shared: Any = None",
            "def shared_value(): ...\nshared = shared_value()",
            "shared = []",
        ] {
            db.write_file(
                "/src/body.py",
                indoc::formatdoc! {"
                from typing import Any, overload
                {definition}
                @overload
                def f() -> str: ...
                @overload
                def f(value: str) -> str: ...
                def f(value: object = shared) -> object:
                    return value
            "},
            )?;
            assert!(
                check_overload_body(&db, function(&db), 1)
                    .unwrap()
                    .is_empty()
            );
            // The body domain never turns an unresolved default into its promised return type.
            assert_eq!(
                check_overload_body(&db, function(&db), 0).unwrap_err(),
                BodyDomainError::Unsupported
            );
        }
        db.write_dedented(
            "/src/body.py",
            "
            from typing import overload
            @overload
            def f(value: int) -> int: ...
            @overload
            def f(value: str) -> str: ...
            def f(value: int | str = None) -> int | str:
                return value
        ",
        )?;
        let f = function(&db);
        let diagnostics = crate::types::check_types(&db, f.program_file(&db));
        assert_eq!(diagnostics.len(), 1, "{diagnostics:#?}");
        assert_eq!(diagnostics[0].id().as_str(), "invalid-parameter-default");
        let _ = check_overload_body(&db, f, 0).unwrap();
        assert_eq!(
            crate::types::check_types(&db, f.program_file(&db)),
            diagnostics
        );
        Ok(())
    }

    #[test]
    fn boolean_return_domains_preserve_parameter_narrowing() -> anyhow::Result<()> {
        let mut db = setup_db();
        db.write_dedented(
            "/src/body.py",
            "
            from typing import Literal, overload
            @overload
            def f(flag: Literal[True]) -> Literal[True]: ...
            @overload
            def f(flag: Literal[False]) -> Literal[False]: ...
            def f(flag: bool) -> bool:
                if flag:
                    return flag
                else:
                    return flag
        ",
        )?;
        for index in [1, 0, 1] {
            let diagnostics = check_overload_body(&db, function(&db), index).unwrap();
            assert!(diagnostics.is_empty(), "{diagnostics:#?}");
        }
        Ok(())
    }

    #[test]
    fn boolean_return_domains_isolate_sparse_checkpoints() -> anyhow::Result<()> {
        let mut db = setup_db();
        let parameters = |annotation: &str| {
            (0..64)
                .map(|index| format!("flag{index}: {annotation}"))
                .collect::<Vec<_>>()
                .join(", ")
        };
        let mut body = String::new();
        for index in 0..64 {
            writeln!(body, "    if flag{index}:\n        return 'set'")?;
        }
        db.write_file("/src/body.py", format!("from typing import Literal, overload\n@overload\ndef f({}) -> int: ...\n@overload\ndef f({}) -> str: ...\ndef f({}) -> int | str:\n{body}    return 0\n", parameters("Literal[False]"), parameters("Literal[True]"), parameters("bool")))?;
        for index in [0, 1, 0] {
            let f = function(&db);
            assert!(crate::types::check_types(&db, f.program_file(&db)).is_empty());
            let diagnostics = check_overload_body(&db, f, index).unwrap();
            assert!(diagnostics.is_empty(), "{diagnostics:#?}");
        }
        let events = db.take_salsa_events();
        assert!(
            ruff_db::testing::find_will_execute_event_by_name(
                &db,
                "evaluate_body_reachability_checkpoint",
                None,
                &events
            )
            .is_some()
        );
        Ok(())
    }

    #[test]
    fn overload_body_aggregation_preserves_suppressions_and_evidence() -> anyhow::Result<()> {
        let mut db = setup_db();
        let source = indoc::indoc! {r#"
            from typing import Literal, overload
            @overload
            def f(flag: Literal[True]) -> int: ...
            @overload
            def f(flag: Literal[False]) -> str: ...
            def f(flag: bool) -> int | str | bytes:
                return b'wrong'
        "#};
        db.write_file("/src/body.py", source)?;
        db.write_file("/src/other.py", source)?;
        let other_file = system_path_to_file(&db, "/src/other.py")?;
        let other_file = ProgramFile::new(&db, other_file, db.program_environment().program(&db));
        let other = crate::place::global_symbol(&db, other_file, "f")
            .place
            .expect_type()
            .expect_function_literal();
        let f = function(&db);
        let file = f.program_file(&db);
        let diagnostics = check_types_with_overload_bodies(&db, file, [], [f, other, f]);
        assert_eq!(diagnostics.len(), 1, "{diagnostics:#?}");
        assert_eq!(diagnostics[0].id().as_str(), "invalid-return-type");
        insta::assert_snapshot!(
            "overload_domain_full",
            DisplayDiagnostics::new(
                &db,
                &DisplayDiagnosticConfig::new("ty").context(0),
                &diagnostics,
            )
        );
        insta::assert_snapshot!(
            "overload_domain_concise",
            DisplayDiagnostics::new(
                &db,
                &DisplayDiagnosticConfig::new("ty").format(DiagnosticFormat::Concise),
                &diagnostics,
            )
        );
        assert!(
            diagnostics[0]
                .sub_diagnostics()
                .iter()
                .flat_map(SubDiagnostic::annotations)
                .any(|annotation| annotation
                    .get_message()
                    .is_some_and(|message| message.contains("str")))
        );
        assert!(check_types_with_overload_bodies(&db, file, [], [other]).is_empty());
        let first = check_overload_body(&db, f, 0).unwrap();
        let second = check_overload_body(&db, f, 1).unwrap();
        let mut merged = TypeCheckDiagnostics::default();
        merged.extend_overload_domains(&first);
        merged.extend_overload_domains(&second);
        let expected = merged.diagnostics().to_vec();
        merged.extend_overload_domains(&first);
        merged.extend_overload_domains(&second);
        assert_eq!(merged.diagnostics(), expected);

        db.write_file(
            "/src/body.py",
            source.replace(
                "return b'wrong'",
                "return b'wrong'  # ty: ignore[invalid-return-type]",
            ),
        )?;
        let f = function(&db);
        let ordinary = crate::types::check_types(&db, f.program_file(&db));
        assert_eq!(ordinary.len(), 1, "{ordinary:#?}");
        assert_eq!(ordinary[0].id().as_str(), "unused-ignore-comment");
        assert!(check_types_with_overload_bodies(&db, f.program_file(&db), [], [f]).is_empty());

        // An ordinary return error retains ownership even when both domains reject that site.
        db.write_file(
            "/src/body.py",
            source.replace("return b'wrong'", "return None"),
        )?;
        let f = function(&db);
        let ordinary = crate::types::check_types(&db, f.program_file(&db));
        assert_eq!(ordinary.len(), 1, "{ordinary:#?}");
        let combined = check_types_with_overload_bodies(&db, f.program_file(&db), [], [f]);
        assert_eq!(combined, ordinary);
        Ok(())
    }

    #[test]
    fn overload_body_aggregation_keeps_callable_details() -> anyhow::Result<()> {
        let mut db = setup_db();
        db.write_dedented("/src/body.py", "
            from typing import Callable, Literal, overload
            def callback(value: int) -> None: ...
            @overload
            def f(flag: Literal[True]) -> Callable[[str], None]: ...
            @overload
            def f(flag: Literal[False]) -> Callable[[bytes], None]: ...
            def f(flag: bool) -> Callable[[str], None] | Callable[[bytes], None] | Callable[[int], None]:
                return callback
        ")?;
        let f = function(&db);
        let combined =
            crate::types::check_types_with_overload_bodies(&db, f.program_file(&db), [], [f]);
        assert_eq!(combined.len(), 1, "{combined:#?}");
        for index in [0, 1] {
            let domain = check_overload_body(&db, f, index).unwrap();
            assert_eq!(domain.diagnostics().len(), 1);
            let details = domain.diagnostics()[0].sub_diagnostics();
            assert!(!details.is_empty());
            for detail in details {
                assert!(combined[0].sub_diagnostics().contains(detail));
            }
        }
        Ok(())
    }

    #[test]
    fn boolean_return_domains_do_not_use_unreachable_suppressions() -> anyhow::Result<()> {
        let mut db = setup_db();
        let source = "from typing import Literal, overload\n@overload\ndef f(flag: Literal[True]) -> int: ...\n@overload\ndef f(flag: Literal[False]) -> str: ...\ndef f(flag: bool) -> int | str:\n    if flag:\n        return 1  # ty: ignore[invalid-return-type]\n    return 'value'\n";
        for (value, expected) in [
            ("1", Some("unused-ignore-comment")),
            ("'wrong'", None),
            ("1", Some("unused-ignore-comment")),
        ] {
            db.write_file(
                "/src/body.py",
                source.replace("return 1", &format!("return {value}")),
            )?;
            let f = function(&db);
            let diagnostics = check_types_with_overload_bodies(&db, f.program_file(&db), [], [f]);
            let actual: Vec<_> = diagnostics
                .iter()
                .map(|diagnostic| diagnostic.id().as_str())
                .collect();
            assert_eq!(actual, expected.into_iter().collect::<Vec<_>>());
        }
        db.write_file(
            "/src/body.py",
            source
                .replace("return 1", "return 'wrong'")
                .replace("  # ty: ignore[invalid-return-type]", ""),
        )?;
        let f = function(&db);
        let diagnostics = check_types_with_overload_bodies(&db, f.program_file(&db), [], [f]);
        assert_eq!(diagnostics.len(), 1, "{diagnostics:#?}");
        assert_eq!(diagnostics[0].id().as_str(), "invalid-return-type");

        db.write_file("/src/body.py", "def f() -> int:\n    if False:\n        return 'wrong'  # ty: ignore[invalid-return-type]\n    return 1\n")?;
        let f = function(&db);
        assert!(crate::types::check_types(&db, f.program_file(&db)).is_empty());
        Ok(())
    }

    #[test]
    fn boolean_return_domains_use_reachable_returns() -> anyhow::Result<()> {
        let mut db = setup_db();
        let source = indoc::indoc! {r#"
            from typing import Literal, overload
            @overload
            def f(*, executable: bool, test: Literal[True]) -> str: ...
            @overload
            def f(*, executable: Literal[True], test: Literal[False]) -> int: ...
            @overload
            def f(*, executable: Literal[False], test: Literal[False]) -> bytes: ...
            @overload
            def f(*, executable: bool, test: bool) -> str | int | bytes: ...
            def f(*, executable: bool, test: bool) -> str | int | bytes:
                if test:
                    return 'test'
                elif executable:
                    return 1
                else:
                    return b'alias'
        "#};
        db.write_file("/src/body.py", source)?;
        for index in [3, 0, 2, 1, 0, 3] {
            let f = function(&db);
            let diagnostics = check_overload_body(&db, f, index)
                .unwrap()
                .into_diagnostics();
            assert!(diagnostics.is_empty(), "domain {index}: {diagnostics:#?}");
            assert!(crate::types::check_types(&db, f.program_file(&db)).is_empty());
        }
        db.write_file(
            "/src/body.py",
            source.replace("return 'test'", "return b'alias'"),
        )?;
        let f = function(&db);
        assert!(crate::types::check_types(&db, f.program_file(&db)).is_empty());
        let diagnostics = check_overload_body(&db, f, 0).unwrap().into_diagnostics();
        assert_eq!(diagnostics.len(), 1, "{diagnostics:#?}");
        assert_eq!(diagnostics[0].id().as_str(), "invalid-return-type");
        for index in [1, 2, 3] {
            assert!(check_overload_body(&db, f, index).unwrap().is_empty());
        }
        Ok(())
    }

    #[test]
    fn boolean_return_domains_check_fallthrough() -> anyhow::Result<()> {
        let mut db = setup_db();
        db.write_dedented(
            "/src/body.py",
            "
            from typing import Literal, overload
            @overload
            def f(flag: Literal[True]) -> int: ...
            @overload
            def f(flag: Literal[False]) -> str: ...
            def f(flag: bool) -> int | str:
                if flag:
                    return 1
        ",
        )?;
        let f = function(&db);
        assert!(check_overload_body(&db, f, 0).unwrap().is_empty());
        let diagnostics = check_overload_body(&db, f, 1).unwrap().into_diagnostics();
        assert_eq!(diagnostics.len(), 1, "{diagnostics:#?}");
        assert_eq!(diagnostics[0].id().as_str(), "invalid-return-type");
        Ok(())
    }

    #[test]
    fn boolean_return_domains_follow_writes_and_aliases() -> anyhow::Result<()> {
        let mut db = setup_db();
        for (body, errors) in [
            (
                "flag = False\n    if flag:\n        return 1\n    return 'ok'",
                1,
            ),
            (
                "if flag:\n        flag = False\n        return 1\n    return 'ok'",
                0,
            ),
            (
                "alias = flag\n    if alias:\n        return 1\n    return 'ok'",
                0,
            ),
        ] {
            db.write_file("/src/body.py", format!("from typing import Literal, overload\n@overload\ndef f(flag: Literal[True]) -> int: ...\n@overload\ndef f(flag: Literal[False]) -> str: ...\ndef f(flag: bool) -> int | str:\n    {body}\n"))?;
            let f = function(&db);
            let diagnostics = check_overload_body(&db, f, 0).unwrap();
            assert_eq!(
                diagnostics.diagnostics().len(),
                errors,
                "{body}: {diagnostics:#?}"
            );
            if errors != 0 {
                assert_eq!(
                    diagnostics.diagnostics()[0].id().as_str(),
                    "invalid-return-type"
                );
            }
            assert!(check_overload_body(&db, f, 1).unwrap().is_empty());
        }
        Ok(())
    }

    #[test]
    fn body_domains_isolate_local_bindings_and_ordinary_queries() -> anyhow::Result<()> {
        let mut db = setup_db();
        db.write_dedented(
            "/src/body.py",
            "
            from typing import overload
            @overload
            def f(value: int) -> int: ...
            @overload
            def f(value: str) -> str: ...
            def f(value: int | str) -> int | str:
                copied = value
                return copied
            int_result = f(1)
            str_result = f('ok')
            bad_result = f(None)
        ",
        )?;
        let function = function(&db);
        let public_type = Type::FunctionLiteral(function);
        let int_domain = prepare_body_domain(&db, function, 0).unwrap();
        let str_domain = prepare_body_domain(&db, function, 1).unwrap();
        let env = db.program_environment();
        let check_public_calls = || {
            for (name, expected) in [("int_result", "int"), ("str_result", "str")] {
                let ty = crate::place::global_symbol(&db, function.program_file(&db), name)
                    .place
                    .expect_type();
                assert_eq!(ty.display(&db, &env).to_string(), expected);
            }
            let diagnostics = crate::types::check_types(&db, function.program_file(&db));
            assert_eq!(diagnostics.len(), 1, "{diagnostics:#?}");
            assert_eq!(diagnostics[0].id().as_str(), "no-matching-overload");
        };
        check_public_calls();
        for (domain, expected) in [
            (None, "int | str"),
            (Some(int_domain), "int"),
            (Some(str_domain), "str"),
            (None, "int | str"),
            (Some(str_domain), "str"),
            (Some(int_domain), "int"),
        ] {
            assert_eq!(
                returned_type(&db, function, domain)
                    .display(&db, &env)
                    .to_string(),
                expected
            );
            assert_eq!(Type::FunctionLiteral(self::function(&db)), public_type);
            check_public_calls();
        }
        assert!(check_overload_body(&db, function, 0).unwrap().is_empty());
        assert!(check_overload_body(&db, function, 1).unwrap().is_empty());
        Ok(())
    }

    #[test]
    fn body_domain_keeps_source_assignment_contract() -> anyhow::Result<()> {
        let mut db = setup_db();
        db.write_dedented(
            "/src/body.py",
            "
            from typing import overload
            @overload
            def f(value: int) -> int: ...
            @overload
            def f(value: str) -> str: ...
            def f(value: int | str) -> int | str:
                value = 42
                copied = value
                return copied
        ",
        )?;
        let function = function(&db);
        assert!(check_overload_body(&db, function, 0).unwrap().is_empty());
        let diagnostics = check_overload_body(&db, function, 1)
            .unwrap()
            .into_diagnostics();
        assert_eq!(diagnostics.len(), 1, "{diagnostics:#?}");
        assert_eq!(diagnostics[0].id().as_str(), "invalid-return-type");
        let domain = prepare_body_domain(&db, function, 1).unwrap();
        assert_eq!(
            returned_type(&db, function, Some(domain))
                .display(&db, &db.program_environment())
                .to_string(),
            "Literal[42]"
        );
        let scope = function.literal(&db).last_definition.body_scope(&db);
        assert!(
            infer_complete_scope_types(&db, scope)
                .diagnostics()
                .is_none_or(crate::types::diagnostic::TypeCheckDiagnostics::is_empty)
        );
        Ok(())
    }

    #[test]
    fn body_domain_rejects_assignment_outside_source_declaration() -> anyhow::Result<()> {
        let mut db = setup_db();
        db.write_dedented(
            "/src/body.py",
            "
            from typing import overload
            @overload
            def f(value: int) -> int: ...
            @overload
            def f(value: str) -> str: ...
            def f(value: int | str) -> int | str:
                value = None
                return 'ok'
        ",
        )?;
        let diagnostics = check_overload_body(&db, function(&db), 1)
            .unwrap()
            .into_diagnostics();
        assert_eq!(diagnostics.len(), 1, "{diagnostics:#?}");
        assert_eq!(diagnostics[0].id().as_str(), "invalid-assignment");
        Ok(())
    }

    #[test]
    fn body_domains_read_generic_members() -> anyhow::Result<()> {
        let mut db = setup_db();
        for declaration in [
            "class Record[T](Protocol):",
            "T = TypeVar('T', covariant=True)\nclass Record(Protocol[T]):",
        ] {
            let source = indoc::formatdoc! {"
            from typing import Protocol, TypeVar, overload
            {declaration}
                @property
                def value(self) -> T: ...
                @property
                def marker(self) -> str: ...
            @overload
            def f(record: Record[int]) -> int: ...
            @overload
            def f(record: Record[str]) -> str: ...
            def f(record: Record[int] | Record[str]) -> object:
                return record.value
        "};
            for member in ["value", "marker", "missing", "value"] {
                db.write_file(
                    "/src/body.py",
                    source.replace("return record.value", &format!("return record.{member}")),
                )?;
                let f = function(&db);
                let ordinary = crate::types::check_types(&db, f.program_file(&db));
                if member != "missing" {
                    assert!(ordinary.is_empty(), "{member}: {ordinary:#?}");
                }
                for index in [0, 1, 0] {
                    let diagnostics = check_overload_body(&db, f, index).unwrap();
                    let expected = match member {
                        "marker" => (index == 0).then_some("invalid-return-type"),
                        "missing" => Some("unresolved-attribute"),
                        _ => None,
                    };
                    assert_eq!(
                        diagnostics
                            .diagnostics()
                            .iter()
                            .map(|diagnostic| diagnostic.id().as_str())
                            .collect::<Vec<_>>(),
                        expected.into_iter().collect::<Vec<_>>(),
                        "{member} domain {index}: {diagnostics:#?}"
                    );
                    assert_eq!(
                        crate::types::check_types(&db, f.program_file(&db)),
                        ordinary
                    );
                }
            }
        }
        Ok(())
    }

    #[test]
    fn body_domains_infer_generic_and_overloaded_calls() -> anyhow::Result<()> {
        let mut db = setup_db();
        for helper in [
            "def identity[T](value: T) -> T:\n    return value",
            "T = TypeVar('T')\ndef identity(value: T) -> T:\n    return value",
            "@overload\ndef identity(value: int) -> int: ...\n@overload\ndef identity(value: str) -> str: ...\ndef identity(value: int | str) -> int | str:\n    return value",
        ] {
            let source = indoc::formatdoc! {"
                from typing import TypeVar, overload
                {helper}
                @overload
                def f(value: int) -> int: ...
                @overload
                def f(value: str) -> str: ...
                def f(value: int | str) -> object:
                    return identity(value)
            "};
            for argument in ["value", "42", "value"] {
                db.write_file(
                    "/src/body.py",
                    source.replace(
                        "return identity(value)",
                        &format!("return identity({argument})"),
                    ),
                )?;
                let f = function(&db);
                let ordinary = crate::types::check_types(&db, f.program_file(&db));
                assert!(ordinary.is_empty(), "{helper}; {argument}: {ordinary:#?}");
                for index in [0, 1, 0] {
                    let diagnostics = check_overload_body(&db, f, index).unwrap();
                    let expected = usize::from(argument == "42" && index == 1);
                    assert_eq!(
                        diagnostics.diagnostics().len(),
                        expected,
                        "{helper}; {argument}; domain {index}: {diagnostics:#?}"
                    );
                    assert!(
                        diagnostics
                            .diagnostics()
                            .iter()
                            .all(|diagnostic| diagnostic.id().as_str() == "invalid-return-type")
                    );
                    assert_eq!(
                        crate::types::check_types(&db, f.program_file(&db)),
                        ordinary
                    );
                }
            }
        }
        Ok(())
    }

    #[test]
    fn body_domains_follow_local_callees() -> anyhow::Result<()> {
        let mut db = setup_db();
        let source = indoc::indoc! {"
            from collections import namedtuple
            from typing import Literal, overload

            def accept_int(value: int) -> None: ...
            def accept_str(value: str) -> None: ...

            @overload
            def f(flag: Literal[True], value: int) -> None: ...
            @overload
            def f(flag: Literal[False], value: str) -> None: ...
            def f(flag: bool, value: int | str) -> None:
                callee = accept_int if flag else accept_str
                callee(value)
        "};
        for (argument, bad_domain) in [("value", None), ("42", Some(1))] {
            db.write_file(
                "/src/body.py",
                source.replace("callee(value)", &format!("callee({argument})")),
            )?;
            let f = function(&db);
            let ordinary = crate::types::check_types(&db, f.program_file(&db));
            for index in [0, 1, 0] {
                let diagnostics = check_overload_body(&db, f, index).unwrap();
                let ids: Vec<_> = diagnostics
                    .diagnostics()
                    .iter()
                    .map(|diagnostic| diagnostic.id().as_str())
                    .collect();
                let expected = (bad_domain == Some(index)).then_some("invalid-argument-type");
                assert_eq!(ids, expected.into_iter().collect::<Vec<_>>());
            }
            assert_eq!(
                crate::types::check_types(&db, f.program_file(&db)),
                ordinary
            );
        }

        for assignment in [
            "accept_int if flag else namedtuple",
            "accept_int\n    if flag:\n        callee = namedtuple",
            "f",
        ] {
            db.write_file(
                "/src/body.py",
                source.replace("accept_int if flag else accept_str", assignment),
            )?;
            assert_eq!(
                check_overload_body(&db, function(&db), 0),
                Err(BodyDomainError::Unsupported),
                "{assignment}"
            );
        }
        Ok(())
    }

    #[test]
    fn body_domains_specialize_type_form_arguments() -> anyhow::Result<()> {
        let mut db = setup_db();
        for (declaration, parameters) in [("", "[T]"), ("T = TypeVar('T')", "")] {
            for callee in ["cast", "typed"] {
                db.write_file(
                    "/src/body.py",
                    indoc::formatdoc! {"
                        from typing import cast, TypeVar, overload
                        from typing_extensions import TypeForm
                        {declaration}
                        def erase(value: object) -> object:
                            return value
                        def typed[U](annotation: TypeForm[U], value: object) -> U:
                            return cast(annotation, value)
                        @overload
                        def f(value: int) -> int: ...
                        @overload
                        def f(value: str) -> str: ...
                        def f{parameters}(value: T) -> T:
                            return {callee}(T, erase(value))
                    "},
                )?;
                let f = function(&db);
                let signature = f.last_definition_signature(&db).clone();
                let ordinary = crate::types::check_types(&db, f.program_file(&db));
                assert!(ordinary.is_empty(), "{ordinary:#?}");
                for index in [0, 1, 0] {
                    let domain = prepare_body_domain(&db, f, index).unwrap();
                    let diagnostics = check_overload_body(&db, f, index).unwrap();
                    assert!(
                        diagnostics.is_empty(),
                        "{callee}; {parameters}; domain {index}: {diagnostics:#?}"
                    );
                    assert_eq!(returned_type(&db, f, Some(domain)), domain.return_type(&db));
                    assert_eq!(f.last_definition_signature(&db), &signature);
                    assert_eq!(
                        crate::types::check_types(&db, f.program_file(&db)),
                        ordinary
                    );
                }
            }
        }
        Ok(())
    }

    #[test]
    fn body_domains_follow_module_call_terminality() -> anyhow::Result<()> {
        let mut db = setup_db();
        for declarations in [
            "@overload\ndef stop(value: Literal[True]) -> Never: ...\n@overload\ndef stop(value: Literal[False]) -> None: ...",
            "@overload\ndef stop(value: Literal[False]) -> None: ...\n@overload\ndef stop(value: Literal[True]) -> Never: ...",
        ] {
            db.write_file(
                "/src/calls.pyi",
                format!("from typing import Literal, overload\nfrom typing_extensions import Never\n{declarations}\ndef finish() -> Never: ...\n"),
            )?;
            let calls = system_path_to_file(&db, "/src/calls.pyi")?;
            let calls = ProgramFile::new(&db, calls, db.program_environment().program(&db));
            let diagnostics = crate::types::check_types(&db, calls);
            assert!(diagnostics.is_empty(), "{diagnostics:#?}");
            let source = indoc::indoc! {"
                from typing import Literal, overload
                from calls import finish, stop
                @overload
                def f(value: Literal[True]) -> int: ...
                @overload
                def f(value: Literal[False]) -> str: ...
                def f(value: bool) -> object:
                    stop(value)
                    return 'finished'
            "};
            for replacement in ["'finished'", "42", "finish()", "'finished'"] {
                db.write_file(
                    "/src/body.py",
                    source.replace("return 'finished'", &format!("return {replacement}")),
                )?;
                let f = function(&db);
                let ordinary = crate::types::check_types(&db, f.program_file(&db));
                assert!(ordinary.is_empty(), "{replacement}: {ordinary:#?}");
                for index in [0, 1, 0] {
                    let diagnostics = check_overload_body(&db, f, index).unwrap();
                    assert_eq!(
                        diagnostics
                            .diagnostics()
                            .iter()
                            .filter(|diagnostic| diagnostic.id().as_str() == "invalid-return-type")
                            .count(),
                        usize::from(index == 1 && replacement == "42"),
                        "{replacement}; domain {index}: {diagnostics:#?}"
                    );
                    assert_eq!(
                        crate::types::check_types(&db, f.program_file(&db)),
                        ordinary
                    );
                }
            }
        }
        Ok(())
    }

    #[test]
    fn body_domain_checks_arguments_to_module_callee() -> anyhow::Result<()> {
        let mut db = setup_db();
        db.write_dedented(
            "/src/body.py",
            "
            from typing import overload
            def consume(value: str) -> None: ...
            @overload
            def f(value: int) -> int: ...
            @overload
            def f(value: str) -> str: ...
            def f(value: int | str) -> int | str:
                copied = value
                consume(copied)
                return copied
        ",
        )?;
        let function = function(&db);
        let positive = check_overload_body(&db, function, 1).unwrap();
        assert!(positive.is_empty(), "{positive:#?}");
        let diagnostics = check_overload_body(&db, function, 0)
            .unwrap()
            .into_diagnostics();
        assert_eq!(diagnostics.len(), 1, "{diagnostics:#?}");
        assert_eq!(diagnostics[0].id().as_str(), "invalid-argument-type");
        Ok(())
    }

    #[test]
    fn body_domain_rejects_inconsistent_or_unhandled_domains() -> anyhow::Result<()> {
        let mut db = setup_db();
        for (parameter, body, expected) in [
            ("value: int", "return value", BodyDomainError::Inconsistent),
            (
                "value: int | str",
                "return [item for item in value]",
                BodyDomainError::Unsupported,
            ),
            (
                "value: int | str",
                "check, other = value\n    return value",
                BodyDomainError::Unsupported,
            ),
            (
                "value: int | str",
                "check = value.upper()\n    return value",
                BodyDomainError::Unsupported,
            ),
            (
                "value: int | str",
                "if value:\n        return str(1)\n    return value",
                BodyDomainError::Unsupported,
            ),
        ] {
            db.write_file("/src/body.py", format!("from typing import overload\n@overload\ndef f(value: int) -> int: ...\n@overload\ndef f(value: str) -> str: ...\ndef f({parameter}) -> int | str:\n    {body}\n"))?;
            assert_eq!(
                check_overload_body(&db, function(&db), 1).unwrap_err(),
                expected
            );
        }
        Ok(())
    }
    #[test]
    fn body_domains_follow_overload_edits() -> anyhow::Result<()> {
        let mut db = setup_db();
        let source = "from typing import overload\n@overload\ndef f(value: int) -> int: ...\n@overload\ndef f(value: str) -> str: ...\ndef f(value: int | str) -> int | str:\n    copied = value\n    return copied\n";
        db.write_file("/src/body.py", source)?;
        for (first, second) in [(1, 0), (0, 1)] {
            let f = function(&db);
            assert!(check_overload_body(&db, f, first).unwrap().is_empty());
            assert!(check_overload_body(&db, f, second).unwrap().is_empty());
            assert_eq!(
                returned_type(&db, f, None)
                    .display(&db, &db.program_environment())
                    .to_string(),
                "int | str"
            );
        }
        db.write_file(
            "/src/body.py",
            source.replace(
                "def f(value: int) -> int: ...",
                "def f(value: bool) -> bool: ...",
            ),
        )?;
        let f = function(&db);
        let domain = prepare_body_domain(&db, f, 0).unwrap();
        assert_eq!(
            returned_type(&db, f, Some(domain))
                .display(&db, &db.program_environment())
                .to_string(),
            "bool"
        );
        assert!(check_overload_body(&db, f, 0).unwrap().is_empty());
        let domain = prepare_body_domain(&db, f, 1).unwrap();
        assert_eq!(
            returned_type(&db, f, Some(domain))
                .display(&db, &db.program_environment())
                .to_string(),
            "str"
        );
        assert_eq!(
            returned_type(&db, f, None)
                .display(&db, &db.program_environment())
                .to_string(),
            "int | str"
        );
        Ok(())
    }
    #[test]
    fn body_domain_projects_normalized_typed_dictionary_kwargs() -> anyhow::Result<()> {
        let mut db = setup_db();
        db.write_dedented(
            "/src/body.py",
            "
            from typing import overload
            from typing_extensions import TypedDict, Unpack
            class Integers(TypedDict, closed=True):
                value: int
            class Strings(TypedDict, closed=True):
                value: str
            class Values(TypedDict, closed=True):
                value: int | str
            @overload
            def f(**kwargs: Unpack[Integers]) -> Integers: ...
            @overload
            def f(**kwargs: Unpack[Strings]) -> Strings: ...
            def f(**kwargs: Unpack[Values]) -> object:
                copied = kwargs
                return copied
        ",
        )?;
        for index in [0, 1] {
            assert_eq!(
                check_overload_body(&db, function(&db), index),
                Err(BodyDomainError::Unsupported)
            );
        }
        Ok(())
    }
    #[test]
    fn body_domains_check_nominal_callable_parameters() -> anyhow::Result<()> {
        let mut db = setup_db();
        let source = indoc::indoc! {"
            from typing import overload
            class Integer:
                def __call__(self, value: int) -> int:
                    return value
            class String:
                def __call__(self, value: int) -> str:
                    return 'converted'
            @overload
            def f(callback: Integer) -> int: ...
            @overload
            def f(callback: String) -> str: ...
            def f(callback: Integer | String) -> int | str:
                return callback(1)
        "};
        for argument in ["1", "'wrong'", "1"] {
            db.write_file(
                "/src/body.py",
                source.replace("callback(1)", &format!("callback({argument})")),
            )?;
            let f = function(&db);
            let ordinary = crate::types::check_types(&db, f.program_file(&db));
            if argument == "1" {
                assert!(ordinary.is_empty(), "{ordinary:#?}");
            }
            for index in [0, 1, 0] {
                let diagnostics = check_overload_body(&db, f, index).unwrap();
                assert_eq!(
                    diagnostics
                        .diagnostics()
                        .iter()
                        .map(|diagnostic| diagnostic.id().as_str())
                        .collect::<Vec<_>>(),
                    (argument != "1")
                        .then_some("invalid-argument-type")
                        .into_iter()
                        .collect::<Vec<_>>(),
                    "{argument}, domain {index}: {diagnostics:#?}"
                );
                assert_eq!(
                    crate::types::check_types(&db, f.program_file(&db)),
                    ordinary
                );
            }
        }
        Ok(())
    }

    #[test]
    fn body_domain_checks_local_callable_and_declines_captures() -> anyhow::Result<()> {
        let mut db = setup_db();
        db.write_dedented(
            "/src/body.py",
            "
            from typing import Callable, overload
            @overload
            def f(value: Callable[[int], int]) -> int: ...
            @overload
            def f(value: Callable[[str], str]) -> str: ...
            def f(value: Callable[[int], int] | Callable[[str], str]) -> int | str:
                return value(1)
        ",
        )?;
        assert!(
            check_overload_body(&db, function(&db), 0)
                .unwrap()
                .is_empty()
        );
        let diagnostics = check_overload_body(&db, function(&db), 1).unwrap();
        assert_eq!(diagnostics.diagnostics().len(), 1, "{diagnostics:#?}");
        assert_eq!(
            diagnostics.diagnostics()[0].id().as_str(),
            "invalid-argument-type"
        );
        db.write_dedented(
            "/src/body.py",
            "
            from typing import overload
            def outer(captured: int):
                @overload
                def f(value: int) -> int: ...
                @overload
                def f(value: str) -> str: ...
                def f(value: int | str) -> int | str:
                    return captured
                return f
        ",
        )?;
        let file = system_path_to_file(&db, "/src/body.py")?;
        let file = ProgramFile::new(&db, file, db.program_environment().program(&db));
        let module = parsed_module(&db, file.python_file(&db)).load(&db);
        let outer = module.suite()[1].as_function_def_stmt().unwrap();
        let implementation = outer.body[2].as_function_def_stmt().unwrap();
        let definition =
            ty_python_core::semantic_index(&db, file).expect_single_definition(implementation);
        let function = infer_definition_types(&db, definition)
            .function_type(definition)
            .unwrap();
        assert_eq!(
            check_overload_body(&db, function, 0).unwrap_err(),
            BodyDomainError::Unsupported
        );
        Ok(())
    }
}
