//! Opt-in checking of a named function body under one declared overload.
//!
//! Domains are limited to fixed parameters, straight-line bodies, and return trees
//! guarded by Boolean parameters. Unsupported syntax must be rejected before inference: general
//! narrowing, capture, and collection queries do not yet carry a body domain.

use itertools::Itertools;
use ruff_db::parsed::parsed_module;
use ruff_python_ast as ast;
use ty_python_core::definition::Definition;
use ty_python_core::scope::ScopeId;
use ty_python_core::semantic_index;
use ty_python_core::statement::StatementInner;

use super::{
    DefinitionInference, ExpressionInference, FunctionType, InferExpression, InferScope,
    ScopeInference, StatementInferenceInner, TypeContext, infer_definition_region,
    infer_definition_types, infer_expression_region, infer_scope_region, infer_statement_region,
};
use crate::types::call::Argument;
use crate::types::constraints::ConstraintSetBuilder;
use crate::types::function::{KnownFunction, OverloadLiteral};
use crate::types::generics::Specialization;
use crate::types::signatures::{
    ParameterConsistency, PreparedOverloadImplementation, ReturnCallableTypeVarScope,
    ReturnTypeConsistency,
};
use crate::types::string_annotation::SourceAnnotation;
use crate::types::{
    CallArguments, ParameterKind, Signature, Type, TypeCheckDiagnostics, UnionType,
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
/// Only fixed parameters, simple straight-line bodies, and Boolean-parameter return trees are
/// supported. Generic implementations require complete specialization from fixed overload inputs.
/// The same substitution applies to source declarations and already inferred default types;
/// their ordinary inference and shared runtime identity are unchanged. Generic domains require
/// inhabited input evidence for every source slot. Nongeneric omitted slots retain their ordinary
/// source default types. Optional positional-only domains remain unsupported because their omitted
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

    pub(super) fn parameter_type(
        self,
        db: &'db dyn Db,
        definition: Definition<'db>,
    ) -> Option<Type<'db>> {
        self.parameters(db)
            .iter()
            .find_map(|(parameter, ty)| (*parameter == definition).then_some(*ty))
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
    if node.is_async
        || !node.decorator_list.is_empty()
        || node.parameters.vararg.is_some()
        || node.parameters.kwarg.is_some()
    {
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
    if overload_node.decorator_list.len() != 1
        || overload_node.parameters.vararg.is_some()
        || overload_node.parameters.kwarg.is_some()
    {
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
        ) && signature.return_ty.is_fully_static(db, &env)
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
                        }
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

/// Project a fixed call domain into source bindings using the ordinary argument matcher.
fn project_body_parameters<'db>(
    db: &'db dyn Db,
    env: &ProgramEnvironment<'db>,
    scope: ScopeId<'db>,
    implementation: &Signature<'db>,
    overload: &Signature<'db>,
    specialization: Option<Specialization<'db>>,
) -> Result<Box<[(Definition<'db>, Type<'db>)]>, BodyDomainError> {
    let bind = |keywords: bool| {
        let arguments: Option<CallArguments<'_, 'db>> = overload
            .parameters()
            .iter()
            .map(|parameter| {
                let argument = match parameter.kind() {
                    ParameterKind::PositionalOnly {
                        name: _,
                        default_type: _,
                    } => Argument::Positional,
                    ParameterKind::PositionalOrKeyword {
                        name,
                        default_type: _,
                    } => {
                        if keywords {
                            Argument::Keyword(name.as_str())
                        } else {
                            Argument::Positional
                        }
                    }
                    ParameterKind::KeywordOnly {
                        name,
                        default_type: _,
                    } => Argument::Keyword(name.as_str()),
                    ParameterKind::Variadic { name: _ } => return None,
                    ParameterKind::KeywordVariadic { name: _ } => return None,
                };
                Some((argument, Some(parameter.annotated_type())))
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
                let [parameter] = matched.parameters.as_slice() else {
                    return None;
                };
                Some(parameter.index)
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
    let mut may_be_omitted = vec![true; implementation.parameters().len()];
    for (parameter, index) in overload.parameters().iter().zip(positional) {
        may_be_omitted[index] = parameter.has_default();
    }
    implementation
        .parameters()
        .iter()
        .zip_eq(supplied)
        .zip_eq(may_be_omitted)
        .map(|((parameter, supplied), omitted)| {
            // Generic omitted inputs need a projection distinct from the fixed input evidence
            // used to specialize the implementation. Do not use a default to invent that evidence.
            if (specialization.is_some() || !overload.is_non_generic())
                && supplied.is_none_or(|ty| ty.is_never())
            {
                return Err(BodyDomainError::Unsupported);
            }
            let definition = parameter.definition().ok_or(BodyDomainError::Unsupported)?;
            if definition.scope(db) != scope {
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
            ast::Expr::Call(call) => {
                let ast::Expr::Name(name) = call.func.as_ref() else {
                    return false;
                };
                if name.id == *function.name(db) {
                    return false;
                }
                if locals.contains(&name.id.as_str()) {
                    if !callees.contains(&name.id.as_str()) {
                        return false;
                    }
                } else {
                    let Some(Type::FunctionLiteral(callee)) = crate::place::global_symbol(
                        db,
                        function.program_file(db),
                        name.id.as_str(),
                    )
                    .place
                    .ignore_possibly_undefined() else {
                        return false;
                    };
                    let signature = callee
                        .literal(db)
                        .last_definition
                        .raw_signature(db, ReturnCallableTypeVarScope::Lexical);
                    if matches!(
                        callee.known(db),
                        Some(KnownFunction::NewClass | KnownFunction::NamedTuple)
                    ) || !callee.overloads_and_implementation(db).0.is_empty()
                        || !signature.is_non_generic()
                        || signature.return_ty.is_never()
                    {
                        return false;
                    }
                }
                // Calls are admitted only in straight-line bodies. General narrowing queries
                // still need domain propagation before calls can coexist with conditional flow.
                call.arguments
                    .args
                    .iter()
                    .all(|argument| expression(db, function, locals, callees, argument))
                    && call.arguments.keywords.iter().all(|argument| {
                        argument.arg.is_some()
                            && expression(db, function, locals, callees, &argument.value)
                    })
            }
            _ => false,
        }
    }
    fn statements(
        db: &dyn Db,
        function: FunctionType<'_>,
        locals: &[&str],
        callees: &[&str],
        parameters: &[&str],
        body: &[ast::Stmt],
        return_tree: bool,
    ) -> bool {
        body.iter().all(|statement| match statement {
            ast::Stmt::Return(statement) => statement.value.as_deref().is_none_or(|value| {
                if return_tree {
                    // Return trees do not invoke callees or create local bindings: their only
                    // domain-sensitive flow is the truthiness of immutable Boolean parameters.
                    matches!(
                        value,
                        ast::Expr::Name(_)
                            | ast::Expr::BooleanLiteral(_)
                            | ast::Expr::NumberLiteral(_)
                            | ast::Expr::StringLiteral(_)
                            | ast::Expr::BytesLiteral(_)
                            | ast::Expr::NoneLiteral(_)
                    )
                } else {
                    expression(db, function, locals, callees, value)
                }
            }),
            ast::Stmt::If(statement) => {
                let condition = |condition: &ast::Expr| {
                    condition
                        .as_name_expr()
                        .is_some_and(|name| parameters.contains(&name.id.as_str()))
                };
                return_tree
                    && condition(&statement.test)
                    && statements(
                        db,
                        function,
                        locals,
                        callees,
                        parameters,
                        &statement.body,
                        true,
                    )
                    && statement.elif_else_clauses.iter().all(|clause| {
                        clause.test.as_ref().is_none_or(condition)
                            && statements(
                                db,
                                function,
                                locals,
                                callees,
                                parameters,
                                &clause.body,
                                true,
                            )
                    })
            }
            ast::Stmt::Assign(assignment) => {
                !return_tree && expression(db, function, locals, callees, &assignment.value)
            }
            ast::Stmt::AnnAssign(assignment) => {
                !return_tree
                    && assignment
                        .value
                        .as_deref()
                        .is_some_and(|value| expression(db, function, locals, callees, value))
            }
            ast::Stmt::Expr(statement) => {
                !return_tree && expression(db, function, locals, callees, &statement.value)
            }
            ast::Stmt::Pass(_) => true,
            _ => false,
        })
    }
    fn callable_entry(db: &dyn Db, ty: Type<'_>) -> bool {
        match ty.resolve_type_alias(db) {
            Type::Callable(_) | Type::ProtocolInstance(_) | Type::Dynamic(_) => true,
            Type::Union(union) => union.elements(db).iter().all(|ty| callable_entry(db, *ty)),
            _ => false,
        }
    }
    // Direct parameter calls cannot invoke local declaration factories or aliases. Only ordinary
    // callable/protocol/gradual entry types participate, and any source reassignment removes the
    // parameter from this set. Broader local-callee support needs its own declaration admission.
    let mut callees: Vec<&str> = signature
        .parameters()
        .iter()
        .filter_map(|parameter| {
            let definition = parameter.definition()?;
            let (_, ty) = entries.iter().find(|(entry, _)| *entry == definition)?;
            if callable_entry(db, *ty) {
                parameter.name().map(ast::name::Name::as_str)
            } else {
                None
            }
        })
        .collect();
    let mut local_names: Vec<&str> = node
        .parameters
        .iter()
        .map(|parameter| parameter.name().as_str())
        .collect();
    for statement in &node.body {
        match statement {
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
                callees.retain(|callee| *callee != name.id.as_str());
                local_names.push(name.id.as_str());
            }
            ast::Stmt::AnnAssign(assignment) => {
                let ast::Expr::Name(name) = assignment.target.as_ref() else {
                    return false;
                };
                if SemanticModel::new(db, function.program_file(db))
                    .is_type_alias_annotation(&assignment.annotation)
                {
                    return false;
                }
                callees.retain(|callee| *callee != name.id.as_str());
                local_names.push(name.id.as_str());
            }
            _ => {}
        }
    }
    let parameters: Vec<_> = signature
        .parameters()
        .iter()
        .filter_map(|parameter| {
            if parameter
                .annotated_type()
                .resolve_type_alias(db)
                .is_bool(db)
            {
                parameter.name().map(ast::name::Name::as_str)
            } else {
                None
            }
        })
        .collect();
    let return_tree = node.body.iter().any(ast::Stmt::is_if_stmt);
    statements(
        db,
        function,
        &local_names,
        &callees,
        &parameters,
        &node.body,
        return_tree,
    )
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
    fn body_domain_declines_call_narrowing_combinations() -> anyhow::Result<()> {
        let mut db = setup_db();
        for body in [
            "    callback()\n    if flag:\n        return 1\n    return 0",
            "    return callback() == 1",
        ] {
            db.write_file("/src/body.py", format!("from typing import Callable, Literal, overload\n@overload\ndef f(callback: Callable[[], int], flag: Literal[True]) -> int: ...\n@overload\ndef f(callback: Callable[[], int], flag: Literal[False]) -> int: ...\ndef f(callback: Callable[[], int], flag: bool) -> int:\n{body}\n"))?;
            assert_eq!(
                check_overload_body(&db, function(&db), 0).unwrap_err(),
                BodyDomainError::Unsupported
            );
        }
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
        assert_eq!(
            project_body_parameters(
                &db,
                &db.program_environment(),
                implementation.body_scope(&db),
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
    fn boolean_return_domains_decline_writes_and_aliases() -> anyhow::Result<()> {
        let mut db = setup_db();
        for body in [
            "flag = False\n    if flag:\n        return 1\n    return 'ok'",
            "if flag:\n        flag = False\n        return 1\n    return 'ok'",
            "alias = flag\n    if alias:\n        return 1\n    return 'ok'",
            "if flag:\n        return str(1)\n    return 'ok'",
        ] {
            db.write_file("/src/body.py", format!("from typing import Literal, overload\n@overload\ndef f(flag: Literal[True]) -> int: ...\n@overload\ndef f(flag: Literal[False]) -> str: ...\ndef f(flag: bool) -> int | str:\n    {body}\n"))?;
            assert_eq!(
                check_overload_body(&db, function(&db), 0).unwrap_err(),
                BodyDomainError::Unsupported
            );
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
                "return [value]",
                BodyDomainError::Unsupported,
            ),
            (
                "value: int | str",
                "if value:\n        return value\n    return value",
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
    fn body_domain_declines_normalized_typed_dictionary_kwargs() -> anyhow::Result<()> {
        let mut db = setup_db();
        db.write_dedented(
            "/src/body.py",
            "
            from typing import overload, Unpack
            from typing_extensions import TypedDict
            class Integers(TypedDict, closed=True):
                value: int
            class Strings(TypedDict, closed=True):
                value: str
            class Values(TypedDict, closed=True):
                value: int | str
            @overload
            def f(**kwargs: Unpack[Integers]) -> object: ...
            @overload
            def f(**kwargs: Unpack[Strings]) -> object: ...
            def f(**kwargs: Unpack[Values]) -> object:
                copied = kwargs
                return copied
        ",
        )?;
        for index in [0, 1] {
            assert_eq!(
                check_overload_body(&db, function(&db), index).unwrap_err(),
                BodyDomainError::Unsupported
            );
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
