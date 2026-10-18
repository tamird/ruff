//! Opt-in checking of a named function body under one declared overload.
//!
//! The initial domain is deliberately limited to required nongeneric parameters and straight-line
//! bodies. Unsupported syntax must be rejected before inference: the ordinary flow, capture, and
//! collection queries do not yet carry a body domain.

use ruff_db::diagnostic::Diagnostic;
use ruff_db::parsed::parsed_module;
use ruff_python_ast as ast;
use ty_python_core::Statement;
use ty_python_core::definition::Definition;
use ty_python_core::expression::Expression;
use ty_python_core::scope::ScopeId;
use ty_python_core::statement::StatementInner;

use super::{
    DefinitionInference, ExpressionInference, FunctionType, InferExpression, InferScope,
    ScopeInference, StatementInference, StatementInferenceInner, TypeContext,
    infer_definition_region, infer_definition_types, infer_expression_region,
    infer_expression_types, infer_scope_region, infer_statement_region,
    infer_statement_with_body_domain,
};
use crate::types::function::OverloadLiteral;
use crate::types::signatures::{
    ParameterConsistency, ReturnCallableTypeVarScope, ReturnTypeConsistency,
};
use crate::types::{ParameterKind, Type};
use crate::{Db, ProgramEnvironment};

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
/// It preserves the public callable type. Only fixed required nongeneric parameters and simple
/// straight-line bodies are currently supported; an unsupported domain never means success.
pub fn check_overload_body<'db>(
    db: &'db dyn Db,
    function: FunctionType<'db>,
    overload_index: usize,
) -> Result<Vec<Diagnostic>, BodyDomainError> {
    let domain = prepare_body_domain(db, function, overload_index)?;
    let inference = infer_body_scope(db, domain);
    Ok(inference
        .diagnostics()
        .map_or_else(Vec::new, |diagnostics| {
            diagnostics.into_iter().cloned().collect()
        }))
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

    pub(crate) fn infer_definition(
        self,
        db: &'db dyn Db,
        definition: Definition<'db>,
    ) -> &'db DefinitionInference<'db> {
        if definition.scope(db) == self.scope(db) {
            infer_body_definition(db, definition, self)
        } else {
            // Module functions, annotations, and all public callable declarations keep their
            // ordinary query identity. A domain only changes bindings inside its own body.
            infer_definition_types(db, definition)
        }
    }

    pub(super) fn infer_statement(
        self,
        db: &'db dyn Db,
        statement: Statement<'db>,
    ) -> StatementInference<'db> {
        infer_statement_with_body_domain(db, statement, Some(self))
    }

    pub(super) fn infer_statement_region(
        self,
        db: &'db dyn Db,
        statement: StatementInner<'db>,
    ) -> &'db StatementInferenceInner<'db> {
        debug_assert_eq!(statement.scope(db), self.scope(db));
        infer_body_statement(db, statement, self)
    }

    pub(super) fn infer_expression(
        self,
        db: &'db dyn Db,
        expression: Expression<'db>,
        tcx: TypeContext<'db>,
    ) -> &'db ExpressionInference<'db> {
        if expression.scope(db) == self.scope(db) {
            infer_body_expression(db, InferExpression::new(db, expression, tcx), self)
        } else {
            infer_expression_types(db, expression, tcx)
        }
    }
}

fn prepare_body_domain<'db>(
    db: &'db dyn Db,
    function: FunctionType<'db>,
    overload_index: usize,
) -> Result<FunctionBodyDomain<'db>, BodyDomainError> {
    let (overloads, implementation) = function.overloads_and_implementation(db);
    let implementation = implementation.ok_or(BodyDomainError::Unsupported)?;
    let overload = *overloads
        .get(overload_index)
        .ok_or(BodyDomainError::Unsupported)?;
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
        || node.type_params.is_some()
        || node.parameters.vararg.is_some()
        || node.parameters.kwarg.is_some()
        || !supported_body(db, function, node)
    {
        return Err(BodyDomainError::Unsupported);
    }
    let overload_node = overload
        .body_scope(db)
        .node(db)
        .expect_function()
        .node(&module);
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
        signature.is_non_generic()
            && !matches!(
                signature.return_ty.resolve_type_alias(db),
                Type::TypeIs(_) | Type::TypeGuard(_)
            )
            && Type::single_callable(db, signature.clone()).is_fully_static(db, &env)
            && !signature.return_ty.has_indeterminate_inference(db, &env)
            && signature.parameters().iter().all(|parameter| {
                !parameter.has_default()
                    && !parameter
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
    let implementation_signature = implementation_signature
        .specialize_for_overload_implementation(db, &env, &overload_signature)
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
    // With identical required slot shapes, the canonical coverage comparison establishes an
    // unambiguous one-to-one entry projection. Other call shapes need binder-owned projection.
    let source_parameters = implementation_signature.parameters();
    let domain_parameters = overload_signature.parameters();
    if source_parameters.len() != domain_parameters.len() {
        return Err(BodyDomainError::Unsupported);
    }
    let parameters = source_parameters
        .iter()
        .zip(domain_parameters.iter())
        .map(|(source, domain)| {
            if source.kind() != domain.kind() {
                return Err(BodyDomainError::Unsupported);
            }
            let definition = source.definition().ok_or(BodyDomainError::Unsupported)?;
            if definition.scope(db) != implementation.body_scope(db) {
                return Err(BodyDomainError::Unsupported);
            }
            Ok((definition, domain.annotated_type()))
        })
        .collect::<Result<Box<[_]>, _>>()?;
    Ok(FunctionBodyDomain::new(
        db,
        implementation,
        overload,
        parameters,
        overload_signature.return_ty,
    ))
}

fn supported_body(db: &dyn Db, function: FunctionType<'_>, node: &ast::StmtFunctionDef) -> bool {
    fn expression(
        db: &dyn Db,
        function: FunctionType<'_>,
        locals: &[&str],
        value: &ast::Expr,
    ) -> bool {
        match value {
            ast::Expr::Name(_) => true,
            ast::Expr::NumberLiteral(_) => true,
            ast::Expr::StringLiteral(_) => true,
            ast::Expr::BooleanLiteral(_) => true,
            ast::Expr::NoneLiteral(_) => true,
            ast::Expr::Call(call) => {
                let ast::Expr::Name(name) = call.func.as_ref() else {
                    return false;
                };
                if locals.contains(&name.id.as_str()) || name.id == *function.name(db) {
                    return false;
                }
                let Some(Type::FunctionLiteral(callee)) =
                    crate::place::global_symbol(db, function.program_file(db), name.id.as_str())
                        .place
                        .ignore_possibly_undefined()
                else {
                    return false;
                };
                let signature = callee
                    .literal(db)
                    .last_definition
                    .raw_signature(db, ReturnCallableTypeVarScope::Lexical);
                callee.overloads_and_implementation(db).0.is_empty()
                    && signature.is_non_generic()
                    && !signature.return_ty.is_never()
                    && call
                        .arguments
                        .args
                        .iter()
                        .all(|argument| expression(db, function, locals, argument))
                    && call.arguments.keywords.iter().all(|argument| {
                        argument.arg.is_some() && expression(db, function, locals, &argument.value)
                    })
            }
            _ => false,
        }
    }
    let mut local_names: Vec<&str> = node
        .parameters
        .iter()
        .map(|parameter| parameter.name().as_str())
        .collect();
    for statement in &node.body {
        if let ast::Stmt::Assign(assignment) = statement {
            let [ast::Expr::Name(name)] = assignment.targets.as_slice() else {
                return false;
            };
            local_names.push(name.id.as_str());
        }
    }
    let Some((ast::Stmt::Return(last), prefix)) = node.body.split_last() else {
        return false;
    };
    last.value
        .as_deref()
        .is_none_or(|value| expression(db, function, &local_names, value))
        && prefix.iter().all(|statement| match statement {
            ast::Stmt::Assign(assignment) => {
                expression(db, function, &local_names, &assignment.value)
            }
            ast::Stmt::Expr(statement) => expression(db, function, &local_names, &statement.value),
            ast::Stmt::Pass(_) => true,
            _ => false,
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
fn infer_body_definition<'db>(
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
fn infer_body_expression<'db>(
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
fn infer_body_statement<'db>(
    db: &'db dyn Db,
    statement: StatementInner<'db>,
    domain: FunctionBodyDomain<'db>,
) -> StatementInferenceInner<'db> {
    infer_statement_region(db, statement, Some(domain))
}

#[cfg(test)]
mod tests {
    use std::assert_matches;

    use ruff_db::files::system_path_to_file;
    use ruff_db::system::DbWithWritableSystem;
    use ty_python_core::ProgramFile;

    use super::*;
    use crate::db::tests::{TestDb, setup_db};
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
        assert_matches!(function.body.last(), Some(ast::Stmt::Return(_)));
        let statement = function.body.last().unwrap().as_return_stmt().unwrap();
        let value = statement.value.as_deref().unwrap();
        let inference = domain.map_or_else(
            || infer_complete_scope_types(db, scope),
            |domain| infer_body_scope(db, domain),
        );
        inference.expression_type(value)
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
        let diagnostics = check_overload_body(&db, function, 1).unwrap();
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
        let diagnostics = check_overload_body(&db, function(&db), 1).unwrap();
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
        let diagnostics = check_overload_body(&db, function, 0).unwrap();
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
                "value: int | str = 0",
                "return value",
                BodyDomainError::Unsupported,
            ),
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
    fn body_domain_declines_local_callable_and_captures() -> anyhow::Result<()> {
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
        assert_eq!(
            check_overload_body(&db, function(&db), 0).unwrap_err(),
            BodyDomainError::Unsupported
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
