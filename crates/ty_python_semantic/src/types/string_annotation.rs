use ruff_db::files::FileRange;
use ruff_db::parsed::parsed_module;
use ruff_db::parsed::{parsed_annotation_range, parsed_string_annotation};
use ruff_db::source::source_text;
use ruff_python_ast::{self as ast, HasNodeIndex, NodeIndex, StringFlags};
use ruff_python_parser::{ParseError, ParseErrorType, Parsed};
use ruff_text_size::{Ranged, TextRange};
use ty_python_core::definition::{Definition, DefinitionKind};
use ty_python_core::node_key::NodeKey;
use ty_python_core::{
    ExpressionNodeKey, ProgramFile, ProvidedAnnotation, global_scope, semantic_index,
};

use crate::Db;
use crate::declare_lint;
use crate::lint::{Level, LintStatus};
use crate::provided::ProvidedReturnType;
use crate::types::diagnostic::INVALID_TYPE_FORM;
use crate::types::diagnostic::autofix_with_literal;
use crate::types::infer::{
    InferenceFlags, TypeContext, TypeContextPurpose, TypeExpressionFlags, infer_definition_types,
};
use crate::types::signatures::function_signature_annotation_info;
use crate::types::{Type, TypeAndQualifiers};

use super::context::InferContext;

declare_lint! {
    #[doc = include_str!("../../resources/lint_docs/raw-string-type-annotation.md")]
    pub(crate) static RAW_STRING_TYPE_ANNOTATION = {
        summary: "detects raw strings in type annotation positions",
        status: LintStatus::stable("0.0.1-alpha.1"),
        default_level: Level::Error,
    }
}

declare_lint! {
    #[doc = include_str!("../../resources/lint_docs/implicit-concatenated-string-type-annotation.md")]
    pub(crate) static IMPLICIT_CONCATENATED_STRING_TYPE_ANNOTATION = {
        summary: "detects implicit concatenated strings in type annotations",
        status: LintStatus::stable("0.0.1-alpha.1"),
        default_level: Level::Error,
    }
}

declare_lint! {
    #[doc = include_str!("../../resources/lint_docs/invalid-syntax-in-forward-annotation.md")]
    pub(crate) static INVALID_SYNTAX_IN_FORWARD_ANNOTATION = {
        summary: "detects invalid syntax in forward annotations",
        status: LintStatus::stable("0.0.1-alpha.1"),
        default_level: Level::Error,
    }
}

declare_lint! {
    #[doc = include_str!("../../resources/lint_docs/escape-character-in-forward-annotation.md")]
    pub(crate) static ESCAPE_CHARACTER_IN_FORWARD_ANNOTATION = {
        summary: "detects forward type annotations with escape characters",
        status: LintStatus::stable("0.0.1-alpha.1"),
        default_level: Level::Error,
    }
}

/// An annotation in the module AST or a detached expression anchored to a canonical source node.
pub(crate) enum SourceAnnotation<'a, 'db> {
    Native(&'a ast::Expr),
    Detached {
        owner: NodeKey,
        range: TextRange,
        parsed: Result<Parsed<ast::ModExpression>, ParseError>,
    },
    External {
        annotation: ExternalAnnotation<'db>,
        purpose: TypeContextPurpose,
        /// The local declaration is the diagnostic location for invalid annotation use.
        range: TextRange,
    },
    Provided {
        annotation: ProvidedReturnType<'db>,
        range: TextRange,
    },
}

impl<'a, 'db> SourceAnnotation<'a, 'db> {
    pub(crate) fn function_return(
        db: &'db dyn Db,
        file: ProgramFile<'db>,
        function: &'a ast::StmtFunctionDef,
    ) -> Option<Self> {
        Self::new(db, file, function, function.returns.as_deref()).or_else(|| {
            let definition = semantic_index(db, file).try_definition(function)?;
            Some(Self::Provided {
                annotation: db.provided_return_type(definition)?,
                range: function.name.range,
            })
        })
    }

    pub(crate) fn new(
        db: &'db dyn Db,
        file: ProgramFile<'db>,
        owner: impl HasNodeIndex + Ranged,
        native: Option<&'a ast::Expr>,
    ) -> Option<Self> {
        if let Some(expr) = native {
            return Some(Self::Native(expr));
        }
        let range = match db.provided_annotation(file, owner.node_index().load())? {
            ProvidedAnnotation::Range(range) => range,
            ProvidedAnnotation::External {
                file: foreign_file,
                owner: foreign_owner,
            } => {
                return Self::external(
                    db,
                    file,
                    owner,
                    foreign_file,
                    foreign_owner,
                    TypeContextPurpose::Inference,
                );
            }
            ProvidedAnnotation::ExternalValueContract {
                file: foreign_file,
                owner: foreign_owner,
            } => {
                return Self::external(
                    db,
                    file,
                    owner,
                    foreign_file,
                    foreign_owner,
                    TypeContextPurpose::ValueContract,
                );
            }
        };
        let source = source_text(db, file.file(db));
        let parsed = parsed_annotation_range(&source, range, owner.node_index().load());
        Some(Self::Detached {
            owner: NodeKey::from_node(owner),
            range,
            parsed,
        })
    }

    fn external(
        db: &'db dyn Db,
        file: ProgramFile<'db>,
        owner: impl HasNodeIndex + Ranged,
        foreign_file: ProgramFile<'db>,
        foreign_owner: NodeIndex,
        purpose: TypeContextPurpose,
    ) -> Option<Self> {
        let annotation = external_annotation(db, foreign_file, foreign_owner)?;
        let local_module = parsed_module(db, file.python_file(db)).load(db);
        let local_assignment = match local_module.get_by_index(owner.node_index().load()) {
            ast::AnyRootNodeRef::Expr(expression) => expression.is_name_expr(),
            _ => false,
        };
        if local_assignment
            != matches!(
                annotation.definition.kind(db),
                DefinitionKind::AnnotatedAssignment(_)
            )
            || (matches!(purpose, TypeContextPurpose::ValueContract) && !local_assignment)
        {
            return None;
        }
        Some(Self::External {
            annotation,
            purpose,
            range: owner.range(),
        })
    }

    pub(crate) fn initializer_context(&self, annotation: Type<'db>) -> TypeContext<'db> {
        if let Self::External {
            annotation: _,
            purpose,
            range: _,
        } = self
            && matches!(purpose, TypeContextPurpose::ValueContract)
        {
            TypeContext::for_value_contract(annotation)
        } else {
            TypeContext::new(Some(annotation))
        }
    }

    pub(crate) fn expression_or_report(&self, context: &InferContext) -> Option<&ast::Expr> {
        if let Self::Detached {
            owner: _,
            range: _,
            parsed: Err(error),
        } = self
            && let Some(builder) = context.report_lint(&INVALID_TYPE_FORM, error.location)
        {
            builder.into_diagnostic(format_args!("Invalid type expression: {}", error.error));
        }
        self.expression()
    }

    pub(crate) fn expression(&self) -> Option<&ast::Expr> {
        match self {
            Self::Native(expr) => Some(expr),
            Self::Detached {
                owner: _,
                range: _,
                parsed,
            } => parsed.as_ref().ok().map(Parsed::expr),
            Self::External {
                annotation: _,
                purpose: _,
                range: _,
            } => None,
            Self::Provided {
                annotation: _,
                range: _,
            } => None,
        }
    }

    pub(crate) fn source(&self, file: ruff_db::files::File) -> FileRange {
        match self {
            Self::External {
                annotation,
                purpose: _,
                range: _,
            } => annotation.source,
            Self::Provided { annotation, range } => annotation
                .source
                .unwrap_or_else(|| FileRange::new(file, *range)),
            Self::Native(_)
            | Self::Detached {
                owner: _,
                range: _,
                parsed: _,
            } => FileRange::new(file, self.range()),
        }
    }

    pub(crate) fn external_type(&self, db: &'db dyn Db) -> Option<Type<'db>> {
        match self {
            Self::External {
                annotation,
                purpose: _,
                range: _,
            } => Some(annotation.inferred(db).0),
            Self::Provided {
                annotation,
                range: _,
            } => Some(annotation.ty),
            Self::Native(_)
            | Self::Detached {
                owner: _,
                range: _,
                parsed: _,
            } => None,
        }
    }

    pub(crate) fn external_declaration(&self, db: &'db dyn Db) -> Option<TypeAndQualifiers<'db>> {
        let Self::External {
            annotation,
            purpose: _,
            range: _,
        } = self
        else {
            return None;
        };
        annotation.declaration(db)
    }

    pub(crate) fn is_starred(&self) -> bool {
        match self {
            Self::External {
                annotation,
                purpose: _,
                range: _,
            } => annotation.starred,
            Self::Provided {
                annotation: _,
                range: _,
            } => false,
            Self::Native(_)
            | Self::Detached {
                owner: _,
                range: _,
                parsed: _,
            } => self.expression().is_some_and(ast::Expr::is_starred_expr),
        }
    }

    pub(crate) fn inferred_type(&self, db: &'db dyn Db, function: Definition<'db>) -> Type<'db> {
        self.inferred(db, function).0
    }

    pub(crate) fn inferred(
        &self,
        db: &'db dyn Db,
        function: Definition<'db>,
    ) -> (Type<'db>, TypeExpressionFlags) {
        if let Self::External {
            annotation,
            purpose: _,
            range: _,
        } = self
        {
            return annotation.inferred(db);
        }
        if let Self::Provided {
            annotation,
            range: _,
        } = self
        {
            return (annotation.ty, TypeExpressionFlags::empty());
        }
        let Some(expression) = self.expression() else {
            return (Type::unknown(), TypeExpressionFlags::empty());
        };
        let (ty, flags) = function_signature_annotation_info(db, function, expression.into());
        (ty.unwrap_or_else(Type::unknown), flags)
    }
}

impl Ranged for SourceAnnotation<'_, '_> {
    fn range(&self) -> TextRange {
        match self {
            Self::Native(expr) => expr.range(),
            Self::Detached {
                owner: _,
                range,
                parsed: _,
            } => *range,
            Self::External {
                annotation: _,
                purpose: _,
                range,
            } => *range,
            Self::Provided {
                annotation: _,
                range,
            } => *range,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, salsa::SalsaValue)]
pub(crate) struct ExternalAnnotation<'db> {
    definition: Definition<'db>,
    expression: ExpressionNodeKey,
    source: FileRange,
    starred: bool,
}

impl<'db> ExternalAnnotation<'db> {
    fn declaration(&self, db: &'db dyn Db) -> Option<TypeAndQualifiers<'db>> {
        if !matches!(
            self.definition.kind(db),
            DefinitionKind::AnnotatedAssignment(_)
        ) {
            return None;
        }
        let inference = infer_definition_types(db, self.definition);
        // A TypeAlias declaration describes the alias binding, not an assignment annotation.
        if inference
            .try_expression_type(self.expression)
            .is_some_and(|ty| ty.is_typealias_special_form())
        {
            return None;
        }
        inference.inferred_declaration(self.definition).declared()
    }

    fn inferred(&self, db: &'db dyn Db) -> (Type<'db>, TypeExpressionFlags) {
        let Self {
            definition,
            expression,
            source: _,
            starred: _,
        } = self;
        if !matches!(definition.kind(db), DefinitionKind::Function(_)) {
            return (Type::unknown(), TypeExpressionFlags::empty());
        }
        let (ty, flags) = function_signature_annotation_info(db, *definition, *expression);
        (ty.unwrap_or_else(Type::unknown), flags)
    }
}

/// Preserve the declaring definition and expression identity for lazy annotation inference.
/// Foreign nodes stay in their own expression table and name-resolution scope.
#[salsa::tracked(returns(copy))]
fn external_annotation<'db>(
    db: &'db dyn Db,
    file: ProgramFile<'db>,
    owner: NodeIndex,
) -> Option<ExternalAnnotation<'db>> {
    let module = parsed_module(db, file.python_file(db)).load(db);
    let index = semantic_index(db, file);
    let (definition, expression) = match module.get_by_index(owner) {
        ast::AnyRootNodeRef::Stmt(statement) => match statement {
            ast::Stmt::FunctionDef(function) => (
                index.try_definition(function)?,
                function.returns.as_deref()?,
            ),
            ast::Stmt::AnnAssign(assignment) => {
                if !assignment.target.is_name_expr() {
                    return None;
                }
                let definition = index.try_definition(assignment)?;
                if definition.scope(db) != global_scope(db, file) {
                    return None;
                }
                (definition, assignment.annotation.as_ref())
            }
            _ => return None,
        },
        ast::AnyRootNodeRef::Parameter(parameter) => {
            let definition = index.try_definition(parameter)?;
            let function = definition.scope(db).node(db).as_function()?;
            (
                index.try_definition(function.node(&module))?,
                parameter.annotation()?,
            )
        }
        _ => return None,
    };
    Some(ExternalAnnotation {
        definition,
        expression: expression.into(),
        source: FileRange::new(file.file(db), expression.range()),
        starred: expression.is_starred_expr(),
    })
}

/// Parses the given expression as a string annotation.
pub(crate) fn parse_string_annotation<'a, 'db>(
    context: &InferContext<'db, '_>,
    inference_flags: InferenceFlags,
    string_expr: &ast::ExprStringLiteral,
    owner: NodeKey,
) -> Option<SourceAnnotation<'a, 'db>> {
    let file = context.file();
    let db = context.db();

    let _span = tracing::trace_span!("parse_string_annotation", string=?string_expr.range(), ?file)
        .entered();

    let source = source_text(db, file);

    if let Some(string_literal) = string_expr.as_single_part_string() {
        let prefix = string_literal.flags.prefix();
        if prefix.is_raw() {
            if let Some(builder) = context.report_lint(&RAW_STRING_TYPE_ANNOTATION, string_literal)
            {
                builder.into_diagnostic(format_args!(
                    "Raw string literals are not allowed in {}s",
                    inference_flags.type_expression_context()
                ));
            }
        // Compare the raw contents (without quotes) of the expression with the parsed contents
        // contained in the string literal.
        } else if &source[string_literal.content_range()] == string_literal.as_str() {
            match parsed_string_annotation(source.as_str(), string_literal) {
                Ok(parsed) => {
                    return Some(SourceAnnotation::Detached {
                        owner,
                        range: string_expr.range(),
                        parsed: Ok(parsed),
                    });
                }
                Err(ParseError { error, location }) => {
                    if let Some(builder) =
                        context.report_lint(&INVALID_SYNTAX_IN_FORWARD_ANNOTATION, location)
                    {
                        let mut diagnostic =
                            builder.into_diagnostic("Syntax error in forward annotation");

                        diagnostic.set_primary_annotation_message(&error);

                        let possible_secondary = string_literal
                            .range()
                            .add_start(string_literal.flags.opener_len())
                            .sub_end(string_literal.flags.closer_len());
                        if possible_secondary.contains_range(location)
                            && (possible_secondary.start() < location.start()
                                || possible_secondary.end() > location.end())
                        {
                            diagnostic.annotate(context.secondary(possible_secondary));
                        }

                        if !matches!(error, ParseErrorType::StringAnnotationError(_))
                            && !string_literal.contains('\n')
                        {
                            diagnostic.help(format_args!(
                                "Did you mean `typing.Literal[\"{}\"]`?",
                                string_literal.as_str()
                            ));
                            autofix_with_literal(context, &mut diagnostic, string_expr);
                        }
                    }
                }
            }
        } else if let Some(builder) =
            context.report_lint(&ESCAPE_CHARACTER_IN_FORWARD_ANNOTATION, string_expr)
        {
            // The raw contents of the string doesn't match the parsed content. This could be the
            // case for annotations that contain escape sequences.
            builder.into_diagnostic(format_args!(
                "Escape characters are not allowed in {}s",
                inference_flags.type_expression_context()
            ));
        }
    } else if let Some(builder) =
        context.report_lint(&IMPLICIT_CONCATENATED_STRING_TYPE_ANNOTATION, string_expr)
    {
        // String is implicitly concatenated.
        builder.into_diagnostic("Type expressions cannot span multiple string literals");
    }

    None
}
