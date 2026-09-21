use ruff_db::files::FileRange;
use ruff_db::parsed::parsed_module;
use ruff_db::parsed::{parsed_annotation_range, parsed_string_annotation};
use ruff_db::source::source_text;
use ruff_python_ast::{self as ast, HasNodeIndex, NodeIndex, StringFlags};
use ruff_python_parser::{ParseError, ParseErrorType, Parsed};
use ruff_text_size::{Ranged, TextRange};
use ty_python_core::definition::Definition;
use ty_python_core::node_key::NodeKey;
use ty_python_core::{ExpressionNodeKey, ProgramFile, ProvidedAnnotation, semantic_index};

use crate::Db;
use crate::declare_lint;
use crate::lint::{Level, LintStatus};
use crate::types::Type;
use crate::types::diagnostic::INVALID_TYPE_FORM;
use crate::types::diagnostic::autofix_with_literal;
use crate::types::infer::{InferenceFlags, TypeExpressionFlags};
use crate::types::signatures::function_signature_annotation_info;

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
        /// The local declaration is the diagnostic location for invalid annotation use.
        range: TextRange,
    },
}

impl<'a, 'db> SourceAnnotation<'a, 'db> {
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
                file,
                owner: foreign_owner,
            } => {
                return Some(Self::External {
                    annotation: external_annotation(db, file, foreign_owner)?,
                    range: owner.range(),
                });
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
                range: _,
            } => None,
        }
    }

    pub(crate) fn source(&self, file: ruff_db::files::File) -> FileRange {
        match self {
            Self::External {
                annotation,
                range: _,
            } => annotation.source,
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
                range: _,
            } => Some(annotation.inferred(db).0),
            Self::Native(_)
            | Self::Detached {
                owner: _,
                range: _,
                parsed: _,
            } => None,
        }
    }

    pub(crate) fn is_starred(&self) -> bool {
        match self {
            Self::External {
                annotation,
                range: _,
            } => annotation.starred,
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
            range: _,
        } = self
        {
            return annotation.inferred(db);
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
                range,
            } => *range,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, salsa::SalsaValue)]
pub(crate) struct ExternalAnnotation<'db> {
    function: Definition<'db>,
    expression: ExpressionNodeKey,
    source: FileRange,
    starred: bool,
}

impl<'db> ExternalAnnotation<'db> {
    fn inferred(&self, db: &'db dyn Db) -> (Type<'db>, TypeExpressionFlags) {
        let Self {
            function,
            expression,
            source: _,
            starred: _,
        } = self;
        let (ty, flags) = function_signature_annotation_info(db, *function, *expression);
        (ty.unwrap_or_else(Type::unknown), flags)
    }
}

/// Preserve the declaring function and expression identity for lazy annotation inference.
/// Foreign nodes stay in their own expression table and name-resolution scope.
#[salsa::tracked(returns(copy))]
fn external_annotation<'db>(
    db: &'db dyn Db,
    file: ProgramFile<'db>,
    owner: NodeIndex,
) -> Option<ExternalAnnotation<'db>> {
    let module = parsed_module(db, file.python_file(db)).load(db);
    let index = semantic_index(db, file);
    let (function, expression) = match module.get_by_index(owner) {
        ast::AnyRootNodeRef::Stmt(statement) => {
            let ast::Stmt::FunctionDef(function) = statement else {
                return None;
            };
            (
                index.try_definition(function)?,
                function.returns.as_deref()?,
            )
        }
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
        function,
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
