use ruff_python_ast::{self as ast, name::Name};
use ty_python_core::ProgramFile;
use ty_python_core::definition::Definition;

use super::arguments::CallArgumentTypes;
use super::{Binding, CallArguments};
use crate::types::Type;
use crate::types::class::DynamicClassAnchor;

/// Whether a checked parameter was supplied by one definite argument.
pub enum CheckedArgument<'a, 'db> {
    /// No argument supplied this parameter.
    Omitted,
    /// A single value supplied this parameter. A synthetic receiver has no source expression.
    Value {
        ty: Type<'db>,
        expression: Option<&'a ast::Expr>,
    },
    /// Argument recovery or unpacking did not determine a single value.
    Indeterminate,
}

/// A call after ordinary argument matching and type checking.
///
/// Native refinements can update the return type through this view. Applications receive
/// read-only access. Child types come from the current inference result, so inspecting them
/// cannot recursively request the enclosing scope. Source nodes belong to the original call.
pub struct CheckedCall<'a, 'db> {
    pub(crate) binding: &'a mut Binding<'db>,
    pub(crate) arguments: &'a CallArguments<'a, 'db>,
    pub(crate) bound_receiver: bool,
    pub(crate) file: ProgramFile<'db>,
    pub(crate) call: &'a ast::ExprCall,
    pub(crate) expression_type: &'a dyn Fn(&ast::Expr) -> Option<Type<'db>>,
    pub(crate) class_anchor: &'a dyn Fn(Box<[Type<'db>]>) -> DynamicClassAnchor<'db>,
    pub(crate) has_binding_errors: bool,
}

impl<'a, 'db> CheckedCall<'a, 'db> {
    pub fn file(&self) -> ProgramFile<'db> {
        self.file
    }

    pub fn call(&self) -> &'a ast::ExprCall {
        self.call
    }

    pub fn declaration(&self) -> Option<Definition<'db>> {
        self.binding.signature.definition()
    }

    pub fn return_type(&self) -> Type<'db> {
        self.binding.return_ty
    }

    pub fn has_binding_errors(&self) -> bool {
        self.has_binding_errors
    }

    pub fn expression_type(&self, expression: &ast::Expr) -> Option<Type<'db>> {
        (self.expression_type)(expression)
    }

    pub fn argument(&self, name: &str) -> CheckedArgument<'a, 'db> {
        let Some(parameter) = self
            .binding
            .signature
            .parameters()
            .iter()
            .position(|parameter| parameter.name().map(Name::as_str) == Some(name))
        else {
            return CheckedArgument::Indeterminate;
        };
        self.argument_at(parameter)
    }

    fn argument_at(&self, parameter: usize) -> CheckedArgument<'a, 'db> {
        let mut arguments = self.matched_arguments(parameter);
        let Some(source) = arguments.next() else {
            return CheckedArgument::Omitted;
        };
        if arguments.next().is_some() {
            return CheckedArgument::Indeterminate;
        }
        let Some(ty) = self.parameter_types()[parameter] else {
            return CheckedArgument::Indeterminate;
        };
        let expression = match source {
            Some((source, _)) => {
                let expression = match source {
                    ast::ArgOrKeyword::Arg(expression) => {
                        if expression.is_starred_expr() {
                            return CheckedArgument::Indeterminate;
                        }
                        expression
                    }
                    ast::ArgOrKeyword::Keyword(keyword) => {
                        if keyword.arg.is_none() {
                            return CheckedArgument::Indeterminate;
                        }
                        &keyword.value
                    }
                };
                Some(expression)
            }
            None => None,
        };
        CheckedArgument::Value { ty, expression }
    }

    /// Associates the matcher's receiver-prefixed arguments with original source arguments.
    /// Literal unpacking still occupies one source entry, even if it supplies several parameters.
    fn matched_arguments(
        &self,
        parameter: usize,
    ) -> impl Iterator<Item = Option<(ast::ArgOrKeyword<'a>, &CallArgumentTypes<'db>)>> {
        let matches = move |argument: &super::MatchedArgument<'db>| {
            argument
                .parameters
                .iter()
                .any(|matched| matched.index == parameter)
        };
        let receiver = self
            .binding
            .argument_matches()
            .first()
            .filter(|argument| self.bound_receiver && matches(argument))
            .map(|_| None);
        let sources = self
            .call
            .arguments
            .iter_source_order()
            .zip(self.arguments.iter_types())
            .enumerate()
            .filter_map(move |(index, (source, types))| {
                let argument = self
                    .binding
                    .matched_argument_for_call_argument(self.bound_receiver, index)?;
                matches(argument).then_some(Some((source, types)))
            });
        receiver.into_iter().chain(sources)
    }

    pub(crate) fn parameter_types(&self) -> &[Option<Type<'db>>] {
        self.binding.parameter_types()
    }

    pub(crate) fn arguments_for_parameter(
        &self,
        parameter: usize,
    ) -> impl Iterator<Item = Type<'db>> {
        self.matched_arguments(parameter)
            .filter_map(move |argument| match argument {
                Some((_, types)) => {
                    let declared = self.binding.signature.parameters()[parameter].annotated_type();
                    Some(types.get_for_declared_type(declared))
                }
                None => self.parameter_types()[parameter],
            })
    }

    /// Returns the complete source argument for diagnostics, including a keyword's name.
    pub(crate) fn argument_node(&self, parameter: usize) -> Option<ast::AnyNodeRef<'a>> {
        let mut arguments = self.matched_arguments(parameter);
        let (source, _) = arguments.next()??;
        if arguments.next().is_some() {
            return None;
        }
        Some(match source {
            ast::ArgOrKeyword::Arg(expression) => expression.into(),
            ast::ArgOrKeyword::Keyword(keyword) => keyword.into(),
        })
    }

    pub(crate) fn argument_expression(&self, parameter: usize) -> Option<&'a ast::Expr> {
        match self.argument_at(parameter) {
            CheckedArgument::Value { ty: _, expression } => expression,
            CheckedArgument::Omitted => None,
            CheckedArgument::Indeterminate => None,
        }
    }

    pub(crate) fn set_return_type(&mut self, ty: Type<'db>) {
        self.binding.set_return_type(ty);
    }

    pub(crate) fn class_anchor(&self, bases: Box<[Type<'db>]>) -> DynamicClassAnchor<'db> {
        (self.class_anchor)(bases)
    }
}

#[cfg(test)]
mod tests {
    use ruff_db::files::system_path_to_file;
    use ruff_text_size::{TextLen, TextRange, TextSize};

    use crate::Db as _;
    use crate::db::tests::TestDbBuilder;

    #[test]
    fn native_diagnostics_keep_the_complete_keyword() -> anyhow::Result<()> {
        let source = "from ty_extensions import static_assert\nstatic_assert(condition=False)\n";
        let db = TestDbBuilder::new()
            .with_file("/src/main.py", source)
            .build()?;
        let file = system_path_to_file(&db, "/src/main.py")?;
        let diagnostics = db.check_file(file);
        let [diagnostic] = diagnostics.as_slice() else {
            panic!("expected one static assertion diagnostic: {diagnostics:#?}");
        };
        assert_eq!(diagnostic.id().as_str(), "static-assert-error");
        let start = TextSize::try_from(source.find("condition=False").unwrap())?;
        let expected = TextRange::at(start, "condition=False".text_len());
        assert!(
            diagnostic
                .secondary_annotations()
                .any(|annotation| annotation.get_span().range() == Some(expected)),
            "{diagnostic:#?}"
        );
        Ok(())
    }
}
