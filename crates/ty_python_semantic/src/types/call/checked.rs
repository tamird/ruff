use ruff_python_ast as ast;

use super::arguments::CallArgumentTypes;
use super::{Binding, CallArguments};
use crate::types::Type;

/// A call after ordinary argument matching and type checking.
///
/// Native refinements use the matcher's checked parameter types and original source nodes.
pub(crate) struct CheckedCall<'a, 'db> {
    pub(crate) binding: &'a mut Binding<'db>,
    pub(crate) arguments: &'a CallArguments<'a, 'db>,
    pub(crate) bound_receiver: bool,
    pub(crate) call: &'a ast::ExprCall,
}

impl<'a, 'db> CheckedCall<'a, 'db> {
    pub(crate) fn call(&self) -> &'a ast::ExprCall {
        self.call
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
        let mut arguments = self.matched_arguments(parameter);
        let (source, _) = arguments.next()??;
        if arguments.next().is_some() {
            return None;
        }
        self.parameter_types()[parameter]?;
        match source {
            ast::ArgOrKeyword::Arg(expression) => {
                (!expression.is_starred_expr()).then_some(expression)
            }
            ast::ArgOrKeyword::Keyword(keyword) => {
                keyword.arg.as_ref()?;
                Some(&keyword.value)
            }
        }
    }

    pub(crate) fn set_return_type(&mut self, ty: Type<'db>) {
        self.binding.set_return_type(ty);
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
