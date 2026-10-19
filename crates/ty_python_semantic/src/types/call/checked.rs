use ruff_python_ast::{self as ast, name::Name};
use ruff_text_size::Ranged;
use ty_python_core::ProgramFile;
use ty_python_core::definition::Definition;

use super::arguments::CallArgumentTypes;
use super::{Binding, CallArguments};
use crate::types::class::DynamicClassAnchor;
use crate::types::{DictionaryItems, Type};
use crate::{Db, ProgramEnvironment};

/// Whether a checked parameter was supplied by one definite argument.
pub enum CheckedArgument<'a, 'db> {
    /// No argument supplied this parameter.
    Omitted,
    /// A single value supplied this parameter. A synthetic receiver or unpacked argument has no
    /// individual source expression.
    Value {
        ty: Type<'db>,
        expression: Option<&'a ast::Expr>,
    },
    /// Argument recovery or unpacking did not determine a single value.
    Indeterminate,
}

enum ArgumentSource<'a> {
    Expression(&'a ast::Expr),
    KeywordUnpacking(&'a ast::Expr),
    Receiver,
}

enum ArgumentAbsence {
    Omitted,
    Indeterminate,
}

/// A call after ordinary argument matching and type checking.
///
/// Argument-context providers receive a provisional check during sibling inference; its child
/// types and binding errors may change before the final check. Result providers receive the
/// completed check. Neither view requests completed inference of the enclosing scope.
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
    pub(crate) dictionary_items:
        &'a dyn Fn(&ast::Expr, Type<'db>, Option<&str>) -> Option<DictionaryItems<'db>>,
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

    /// Refines the result of a native getattr call from its already matched operands.
    ///
    /// The matched parameters must be the object, name, and optional default, in that order.
    /// Applications select the native operation declaration and establish its input contract.
    pub fn getattr_return_type(&self, db: &'db dyn Db) -> Option<Type<'db>> {
        if self.has_binding_errors || self.bound_receiver {
            return None;
        }
        let env = ProgramEnvironment::from_file(self.file);
        self.binding.getattr_call_result(db, &env)
    }

    pub fn has_binding_errors(&self) -> bool {
        self.has_binding_errors
    }

    pub fn expression_type(&self, expression: &ast::Expr) -> Option<Type<'db>> {
        (self.expression_type)(expression)
    }

    pub fn argument(&self, name: &str) -> CheckedArgument<'a, 'db> {
        let Some(parameter) = self.parameter_index(name) else {
            return CheckedArgument::Indeterminate;
        };
        self.argument_at(parameter)
    }

    /// Known entries of a definitely supplied dictionary argument.
    pub fn dictionary_argument(&self, db: &'db dyn Db, name: &str) -> Option<DictionaryItems<'db>> {
        let parameter = self.parameter_index(name)?;
        let (ty, source) = self.matched_value(parameter).ok()?;
        let (expression, keyword) = match source {
            ArgumentSource::Expression(expression) => (expression, None),
            ArgumentSource::KeywordUnpacking(expression) => {
                // A variadic parameter's name does not identify the caller's keyword.
                if self.binding.signature.parameters()[parameter].is_variadic() {
                    return None;
                }
                (expression, Some(name))
            }
            ArgumentSource::Receiver => return None,
        };
        self.observed_dictionary_items(db, expression, ty, keyword)
    }

    /// Dictionary entries observed for an already inferred child expression of this call.
    /// Optional entries and residual value bounds do not establish that a key is present.
    pub fn dictionary_items(
        &self,
        db: &'db dyn Db,
        expression: &ast::Expr,
    ) -> Option<DictionaryItems<'db>> {
        let ty = self.expression_type(expression)?;
        self.observed_dictionary_items(db, expression, ty, None)
    }

    fn observed_dictionary_items(
        &self,
        db: &'db dyn Db,
        expression: &ast::Expr,
        ty: Type<'db>,
        keyword: Option<&str>,
    ) -> Option<DictionaryItems<'db>> {
        (self.dictionary_items)(expression, ty, keyword).or_else(|| {
            let env = ProgramEnvironment::from_file(self.file);
            DictionaryItems::from_typed_dict_type(db, &env, ty, expression.range())
        })
    }

    /// Inspects a matched parameter by its zero-based signature position.
    /// An absent parameter is omitted.
    pub fn argument_at(&self, parameter: usize) -> CheckedArgument<'a, 'db> {
        match self.matched_value(parameter) {
            Ok((ty, source)) => CheckedArgument::Value {
                ty,
                expression: match source {
                    ArgumentSource::Expression(expression) => Some(expression),
                    ArgumentSource::KeywordUnpacking(_) => None,
                    ArgumentSource::Receiver => None,
                },
            },
            Err(ArgumentAbsence::Omitted) => CheckedArgument::Omitted,
            Err(ArgumentAbsence::Indeterminate) => CheckedArgument::Indeterminate,
        }
    }

    fn parameter_index(&self, name: &str) -> Option<usize> {
        self.binding
            .signature
            .parameters()
            .iter()
            .position(|parameter| parameter.name().map(Name::as_str) == Some(name))
    }

    fn matched_value(
        &self,
        parameter: usize,
    ) -> Result<(Type<'db>, ArgumentSource<'a>), ArgumentAbsence> {
        let mut arguments = self.matched_arguments(parameter);
        let Some(source) = arguments.next() else {
            return Err(ArgumentAbsence::Omitted);
        };
        if arguments.next().is_some() {
            return Err(ArgumentAbsence::Indeterminate);
        }
        let Some(ty) = self.parameter_types()[parameter] else {
            return Err(ArgumentAbsence::Indeterminate);
        };
        let source = match source {
            Some((source, _, argument)) => {
                let mut matches = argument
                    .parameters
                    .iter()
                    .filter(|matched| matched.index == parameter);
                let (Some(matched), None) = (matches.next(), matches.next()) else {
                    return Err(ArgumentAbsence::Indeterminate);
                };
                match source {
                    ast::ArgOrKeyword::Arg(expression) => {
                        if expression.is_starred_expr() {
                            return Err(ArgumentAbsence::Indeterminate);
                        }
                        ArgumentSource::Expression(expression)
                    }
                    ast::ArgOrKeyword::Keyword(keyword) => {
                        if keyword.arg.is_some() {
                            ArgumentSource::Expression(&keyword.value)
                        } else {
                            if !matched.is_definite_keyword() {
                                return Err(ArgumentAbsence::Indeterminate);
                            }
                            ArgumentSource::KeywordUnpacking(&keyword.value)
                        }
                    }
                }
            }
            None => ArgumentSource::Receiver,
        };
        Ok((ty, source))
    }

    /// Associates the matcher's receiver-prefixed arguments with original source arguments.
    /// Literal unpacking still occupies one source entry, even if it supplies several parameters.
    fn matched_arguments(
        &self,
        parameter: usize,
    ) -> impl Iterator<
        Item = Option<(
            ast::ArgOrKeyword<'a>,
            &CallArgumentTypes<'db>,
            &super::MatchedArgument<'db>,
        )>,
    > {
        let matches_parameter = move |argument: &super::MatchedArgument<'db>| {
            argument
                .parameters
                .iter()
                .any(|matched| matched.index == parameter)
        };
        let receiver = self
            .binding
            .argument_matches()
            .first()
            .filter(|argument| self.bound_receiver && matches_parameter(argument))
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
                matches_parameter(argument).then_some(Some((source, types, argument)))
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
                Some((_, types, _)) => {
                    let declared = self.binding.signature.parameters()[parameter].annotated_type();
                    Some(types.get_for_declared_type(declared))
                }
                None => self.parameter_types()[parameter],
            })
    }

    /// Returns the complete source argument for diagnostics, including a keyword's name.
    pub(crate) fn argument_node(&self, parameter: usize) -> Option<ast::AnyNodeRef<'a>> {
        let mut arguments = self.matched_arguments(parameter);
        let (source, _, _) = arguments.next()??;
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
