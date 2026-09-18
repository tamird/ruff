//! Match call arguments to parameters without inspecting their types.
//!
//! Callers expand unpacked arguments, decide which uncertain arguments can satisfy a
//! parameter, and report errors. The matcher owns parameter selection and occupancy,
//! and retains caller-provided data for each argument-to-parameter relationship.

use smallvec::SmallVec;

/// The part of a parameter declaration that determines argument matching.
///
/// Indices refer to the order of these parameters, excluding syntax separators such
/// as `/` and a bare `*`. Positional parameters precede variadic and keyword-only
/// parameters in a valid signature.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Parameter<'a> {
    PositionalOnly(Option<&'a str>),
    PositionalOrKeyword(&'a str),
    KeywordOnly(&'a str),
    Variadic,
    KeywordVariadic,
}

impl<'a> Parameter<'a> {
    fn is_positional(self) -> bool {
        matches!(self, Self::PositionalOnly(_) | Self::PositionalOrKeyword(_))
    }

    fn is_variadic(self) -> bool {
        matches!(self, Self::Variadic | Self::KeywordVariadic)
    }

    fn keyword_name(self) -> Option<&'a str> {
        match self {
            Self::PositionalOrKeyword(name) => Some(name),
            Self::KeywordOnly(name) => Some(name),
            Self::PositionalOnly(_) => None,
            Self::Variadic => None,
            Self::KeywordVariadic => None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum KeywordError {
    PositionalOnly(usize),
    Unknown,
}

/// One parameter matched to an argument, with data owned by the caller.
#[derive(Clone, Copy, Debug)]
pub struct MatchedParameter<T> {
    pub index: usize,
    pub data: T,
}

/// The parameters matched by one source argument.
#[derive(Clone, Debug)]
pub struct MatchedArgument<T> {
    /// An unpacked argument can contribute to several parameters.
    pub parameters: SmallVec<[MatchedParameter<T>; 1]>,
    /// Whether an assignment was recorded for this argument. Constraint-only
    /// relationships do not set this flag.
    pub matched: bool,
}

impl<T> Default for MatchedArgument<T> {
    fn default() -> Self {
        Self {
            parameters: SmallVec::new(),
            matched: false,
        }
    }
}

impl<T: Copy> MatchedArgument<T> {
    pub fn iter(&self) -> impl Iterator<Item = MatchedParameter<T>> + '_ {
        self.parameters.iter().copied()
    }
}

struct ParameterState<'a> {
    parameter: Parameter<'a>,
    matched: bool,
    keyword_reserved: bool,
}

/// Structural matching state for one signature and one call.
///
/// Parameter indices refer to the sequence passed to [`Self::new`]. Argument
/// indices must be less than its `argument_count`; expanded arguments retain
/// the index of the source argument they came from.
pub struct Matcher<'a, T> {
    parameters: Vec<ParameterState<'a>>,
    arguments: Vec<MatchedArgument<T>>,
    next_positional: usize,
    first_excess_positional: Option<usize>,
}

impl<'a, T> Matcher<'a, T> {
    pub fn new(parameters: impl IntoIterator<Item = Parameter<'a>>, argument_count: usize) -> Self {
        Self {
            parameters: parameters
                .into_iter()
                .map(|parameter| ParameterState {
                    parameter,
                    matched: false,
                    keyword_reserved: false,
                })
                .collect(),
            arguments: std::iter::repeat_with(MatchedArgument::default)
                .take(argument_count)
                .collect(),
            next_positional: 0,
            first_excess_positional: None,
        }
    }

    /// Select and advance past one positional argument, including excess arguments.
    /// Occupied parameters remain eligible so assignment can detect duplicates.
    pub fn next_positional(&mut self, argument_index: usize) -> Option<usize> {
        let parameter = self.positional_index().or_else(|| self.variadic_index());
        self.next_positional += 1;
        if parameter.is_none() {
            self.first_excess_positional.get_or_insert(argument_index);
        }
        parameter
    }

    /// The next fixed positional parameter, excluding the variadic fallback.
    pub fn positional_index(&self) -> Option<usize> {
        self.parameters
            .get(self.next_positional)
            .filter(|state| state.parameter.is_positional())
            .map(|_| self.next_positional)
    }

    pub fn variadic_index(&self) -> Option<usize> {
        self.parameters
            .iter()
            .position(|state| matches!(state.parameter, Parameter::Variadic))
    }

    pub fn keyword_variadic_index(&self) -> Option<usize> {
        self.parameters
            .iter()
            .rposition(|state| matches!(state.parameter, Parameter::KeywordVariadic))
    }

    fn keyword_by_name(&self, name: &str) -> Option<usize> {
        self.parameters
            .iter()
            .position(|state| state.parameter.keyword_name() == Some(name))
    }

    /// Named parameters take precedence over `**kwargs`, even when occupied.
    /// Positional-only names can be accepted by `**kwargs` without satisfying the
    /// positional-only parameter.
    pub fn keyword(&self, name: &str) -> Result<usize, KeywordError> {
        if let Some(index) = self
            .keyword_by_name(name)
            .or_else(|| self.keyword_variadic_index())
        {
            return Ok(index);
        }
        if let Some(index) = self.parameters.iter().position(|state| {
            let Parameter::PositionalOnly(parameter_name) = state.parameter else {
                return false;
            };
            parameter_name == Some(name)
        }) {
            return Err(KeywordError::PositionalOnly(index));
        }
        Err(KeywordError::Unknown)
    }

    /// Reserve a named parameter before expanding uncertain positional arguments.
    /// Reservation does not assign the parameter or change ordinary matching.
    pub fn reserve_keyword(&mut self, name: &str) {
        if let Some(index) = self.keyword_by_name(name) {
            self.parameters[index].keyword_reserved = true;
        }
    }

    pub fn keyword_reserved(&self, index: usize) -> bool {
        self.parameters[index].keyword_reserved
    }

    pub fn parameter_matched(&self, index: usize) -> bool {
        self.parameters[index].matched
    }

    /// Record an assignment, returning whether a non-variadic parameter was already
    /// occupied. Duplicate assignments are retained for subsequent type checking.
    pub fn assign(&mut self, argument_index: usize, parameter_index: usize, data: T) -> bool {
        let state = &mut self.parameters[parameter_index];
        let duplicate = state.matched && !state.parameter.is_variadic();
        state.matched = true;
        self.constrain(argument_index, parameter_index, data);
        self.arguments[argument_index].matched = true;
        duplicate
    }

    /// Record a type relationship without satisfying the parameter. For example,
    /// possible extra mapping keys can constrain a named parameter's type without
    /// guaranteeing that its required argument is present.
    pub fn constrain(&mut self, argument_index: usize, parameter_index: usize, data: T) {
        self.arguments[argument_index]
            .parameters
            .push(MatchedParameter {
                index: parameter_index,
                data,
            });
    }

    /// Count the initial contiguous positional parameters. Invalid signatures can
    /// contain later positional parameters, which are not included in this count.
    pub fn positional_count(&self) -> usize {
        self.parameters
            .iter()
            .take_while(|state| state.parameter.is_positional())
            .count()
    }

    pub fn provided_positional_count(&self) -> usize {
        self.next_positional
    }

    pub fn first_excess_positional(&self) -> Option<usize> {
        self.first_excess_positional
    }

    pub fn matches(&self) -> &[MatchedArgument<T>] {
        &self.arguments
    }

    /// Mutate caller-owned data without changing the matched parameter indices.
    pub fn matched_parameters_mut(&mut self) -> impl Iterator<Item = (usize, &mut T)> {
        self.arguments.iter_mut().flat_map(|argument| {
            let MatchedArgument {
                parameters,
                matched: _,
            } = argument;
            parameters
                .iter_mut()
                .map(|MatchedParameter { index, data }| (*index, data))
        })
    }

    pub fn into_matches(self) -> Box<[MatchedArgument<T>]> {
        let Self {
            parameters: _,
            arguments,
            next_positional: _,
            first_excess_positional: _,
        } = self;
        arguments.into_boxed_slice()
    }
}

#[cfg(test)]
mod tests {
    use super::{KeywordError, Matcher, Parameter};

    #[test]
    fn positional_arguments_do_not_skip_occupied_parameters() {
        let mut matcher = Matcher::new(
            [
                Parameter::PositionalOrKeyword("x"),
                Parameter::PositionalOrKeyword("y"),
            ],
            3,
        );
        assert_eq!(matcher.keyword("x"), Ok(0));
        assert!(!matcher.assign(0, 0, "keyword"));
        assert_eq!(matcher.next_positional(1), Some(0));
        assert!(matcher.assign(1, 0, "positional"));
        assert_eq!(matcher.next_positional(2), Some(1));
        assert_eq!(matcher.matches()[1].parameters[0].data, "positional");
    }

    #[test]
    fn keywords_prefer_named_parameters_to_kwargs() {
        let mut matcher = Matcher::new(
            [
                Parameter::PositionalOnly(Some("x")),
                Parameter::KeywordOnly("y"),
                Parameter::KeywordVariadic,
            ],
            3,
        );
        assert_eq!(matcher.keyword("x"), Ok(2));
        assert_eq!(matcher.keyword("unknown"), Ok(2));
        assert_eq!(matcher.keyword("y"), Ok(1));
        assert!(!matcher.assign(0, 1, ()));
        assert_eq!(matcher.keyword("y"), Ok(1));
        assert!(matcher.assign(1, 1, ()));
        assert!(!matcher.assign(2, 2, ()));
        assert!(!matcher.assign(2, 2, ()));
        assert!(!matcher.parameter_matched(0));
        assert_eq!(matcher.matches()[1].parameters[0].index, 1);
        assert_eq!(matcher.matches()[2].parameters.len(), 2);
    }

    #[test]
    fn keyword_errors_distinguish_positional_only_parameters() {
        let matcher = Matcher::<()>::new([Parameter::PositionalOnly(Some("x"))], 0);
        assert_eq!(matcher.keyword("x"), Err(KeywordError::PositionalOnly(0)));
        assert_eq!(matcher.keyword("other"), Err(KeywordError::Unknown));
    }

    #[test]
    fn malformed_signatures_preserve_parameter_order() {
        let mut matcher = Matcher::<()>::new(
            [
                Parameter::PositionalOnly(None),
                Parameter::KeywordOnly("duplicate"),
                Parameter::PositionalOrKeyword("duplicate"),
                Parameter::Variadic,
                Parameter::Variadic,
                Parameter::KeywordVariadic,
                Parameter::KeywordVariadic,
            ],
            3,
        );
        assert_eq!(matcher.keyword("duplicate"), Ok(1));
        assert_eq!(matcher.keyword("other"), Ok(6));
        assert_eq!(matcher.variadic_index(), Some(3));
        assert_eq!(matcher.positional_count(), 1);
        assert_eq!(matcher.next_positional(0), Some(0));
        assert_eq!(matcher.next_positional(1), Some(3));
        assert_eq!(matcher.next_positional(2), Some(2));
    }

    #[test]
    fn variadic_and_excess_positionals_advance_the_cursor() {
        let mut matcher =
            Matcher::<()>::new([Parameter::PositionalOnly(None), Parameter::Variadic], 3);
        assert_eq!(matcher.next_positional(0), Some(0));
        assert_eq!(matcher.next_positional(1), Some(1));
        assert_eq!(matcher.next_positional(2), Some(1));
        assert_eq!(matcher.provided_positional_count(), 3);
        assert_eq!(matcher.first_excess_positional(), None);

        let mut matcher = Matcher::<()>::new([Parameter::PositionalOnly(None)], 3);
        assert_eq!(matcher.next_positional(0), Some(0));
        assert_eq!(matcher.next_positional(1), None);
        assert_eq!(matcher.next_positional(2), None);
        assert_eq!(matcher.first_excess_positional(), Some(1));
        assert_eq!(matcher.provided_positional_count(), 3);
    }

    #[test]
    fn constraints_and_reservations_do_not_assign_parameters() {
        let mut matcher = Matcher::new([Parameter::PositionalOrKeyword("x")], 2);
        matcher.reserve_keyword("x");
        matcher.constrain(0, 0, "possible");
        assert!(!matcher.parameter_matched(0));
        assert!(!matcher.matches()[0].matched);
        assert!(matcher.keyword_reserved(0));
        assert_eq!(matcher.next_positional(1), Some(0));
        assert!(!matcher.assign(1, 0, "definite"));
        assert_eq!(matcher.matches()[0].parameters[0].data, "possible");
        assert!(matcher.matches()[1].matched);
    }
}
