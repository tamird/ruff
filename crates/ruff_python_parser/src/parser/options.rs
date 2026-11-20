use std::borrow::Cow;

use ruff_python_ast::{PySourceType, PythonVersion};

use crate::{AsMode, Mode};

/// Options for controlling how a source file is parsed.
///
/// You can construct a [`ParseOptions`] directly from a [`Mode`]:
///
/// ```
/// use ruff_python_parser::{Mode, ParseOptions};
///
/// let options = ParseOptions::from(Mode::Module);
/// ```
///
/// or from a [`PySourceType`]
///
/// ```
/// use ruff_python_ast::PySourceType;
/// use ruff_python_parser::ParseOptions;
///
/// let options = ParseOptions::from(PySourceType::Python);
/// ```
#[derive(Clone, Debug)]
pub struct ParseOptions {
    /// Specify the mode in which the code will be parsed.
    pub(crate) mode: Mode,
    /// Target version for detecting version-related syntax errors.
    pub(crate) target_version: PythonVersion,
    /// Optional source-fragment interpretation for an embedding language.
    string_literal_decoder: Option<StringLiteralDecoder>,
}

/// Interprets an unescaped source fragment inside an ordinary string literal.
///
/// Escape sequences are interpreted independently by the parser. Returning `None` preserves the
/// source fragment. The decoder must be deterministic and preserve concatenation: interpreting
/// two fragments separately must give the same value as interpreting their concatenation.
pub type StringLiteralDecoder = fn(&str) -> Option<Box<str>>;

impl ParseOptions {
    #[must_use]
    pub fn with_target_version(mut self, target_version: PythonVersion) -> Self {
        self.target_version = target_version;
        self
    }

    pub fn target_version(&self) -> PythonVersion {
        self.target_version
    }

    /// Interprets physical source fragments in ordinary string literals.
    ///
    /// Callers that reparse detached source must pass equivalent options to an options-aware
    /// parser entry point. Convenience APIs without parse options use Python interpretation.
    #[must_use]
    pub fn with_string_literal_decoder(mut self, decoder: StringLiteralDecoder) -> Self {
        self.string_literal_decoder = Some(decoder);
        self
    }

    pub(crate) fn has_string_literal_decoder(&self) -> bool {
        self.string_literal_decoder.is_some()
    }

    #[inline]
    pub(crate) fn decode_string_literal_source<'a>(&self, source: &'a str) -> Cow<'a, str> {
        self.string_literal_decoder
            .and_then(|decoder| decoder(source))
            .map_or(Cow::Borrowed(source), |value| {
                Cow::Owned(value.into_string())
            })
    }
}

impl From<Mode> for ParseOptions {
    fn from(mode: Mode) -> Self {
        Self {
            mode,
            target_version: PythonVersion::default(),
            string_literal_decoder: None,
        }
    }
}

impl From<PySourceType> for ParseOptions {
    fn from(source_type: PySourceType) -> Self {
        Self {
            mode: source_type.as_mode(),
            target_version: PythonVersion::default(),
            string_literal_decoder: None,
        }
    }
}
