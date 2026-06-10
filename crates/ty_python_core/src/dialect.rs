use ruff_db::files::File;
use ruff_db::system::SystemPath;
use ruff_python_ast::PySourceType;

use crate::Db;

/// The language dialect used by a source file.
///
/// This is separate from [`PySourceType`], which describes how Python-shaped
/// source is stored (for example, as an implementation file or a stub).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SourceDialect {
    Python,
    Starlark,
}

impl SourceDialect {
    /// Returns the dialect for a supported source path.
    pub fn try_from_path(path: &SystemPath) -> Option<Self> {
        if is_starlark_path(path.as_str()) {
            Some(Self::Starlark)
        } else {
            path.extension()
                .and_then(PySourceType::try_from_extension)
                .map(|_| Self::Python)
        }
    }

    /// Returns the dialect for an interned source file.
    ///
    /// Explicitly provided files with unknown extensions retain ty's existing
    /// behavior and are treated as Python.
    pub fn from_file(db: &dyn Db, file: File) -> Self {
        if is_starlark_path(file.path(db).as_str()) {
            Self::Starlark
        } else {
            Self::Python
        }
    }
}

fn is_starlark_path(path: &str) -> bool {
    path.ends_with(".bzl") || path.ends_with(".bzl.pyi")
}

#[cfg(test)]
mod tests {
    use ruff_db::system::SystemPath;

    use super::SourceDialect;

    #[test]
    fn dialect_from_path() {
        assert_eq!(
            SourceDialect::try_from_path(SystemPath::new("rules.bzl")),
            Some(SourceDialect::Starlark)
        );
        assert_eq!(
            SourceDialect::try_from_path(SystemPath::new("rules.bzl.pyi")),
            Some(SourceDialect::Starlark)
        );
        assert_eq!(
            SourceDialect::try_from_path(SystemPath::new("rules.py")),
            Some(SourceDialect::Python)
        );
        assert_eq!(
            SourceDialect::try_from_path(SystemPath::new("README.md")),
            None
        );
    }
}
