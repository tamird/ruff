use ruff_db::files::{File, system_path_to_file};
use ruff_db::system::SystemPathBuf;

use crate::{Db, ModuleResolveMode, search_paths};

#[derive(Clone, Debug, Eq, PartialEq, thiserror::Error)]
pub enum StarlarkLoadError {
    #[error("repository-qualified labels are not supported yet")]
    UnsupportedRepository,
    #[error("invalid Starlark load label")]
    InvalidLabel,
    #[error("the importing file is outside a first-party source root")]
    UnknownWorkspace,
    #[error("the loaded file does not exist")]
    NotFound,
}

/// Resolves a main-repository Starlark load label to its source or sibling stub.
pub fn resolve_starlark_load(
    db: &dyn Db,
    importing_file: File,
    label: &str,
) -> Result<File, StarlarkLoadError> {
    if label.starts_with('@') {
        return Err(StarlarkLoadError::UnsupportedRepository);
    }

    let importing_path = importing_file
        .path(db)
        .as_system_path()
        .ok_or(StarlarkLoadError::UnknownWorkspace)?;
    let workspace_root = search_paths(db, ModuleResolveMode::StubsAllowed)
        .filter(|search_path| search_path.is_first_party())
        .filter_map(|search_path| search_path.as_system_path())
        .find(|root| importing_path.strip_prefix(root).is_ok())
        .ok_or(StarlarkLoadError::UnknownWorkspace)?;

    let target = if let Some(absolute) = label.strip_prefix("//") {
        let (package, target) = absolute
            .split_once(':')
            .ok_or(StarlarkLoadError::InvalidLabel)?;
        if !is_valid_relative_path(package, true) || !is_valid_target(target) {
            return Err(StarlarkLoadError::InvalidLabel);
        }
        workspace_root.join(package).join(target)
    } else if let Some(target) = label.strip_prefix(':') {
        if !is_valid_target(target) {
            return Err(StarlarkLoadError::InvalidLabel);
        }
        importing_path
            .parent()
            .ok_or(StarlarkLoadError::InvalidLabel)?
            .join(target)
    } else {
        return Err(StarlarkLoadError::InvalidLabel);
    };

    let implementation =
        system_path_to_file(db, &target).map_err(|_| StarlarkLoadError::NotFound)?;
    let stub = SystemPathBuf::from(format!("{}.pyi", target.as_str()));
    Ok(system_path_to_file(db, &stub).unwrap_or(implementation))
}

fn is_valid_target(target: &str) -> bool {
    !target.contains(':') && target.ends_with(".bzl") && is_valid_relative_path(target, false)
}

fn is_valid_relative_path(path: &str, allow_empty: bool) -> bool {
    if path.is_empty() {
        return allow_empty;
    }

    !path.contains('\\')
        && path
            .split('/')
            .all(|component| !matches!(component, "" | "." | ".."))
}

#[cfg(test)]
mod tests {
    use ruff_db::files::{File, system_path_to_file};
    use ruff_db::system::{DbWithTestSystem, DbWithWritableSystem};

    use crate::testing::{TestCase, TestCaseBuilder};

    use super::{StarlarkLoadError, resolve_starlark_load};

    #[test]
    fn resolves_absolute_and_relative_labels_with_stub_precedence() {
        let TestCase { db, src, .. } = TestCaseBuilder::new()
            .with_src_files(&[
                ("app/use.bzl", ""),
                ("app/lib.bzl", ""),
                ("app/lib.bzl.pyi", ""),
                ("root.bzl", ""),
            ])
            .build();
        let importer = system_path_to_file(&db, src.join("app/use.bzl")).unwrap();

        for label in ["//app:lib.bzl", ":lib.bzl"] {
            let resolved = resolve_starlark_load(&db, importer, label).unwrap();
            assert_eq!(resolved.path(&db), &src.join("app/lib.bzl.pyi"));
        }

        let resolved = resolve_starlark_load(&db, importer, "//:root.bzl").unwrap();
        assert_eq!(resolved.path(&db), &src.join("root.bzl"));
    }

    #[test]
    fn rejects_unsupported_or_escaping_labels() {
        let TestCase { db, src, .. } = TestCaseBuilder::new()
            .with_src_files(&[
                ("app/use.bzl", ""),
                ("app/stub-only.bzl.pyi", ""),
                ("outside.bzl", ""),
            ])
            .build();
        let importer = system_path_to_file(&db, src.join("app/use.bzl")).unwrap();

        assert_eq!(
            resolve_starlark_load(&db, importer, "@repo//pkg:lib.bzl"),
            Err(StarlarkLoadError::UnsupportedRepository)
        );
        assert_eq!(
            resolve_starlark_load(&db, importer, ":../outside.bzl"),
            Err(StarlarkLoadError::InvalidLabel)
        );
        assert_eq!(
            resolve_starlark_load(&db, importer, ":stub-only.bzl"),
            Err(StarlarkLoadError::NotFound)
        );
    }

    #[test]
    fn observes_stub_addition_and_implementation_removal() -> anyhow::Result<()> {
        let TestCase { mut db, src, .. } = TestCaseBuilder::new()
            .with_src_files(&[("app/use.bzl", ""), ("app/lib.bzl", "")])
            .build();
        let importer = system_path_to_file(&db, src.join("app/use.bzl"))?;
        let implementation = src.join("app/lib.bzl");
        let stub = src.join("app/lib.bzl.pyi");

        let resolved = resolve_starlark_load(&db, importer, ":lib.bzl")?;
        assert_eq!(resolved.path(&db), &implementation);

        db.write_file(&stub, "")?;
        let resolved = resolve_starlark_load(&db, importer, ":lib.bzl")?;
        assert_eq!(resolved.path(&db), &stub);

        db.memory_file_system().remove_file(&implementation)?;
        File::sync_path(&mut db, &implementation);
        assert_eq!(
            resolve_starlark_load(&db, importer, ":lib.bzl"),
            Err(StarlarkLoadError::NotFound)
        );

        Ok(())
    }
}
