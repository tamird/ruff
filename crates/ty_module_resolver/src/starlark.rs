use ruff_db::files::{File, system_path_to_file};
use ruff_db::system::{SystemPath, SystemPathBuf};

use crate::{Db, ModuleResolveMode, search_paths};

#[derive(Clone, Debug, Eq, PartialEq, thiserror::Error)]
pub enum StarlarkLoadError {
    #[error("repository-qualified labels are not supported yet")]
    UnsupportedRepository,
    #[error("invalid Starlark load label")]
    InvalidLabel,
    #[error("the importing file is outside a Bazel repository")]
    UnknownWorkspace,
    #[error("the Starlark file is outside a Bazel package")]
    UnknownPackage,
    #[error("the load target crosses a Bazel package boundary")]
    PackageBoundary,
    #[error("the loaded file does not exist")]
    NotFound,
}

#[salsa::interned(heap_size=ruff_memory_usage::heap_size)]
struct StarlarkLoad<'db> {
    importing_file: File,
    #[returns(ref)]
    label: String,
}

/// Resolves a main-repository Starlark load label to its source or sibling stub.
pub fn resolve_starlark_load(
    db: &dyn Db,
    importing_file: File,
    label: &str,
) -> Result<File, StarlarkLoadError> {
    resolve_starlark_load_query(db, StarlarkLoad::new(db, importing_file, label))
}

#[salsa::tracked]
fn resolve_starlark_load_query(
    db: &dyn Db,
    load: StarlarkLoad<'_>,
) -> Result<File, StarlarkLoadError> {
    let importing_file = load.importing_file(db);
    let label = load.label(db);
    if label.starts_with('@') {
        return Err(StarlarkLoadError::UnsupportedRepository);
    }

    let importing_path = importing_file
        .path(db)
        .as_system_path()
        .ok_or(StarlarkLoadError::UnknownWorkspace)?;
    search_paths(db, ModuleResolveMode::StubsAllowed)
        .filter(|search_path| search_path.is_first_party())
        .filter_map(|search_path| search_path.as_system_path())
        .filter(|root| importing_path.strip_prefix(root).is_ok())
        .max_by_key(|root| root.as_str().len())
        .ok_or(StarlarkLoadError::UnknownWorkspace)?;
    let workspace_root = find_ancestor(db, importing_path, None, is_workspace_root)
        .ok_or(StarlarkLoadError::UnknownWorkspace)?;

    let (package_root, target) = if let Some(absolute) = label.strip_prefix("//") {
        let (package, target) = absolute
            .split_once(':')
            .ok_or(StarlarkLoadError::InvalidLabel)?;
        if !is_valid_relative_path(package, true) || !is_valid_target(target) {
            return Err(StarlarkLoadError::InvalidLabel);
        }
        let package_root = workspace_root.join(package);
        if !is_package(db, &package_root) {
            return Err(StarlarkLoadError::UnknownPackage);
        }
        let target = package_root.join(target);
        (package_root, target)
    } else if let Some(target) = label.strip_prefix(':') {
        if !is_valid_target(target) {
            return Err(StarlarkLoadError::InvalidLabel);
        }
        let package_root = find_ancestor(db, importing_path, Some(&workspace_root), is_package)
            .ok_or(StarlarkLoadError::UnknownPackage)?;
        let target = package_root.join(target);
        (package_root, target)
    } else {
        return Err(StarlarkLoadError::InvalidLabel);
    };

    if target.parent().is_some_and(|parent| {
        parent
            .ancestors()
            .take_while(|directory| *directory != package_root.as_path())
            .any(|directory| is_package(db, directory))
    }) {
        return Err(StarlarkLoadError::PackageBoundary);
    }

    let implementation =
        system_path_to_file(db, &target).map_err(|_| StarlarkLoadError::NotFound)?;
    let stub = SystemPathBuf::from(format!("{}.pyi", target.as_str()));
    Ok(system_path_to_file(db, &stub).unwrap_or(implementation))
}

fn find_ancestor(
    db: &dyn Db,
    path: &SystemPath,
    boundary: Option<&SystemPath>,
    predicate: impl Fn(&dyn Db, &SystemPath) -> bool,
) -> Option<SystemPathBuf> {
    let mut directory = path.parent()?;
    loop {
        if predicate(db, directory) {
            return Some(directory.to_path_buf());
        }
        if boundary.is_some_and(|boundary| directory == boundary) {
            return None;
        }
        directory = directory.parent()?;
    }
}

fn is_workspace_root(db: &dyn Db, directory: &SystemPath) -> bool {
    ["MODULE.bazel", "REPO.bazel", "WORKSPACE.bazel", "WORKSPACE"]
        .into_iter()
        .any(|marker| system_path_to_file(db, directory.join(marker)).is_ok())
}

fn is_package(db: &dyn Db, directory: &SystemPath) -> bool {
    ["BUILD.bazel", "BUILD"]
        .into_iter()
        .any(|marker| system_path_to_file(db, directory.join(marker)).is_ok())
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
    fn resolves_labels_from_repository_and_package_roots() {
        let TestCase { db, src, .. } = TestCaseBuilder::new()
            .with_src_files(&[
                ("MODULE.bazel", ""),
                ("BUILD.bazel", ""),
                ("app/BUILD.bazel", ""),
                ("app/subdir/use.bzl", ""),
                ("app/lib.bzl", ""),
                ("app/lib.bzl.pyi", ""),
                ("root.bzl", ""),
            ])
            .build();
        let importer = system_path_to_file(&db, src.join("app/subdir/use.bzl")).unwrap();

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
                ("MODULE.bazel", ""),
                ("BUILD.bazel", ""),
                ("app/BUILD.bazel", ""),
                ("app/use.bzl", ""),
                ("app/sub/BUILD.bazel", ""),
                ("app/sub/lib.bzl", ""),
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
        assert_eq!(
            resolve_starlark_load(&db, importer, "//missing:lib.bzl"),
            Err(StarlarkLoadError::UnknownPackage)
        );
        for label in ["//app:sub/lib.bzl", ":sub/lib.bzl"] {
            assert_eq!(
                resolve_starlark_load(&db, importer, label),
                Err(StarlarkLoadError::PackageBoundary)
            );
        }
        assert_eq!(
            resolve_starlark_load(&db, importer, "//app/sub:lib.bzl")
                .unwrap()
                .path(&db),
            &src.join("app/sub/lib.bzl")
        );
    }

    #[test]
    fn rejects_files_outside_bazel_repositories_and_packages() {
        let TestCase { mut db, src, .. } = TestCaseBuilder::new()
            .with_src_files(&[("app/use.bzl", ""), ("app/lib.bzl", "")])
            .build();
        let importer = system_path_to_file(&db, src.join("app/use.bzl")).unwrap();

        assert_eq!(
            resolve_starlark_load(&db, importer, "//app:lib.bzl"),
            Err(StarlarkLoadError::UnknownWorkspace)
        );

        db.write_file(src.join("MODULE.bazel"), "").unwrap();
        assert_eq!(
            resolve_starlark_load(&db, importer, ":lib.bzl"),
            Err(StarlarkLoadError::UnknownPackage)
        );
    }

    #[test]
    fn observes_stub_addition_and_implementation_removal() -> anyhow::Result<()> {
        let TestCase { mut db, src, .. } = TestCaseBuilder::new()
            .with_src_files(&[
                ("MODULE.bazel", ""),
                ("app/BUILD.bazel", ""),
                ("app/use.bzl", ""),
                ("app/lib.bzl", ""),
            ])
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
