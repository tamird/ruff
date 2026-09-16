use ruff_db::Db;
use ruff_db::files::{File, system_path_to_file};
use ruff_db::system::{SystemPath, SystemPathBuf};

use crate::source::BazelSource;

/// The caller-selected main repository for Bazel `.bzl` and BUILD sources.
///
/// The root must be absolute, contain no parent traversal, and have a Bazel
/// repository marker. Loads also check the importer's repository and package.
#[salsa::interned(heap_size = ruff_memory_usage::heap_size)]
pub struct BazelRepository<'db> {
    #[returns(ref)]
    root: SystemPathBuf,
}

impl get_size2::GetSize for BazelRepository<'_> {}

#[derive(Clone, Debug, Eq, PartialEq, get_size2::GetSize, thiserror::Error)]
pub enum BazelLoadError {
    #[error("selected root is not a valid marked Bazel repository")]
    InvalidRepository,
    #[error("the importing file is outside the selected Bazel repository")]
    ImporterOutsideRepository,
    #[error("the importing file is neither a .bzl source nor an active BUILD file")]
    InvalidImporter,
    #[error("BUILD is shadowed by BUILD.bazel in its package")]
    InactiveBuildFile,
    #[error("the importing file is outside a Bazel package")]
    ImporterOutsidePackage,
    #[error("relative Bazel source label needs a package directory")]
    MissingRelativeDirectory,
    #[error("relative target directory contains parent traversal")]
    RelativeTargetParentTraversal,
    #[error("the relative target directory is outside the selected Bazel repository")]
    RelativeTargetOutsideRepository,
    #[error("the relative target directory has no BUILD file")]
    RelativeTargetOutsidePackage,
    #[error("external repository labels are not supported")]
    UnsupportedRepository,
    #[error("invalid Bazel source label")]
    InvalidLabel,
    #[error("the selected target package has no BUILD file")]
    UnknownTargetPackage,
    #[error("the selected target belongs to another Bazel repository")]
    RepositoryBoundary,
    #[error("the selected target crosses a Bazel package boundary")]
    PackageBoundary,
    #[error("the selected source file does not exist")]
    NotFound,
}

#[salsa::interned(heap_size = ruff_memory_usage::heap_size)]
struct BazelLoad<'db> {
    repository: BazelRepository<'db>,
    importing_file: File,
    #[returns(ref)]
    label: String,
}

#[salsa::interned(heap_size = ruff_memory_usage::heap_size)]
struct BazelTarget<'db> {
    repository: BazelRepository<'db>,
    #[returns(ref)]
    relative_directory: Option<SystemPathBuf>,
    #[returns(ref)]
    label: String,
    allow_build: bool,
}

/// Resolve a `.bzl` load in the selected main Bazel repository.
///
/// Relative `:file.bzl` labels use the importer's BUILD package. Absolute
/// `//pkg:file.bzl` and `@@//pkg:file.bzl` use the selected main repository,
/// including when the package differs from the importer's. External
/// repositories and nested repository or package boundaries are outside this
/// resolver's scope.
/// Callers must validate `.bzl` load visibility and exported bindings before
/// trusting declarations from the returned source file.
pub fn resolve_bazel_load<'db>(
    db: &'db dyn Db,
    repository: BazelRepository<'db>,
    importing_file: File,
    label: &str,
) -> Result<BazelSource<'db>, BazelLoadError> {
    let load = BazelLoad::new(db, repository, importing_file, label);
    let file = resolve_bazel_load_query(db, load)?;
    Ok(BazelSource::new(db, repository, file))
}

/// Select a main-repository `.bzl` or active BUILD file without an importer.
///
/// Absolute `//` and `@@//` labels use only the selected marked repository.
/// Relative `:` labels require a BUILD file in the supplied directory itself,
/// as Bazel [target patterns] use the current directory. A source load's
/// relative label instead uses its importing source's owning BUILD package.
/// Selected BUILD files must be the active package marker; their loads still
/// resolve only to `.bzl` sources. Only source-first verification of `.bzl`
/// may interpret an optional Ty-only sibling `.bzl.pyi` stub.
///
/// [target patterns]: https://bazel.build/versions/9.0.0/run/build
pub fn resolve_bazel_target<'db>(
    db: &'db dyn Db,
    repository: BazelRepository<'db>,
    relative_directory: Option<&SystemPath>,
    label: &str,
) -> Result<BazelSource<'db>, BazelLoadError> {
    let relative_directory = if label.starts_with(':') {
        relative_directory.map(SystemPath::to_path_buf)
    } else {
        None
    };
    let target = BazelTarget::new(db, repository, relative_directory, label, true);
    let file = resolve_bazel_target_query(db, target)?;
    Ok(BazelSource::new(db, repository, file))
}

#[salsa::tracked(returns(clone))]
fn resolve_bazel_load_query(db: &dyn Db, load: BazelLoad<'_>) -> Result<File, BazelLoadError> {
    let importing_package =
        validate_bazel_source(db, *load.repository(db), *load.importing_file(db))?;
    let relative_directory = load.label(db).starts_with(':').then_some(importing_package);
    let target = BazelTarget::new(
        db,
        *load.repository(db),
        relative_directory,
        load.label(db),
        false,
    );
    resolve_bazel_target_query(db, target)
}

#[salsa::tracked(returns(clone))]
fn resolve_bazel_target_query(
    db: &dyn Db,
    selection: BazelTarget<'_>,
) -> Result<File, BazelLoadError> {
    let repository = *selection.repository(db);
    validate_bazel_repository(db, repository)?;
    let root = repository.root(db);
    let label = selection.label(db);
    let (package_root, target) = if let Some(absolute) = label
        .strip_prefix("//")
        .or_else(|| label.strip_prefix("@@//"))
    {
        let (package, target) = absolute
            .split_once(':')
            .ok_or(BazelLoadError::InvalidLabel)?;
        if !is_valid_package(package) || !is_valid_target(target, *selection.allow_build(db)) {
            return Err(BazelLoadError::InvalidLabel);
        }
        (root.join(package), target)
    } else if label.starts_with('@') {
        return Err(BazelLoadError::UnsupportedRepository);
    } else if let Some(name) = label.strip_prefix(':') {
        if !is_valid_target(name, *selection.allow_build(db)) {
            return Err(BazelLoadError::InvalidLabel);
        }
        let directory = selection
            .relative_directory(db)
            .as_ref()
            .ok_or(BazelLoadError::MissingRelativeDirectory)?;
        if has_parent_component(directory) {
            return Err(BazelLoadError::RelativeTargetParentTraversal);
        }
        if !directory.is_absolute()
            || !directory.starts_with(root)
            || directory
                .ancestors()
                .find(|ancestor| is_repository_root(db, ancestor))
                != Some(root.as_path())
        {
            return Err(BazelLoadError::RelativeTargetOutsideRepository);
        }
        if !is_package(db, directory) {
            return Err(BazelLoadError::RelativeTargetOutsidePackage);
        }
        (directory.clone(), name)
    } else {
        return Err(BazelLoadError::InvalidLabel);
    };

    let source_path = package_root.join(target);
    if find_ancestor(db, &source_path, None, is_repository_root).as_deref() != Some(root.as_path())
    {
        return Err(BazelLoadError::RepositoryBoundary);
    }
    if !is_package(db, &package_root) {
        return Err(BazelLoadError::UnknownTargetPackage);
    }
    if source_path.parent().is_some_and(|parent| {
        parent
            .ancestors()
            .take_while(|directory| *directory != package_root.as_path())
            .any(|directory| is_package(db, directory))
    }) {
        return Err(BazelLoadError::PackageBoundary);
    }

    let file = system_path_to_file(db, &source_path).map_err(|_| BazelLoadError::NotFound)?;
    if *selection.allow_build(db) && matches!(target, "BUILD" | "BUILD.bazel") {
        validate_bazel_source(db, repository, file)?;
    }
    Ok(file)
}

fn validate_bazel_repository(
    db: &dyn Db,
    repository: BazelRepository<'_>,
) -> Result<(), BazelLoadError> {
    let root = repository.root(db);
    if !root.is_absolute() || has_parent_component(root) || !is_repository_root(db, root) {
        return Err(BazelLoadError::InvalidRepository);
    }
    Ok(())
}

/// Validate the selected repository and a source's owning BUILD package.
/// A source reached via `load()` and one selected directly have the same owner.
pub(crate) fn validate_bazel_source(
    db: &dyn Db,
    repository: BazelRepository<'_>,
    file: File,
) -> Result<SystemPathBuf, BazelLoadError> {
    validate_bazel_repository(db, repository)?;
    let root = repository.root(db);

    let importing_path = file
        .path(db)
        .as_system_path()
        .ok_or(BazelLoadError::ImporterOutsideRepository)?;
    let build = matches!(importing_path.file_name(), Some("BUILD" | "BUILD.bazel"));
    if !build && importing_path.extension() != Some("bzl") {
        return Err(BazelLoadError::InvalidImporter);
    }
    if has_parent_component(importing_path)
        || !importing_path.starts_with(root)
        || find_ancestor(db, importing_path, None, is_repository_root).as_deref()
            != Some(root.as_path())
    {
        return Err(BazelLoadError::ImporterOutsideRepository);
    }
    let package = find_ancestor(db, importing_path, Some(root), is_package)
        .ok_or(BazelLoadError::ImporterOutsidePackage)?;
    if build && importing_path.parent() != Some(package.as_path()) {
        return Err(BazelLoadError::ImporterOutsidePackage);
    }
    if importing_path.file_name() == Some("BUILD")
        && system_path_to_file(db, package.join("BUILD.bazel")).is_ok()
    {
        return Err(BazelLoadError::InactiveBuildFile);
    }
    Ok(package)
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

fn has_parent_component(path: &SystemPath) -> bool {
    path.components()
        .any(|component| component.as_str() == "..")
}

/// Select the nearest marked main repository containing the current directory.
/// An explicit CLI workspace may instead choose a different marked root.
pub fn find_bazel_repository(db: &dyn Db, cwd: &SystemPath) -> Option<SystemPathBuf> {
    cwd.ancestors()
        .find(|directory| is_repository_root(db, directory))
        .map(SystemPath::to_path_buf)
}

fn is_repository_root(db: &dyn Db, directory: &SystemPath) -> bool {
    ["MODULE.bazel", "REPO.bazel", "WORKSPACE.bazel", "WORKSPACE"]
        .into_iter()
        .any(|marker| system_path_to_file(db, directory.join(marker)).is_ok())
}

fn is_package(db: &dyn Db, directory: &SystemPath) -> bool {
    ["BUILD.bazel", "BUILD"]
        .into_iter()
        .any(|marker| system_path_to_file(db, directory.join(marker)).is_ok())
}

#[expect(
    clippy::case_sensitive_file_extension_comparisons,
    reason = "Bazel requires the exact lowercase .bzl suffix"
)]
fn is_valid_target(target: &str, allow_build: bool) -> bool {
    !target.contains(':')
        && (target.ends_with(".bzl") || (allow_build && matches!(target, "BUILD" | "BUILD.bazel")))
        && is_valid_relative_path(target, false)
        && target
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || TARGET_PUNCTUATION.contains(&byte))
}

// Bazel 9 allows spaces and dots in package names, but not arbitrary Unicode
// or components made entirely of dots.
// <https://bazel.build/versions/9.0.0/concepts/labels>
fn is_valid_package(package: &str) -> bool {
    is_valid_relative_path(package, true)
        && (package.is_empty()
            || package
                .split('/')
                .all(|component| component.bytes().any(|byte| byte != b'.')))
        && package
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || PACKAGE_PUNCTUATION.contains(&byte))
}

const TARGET_PUNCTUATION: &[u8] = b"!%-@^_\"#$&'()*+,;<=>?[]{|}~/.";
const PACKAGE_PUNCTUATION: &[u8] = b"! \"#$%&'()*+,-.;<=>?@[]^_`{|}/";

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
mod tests;
