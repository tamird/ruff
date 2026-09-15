use ruff_db::Db;
use ruff_db::files::{File, system_path_to_file};
use ruff_db::system::{SystemPath, SystemPathBuf};

/// The caller-selected main repository for Bazel `.bzl` loads.
///
/// The root must be absolute and contain a Bazel repository marker. Resolution
/// checks the marker and the importer's ownership before interpreting a label.
#[salsa::interned(heap_size = ruff_memory_usage::heap_size)]
pub struct BazelRepository<'db> {
    #[returns(ref)]
    root: SystemPathBuf,
}

impl get_size2::GetSize for BazelRepository<'_> {}

/// A Bazel source file and its optional, ty-only type stub.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct BazelLoadedFile {
    pub source: File,
    pub stub: Option<File>,
}

impl BazelLoadedFile {
    pub fn type_file(self) -> File {
        self.stub.unwrap_or(self.source)
    }
}

#[derive(Clone, Debug, Eq, PartialEq, thiserror::Error)]
pub enum BazelLoadError {
    #[error("selected root is not a Bazel repository")]
    InvalidRepository,
    #[error("the importing file is outside the selected Bazel repository")]
    ImporterOutsideRepository,
    #[error("the importing file is not a .bzl source")]
    InvalidImporter,
    #[error("the importing file is outside a Bazel package")]
    ImporterOutsidePackage,
    #[error("external repository labels are not supported")]
    UnsupportedRepository,
    #[error("invalid Bazel load label")]
    InvalidLabel,
    #[error("the load target package has no BUILD file")]
    UnknownTargetPackage,
    #[error("the load target belongs to another Bazel repository")]
    RepositoryBoundary,
    #[error("the load target crosses a Bazel package boundary")]
    PackageBoundary,
    #[error("the loaded .bzl source file does not exist")]
    NotFound,
}

#[salsa::interned(heap_size = ruff_memory_usage::heap_size)]
struct BazelLoad<'db> {
    repository: BazelRepository<'db>,
    importing_file: File,
    #[returns(ref)]
    label: String,
}

/// Resolve a `.bzl` load in the selected main Bazel repository.
///
/// Relative `:file.bzl` labels use the importer's BUILD package. Absolute
/// `//pkg:file.bzl` labels use the package named in the label, including when
/// that package differs from the importer's. External repositories and nested
/// repository or package boundaries are outside this resolver's scope.
/// Callers must validate `.bzl` load visibility and exported bindings before
/// trusting declarations from the returned source file.
pub fn resolve_bazel_load(
    db: &dyn Db,
    repository: BazelRepository<'_>,
    importing_file: File,
    label: &str,
) -> Result<BazelLoadedFile, BazelLoadError> {
    let load = BazelLoad::new(db, repository, importing_file, label);
    resolve_bazel_load_query(db, load)
}

#[salsa::tracked(returns(clone))]
fn resolve_bazel_load_query(
    db: &dyn Db,
    load: BazelLoad<'_>,
) -> Result<BazelLoadedFile, BazelLoadError> {
    let root = load.repository(db).root(db);
    if !root.as_path().is_absolute() || !is_repository_root(db, root) {
        return Err(BazelLoadError::InvalidRepository);
    }

    let importing_path = load
        .importing_file(db)
        .path(db)
        .as_system_path()
        .ok_or(BazelLoadError::ImporterOutsideRepository)?;
    if importing_path.extension() != Some("bzl") {
        return Err(BazelLoadError::InvalidImporter);
    }
    if !importing_path.starts_with(root)
        || find_ancestor(db, importing_path, None, is_repository_root).as_deref()
            != Some(root.as_path())
    {
        return Err(BazelLoadError::ImporterOutsideRepository);
    }
    let importing_package = find_ancestor(db, importing_path, Some(root), is_package)
        .ok_or(BazelLoadError::ImporterOutsidePackage)?;

    let label = load.label(db);
    let (package_root, target) = if label.starts_with('@') {
        return Err(BazelLoadError::UnsupportedRepository);
    } else if let Some(absolute) = label.strip_prefix("//") {
        let (package, target) = absolute
            .split_once(':')
            .ok_or(BazelLoadError::InvalidLabel)?;
        if !is_valid_relative_path(package, true) || !is_valid_target(target) {
            return Err(BazelLoadError::InvalidLabel);
        }
        (root.join(package), target)
    } else if let Some(target) = label.strip_prefix(':') {
        if !is_valid_target(target) {
            return Err(BazelLoadError::InvalidLabel);
        }
        (importing_package, target)
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

    let source = system_path_to_file(db, &source_path).map_err(|_| BazelLoadError::NotFound)?;
    let stub_path = SystemPathBuf::from(format!("{}.pyi", source_path.as_str()));
    let stub = system_path_to_file(db, &stub_path).ok();
    Ok(BazelLoadedFile { source, stub })
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
mod tests;
