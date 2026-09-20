use crate::{Db, platform::PythonPlatform};

use ruff_db::files::File;
use ruff_db::system::SystemPath;
use ruff_db::vendored::VendoredFileSystem;
use ruff_python_ast::PythonVersion;
use ruff_python_ast::name::Name;
use ty_module_resolver::{ResolverEnvironment, SearchPaths};
use ty_site_packages::PythonVersionWithSource;

use crate::ProgramFile;

// Re-export the misconfiguration strategy types from ty_module_resolver.
pub use ty_module_resolver::{FallibleStrategy, MisconfigurationStrategy, UseDefaultStrategy};

#[salsa::interned(debug, constructor = new_internal, heap_size=ruff_memory_usage::heap_size)]
pub struct Program<'db> {
    #[returns(ref)]
    pub python_platform: PythonPlatform,

    #[returns(copy)]
    pub resolver_environment: ResolverEnvironment<'db>,

    /// Identifies the embedding application's semantic environment.
    ///
    /// Programs with different environments share parsing and module resolution, but not
    /// semantic queries. This is a stable identity, not a configuration revision: queries
    /// must read the environment's configuration through tracked database inputs.
    #[returns(ref)]
    pub semantic_namespace: Option<Name>,
}

impl get_size2::GetSize for Program<'_> {}

impl<'db> Program<'db> {
    pub fn new(
        db: &'db dyn Db,
        python_platform: &PythonPlatform,
        resolver_environment: ResolverEnvironment<'db>,
    ) -> Self {
        Self::new_internal(db, python_platform, resolver_environment, None)
    }

    /// Creates a program whose semantic configuration belongs to an embedding application.
    /// The application must give each namespace one meaning within a database.
    pub fn with_semantic_namespace(
        db: &'db dyn Db,
        python_platform: &PythonPlatform,
        resolver_environment: ResolverEnvironment<'db>,
        namespace: &Name,
    ) -> Self {
        Self::new_internal(
            db,
            python_platform,
            resolver_environment,
            Some(namespace.clone()),
        )
    }

    /// Returns the Python support environment shared by application namespaces using the same
    /// platform and resolver. Typeshed and other Python declarations must keep canonical nominal
    /// identities when their types are used by an embedded program.
    #[must_use]
    pub fn without_semantic_namespace(self, db: &'db dyn Db) -> Self {
        if self.semantic_namespace(db).is_none() {
            self
        } else {
            Self::new(db, self.python_platform(db), self.resolver_environment(db))
        }
    }

    /// Creates a program from settings whose search roots have already been registered.
    pub fn from_settings(db: &'db dyn Db, settings: &ProgramSettings) -> Self {
        let ProgramSettings {
            python_version,
            python_platform,
            search_paths,
        } = settings;

        let resolver_environment =
            ResolverEnvironment::new(db, python_version.version, search_paths);
        Program::new(db, python_platform, resolver_environment)
    }

    pub fn python_version(self, db: &'db dyn Db) -> PythonVersion {
        self.resolver_environment(db).python_version(db)
    }

    pub fn search_paths(self, db: &'db dyn Db) -> &'db SearchPaths {
        self.resolver_environment(db).search_paths(db)
    }

    pub fn program_file(self, db: &'db dyn Db, file: File) -> ProgramFile<'db> {
        ProgramFile::new(db, file, self)
    }

    pub fn custom_stdlib_search_path(self, db: &'db dyn Db) -> Option<&'db SystemPath> {
        self.search_paths(db).custom_stdlib()
    }
}

#[derive(Clone, Debug, Eq, PartialEq, get_size2::GetSize)]
pub struct ProgramSettings {
    pub python_version: PythonVersionWithSource,
    pub python_platform: PythonPlatform,
    pub search_paths: SearchPaths,
}

impl ProgramSettings {
    pub fn empty(vendored: &VendoredFileSystem) -> Self {
        Self {
            python_version: PythonVersionWithSource::default(),
            python_platform: PythonPlatform::default(),
            search_paths: SearchPaths::empty(vendored),
        }
    }
}

#[cfg(test)]
mod tests {
    use ruff_db::files::system_path_to_file;

    use super::Program;
    use crate::db::TestProgramDb;
    use crate::db::tests::TestDbBuilder;

    #[test]
    fn semantic_namespaces_share_parser_and_resolver() -> anyhow::Result<()> {
        let db = TestDbBuilder::new()
            .with_file("/src/shared.py", "value = 1")
            .build()?;
        let file = system_path_to_file(&db, "/src/shared.py")?;
        let default = db.program();
        let first = Program::with_semantic_namespace(
            &db,
            default.python_platform(&db),
            default.resolver_environment(&db),
            &"first".into(),
        );
        let second = Program::with_semantic_namespace(
            &db,
            default.python_platform(&db),
            default.resolver_environment(&db),
            &"second".into(),
        );
        let default = default.program_file(&db, file);
        let first = first.program_file(&db, file);
        let second = second.program_file(&db, file);
        assert_ne!(default, first);
        assert_ne!(first, second);
        assert_eq!(first.python_file(&db), second.python_file(&db));
        assert_eq!(default.python_file(&db), first.python_file(&db));
        assert_eq!(first.resolver_file(&db), second.resolver_file(&db));
        assert_eq!(default.resolver_file(&db), first.resolver_file(&db));
        Ok(())
    }
}
