//! A captured Starlark graph analyzed through Ty's semantic database.

use std::collections::HashMap;
use std::sync::Arc;

use anyhow::{Context, Result};
use ruff_db::diagnostic::{Diagnostic, Severity, Span, UnifiedFile};
use ruff_db::files::{File, FileRootKind, Files, system_path_to_file};
use ruff_db::source::source_text;
use ruff_db::system::{InMemorySystem, MemoryFileSystem, System, SystemPath};
use ruff_db::vendored::VendoredFileSystem;
use ruff_python_ast::PythonVersion;
use ruff_source_file::{SourceFile, SourceFileBuilder};
use ty_module_resolver::SearchPathSettings;
use ty_python_core::ProgramFile;
use ty_python_core::platform::PythonPlatform;
use ty_python_core::program::{FallibleStrategy, Program, ProgramSettings};
use ty_python_semantic::dependency::DependencyMetadata;
use ty_python_semantic::lint::{LintRegistry, LintSource, RuleSelection};
use ty_python_semantic::{AnalysisSettings, PythonVersionWithSource, default_lint_registry};

const STDLIB: &[(&str, &str)] = &[
    (
        "typing.pyi",
        include_str!("../resources/starlark/typing.pyi"),
    ),
    ("types.pyi", include_str!("../resources/starlark/types.pyi")),
    ("_typeshed.pyi", "from types import NoneType as NoneType\n"),
    ("collections/__init__.pyi", ""),
    (
        "collections/abc.pyi",
        include_str!("../resources/starlark/collections/abc.pyi"),
    ),
    (
        "VERSIONS",
        "builtins: 3.0-\ntyping: 3.0-\ntypes: 3.0-\n_typeshed: 3.0-\ncollections: 3.0-\ncollections.abc: 3.0-\n",
    ),
];

#[derive(Clone, Copy)]
pub(crate) enum StarlarkProfile {
    Bazel,
    Hosted,
}

/// The database reads only captured text and embedded builtin declarations.
/// File handles never cross this database's boundary; diagnostics own their
/// sources before the database is dropped.
#[salsa::db]
#[derive(Clone)]
pub(crate) struct AnalysisDb {
    storage: salsa::Storage<Self>,
    files: Files,
    system: InMemorySystem,
    vendored: VendoredFileSystem,
    settings: ProgramSettings,
    rules: Arc<RuleSelection>,
    analysis: Arc<AnalysisSettings>,
    sources: HashMap<File, SourceFile>,
}

impl AnalysisDb {
    pub(crate) fn new(profile: StarlarkProfile) -> Result<Self> {
        let fs = MemoryFileSystem::new();
        fs.create_directory_all("/stdlib/stdlib/collections")?;
        fs.create_directory_all("/sources")?;
        for (path, text) in STDLIB {
            fs.write_file(format!("/stdlib/stdlib/{path}"), text)?;
        }
        // Canonical classes must remain in `builtins` for Ty's KnownClass
        // recognition. Share method declarations, then select host signatures
        // and type-value capabilities within that same module.
        let profile = match profile {
            StarlarkProfile::Bazel => include_str!("../resources/starlark/bazel.pyi"),
            StarlarkProfile::Hosted => include_str!("../resources/starlark/hosted.pyi"),
        };
        let builtins = format!(
            "{}\n{profile}",
            include_str!("../resources/starlark/builtins.pyi")
        );
        fs.write_file("/stdlib/stdlib/builtins.pyi", &builtins)?;
        let system = InMemorySystem::from_memory_fs(fs);
        let vendored = VendoredFileSystem::default();
        let search_settings = SearchPathSettings {
            extra_paths: Vec::new(),
            src_roots: Vec::new(),
            custom_typeshed: Some("/stdlib".into()),
            site_packages_paths: Vec::new(),
            real_stdlib_path: None,
        };
        let search_paths =
            search_settings.to_search_paths(&system, &vendored, &FallibleStrategy)?;
        let registry = default_lint_registry();
        let mut rules = RuleSelection::from_registry(registry);
        rules.enable(
            registry.get("possibly-missing-import")?,
            Severity::Error,
            LintSource::File,
        );
        let python_version = PythonVersionWithSource {
            version: PythonVersion::PY310,
            ..PythonVersionWithSource::default()
        };
        let db = Self {
            storage: salsa::Storage::default(),
            files: Files::default(),
            system,
            vendored,
            settings: ProgramSettings {
                python_version,
                python_platform: PythonPlatform::default(),
                search_paths,
            },
            rules: Arc::new(rules),
            analysis: Arc::new(AnalysisSettings::default()),
            sources: HashMap::new(),
        };
        db.settings.search_paths.try_register_static_roots(&db);
        db.files
            .try_add_root(&db, SystemPath::new("/sources"), FileRootKind::Project);
        Ok(db)
    }

    pub(crate) fn add_source(&mut self, source: SourceFile) -> Result<File> {
        let path = format!("/sources/{}.star", self.sources.len());
        self.system.fs().write_file(&path, source.source_text())?;
        let file = system_path_to_file(self, &path)?;
        self.sources.insert(file, source);
        Ok(file)
    }

    pub(crate) fn program(&self) -> Program<'_> {
        Program::from_starlark_settings(self, &self.settings)
    }

    pub(crate) fn freeze(&self, diagnostics: &mut [Diagnostic]) -> Result<()> {
        let mut sources = self.sources.clone();
        for diagnostic in diagnostics {
            diagnostic.remove_fix();
            self.freeze_annotations(diagnostic.annotations_mut(), &mut sources)?;
            for sub in diagnostic.sub_diagnostics_mut() {
                self.freeze_annotations(sub.annotations_mut(), &mut sources)?;
            }
        }
        Ok(())
    }

    fn freeze_annotations<'a>(
        &self,
        annotations: impl Iterator<Item = &'a mut ruff_db::diagnostic::Annotation>,
        sources: &mut HashMap<File, SourceFile>,
    ) -> Result<()> {
        for annotation in annotations {
            let span = annotation.get_span();
            let UnifiedFile::Ty(file) = span.file() else {
                continue;
            };
            let captured = sources.entry(*file).or_insert_with(|| {
                let source = source_text(self, *file);
                let path = file.path(self);
                let name = path
                    .as_str()
                    .strip_prefix("/stdlib/stdlib/")
                    .unwrap_or(path.as_str());
                SourceFileBuilder::new(name, source.as_str()).finish()
            });
            if let Some(range) = span.range() {
                captured
                    .source_text()
                    .get(range.start().to_usize()..range.end().to_usize())
                    .context("semantic diagnostic is outside its captured source")?;
            }
            let frozen = Span::from(captured.clone()).with_optional_range(span.range());
            annotation.set_span(frozen);
        }
        Ok(())
    }
}

#[salsa::db]
impl ruff_db::Db for AnalysisDb {
    fn vendored(&self) -> &VendoredFileSystem {
        &self.vendored
    }
    fn system(&self) -> &dyn System {
        &self.system
    }
    fn files(&self) -> &Files {
        &self.files
    }
}

#[salsa::db]
impl ty_module_resolver::Db for AnalysisDb {}

#[salsa::db]
impl ty_python_core::Db for AnalysisDb {
    fn should_check_file(&self, file: File) -> bool {
        self.sources.contains_key(&file)
    }
}

#[salsa::db]
impl ty_python_semantic::Db for AnalysisDb {
    fn check_file(&self, file: File) -> Vec<Diagnostic> {
        ty_python_semantic::check_file_unwrap(self, self.program_file(file))
    }
    fn program_file(&self, file: File) -> ProgramFile<'_> {
        self.program().program_file(self, file)
    }
    fn python_version_with_source(&self, _file: File) -> &PythonVersionWithSource {
        &self.settings.python_version
    }
    fn rule_selection(&self, _file: File) -> &RuleSelection {
        &self.rules
    }
    fn lint_registry(&self) -> &LintRegistry {
        default_lint_registry()
    }
    fn analysis_settings(&self, _file: File) -> &AnalysisSettings {
        &self.analysis
    }
    fn dependency_metadata(&self, _file: File) -> Option<&DependencyMetadata> {
        None
    }
    fn verbose(&self) -> bool {
        false
    }
    fn is_open_file(&self, _file: File) -> bool {
        false
    }
    fn dyn_clone(&self) -> Box<dyn ty_python_semantic::Db> {
        Box::new(self.clone())
    }
}

#[salsa::db]
impl salsa::Database for AnalysisDb {}
