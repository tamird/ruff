use crate::dependency::DependencyMetadata;
use crate::lint::{LintRegistry, RuleSelection};
use crate::provided::{
    BuiltinUsage, ProvidedBindingResolution, ProvidedBindingValue, ProvidedCallResult,
};
use crate::types::CheckedCall;
use crate::{AnalysisSettings, PythonVersionWithSource};
use ruff_db::diagnostic::Diagnostic;
use ruff_db::files::File;
use ty_python_core::definition::Definition;
use ty_python_core::{Db as PythonCoreDb, ProgramFile};

/// Selects the facts and runtime input view used for a function scope.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum FunctionInferenceMode {
    /// Ordinary inference and diagnostics.
    #[default]
    Default,
    /// Ordinary inference with retained return-type correspondence facts.
    OutputProof,
    /// Upper-bound materialization of initial function parameter bindings and explicit
    /// runtime module-global reads. Parameter declarations, signatures and default checks
    /// retain ordinary inference. Lambda parameters and local bindings are not independently
    /// projected; captures and operations consume the types supplied by their bindings.
    /// Eager global snapshots and member results have no separate projection.
    Conservative,
}

/// Database giving access to semantic information about a Python program.
#[salsa::db]
pub trait Db: PythonCoreDb {
    /// Selects function inference using tracked configuration inputs.
    ///
    /// This changes the active configuration, not a simultaneous alternate view.
    /// Output facts concern declared return types; conservative inputs constrain operations.
    /// Neither mode establishes complete implementation evidence on its own.
    fn function_inference_mode(
        &self,
        _scope: ty_python_core::scope::ScopeId<'_>,
    ) -> FunctionInferenceMode {
        FunctionInferenceMode::Default
    }

    /// Resolves a binding introduced by [`PythonCoreDb::provided_statements`].
    /// Implementations must read tracked inputs and preserve the target program's context.
    fn provided_binding<'db>(
        &'db self,
        _definition: Definition<'db>,
    ) -> ProvidedBindingResolution<'db> {
        ProvidedBindingValue::Unresolved.into()
    }

    /// Overrides a name in the builtin namespace of an embedded program.
    /// `None` selects ordinary Python lookup; `Some(Unresolved)` hides that name.
    fn provided_builtin<'db>(
        &'db self,
        _file: ProgramFile<'db>,
        _name: &str,
        _usage: BuiltinUsage,
    ) -> Option<ProvidedBindingValue<'db>> {
        None
    }

    /// Supplies the initial body type of an unannotated ordinary parameter.
    ///
    /// This does not change the function's public signature or declare a type for later
    /// assignments. Source annotations, defaults, and implicit method receivers take precedence.
    /// Implementations must read tracked inputs and must not infer this parameter's body scope.
    fn provided_parameter_type<'db>(
        &'db self,
        _definition: Definition<'db>,
    ) -> Option<crate::types::Type<'db>> {
        None
    }

    /// Supplies a return contract for a function without a source annotation.
    ///
    /// The contract participates in ordinary signature and body checking. Native and supplied
    /// source annotations take precedence. Implementations must read tracked inputs and must not
    /// infer the function body or its enclosing scope while resolving this contract.
    fn provided_return_type<'db>(
        &'db self,
        _definition: Definition<'db>,
    ) -> Option<crate::provided::ProvidedReturnType<'db>> {
        None
    }

    /// Supplies result refinements and diagnostics after ordinary argument checking.
    ///
    /// The declaration, bound arguments, and inferred child types come from this inference pass.
    /// Implementations must identify the resolved declaration, rather than the spelling of the
    /// call, and must not request completed inference of the scope currently being inferred.
    /// Invalid calls retain their diagnostics and can supply a recovery result. Overloaded
    /// callables retain ordinary inference; this hook only handles single-signature callables.
    /// Supplied diagnostics use the current lint rules and source suppressions and are omitted
    /// for unreachable calls and `@no_type_check` scopes. Reporting diagnostics does not require
    /// a return-type refinement.
    fn provided_call_result<'db>(
        &'db self,
        _call: &CheckedCall<'_, 'db>,
    ) -> ProvidedCallResult<'db> {
        ProvidedCallResult::default()
    }

    /// Whether a factory stores direct named keyword arguments unchanged in same-named
    /// readable result fields.
    ///
    /// This declaration fact lets ordinary argument inference use the corresponding readonly
    /// property of an expected protocol as context. It does not supply the actual result type
    /// or replace argument checking. Implementations must identify the resolved declaration
    /// and read tracked inputs without inferring its body or the calling scope.
    fn provided_keyword_field_factory(&self, _definition: Definition<'_>) -> bool {
        false
    }

    /// Whether a supplied `__getattr__` declaration bounds the values of existing members
    /// without guaranteeing that the requested member exists.
    ///
    /// This describes the requested attribute, not the availability of the getter itself.
    /// Ty preserves ordinary argument checking and the specialized return type, but marks
    /// the fallback member as possibly undefined. Implementations must identify the resolved
    /// declaration and read tracked inputs without inferring the getter's body.
    fn provided_getattr_may_be_missing(&self, _definition: Definition<'_>) -> bool {
        false
    }

    /// Marks a supplied function declaration as usable only for type checking.
    ///
    /// An embedding can describe an implicit operation without promising a runtime attribute.
    /// This has the same effect as `@typing.type_check_only` on the declaration. Implementations
    /// must depend on tracked declaration inputs and must not infer its signature or body.
    fn provided_function_type_check_only(&self, _definition: Definition<'_>) -> bool {
        false
    }

    /// Describes an exhaustive runtime type test in an embedded program.
    ///
    /// The comparison `callable(subject) == compared_value` must hold exactly when `subject`
    /// belongs to the returned instance type. Equality and inequality must be complementary for
    /// every runtime value represented by the supplied types. Ty calls this hook for one
    /// positional argument and no keywords, and applies ordinary flow narrowing, including
    /// retention of known generic arguments. Generic targets should use `Unknown` arguments.
    /// Implementations must identify the resolved callable and read tracked inputs. The supplied
    /// types come from this inference pass; implementations must not request completed inference
    /// of the enclosing scope.
    fn provided_type_test<'db>(
        &'db self,
        _file: ProgramFile<'db>,
        _callable: crate::types::Type<'db>,
        _compared_value: crate::types::Type<'db>,
    ) -> Option<crate::types::Type<'db>> {
        None
    }

    fn check_file(&self, file: File) -> Vec<Diagnostic>;

    /// Returns the program file for `file`.
    fn program_file(&self, file: File) -> ProgramFile<'_>;

    /// Returns the Python version and its configuration source for `file`.
    fn python_version_with_source(&self, file: File) -> &PythonVersionWithSource;

    /// Resolves the rule selection for a given file.
    fn rule_selection(&self, file: File) -> &RuleSelection;

    fn lint_registry(&self) -> &LintRegistry;

    fn analysis_settings(&self, file: File) -> &AnalysisSettings;

    /// Returns the package manager's dependency information for this file.
    fn dependency_metadata(&self, file: File) -> Option<&DependencyMetadata>;

    /// Whether ty is running with logging verbosity INFO or higher (`-v` or more).
    fn verbose(&self) -> bool;

    /// Returns `true` if `file` is open in the editor.
    ///
    /// Expected types for string-literal completions are only collected for open files.
    fn is_open_file(&self, file: File) -> bool;

    fn dyn_clone(&self) -> Box<dyn Db>;
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;

    use std::sync::{Arc, Mutex};

    use anyhow::Context;
    use salsa::Setter;
    use ty_python_core::platform::PythonPlatform;

    use crate::{ProgramEnvironment, check_file_unwrap, default_lint_registry};
    use ruff_db::Db as SourceDb;
    use ruff_db::files::Files;
    use ruff_db::system::{
        DbWithTestSystem, DbWithWritableSystem as _, System, SystemPath, SystemPathBuf, TestSystem,
    };
    use ruff_db::vendored::VendoredFileSystem;
    use ruff_python_ast::PythonVersion;
    use ty_module_resolver::{Db as ModuleResolverDb, SearchPathSettings};
    use ty_python_core::TestProgramDb;
    use ty_python_core::program::{FallibleStrategy, ProgramSettings};
    use ty_site_packages::{PythonVersionSource, PythonVersionWithSource};

    pub(crate) trait SourceProvider: Send + Sync {
        fn exclusions(
            &self,
            _db: &TestDb,
            _file: ProgramFile<'_>,
        ) -> ty_python_core::SourceExclusions {
            ty_python_core::SourceExclusions::default()
        }
        fn statements(
            &self,
            db: &TestDb,
            file: ProgramFile<'_>,
        ) -> Vec<ty_python_core::definition::ProvidedStatement>;
        fn annotation<'db>(
            &self,
            db: &'db TestDb,
            file: ProgramFile<'db>,
            owner: ruff_python_ast::NodeIndex,
        ) -> Option<ty_python_core::ProvidedAnnotation<'db>>;
        fn binding<'db>(
            &self,
            db: &'db TestDb,
            definition: Definition<'db>,
        ) -> ProvidedBindingResolution<'db>;
        fn builtin<'db>(
            &self,
            db: &'db TestDb,
            file: ProgramFile<'db>,
            name: &str,
            usage: BuiltinUsage,
        ) -> Option<ProvidedBindingValue<'db>>;

        fn parameter_type<'db>(
            &self,
            _db: &'db TestDb,
            _definition: Definition<'db>,
        ) -> Option<crate::types::Type<'db>> {
            None
        }

        fn return_type<'db>(
            &self,
            _db: &'db TestDb,
            _definition: Definition<'db>,
        ) -> Option<crate::provided::ProvidedReturnType<'db>> {
            None
        }
    }

    type Events = Arc<Mutex<Vec<salsa::Event>>>;
    #[salsa::input]
    struct FunctionInferenceSelection {
        #[returns(ref)]
        selected: Option<(File, Vec<String>, super::FunctionInferenceMode)>,
    }
    type CallResultProvider =
        for<'db> fn(&'db TestDb, &CheckedCall<'_, 'db>) -> crate::provided::ProvidedCallResult<'db>;
    type DeclarationPredicate = for<'db> fn(&'db TestDb, Definition<'db>) -> bool;
    type TypeTestProvider = for<'db> fn(
        &'db TestDb,
        ProgramFile<'db>,
        crate::types::Type<'db>,
        crate::types::Type<'db>,
    ) -> Option<crate::types::Type<'db>>;

    #[salsa::db]
    #[derive(Clone)]
    pub(crate) struct TestDb {
        function_inference_selection: Option<FunctionInferenceSelection>,
        storage: salsa::Storage<Self>,
        files: Files,
        system: TestSystem,
        vendored: VendoredFileSystem,
        events: Events,
        rule_selection: Arc<RuleSelection>,
        lint_registry: Option<Arc<LintRegistry>>,
        analysis_settings: Arc<AnalysisSettings>,
        open_files: rustc_hash::FxHashSet<File>,
        program_settings: ProgramSettings,
        call_result_provider: Option<CallResultProvider>,
        type_test_provider: Option<TypeTestProvider>,
        getattr_presence_provider: Option<DeclarationPredicate>,
        keyword_field_factory: Option<DeclarationPredicate>,
        source_provider: Option<Arc<dyn SourceProvider>>,
    }

    impl TestDb {
        fn new(vendored: VendoredFileSystem) -> Self {
            let events = Events::default();
            let program_settings = ProgramSettings::empty(&vendored);
            let mut db = Self {
                function_inference_selection: None,
                storage: salsa::Storage::new(Some(Box::new({
                    let events = events.clone();
                    move |event| {
                        tracing::trace!("event: {event:?}");
                        let mut events = events.lock().unwrap();
                        events.push(event);
                    }
                }))),
                system: TestSystem::default(),
                vendored,
                events,
                files: Files::default(),
                rule_selection: Arc::new(RuleSelection::from_registry(default_lint_registry())),
                lint_registry: None,
                analysis_settings: AnalysisSettings::default().into(),
                open_files: rustc_hash::FxHashSet::default(),
                program_settings,
                call_result_provider: None,
                type_test_provider: None,
                getattr_presence_provider: None,
                keyword_field_factory: None,
                source_provider: None,
            };
            db.function_inference_selection = Some(FunctionInferenceSelection::new(&db, None));
            db
        }

        pub(crate) fn select_function_inference(
            &mut self,
            selected: Option<(File, Vec<String>, super::FunctionInferenceMode)>,
        ) {
            if let Some(selection) = self.function_inference_selection {
                selection.set_selected(self).to(selected);
            }
        }

        pub(crate) fn python_version(&self) -> PythonVersion {
            self.program().python_version(self)
        }

        pub(crate) fn program_environment(&self) -> ProgramEnvironment<'_> {
            ProgramEnvironment::from_program(self.program())
        }

        /// Marks `file` as open in the editor.
        ///
        /// This is untracked state: open a file before running any queries.
        pub(crate) fn open_file(&mut self, file: File) {
            self.open_files.insert(file);
        }

        /// Takes the salsa events.
        pub(crate) fn take_salsa_events(&mut self) -> Vec<salsa::Event> {
            let mut events = self.events.lock().unwrap();

            std::mem::take(&mut *events)
        }

        /// Clears the salsa events.
        ///
        /// ## Panics
        /// If there are any pending salsa snapshots.
        pub(crate) fn clear_salsa_events(&mut self) {
            self.take_salsa_events();
        }
    }

    impl DbWithTestSystem for TestDb {
        fn test_system(&self) -> &TestSystem {
            &self.system
        }

        fn test_system_mut(&mut self) -> &mut TestSystem {
            &mut self.system
        }
    }

    #[salsa::db]
    impl SourceDb for TestDb {
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
    impl ty_python_core::Db for TestDb {
        fn source_exclusions(&self, file: ProgramFile<'_>) -> ty_python_core::SourceExclusions {
            self.source_provider
                .as_ref()
                .map_or_else(ty_python_core::SourceExclusions::default, |provider| {
                    provider.exclusions(self, file)
                })
        }
        fn provided_statements(
            &self,
            file: ProgramFile<'_>,
        ) -> Vec<ty_python_core::definition::ProvidedStatement> {
            self.source_provider
                .as_ref()
                .map_or_else(Vec::new, |provider| provider.statements(self, file))
        }

        fn provided_annotation<'db>(
            &'db self,
            file: ProgramFile<'db>,
            owner: ruff_python_ast::NodeIndex,
        ) -> Option<ty_python_core::ProvidedAnnotation<'db>> {
            self.source_provider
                .as_ref()
                .and_then(|provider| provider.annotation(self, file, owner))
        }

        fn should_check_file(&self, file: File) -> bool {
            !file.path(self).is_vendored_path()
        }
    }

    #[salsa::db]
    impl TestProgramDb for TestDb {
        fn program_settings(&self) -> &ProgramSettings {
            &self.program_settings
        }
    }

    #[salsa::db]
    impl Db for TestDb {
        fn function_inference_mode(
            &self,
            scope: ty_python_core::scope::ScopeId<'_>,
        ) -> super::FunctionInferenceMode {
            let Some(selection) = self.function_inference_selection else {
                return super::FunctionInferenceMode::Default;
            };
            let Some((file, names, mode)) = selection.selected(self) else {
                return super::FunctionInferenceMode::Default;
            };
            if scope.program_file(self).python_file(self).file(self) != *file {
                return super::FunctionInferenceMode::Default;
            }
            let module =
                ruff_db::parsed::parsed_module(self, scope.program_file(self).python_file(self))
                    .load(self);
            if names.iter().any(|name| name == scope.name(self, &module)) {
                *mode
            } else {
                super::FunctionInferenceMode::Default
            }
        }

        fn provided_binding<'db>(
            &'db self,
            definition: Definition<'db>,
        ) -> ProvidedBindingResolution<'db> {
            self.source_provider.as_ref().map_or_else(
                || ProvidedBindingValue::Unresolved.into(),
                |provider| provider.binding(self, definition),
            )
        }

        fn provided_builtin<'db>(
            &'db self,
            file: ProgramFile<'db>,
            name: &str,
            usage: BuiltinUsage,
        ) -> Option<ProvidedBindingValue<'db>> {
            self.source_provider
                .as_ref()
                .and_then(|provider| provider.builtin(self, file, name, usage))
        }

        fn provided_call_result<'db>(
            &'db self,
            call: &CheckedCall<'_, 'db>,
        ) -> crate::provided::ProvidedCallResult<'db> {
            self.call_result_provider
                .map_or_else(crate::provided::ProvidedCallResult::default, |provider| {
                    provider(self, call)
                })
        }

        fn provided_keyword_field_factory(&self, definition: Definition<'_>) -> bool {
            self.keyword_field_factory
                .is_some_and(|provider| provider(self, definition))
        }

        fn provided_getattr_may_be_missing(&self, definition: Definition<'_>) -> bool {
            self.getattr_presence_provider
                .is_some_and(|provider| provider(self, definition))
        }

        fn provided_type_test<'db>(
            &'db self,
            file: ProgramFile<'db>,
            callable: crate::types::Type<'db>,
            compared_value: crate::types::Type<'db>,
        ) -> Option<crate::types::Type<'db>> {
            self.type_test_provider
                .and_then(|provider| provider(self, file, callable, compared_value))
        }

        fn provided_parameter_type<'db>(
            &'db self,
            definition: Definition<'db>,
        ) -> Option<crate::types::Type<'db>> {
            self.source_provider
                .as_ref()
                .and_then(|provider| provider.parameter_type(self, definition))
        }

        fn provided_return_type<'db>(
            &'db self,
            definition: Definition<'db>,
        ) -> Option<crate::provided::ProvidedReturnType<'db>> {
            self.source_provider
                .as_ref()
                .and_then(|provider| provider.return_type(self, definition))
        }

        fn check_file(&self, file: File) -> Vec<Diagnostic> {
            if !self.should_check_file(file) {
                return Vec::new();
            }

            check_file_unwrap(self, self.program_file(file))
        }

        fn program_file(&self, file: File) -> ProgramFile<'_> {
            self.program().program_file(self, file)
        }

        fn python_version_with_source(&self, _file: File) -> &PythonVersionWithSource {
            &self.program_settings.python_version
        }

        fn rule_selection(&self, _file: File) -> &RuleSelection {
            &self.rule_selection
        }

        fn lint_registry(&self) -> &LintRegistry {
            self.lint_registry
                .as_deref()
                .unwrap_or_else(|| default_lint_registry())
        }

        fn analysis_settings(&self, _file: File) -> &AnalysisSettings {
            &self.analysis_settings
        }

        fn dependency_metadata(&self, _file: File) -> Option<&DependencyMetadata> {
            None
        }

        fn verbose(&self) -> bool {
            false
        }

        fn is_open_file(&self, file: File) -> bool {
            self.open_files.contains(&file)
        }

        fn dyn_clone(&self) -> Box<dyn crate::Db> {
            Box::new(self.clone())
        }
    }

    #[salsa::db]
    impl ModuleResolverDb for TestDb {}

    #[salsa::db]
    impl salsa::Database for TestDb {}

    pub(crate) struct TestDbBuilder<'a> {
        vendored: VendoredFileSystem,
        /// Target Python version
        python_version: PythonVersion,
        /// Target Python platform
        python_platform: PythonPlatform,
        /// Roots containing first-party modules.
        src_roots: Vec<SystemPathBuf>,
        /// Path and content pairs for files that should be present
        files: Vec<(&'a str, &'a str)>,
        /// Whether module resolution should include packages from the synthetic virtual environment.
        third_party_packages: bool,
        rule_selection: Option<RuleSelection>,
        lint_registry: Option<LintRegistry>,
        call_result_provider: Option<CallResultProvider>,
        type_test_provider: Option<TypeTestProvider>,
        getattr_presence_provider: Option<DeclarationPredicate>,
        keyword_field_factory: Option<DeclarationPredicate>,
        source_provider: Option<Arc<dyn SourceProvider>>,
    }

    impl<'a> TestDbBuilder<'a> {
        pub(crate) fn new() -> Self {
            Self {
                vendored: ty_vendored::file_system().clone(),
                python_version: PythonVersion::default(),
                python_platform: PythonPlatform::default(),
                src_roots: vec![SystemPathBuf::from("/src")],
                files: vec![],
                third_party_packages: false,
                rule_selection: None,
                lint_registry: None,
                call_result_provider: None,
                type_test_provider: None,
                getattr_presence_provider: None,
                keyword_field_factory: None,
                source_provider: None,
            }
        }

        pub(crate) fn with_vendored(mut self, vendored: VendoredFileSystem) -> Self {
            self.vendored = vendored;
            self
        }

        pub(crate) fn with_python_version(mut self, version: PythonVersion) -> Self {
            self.python_version = version;
            self
        }

        pub(crate) fn with_python_platform(mut self, platform: PythonPlatform) -> Self {
            self.python_platform = platform;
            self
        }

        pub(crate) fn with_src_roots(mut self, src_roots: Vec<SystemPathBuf>) -> Self {
            self.src_roots = src_roots;
            self
        }

        pub(crate) fn with_rule_selection(mut self, selection: RuleSelection) -> Self {
            self.rule_selection = Some(selection);
            self
        }

        pub(crate) fn with_lint_registry(mut self, registry: LintRegistry) -> Self {
            self.lint_registry = Some(registry);
            self
        }

        pub(crate) fn with_source_provider(
            mut self,
            provider: impl SourceProvider + 'static,
        ) -> Self {
            self.source_provider = Some(Arc::new(provider));
            self
        }

        pub(crate) fn with_call_result_provider(mut self, provider: CallResultProvider) -> Self {
            self.call_result_provider = Some(provider);
            self
        }

        pub(crate) fn with_keyword_field_factory(mut self, provider: DeclarationPredicate) -> Self {
            self.keyword_field_factory = Some(provider);
            self
        }

        pub(crate) fn with_getattr_presence_provider(
            mut self,
            provider: DeclarationPredicate,
        ) -> Self {
            self.getattr_presence_provider = Some(provider);
            self
        }

        pub(crate) fn with_type_test_provider(mut self, provider: TypeTestProvider) -> Self {
            self.type_test_provider = Some(provider);
            self
        }

        pub(crate) fn with_file(
            mut self,
            path: &'a (impl AsRef<SystemPath> + ?Sized),
            content: &'a str,
        ) -> Self {
            self.files.push((path.as_ref().as_str(), content));
            self
        }

        /// Makes packages installed in the synthetic virtual environment available for imports.
        ///
        /// Files under `/.venv/lib/python3.13/site-packages` are treated as third-party modules,
        /// mirroring the import roots discovered from a project's configured Python environment.
        pub(crate) fn with_third_party_packages(mut self) -> Self {
            self.third_party_packages = true;
            self
        }

        pub(crate) fn build(self) -> anyhow::Result<TestDb> {
            let mut db = TestDb::new(self.vendored);
            db.call_result_provider = self.call_result_provider;
            db.type_test_provider = self.type_test_provider;
            db.getattr_presence_provider = self.getattr_presence_provider;
            db.keyword_field_factory = self.keyword_field_factory;
            db.source_provider = self.source_provider;

            if let Some(registry) = self.lint_registry {
                db.rule_selection = Arc::new(RuleSelection::from_registry(&registry));
                db.lint_registry = Some(Arc::new(registry));
            }

            if let Some(selection) = self.rule_selection {
                db.rule_selection = Arc::new(selection);
            }

            for src_root in &self.src_roots {
                db.memory_file_system().create_directory_all(src_root)?;
            }

            let site_packages = SystemPathBuf::from("/.venv/lib/python3.13/site-packages");
            if self.third_party_packages {
                db.memory_file_system()
                    .create_directory_all(&site_packages)?;
            }

            db.write_files(self.files)
                .context("Failed to write test files")?;

            let search_path_settings = if self.third_party_packages {
                SearchPathSettings {
                    src_roots: self.src_roots,
                    site_packages_paths: vec![site_packages],
                    ..SearchPathSettings::empty()
                }
            } else {
                SearchPathSettings::new(self.src_roots)
            };

            let program_settings = ProgramSettings {
                python_version: PythonVersionWithSource {
                    version: self.python_version,
                    source: PythonVersionSource::default(),
                },
                python_platform: self.python_platform,
                search_paths: search_path_settings
                    .to_search_paths(db.system(), db.vendored(), &FallibleStrategy)
                    .context("Invalid search path settings")?,
            };
            program_settings.search_paths.try_register_static_roots(&db);
            db.program_settings = program_settings;

            Ok(db)
        }
    }

    pub(crate) fn setup_db() -> TestDb {
        TestDbBuilder::new().build().expect("valid TestDb setup")
    }
}
