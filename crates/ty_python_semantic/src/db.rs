use crate::dependency::DependencyMetadata;
use crate::lint::{LintRegistry, RuleSelection};
use crate::provided::{
    BuiltinUsage, ProvidedBindingResolution, ProvidedBindingValue, ProvidedCallResult,
    ProvidedData, ProvidedGetattrResult, ProvidedInstanceFields, ProvidedReturnType,
    ProvidedTypeApplication, TypeExpressionContext,
};
use crate::types::CheckedCall;
use crate::{AnalysisSettings, PythonVersionWithSource};
use ruff_db::diagnostic::Diagnostic;
use ruff_db::files::File;
use ruff_python_ast::name::Name;
use ty_python_core::definition::Definition;
use ty_python_core::{Db as PythonCoreDb, ProgramFile};

/// Database giving access to semantic information about a Python program.
#[salsa::db]
pub trait Db: PythonCoreDb {
    /// Resolves a binding introduced by [`PythonCoreDb::provided_statements`].
    /// Implementations must read tracked inputs and preserve the target program's context.
    fn provided_binding<'db>(
        &'db self,
        _definition: Definition<'db>,
    ) -> ProvidedBindingResolution<'db> {
        ProvidedBindingValue::Unresolved.into()
    }

    /// Whether values exported by this module are frozen before a supplied binding can read them.
    ///
    /// The application must guarantee completed evaluation and prevent later mutation through
    /// every alias. This permits observing the existing end-of-module contents; it does not
    /// erase mutations or escapes during evaluation. Ordinary Python modules do not qualify.
    fn provided_exports_are_frozen(&self, _file: ProgramFile<'_>) -> bool {
        false
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

    /// Selects a nominal allocation class for builtin collection construction.
    ///
    /// The declaration must be an empty final subclass whose sole base specializes the
    /// builtin with the same unconstrained type parameters. The application guarantees
    /// that construction produces this runtime subset and preserves the builtin's operations.
    /// Annotations and structural dictionary schemas continue to denote the builtin class.
    /// Implementations must select the association from tracked inputs of the requesting program.
    /// The declaration may belong to a shared support program; its builtin base must have the same
    /// identity as the builtin resolved in the requesting program.
    fn provided_allocation_class<'db>(
        &'db self,
        _program: crate::Program<'db>,
        _class: crate::types::KnownClass,
    ) -> Option<ProvidedBindingValue<'db>> {
        None
    }

    /// Supplies the initial body type of an unannotated parameter.
    ///
    /// This does not change the function's public signature or declare a type for later
    /// assignments. Source annotations and implicit method receivers take precedence.
    /// Source defaults contribute their inferred types to the initial binding.
    /// For `*args` and `**kwargs`, supply the full tuple or dictionary type used in the body.
    /// Implementations must read tracked inputs and must not infer this parameter's body scope.
    fn provided_parameter_type<'db>(
        &'db self,
        _definition: Definition<'db>,
    ) -> Option<crate::types::Type<'db>> {
        None
    }

    /// Supplies an expected return value for checking an unannotated function body.
    ///
    /// Source and external return annotations take precedence. The supplied type provides
    /// context for return expressions and ordinary return diagnostics; it does not declare
    /// the function's public return type. Implementations must read tracked inputs and must
    /// not infer the function body whose returns are being checked.
    fn provided_function_return_type<'db>(
        &'db self,
        _definition: Definition<'db>,
    ) -> Option<ProvidedReturnType<'db>> {
        None
    }

    /// Whether a supplied declaration describes a native builtin function.
    ///
    /// The declaration retains its signature and identity, but its runtime class is
    /// `types.BuiltinFunctionType`. Every declaration in an overload family must agree.
    /// Implementations must read tracked declaration inputs and must not infer the function's
    /// signature or body.
    fn provided_function_is_builtin(&self, _definition: Definition<'_>) -> bool {
        false
    }

    /// Interprets an application-defined type subscription after resolving its constructor.
    ///
    /// Implementations must identify the resolved declaration and infer child annotations
    /// through `context`. Returning `None` preserves ordinary specialization and must not
    /// infer children or report diagnostics. Implementations must read tracked inputs and
    /// must not request completed inference of the scope currently being inferred.
    fn provided_type_application<'db>(
        &'db self,
        _application: ProvidedTypeApplication<'_, 'db>,
        _context: &mut dyn TypeExpressionContext<'db>,
    ) -> Option<crate::types::Type<'db>> {
        None
    }

    /// Interprets a resolved value used as a type annotation in an embedded program.
    ///
    /// Returning `None` preserves ordinary type conversion. Implementations must identify
    /// the resolved declaration, read tracked inputs, and avoid requesting completed inference
    /// of the scope containing the reference.
    fn provided_type_reference<'db>(
        &'db self,
        _file: ProgramFile<'db>,
        _value_type: crate::types::Type<'db>,
        _definition: Option<Definition<'db>>,
    ) -> Option<crate::types::Type<'db>> {
        None
    }

    /// Resolves the immutable instance fields of a supplied nominal class.
    ///
    /// `file` owns the class's source anchor. The metadata identifies the field declaration;
    /// it must be sufficient to create the class's identity without resolving these fields.
    /// Implementations must read tracked inputs and retain field declaration locations.
    /// Fields must not depend on a generic specialization of the supplied class.
    fn provided_instance_fields<'db>(
        &'db self,
        _file: ProgramFile<'db>,
        _source: &ProvidedData,
    ) -> Option<ProvidedInstanceFields<'db>> {
        None
    }

    /// Supplies result refinements and diagnostics after ordinary argument checking.
    ///
    /// The declaration, bound arguments, and inferred child types come from this inference pass.
    /// Implementations must identify the resolved declaration, rather than the spelling of the
    /// call, and must not request completed inference of the scope currently being inferred.
    /// Selected overloads are refined separately and retain ordinary result aggregation.
    /// Calls requiring argument expansion retain ordinary inference because their complete
    /// checked bindings are not available. Invalid single-signature calls retain their
    /// diagnostics and can supply a recovery result.
    /// Supplied diagnostics use the current lint rules and source suppressions and are omitted
    /// for unreachable calls and `@no_type_check` scopes. Reporting diagnostics does not require
    /// a return-type refinement.
    fn provided_call_result<'db>(
        &'db self,
        _call: &CheckedCall<'_, 'db>,
    ) -> ProvidedCallResult<'db> {
        ProvidedCallResult::default()
    }

    /// Parameters whose argument context depends on other arguments of a supplied call.
    ///
    /// This declaration fact opts a single-signature call into sibling argument inference,
    /// including nongeneric calls. Implementations must read tracked inputs without inferring
    /// the declaration body or the calling scope. Unlisted parameters use ordinary context.
    fn provided_contextual_parameters(&self, _definition: Definition<'_>) -> Box<[Name]> {
        Box::default()
    }

    /// Supplies argument context after a provisional pass of ordinary argument checking.
    ///
    /// The call can contain incomplete child types and binding errors. Implementations must
    /// identify the declaration and use this view's child types rather than requesting completed
    /// inference of the calling scope. The context is recomputed during sibling inference;
    /// it guides inference without replacing final argument checking or the declared signature.
    /// Overloaded and union callees retain ordinary inference.
    fn provided_call_argument_context<'db>(
        &'db self,
        _call: &CheckedCall<'_, 'db>,
        _parameter: &str,
    ) -> Option<crate::types::Type<'db>> {
        None
    }

    /// Whether a factory returns a fresh object retaining each direct named keyword argument
    /// unchanged in an inert, readonly, same-named field.
    ///
    /// The factory must not mutate the arguments or retain additional aliases to them or the
    /// result. Reading a field must return the original argument without executing user code.
    /// This permits argument context from an expected readonly protocol property and contents
    /// observations through a field while the original argument is independently proved
    /// unchanged. The original argument still escapes through the call.
    ///
    /// This declaration fact does not supply the result type or replace argument checking.
    /// Implementations must identify the resolved declaration and read tracked inputs without
    /// inferring its body or the calling scope.
    fn provided_keyword_field_factory(&self, _definition: Definition<'_>) -> bool {
        false
    }

    /// Whether a supplied function preserves a parameter's outer container contents.
    ///
    /// The declaration must neither change the container's key/value associations nor retain
    /// or return that container. Values stored inside it may escape. This is a declaration
    /// fact, independent of the parameter's annotation; ordinary `Mapping` annotations do not
    /// provide this guarantee. Implementations must read tracked inputs and must not infer the
    /// function body or the calling scope.
    fn provided_parameter_preserves_contents(
        &self,
        _definition: Definition<'_>,
        _parameter: &str,
    ) -> bool {
        false
    }

    /// Describes an attribute handled by a supplied `__getattr__` declaration.
    ///
    /// Ordinary argument checking runs before the optional return-type refinement. An absent
    /// result participates in ordinary missing-member lookup, including union alternatives and
    /// `getattr` defaults. Implementations must identify the resolved declaration and read
    /// tracked inputs without inferring the getter's body.
    fn provided_getattr_result<'db>(
        &'db self,
        _definition: Definition<'db>,
        _receiver: crate::types::Type<'db>,
        _attribute: &str,
    ) -> ProvidedGetattrResult<'db> {
        ProvidedGetattrResult::default()
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
        fn function_return_type<'db>(
            &self,
            _db: &'db TestDb,
            _definition: Definition<'db>,
        ) -> Option<ProvidedReturnType<'db>> {
            None
        }

        fn allocation_class<'db>(
            &self,
            _db: &'db TestDb,
            _program: crate::Program<'db>,
            _class: crate::types::KnownClass,
        ) -> Option<ProvidedBindingValue<'db>> {
            None
        }

        fn exports_are_frozen(&self, _db: &TestDb, _file: ProgramFile<'_>) -> bool {
            false
        }

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
    }

    type Events = Arc<Mutex<Vec<salsa::Event>>>;
    type CallResultProvider =
        for<'db> fn(&'db TestDb, &CheckedCall<'_, 'db>) -> crate::provided::ProvidedCallResult<'db>;
    type ContextualParametersProvider = for<'db> fn(&'db TestDb, Definition<'db>) -> Box<[Name]>;
    type CallArgumentContextProvider =
        for<'db> fn(&'db TestDb, &CheckedCall<'_, 'db>, &str) -> Option<crate::types::Type<'db>>;
    type TypeApplicationProvider = for<'db> fn(
        &'db TestDb,
        ProvidedTypeApplication<'_, 'db>,
        &mut dyn TypeExpressionContext<'db>,
    ) -> Option<crate::types::Type<'db>>;
    type TypeReferenceProvider = for<'db> fn(
        &'db TestDb,
        ProgramFile<'db>,
        crate::types::Type<'db>,
        Option<Definition<'db>>,
    ) -> Option<crate::types::Type<'db>>;
    type InstanceFieldsProvider = for<'db> fn(
        &'db TestDb,
        ProgramFile<'db>,
        &ProvidedData,
    ) -> Option<ProvidedInstanceFields<'db>>;
    type DeclarationPredicate = for<'db> fn(&'db TestDb, Definition<'db>) -> bool;
    type ParameterPredicate = for<'db> fn(&'db TestDb, Definition<'db>, &str) -> bool;
    type GetattrResultProvider = for<'db> fn(
        &'db TestDb,
        Definition<'db>,
        crate::types::Type<'db>,
        &str,
    ) -> ProvidedGetattrResult<'db>;
    type TypeTestProvider = for<'db> fn(
        &'db TestDb,
        ProgramFile<'db>,
        crate::types::Type<'db>,
        crate::types::Type<'db>,
    ) -> Option<crate::types::Type<'db>>;

    #[salsa::db]
    #[derive(Clone)]
    pub(crate) struct TestDb {
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
        contextual_parameters_provider: Option<ContextualParametersProvider>,
        call_argument_context_provider: Option<CallArgumentContextProvider>,
        type_application_provider: Option<TypeApplicationProvider>,
        type_reference_provider: Option<TypeReferenceProvider>,
        instance_fields_provider: Option<InstanceFieldsProvider>,
        type_test_provider: Option<TypeTestProvider>,
        getattr_result_provider: Option<GetattrResultProvider>,
        builtin_function: Option<DeclarationPredicate>,
        keyword_field_factory: Option<DeclarationPredicate>,
        parameter_contents_preserver: Option<ParameterPredicate>,
        source_provider: Option<Arc<dyn SourceProvider>>,
    }

    impl TestDb {
        fn new(vendored: VendoredFileSystem) -> Self {
            let events = Events::default();
            let program_settings = ProgramSettings::empty(&vendored);
            Self {
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
                contextual_parameters_provider: None,
                call_argument_context_provider: None,
                type_application_provider: None,
                type_reference_provider: None,
                instance_fields_provider: None,
                type_test_provider: None,
                getattr_result_provider: None,
                builtin_function: None,
                keyword_field_factory: None,
                parameter_contents_preserver: None,
                source_provider: None,
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
        fn provided_function_is_builtin(&self, definition: Definition<'_>) -> bool {
            self.builtin_function
                .is_some_and(|predicate| predicate(self, definition))
        }

        fn provided_function_return_type<'db>(
            &'db self,
            definition: Definition<'db>,
        ) -> Option<ProvidedReturnType<'db>> {
            self.source_provider
                .as_ref()
                .and_then(|provider| provider.function_return_type(self, definition))
        }

        fn provided_allocation_class<'db>(
            &'db self,
            program: crate::Program<'db>,
            class: crate::types::KnownClass,
        ) -> Option<ProvidedBindingValue<'db>> {
            self.source_provider
                .as_ref()
                .and_then(|provider| provider.allocation_class(self, program, class))
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

        fn provided_exports_are_frozen(&self, file: ProgramFile<'_>) -> bool {
            self.source_provider
                .as_ref()
                .is_some_and(|provider| provider.exports_are_frozen(self, file))
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

        fn provided_contextual_parameters(&self, definition: Definition<'_>) -> Box<[Name]> {
            self.contextual_parameters_provider
                .map_or_else(Box::default, |provider| provider(self, definition))
        }

        fn provided_call_argument_context<'db>(
            &'db self,
            call: &CheckedCall<'_, 'db>,
            parameter: &str,
        ) -> Option<crate::types::Type<'db>> {
            self.call_argument_context_provider
                .and_then(|provider| provider(self, call, parameter))
        }

        fn provided_type_application<'db>(
            &'db self,
            application: ProvidedTypeApplication<'_, 'db>,
            context: &mut dyn TypeExpressionContext<'db>,
        ) -> Option<crate::types::Type<'db>> {
            self.type_application_provider
                .and_then(|provider| provider(self, application, context))
        }

        fn provided_type_reference<'db>(
            &'db self,
            file: ProgramFile<'db>,
            value_type: crate::types::Type<'db>,
            definition: Option<Definition<'db>>,
        ) -> Option<crate::types::Type<'db>> {
            self.type_reference_provider
                .and_then(|provider| provider(self, file, value_type, definition))
        }

        fn provided_instance_fields<'db>(
            &'db self,
            file: ProgramFile<'db>,
            source: &ProvidedData,
        ) -> Option<ProvidedInstanceFields<'db>> {
            self.instance_fields_provider
                .and_then(|provider| provider(self, file, source))
        }

        fn provided_keyword_field_factory(&self, definition: Definition<'_>) -> bool {
            self.keyword_field_factory
                .is_some_and(|provider| provider(self, definition))
        }

        fn provided_parameter_preserves_contents(
            &self,
            definition: Definition<'_>,
            parameter: &str,
        ) -> bool {
            self.parameter_contents_preserver
                .is_some_and(|provider| provider(self, definition, parameter))
        }

        fn provided_getattr_result<'db>(
            &'db self,
            definition: Definition<'db>,
            receiver: crate::types::Type<'db>,
            attribute: &str,
        ) -> ProvidedGetattrResult<'db> {
            self.getattr_result_provider
                .map_or(ProvidedGetattrResult::default(), |provider| {
                    provider(self, definition, receiver, attribute)
                })
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
        contextual_parameters_provider: Option<ContextualParametersProvider>,
        call_argument_context_provider: Option<CallArgumentContextProvider>,
        type_application_provider: Option<TypeApplicationProvider>,
        type_reference_provider: Option<TypeReferenceProvider>,
        instance_fields_provider: Option<InstanceFieldsProvider>,
        type_test_provider: Option<TypeTestProvider>,
        getattr_result_provider: Option<GetattrResultProvider>,
        builtin_function: Option<DeclarationPredicate>,
        keyword_field_factory: Option<DeclarationPredicate>,
        parameter_contents_preserver: Option<ParameterPredicate>,
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
                contextual_parameters_provider: None,
                call_argument_context_provider: None,
                type_application_provider: None,
                type_reference_provider: None,
                instance_fields_provider: None,
                type_test_provider: None,
                getattr_result_provider: None,
                builtin_function: None,
                keyword_field_factory: None,
                parameter_contents_preserver: None,
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

        pub(crate) fn with_call_argument_context_provider(
            mut self,
            parameters: ContextualParametersProvider,
            context: CallArgumentContextProvider,
        ) -> Self {
            self.contextual_parameters_provider = Some(parameters);
            self.call_argument_context_provider = Some(context);
            self
        }

        pub(crate) fn with_type_application_provider(
            mut self,
            provider: TypeApplicationProvider,
        ) -> Self {
            self.type_application_provider = Some(provider);
            self
        }

        pub(crate) fn with_type_reference_provider(
            mut self,
            provider: TypeReferenceProvider,
        ) -> Self {
            self.type_reference_provider = Some(provider);
            self
        }

        pub(crate) fn with_instance_fields_provider(
            mut self,
            provider: InstanceFieldsProvider,
        ) -> Self {
            self.instance_fields_provider = Some(provider);
            self
        }

        pub(crate) fn with_keyword_field_factory(mut self, provider: DeclarationPredicate) -> Self {
            self.keyword_field_factory = Some(provider);
            self
        }

        pub(crate) fn with_builtin_function(mut self, predicate: DeclarationPredicate) -> Self {
            self.builtin_function = Some(predicate);
            self
        }

        pub(crate) fn with_parameter_contents_preserver(
            mut self,
            provider: ParameterPredicate,
        ) -> Self {
            self.parameter_contents_preserver = Some(provider);
            self
        }

        pub(crate) fn with_getattr_result_provider(
            mut self,
            provider: GetattrResultProvider,
        ) -> Self {
            self.getattr_result_provider = Some(provider);
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
            db.contextual_parameters_provider = self.contextual_parameters_provider;
            db.call_argument_context_provider = self.call_argument_context_provider;
            db.type_application_provider = self.type_application_provider;
            db.type_reference_provider = self.type_reference_provider;
            db.instance_fields_provider = self.instance_fields_provider;
            db.type_test_provider = self.type_test_provider;
            db.getattr_result_provider = self.getattr_result_provider;
            db.builtin_function = self.builtin_function;
            db.keyword_field_factory = self.keyword_field_factory;
            db.parameter_contents_preserver = self.parameter_contents_preserver;
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
                virtual_environment: self
                    .third_party_packages
                    .then(|| SystemPathBuf::from("/.venv")),
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
