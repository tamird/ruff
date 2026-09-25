use compact_str::CompactString;
use ruff_db::PythonFile;
use ruff_db::files::{File, FilePath};
use ruff_db::parsed::{parsed_annotation_range, parsed_module, parsed_string_annotation};
use ruff_db::source::{line_index, source_text};
use ruff_python_ast::find_node::{CoveringNode, covering_node};
use ruff_python_ast::{self as ast, ExprStringLiteral, ModExpression, NodeIndex};
use ruff_python_ast::{Expr, ExprRef, name::Name};
use ruff_python_parser::Parsed;
use ruff_source_file::LineIndex;
use ruff_text_size::{Ranged, TextRange, TextSize};
use rustc_hash::{FxHashMap, FxHashSet};
use ty_module_resolver::{
    ImportingFile, KnownModule, Module, ModuleName, list_modules, resolve_module,
    resolve_module_for_import_from,
};

use crate::Db;
use crate::place::definitions::DefinitionResolution;
use crate::place::implicit_globals::all_implicit_module_globals;
use crate::place::{
    builtins_module_scope, class_body_implicit_symbol, implicit_builtins_symbol,
    implicit_builtins_symbol_source, loop_header_reachability, place_from_bindings,
};
use crate::place_load::{
    ImplicitPlaceLoad, PlaceLoadMode, PlaceLoadResolutionStep, PlaceLoadSourceKind,
    resolve_place_load,
};
use crate::provided::{BuiltinUsage, ProvidedBindingValue, ProvidedClass};
use crate::reachability::ReachabilityEvaluationCache;
use crate::types::ide_support::{ImportAliasResolution, definition_for_name};
pub use crate::types::list_members::ObjectMembers;
use crate::types::list_members::{
    all_members, all_members_with_object_policy, all_reachable_members,
};
use crate::types::{
    CycleDetector, DictionaryItems, ProgramEnvironment, SpecialFormType, Type, TypeQualifiers,
    binding_type, infer_complete_scope_types, infer_definition_types, inferred_declaration,
    is_discarded_dict_key_assignment,
};
use crate::types::{function_signature_annotation_info, function_signature_annotation_scope};
use ty_python_core::definition::{Definition, DefinitionKind, DefinitionState};
use ty_python_core::place::PlaceExpr;
use ty_python_core::place_table;
use ty_python_core::scope::{FileScopeId, Scope};
use ty_python_core::semantic_index;
use ty_python_core::symbol::Symbol;
use ty_python_core::{BindingWithConstraintsIterator, Program, ProgramFile, ProvidedAnnotation};

/// The primary interface the LSP should use for querying semantic information about a [`File`].
///
/// Although you can in principle freely construct this type given a `db` and `file`, you should
/// try to construct this at the start of your analysis and thread the same instance through
/// the full analysis.
///
/// The primary reason for this is that it manages traversing into the sub-ASTs of string
/// annotations (see [`Self::enter_string_annotation`]). When you do this you will be handling
/// AST nodes that don't belong to the file's AST (or *any* file's AST). These kinds of nodes
/// will result in panics and confusing results if handed to the wrong subsystem. `SemanticModel`
/// methods use the annotation's enclosing scope to look up these nodes.
pub struct SemanticModel<'db> {
    db: &'db dyn Db,
    file: ProgramFile<'db>,
    /// The enclosing scope when analyzing an annotation outside the module AST.
    annotation_scope: Option<FileScopeId>,
}

impl<'db> SemanticModel<'db> {
    pub fn new(db: &'db dyn Db, file: ProgramFile<'db>) -> Self {
        Self {
            db,
            file,
            annotation_scope: None,
        }
    }

    pub fn db(&self) -> &'db dyn Db {
        self.db
    }

    pub fn file(&self) -> File {
        self.file.file(self.db)
    }

    pub fn python_file(&self) -> PythonFile<'db> {
        self.file.python_file(self.db)
    }

    pub fn program_file(&self) -> ProgramFile<'db> {
        self.file
    }

    pub fn program(&self) -> Program<'db> {
        self.file.program(self.db)
    }

    pub fn program_environment(&self) -> ProgramEnvironment<'db> {
        ProgramEnvironment::from_file(self.program_file())
    }

    /// Returns the inferred value of a binding, including application-supplied source bindings.
    pub fn definition_type(&self, definition: Definition<'db>) -> Type<'db> {
        binding_type(self.db, definition)
    }

    /// Proves that the indexed references to these names are confined to `allowed`.
    ///
    /// Each occurrence must belong to this model's current module AST and resolve to one
    /// ordinary assignment in the same local scope. The returned definitions are aligned
    /// with `allowed`, including repeated occurrences. Rebinding, deletion, loop-carried
    /// bindings, captures, and any other possible indexed reference prevent proof.
    ///
    /// This checks raw lexical references indexed in the file. Callers establish any required
    /// constraints on reflection, external aliases, and object lifetime. The check retains
    /// possible references independently of expression types and semantic reachability.
    pub fn confined_name_definitions(
        &self,
        allowed: &[&ast::ExprName],
    ) -> Option<Vec<Definition<'db>>> {
        if self.annotation_scope.is_some() {
            return None;
        }
        let Some(first) = allowed.first() else {
            return Some(Vec::new());
        };
        let index = semantic_index(self.db, self.file);
        let scope = index.try_expression_scope_id(&ExprRef::from(*first))?;
        let table = index.place_table(scope);
        let use_def = index.use_def_map(scope);
        let mut definitions = Vec::with_capacity(allowed.len());
        let mut candidates = FxHashSet::default();
        let mut names = FxHashSet::default();
        let mut allowed_uses = FxHashSet::default();
        for &name in allowed {
            if index.try_expression_scope_id(&ExprRef::from(name))? != scope {
                return None;
            }
            let symbol = table.symbol_id(&name.id)?;
            if !table.symbol(symbol).is_local() {
                return None;
            }
            let use_id = index.try_expression_use_id(name.into())?;
            let mut bindings = use_def.bindings_at_use(use_id);
            let DefinitionState::Defined(definition) = bindings.next()?.binding else {
                return None;
            };
            if bindings.next().is_some()
                || definition.scope(self.db).file_scope_id(self.db) != scope
                || !matches!(definition.kind(self.db), DefinitionKind::Assignment(_))
            {
                return None;
            }
            if candidates.insert(definition) {
                // Complete history prepends the scope-entry undefined sentinel. Every actual
                // retained binding must be this assignment, including bindings after the use.
                let mut history = use_def.reachable_symbol_bindings(symbol);
                if history.next()?.binding != DefinitionState::Undefined {
                    return None;
                }
                let first_binding = history.next()?.binding;
                if first_binding != DefinitionState::Defined(definition)
                    || history
                        .any(|binding| binding.binding != DefinitionState::Defined(definition))
                {
                    return None;
                }
            }
            definitions.push(definition);
            names.insert(name.id.as_str());
            allowed_uses.insert(ty_python_core::ExpressionNodeKey::from(ExprRef::from(name)));
        }

        let module = parsed_module(self.db, self.python_file()).load(self.db);
        for (scope, expression, _) in index.expression_uses(&module) {
            let ExprRef::Name(name) = expression else {
                continue;
            };
            if !names.contains(name.id.as_str())
                || allowed_uses.contains(&ty_python_core::ExpressionNodeKey::from(expression))
            {
                continue;
            }
            if self.name_may_reference_definitions(name, scope, &candidates)? {
                return None;
            }
        }
        Some(definitions)
    }

    fn name_may_reference_definitions(
        &self,
        name: &ast::ExprName,
        scope: FileScopeId,
        candidates: &FxHashSet<Definition<'db>>,
    ) -> Option<bool> {
        let index = semantic_index(self.db, self.file);
        let resolution = resolve_place_load(
            self.db,
            index,
            scope.to_scope_id(self.db, self.file),
            PlaceExpr::from_expr_name(name),
            PlaceLoadMode::AtExpression(name.into()),
        );
        for step in resolution {
            let source = match step {
                PlaceLoadResolutionStep::Source(source) => source,
                PlaceLoadResolutionStep::MemberResolutionCondition(_) => return None,
                PlaceLoadResolutionStep::Exhausted(_) => return Some(false),
            };
            let bindings = match source.kind {
                PlaceLoadSourceKind::Bindings(bindings) => bindings,
                PlaceLoadSourceKind::DefinitionsFromOwningScope { scope, id } => {
                    if scope.program_file(self.db) != self.file {
                        return None;
                    }
                    index
                        .use_def_map(scope.file_scope_id(self.db))
                        .reachable_bindings(id)
                }
                PlaceLoadSourceKind::Implicit(implicit) => match implicit {
                    ImplicitPlaceLoad::ExplicitGlobalSymbol { file, name } => {
                        if file != self.file {
                            return None;
                        }
                        let symbol = index.place_table(FileScopeId::global()).symbol_id(&name)?;
                        index
                            .use_def_map(FileScopeId::global())
                            .reachable_symbol_bindings(symbol)
                    }
                    ImplicitPlaceLoad::ClassBodySymbol(_) => continue,
                    ImplicitPlaceLoad::DunderClass(_) => return Some(false),
                    ImplicitPlaceLoad::ModuleImplicitGlobal { file: _, name: _ } => {
                        return Some(false);
                    }
                    ImplicitPlaceLoad::Builtin(_) => return Some(false),
                },
            };
            let mut bound = true;
            let mut any_binding = false;
            for binding in bindings {
                any_binding = true;
                match binding.binding {
                    DefinitionState::Defined(definition) => {
                        if candidates.contains(&definition) {
                            return Some(true);
                        }
                        match definition.kind(self.db) {
                            DefinitionKind::LoopHeader(_) => return None,
                            DefinitionKind::NestedBindings(_) => return None,
                            _ => {}
                        }
                    }
                    DefinitionState::Undefined => bound = false,
                    DefinitionState::Deleted => bound = false,
                }
            }
            if any_binding && bound {
                return Some(false);
            }
        }
        Some(false)
    }

    /// Looks up a builtin without consulting local bindings.
    pub fn builtin_type(&self, name: &str, usage: BuiltinUsage) -> Option<Type<'db>> {
        implicit_builtins_symbol(self.db, &self.program_environment(), name, usage)
            .place
            .ignore_possibly_undefined()
    }

    /// Creates an application-supplied class anchored to a call in this file's canonical AST.
    ///
    /// This only establishes source identity; it does not infer or bind the call. Detached
    /// annotation expressions must use their existing inference-time construction path.
    pub fn provided_class_at_call(
        &self,
        call: &ast::ExprCall,
        class: ProvidedClass<'db>,
    ) -> Option<Type<'db>> {
        if self.annotation_scope.is_some() {
            return None;
        }
        class.into_type_at_call(self.db, self.file, call)
    }

    /// Returns known string entries at an original call argument expression.
    ///
    /// Literals, builtin dictionary copies, and indexed mappings retain named entries and
    /// residual values at this use. Reaching mutations update those entries; exposure weakens
    /// presence evidence while preserving ordinary value refinements.
    pub fn dictionary_items(&self, expression: &Expr) -> Option<DictionaryItems<'db>> {
        self.dictionary_observation(expression).ok()
    }

    pub(crate) fn dictionary_observation(
        &self,
        expression: &Expr,
    ) -> crate::types::dictionary::DictionaryObservation<'db> {
        if self.annotation_scope.is_some() {
            return Err(crate::types::dictionary::DictionaryFallback::Unavailable);
        }
        let env = ProgramEnvironment::from_file(self.file);
        let index = semantic_index(self.db, self.file);
        let Some(file_scope) = index.try_expression_scope_id(expression) else {
            return Err(crate::types::dictionary::DictionaryFallback::Unavailable);
        };
        let scope = file_scope.to_scope_id(self.db, self.file);
        match DictionaryItems::expression(self.db, &env, scope, expression, &mut |expression| {
            expression.inferred_type(self)
        }) {
            Err(crate::types::dictionary::DictionaryFallback::Unavailable) => {
                let cache = ReachabilityEvaluationCache::new(
                    scope,
                    index.use_def_map(file_scope).reachability_constraints(),
                );
                let Some(ty) = expression.inferred_type(self) else {
                    return Err(crate::types::dictionary::DictionaryFallback::Unavailable);
                };
                DictionaryItems::observed(self.db, scope, expression, ty, &cache)
            }
            observed => observed,
        }
    }

    /// Returns the type at `offset` in an application-supplied annotation.
    ///
    /// The annotation is read from its owning declaration's inference result. `owner` must be
    /// the canonical node used by [`ty_python_core::Db::provided_annotation`] in this file.
    pub fn provided_annotation_type_at(
        &self,
        owner: NodeIndex,
        offset: TextSize,
    ) -> Option<Type<'db>> {
        let (parsed, definition) = self.provided_annotation(owner)?;
        let expression = parsed.expr();
        let range = TextRange::empty(offset);
        if !expression.range().contains_range(range) {
            return None;
        }
        let node = covering_node(expression.into(), range);
        let expression = node.node().as_expr_ref()?;
        if definition.kind(self.db).is_function_def() {
            function_signature_annotation_info(self.db, definition, expression.into()).0
        } else {
            infer_definition_types(self.db, definition).try_expression_type(expression)
        }
    }

    /// Enters an active, application-supplied annotation in this file.
    ///
    /// `owner` must be its canonical function, parameter, or assignment target.
    /// Use the returned model to query the parsed annotation, including nested
    /// quoted annotations. Native annotations take precedence; externally supplied
    /// annotations are visited in their own source file.
    pub fn enter_provided_annotation(
        &self,
        owner: NodeIndex,
    ) -> Option<(Parsed<ModExpression>, Self)> {
        let (parsed, definition) = self.provided_annotation(owner)?;
        let scope = if definition.kind(self.db).is_function_def() {
            function_signature_annotation_scope(self.db, definition)
        } else {
            definition.scope(self.db)
        };
        Some((
            parsed,
            Self {
                db: self.db,
                file: self.file,
                annotation_scope: Some(scope.file_scope_id(self.db)),
            },
        ))
    }

    /// Parses a local annotation and selects the declaration that owns its inference.
    fn provided_annotation(
        &self,
        owner: NodeIndex,
    ) -> Option<(Parsed<ModExpression>, Definition<'db>)> {
        if self.annotation_scope.is_some() {
            return None;
        }
        let ProvidedAnnotation::Range(range) = self.db.provided_annotation(self.file, owner)?
        else {
            return None;
        };
        let module = parsed_module(self.db, self.python_file()).load(self.db);
        let node = module.get_by_index(owner);
        let index = semantic_index(self.db, self.file);
        if index.is_excluded(node.range()) {
            return None;
        }
        let definition = match node {
            ast::AnyRootNodeRef::Stmt(statement) => {
                let ast::Stmt::FunctionDef(function) = statement else {
                    return None;
                };
                if function.returns.is_some() {
                    return None;
                }
                index.try_definition(function)?
            }
            ast::AnyRootNodeRef::Parameter(parameter) => {
                if parameter.annotation.is_some() {
                    return None;
                }
                let definition = index.try_definition(parameter)?;
                let function = definition.scope(self.db).node(self.db).as_function()?;
                index.try_definition(function.node(&module))?
            }
            ast::AnyRootNodeRef::Expr(owner) => {
                let name = owner.as_name_expr()?;
                let definition = index.try_definition(name)?;
                let DefinitionKind::Assignment(assignment) = definition.kind(self.db) else {
                    return None;
                };
                if assignment.unpack().is_some() {
                    return None;
                }
                definition
            }
            _ => return None,
        };
        let source = source_text(self.db, self.file());
        let parsed = parsed_annotation_range(&source, range, owner).ok()?;
        Some((parsed, definition))
    }

    pub fn file_path(&self) -> &FilePath {
        self.file().path(self.db)
    }

    pub fn line_index(&self) -> LineIndex {
        line_index(self.db, self.file())
    }

    /// Returns whether `name` refers to a standard builtin in the scope containing `node`.
    ///
    /// This method uses a simplified implementation of name resolution: any binding or declaration
    /// in a visible scope shadows the builtin, even if it does not reach `node`. As a result, it
    /// can return `false` when the builtin is actually available. That is acceptable when deciding
    /// whether to offer an autofix: we can safely omit the fix in edge cases where resolving the
    /// name precisely would require more complex analysis.
    ///
    /// Definitions in a project-level `__builtins__.pyi` also shadow standard builtins.
    pub(crate) fn definitely_has_builtin_binding(
        &self,
        name: &str,
        node: ast::AnyNodeRef<'_>,
    ) -> bool {
        let index = semantic_index(self.db, self.program_file());
        let Some(scope) = self.scope(node) else {
            return false;
        };

        if index.visible_ancestor_scopes(scope).any(|(scope, _)| {
            index
                .place_table(scope)
                .symbol_by_name(name)
                .is_some_and(|symbol| symbol.is_bound() || symbol.is_declared())
        }) {
            return false;
        }

        let env = self.program_environment();
        implicit_builtins_symbol_source(self.db, &env, name, self.builtin_usage(node)).is_some_and(
            |source| {
                source.name.is_none() && Some(source.scope) == builtins_module_scope(self.db, &env)
            },
        )
    }

    /// Returns a map from symbol name to that symbol's
    /// type and definition site (if available).
    ///
    /// The symbols are the symbols in scope at the given
    /// AST node.
    pub(crate) fn members_in_scope_at(
        &self,
        node: ast::AnyNodeRef<'_>,
    ) -> FxHashMap<Name, MemberDefinition<'db>> {
        let db = self.db;
        let mut members = FxHashMap::default();
        let program_file = self.program_file();
        let index = semantic_index(self.db, program_file);
        let Some(file_scope) = self.scope(node) else {
            return members;
        };
        for (file_scope, _) in index
            .visible_ancestor_scopes(file_scope)
            .collect::<Vec<_>>()
            .into_iter()
            .rev()
        {
            for memberdef in
                all_reachable_members(db, file_scope.to_scope_id(self.db, program_file))
            {
                members.insert(
                    memberdef.member.name,
                    MemberDefinition {
                        ty: memberdef.member.ty,
                        first_reachable_definition: memberdef.first_reachable_definition,
                    },
                );
            }
        }
        members
    }

    /// Resolve the given import made in this file to a Type
    pub fn resolve_module_type(&self, module: Option<&str>, level: u32) -> Option<Type<'db>> {
        let module = self.resolve_module(module, level)?;
        Some(Type::module_literal(self.db, self.program_file(), module))
    }

    /// Resolve the given import made in this file to a Module
    pub fn resolve_module(&self, module: Option<&str>, level: u32) -> Option<Module<'db>> {
        let importing_file = ImportingFile::File(
            self.file(),
            self.program_environment().resolver_environment(self.db),
        );
        let module_name =
            ModuleName::from_identifier_parts(self.db, importing_file, module, level).ok()?;
        resolve_module(self.db, importing_file, &module_name)
    }

    /// Returns completions for symbols available in a `import <CURSOR>` context.
    pub fn import_completions(&self) -> Vec<Completion<'db>> {
        let resolver_environment = self.program_environment().resolver_environment(self.db);
        list_modules(self.db, resolver_environment)
            .iter()
            .copied()
            .map(|module| {
                let builtin = module.is_known(self.db, KnownModule::Builtins);
                let ty = Type::module_literal(self.db, self.program_file(), module);
                Completion {
                    name: CompactString::new(module.name(self.db).as_str()),
                    ty: Some(ty),
                    builtin,
                    is_type_check_only: false,
                }
            })
            .collect()
    }

    /// Returns completions for symbols available in a `from module import <CURSOR>` context.
    pub fn from_import_completions(&self, import: &ast::StmtImportFrom) -> Vec<Completion<'db>> {
        let module_name = match ModuleName::from_import_statement(
            self.db,
            ImportingFile::File(
                self.file(),
                self.program_environment().resolver_environment(self.db),
            ),
            import,
        ) {
            Ok(module_name) => module_name,
            Err(err) => {
                tracing::debug!(
                    "Could not extract module name from `{module:?}` with level {level}: {err:?}",
                    module = import.module,
                    level = import.level,
                );
                return vec![];
            }
        };
        self.module_completions(&module_name)
    }

    /// Returns submodule-only completions for the given module.
    pub fn import_submodule_completions_for_name(
        &self,
        module_name: &ModuleName,
    ) -> Vec<Completion<'db>> {
        let Some(module) = resolve_module(
            self.db,
            ImportingFile::File(
                self.file(),
                self.program_environment().resolver_environment(self.db),
            ),
            module_name,
        ) else {
            tracing::debug!("Could not resolve module from `{module_name:?}`");
            return vec![];
        };
        self.submodule_completions(&module)
    }

    /// Returns completions for symbols available in the given module as if
    /// it were imported by this model's `File`.
    fn module_completions(&self, module_name: &ModuleName) -> Vec<Completion<'db>> {
        let db = self.db;
        let Some(module) = resolve_module(
            self.db,
            ImportingFile::File(
                self.file(),
                self.program_environment().resolver_environment(self.db),
            ),
            module_name,
        ) else {
            tracing::debug!("Could not resolve module from `{module_name:?}`");
            return vec![];
        };
        let ty = Type::module_literal(self.db, self.program_file(), module);
        let builtin = module.is_known(self.db, KnownModule::Builtins);

        let mut completions = vec![];
        #[expect(
            clippy::iter_over_hash_type,
            reason = "completion order is determined later by relevance ranking"
        )]
        for member in all_members(db, &self.program_environment(), ty) {
            completions.push(Completion {
                name: CompactString::new(member.name),
                ty: Some(member.ty),
                builtin,
                is_type_check_only: member.is_type_check_only,
            });
        }
        completions.extend(self.submodule_completions(&module));
        completions
    }

    /// Returns completions for submodules of the given module.
    fn submodule_completions(&self, module: &Module<'db>) -> Vec<Completion<'db>> {
        let builtin = module.is_known(self.db, KnownModule::Builtins);

        let mut completions = vec![];
        for submodule in module.all_submodules(self.db) {
            let ty = Type::module_literal(self.db, self.program_file(), *submodule);
            let base = submodule.name(self.db).last_component();
            completions.push(Completion {
                name: CompactString::new(base),
                ty: Some(ty),
                builtin,
                is_type_check_only: false,
            });
        }
        completions
    }

    /// Returns completions for symbols available in a `object.<CURSOR>` context.
    pub fn attribute_completions(&self, node: &ast::ExprAttribute) -> Vec<Completion<'db>> {
        let Some(ty) = node.value.inferred_type(self) else {
            return Vec::new();
        };

        self.member_completions(ty, ObjectMembers::Include)
    }

    /// Returns members of an already inferred receiver, including incomplete attribute syntax.
    pub fn member_completions(
        &self,
        ty: Type<'db>,
        object_members: ObjectMembers,
    ) -> Vec<Completion<'db>> {
        all_members_with_object_policy(self.db, &self.program_environment(), ty, object_members)
            .into_iter()
            .map(|member| Completion {
                name: CompactString::new(member.name),
                ty: Some(member.ty),
                builtin: false,
                is_type_check_only: member.is_type_check_only,
            })
            .collect()
    }

    /// Returns symbols from this scope and its enclosing scopes.
    ///
    /// The scope must come from this model's current semantic index. Symbols from nearer scopes come
    /// first; consumers that deduplicate names should retain the first occurrence. Implicit
    /// module globals and builtin namespaces are added separately by the caller.
    pub fn lexical_completions(
        &self,
        file_scope: FileScopeId,
    ) -> impl Iterator<Item = Completion<'db>> + '_ {
        let db = self.db;
        let program_file = self.program_file();
        let index = semantic_index(db, program_file);
        index
            .ancestor_scopes(file_scope)
            .flat_map(move |(file_scope, _)| {
                all_reachable_members(db, file_scope.to_scope_id(db, program_file)).map(
                    |memberdef| Completion {
                        name: CompactString::new(memberdef.member.name),
                        ty: Some(memberdef.member.ty),
                        builtin: false,
                        is_type_check_only: memberdef.member.is_type_check_only,
                    },
                )
            })
    }

    /// Returns completions for symbols available in the given scope, including
    /// implicit module globals and Python builtins.
    ///
    /// The scope must come from this model's current semantic index.
    pub fn scoped_completions(&self, file_scope: FileScopeId) -> Vec<Completion<'db>> {
        let mut completions: Vec<_> = self.lexical_completions(file_scope).collect();

        // Add implicit module globals (like `__file__`, `__name__`, etc.) with their
        // correct types. These are added before builtins so that the deduplication
        // keeps the correct types (e.g., `__file__` is `str` for the current module,
        // not `str | None`).
        completions.extend(
            all_implicit_module_globals(self.db, self.file).map(|(name, ty)| Completion {
                name: CompactString::new(name),
                ty: Some(ty),
                builtin: true,
                is_type_check_only: false,
            }),
        );

        // Project-level builtins take precedence over the standard builtins.
        let project_builtins = ModuleName::new_static("__builtins__").unwrap();
        let importing_file =
            ImportingFile::File(self.file(), self.file.resolver_environment(self.db));
        if resolve_module(self.db, importing_file, &project_builtins).is_some() {
            completions.extend(
                self.module_completions(&project_builtins)
                    .into_iter()
                    .filter(|completion| !completion.is_type_check_only)
                    .map(|mut completion| {
                        completion.builtin = true;
                        completion
                    }),
            );
        }

        // Builtins are available in all scopes.
        let builtins = KnownModule::Builtins.name();
        completions.extend(
            self.module_completions(&builtins)
                .into_iter()
                .filter(|completion| !completion.is_type_check_only),
        );

        // The above can sometimes result in duplicates. Get rid of them.
        completions.sort_by(|c1, c2| c1.name.cmp(&c2.name));
        completions.dedup_by(|c1, c2| c1.name == c2.name);

        completions
    }

    /// Returns `true` if the given class definition's name was previously
    /// bound in the same scope (i.e., the class definition is a re-assignment).
    pub fn is_class_name_reassigned(&self, class_def: &ast::StmtClassDef) -> bool {
        let index = semantic_index(self.db, self.program_file());
        if index.is_excluded(class_def.range()) {
            return false;
        }
        let definition = index.expect_single_definition(class_def);
        let scope = definition.scope(self.db);
        let table = place_table(self.db, scope);
        let place = table.place(definition.place(self.db));
        place.as_symbol().is_some_and(Symbol::is_reassigned)
    }

    /// Returns the scope in which `node` is defined (handles string annotations).
    pub fn scope(&self, node: ast::AnyNodeRef<'_>) -> Option<FileScopeId> {
        let index = semantic_index(self.db, self.program_file());
        if index.is_excluded(node.range()) {
            return None;
        }
        if let Some(scope) = self.annotation_scope {
            return Some(scope);
        }
        match node {
            ast::AnyNodeRef::Identifier(identifier) => index.try_expression_scope_id(identifier),

            // Nodes implementing `HasDefinition`
            ast::AnyNodeRef::StmtFunctionDef(function) => Some(
                function
                    .definition(self)
                    .scope(self.db)
                    .file_scope_id(self.db),
            ),
            ast::AnyNodeRef::StmtClassDef(class) => {
                Some(class.definition(self).scope(self.db).file_scope_id(self.db))
            }
            ast::AnyNodeRef::Parameter(parameter) => Some(
                parameter
                    .definition(self)
                    .scope(self.db)
                    .file_scope_id(self.db),
            ),
            ast::AnyNodeRef::ParameterWithDefault(parameter) => Some(
                parameter
                    .definition(self)
                    .scope(self.db)
                    .file_scope_id(self.db),
            ),
            ast::AnyNodeRef::ExceptHandlerExceptHandler(handler) => handler
                .optional_definition(self)
                .map(|definition| definition.scope(self.db).file_scope_id(self.db))
                .or_else(|| index.try_expression_scope_id(handler.type_.as_deref()?))
                .or(Some(FileScopeId::global())),
            ast::AnyNodeRef::TypeParamTypeVar(var) => {
                Some(var.definition(self).scope(self.db).file_scope_id(self.db))
            }

            // Fallback
            node => match node.as_expr_ref() {
                // If we couldn't identify a specific
                // expression that we're in, then just
                // fall back to the global scope.
                None => Some(FileScopeId::global()),
                Some(expr) => index.try_expression_scope_id(&expr),
            },
        }
    }

    /// Returns the scopes enclosing `node`, starting with the scope containing
    /// the node itself.
    ///
    /// Like [`Self::scope`], this handles nodes inside string annotations.
    pub fn ancestor_scopes(
        &self,
        node: ast::AnyNodeRef<'_>,
    ) -> impl Iterator<Item = (FileScopeId, &Scope)> + '_ {
        let index = semantic_index(self.db, self.program_file());
        self.scope(node)
            .into_iter()
            .flat_map(move |scope| index.ancestor_scopes(scope))
    }

    /// Returns the first local definition created by `covering_node`, if any.
    ///
    /// A local definition is a user-visible definition associated with `covering_node` itself, or
    /// one of its ancestors, whose focus range covers the queried node. This returns only the first
    /// match because one syntax node can represent multiple semantic definitions, for example
    /// `from module import *`. This helper is intended for classifying the local occurrence, such as
    /// deciding whether it is a binding or declaration, not for enumerating every symbol introduced
    /// by the syntax.
    pub fn first_local_definition(
        &self,
        covering_node: &CoveringNode<'_>,
    ) -> Option<Definition<'db>> {
        let index = semantic_index(self.db, self.program_file());
        let parsed = parsed_module(self.db, self.python_file()).load(self.db);
        let target_range = covering_node.node().range();

        for node in covering_node.ancestors() {
            let Some(definitions) = index.try_definitions(node) else {
                continue;
            };

            if let Some(definition) = definitions.iter().copied().find(|definition| {
                let kind = definition.kind(self.db);
                kind.is_user_visible()
                    && definition
                        .focus_range(self.db, &parsed)
                        .range()
                        .contains_range(target_range)
            }) {
                return Some(definition);
            }
        }

        None
    }

    /// Selects the same builtin namespace used to infer the node.
    pub(crate) fn builtin_usage(&self, node: ast::AnyNodeRef<'_>) -> crate::provided::BuiltinUsage {
        let index = semantic_index(self.db, self.program_file());
        let module = parsed_module(self.db, self.program_file().python_file(self.db)).load(self.db);
        if self.annotation_scope.is_some()
            || index.annotation_parent_scope_id(&module, &node).is_some()
        {
            crate::provided::BuiltinUsage::Annotation
        } else {
            crate::provided::BuiltinUsage::Runtime
        }
    }

    /// Given a string expression, determine if it's a string annotation, and if it is,
    /// yield the parsed sub-AST and a sub-model that knows it's analyzing a sub-AST.
    ///
    /// Analysis of the sub-AST should only be done with the sub-model, or else things
    /// may return nonsense results or even panic!
    pub fn enter_string_annotation(
        &self,
        string_expr: &ExprStringLiteral,
    ) -> Option<(Parsed<ModExpression>, Self)> {
        // Ask the inference engine whether this is actually a string annotation
        let expr = ExprRef::StringLiteral(string_expr);
        // Nested string annotations retain the outer annotation's scope.
        let file_scope = self.scope(expr.into())?;
        let scope = file_scope.to_scope_id(self.db, self.program_file());
        // When querying whether the expr is a string annotation, we do however use the actual expr
        // (the inference engine should record this information even for sub-nodes)
        if !infer_complete_scope_types(self.db, scope).is_string_annotation(expr) {
            return None;
        }

        // Parse the sub-AST and preserve the scope that owns its inferred types.
        let source = source_text(self.db, self.file());
        let string_literal = string_expr.as_single_part_string()?;
        let ast = parsed_string_annotation(source.as_str(), string_literal).ok()?;
        let model = Self {
            db: self.db,
            file: self.file,
            annotation_scope: Some(file_scope),
        };
        Some((ast, model))
    }

    /// Returns whether `annotation` declares a PEP 613 type alias.
    pub fn is_type_alias_annotation(&self, annotation: &Expr) -> bool {
        matches!(
            annotation.inferred_type(self),
            Some(Type::SpecialForm(SpecialFormType::TypeAlias))
        )
    }

    /// Returns whether `definition` defines a PEP 613 or PEP 695 type alias.
    pub fn is_type_alias_definition(&self, definition: Definition<'db>) -> bool {
        match definition.kind(self.db) {
            DefinitionKind::TypeAlias(_) => true,
            DefinitionKind::AnnotatedAssignment(assignment) => {
                let parsed = parsed_module(self.db, definition.python_file(self.db));
                let model = Self::new(self.db, definition.program_file(self.db));
                model.is_type_alias_annotation(assignment.annotation(&parsed.load(self.db)))
            }
            _ => false,
        }
    }

    /// Returns the type qualifiers (e.g. `Final`, `ClassVar`) for a given expression,
    /// if the expression refers to a name or attribute with declared qualifiers.
    pub fn type_qualifiers(&self, expr: ExprRef<'_>) -> TypeQualifiers {
        let db = self.db;
        match expr {
            ExprRef::Name(name) => {
                let Some(definition) =
                    definition_for_name(self, name, ImportAliasResolution::ResolveAliases)
                else {
                    return TypeQualifiers::empty();
                };
                let module = parsed_module(self.db, definition.python_file(self.db)).load(self.db);
                if !definition.category(self.db, &module).is_declaration() {
                    return TypeQualifiers::empty();
                }
                let Some(declared) = inferred_declaration(self.db(), definition).declared() else {
                    return TypeQualifiers::empty();
                };
                declared.qualifiers()
            }
            ExprRef::Attribute(attr) => {
                let Some(value_ty) = attr.value.inferred_type(self) else {
                    return TypeQualifiers::empty();
                };
                value_ty
                    .member_lookup_with_policy(
                        db,
                        &self.program_environment(),
                        &attr.attr.id,
                        crate::types::MemberLookupPolicy::default(),
                    )
                    .qualifiers
            }
            _ => TypeQualifiers::empty(),
        }
    }

    /// Returns completion candidates from a string's expected type and dictionary initializer.
    ///
    /// If provided, `subscript` must have `string_expr` as its complete slice.
    /// Initializer keys are suggestions, not a guarantee that a mutable dictionary still contains
    /// them or that it contains no other keys.
    pub fn expected_string_literal_completions(
        &self,
        string_expr: &ast::ExprStringLiteral,
        subscript: Option<&ast::ExprSubscript>,
    ) -> Vec<ExpectedStringLiteralCompletion<'db>> {
        struct StringLiteralCandidates;
        type StringLiteralCandidatesVisitor<'db> = CycleDetector<
            'db,
            StringLiteralCandidates,
            Type<'db>,
            Vec<ExpectedStringLiteralCompletion<'db>>,
            3,
        >;

        fn collect<'db>(
            db: &'db dyn Db,
            ty: Type<'db>,
            visitor: &StringLiteralCandidatesVisitor<'db>,
        ) -> Vec<ExpectedStringLiteralCompletion<'db>> {
            match ty {
                Type::LiteralValue(literal) => literal
                    .as_string()
                    .map(|string_literal| {
                        let value = string_literal.value(db).to_string();
                        vec![ExpectedStringLiteralCompletion {
                            ty: Type::string_literal(db, &*value),
                            value,
                        }]
                    })
                    .unwrap_or_default(),
                Type::Union(union) => union
                    .elements(db)
                    .iter()
                    .flat_map(|element| collect(db, *element, visitor))
                    .collect(),
                Type::Intersection(intersection) => intersection
                    .positive(db)
                    .iter()
                    .flat_map(|element| collect(db, *element, visitor))
                    .collect(),
                Type::TypeAlias(alias) => {
                    visitor.visit(db, ty, || collect(db, alias.value_type(db), visitor))
                }
                Type::Recursive(recursive) => visitor.visit(db, ty, || {
                    recursive
                        .unfold(db, &recursive.environment(db))
                        .map(|unfolded| collect(db, unfolded, visitor))
                        .unwrap_or_else(Vec::new)
                }),
                _ => Vec::new(),
            }
        }
        if semantic_index(self.db, self.file).is_excluded(string_expr.range()) {
            return Vec::new();
        }
        let db = self.db;

        let expected_ty = self.string_literal_completion_expected_type(string_expr);
        let mut candidates = expected_ty
            .map(|expected_ty| collect(db, expected_ty, &StringLiteralCandidatesVisitor::default()))
            .unwrap_or_default();
        // Finite choices from the expected type take precedence. A string used as the complete
        // subscript key can fall back to initializer keys that fit any known expected type.
        if candidates.is_empty()
            && self.annotation_scope.is_none()
            && let Some(subscript) = subscript
        {
            self.dictionary_initializer_keys(
                &subscript.value,
                &mut FxHashSet::default(),
                &mut candidates,
            );
            if let Some(expected_ty) = expected_ty {
                candidates.retain(|candidate| {
                    candidate
                        .ty
                        .is_assignable_to(db, &self.program_environment(), expected_ty)
                });
            }
        }
        candidates.sort_unstable_by(|left, right| left.value.cmp(&right.value));
        candidates.dedup_by(|left, right| left.value == right.value);
        candidates
    }

    /// Appends literal string keys from dictionary initializers that can reach `receiver`.
    ///
    /// Follows reaching definitions, aliases, `from` imports, and nested dictionary lookups,
    /// ignoring unreachable or discarded assignments. The caller's `visited` set breaks
    /// definition cycles. The caller filters candidates against the expected type, sorts them,
    /// and removes duplicates.
    fn dictionary_initializer_keys(
        &self,
        receiver: &ast::Expr,
        visited: &mut FxHashSet<Definition<'db>>,
        candidates: &mut Vec<ExpectedStringLiteralCompletion<'db>>,
    ) {
        if let ast::Expr::Dict(dict) = receiver {
            candidates.extend(dict.items.iter().filter_map(|item| {
                let ast::Expr::StringLiteral(key) = item.key.as_ref()? else {
                    return None;
                };
                let value = key.value.to_string();
                Some(ExpectedStringLiteralCompletion {
                    ty: Type::string_literal(self.db, value.as_str()),
                    value,
                })
            }));
            return;
        }

        let mut definitions = self.reaching_definitions_at(receiver);
        while let Some(definition) = definitions.pop() {
            if !visited.insert(definition) {
                continue;
            }
            let kind = definition.kind(self.db);
            if kind.is_loop_header() {
                definitions.extend(
                    loop_header_reachability(self.db, definition)
                        .reachable_bindings
                        .iter()
                        .map(|binding| binding.definition),
                );
                continue;
            }
            if kind.is_import() {
                self.extend_imported_definitions(definition, &mut definitions);
                continue;
            }
            let file = definition.program_file(self.db);
            let module = parsed_module(self.db, file.python_file(self.db)).load(self.db);
            let value = match kind {
                DefinitionKind::Assignment(assignment) => assignment
                    .unpack()
                    .is_none()
                    .then(|| assignment.value(&module)),
                DefinitionKind::AnnotatedAssignment(assignment) => assignment.value(&module),
                DefinitionKind::DictKeyAssignment(assignment) => Some(assignment.value(&module)),
                _ => None,
            };
            if let Some(value) = value
                && !infer_definition_types(self.db, definition).discards_dict_key_assignments()
                && !is_discarded_dict_key_assignment(self.db, definition)
            {
                Self::new(self.db, file).dictionary_initializer_keys(value, visited, candidates);
            }
        }
    }

    /// Returns definitions that can reach this expression's load.
    ///
    /// Names follow Python's scope lookup rules, stopping at a definitely bound source.
    /// Other tracked places use the bindings recorded at their use site.
    fn reaching_definitions_at(&self, receiver: &ast::Expr) -> Vec<Definition<'db>> {
        let index = semantic_index(self.db, self.file);
        let Some(scope) = index.try_expression_scope_id(receiver) else {
            return Vec::new();
        };
        let Some(use_id) = index.try_expression_use_id(receiver.into()) else {
            return Vec::new();
        };
        let mut definitions = Vec::new();
        let mut add_bindings = |bindings: BindingWithConstraintsIterator<'db, 'db>| {
            let resolution = DefinitionResolution::from_bindings(self.db, bindings);
            definitions.extend_from_slice(resolution.definitions());
        };
        if let ast::Expr::Name(name) = receiver {
            let mut resolution = resolve_place_load(
                self.db,
                index,
                scope.to_scope_id(self.db, self.file),
                PlaceExpr::from_expr_name(name),
                PlaceLoadMode::AtExpression(name.into()),
            );
            while let Some(PlaceLoadResolutionStep::Source(source)) = resolution.next() {
                match source.kind {
                    PlaceLoadSourceKind::Bindings(bindings) => {
                        let bound = place_from_bindings(
                            self.db,
                            &self.program_environment(),
                            bindings.clone(),
                        )
                        .place
                        .is_definitely_bound();
                        add_bindings(bindings);
                        if bound {
                            break;
                        }
                    }
                    PlaceLoadSourceKind::DefinitionsFromOwningScope { scope, id } => {
                        let index = semantic_index(self.db, scope.program_file(self.db));
                        add_bindings(
                            index
                                .use_def_map(scope.file_scope_id(self.db))
                                .reachable_bindings(id),
                        );
                        break;
                    }
                    PlaceLoadSourceKind::Implicit(ImplicitPlaceLoad::ClassBodySymbol(name)) => {
                        if class_body_implicit_symbol(self.db, &self.program_environment(), &name)
                            .place
                            .is_definitely_bound()
                        {
                            break;
                        }
                    }
                    PlaceLoadSourceKind::Implicit(ImplicitPlaceLoad::ExplicitGlobalSymbol {
                        file,
                        name,
                    }) => {
                        let index = semantic_index(self.db, file);
                        if let Some(id) = index.place_table(FileScopeId::global()).symbol_id(&name)
                        {
                            add_bindings(
                                index
                                    .use_def_map(FileScopeId::global())
                                    .reachable_symbol_bindings(id),
                            );
                        }
                        break;
                    }
                    PlaceLoadSourceKind::Implicit(_) => break,
                }
            }
        } else {
            add_bindings(index.use_def_map(scope).bindings_at_use(use_id));
        }
        definitions
    }

    /// Appends the reachable bindings of an imported symbol in its target module.
    ///
    /// Follows one import at a time so an overwritten re-export cannot contribute keys.
    fn extend_imported_definitions(
        &self,
        definition: Definition<'db>,
        definitions: &mut Vec<Definition<'db>>,
    ) {
        let file = definition.program_file(self.db);
        let kind = definition.kind(self.db);
        if matches!(kind, DefinitionKind::ProvidedBinding(_)) {
            match self.db.provided_binding(definition).value {
                ProvidedBindingValue::Export { file, name } => {
                    self.extend_exported_definitions(file, &name, definitions);
                }
                ProvidedBindingValue::Value(_) => {}
                ProvidedBindingValue::Unresolved => {}
            }
            return;
        }
        let module = parsed_module(self.db, file.python_file(self.db)).load(self.db);
        let (import, name) = match &kind {
            DefinitionKind::ImportFrom(import) => {
                (import.import(&module), import.alias(&module).name.as_str())
            }
            DefinitionKind::StarImport(import) => {
                let Some(symbol) = semantic_index(self.db, file)
                    .place_table(definition.file_scope(self.db))
                    .place(definition.place(self.db))
                    .as_symbol()
                else {
                    return;
                };
                (import.import(&module), symbol.name().as_str())
            }
            _ => return,
        };
        let env = ProgramEnvironment::from_file(file);
        let importing_file =
            ImportingFile::File(file.file(self.db), env.resolver_environment(self.db));
        let Some(target_file) = resolve_module_for_import_from(self.db, importing_file, import)
            .and_then(|module| module.file(self.db))
        else {
            return;
        };
        let target_file = ProgramFile::new(self.db, target_file, env.program(self.db));
        self.extend_exported_definitions(target_file, name, definitions);
    }

    fn extend_exported_definitions(
        &self,
        target_file: ProgramFile<'db>,
        name: &str,
        definitions: &mut Vec<Definition<'db>>,
    ) {
        let index = semantic_index(self.db, target_file);
        let Some(id) = index.place_table(FileScopeId::global()).symbol_id(name) else {
            return;
        };
        let resolution = DefinitionResolution::from_bindings(
            self.db,
            index
                .use_def_map(FileScopeId::global())
                .end_of_scope_symbol_bindings(id),
        );
        definitions.extend_from_slice(resolution.definitions());
    }

    fn string_literal_completion_expected_type(
        &self,
        string_expr: &ast::ExprStringLiteral,
    ) -> Option<Type<'db>> {
        let expr = ast::ExprRef::from(string_expr);
        let file_scope = self.scope(expr.into())?;
        let scope = file_scope.to_scope_id(self.db, self.program_file());

        infer_complete_scope_types(self.db, scope).try_expected_type(expr)
    }
}

/// The type and definition of a symbol.
#[derive(Clone, Debug)]
pub(crate) struct MemberDefinition<'db> {
    pub(crate) ty: Type<'db>,
    pub(crate) first_reachable_definition: Definition<'db>,
}

/// A classification of symbol names.
///
/// The ordering here is used for sorting completions.
///
/// This sorts "normal" names first, then dunder names and finally
/// single-underscore names. This matches the order of the variants defined for
/// this enum, which is in turn picked up by the derived trait implementation
/// for `Ord`.
#[derive(Clone, Copy, Debug, Eq, PartialEq, PartialOrd, Ord)]
pub enum NameKind {
    Normal,
    Dunder,
    Sunder,
}

impl NameKind {
    pub fn classify(name: &str) -> NameKind {
        // Dunder needs a prefix and suffix double underscore.
        // When there's only a prefix double underscore, this
        // results in explicit name mangling. We let that be
        // classified as-if they were single underscore names.
        //
        // Ref: <https://docs.python.org/3/reference/lexical_analysis.html#reserved-classes-of-identifiers>
        if name.starts_with("__") && name.ends_with("__") {
            NameKind::Dunder
        } else if name.starts_with('_') {
            NameKind::Sunder
        } else {
            NameKind::Normal
        }
    }
}

/// A suggestion for code completion.
#[derive(Clone, Debug)]
pub struct Completion<'db> {
    /// The label shown to the user for this suggestion.
    pub name: CompactString,
    /// The type of this completion, if available.
    ///
    /// Generally speaking, this is always available
    /// *unless* this was a completion corresponding to
    /// an unimported symbol. In that case, computing the
    /// type of all such symbols could be quite expensive.
    pub ty: Option<Type<'db>>,
    /// Whether this suggestion came from builtins or not.
    ///
    /// At time of writing (2025-06-26), this information
    /// doesn't make it into the LSP response. Instead, we
    /// use it mainly in tests so that we can write less
    /// noisy tests.
    pub builtin: bool,
    /// Whether this symbol is known to exist only for type checking and should
    /// be ranked below runtime values.
    pub is_type_check_only: bool,
}

#[derive(Clone, Debug)]
pub struct ExpectedStringLiteralCompletion<'db> {
    pub value: String,
    pub ty: Type<'db>,
}

pub trait HasType {
    /// Returns the inferred type of `self`.
    ///
    /// ## Panics
    /// May panic if `self` is from another file than `model`.
    fn inferred_type<'db>(&self, model: &SemanticModel<'db>) -> Option<Type<'db>>;
}

pub trait HasDefinition {
    /// Returns the definition of an admitted, indexed source node.
    ///
    /// ## Panics
    /// May panic if `self` is from another file than `model`, or belongs to a statement
    /// excluded by the source frontend. Use [`SemanticModel::scope`] to test source admission.
    fn definition<'db>(&self, model: &SemanticModel<'db>) -> Definition<'db>;
}

trait HasOptionalDefinition {
    /// Returns the definition of `self`, if it has one.
    ///
    /// ## Panics
    /// May panic if `self` is from another file than `model`.
    fn optional_definition<'db>(&self, model: &SemanticModel<'db>) -> Option<Definition<'db>>;
}

impl HasType for ast::ExprRef<'_> {
    fn inferred_type<'db>(&self, model: &SemanticModel<'db>) -> Option<Type<'db>> {
        let file = model.program_file();
        let file_scope = model.scope((*self).into())?;
        let scope = file_scope.to_scope_id(model.db, file);

        infer_complete_scope_types(model.db, scope).try_expression_type(*self)
    }
}

macro_rules! impl_expression_has_type {
    ($ty: ty) => {
        impl HasType for $ty {
            #[inline]
            fn inferred_type<'db>(&self, model: &SemanticModel<'db>) -> Option<Type<'db>> {
                let expression_ref = ExprRef::from(self);
                expression_ref.inferred_type(model)
            }
        }
    };
}

impl_expression_has_type!(ast::ExprBoolOp);
impl_expression_has_type!(ast::ExprNamed);
impl_expression_has_type!(ast::ExprBinOp);
impl_expression_has_type!(ast::ExprUnaryOp);
impl_expression_has_type!(ast::ExprLambda);
impl_expression_has_type!(ast::ExprIf);
impl_expression_has_type!(ast::ExprDict);
impl_expression_has_type!(ast::ExprSet);
impl_expression_has_type!(ast::ExprListComp);
impl_expression_has_type!(ast::ExprSetComp);
impl_expression_has_type!(ast::ExprDictComp);
impl_expression_has_type!(ast::ExprGenerator);
impl_expression_has_type!(ast::ExprAwait);
impl_expression_has_type!(ast::ExprYield);
impl_expression_has_type!(ast::ExprYieldFrom);
impl_expression_has_type!(ast::ExprCompare);
impl_expression_has_type!(ast::ExprCall);
impl_expression_has_type!(ast::ExprFString);
impl_expression_has_type!(ast::ExprTString);
impl_expression_has_type!(ast::ExprStringLiteral);
impl_expression_has_type!(ast::ExprBytesLiteral);
impl_expression_has_type!(ast::ExprNumberLiteral);
impl_expression_has_type!(ast::ExprBooleanLiteral);
impl_expression_has_type!(ast::ExprNoneLiteral);
impl_expression_has_type!(ast::ExprEllipsisLiteral);
impl_expression_has_type!(ast::ExprAttribute);
impl_expression_has_type!(ast::ExprSubscript);
impl_expression_has_type!(ast::ExprStarred);
impl_expression_has_type!(ast::ExprName);
impl_expression_has_type!(ast::ExprList);
impl_expression_has_type!(ast::ExprTuple);
impl_expression_has_type!(ast::ExprSlice);
impl_expression_has_type!(ast::ExprIpyEscapeCommand);

impl HasType for ast::Expr {
    fn inferred_type<'db>(&self, model: &SemanticModel<'db>) -> Option<Type<'db>> {
        match self {
            Expr::BoolOp(inner) => inner.inferred_type(model),
            Expr::Named(inner) => inner.inferred_type(model),
            Expr::BinOp(inner) => inner.inferred_type(model),
            Expr::UnaryOp(inner) => inner.inferred_type(model),
            Expr::Lambda(inner) => inner.inferred_type(model),
            Expr::If(inner) => inner.inferred_type(model),
            Expr::Dict(inner) => inner.inferred_type(model),
            Expr::Set(inner) => inner.inferred_type(model),
            Expr::ListComp(inner) => inner.inferred_type(model),
            Expr::SetComp(inner) => inner.inferred_type(model),
            Expr::DictComp(inner) => inner.inferred_type(model),
            Expr::Generator(inner) => inner.inferred_type(model),
            Expr::Await(inner) => inner.inferred_type(model),
            Expr::Yield(inner) => inner.inferred_type(model),
            Expr::YieldFrom(inner) => inner.inferred_type(model),
            Expr::Compare(inner) => inner.inferred_type(model),
            Expr::Call(inner) => inner.inferred_type(model),
            Expr::FString(inner) => inner.inferred_type(model),
            Expr::TString(inner) => inner.inferred_type(model),
            Expr::StringLiteral(inner) => inner.inferred_type(model),
            Expr::BytesLiteral(inner) => inner.inferred_type(model),
            Expr::NumberLiteral(inner) => inner.inferred_type(model),
            Expr::BooleanLiteral(inner) => inner.inferred_type(model),
            Expr::NoneLiteral(inner) => inner.inferred_type(model),
            Expr::EllipsisLiteral(inner) => inner.inferred_type(model),
            Expr::Attribute(inner) => inner.inferred_type(model),
            Expr::Subscript(inner) => inner.inferred_type(model),
            Expr::Starred(inner) => inner.inferred_type(model),
            Expr::Name(inner) => inner.inferred_type(model),
            Expr::List(inner) => inner.inferred_type(model),
            Expr::Tuple(inner) => inner.inferred_type(model),
            Expr::Slice(inner) => inner.inferred_type(model),
            Expr::IpyEscapeCommand(inner) => inner.inferred_type(model),
        }
    }
}

macro_rules! impl_binding_has_ty_def {
    ($ty: ty) => {
        impl HasDefinition for $ty {
            #[inline]
            fn definition<'db>(&self, model: &SemanticModel<'db>) -> Definition<'db> {
                let index = semantic_index(model.db, model.program_file());
                index.expect_single_definition(self)
            }
        }

        impl HasType for $ty {
            #[inline]
            fn inferred_type<'db>(&self, model: &SemanticModel<'db>) -> Option<Type<'db>> {
                if semantic_index(model.db, model.program_file()).is_excluded(self.range()) {
                    return None;
                }
                let binding = HasDefinition::definition(self, model);
                Some(model.definition_type(binding))
            }
        }
    };
}

impl_binding_has_ty_def!(ast::StmtFunctionDef);
impl_binding_has_ty_def!(ast::StmtClassDef);
impl_binding_has_ty_def!(ast::Parameter);
impl_binding_has_ty_def!(ast::ParameterWithDefault);
impl_binding_has_ty_def!(ast::TypeParamTypeVar);
impl_binding_has_ty_def!(ast::TypeParamParamSpec);
impl_binding_has_ty_def!(ast::TypeParamTypeVarTuple);
impl_binding_has_ty_def!(ast::StmtTypeAlias);

impl HasType for ast::Alias {
    fn inferred_type<'db>(&self, model: &SemanticModel<'db>) -> Option<Type<'db>> {
        if semantic_index(model.db, model.program_file()).is_excluded(self.range()) {
            return None;
        }
        if &self.name == "*" {
            return Some(Type::Never);
        }
        let index = semantic_index(model.db, model.program_file());
        Some(model.definition_type(index.expect_single_definition(self)))
    }
}

impl HasOptionalDefinition for ast::ExceptHandlerExceptHandler {
    fn optional_definition<'db>(&self, model: &SemanticModel<'db>) -> Option<Definition<'db>> {
        self.name.as_ref()?;
        if semantic_index(model.db, model.program_file()).is_excluded(self.range()) {
            return None;
        }

        let index = semantic_index(model.db, model.program_file());
        Some(index.expect_single_definition(self))
    }
}

impl HasType for ast::ExceptHandlerExceptHandler {
    fn inferred_type<'db>(&self, model: &SemanticModel<'db>) -> Option<Type<'db>> {
        let definition = self.optional_definition(model)?;
        Some(model.definition_type(definition))
    }
}

#[cfg(test)]
mod tests {
    use super::ObjectMembers;
    use crate::db::tests::{TestDb, TestDbBuilder};
    use crate::{Db as _, HasType, SemanticModel};
    use ruff_db::files::system_path_to_file;
    use ruff_db::parsed::parsed_module;
    use ruff_db::system::DbWithWritableSystem as _;
    use ruff_python_ast::ExprRef;
    use ruff_text_size::Ranged;
    use ty_python_core::ProgramFile;
    use ty_python_core::definition::DefinitionKind;
    use ty_python_core::semantic_index;

    fn names_are_confined(db: &TestDb, source: &str) -> anyhow::Result<bool> {
        let file = db.program_file(system_path_to_file(db, "/src/main.py")?);
        let module = parsed_module(db, file.python_file(db)).load(db);
        let model = SemanticModel::new(db, file);
        let start = source.find("ROOT =").expect("root assignment");
        let end = source[start..]
            .find('\n')
            .map_or(source.len(), |end| start + end);
        let names: Vec<_> = semantic_index(db, file)
            .expression_uses(&module)
            .filter_map(|(_, expression, _)| {
                let ExprRef::Name(name) = expression else {
                    return None;
                };
                (usize::from(name.start()) >= start && usize::from(name.end()) <= end)
                    .then_some(name)
            })
            .collect();
        assert!(!names.is_empty(), "root contains named leaves");
        let Some(definitions) = model.confined_name_definitions(&names) else {
            return Ok(false);
        };
        assert_eq!(definitions.len(), names.len());
        for (definition, name) in definitions.into_iter().zip(names) {
            let DefinitionKind::Assignment(assignment) = definition.kind(db) else {
                panic!("confined definitions are assignments");
            };
            assert_eq!(
                assignment.target(&module).as_name_expr().unwrap().id,
                name.id
            );
        }
        Ok(true)
    }

    #[test]
    fn name_confinement_uses_raw_bindings_and_lexical_identity() -> anyhow::Result<()> {
        for (source, expected) in [
            ("leaf = ['a']\nROOT = [leaf, leaf]\n", true),
            (
                "first = ['a']\nsecond = ['b']\nROOT = [first, second, first]\n",
                true,
            ),
            (
                "leaf = ['a']\ndef other(leaf): return leaf\nROOT = [leaf]\n",
                true,
            ),
            (
                "leaf = ['a']\ndef other():\n    leaf = []\n    return leaf\nROOT = [leaf]\n",
                true,
            ),
            (
                "leaf = ['a']\nclass Other:\n    leaf = []\n    value = leaf\nROOT = [leaf]\n",
                true,
            ),
            ("leaf = ['a']\ncorrupt(leaf)\nROOT = [leaf]\n", false),
            ("leaf = ['a']\nROOT = [leaf]\ncorrupt(leaf)\n", false),
            (
                "leaf = ['a']\nROOT = [leaf]\nif False: corrupt(leaf)\n",
                false,
            ),
            ("leaf = ['a']\nALIAS = leaf\nROOT = [leaf]\n", false),
            ("leaf = ['a']\nmethod = leaf.append\nROOT = [leaf]\n", false),
            (
                "leaf = ['a']\nother = {'leaf': leaf}\nROOT = [leaf]\n",
                false,
            ),
            ("leaf = ['a']\nleaf[0] = 'b'\nROOT = [leaf]\n", false),
            ("leaf = ['a']\nROOT = [leaf]\ndel leaf\n", false),
            ("leaf = ['a']\nROOT = [leaf]\nleaf += ['b']\n", false),
            ("leaf = ['a']\nROOT = [leaf]\nleaf = []\n", false),
            (
                "for _ in range(2):\n    leaf = ['a']\n    ROOT = [leaf]\n",
                false,
            ),
            ("leaf = ['a']\nROOT = [leaf]\ndef leaf(): pass\n", false),
            (
                "leaf = ['a']\ndef nested(): return leaf\nROOT = [leaf]\n",
                false,
            ),
            (
                "leaf = ['a']\ndef nested():\n    global leaf\n    return leaf\nROOT = [leaf]\n",
                false,
            ),
            (
                "def outer():\n    leaf = ['a']\n    def nested():\n        nonlocal leaf\n        return leaf\n    ROOT = [leaf]\n",
                false,
            ),
            (
                "leaf = ['a']\nclass Other:\n    value = leaf\n    leaf = []\nROOT = [leaf]\n",
                false,
            ),
            ("if condition: leaf = ['a']\nROOT = [leaf]\n", false),
        ] {
            let db = TestDbBuilder::new()
                .with_file("/src/main.py", source)
                .build()?;
            assert_eq!(names_are_confined(&db, source)?, expected, "{source}");
        }
        Ok(())
    }

    #[test]
    fn name_confinement_tracks_source_edits() -> anyhow::Result<()> {
        let mut db = TestDbBuilder::new().with_file("/src/main.py", "").build()?;
        for (source, expected) in [
            ("leaf = ['a']\nROOT = [leaf, leaf]\n", true),
            ("leaf = ['a']\nROOT = [leaf, leaf]\ncorrupt(leaf)\n", false),
            ("leaf = ['a']\nROOT = [leaf, leaf]\n", true),
            ("leaf = ['a']\nleaf = []\nROOT = [leaf, leaf]\n", false),
            ("leaf = ['a']\nROOT = [leaf, leaf]\n", true),
        ] {
            db.write_file("/src/main.py", source)?;
            assert_eq!(names_are_confined(&db, source)?, expected, "{source}");
        }
        Ok(())
    }

    #[test]
    fn member_completion_can_exclude_object_declarations() -> anyhow::Result<()> {
        let db = TestDbBuilder::new()
            .with_file(
                "/src/main.py",
                "class A:\n    __explicit__: int\nclass B:\n    __explicit__: str\ndef use(value: A | B): ...\n",
            )
            .build()?;
        let file = db.program_file(system_path_to_file(&db, "/src/main.py")?);
        let module = parsed_module(&db, file.python_file(&db)).load(&db);
        let model = SemanticModel::new(&db, file);
        let [
            ruff_python_ast::Stmt::ClassDef(class),
            _,
            ruff_python_ast::Stmt::FunctionDef(function),
        ] = module.suite().as_slice()
        else {
            panic!("expected two classes and a function");
        };
        let [parameter] = function.parameters.args.as_slice() else {
            panic!("expected one parameter");
        };
        for ty in [
            class.inferred_type(&model).unwrap(),
            parameter.parameter.inferred_type(&model).unwrap(),
        ] {
            let included = model.member_completions(ty, ObjectMembers::Include);
            assert!(included.iter().any(|member| member.name == "__eq__"));
            let excluded = model.member_completions(ty, ObjectMembers::Exclude);
            assert!(excluded.iter().all(|member| member.name != "__eq__"));
            assert!(excluded.iter().any(|member| member.name == "__explicit__"));
        }
        Ok(())
    }

    #[test]
    fn inherited_completion_preserves_type_check_only() -> anyhow::Result<()> {
        let db = TestDbBuilder::new()
            .with_file(
                "/src/main.py",
                "from typing import type_check_only\nclass Base:\n    @type_check_only\n    def hidden(self) -> int: ...\n    def visible(self) -> int: ...\nclass Child(Base): ...\nvalue = Child()\nvalue.visible\n",
            )
            .build()?;
        let file = db.program_file(system_path_to_file(&db, "/src/main.py")?);
        let module = parsed_module(&db, file.python_file(&db)).load(&db);
        let attribute = module
            .suite()
            .last()
            .unwrap()
            .as_expr_stmt()
            .unwrap()
            .value
            .as_attribute_expr()
            .unwrap();
        let model = SemanticModel::new(&db, file);
        let completions = model.attribute_completions(attribute);
        assert!(
            completions
                .iter()
                .any(|member| member.name == "hidden" && member.is_type_check_only)
        );
        assert!(
            completions
                .iter()
                .any(|member| member.name == "visible" && !member.is_type_check_only)
        );
        Ok(())
    }

    #[test]
    fn function_type() -> anyhow::Result<()> {
        let db = TestDbBuilder::new()
            .with_file("/src/foo.py", "def test(): pass")
            .build()?;

        let foo = system_path_to_file(&db, "/src/foo.py").unwrap();

        let foo = ProgramFile::new(&db, foo, db.program_environment().program(&db));
        let ast = parsed_module(&db, foo.python_file(&db)).load(&db);

        let function = ast.suite()[0].as_function_def_stmt().unwrap();
        let model = SemanticModel::new(&db, foo);
        let ty = function.inferred_type(&model).unwrap();

        assert!(ty.is_function_literal());

        Ok(())
    }

    #[test]
    fn class_type() -> anyhow::Result<()> {
        let db = TestDbBuilder::new()
            .with_file("/src/foo.py", "class Test: pass")
            .build()?;

        let foo = system_path_to_file(&db, "/src/foo.py").unwrap();

        let foo = ProgramFile::new(&db, foo, db.program_environment().program(&db));
        let ast = parsed_module(&db, foo.python_file(&db)).load(&db);

        let class = ast.suite()[0].as_class_def_stmt().unwrap();
        let model = SemanticModel::new(&db, foo);
        let ty = class.inferred_type(&model).unwrap();

        assert!(ty.is_class_literal());

        Ok(())
    }

    #[test]
    fn alias_type() -> anyhow::Result<()> {
        let db = TestDbBuilder::new()
            .with_file("/src/foo.py", "class Test: pass")
            .with_file("/src/bar.py", "from foo import Test")
            .build()?;

        let bar = system_path_to_file(&db, "/src/bar.py").unwrap();

        let bar = ProgramFile::new(&db, bar, db.program_environment().program(&db));
        let ast = parsed_module(&db, bar.python_file(&db)).load(&db);

        let import = ast.suite()[0].as_import_from_stmt().unwrap();
        let alias = &import.names[0];
        let model = SemanticModel::new(&db, bar);
        let ty = alias.inferred_type(&model).unwrap();

        assert!(ty.is_class_literal());

        Ok(())
    }
}
