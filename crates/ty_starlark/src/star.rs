//! A bounded static source check for host-owned typed `.star` graphs.
//!
//! The host captures exact source text and resolves direct loads with its
//! parser. This pass uses those snapshots to check
//! primitive fields of source-declared record constructors. Other Starlark
//! forms remain unproved; an analyzed graph is never a full type proof.

use std::collections::hash_map::Entry;
use std::collections::{HashMap, HashSet};

use ruff_db::files::File;
use ruff_python_ast::visitor::Visitor;
use ruff_python_ast::{self as ast, Expr, ModModule, Number, PythonVersion, Stmt};
use ruff_python_parser::{
    Mode, ParseError, ParseOptions, Parsed, UnsupportedSyntaxError, parse_unchecked,
};
use ruff_text_size::{Ranged, TextRange};

/// Direct bindings already resolved by the host's actual loader.
#[derive(Debug)]
pub struct StarLoadBinding {
    pub local: String,
    pub source: String,
}

/// The label range includes the quotes around the module-ID literal.
#[derive(Debug)]
pub struct StarDirectLoad {
    pub module_id: String,
    pub label_range: TextRange,
    pub bindings: Box<[StarLoadBinding]>,
}

/// The text is the exact UTF-8 snapshot parsed by the host, not a later read.
#[derive(Debug)]
pub struct StarSource {
    pub file: File,
    pub text: String,
    pub loads: Box<[StarDirectLoad]>,
}

#[derive(Debug)]
pub struct StarModule {
    pub id: String,
    pub source: StarSource,
}

/// Producer-provided names and behavior of recognized record constructor forms.
#[derive(Debug)]
pub struct StarSpecialForm {
    pub name: String,
    pub kind: String,
    pub validator: String,
    pub field_types: String,
}

#[derive(Debug)]
pub struct StarHostProfile {
    pub name: String,
    pub special_forms: Box<[StarSpecialForm]>,
}

/// Caller must also run the host's native check on the captured invocation.
/// A clear result from either check cannot prove arbitrary callbacks or data.
#[derive(Debug)]
pub struct StarResolvedGraph {
    pub version: String,
    pub profile: StarHostProfile,
    pub root: StarSource,
    pub modules: Box<[StarModule]>,
}

/// The parser or graph could not establish the identity of a checked site.
#[derive(Debug)]
pub enum StarCheck {
    Partial(StarAnalysis),
    Opaque(StarFailure),
}

/// Only source-backed constructor arguments in this primitive slice are proved.
#[derive(Debug)]
pub struct StarAnalysis {
    problems: Box<[StarTypeProblem]>,
    checked_arguments: usize,
    unproved_arguments: usize,
}

impl StarAnalysis {
    pub fn problems(&self) -> &[StarTypeProblem] {
        &self.problems
    }

    /// Keyword arguments of recognized imported record calls with known
    /// primitive fields and literal argument kinds, including mismatches.
    pub fn checked_arguments(&self) -> usize {
        self.checked_arguments
    }

    /// Unproved keyword arguments of those recognized imported record calls.
    /// Other calls, declarations, and deferred bodies are not counted.
    pub fn unproved_arguments(&self) -> usize {
        self.unproved_arguments
    }
}

/// Native `.star` literal kinds justified by a host-parsed source snapshot.
/// Bazel's scalar kind uses Bazel 9 literal grammar and integer limits instead.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum StarPrimitive {
    Int,
    Str,
    Bool,
    None,
}

impl std::fmt::Display for StarPrimitive {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            StarPrimitive::Int => formatter.write_str("int"),
            StarPrimitive::Str => formatter.write_str("str"),
            StarPrimitive::Bool => formatter.write_str("bool"),
            StarPrimitive::None => formatter.write_str("None"),
        }
    }
}

/// The argument owns the primary location; the declared field is secondary.
#[derive(Debug)]
pub struct StarTypeProblem {
    file: File,
    range: TextRange,
    related_file: File,
    related_range: TextRange,
    constructor: String,
    field: String,
    expected: StarPrimitive,
    actual: StarPrimitive,
}

impl StarTypeProblem {
    pub fn file(&self) -> File {
        self.file
    }

    pub fn range(&self) -> TextRange {
        self.range
    }

    pub fn related_file(&self) -> File {
        self.related_file
    }

    pub fn related_range(&self) -> TextRange {
        self.related_range
    }

    pub fn constructor(&self) -> &str {
        &self.constructor
    }

    pub fn field(&self) -> &str {
        &self.field
    }

    pub fn expected(&self) -> StarPrimitive {
        self.expected
    }

    pub fn actual(&self) -> StarPrimitive {
        self.actual
    }
}

impl std::fmt::Display for StarTypeProblem {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            formatter,
            "{}.{}, expected {}, got {}",
            self.constructor, self.field, self.expected, self.actual
        )
    }
}

#[derive(Debug)]
pub struct StarFailure {
    file: File,
    range: Option<TextRange>,
    reason: StarFailureReason,
}

impl StarFailure {
    pub fn file(&self) -> File {
        self.file
    }

    pub fn range(&self) -> Option<TextRange> {
        self.range
    }

    pub fn reason(&self) -> &StarFailureReason {
        &self.reason
    }

    fn at(file: File, range: Option<TextRange>, reason: StarFailureReason) -> Self {
        Self {
            file,
            range,
            reason,
        }
    }
}

#[derive(Debug, thiserror::Error)]
pub enum StarFailureReason {
    #[error("the host graph has an unsupported version or special-form profile")]
    Profile,
    #[error("the host graph contains duplicate logical module IDs")]
    DuplicateModule,
    #[error("the host graph assigns conflicting source snapshots to one file")]
    ConflictingSnapshot,
    #[error("the host graph references an unresolved module")]
    UnresolvedModule,
    #[error("the host graph contains a cycle of Starlark loads")]
    LoadCycle,
    #[error("a parsed Starlark load differs from the captured host load graph")]
    LoadMismatch,
    #[error("a load requests a private Starlark binding")]
    PrivateImport,
    #[error("the shared Python parser cannot check this Starlark source: {0}")]
    Parser(ParseError),
    #[error("the shared Python parser cannot check this Starlark source: {0}")]
    PythonVersion(UnsupportedSyntaxError),
    #[error("the shared parser returned a non-module source")]
    NonModule,
}

#[derive(Debug)]
struct ParsedStarSource<'source> {
    source: &'source StarSource,
    parsed: Parsed<ModModule>,
    writes: HashMap<String, usize>,
    loaded_names: HashSet<String>,
}

impl ParsedStarSource<'_> {
    fn suite(&self) -> &[Stmt] {
        self.parsed.suite()
    }

    fn is_host_global(&self, name: &str) -> bool {
        !self.writes.contains_key(name) && !self.loaded_names.contains(name)
    }
}

#[derive(Clone, Debug)]
struct StarField {
    scalar: StarPrimitive,
    range: TextRange,
}

#[derive(Clone, Debug)]
struct StarConstructor {
    file: File,
    fields: HashMap<String, StarField>,
}

const GRAPH_VERSION: &str = "sty-star-graph-v1";

#[derive(Clone, Copy)]
enum RecordForm {
    Builtin,
    WithValidator,
}

/// Check a host-resolved snapshot without parsing `.star` as Bazel `.bzl`.
///
/// The host's actual parser, loader, and native checker are separate required
/// checks. Unknown expressions and unmodeled statements provide no precision;
/// `Partial` therefore never means the entire module has been type-proved.
pub fn check_star_graph(graph: &StarResolvedGraph) -> StarCheck {
    let StarResolvedGraph {
        version,
        profile,
        root,
        modules,
    } = graph;
    if version != GRAPH_VERSION {
        return StarCheck::Opaque(StarFailure::at(root.file, None, StarFailureReason::Profile));
    }
    let Some(forms) = supported_forms(profile) else {
        return StarCheck::Opaque(StarFailure::at(root.file, None, StarFailureReason::Profile));
    };

    // A physical File identifies one captured source for owning spans. The
    // same path may be exposed by multiple logical module IDs, but differing
    // snapshots would make the later source location ambiguous.
    let mut snapshots: HashMap<File, &str> = HashMap::new();
    for source in std::iter::once(root).chain(modules.iter().map(|module| &module.source)) {
        match snapshots.entry(source.file) {
            Entry::Occupied(entry) => {
                if *entry.get() != source.text.as_str() {
                    return StarCheck::Opaque(StarFailure::at(
                        source.file,
                        None,
                        StarFailureReason::ConflictingSnapshot,
                    ));
                }
            }
            Entry::Vacant(entry) => {
                entry.insert(source.text.as_str());
            }
        }
    }

    let mut by_id = HashMap::new();
    for (index, module) in modules.iter().enumerate() {
        let StarModule { id, source } = module;
        match by_id.entry(id.as_str()) {
            Entry::Occupied(_) => {
                return StarCheck::Opaque(StarFailure::at(
                    source.file,
                    None,
                    StarFailureReason::DuplicateModule,
                ));
            }
            Entry::Vacant(entry) => {
                entry.insert(index);
            }
        }
    }

    let parsed_root = match parse_star_source(root) {
        Ok(parsed) => parsed,
        Err(failure) => return StarCheck::Opaque(failure),
    };
    let mut parsed_modules = Vec::with_capacity(modules.len());
    for module in modules {
        let parsed = match parse_star_source(&module.source) {
            Ok(parsed) => parsed,
            Err(failure) => return StarCheck::Opaque(failure),
        };
        parsed_modules.push(parsed);
    }
    for parsed in std::iter::once(&parsed_root).chain(&parsed_modules) {
        for load in &parsed.source.loads {
            if !by_id.contains_key(load.module_id.as_str()) {
                return StarCheck::Opaque(StarFailure::at(
                    parsed.source.file,
                    Some(load.label_range),
                    StarFailureReason::UnresolvedModule,
                ));
            }
            if load
                .bindings
                .iter()
                .any(|binding| binding.source.starts_with('_'))
            {
                return StarCheck::Opaque(StarFailure::at(
                    parsed.source.file,
                    Some(load.label_range),
                    StarFailureReason::PrivateImport,
                ));
            }
        }
    }
    if let Err(failure) = validate_load_dag(modules, &by_id) {
        return StarCheck::Opaque(failure);
    }

    let constructors: Vec<_> = parsed_modules
        .iter()
        .map(|parsed| source_constructors(parsed, &forms))
        .collect();
    let mut problems = Vec::new();
    let mut checked_arguments = 0;
    let mut unproved_arguments = 0;
    for parsed in parsed_modules.iter().chain(std::iter::once(&parsed_root)) {
        // Every source sees only constructors from modules its own verified
        // direct loads selected. Root-local declarations need source-order
        // initialization and remain unproved in this first slice.
        let visible = match imported_constructors(parsed, &constructors, &by_id) {
            Ok(visible) => visible,
            Err(failure) => return StarCheck::Opaque(failure),
        };
        let mut scanner = CallScanner {
            file: parsed.source.file,
            visible: &visible,
            problems: Vec::new(),
            checked_arguments: 0,
            unproved_arguments: 0,
        };
        scanner.visit_body(parsed.suite());
        problems.extend(scanner.problems);
        checked_arguments += scanner.checked_arguments;
        unproved_arguments += scanner.unproved_arguments;
    }
    StarCheck::Partial(StarAnalysis {
        problems: problems.into_boxed_slice(),
        checked_arguments,
        unproved_arguments,
    })
}

fn imported_constructors(
    parsed: &ParsedStarSource<'_>,
    constructors: &[HashMap<String, StarConstructor>],
    by_id: &HashMap<&str, usize>,
) -> Result<HashMap<String, StarConstructor>, StarFailure> {
    let mut visible = HashMap::new();
    for load in &parsed.source.loads {
        let Some(&index) = by_id.get(load.module_id.as_str()) else {
            return Err(StarFailure::at(
                parsed.source.file,
                Some(load.label_range),
                StarFailureReason::UnresolvedModule,
            ));
        };
        for binding in &load.bindings {
            let StarLoadBinding { local, source } = binding;
            // A shadowed file-block alias cannot retain the imported type.
            if parsed.writes.contains_key(local) {
                visible.remove(local);
            } else if let Some(constructor) = constructors[index].get(source) {
                visible.insert(local.clone(), constructor.clone());
            }
        }
    }
    Ok(visible)
}

fn validate_load_dag(
    modules: &[StarModule],
    by_id: &HashMap<&str, usize>,
) -> Result<(), StarFailure> {
    let mut dependencies = vec![0usize; modules.len()];
    let mut dependents = vec![Vec::new(); modules.len()];
    for (index, module) in modules.iter().enumerate() {
        for load in &module.source.loads {
            let Some(&target) = by_id.get(load.module_id.as_str()) else {
                return Err(StarFailure::at(
                    module.source.file,
                    Some(load.label_range),
                    StarFailureReason::UnresolvedModule,
                ));
            };
            dependencies[index] += 1;
            dependents[target].push(index);
        }
    }
    let mut ready: Vec<_> = dependencies
        .iter()
        .enumerate()
        .filter_map(|(index, count)| (*count == 0).then_some(index))
        .collect();
    let mut peeled = 0;
    while let Some(target) = ready.pop() {
        peeled += 1;
        for &importer in &dependents[target] {
            dependencies[importer] -= 1;
            if dependencies[importer] == 0 {
                ready.push(importer);
            }
        }
    }
    if peeled != modules.len() {
        let Some((index, _)) = dependencies
            .iter()
            .enumerate()
            .find(|(_, count)| **count > 0)
        else {
            return Ok(());
        };
        let source = &modules[index].source;
        return Err(StarFailure::at(
            source.file,
            source.loads.first().map(|load| load.label_range),
            StarFailureReason::LoadCycle,
        ));
    }
    Ok(())
}

fn supported_forms(profile: &StarHostProfile) -> Option<HashMap<&str, RecordForm>> {
    let StarHostProfile {
        name,
        special_forms,
    } = profile;
    if name.is_empty() || special_forms.is_empty() {
        return None;
    }
    let mut forms = HashMap::new();
    for form in special_forms {
        let StarSpecialForm {
            name,
            kind,
            validator,
            field_types,
        } = form;
        if name.is_empty() || field_types != "named_keyword_type_expressions" {
            return None;
        }
        let semantic = match (kind.as_str(), validator.as_str()) {
            ("builtin_record", "none") => RecordForm::Builtin,
            ("record_with_validator", "first_positional_callable") => RecordForm::WithValidator,
            _ => return None,
        };
        match forms.entry(name.as_str()) {
            Entry::Occupied(_) => return None,
            Entry::Vacant(entry) => {
                entry.insert(semantic);
            }
        }
    }
    Some(forms)
}

fn parse_star_source(source: &StarSource) -> Result<ParsedStarSource<'_>, StarFailure> {
    let StarSource { file, text, loads } = source;
    // The host profile enables type syntax and top-level statements. Ruff's
    // fixed shared parser admits only their overlapping syntax, never Python
    // project configuration or the Bazel source admission profile.
    let options = ParseOptions::from(Mode::Module).with_target_version(PythonVersion::PY310);
    let parsed = parse_unchecked(text, options);
    let Some(parsed) = parsed.try_into_module() else {
        return Err(StarFailure::at(*file, None, StarFailureReason::NonModule));
    };
    let parser_error = parsed
        .errors()
        .iter()
        .min_by_key(|error| error.range().start());
    let version_error = parsed
        .unsupported_syntax_errors()
        .iter()
        .min_by_key(|error| error.range().start());
    if let Some(error) = parser_error
        && version_error.is_none_or(|other| error.range().start() <= other.range().start())
    {
        return Err(StarFailure::at(
            *file,
            Some(error.range()),
            StarFailureReason::Parser(error.clone()),
        ));
    }
    if let Some(error) = version_error {
        return Err(StarFailure::at(
            *file,
            Some(error.range()),
            StarFailureReason::PythonVersion(error.clone()),
        ));
    }
    validate_direct_loads(*file, parsed.suite(), loads)?;
    let mut aliases = HashSet::new();
    for load in loads {
        for binding in &load.bindings {
            if !aliases.insert(binding.local.as_str()) {
                return Err(StarFailure::at(
                    *file,
                    Some(load.label_range),
                    StarFailureReason::LoadMismatch,
                ));
            }
        }
    }
    let mut written = ModuleWrites::default();
    written.visit_body(parsed.suite());
    let loaded_names = aliases.into_iter().map(str::to_string).collect();
    Ok(ParsedStarSource {
        source,
        parsed,
        writes: written.names,
        loaded_names,
    })
}

fn validate_direct_loads(
    file: File,
    suite: &[Stmt],
    declared: &[StarDirectLoad],
) -> Result<(), StarFailure> {
    let mut observed = Vec::new();
    for statement in suite {
        let Stmt::Expr(expr_stmt) = statement else {
            continue;
        };
        let Expr::Call(call) = expr_stmt.value.as_ref() else {
            continue;
        };
        let Expr::Name(callee) = call.func.as_ref() else {
            continue;
        };
        if callee.id != "load" {
            continue;
        }
        let Some(Expr::StringLiteral(module)) = call.arguments.args.first() else {
            return Err(StarFailure::at(
                file,
                Some(call.range()),
                StarFailureReason::LoadMismatch,
            ));
        };
        let mut bindings = Vec::new();
        for binding in call.arguments.iter_source_order().skip(1) {
            let (source, local) = match binding {
                ast::ArgOrKeyword::Arg(Expr::StringLiteral(name)) => {
                    (name.value.to_str(), name.value.to_str())
                }
                ast::ArgOrKeyword::Keyword(keyword) => {
                    let Expr::StringLiteral(name) = &keyword.value else {
                        return Err(StarFailure::at(
                            file,
                            Some(keyword.range()),
                            StarFailureReason::LoadMismatch,
                        ));
                    };
                    let Some(alias) = &keyword.arg else {
                        return Err(StarFailure::at(
                            file,
                            Some(keyword.range()),
                            StarFailureReason::LoadMismatch,
                        ));
                    };
                    (name.value.to_str(), alias.as_str())
                }
                ast::ArgOrKeyword::Arg(other) => {
                    return Err(StarFailure::at(
                        file,
                        Some(other.range()),
                        StarFailureReason::LoadMismatch,
                    ));
                }
            };
            bindings.push((local.to_string(), source.to_string()));
        }
        observed.push((module.value.to_str().to_string(), module.range(), bindings));
    }
    if observed.len() != declared.len() {
        return Err(StarFailure::at(file, None, StarFailureReason::LoadMismatch));
    }
    for ((module_id, range, bindings), load) in observed.iter().zip(declared) {
        let StarDirectLoad {
            module_id: declared_id,
            label_range,
            bindings: declared_bindings,
        } = load;
        if module_id != declared_id
            || range != label_range
            || bindings.len() != declared_bindings.len()
            || bindings
                .iter()
                .zip(declared_bindings)
                .any(|((local, source), declared)| {
                    local != &declared.local || source != &declared.source
                })
        {
            return Err(StarFailure::at(
                file,
                Some(*label_range),
                StarFailureReason::LoadMismatch,
            ));
        }
    }
    Ok(())
}

#[derive(Default)]
struct ModuleWrites {
    names: HashMap<String, usize>,
}

impl ModuleWrites {
    fn write(&mut self, name: &str) {
        *self.names.entry(name.to_string()).or_default() += 1;
    }
}

impl<'source> Visitor<'source> for ModuleWrites {
    fn visit_stmt(&mut self, statement: &'source Stmt) {
        match statement {
            Stmt::FunctionDef(function) => self.write(function.name.as_str()),
            Stmt::ClassDef(class) => self.write(class.name.as_str()),
            _ => ast::visitor::walk_stmt(self, statement),
        }
    }

    fn visit_expr(&mut self, expression: &'source Expr) {
        if let Expr::Name(name) = expression
            && name.ctx == ast::ExprContext::Store
        {
            self.write(name.id.as_str());
        }
        ast::visitor::walk_expr(self, expression);
    }
}

fn source_constructors(
    parsed: &ParsedStarSource<'_>,
    forms: &HashMap<&str, RecordForm>,
) -> HashMap<String, StarConstructor> {
    let mut constructors = HashMap::new();
    let mut preceding_callables = HashSet::new();
    for statement in parsed.suite() {
        let assign = match statement {
            Stmt::FunctionDef(function) => {
                let name = function.name.as_str();
                if function.decorator_list.is_empty()
                    && parsed.writes.get(name) == Some(&1)
                    && !parsed.loaded_names.contains(name)
                {
                    preceding_callables.insert(name);
                }
                continue;
            }
            Stmt::Assign(assign) => assign,
            _ => continue,
        };
        let [Expr::Name(target)] = assign.targets.as_slice() else {
            continue;
        };
        if parsed.writes.get(target.id.as_str()) != Some(&1)
            || parsed.loaded_names.contains(target.id.as_str())
        {
            continue;
        }
        let Expr::Call(call) = assign.value.as_ref() else {
            continue;
        };
        let Expr::Name(callee) = call.func.as_ref() else {
            continue;
        };
        if !parsed.is_host_global(callee.id.as_str()) {
            continue;
        }
        let expected_args = match forms.get(callee.id.as_str()) {
            Some(RecordForm::Builtin) => 0,
            Some(RecordForm::WithValidator) => 1,
            None => continue,
        };
        if call.arguments.args.len() != expected_args
            || call.arguments.args.iter().any(Expr::is_starred_expr)
            || call
                .arguments
                .keywords
                .iter()
                .any(|keyword| keyword.arg.is_none())
        {
            continue;
        }
        if expected_args == 1 {
            let [Expr::Name(validator)] = call.arguments.args.as_ref() else {
                continue;
            };
            if !preceding_callables.contains(validator.id.as_str()) {
                continue;
            }
        }
        let mut fields = HashMap::new();
        let mut safe = true;
        for keyword in &call.arguments.keywords {
            let Some(name) = keyword.arg.as_ref() else {
                safe = false;
                break;
            };
            let Expr::Name(annotation) = &keyword.value else {
                safe = false;
                break;
            };
            let scalar = match annotation.id.as_str() {
                "int" => parsed.is_host_global("int").then_some(StarPrimitive::Int),
                "str" => parsed.is_host_global("str").then_some(StarPrimitive::Str),
                "bool" => parsed.is_host_global("bool").then_some(StarPrimitive::Bool),
                _ => None,
            };
            let Some(scalar) = scalar else {
                safe = false;
                break;
            };
            match fields.entry(name.as_str().to_string()) {
                Entry::Occupied(_) => {
                    safe = false;
                    break;
                }
                Entry::Vacant(entry) => {
                    entry.insert(StarField {
                        scalar,
                        range: annotation.range(),
                    });
                }
            }
        }
        if safe {
            constructors.insert(
                target.id.as_str().to_string(),
                StarConstructor {
                    file: parsed.source.file,
                    fields,
                },
            );
        }
    }
    constructors
}

struct CallScanner<'types> {
    file: File,
    visible: &'types HashMap<String, StarConstructor>,
    problems: Vec<StarTypeProblem>,
    checked_arguments: usize,
    unproved_arguments: usize,
}

impl<'source> Visitor<'source> for CallScanner<'_> {
    fn visit_stmt(&mut self, statement: &'source Stmt) {
        match statement {
            // This first slice scans eager top-level code and every top-level
            // `if` arm, including dead branches. Function locals and closure
            // values need a separate lexical context before trusting names.
            Stmt::FunctionDef(_) => {}
            Stmt::ClassDef(_) => {}
            _ => ast::visitor::walk_stmt(self, statement),
        }
    }

    fn visit_expr(&mut self, expression: &'source Expr) {
        // These bodies bind their own names or run later. Without their
        // lexical environment, the imported alias may refer to a parameter
        // or comprehension iterator instead of the loaded constructor.
        match expression {
            Expr::Lambda(_) => return,
            Expr::ListComp(_) => return,
            Expr::SetComp(_) => return,
            Expr::DictComp(_) => return,
            Expr::Generator(_) => return,
            _ => {}
        }
        if let Expr::Call(call) = expression
            && let Expr::Name(name) = call.func.as_ref()
            && let Some(constructor) = self.visible.get(name.id.as_str())
        {
            for keyword in &call.arguments.keywords {
                let Some(field_name) = &keyword.arg else {
                    self.unproved_arguments += 1;
                    continue;
                };
                let Some(field) = constructor.fields.get(field_name.as_str()) else {
                    self.unproved_arguments += 1;
                    continue;
                };
                let Some(actual) = literal_type(&keyword.value) else {
                    self.unproved_arguments += 1;
                    continue;
                };
                self.checked_arguments += 1;
                if actual != field.scalar {
                    self.problems.push(StarTypeProblem {
                        file: self.file,
                        range: keyword.value.range(),
                        related_file: constructor.file,
                        related_range: field.range,
                        constructor: name.id.to_string(),
                        field: field_name.to_string(),
                        expected: field.scalar,
                        actual,
                    });
                }
            }
        }
        ast::visitor::walk_expr(self, expression);
    }
}

fn literal_type(expression: &Expr) -> Option<StarPrimitive> {
    match expression {
        Expr::NumberLiteral(number) => {
            matches!(number.value, Number::Int(_)).then_some(StarPrimitive::Int)
        }
        Expr::StringLiteral(_) => Some(StarPrimitive::Str),
        Expr::BooleanLiteral(_) => Some(StarPrimitive::Bool),
        Expr::NoneLiteral(_) => Some(StarPrimitive::None),
        _ => None,
    }
}

#[cfg(test)]
mod tests;
