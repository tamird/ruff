//! A bounded static source check for host-owned typed `.star` graphs.
//!
//! The host captures exact source text and resolves direct loads with its
//! parser. This pass checks source-declared record fields, annotated source
//! functions, and attested native calls whose types can be established from
//! the graph. Other forms remain unproved; an analyzed graph is never a full
//! type proof.

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

/// Producer-attested semantics of a native Starlark global.
#[derive(Debug)]
pub struct StarIntrinsic {
    pub name: String,
    pub kind: String,
}

#[derive(Debug)]
pub struct StarHostProfile {
    pub name: String,
    pub special_forms: Box<[StarSpecialForm]>,
    pub intrinsics: Box<[StarIntrinsic]>,
    pub host_functions: Box<[StarHostFunction]>,
}

/// Producer-attested native callable signature and its evaluator availability.
#[derive(Debug)]
pub struct StarHostFunction {
    pub name: String,
    pub params: Box<[StarHostParam]>,
    pub returns: String,
    pub availability: String,
}

#[derive(Debug)]
pub struct StarHostParam {
    pub name: String,
    pub mode: String,
    pub required: bool,
    pub ty: String,
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

/// Proves known source fields, source parameters, and attested native parameters.
#[derive(Debug)]
pub struct StarAnalysis {
    problems: Box<[StarTypeProblem]>,
    native_problems: Box<[StarNativeTypeProblem]>,
    native_call_problems: Box<[StarNativeCallProblem]>,
    checked_arguments: usize,
    unproved_arguments: usize,
}

impl StarAnalysis {
    pub fn problems(&self) -> &[StarTypeProblem] {
        &self.problems
    }

    pub fn native_problems(&self) -> &[StarNativeTypeProblem] {
        &self.native_problems
    }

    pub fn native_call_problems(&self) -> &[StarNativeCallProblem] {
        &self.native_call_problems
    }

    /// Known source fields, annotated source parameters, and attested native
    /// parameters, including errors.
    pub fn checked_arguments(&self) -> usize {
        self.checked_arguments
    }

    /// Supplied arguments of recognized calls without established argument
    /// types or a provable parameter mapping. Calls without a recognized
    /// signature and unmodeled closure bodies are not counted.
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

/// A source-backed type, with nominal record identity scoped to an evaluated
/// logical module rather than its physical source file.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum StarKnownType {
    Primitive(StarPrimitive),
    Record(StarRecordId),
    Union(Box<[StarKnownType]>),
    List(Box<StarKnownType>),
    Callable,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct StarRecordId {
    module: StarRecordModule,
    declaration: TextRange,
    name: String,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum StarRecordModule {
    Root,
    Loaded(String),
}

impl std::fmt::Display for StarRecordModule {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Root => formatter.write_str("source root"),
            Self::Loaded(id) => formatter.write_str(id),
        }
    }
}

impl std::fmt::Display for StarKnownType {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Primitive(primitive) => primitive.fmt(formatter),
            Self::Record(record) => formatter.write_str(&record.name),
            Self::Union(alternatives) => {
                for (index, alternative) in alternatives.iter().enumerate() {
                    if index > 0 {
                        formatter.write_str(" | ")?;
                    }
                    alternative.fmt(formatter)?;
                }
                Ok(())
            }
            Self::List(element) => write!(formatter, "list[{element}]"),
            Self::Callable => formatter.write_str("callable"),
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
    kind: StarTypeProblemKind,
    expected: StarKnownType,
    actual: StarKnownType,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum StarTypeProblemKind {
    RecordField,
    FunctionParameter,
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

    /// Secondary annotation label for the declaration owning this type.
    pub fn related_label(&self) -> &'static str {
        match self.kind {
            StarTypeProblemKind::RecordField => "field declared",
            StarTypeProblemKind::FunctionParameter => "parameter annotated",
        }
    }

    pub fn expected(&self) -> &StarKnownType {
        &self.expected
    }

    pub fn actual(&self) -> &StarKnownType {
        &self.actual
    }
}

impl std::fmt::Display for StarTypeProblem {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let subject = match self.kind {
            StarTypeProblemKind::RecordField => format!("{}.{}", self.constructor, self.field),
            StarTypeProblemKind::FunctionParameter => {
                format!("{} parameter {}", self.constructor, self.field)
            }
        };
        if let (StarKnownType::Record(expected), StarKnownType::Record(actual)) =
            (&self.expected, &self.actual)
            && expected.name == actual.name
            && expected != actual
        {
            return write!(
                formatter,
                "{}, expected {} ({}), got {} ({})",
                subject, expected.name, expected.module, actual.name, actual.module
            );
        }
        write!(
            formatter,
            "{}, expected {}, got {}",
            subject, self.expected, self.actual
        )
    }
}

/// A native contract has no source declaration in the captured graph.
#[derive(Debug)]
pub struct StarNativeTypeProblem {
    file: File,
    range: TextRange,
    function: String,
    parameter: String,
    expected: StarKnownType,
    actual: StarKnownType,
    signature: String,
}

impl StarNativeTypeProblem {
    pub fn file(&self) -> File {
        self.file
    }

    pub fn range(&self) -> TextRange {
        self.range
    }

    /// A textual contract from producer-attested parameter facts.
    pub fn signature(&self) -> &str {
        &self.signature
    }
}

impl std::fmt::Display for StarNativeTypeProblem {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            formatter,
            "{} parameter {}, expected {}, got {}",
            self.function, self.parameter, self.expected, self.actual
        )
    }
}

/// A native call's argument mapping contradicts its attested host contract.
#[derive(Debug)]
pub struct StarNativeCallProblem {
    file: File,
    range: TextRange,
    function: String,
    reason: StarNativeCallReason,
    signature: String,
}

impl StarNativeCallProblem {
    pub fn file(&self) -> File {
        self.file
    }

    pub fn range(&self) -> TextRange {
        self.range
    }

    pub fn signature(&self) -> &str {
        &self.signature
    }
}

impl std::fmt::Display for StarNativeCallProblem {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(formatter, "{} {}", self.function, self.reason)
    }
}

#[derive(Debug)]
enum StarNativeCallReason {
    ExcessPositional,
    NamedOnly(String),
    PositionalOnly(String),
    UnknownNamed(String),
    Duplicate(String),
    Missing(String),
}

impl std::fmt::Display for StarNativeCallReason {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::ExcessPositional => formatter.write_str("received too many positional arguments"),
            Self::NamedOnly(name) => {
                write!(formatter, "parameter {name} requires a named argument")
            }
            Self::PositionalOnly(name) => {
                write!(formatter, "parameter {name} requires a positional argument")
            }
            Self::UnknownNamed(name) => write!(formatter, "has no named parameter {name}"),
            Self::Duplicate(name) => write!(formatter, "parameter {name} was passed twice"),
            Self::Missing(name) => write!(formatter, "missing required parameter {name}"),
        }
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
    ty: StarKnownType,
    range: TextRange,
}

#[derive(Clone, Debug)]
struct StarConstructor {
    file: File,
    ty: StarKnownType,
    fields: HashMap<String, StarField>,
}

#[derive(Clone, Debug)]
struct StarFunction {
    file: File,
    parameters: Box<[StarParameter]>,
    returns: Option<StarField>,
}

#[derive(Clone, Debug)]
struct StarParameter {
    name: String,
    annotation: Option<StarField>,
}

#[derive(Clone, Debug)]
enum StarBinding {
    Constructor(StarConstructor),
    Alias(StarKnownType),
    Struct(HashMap<String, StarBinding>),
    Function(StarFunction),
}

impl StarBinding {
    fn annotation_type(&self) -> Option<&StarKnownType> {
        match self {
            Self::Constructor(constructor) => Some(&constructor.ty),
            Self::Alias(ty) => Some(ty),
            Self::Struct(_) => None,
            Self::Function(_) => None,
        }
    }
}

const GRAPH_VERSION_V1: &str = "sty-star-graph-v1";
const GRAPH_VERSION_V2: &str = "sty-star-graph-v2";
const GRAPH_VERSION_V3: &str = "sty-star-graph-v3";

#[derive(Clone, Copy)]
enum RecordForm {
    Builtin,
    WithValidator,
}

struct StarSupportedForms<'profile> {
    record_forms: HashMap<&'profile str, RecordForm>,
    host_functions: HashMap<&'profile str, &'profile StarHostFunction>,
    field_attested: bool,
    struct_attested: bool,
    source_functions: bool,
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
    let Some(forms) = supported_forms(version, profile) else {
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
    let dependency_order = match validate_load_dag(modules, &by_id) {
        Ok(order) => order,
        Err(failure) => return StarCheck::Opaque(failure),
    };

    // A loaded module is initialized once under its logical load spelling.
    // Build its exports only after the exports of its verified dependencies.
    let mut exports = vec![HashMap::new(); modules.len()];
    for index in dependency_order {
        let parsed = &parsed_modules[index];
        let imported = match imported_bindings(parsed, &exports, &by_id) {
            Ok(imported) => imported,
            Err(failure) => return StarCheck::Opaque(failure),
        };
        exports[index] = source_bindings(
            parsed,
            &StarRecordModule::Loaded(modules[index].id.clone()),
            &forms,
            imported,
        );
    }
    let root_imports = match imported_bindings(&parsed_root, &exports, &by_id) {
        Ok(imported) => imported,
        Err(failure) => return StarCheck::Opaque(failure),
    };
    let root_exports = source_bindings(&parsed_root, &StarRecordModule::Root, &forms, root_imports);
    let mut problems = Vec::new();
    let mut native_problems = Vec::new();
    let mut native_call_problems = Vec::new();
    let mut checked_arguments = 0;
    let mut unproved_arguments = 0;
    for (parsed, declarations, loaded_module) in parsed_modules
        .iter()
        .zip(&exports)
        .map(|(parsed, declarations)| (parsed, declarations, true))
        .chain(std::iter::once((&parsed_root, &root_exports, false)))
    {
        let visible = match imported_bindings(parsed, &exports, &by_id) {
            Ok(visible) => visible,
            Err(failure) => return StarCheck::Opaque(failure),
        };
        let mut scanner = CallScanner {
            file: parsed.source.file,
            visible,
            declarations,
            writes: &parsed.writes,
            loaded_names: &parsed.loaded_names,
            host_functions: &forms.host_functions,
            local_names: HashSet::new(),
            loaded_module,
            deferred: false,
            problems: Vec::new(),
            native_problems: Vec::new(),
            native_call_problems: Vec::new(),
            checked_arguments: 0,
            unproved_arguments: 0,
        };
        scanner.visit_body(parsed.suite());
        if forms.source_functions {
            scanner.scan_deferred_bodies(parsed.suite());
        }
        problems.extend(scanner.problems);
        native_problems.extend(scanner.native_problems);
        native_call_problems.extend(scanner.native_call_problems);
        checked_arguments += scanner.checked_arguments;
        unproved_arguments += scanner.unproved_arguments;
    }
    StarCheck::Partial(StarAnalysis {
        problems: problems.into_boxed_slice(),
        native_problems: native_problems.into_boxed_slice(),
        native_call_problems: native_call_problems.into_boxed_slice(),
        checked_arguments,
        unproved_arguments,
    })
}

fn imported_bindings(
    parsed: &ParsedStarSource<'_>,
    exports: &[HashMap<String, StarBinding>],
    by_id: &HashMap<&str, usize>,
) -> Result<HashMap<String, StarBinding>, StarFailure> {
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
            } else if let Some(value) = exports[index].get(source) {
                visible.insert(local.clone(), value.clone());
            }
        }
    }
    Ok(visible)
}

fn validate_load_dag(
    modules: &[StarModule],
    by_id: &HashMap<&str, usize>,
) -> Result<Vec<usize>, StarFailure> {
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
    let mut order = Vec::with_capacity(modules.len());
    while let Some(target) = ready.pop() {
        order.push(target);
        for &importer in &dependents[target] {
            dependencies[importer] -= 1;
            if dependencies[importer] == 0 {
                ready.push(importer);
            }
        }
    }
    if order.len() != modules.len() {
        let Some((index, _)) = dependencies
            .iter()
            .enumerate()
            .find(|(_, count)| **count > 0)
        else {
            return Ok(order);
        };
        let source = &modules[index].source;
        return Err(StarFailure::at(
            source.file,
            source.loads.first().map(|load| load.label_range),
            StarFailureReason::LoadCycle,
        ));
    }
    Ok(order)
}

fn supported_forms<'profile>(
    version: &str,
    profile: &'profile StarHostProfile,
) -> Option<StarSupportedForms<'profile>> {
    let StarHostProfile {
        name,
        special_forms,
        intrinsics,
        host_functions,
    } = profile;
    match version {
        GRAPH_VERSION_V1 => {
            if !intrinsics.is_empty() || !host_functions.is_empty() {
                return None;
            }
        }
        GRAPH_VERSION_V2 | GRAPH_VERSION_V3 => {
            if version == GRAPH_VERSION_V2 && !host_functions.is_empty() {
                return None;
            }
            if intrinsics.len() != 2 {
                return None;
            }
            let mut found = HashSet::new();
            for intrinsic in intrinsics {
                let StarIntrinsic { name, kind } = intrinsic;
                if !matches!(
                    (name.as_str(), kind.as_str()),
                    ("field", "field_first_type_optional_default")
                        | ("struct", "struct_named_members")
                ) || !found.insert(name.as_str())
                {
                    return None;
                }
            }
        }
        _ => return None,
    }
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
    if version == GRAPH_VERSION_V3 && !supported_host_functions(host_functions, &forms) {
        return None;
    }
    Some(StarSupportedForms {
        record_forms: forms,
        host_functions: host_functions
            .iter()
            .map(|function| (function.name.as_str(), function))
            .collect(),
        field_attested: version != GRAPH_VERSION_V1,
        struct_attested: version != GRAPH_VERSION_V1,
        source_functions: version != GRAPH_VERSION_V1,
    })
}

fn supported_host_functions(
    functions: &[StarHostFunction],
    forms: &HashMap<&str, RecordForm>,
) -> bool {
    let mut names = HashSet::new();
    for function in functions {
        let StarHostFunction {
            name,
            params,
            returns,
            availability,
        } = function;
        if name.is_empty()
            || forms.contains_key(name.as_str())
            || matches!(name.as_str(), "field" | "struct")
            || !names.insert(name.as_str())
            || !supported_host_type(returns)
            || !matches!(
                availability.as_str(),
                "any_module" | "loaded_module_initialization"
            )
        {
            return false;
        }
        let mut parameters = HashSet::new();
        let mut previous_mode = 0;
        let mut optional_positional = false;
        for param in params {
            let StarHostParam {
                name,
                mode,
                required,
                ty,
            } = param;
            let mode = match mode.as_str() {
                "pos_only" => 0,
                "pos_or_named" => 1,
                "named_only" => 2,
                _ => return false,
            };
            if name.is_empty()
                || !parameters.insert(name.as_str())
                || mode < previous_mode
                || !supported_host_type(ty)
                || mode != 2 && optional_positional && *required
            {
                return false;
            }
            if mode != 2 && !*required {
                optional_positional = true;
            }
            previous_mode = mode;
        }
    }
    true
}

fn supported_host_type(ty: &str) -> bool {
    matches!(ty, "any" | "bool" | "int" | "str" | "callable" | "unknown")
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

fn source_bindings(
    parsed: &ParsedStarSource<'_>,
    module: &StarRecordModule,
    forms: &StarSupportedForms<'_>,
    mut visible: HashMap<String, StarBinding>,
) -> HashMap<String, StarBinding> {
    let mut preceding_callables = HashSet::new();
    let mut exports = HashMap::new();
    for statement in parsed.suite() {
        let assign = match statement {
            Stmt::FunctionDef(function) => {
                let name = function.name.as_str();
                if function.decorator_list.is_empty()
                    && parsed.writes.get(name) == Some(&1)
                    && !parsed.loaded_names.contains(name)
                {
                    preceding_callables.insert(name);
                    if forms.source_functions
                        && let Some(function) = function_declaration(parsed, function, &visible)
                    {
                        let binding = StarBinding::Function(function);
                        visible.insert(name.to_string(), binding.clone());
                        exports.insert(name.to_string(), binding);
                    }
                }
                continue;
            }
            Stmt::Assign(assign) => assign,
            _ => continue,
        };
        let [Expr::Name(target)] = assign.targets.as_slice() else {
            continue;
        };
        // Shadowing a native type name must not establish a replacement host
        // global from this bounded source summary.
        let name = target.id.as_str();
        if parsed.writes.get(name) != Some(&1)
            || parsed.loaded_names.contains(name)
            || matches!(name, "int" | "str" | "bool" | "list")
        {
            continue;
        }
        let declaration = match assign.value.as_ref() {
            Expr::Call(call) => record_declaration(
                parsed,
                module,
                name,
                call,
                forms,
                &visible,
                &preceding_callables,
            )
            .map(StarBinding::Constructor)
            .or_else(|| struct_declaration(parsed, call, forms, &visible)),
            Expr::Name(_) | Expr::Attribute(_) => binding_in_scope(&assign.value, &visible)
                .cloned()
                .or_else(|| {
                    type_expression(parsed, &visible, &assign.value).map(StarBinding::Alias)
                }),
            expression => type_expression(parsed, &visible, expression).map(StarBinding::Alias),
        };
        if let Some(declaration) = declaration {
            visible.insert(name.to_string(), declaration.clone());
            exports.insert(name.to_string(), declaration);
        }
    }
    // v1 does not attest whether load aliases themselves are reexported.
    // Explicit declarations can retain an imported type's identity.
    exports
}

fn struct_declaration(
    parsed: &ParsedStarSource<'_>,
    call: &ast::ExprCall,
    forms: &StarSupportedForms<'_>,
    visible: &HashMap<String, StarBinding>,
) -> Option<StarBinding> {
    let StarSupportedForms {
        record_forms: _,
        host_functions: _,
        field_attested: _,
        struct_attested,
        source_functions: _,
    } = forms;
    if !struct_attested || !parsed.is_host_global("struct") {
        return None;
    }
    let Expr::Name(callee) = call.func.as_ref() else {
        return None;
    };
    if callee.id != "struct" || !call.arguments.args.is_empty() {
        return None;
    }
    let mut members = HashMap::new();
    let mut seen = HashSet::new();
    for keyword in &call.arguments.keywords {
        let name = keyword.arg.as_ref()?;
        if !seen.insert(name.as_str()) {
            return None;
        }
        let binding = binding_in_scope(&keyword.value, visible)
            .cloned()
            .or_else(|| type_expression(parsed, visible, &keyword.value).map(StarBinding::Alias));
        if let Some(binding) = binding {
            members.insert(name.as_str().to_string(), binding);
        }
    }
    Some(StarBinding::Struct(members))
}

fn function_declaration(
    parsed: &ParsedStarSource<'_>,
    function: &ast::StmtFunctionDef,
    visible: &HashMap<String, StarBinding>,
) -> Option<StarFunction> {
    let parameters = &function.parameters;
    if function.is_async
        || function.type_params.is_some()
        || !parameters.posonlyargs.is_empty()
        || parameters.vararg.is_some()
        || !parameters.kwonlyargs.is_empty()
        || parameters.kwarg.is_some()
    {
        return None;
    }
    let mut parsed_parameters = Vec::with_capacity(parameters.args.len());
    let mut seen = HashSet::new();
    for parameter in &parameters.args {
        let name = parameter.name().as_str();
        if !seen.insert(name) {
            return None;
        }
        let annotation = parameter.annotation().and_then(|expression| {
            let ty = type_expression(parsed, visible, expression)?;
            Some(StarField {
                ty,
                range: expression.range(),
            })
        });
        parsed_parameters.push(StarParameter {
            name: name.to_string(),
            annotation,
        });
    }
    let returns = function.returns.as_deref().and_then(|expression| {
        let ty = type_expression(parsed, visible, expression)?;
        Some(StarField {
            ty,
            range: expression.range(),
        })
    });
    Some(StarFunction {
        file: parsed.source.file,
        parameters: parsed_parameters.into_boxed_slice(),
        returns,
    })
}

fn binding_in_scope<'scope>(
    expression: &Expr,
    visible: &'scope HashMap<String, StarBinding>,
) -> Option<&'scope StarBinding> {
    match expression {
        Expr::Name(name) => visible.get(name.id.as_str()),
        Expr::Attribute(attribute) => {
            let parent = binding_in_scope(&attribute.value, visible)?;
            let StarBinding::Struct(members) = parent else {
                return None;
            };
            members.get(attribute.attr.as_str())
        }
        _ => None,
    }
}

fn binding_name(expression: &Expr) -> Option<String> {
    match expression {
        Expr::Name(name) => Some(name.id.to_string()),
        Expr::Attribute(attribute) => {
            let parent = binding_name(&attribute.value)?;
            Some(format!("{parent}.{}", attribute.attr))
        }
        _ => None,
    }
}

fn record_declaration(
    parsed: &ParsedStarSource<'_>,
    module: &StarRecordModule,
    name: &str,
    call: &ast::ExprCall,
    forms: &StarSupportedForms<'_>,
    visible: &HashMap<String, StarBinding>,
    preceding_callables: &HashSet<&str>,
) -> Option<StarConstructor> {
    let StarSupportedForms {
        record_forms,
        host_functions: _,
        field_attested,
        struct_attested: _,
        source_functions: _,
    } = forms;
    let Expr::Name(callee) = call.func.as_ref() else {
        return None;
    };
    if !parsed.is_host_global(callee.id.as_str()) {
        return None;
    }
    let expected_args = match record_forms.get(callee.id.as_str()) {
        Some(RecordForm::Builtin) => 0,
        Some(RecordForm::WithValidator) => 1,
        None => return None,
    };
    if call.arguments.args.len() != expected_args
        || call.arguments.args.iter().any(Expr::is_starred_expr)
        || call
            .arguments
            .keywords
            .iter()
            .any(|keyword| keyword.arg.is_none())
    {
        return None;
    }
    if expected_args == 1 {
        let [Expr::Name(validator)] = call.arguments.args.as_ref() else {
            return None;
        };
        if !preceding_callables.contains(validator.id.as_str()) {
            return None;
        }
    }
    let mut fields = HashMap::new();
    let mut seen_fields = HashSet::new();
    for keyword in &call.arguments.keywords {
        let name = keyword.arg.as_ref()?;
        if !seen_fields.insert(name.as_str()) {
            return None;
        }
        let (ty, range) = match type_expression(parsed, visible, &keyword.value) {
            Some(ty) => (ty, keyword.value.range()),
            None => {
                if !field_attested {
                    continue;
                }
                let Some(field) = intrinsic_field_type(parsed, visible, &keyword.value) else {
                    continue;
                };
                field
            }
        };
        fields.insert(name.as_str().to_string(), StarField { ty, range });
    }
    Some(StarConstructor {
        file: parsed.source.file,
        ty: StarKnownType::Record(StarRecordId {
            module: module.clone(),
            declaration: call.range(),
            name: name.to_string(),
        }),
        fields,
    })
}

fn intrinsic_field_type(
    parsed: &ParsedStarSource<'_>,
    visible: &HashMap<String, StarBinding>,
    expression: &Expr,
) -> Option<(StarKnownType, TextRange)> {
    let Expr::Call(call) = expression else {
        return None;
    };
    let Expr::Name(callee) = call.func.as_ref() else {
        return None;
    };
    if callee.id != "field" || !parsed.is_host_global("field") {
        return None;
    }
    if call.arguments.args.iter().any(Expr::is_starred_expr) {
        return None;
    }
    let (annotation, positional_default) = match call.arguments.args.as_ref() {
        [annotation] => (annotation, false),
        [annotation, _default] => (annotation, true),
        _ => return None,
    };
    let named_default = match call.arguments.keywords.as_ref() {
        [] => false,
        [keyword] => {
            let name = keyword.arg.as_ref()?;
            if name.as_str() != "default" {
                return None;
            }
            true
        }
        _ => return None,
    };
    if positional_default && named_default {
        return None;
    }
    // Native field compiles this type and checks any supplied default.
    // The default's value and requiredness remain the host's responsibility.
    let ty = type_expression(parsed, visible, annotation)?;
    Some((ty, annotation.range()))
}

fn type_expression(
    parsed: &ParsedStarSource<'_>,
    visible: &HashMap<String, StarBinding>,
    expression: &Expr,
) -> Option<StarKnownType> {
    match expression {
        Expr::Name(name) => {
            let name = name.id.as_str();
            if let Some(binding) = visible.get(name) {
                return binding.annotation_type().cloned();
            }
            if !parsed.is_host_global(name) {
                return None;
            }
            let primitive = match name {
                "int" => StarPrimitive::Int,
                "str" => StarPrimitive::Str,
                "bool" => StarPrimitive::Bool,
                _ => return None,
            };
            Some(StarKnownType::Primitive(primitive))
        }
        Expr::NoneLiteral(_) => Some(StarKnownType::Primitive(StarPrimitive::None)),
        Expr::BinOp(binary) => {
            if binary.op != ast::Operator::BitOr {
                return None;
            }
            let left = type_expression(parsed, visible, &binary.left)?;
            let right = type_expression(parsed, visible, &binary.right)?;
            Some(type_union(left, [right]))
        }
        Expr::Subscript(subscript) => {
            let Expr::Name(name) = subscript.value.as_ref() else {
                return None;
            };
            if name.id != "list" || !parsed.is_host_global("list") {
                return None;
            }
            let element = type_expression(parsed, visible, &subscript.slice)?;
            Some(StarKnownType::List(Box::new(element)))
        }
        _ => None,
    }
}

fn type_union(
    first: StarKnownType,
    rest: impl IntoIterator<Item = StarKnownType>,
) -> StarKnownType {
    let mut alternatives = Vec::new();
    for ty in std::iter::once(first).chain(rest) {
        match ty {
            StarKnownType::Union(members) => {
                for member in members {
                    if !alternatives.contains(&member) {
                        alternatives.push(member);
                    }
                }
            }
            other => {
                if !alternatives.contains(&other) {
                    alternatives.push(other);
                }
            }
        }
    }
    if let [only] = alternatives.as_slice() {
        return only.clone();
    }
    StarKnownType::Union(alternatives.into_boxed_slice())
}

struct CallScanner<'types, 'profile> {
    file: File,
    visible: HashMap<String, StarBinding>,
    declarations: &'types HashMap<String, StarBinding>,
    writes: &'types HashMap<String, usize>,
    loaded_names: &'types HashSet<String>,
    host_functions: &'types HashMap<&'profile str, &'profile StarHostFunction>,
    local_names: HashSet<String>,
    loaded_module: bool,
    deferred: bool,
    problems: Vec<StarTypeProblem>,
    native_problems: Vec<StarNativeTypeProblem>,
    native_call_problems: Vec<StarNativeCallProblem>,
    checked_arguments: usize,
    unproved_arguments: usize,
}

impl<'source> Visitor<'source> for CallScanner<'_, '_> {
    fn visit_stmt(&mut self, statement: &'source Stmt) {
        match statement {
            // The eager pass scans top-level code and top-level `if` arms.
            // The deferred pass scans direct function bodies with their local
            // names excluded; nested functions still need their own scope.
            Stmt::FunctionDef(function) => {
                if self.deferred {
                    return;
                }
                let name = function.name.as_str();
                if self.writes.get(name) == Some(&1)
                    && !self.loaded_names.contains(name)
                    && let Some(StarBinding::Function(binding)) = self.declarations.get(name)
                {
                    self.visible
                        .insert(name.to_string(), StarBinding::Function(binding.clone()));
                }
            }
            Stmt::ClassDef(_) => {}
            Stmt::Assign(assign) => {
                ast::visitor::walk_stmt(self, statement);
                if self.deferred {
                    return;
                }
                let [Expr::Name(target)] = assign.targets.as_slice() else {
                    return;
                };
                let name = target.id.as_str();
                if self.writes.get(name) == Some(&1)
                    && !self.loaded_names.contains(name)
                    && let Some(binding) = self.declarations.get(name)
                {
                    self.visible.insert(name.to_string(), binding.clone());
                }
            }
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
            && self.callee_is_unshadowed(&call.func)
            && let Some(StarBinding::Constructor(constructor)) =
                binding_in_scope(&call.func, &self.visible)
            && let Some(name) = binding_name(&call.func)
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
                let Some(actual) =
                    argument_type(&keyword.value, &self.visible, &self.native_scope())
                else {
                    self.unproved_arguments += 1;
                    continue;
                };
                self.checked_arguments += 1;
                if !type_accepts(&field.ty, &actual) {
                    self.problems.push(StarTypeProblem {
                        file: self.file,
                        range: keyword.value.range(),
                        related_file: constructor.file,
                        related_range: field.range,
                        constructor: name.clone(),
                        field: field_name.to_string(),
                        kind: StarTypeProblemKind::RecordField,
                        expected: field.ty.clone(),
                        actual,
                    });
                }
            }
        }
        if let Expr::Call(call) = expression
            && self.callee_is_unshadowed(&call.func)
            && let Some(StarBinding::Function(function)) =
                binding_in_scope(&call.func, &self.visible)
            && let Some(name) = binding_name(&call.func)
        {
            let function = function.clone();
            self.check_function_call(call, &function, &name);
        }
        if let Expr::Call(call) = expression {
            let native = self.native_scope();
            if let Some(function) = native.function(&call.func) {
                let result =
                    native_call_type_analysis(self.file, call, function, &self.visible, &native);
                self.checked_arguments += result.checked_arguments;
                self.unproved_arguments += result.unproved_arguments;
                self.native_problems.extend(result.problems);
                self.native_call_problems.extend(result.call_problems);
            }
        }
        ast::visitor::walk_expr(self, expression);
    }
}

impl CallScanner<'_, '_> {
    fn scan_deferred_bodies(&mut self, suite: &[Stmt]) {
        let final_visible = self.visible.clone();
        for statement in suite {
            let Stmt::FunctionDef(function) = statement else {
                continue;
            };
            let mut scope = final_visible.clone();
            let mut writes = FunctionScopeWrites::default();
            for parameter in &function.parameters {
                writes.names.insert(parameter.name().as_str().to_string());
            }
            writes.visit_body(&function.body);
            scope.retain(|name, _| !writes.names.contains(name));
            let mut scanner = CallScanner {
                file: self.file,
                visible: scope,
                declarations: self.declarations,
                writes: self.writes,
                loaded_names: self.loaded_names,
                host_functions: self.host_functions,
                local_names: writes.names,
                loaded_module: self.loaded_module,
                deferred: true,
                problems: Vec::new(),
                native_problems: Vec::new(),
                native_call_problems: Vec::new(),
                checked_arguments: 0,
                unproved_arguments: 0,
            };
            scanner.visit_body(&function.body);
            self.problems.extend(scanner.problems);
            self.native_problems.extend(scanner.native_problems);
            self.native_call_problems
                .extend(scanner.native_call_problems);
            self.checked_arguments += scanner.checked_arguments;
            self.unproved_arguments += scanner.unproved_arguments;
        }
    }

    fn callee_is_unshadowed(&self, expression: &Expr) -> bool {
        callee_root_name(expression).is_some_and(|name| !self.local_names.contains(name))
    }

    fn native_scope(&self) -> NativeScope<'_, '_> {
        NativeScope {
            functions: self.host_functions,
            writes: self.writes,
            loaded_names: self.loaded_names,
            local_names: &self.local_names,
            loaded_initialization: self.loaded_module && !self.deferred,
        }
    }

    fn check_function_call(&mut self, call: &ast::ExprCall, function: &StarFunction, name: &str) {
        let StarFunction {
            file,
            parameters,
            returns: _,
        } = function;
        if parameters
            .iter()
            .all(|parameter| parameter.annotation.is_none())
        {
            return;
        }
        let arguments = &call.arguments;
        if !function_call_shape_known(call, function) {
            self.unproved_arguments += arguments.args.len() + arguments.keywords.len();
            return;
        }
        for (argument, parameter) in arguments.args.iter().zip(parameters) {
            self.check_function_argument(argument, parameter, *file, name);
        }
        for keyword in &arguments.keywords {
            let Some(keyword_name) = keyword.arg.as_ref() else {
                continue;
            };
            let Some(parameter) = parameters
                .iter()
                .find(|parameter| parameter.name == keyword_name.as_str())
            else {
                continue;
            };
            self.check_function_argument(&keyword.value, parameter, *file, name);
        }
    }

    fn check_function_argument(
        &mut self,
        expression: &Expr,
        parameter: &StarParameter,
        related_file: File,
        function_name: &str,
    ) {
        let StarParameter { name, annotation } = parameter;
        let Some(StarField {
            ty: expected,
            range,
        }) = annotation
        else {
            self.unproved_arguments += 1;
            return;
        };
        let Some(actual) = argument_type(expression, &self.visible, &self.native_scope()) else {
            self.unproved_arguments += 1;
            return;
        };
        self.checked_arguments += 1;
        if !type_accepts(expected, &actual) {
            self.problems.push(StarTypeProblem {
                file: self.file,
                range: expression.range(),
                related_file,
                related_range: *range,
                constructor: function_name.to_string(),
                field: name.clone(),
                kind: StarTypeProblemKind::FunctionParameter,
                expected: expected.clone(),
                actual,
            });
        }
    }
}

fn callee_root_name(expression: &Expr) -> Option<&str> {
    match expression {
        Expr::Name(name) => Some(name.id.as_str()),
        Expr::Attribute(attribute) => callee_root_name(&attribute.value),
        _ => None,
    }
}

#[derive(Default)]
struct FunctionScopeWrites {
    names: HashSet<String>,
}

impl<'source> Visitor<'source> for FunctionScopeWrites {
    fn visit_stmt(&mut self, statement: &'source Stmt) {
        match statement {
            Stmt::FunctionDef(function) => {
                self.names.insert(function.name.as_str().to_string());
            }
            Stmt::ClassDef(class) => {
                self.names.insert(class.name.as_str().to_string());
            }
            _ => ast::visitor::walk_stmt(self, statement),
        }
    }

    fn visit_expr(&mut self, expression: &'source Expr) {
        match expression {
            // These bind their own names; their calls are also skipped by
            // the deferred scanner until a separate closure scope exists.
            Expr::Lambda(_)
            | Expr::ListComp(_)
            | Expr::SetComp(_)
            | Expr::DictComp(_)
            | Expr::Generator(_) => return,
            Expr::Name(name) if name.ctx == ast::ExprContext::Store => {
                self.names.insert(name.id.as_str().to_string());
            }
            _ => {}
        }
        ast::visitor::walk_expr(self, expression);
    }

    fn visit_except_handler(&mut self, except_handler: &'source ast::ExceptHandler) {
        let ast::ExceptHandler::ExceptHandler(handler) = except_handler;
        if let Some(name) = &handler.name {
            self.names.insert(name.as_str().to_string());
        }
        ast::visitor::walk_except_handler(self, except_handler);
    }

    fn visit_alias(&mut self, alias: &'source ast::Alias) {
        let name = alias
            .asname
            .as_ref()
            .map_or(alias.name.as_str(), |name| name.as_str());
        self.names
            .insert(name.split('.').next().unwrap_or(name).to_string());
    }
}

fn function_call_shape_known(call: &ast::ExprCall, function: &StarFunction) -> bool {
    let arguments = &call.arguments;
    let parameters = &function.parameters;
    if arguments.args.len() > parameters.len() || arguments.args.iter().any(Expr::is_starred_expr) {
        return false;
    }
    let mut seen = HashSet::new();
    for parameter in parameters.iter().take(arguments.args.len()) {
        seen.insert(parameter.name.as_str());
    }
    for keyword in &arguments.keywords {
        let Some(name) = keyword.arg.as_ref() else {
            return false;
        };
        if !parameters
            .iter()
            .any(|parameter| parameter.name == name.as_str())
            || !seen.insert(name.as_str())
        {
            return false;
        }
    }
    true
}

struct NativeScope<'scope, 'profile> {
    functions: &'scope HashMap<&'profile str, &'profile StarHostFunction>,
    writes: &'scope HashMap<String, usize>,
    loaded_names: &'scope HashSet<String>,
    local_names: &'scope HashSet<String>,
    loaded_initialization: bool,
}

impl<'profile> NativeScope<'_, 'profile> {
    fn function(&self, expression: &Expr) -> Option<&'profile StarHostFunction> {
        let Expr::Name(name) = expression else {
            return None;
        };
        let name = name.id.as_str();
        if self.writes.contains_key(name)
            || self.loaded_names.contains(name)
            || self.local_names.contains(name)
        {
            return None;
        }
        let function = self.functions.get(name).copied()?;
        if function.availability == "loaded_module_initialization" && !self.loaded_initialization {
            return None;
        }
        Some(function)
    }
}

/// Map only a call whose native parameter bindings are determined by the
/// attested positional and keyword modes, including required parameters.
enum NativeCallShape {
    Unproved,
    Invalid {
        range: TextRange,
        reason: StarNativeCallReason,
    },
}

fn native_call_mapping<'arg, 'profile>(
    call: &'arg ast::ExprCall,
    function: &'profile StarHostFunction,
) -> Result<Vec<(&'arg Expr, &'profile StarHostParam)>, NativeCallShape> {
    let arguments = &call.arguments;
    if arguments.args.iter().any(Expr::is_starred_expr)
        || arguments
            .keywords
            .iter()
            .any(|keyword| keyword.arg.is_none())
    {
        return Err(NativeCallShape::Unproved);
    }
    let mut positional = function
        .params
        .iter()
        .filter(|param| param.mode != "named_only");
    let mut mapped = Vec::with_capacity(arguments.args.len() + arguments.keywords.len());
    let mut seen = HashSet::new();
    for expression in &arguments.args {
        let Some(param) = positional.next() else {
            let reason = function
                .params
                .iter()
                .find(|param| {
                    param.mode == "named_only"
                        && !arguments.keywords.iter().any(|keyword| {
                            keyword
                                .arg
                                .as_ref()
                                .is_some_and(|name| name.as_str() == param.name)
                        })
                })
                .map_or(StarNativeCallReason::ExcessPositional, |param| {
                    StarNativeCallReason::NamedOnly(param.name.clone())
                });
            return Err(NativeCallShape::Invalid {
                range: expression.range(),
                reason,
            });
        };
        seen.insert(param.name.as_str());
        mapped.push((expression, param));
    }
    for keyword in &arguments.keywords {
        let Some(name) = keyword.arg.as_ref() else {
            return Err(NativeCallShape::Unproved);
        };
        let Some(param) = function
            .params
            .iter()
            .find(|param| param.name == name.as_str())
        else {
            return Err(NativeCallShape::Invalid {
                range: keyword.range(),
                reason: StarNativeCallReason::UnknownNamed(name.to_string()),
            });
        };
        if param.mode == "pos_only" {
            return Err(NativeCallShape::Invalid {
                range: keyword.range(),
                reason: StarNativeCallReason::PositionalOnly(param.name.clone()),
            });
        }
        if !seen.insert(param.name.as_str()) {
            return Err(NativeCallShape::Invalid {
                range: keyword.range(),
                reason: StarNativeCallReason::Duplicate(param.name.clone()),
            });
        }
        mapped.push((&keyword.value, param));
    }
    if let Some(param) = function
        .params
        .iter()
        .find(|param| param.required && !seen.contains(param.name.as_str()))
    {
        return Err(NativeCallShape::Invalid {
            range: call.range(),
            reason: StarNativeCallReason::Missing(param.name.clone()),
        });
    }
    Ok(mapped)
}

fn known_host_type(ty: &str) -> Option<StarKnownType> {
    match ty {
        "int" => Some(StarKnownType::Primitive(StarPrimitive::Int)),
        "str" => Some(StarKnownType::Primitive(StarPrimitive::Str)),
        "bool" => Some(StarKnownType::Primitive(StarPrimitive::Bool)),
        "callable" => Some(StarKnownType::Callable),
        // `any` permits every value; `unknown` attests no portable type.
        "any" | "unknown" => None,
        _ => unreachable!("host type was validated before native analysis"),
    }
}

fn host_signature(function: &StarHostFunction) -> String {
    let mut parts = Vec::with_capacity(function.params.len() + 2);
    let mut positional_only = false;
    let mut named_only = false;
    for param in &function.params {
        if param.mode != "pos_only" && positional_only {
            parts.push("/".to_string());
            positional_only = false;
        }
        if param.mode == "named_only" && !named_only {
            parts.push("*".to_string());
            named_only = true;
        }
        let optional = if param.required { "" } else { " (optional)" };
        parts.push(format!("{}: {}{optional}", param.name, param.ty));
        if param.mode == "pos_only" {
            positional_only = true;
        }
    }
    if positional_only {
        parts.push("/".to_string());
    }
    format!(
        "{}({}) -> {}",
        function.name,
        parts.join(", "),
        function.returns
    )
}

#[derive(Default)]
struct NativeCallTypeAnalysis {
    problems: Vec<StarNativeTypeProblem>,
    call_problems: Vec<StarNativeCallProblem>,
    checked_arguments: usize,
    unproved_arguments: usize,
}

fn native_call_type_analysis(
    file: File,
    call: &ast::ExprCall,
    function: &StarHostFunction,
    visible: &HashMap<String, StarBinding>,
    native: &NativeScope<'_, '_>,
) -> NativeCallTypeAnalysis {
    let mut result = NativeCallTypeAnalysis::default();
    let mapped = match native_call_mapping(call, function) {
        Ok(mapped) => mapped,
        Err(shape) => {
            result.unproved_arguments = call.arguments.args.len() + call.arguments.keywords.len();
            if let NativeCallShape::Invalid { range, reason } = shape {
                result.call_problems.push(StarNativeCallProblem {
                    file,
                    range,
                    function: function.name.clone(),
                    reason,
                    signature: host_signature(function),
                });
            }
            return result;
        }
    };
    for (expression, param) in mapped {
        let Some(expected) = known_host_type(&param.ty) else {
            result.unproved_arguments += 1;
            continue;
        };
        let Some(actual) = argument_type(expression, visible, native) else {
            result.unproved_arguments += 1;
            continue;
        };
        result.checked_arguments += 1;
        if !type_accepts(&expected, &actual) {
            result.problems.push(StarNativeTypeProblem {
                file,
                range: expression.range(),
                function: function.name.clone(),
                parameter: param.name.clone(),
                expected,
                actual,
                signature: host_signature(function),
            });
        }
    }
    result
}

fn argument_type(
    expression: &Expr,
    visible: &HashMap<String, StarBinding>,
    native: &NativeScope<'_, '_>,
) -> Option<StarKnownType> {
    match expression {
        Expr::NumberLiteral(number) => matches!(number.value, Number::Int(_))
            .then_some(StarKnownType::Primitive(StarPrimitive::Int)),
        Expr::StringLiteral(_) => Some(StarKnownType::Primitive(StarPrimitive::Str)),
        Expr::BooleanLiteral(_) => Some(StarKnownType::Primitive(StarPrimitive::Bool)),
        Expr::NoneLiteral(_) => Some(StarKnownType::Primitive(StarPrimitive::None)),
        Expr::Name(_) | Expr::Attribute(_) => {
            let StarBinding::Function(_) = binding_in_scope(expression, visible)? else {
                return None;
            };
            Some(StarKnownType::Callable)
        }
        Expr::Call(call) => {
            if let Some(binding) = binding_in_scope(&call.func, visible) {
                return match binding {
                    StarBinding::Constructor(constructor) => Some(constructor.ty.clone()),
                    StarBinding::Function(function) => {
                        if !function_call_shape_known(call, function)
                            || call.arguments.args.len() + call.arguments.keywords.len()
                                != function.parameters.len()
                        {
                            return None;
                        }
                        let returns = function.returns.as_ref()?;
                        Some(returns.ty.clone())
                    }
                    StarBinding::Alias(_) | StarBinding::Struct(_) => None,
                };
            }
            let function = native.function(&call.func)?;
            let mapped = native_call_mapping(call, function).ok()?;
            for (expression, param) in mapped {
                if let Some(expected) = known_host_type(&param.ty)
                    && let Some(actual) = argument_type(expression, visible, native)
                    && !type_accepts(&expected, &actual)
                {
                    // A call rejected by its known native parameter type
                    // cannot supply a value of the declared return type.
                    return None;
                }
            }
            known_host_type(&function.returns)
        }
        Expr::List(list) => {
            let mut elements = list.elts.iter();
            let first = elements.next()?;
            let first = argument_type(first, visible, native)?;
            let mut types = Vec::new();
            for element in elements {
                let actual = argument_type(element, visible, native)?;
                types.push(actual);
            }
            let element = type_union(first, types);
            Some(StarKnownType::List(Box::new(element)))
        }
        _ => None,
    }
}

fn type_accepts(expected: &StarKnownType, actual: &StarKnownType) -> bool {
    if let StarKnownType::Union(members) = actual {
        return members.iter().all(|member| type_accepts(expected, member));
    }
    match expected {
        StarKnownType::Primitive(expected) => {
            matches!(actual, StarKnownType::Primitive(actual) if actual == expected)
        }
        StarKnownType::Record(expected) => {
            matches!(actual, StarKnownType::Record(actual) if actual == expected)
        }
        StarKnownType::Union(alternatives) => alternatives
            .iter()
            .any(|member| type_accepts(member, actual)),
        StarKnownType::List(element) => {
            matches!(actual, StarKnownType::List(actual) if type_accepts(element, actual))
        }
        StarKnownType::Callable => matches!(actual, StarKnownType::Callable),
    }
}

#[cfg(test)]
mod tests;
