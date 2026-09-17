# Shared Starlark analysis

Bazel `.bzl` files, BUILD files, and hosted `.star` sources use Ty's semantic
engine. The frontends admit syntax, resolve loads, and provide
declarations; Ty owns inference, argument binding, assignability, and
body checking.

## Ownership

| Owner                | Responsibility                                                                                         |
| -------------------- | ------------------------------------------------------------------------------------------------------ |
| `sty`                | CLI targets, editor documents, host process lifecycle, configuration, and presentation                 |
| `ty_starlark`        | Starlark syntax admission, Bazel roots and labels, resolved load bindings, and host facts              |
| `ty_python_core`     | Semantic module identity, definitions, scopes, use/definition maps, and dependency tracking            |
| `ty_python_semantic` | Types, signatures, argument binding, assignability, function bodies, returns, and semantic diagnostics |
| `ty_ide`             | Completion contexts, ranking, signatures, and source definition queries                                |
| `ruff_db`            | Source snapshots, parsing infrastructure, diagnostic spans, and rendering                              |
| External host        | Its parser, private loader, and declarations of native capabilities                                    |

The external host continues to produce a declarative source graph. Sty owns
static analysis. Native execution, deployment evaluation, and host runtime
checks remain separately invoked operations.

## Source and module identity

A physical source and a semantic module need separate identities. A host
can expose the same captured text under two logical module IDs. Records
declared in those modules must remain nominally distinct. Conversely,
repeated loads of one logical module must share its declarations.

[`StarlarkModule`](../ty_python_core/src/starlark.rs) is a tracked input that
identifies a logical module and supplies its resolved load edges.
[`ProgramFile`](../ty_python_core/src/program_file.rs) includes that identity
alongside the physical parser key and program. Parsing shares identical
sources while definitions remain separate for distinct logical modules.
The physical file stays fixed for each module instance; its contents and
resolved edges can be updated through tracked inputs.

Each check captures its graph in a fresh in-memory semantic database,
[`AnalysisDb`](../ty_starlark/src/analysis.rs). Sources, resolved edges, and
host declarations become tracked inputs within that database. Bazel reads
source, companion, package, and repository files through the outer database's
tracked filesystem; editor changes trigger a new graph check. The editor
retains the resulting `Analysis` for shared IDE queries. A host result's
captured text is never replaced by a later disk read. Hosted recovery updates
tracked source text and safe load edges within the retained database while
new host facts are pending; it cannot establish checked diagnostics.

## Loads and builtins

Each admitted `load` binding is a definition at its original string or alias
span, with the resolved target module and exported name.
The frontend supplies resolution. The semantic index records the load's
bindings directly, and inference reads the resolved module's exports.

Ty's Python imports and Starlark loads share the explicit end-of-module
lookup in [`exported_symbol`](../ty_python_semantic/src/place.rs). Python's
implicit module attributes remain in its import fallback. Starlark loads
do not reexport imported bindings; an explicit assignment can reexport a
value. Host label resolution and private-name visibility remain frontend
policy. Aliases and local rebinding use the shared scope and definition maps.

Starlark calls in unreachable code are checked using lexical binding types
without the unreachable region's narrowing. Live uses and module exports
retain the usual control-flow analysis. This keeps a dead assignment from
changing an exported type while still checking calls inside that branch.

The existing custom standard-library mechanism supplies builtin declarations.
Shared methods live in [`builtins.pyi`](../ty_starlark/resources/starlark/builtins.pyi);
small Bazel and hosted fragments select differing signatures, visible globals,
and type-value operations. They form one builtin module so Ty retains its
canonical builtin identities. The
[custom-typeshed regression](../ty_python_semantic/resources/mdtest/mdtest_custom_typeshed.md)
proves that Ty's existing argument and return checks distinguish `bool`
from `int` when their builtin classes are unrelated, while normal Python
programs retain their inheritance relationship.

`ProgramLanguage` selects the operations whose Python behavior cannot be
expressed by declarations alone: Boolean literal arithmetic and equality,
float widening, string iteration, `type()` results, and fixed tuple type
expressions. Python programs retain their existing behavior. The embedded
builtin module's `__all__` declares the globals visible to Starlark source;
internal type lookups can still use its supporting declarations.

## Native functions and records

Native signatures use existing `Parameter`, `Parameters`, and `Signature`
representations. Parameter modes and requiredness come from validated host
facts. Their semantic values retain the declaration identity through aliases
and unions without adding Python receiver binding. Host availability is a
separate contextual rule; a callable signature cannot establish when
execution is allowed.

`DynamicClassLiteral` carries synthesized nominal metadata for records:
fields, defaults, declaration identity, and source provenance. Its shared
constructor-signature query serves both calls and conversion to a callable.
The return instance is constructed from the class identity when queried,
avoiding a self-reference in the metadata. Struct fields use the same
instance-member representation; function values do not acquire receivers.

The captured graph is checked in an in-memory database with embedded
Starlark builtin declarations. Physical source snapshots share parser keys;
logical modules retain separate semantic identities. Every diagnostic
annotation is converted to an owned source snapshot before returning to the
caller. Editor queries likewise return owned completion presentations or
captured definition sources and ranges. No database file handle escapes.

## Bazel declarations

[`stub.rs`](../ty_starlark/src/stub.rs) parses the exact `.bzl.pyi` sibling and
matches each declaration to a public source function. The MVP supports
`int`, `str`, `bool`, and `None` annotations on positional-or-keyword functions.
Parameter names, kinds, counts, and default presence must match; malformed or
unmatched declarations reject the companion as a whole.

`StarlarkFunctionAnnotations` attaches types to original function and parameter
ranges, with separate companion origins. Ty's shared signature, parameter,
default, reassignment, and return checks consume those annotations. Loads still
resolve to source definitions. Semantic errors stay attached to the offending
source; they do not turn the whole load graph into an opaque module.

BUILD files are selected by exact package labels and share the load graph
with `.bzl` dependencies. Loads may target only `.bzl` sources. Each module
has its own builtin environment: `select` is visible in both source kinds,
while `glob`, `package`, `exports_files`, `filegroup`, and `genrule` are
direct globals only in BUILD files. These functions use precise declarations
in [`bazel.pyi`](../ty_starlark/resources/starlark/bazel.pyi). The declarations
are not exported from the general Starlark builtin inventory; Ty resolves
them by name only through the selected source environment. No companion
declarations apply to BUILD files.

Syntax, label, companion, and cycle failures prevent dependent modules from
being analyzed. Independent admitted modules remain checkable.

Unannotated functions use Ty's ordinary inference. In particular, their
parameters and return values can remain unknown. Callers do not specialize
helper bodies; `.bzl.pyi` annotations supply the missing constraints. Those
annotations constrain source bodies, defaults, and reassignments.

## Diagnostics and editor integration

Both frontends produce `ruff_db::Diagnostic` values.
Semantic diagnostics own immutable `SourceFile` spans. The CLI uses Ruff's
renderer; the editor converts those same diagnostics to LSP.
[`diagnostics.rs`](src/diagnostics.rs) also projects host admission failures
onto the captured source graph.

The LSP conversion preserves located subdiagnostics and secondary annotations.
Embedded builtin declarations have display-only names; their annotations
appear as text when no editor location exists. Sty owns document synchronization
and host-worker scheduling, independently of Ty's Python project server.

[`ty_ide::local_completion`](../ty_ide/src/completion.rs) uses the same
context, ranking, and signature logic as Python completion, with no project
search or import edits. Runtime names use the same builtin visibility lookup
as inference. Definition queries follow final public load exports and retain
record field declaration names separately from diagnostic type origins.
Queries run in every logical context for a physical file and deduplicate
identical presentations or locations.

Bazel recovery reuses the source admission visitor and load discovery, allows
parser recovery placeholders, and retains local facts when a dependency is
unavailable. It does not relax CLI admission or publish recovery diagnostics.
Valid dependencies retain their companion declarations. Hosted recovery
requires an earlier admitted graph: unchanged, unique top-level load call
text may retain its original edge at a new source range. Changed, reordered,
or nested calls lose their old edges. Source edits discard companion offsets.
The original attestations remain the reference across repeated edits and undo.

The server installs host analyses behind the same revision gates as diagnostics.
Watched dependency, executable, manifest, and input changes invalidate retained
facts and advance the host revision. Definition positions use captured target
text, including unsaved Unicode, through the diagnostic span projector.

## MVP limits

The Bazel frontend selects BUILD files and `.bzl` sources in one main
repository, not arbitrary Bazel build targets or external repositories.
Its builtin inventory is a subset of Bazel's language environment;
other native rules, `.bzl` native methods, provider, and repository APIs
are not yet declared.
The shared Python parser also rejects some valid Starlark
forms, including positional symbols after named aliases in `load`.

The server provides diagnostics, completion, and source Go to Definition.
Hover, embedded builtin navigation, and arbitrary Bazel target navigation
are not implemented. Hosted IDE queries need a first successful graph capture.
A single CLI invocation selects
either Bazel or a configured hosted graph; it does not combine Python and
Starlark projects.
