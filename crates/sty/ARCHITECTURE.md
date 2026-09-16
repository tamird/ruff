# Shared Starlark analysis

## Status and target

Hosted `.star` graphs use Ty's inference for types, scopes, calls, records,
and diagnostics. Their frontend validates captured sources and host facts,
then creates explicit Starlark semantic inputs. The former hosted type
model, argument mapper, and proof counters have been removed.

The Bazel frontend still uses its scalar analyzer. Its remaining migration
requires external function annotations; see the Bazel declarations section
below.

Success means removing the replaced inference, signature, and assignability
code. A second implementation behind a backend switch would add maintenance
work. Each production migration must replace a complete mechanism and keep
its existing conformance tests.

## Ownership

| Owner                | Responsibility                                                                                              |
| -------------------- | ----------------------------------------------------------------------------------------------------------- |
| `sty`                | CLI targets, editor documents, host process lifecycle, configuration, and presentation                      |
| `ty_starlark`        | Starlark syntax admission, Bazel roots and labels, resolved load bindings, host facts, and dialect policies |
| `ty_python_core`     | Semantic module identity, definitions, scopes, use/definition maps, and dependency tracking                 |
| `ty_python_semantic` | Types, signatures, argument binding, assignability, function bodies, returns, and semantic diagnostics      |
| `ruff_db`            | Source snapshots, parsing infrastructure, diagnostic spans, and rendering                                   |
| External host        | Its parser, private loader, and declarations of native capabilities                                         |

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

Captured source, resolved edges, and host declarations must enter the
database as tracked inputs. Updating a loaded source or changing an edge
must invalidate its importers. A host result's source text must never be
replaced by a later disk read. Concurrent host profiles or captured revisions
must not share semantic results merely because their paths match.

## Loads and builtins

Each admitted `load` binding is a definition at its original string or alias
span, with the resolved target module and exported name.
The frontend supplies resolution; the semantic engine must not reinterpret
Bazel labels as Python imports. Handle the load statement as definitions
instead of inferring an ordinary call to a global named `load`.

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

Use program-specific builtin declarations through the existing custom
standard-library mechanism. The
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
logical modules retain separate semantic identities. Before the database
is dropped, every diagnostic annotation and subdiagnostic annotation is
converted to an owned source snapshot. No database file handle escapes.

## Bazel declarations

The existing [`overlay`](../ty_starlark/src/overlay.rs) checks runtime
function bodies before exposing `.bzl.pyi` signatures. Preserve that
contract. External annotations must supply types to signature construction,
body parameters, and return checking, with declaration spans in the stub.
Simply resolving a load to the stub would bypass the runtime-body check.

Unannotated functions use Ty's ordinary inference. In particular, their
parameters and return values can remain unknown. Callers do not specialize
helper bodies; `.bzl.pyi` annotations supply the missing constraints. Those
annotations must also check source bodies, defaults, and reassignments.

## Diagnostics and editor integration

Both frontends now produce `ruff_db::Diagnostic` through
[`diagnostics.rs`](src/diagnostics.rs). Hosted diagnostics own immutable
`SourceFile` spans. The CLI uses Ruff's renderer; the editor converts those
same diagnostics to LSP. The old CLI reporters and editor snapshot renderer
have been removed.

The LSP conversion preserves located subdiagnostics and secondary annotations.
Embedded builtin declarations have display-only names; their annotations
appear as text when no editor location exists. Keep
document synchronization and host-worker scheduling separate from semantic
analysis. Sharing Ty's entire Python project server is not a prerequisite
for sharing its analysis.

## Migration gates

1. Establish the module identity and load-definition boundary with Ty
    tests: aliases, shadowing, final exports, original spans, and importer
    invalidation. Include two logical modules sharing one physical source.
    Also check one physical source under distinct builtin/host profiles and
    captured revisions in the same database.
1. Prove nominal records, union fields, native signatures, and annotated
    function bodies through Ty. Cover wrong nominal arguments, constructor
    keyword rules, callable fields, loaded `struct` members, related spans,
    and invalid returns.
1. Route the hosted frontend through that path and remove `StarKnownType`,
    `type_accepts`, source-function signatures, native argument mapping, and
    the replaced analysis in [`star.rs`](../ty_starlark/src/star.rs).
1. Supply Bazel external declarations to the same
    engine. Remove the replaced inference in
    [`checker.rs`](../ty_starlark/src/checker.rs),
    [`imports.rs`](../ty_starlark/src/imports.rs), and
    [`overlay.rs`](../ty_starlark/src/overlay.rs); retain frontend admission,
    label resolution, and declaration validation.

Keep each change reviewable against its Python users as well as its
Starlark users. Add shared interfaces alongside real consumers, and avoid
broad crate renames or a generic compiler framework during these steps.
