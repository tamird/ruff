# Shared Starlark analysis

## Status and target

Sty currently shares Ruff's parser, source infrastructure, and diagnostics.
Its Bazel and hosted `.star` analyzers still implement separate type systems.
The target is to replace those analyzers with Ty inference, with explicit
Starlark frontend inputs. Ty now accepts logical Starlark modules and resolved
loads and checks their annotated functions through its existing inference.
Sty's production frontends still need to migrate to that semantic boundary.

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

Builtin declarations alone do not establish Starlark semantics. Ty's
[binary expression inference](../ty_python_semantic/src/types/infer/builder/binary_expressions.rs)
also converts Boolean literals to integers directly. Audit and isolate
such operations, Python implicit globals, annotation evaluation, and scope
rules before admitting their Starlark forms. Keep unsupported forms explicit
throughout migration.

## Native functions and records

Native signatures fit existing `Parameter`, `Parameters`, `Signature`, and
`Type::single_callable` representations. Parameter modes and requiredness
come from validated host facts. Use regular callable types so attribute
access does not add Python receiver binding. Host availability is a separate
contextual rule; a callable signature cannot establish when execution is
allowed.

Records need explicit synthesized nominal-class metadata: declaration
identity, instance fields, constructor parameters, and source provenance.
The existing
[`DynamicClassLiteral`](../ty_python_semantic/src/types/class/dynamic_literal.rs)
provides nominal machinery, but its current members are Python class
attributes and its definition anchor interprets `type(...)` syntax. Those
assumptions must be separated before using it for records.

One constructor-signature query should serve both constructor checking and
conversion to a callable. Construct its return instance from the class
identity when queried, avoiding a self-reference in the interned metadata.
Keep callable-valued fields as ordinary instance values and retain related
field declaration spans. Reuse Ty unions and assignability after these
representations exist. Do not encode records as tuples or structural maps:
their identity, members, and subtype relationships differ.

## Bazel declarations

The existing [`overlay`](../ty_starlark/src/overlay.rs) checks runtime
function bodies before exposing `.bzl.pyi` signatures. Preserve that
contract. External annotations must supply types to signature construction,
body parameters, and return checking, with declaration spans in the stub.
Simply resolving a load to the stub would bypass the runtime-body check.

Ty's ordinary unannotated source signatures currently use an unknown return type.
The migration must account for Bazel's current source-derived return
summaries and specialization explicitly, including recursion and failing
bodies. Do not silently trade those checks for trusted stub returns.

## Diagnostics and editor integration

Both frontends now produce `ruff_db::Diagnostic` through
[`diagnostics.rs`](src/diagnostics.rs). Hosted diagnostics own immutable
`SourceFile` spans. The CLI uses Ruff's renderer; the editor converts those
same diagnostics to LSP. The old CLI reporters and editor snapshot renderer
have been removed.

Before routing native Ty diagnostics into Sty, extend the LSP conversion
to preserve located subdiagnostics as well as secondary annotations. Keep
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
1. Supply Bazel external declarations and source summaries to the same
    engine. Remove the replaced inference in
    [`checker.rs`](../ty_starlark/src/checker.rs),
    [`imports.rs`](../ty_starlark/src/imports.rs), and
    [`overlay.rs`](../ty_starlark/src/overlay.rs); retain frontend admission,
    label resolution, and declaration validation.

Keep each change reviewable against its Python users as well as its
Starlark users. Add shared interfaces alongside real consumers, and avoid
broad crate renames or a generic compiler framework during these steps.
