# Starlark type checking

This document records the design, evidence, decisions, and progress for adding
Starlark type checking to ty. It is a working project record, not documentation
for a released feature.

## Goal

Check type annotations in `.bzl` files without changing how Bazel evaluates
them. The checker should understand Bazel `load()` statements and support
out-of-line stubs for code that cannot carry annotations itself.

The initial end-to-end result is:

1. Two annotated `.bzl` files connected by `load()`.
1. A `.bzl.pyi` stub that supplies an unannotated dependency's interface.
1. Starlark and Bazel builtins supplied without editing the checked source.
1. A cross-file type error reported at its original `.bzl` source range.
1. The same `.bzl` files continuing to load under stable Bazel.

## Non-goals for the initial spike

- Checking `BUILD`, `MODULE.bazel`, or `.scl` files.
- Resolving external repositories or repository mappings.
- Modeling every Bazel provider, rule, and analysis API.
- Treating Starlark as Python when their semantics differ.
- Shipping a source-to-source translation as the production design.

## Current state

### Bazel

- Bazel 9.1.1 enables type syntax in `.bzl` files by default but does not
    provide the static type-checking flag present on Bazel's main branch.
- Bazel's main branch contains an experimental static checker and propagates
    exported types through transitive `load()` dependencies.
- Bazel has no out-of-line type stub mechanism.
- The native checker is part of Bazel loading. It is not a standalone checker
    for arbitrary `.bzl` files.

Relevant upstream work:

- <https://github.com/bazelbuild/bazel/issues/27370>
- <https://github.com/bazelbuild/bazel/issues/28325>

### ty

- Passing a `.bzl` path explicitly to released ty parses the file as Python.
    The resulting diagnostics are semantic: unresolved `load`, loaded symbols,
    `struct`, and `depset`. No parse diagnostic is emitted.
- Starlark `load()` is valid Python call syntax. Supporting it does not require
    a new parser statement.
- ty already prefers `.pyi` stubs to Python source modules and supports
    project-level `__builtins__.pyi` files.
- The prototype automatically discovers `.bzl` files and records their
    language separately from Python's implementation/stub source kind.
- The prototype binds positional and renamed symbols from top-level `load()`
    calls and infers their types directly from the resolved file.
- Main-repository absolute labels with an explicit target and same-directory
    relative labels are supported. Repository-qualified labels and full Bazel
    package discovery are not yet supported.
- A sibling `.bzl.pyi` takes precedence over the loaded `.bzl` implementation,
    but does not make a missing implementation loadable.
- Starlark loads re-export names from `.bzl.pyi` files without applying
    Python's explicit-stub-re-export convention.
- Invalid labels, missing loaded files, and missing exports currently become
    `Unknown` without a Starlark-specific diagnostic.
- Python module resolution only considers Python package names and `.py` or
    `.pyi` files.

### Other tooling

`starpls` already implements Bazel label resolution, repository mapping, and
cross-file inference. It currently documents PEP 484 type comments rather than
Bazel's annotation syntax. Its resolver is prior art for the Bazel-specific
parts of this project:

<https://github.com/withered-magic/starpls>

## Design constraints

1. Diagnostics and IDE operations must retain original `.bzl` source ranges.
1. Bazel labels, not synthetic Python module names, identify Starlark modules.
1. Stubs shadow implementations for type information without affecting Bazel
    evaluation.
1. Starlark behavior must be explicit in the database. A `.bzl` file must not
    silently acquire Python semantics merely because both use the same parser.
1. `load()` handling belongs in semantic indexing and module resolution, not
    in preprocessing.
1. Builtin declarations should eventually be generated from Bazel metadata,
    not maintained as a second handwritten API definition.
1. The initial implementation should expose the smallest useful dialect
    boundary in ty rather than adding Starlark branches throughout Ruff.

## Proposed architecture

### Source and dialect

Teach the ty project layer to discover `.bzl` files and associate them with an
explicit Starlark dialect. Continue using Ruff's Python parser for shared
syntax. Keep the dialect separate from whether a file is an implementation or
a stub.

Avoid adding a `Starlark` variant to `PySourceType` unless investigation shows
that source kind and language dialect cannot remain separate. `PySourceType`
is shared across Ruff's parser, formatter, linter, and ty, so extending it
would create unrelated exhaustiveness and behavior changes.

### Loads and modules

Recognize a top-level call with the Starlark `load()` shape during semantic
indexing:

```starlark
load("//pkg:lib.bzl", "name", local_name = "exported_name")
```

The first argument identifies a module. Positional string arguments bind the
same exported and local name. Keyword arguments bind the keyword name locally
to the string-valued exported name.

Resolve the initial spike's labels relative to the importing file and workspace
root. Later support apparent repository names using `bazel mod dump_repo_mapping` and resolve external repository roots through Bazel.

### Stubs

Use `foo.bzl.pyi` as the sibling stub for `foo.bzl`. The final `.pyi` extension
already gives the file stub semantics in ty, while the `.bzl` component makes
the association unambiguous.

Sibling stubs are insufficient for external repositories. A later phase needs
an explicit label-to-stub overlay whose keys are canonical Bazel labels.

### Builtins

Use ty's existing project-level `__builtins__.pyi` support for the spike. Begin
with only the Starlark values required by the fixture. Investigate generating
the complete declaration set from Bazel's Starlark API metadata after the
cross-file path works.

This mechanism is project-wide, so a production design must avoid exposing
Starlark-only builtins to Python files in mixed projects.

### Type semantics

Start by identifying places where ty's Python assumptions produce incorrect
Starlark results. Do not suppress those differences globally. Introduce
dialect-aware behavior at the semantic operation that owns each difference.

Known examples include strings not being iterable in Starlark and Bazel-only
values such as `depset`, providers, rules, and analysis context objects.

## Testing

Use ty's Markdown test harness for Starlark type-system behavior. A `bzl` code
block without an explicit path becomes `/src/mdtest_snippet.bzl`. Explicit
paths create multi-file load graphs, and a `.bzl.pyi` stub uses a `pyi` code
block:

````markdown
`defs.bzl`:

```bzl
def accepts_int(value: int) -> None:
    pass
```

`main.bzl`:

```bzl
load("//:defs.bzl", "accepts_int")
accepts_int("bad")  # error: [invalid-argument-type]
```
````

Keep CLI tests for discovery and command behavior, resolver unit tests for
label and filesystem semantics, and IDE tests for navigation. The checked-in
Bazel fixture separately proves that stable Bazel accepts the same annotated
sources checked by ty.

Run the Starlark semantic suite with:

```console
cargo nextest run -p ty_python_semantic --test mdtest starlark
```

In an OSS repository, a public PyPI override may be used when the configured
package index is missing hook packages:

```console
UV_DEFAULT_INDEX=https://pypi.org/simple/ uvx prek run -a
```

Never use that override in a private or internal repository.

## Milestones

- [x] M0: Discover and parse `.bzl` files in explicit Starlark mode.
- [x] M1: Bind same-repository `load()` symbols without source rewriting.
- [x] M2: Prefer a sibling `.bzl.pyi` over an implementation's exported types.
- [x] M3: Supply minimal Starlark builtins and report a cross-file type error.
- [ ] M4: Add repository mapping and external repository resolution.
- [ ] M5: Generate Bazel builtin declarations from an upstream source of truth.
- [ ] M6: Review correctness, incrementality, architecture, and upstream fit.

## Validation record

| Date       | Revision                       | Validation                                                        | Result                                                                  |
| ---------- | ------------------------------ | ----------------------------------------------------------------- | ----------------------------------------------------------------------- |
| 2026-06-10 | Bazel `8c5accefec19`           | `SyntaxTests` and `StarlarkTypesTest`                             | Passed                                                                  |
| 2026-06-10 | ty 0.0.47                      | Check existing `struct_to_dict.bzl` explicitly                    | Parsed; expected unresolved Starlark semantics                          |
| 2026-06-10 | Ruff `7dd5f3029d`              | Project branch baseline                                           | No project changes                                                      |
| 2026-06-10 | `starlark-typing` working tree | `dialect_from_path` and `starlark_files_are_discovered`           | Passed                                                                  |
| 2026-06-10 | `starlark-typing` working tree | Module-resolver Starlark tests                                    | Passed                                                                  |
| 2026-06-10 | `starlark-typing` working tree | Starlark load, sibling-stub, and builtin mdtests                  | Passed; inline assertions retain consumer and declaration ranges        |
| 2026-06-10 | `starlark-typing` working tree | Transitive load typing and goto-definition tests                  | Passed; both resolve to the originating declaration                     |
| 2026-06-10 | Bazel 9.1.1                    | `bazel query --lockfile_mode=off //...` in the checked-in fixture | Passed; stable Bazel evaluated the annotated load graph                 |
| 2026-06-10 | `starlark-typing` working tree | `ty check crates/ty/tests/fixtures/starlark`                      | Passed on the same files evaluated by Bazel                             |
| 2026-06-10 | `starlark-typing` working tree | Resolver filesystem-transition test                               | Passed; stub creation and implementation deletion invalidate resolution |
| 2026-06-10 | `starlark-typing` working tree | All 103 mdtest parser tests                                       | Passed                                                                  |
| 2026-06-10 | `starlark-typing` working tree | `cargo check -p ty -p ty_test -p mdtest`                          | Passed                                                                  |
| 2026-06-10 | `starlark-typing` working tree | Full tracked-file `prek` plus explicit new files                  | Passed using the OSS-only public PyPI override                          |

## Decision log

| Date       | Decision                                                          | Reason                                                                                                             |
| ---------- | ----------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------ |
| 2026-06-10 | Implement in the Ruff repository under ty                         | ty's Rust implementation lives in Ruff; the outer ty repository contains release and documentation infrastructure  |
| 2026-06-10 | Preserve `load()` in the original syntax tree                     | It already parses as a call, and rewriting would complicate diagnostics and IDE source mapping                     |
| 2026-06-10 | Use `.bzl.pyi` for sibling stubs                                  | It preserves the implementation name and reuses ty's existing stub syntax                                          |
| 2026-06-10 | Keep language dialect separate from `PySourceType` initially      | `PySourceType` is shared broadly across Ruff and conflates syntax container with language semantics                |
| 2026-06-10 | Classify dialect in `ty_python_core`                              | Project discovery and semantic analysis share one language-level owner without changing Ruff's Python source model |
| 2026-06-10 | Limit the first resolver to the main repository                   | This proves the type-checking contract before introducing Bazel server and bzlmod integration                      |
| 2026-06-10 | Represent each loaded symbol as a dedicated definition            | Starlark loads retain their original AST nodes and Bazel labels without pretending to be Python imports            |
| 2026-06-10 | Resolve loads to `File` and reuse public-symbol inference         | Cross-file type inference is shared while Python module naming and resolution remain separate                      |
| 2026-06-10 | Require the `.bzl` implementation before selecting a sibling stub | A stub supplies type information but must not make an invalid Bazel load appear valid                              |
| 2026-06-10 | Do not apply Python stub re-export rules to Starlark loads        | Loaded Starlark globals retain Bazel's re-export behavior even when their types come from `.bzl.pyi`               |

## Open questions

- How should an explicit external stub overlay be configured and versioned?
- Which Bazel API metadata is sufficiently complete and stable to generate
    builtin stubs?
- Which parts of `starpls` label resolution can be reused directly, and which
    should only inform an independent implementation?
- Where should statement-level load validation live so one unresolved module
    diagnostic is emitted per `load()` while missing exports remain anchored to
    their individual bindings?

## Progress log

### 2026-06-10

- Confirmed stable Bazel accepts annotations while Bazel main has a separate,
    experimental checker.
- Confirmed released ty parses an explicitly selected `.bzl` file.
- Identified file discovery, `load()` semantics, Bazel label resolution,
    builtins, and Starlark-specific operations as the real integration surface.
- Created branch `starlark-typing` from Ruff `7dd5f3029d`.
- Added an explicit `SourceDialect` distinct from `PySourceType` and taught
    project discovery to include `.bzl` files.
- Validated the classifier and automatic CLI discovery with focused tests.
- Added a main-repository Starlark label resolver with traversal rejection and
    sibling-stub precedence.
- Added dedicated load definitions for positional and renamed bindings and
    connected them to cross-file public-symbol inference.
- Validated cross-file call diagnostics and `.bzl.pyi` precedence end to end.
- Validated a minimal real Starlark builtin through project-level
    `__builtins__.pyi` alongside a cross-file load diagnostic.
- Added a checked-in annotated fixture and validated the same load graph with
    stable Bazel 9.1.1 and the patched ty checker.
- Validated transitive typing and goto-definition through two `load()` edges.
- Required sibling stubs to accompany real implementations and preserved
    Starlark re-exports through `.bzl.pyi` files.
- Validated resolver invalidation when a stub appears and when its underlying
    implementation disappears.
- Extended mdtest with `bzl` files and migrated Starlark semantic coverage from
    CLI snapshots to literate, multi-file tests.
- Reviewed unresolved-load diagnostics, external repository resolution, and
    dialect-specific builtins as the remaining architectural boundaries rather
    than adding local compatibility behavior.
