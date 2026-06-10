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
- Main-repository `//package:file.bzl` and `:file.bzl` labels resolve from
    Bazel repository and package markers. Repository-qualified labels are not
    yet supported.
- Labels that enter a descendant Bazel package are rejected; the target must be
    addressed through that package's own label.
- A sibling `.bzl.pyi` takes precedence over the loaded `.bzl` implementation,
    but does not make a missing implementation loadable.
- Loaded names are private to the importing module unless explicitly assigned
    to a public name, matching Bazel's export behavior.
- Malformed loads, missing loaded files, and missing exports produce
    deterministic diagnostics even when the loaded binding is unused.
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
1. Semantic indexing owns structural `load()` identity and local bindings;
    tracked module resolution owns labels, packages, repositories, and stubs.
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

Recognize a call with the Starlark `load()` shape during semantic indexing and
validate that it is a top-level statement before other executable statements:

```starlark
load("//pkg:lib.bzl", "name", local_name = "exported_name")
```

The first argument identifies a module. Positional string arguments bind the
same exported and local name. Keyword arguments bind the keyword name locally
to the string-valued exported name.

Keep only the load expression and binding index in the semantic index. Resolve
labels through a tracked module-resolver query when inference or IDE features
need the target. Main-repository labels use the nearest Bazel repository and
package markers. Later support apparent repository names using
`bazel mod dump_repo_mapping` and resolve external repository roots through
Bazel.

### Stubs

Use `foo.bzl.pyi` as the sibling overlay for `foo.bzl`. This is a ty-specific
Starlark interface convention, not a Python stub module. The final `.pyi`
extension gives the file stub semantics in ty, while the `.bzl` component
makes the association unambiguous.

Sibling stubs are insufficient for external repositories. A later phase needs
an explicit label-to-stub overlay whose keys are canonical Bazel labels.

### Builtins

Do not use ty's project-level `__builtins__.pyi`: it also changes Python files
in a mixed project. Starlark builtins need a dialect-specific source that can
eventually be generated from Bazel's Starlark API metadata. Until that source
is designed, builtin coverage remains intentionally incomplete.

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
- [ ] M3: Supply Starlark builtins without changing Python analysis.
- [ ] M4: Add repository mapping and external repository resolution.
- [ ] M5: Generate Bazel builtin declarations from an upstream source of truth.
- [x] M6: Review correctness, incrementality, architecture, and upstream fit.

## Validation record

| Date       | Revision                       | Validation                                                        | Result                                                                  |
| ---------- | ------------------------------ | ----------------------------------------------------------------- | ----------------------------------------------------------------------- |
| 2026-06-10 | Bazel `8c5accefec19`           | `SyntaxTests` and `StarlarkTypesTest`                             | Passed                                                                  |
| 2026-06-10 | ty 0.0.47                      | Check existing `struct_to_dict.bzl` explicitly                    | Parsed; expected unresolved Starlark semantics                          |
| 2026-06-10 | Ruff `7dd5f3029d`              | Project branch baseline                                           | No project changes                                                      |
| 2026-06-10 | `starlark-typing` working tree | `dialect_from_path` and `starlark_files_are_discovered`           | Passed                                                                  |
| 2026-06-10 | `starlark-typing` working tree | Module-resolver Starlark tests                                    | Passed                                                                  |
| 2026-06-10 | `starlark-typing` working tree | Starlark load and sibling-overlay mdtests                         | Passed; inline assertions retain consumer and declaration ranges        |
| 2026-06-10 | `starlark-typing` working tree | Transitive load typing and goto-definition tests                  | Passed through valid load and explicit re-export edges                  |
| 2026-06-10 | Bazel 9.1.1                    | `bazel query --lockfile_mode=off //...` in the checked-in fixture | Passed; stable Bazel evaluated the annotated load graph                 |
| 2026-06-10 | `starlark-typing` working tree | `ty check crates/ty/tests/fixtures/starlark`                      | Passed on the same files evaluated by Bazel                             |
| 2026-06-10 | `starlark-typing` working tree | Resolver filesystem-transition test                               | Passed; stub creation and implementation deletion invalidate resolution |
| 2026-06-10 | `starlark-typing` working tree | All 103 mdtest parser tests                                       | Passed                                                                  |
| 2026-06-10 | `starlark-typing` working tree | `cargo check -p ty -p ty_test -p mdtest`                          | Passed                                                                  |
| 2026-06-10 | `starlark-typing` working tree | Full tracked-file `prek` plus explicit new files                  | Passed using the OSS-only public PyPI override                          |
| 2026-06-10 | `2877bf588d`                   | Resolver, index, semantic, incrementality, and IDE Starlark tests | Passed; eight focused tests across six binaries                         |
| 2026-06-10 | `2877bf588d`                   | `invalid-starlark-load` with concise output                       | Passed; one source location and concise diagnostic                      |
| 2026-06-10 | `df91751f48`                   | Nested Bazel package-boundary resolution                          | Passed for repository-relative and package-relative labels              |
| 2026-06-10 | `ca18aa6181`                   | Explicit and implicit re-export navigation                        | Passed; invalid traversal stops at the local load binding               |
| 2026-06-10 | `f9e7303660`                   | Starlark-focused nextest run                                      | Passed; 11 tests across 11 binaries                                     |
| 2026-06-10 | `f9e7303660`                   | Clippy for all affected crates, targets, and features             | Passed with warnings denied                                             |

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
| 2026-06-10 | Store load syntax identity rather than resolved files             | Target resolution remains a tracked consumer query, preserving Salsa invalidation boundaries                       |
| 2026-06-10 | Require the `.bzl` implementation before selecting a sibling stub | A stub supplies type information but must not make an invalid Bazel load appear valid                              |
| 2026-06-10 | Require explicit assignment to re-export a loaded name            | Bazel does not expose a name merely because another module loaded it                                               |
| 2026-06-10 | Resolve labels from Bazel repository and package markers          | `//` is repository-relative and `:` is package-relative, independent of the importing file's directory             |
| 2026-06-10 | Reject project-wide builtins for Starlark                         | Reusing `__builtins__.pyi` would leak Starlark-only names into Python analysis                                     |
| 2026-06-10 | Reject labels that cross into descendant packages                 | Bazel assigns files below another package marker to that package                                                   |
| 2026-06-10 | Apply explicit export rules to IDE navigation                     | Navigation must not cross a module boundary that inference rejects                                                 |

## Review record

Review rounds covered ty and Ruff architecture, Bazel and Starlark semantics,
Rust performance, Python compatibility, and general API design.

Accepted findings:

- Keep target resolution out of semantic indexing and retain only AST identity
    plus binding position there.
- Visit the complete load expression structurally even though inference gives
    it Starlark-specific behavior.
- Require explicit re-exports in inference and IDE navigation.
- Resolve labels from repository and package roots, and reject descendant
    package crossings.
- Keep Starlark builtins separate from Python project builtins.

Rejected finding:

- One review proposed allowing only a leading docstring before `load()`.
    Bazel's `Resolver.checkLoadAfterStatement` ignores every top-level string
    literal while finding the first non-load statement, so the implementation
    intentionally does the same.

Deferred findings:

- External repositories and repository mappings belong in M4.
- Complete rejection of Python syntax that Starlark does not support remains a
    prerequisite for moving beyond the experimental dialect.
- Dialect-specific, generated Starlark builtins belong in M3 and M5.

## Open questions

- How should an explicit external stub overlay be configured and versioned?
- Which Bazel API metadata is sufficiently complete and stable to generate
    builtin stubs?
- Which parts of `starpls` label resolution can be reused directly, and which
    should only inform an independent implementation?
- What source and database boundary can supply builtins only to Starlark files?
- Which additional Starlark syntax differences must be rejected before this
    can move beyond an experimental dialect?

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
- Added a checked-in annotated fixture and validated the same load graph with
    stable Bazel 9.1.1 and the patched ty checker.
- Validated transitive typing and goto-definition through two `load()` edges.
- Required sibling overlays to accompany real implementations and required
    explicit assignments for Starlark re-exports.
- Validated resolver invalidation when a stub appears and when its underlying
    implementation disappears.
- Extended mdtest with `bzl` files and migrated Starlark semantic coverage from
    CLI snapshots to literate, multi-file tests.
- Moved target resolution out of semantic indexing so editing a dependency does
    not invalidate the importer's structural index.
- Corrected label resolution to use Bazel repository and package markers.
- Added static load validation and deterministic diagnostics for unresolved
    files and exports.
- Ran adversarial reviews from ty, Bazel/Starlark, Rust performance, Python,
    and general software-design perspectives. Accepted findings on ownership,
    traversal, export semantics, package semantics, diagnostics, and builtin
    isolation. Deferred external repositories, complete syntax rejection, and
    generated builtins as explicit later milestones.
- Rejected labels that cross nested Bazel package boundaries and aligned IDE
    navigation with inference's explicit re-export requirement.
- Completed the affected-crate clippy pass and an 11-test cross-crate Starlark
    validation run.
