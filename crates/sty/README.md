# Sty

Sty is an unpublished workspace command for a bounded Starlark check.
See [the architecture and migration plan](ARCHITECTURE.md) for ownership
boundaries and the planned reuse of Ty's semantic analysis.

Build it once from the Ruff checkout:

```sh
cargo build -p sty --locked
```

Run the built executable from a marked Bazel main repository. The direct
`:entry.bzl` example runs from the target package directory with BUILD:

```sh
cd /abs/repo
/abs/ruff/target/debug/sty check //pkg:entry.bzl //shared:defs.bzl
cd pkg
/abs/ruff/target/debug/sty check :entry.bzl
/abs/ruff/target/debug/sty check --workspace /abs/repo //pkg:entry.bzl
```

Sty selects the nearest Bazel repository marker unless `--workspace`
chooses another marked root. A direct `:entry.bzl` label requires a BUILD
file in the exact current directory. Runtime sources use `.bzl`; Ty-only
primitive signatures may live in the matching sibling `.bzl.pyi`. Sty
checks every selected source and its load dependencies. Its bounded
parser also marks valid Starlark forms outside the shared Python parser
subset opaque. Unsupported source semantics and uncheckable stubs are
opaque, and opaque sources cause a nonzero exit.

Command diagnostics use Ruff's renderer, with source snippets, diagnostic
codes, and related declarations. The editor uses the same diagnostics and
codes. Host source snippets and editor ranges refer to the captured source
text, including unsaved changes.

`sty server` checks open `.bzl` and sibling `.bzl.pyi` files in a marked
repository without Sty configuration. It uses unsaved editor text and
rechecks importers when an opened load, BUILD file, or repository marker
changes. Open loaded files through the same repository path used by
their Bazel loads. If an opened file uses a different symlink path,
the importer may instead read that source from disk; its diagnostics
can then be stale relative to the unsaved editor text.

Register `/abs/ruff/target/debug/sty server` as a stdio LSP command for
`.bzl`, `.bzl.pyi`, and `.star` filetypes. Sty currently publishes
diagnostics and related source locations; it does not provide hover,
completion, or navigation. Opened and changed buffers recheck directly.
The client may also send `workspace/didChangeWatchedFiles` for changes
on disk; Sty does not register file-watch patterns itself, so configure
external file watches in the editor when needed.

For `.star`, pass the host and selected source roots in the editor's
LSP initialization options. A loaded `.star` file opened alone is
checked through the configured root's private loader. For example:

```json
{
  "hostSources": [
    {
      "root": "/abs/monorepo/service/manage/deploy.star",
      "checker": "/abs/bin/project/deploy_star/deploy_star",
      "runfilesManifest": "/abs/bin/project/deploy_star/deploy_star.runfiles_manifest",
      "inputs": {}
    }
  ]
}
```

Use absolute paths for roots, checker, manifest, and any named input
paths. A host must implement `--sty-graph-v3 --sty-overlays-stdin` and
the `sty-star-overlays-v1` stdin protocol to check unsaved buffers.
The host's loader locates physically existing sources and resolves its
private loads; Sty checks captured text and host facts without running
native checks or deployment evaluation. An opened `.star` without a
configured host root receives a setup diagnostic.

For a `.star` file, supply a host implementing `--sty-graph-v3`. This
works from any directory without a Bazel marker or BUILD file.
`//pkg:file.star` is a Bazel selector; `//abs/path.star` is an absolute
file path. A host built with Bazel needs its own runfiles manifest in
the process environment when launched outside Bazel:

```sh
RUNFILES_MANIFEST_FILE=/abs/bin/starlark_host.runfiles_manifest \
  /abs/ruff/target/debug/sty check \
  --host-checker /abs/bin/starlark_host \
  /abs/deploy.star
```

The host decides which named inputs to accept; supply further
`--input NAME=ABS` pairs only when its graph invocation requires them.

Sty first invokes `--sty-graph-v3 --source ABS` with each named
`--input NAME=ABS`. The host parses the captured UTF-8 source, resolves
custom loads, and returns direct aliases, declarative record forms,
native `field` and `struct` intrinsic facts, and an inventory of host
functions. Sty requires recognized record semantics and well-formed
intrinsic and host function facts.

Admitted graphs use Ty's semantic engine. It checks annotated function
bodies and returns, positional and named arguments, defaults, required
parameters, and calls in unreachable code. Resolved loads retain their
original aliases and source locations. An explicit assignment can
reexport a loaded binding; a bare load does not reexport it.

Records have nominal identity per logical module and declaration.
Constructors, instance fields, and related diagnostic locations share
the same field definitions. `field(int, default=7)` supplies a type and
optional default, both of which are checked. Unions, lists, and fixed
tuple annotations use Ty's type operations. `struct` preserves known
members, including functions and record constructors, without adding
Python method receiver binding.

Builtin declarations describe the supported Starlark operations.
Boolean and integer types are distinct, float annotations require
floats, strings require `.elems()` for iteration, and `type(value)`
returns a string. Internal declaration helpers are hidden from source
lookup. Unknown values and unannotated return types limit precision.
Source variadic annotations describe the collected tuple or dictionary.
Correlated unions of those aggregate types are not supported; Sty reports
the unsupported annotation instead of checking arguments independently.

Native calls use the host's declared parameter modes, requiredness,
argument types, and return types. Diagnostics include the host
signature. Calls from the source root are rejected when a native
requires loaded module initialization. A loaded function body might
execute during initialization or later, so that availability remains
unknown; its argument types are still checked.

Sty reads the captured graph without evaluating deployment code or
reading catalogs. The shared Python parser can reject Starlark syntax
outside its supported overlap. The host's runtime checks and
validation of data-dependent behavior remain separate operations.

Relative source and input paths become absolute from the current
directory; already absolute paths keep their spelling. The host
decides when to read named inputs, and an unused input may remain
unopened. Sty captures graph stdout privately and inherits graph
stderr and the process environment.

Bazel checks return 0 when clear, 1 for checked problems or opaque
sources, and 2 for invalid invocation or label selection. `.star`
returns 1 for a known source type problem or an opaque source, and 2
for malformed graph facts or Sty setup errors. A failed graph process
relays the host exit code. Unknown values can prevent a static diagnosis;
runtime validation remains the host's responsibility.
