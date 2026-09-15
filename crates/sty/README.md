# Sty

Sty is an unpublished workspace command for a bounded Starlark check.
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

For a `.star` file, supply a host implementing `--sty-graph-v2` and
`--sty-check-v1`.
This works from any directory without a Bazel marker or BUILD file.
`//pkg:file.star` is a Bazel selector; `//abs/path.star` is an absolute
file path. A host built with Bazel needs its own runfiles manifest in
the process environment when launched outside Bazel:

```sh
RUNFILES_MANIFEST_FILE=/abs/bin/deploy_star.runfiles_manifest \
  /abs/ruff/target/debug/sty check \
  --host-checker /abs/bin/deploy_star \
  --input cloud_locations=/abs/locations.json \
  --input engine_clusters=/abs/clusters.json \
  /abs/deploy.star
```

Sty first invokes `--sty-graph-v2 --source ABS` with each named
`--input NAME=ABS`. The host parses the captured UTF-8 source, resolves
custom loads, and returns direct aliases, declarative record forms, and
the native `field` and `struct` intrinsic facts. Sty requires recognized
record semantics and both attested intrinsic behaviors. It checks
source-declared primitive, nominal record, union, and list fields against
known arguments in the root and loaded modules, including dead top level
`if` arms. It reports an argument source span and the related field
declaration span on a known mismatch.

`field(TYPE, default=...)` declarations, `struct` members, attributes,
callback and function bodies, and values computed at runtime remain
unproved. The shared Python parser may also mark a valid host
Starlark form opaque. A clear bounded source pass must then invoke
`--sty-check-v1` with the same source and inputs. The host still owns
its parser, loader, native annotation checks, and runtime checks.
Native v1 rereads files, so keep sources and catalogs stable across
the two invocations; it does not attest one shared source revision.

Relative source and input paths become absolute from the current
directory; already absolute paths keep their spelling. The host
decides when to read named inputs, and an unused input may remain
unopened. Sty captures graph stdout privately and inherits graph
stderr and the process environment. Native check stdout and stderr
are inherited unchanged.

Bazel checks return 0 when clear, 1 for checked problems or opaque
sources, and 2 for invalid invocation or label selection. `.star`
returns 1 for a known source type problem or an opaque source, and 2
for malformed graph facts or Sty setup errors. A failed graph process
relays the host exit code, including its native parser error status.
A clear Sty pass relays the subsequent native host check exit code.
