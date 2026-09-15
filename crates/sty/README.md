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

For a `.star` file, supply an executable checker that implements the v1
host process interface. This mode works from any directory and requires
no Bazel marker or BUILD file. It rejects Bazel selectors such as
`//pkg:file.star`, while `//abs/path.star` is an absolute file path:

```sh
/abs/ruff/target/debug/sty check \
  --host-checker /abs/bin/deploy_star \
  --input locations=/abs/locations.json \
  --input clusters=/abs/clusters.json \
  /abs/deploy.star
```

Sty invokes the executable with `--sty-check-v1 --source ABS` and each
`--input NAME=ABS`. Relative source and input paths become absolute from
the current directory; already absolute paths keep their spelling. The
host parses `.star`, resolves its loads, and decides when to read named
inputs. An unused input may remain unopened.

Sty inherits the process environment, stdout, and stderr and relays the
host exit code. A Bazel-built host may need `RUNFILES_MANIFEST_FILE` set
to its own adjacent runfiles manifest when launched outside Bazel.

Bazel checks return 0 when clear, 1 for checked problems or opaque
sources, and 2 for invalid invocation or label selection. Host checks
return the executable's exit code; setup errors return 2.
