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

For a `.star` file, supply a host implementing `--sty-graph-v3` and
`--sty-check-v1`. This works from any directory without a Bazel marker
or BUILD file.
`//pkg:file.star` is a Bazel selector; `//abs/path.star` is an absolute
file path. A host built with Bazel needs its own runfiles manifest in
the process environment when launched outside Bazel:

```sh
RUNFILES_MANIFEST_FILE=/abs/bin/starlark_host.runfiles_manifest \
  /abs/ruff/target/debug/sty check \
  --host-checker /abs/bin/starlark_host \
  --input catalog=/abs/catalog.json \
  /abs/deploy.star
```

The host decides which named inputs to accept; supply further
`--input NAME=ABS` pairs when its invocation requires them.

Sty first invokes `--sty-graph-v3 --source ABS` with each named
`--input NAME=ABS`. The host parses the captured UTF-8 source, resolves
custom loads, and returns direct aliases, declarative record forms,
native `field` and `struct` intrinsic facts, and an inventory of host
functions. Sty requires recognized record semantics and well-formed
intrinsic and host function facts. It checks source-declared primitive,
nominal record, union, and list fields against
known arguments in the root and loaded modules, including dead top level
`if` arms. It reports an argument source span and the related field
type span on a known mismatch. With the attested `field` intrinsic,
Sty reads the first positional type expression in a source declaration
such as `record(value=field(int, default=7))`. Positional defaults
work the same way. Unknown type expressions and shadowed native names
stay unproved.

Sty also follows source `struct` members that refer to known record
constructors or other proven `struct` bindings, including through
resolved loads. Members computed at runtime stay unproved. The native
checker validates field defaults and missing required fields.

When a top level name has one assignment, Sty can carry a scalar value
or proven nominal record instance through a load, alias, or direct
function body. An instance supplies an argument type but never an
annotation type. Mutable lists and arbitrary computed or catalog values
stay unproved.

For a validated v3 graph, Sty also follows stable source `def` bindings and
checks their known regular positional and named parameter annotations,
including functions exported through `struct` and resolved loads. A
known return annotation can supply a type when the call supplies every
named or positional parameter and every established parameter type
matches a known argument. A nominal record result requires complete
known field declarations and compatible named arguments for every
field. Typed `def` semantics come from the
host's Starlark language and native annotation checks; the intrinsic
facts attest `field` and `struct` only. Parameter defaults, requiredness,
computed attributes, and unrecognized type aliases remain the host's
responsibility or unproved when analyzing source function call arguments.
Sty checks known calls inside direct source
function defaults in eager source order, then checks direct function
bodies using stable final module bindings while excluding function
parameters and local names. Nested functions, lambdas, and
comprehensions await their own proven scope. With v3 host function facts,
Sty also checks known scalar and callable arguments of direct native
global calls. It uses the host's ordered positional and named modes,
required parameters, and evaluator availability before proving a call.
A typed native return can supply an argument type when the call has a
valid parameter mapping and no known wrong inputs. Native returns of
`any` or `unknown`, computed callbacks, and shadowed names stay unproved.
A direct unshadowed native call in the source root is an error when
the host attests that its function requires loaded module initialization.
Sty shows the captured callee span and textual host availability. A
loaded deferred function might execute during initialization or later,
so its availability stays unproved. A known native mismatch shows the
captured argument span and a textual host signature; the graph has no
native declaration source span. Definite native call shape errors,
including a missing required parameter and a positional argument for
a named-only parameter, use the captured call or argument span and the
same host signature. Starred and dynamic keyword arguments have no
stable mapping and stay unproved. The shared Python parser may
mark valid host Starlark syntax opaque. A clear bounded source pass invokes
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
