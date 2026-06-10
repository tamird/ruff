# Starlark loads

## Direct and renamed loads

`MODULE.bazel`:

```text
module(name = "test")
```

`BUILD.bazel`:

```text
# Package marker.
```

`defs.bzl`:

```bzl
def accepts_int(value: int) -> None:
    pass
```

`main.bzl`:

```bzl
"""Module documentation."""

load("//:defs.bzl", "accepts_int", renamed = "accepts_int")

accepts_int("bad")  # error: [invalid-argument-type]
renamed("also bad")  # error: [invalid-argument-type]
```

## Sibling stubs

The implementation's annotation is deliberately wrong for the caller, proving that the sibling stub
takes precedence.

`MODULE.bazel`:

```text
module(name = "test")
```

`BUILD.bazel`:

```text
# Package marker.
```

`defs.bzl`:

```bzl
def accepts_int(value: str) -> None:
    pass
```

`defs.bzl.pyi`:

```pyi
def accepts_int(value: int) -> None: ...
```

`main.bzl`:

```bzl
load("//:defs.bzl", "accepts_int")

accepts_int("bad")  # error: [invalid-argument-type]
```

## Invalid load statements

`MODULE.bazel`:

```text
module(name = "test")
```

`BUILD.bazel`:

```text
# Package marker.
```

`missing_label.bzl`:

```bzl
load()  # error: [invalid-starlark-load]
```

`invalid_label.bzl`:

```bzl
load(1, "value")  # error: [invalid-starlark-load]
```

`missing_binding.bzl`:

```bzl
load("//:defs.bzl")  # error: [invalid-starlark-load]
```

`invalid_binding.bzl`:

```bzl
load("//:defs.bzl", value)  # error: [invalid-starlark-load]
```

`private_symbol.bzl`:

```bzl
load("//:defs.bzl", "_private")  # error: [invalid-starlark-load]
```

`duplicate_binding.bzl`:

```bzl
load("//:defs.bzl", "value", value = "other")  # error: [invalid-starlark-load]
```

`nested.bzl`:

```bzl
def f():
    load("//:defs.bzl", "value")  # error: [invalid-starlark-load]
```

`late.bzl`:

```bzl
value = 1
load("//:defs.bzl", "other")  # error: [invalid-starlark-load]
```

## Unresolved loads

`MODULE.bazel`:

```text
module(name = "test")
```

`BUILD.bazel`:

```text
# Package marker.
```

`defs.bzl`:

```bzl
value: int = 1
```

`missing_file.bzl`:

```bzl
load("//:missing.bzl", "value")  # error: [unresolved-import]
```

`missing_symbol.bzl`:

```bzl
load("//:defs.bzl", "missing")  # error: [unresolved-import]
```

`reexports.bzl`:

```bzl
load("//:defs.bzl", "value")
```

`implicit_reexport.bzl`:

```bzl
load("//:reexports.bzl", "value")  # error: [unresolved-import]
```

## Load cycles terminate

`MODULE.bazel`:

```text
module(name = "test")
```

`BUILD.bazel`:

```text
# Package marker.
```

`a.bzl`:

```bzl
load("//:b.bzl", "b")

a = b
```

`b.bzl`:

```bzl
load("//:a.bzl", "a")

b = a
```

## Project builtins

`MODULE.bazel`:

```text
module(name = "test")
```

`BUILD.bazel`:

```text
# Package marker.
```

`__builtins__.pyi`:

```pyi
def fail(message: str) -> None: ...
```

`main.bzl`:

```bzl
fail(1)  # error: [invalid-argument-type]
```

## Explicit re-exports

`MODULE.bazel`:

```text
module(name = "test")
```

`BUILD.bazel`:

```text
# Package marker.
```

`defs.bzl`:

```bzl
def accepts_int(value: int) -> None:
    pass
```

`reexports.bzl`:

```bzl
load("//:defs.bzl", _accepts_int = "accepts_int")

accepts_int = _accepts_int
```

`main.bzl`:

```bzl
load("//:reexports.bzl", "accepts_int")

accepts_int("bad")  # error: [invalid-argument-type]
```
