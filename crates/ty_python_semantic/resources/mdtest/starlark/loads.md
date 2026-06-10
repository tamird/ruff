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
