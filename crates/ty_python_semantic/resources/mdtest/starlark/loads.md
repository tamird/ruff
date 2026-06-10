# Starlark loads

## Direct and renamed loads

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

The implementation's annotation is deliberately wrong for the caller. The sibling stub re-exports
the correctly typed function from another Starlark file, proving both stub precedence and Starlark
re-export semantics.

`stub_defs.bzl`:

```bzl
def accepts_int(value: int) -> None:
    pass
```

`defs.bzl`:

```bzl
def accepts_int(value: str) -> None:
    pass
```

`defs.bzl.pyi`:

```pyi
load("//:stub_defs.bzl", "accepts_int")
```

`main.bzl`:

```bzl
load("//:defs.bzl", "accepts_int")

accepts_int("bad")  # error: [invalid-argument-type]
```

## Project builtins

`__builtins__.pyi`:

```pyi
def fail(message: str) -> None: ...
```

`main.bzl`:

```bzl
fail(1)  # error: [invalid-argument-type]
```

## Transitive loads

`defs.bzl`:

```bzl
def accepts_int(value: int) -> None:
    pass
```

`reexports.bzl`:

```bzl
load("//:defs.bzl", "accepts_int")
```

`main.bzl`:

```bzl
load("//:reexports.bzl", "accepts_int")

accepts_int("bad")  # error: [invalid-argument-type]
```
