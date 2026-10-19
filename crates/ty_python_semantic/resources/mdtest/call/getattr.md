# `getattr`

## Literal attribute names

Runtime lookup binds methods and invokes descriptors, just like attribute syntax.

```py
from builtins import getattr as lookup

class Example:
    value: int = 1

    def method(self, value: int) -> str:
        return str(value)

    @property
    def text(self) -> str:
        return "text"

def _(example: Example):
    reveal_type(getattr(example, "value"))  # revealed: int
    reveal_type(lookup(example, "text"))  # revealed: str
    reveal_type(getattr(example, "method")(1))  # revealed: str
    # error: [invalid-argument-type]
    getattr(example, "method")("wrong")
```

## Finite attribute alternatives

```toml
[environment]
python-version = "3.12"
```

Every literal name contributes its member type. An unknown alternative keeps the ordinary `getattr`
result.

```py
from typing import Literal

type Names = Literal["number", "text"]

class Example:
    number: int = 1
    text: str = "text"

def _(example: Example, name: Names, missing: Literal["number", "missing"], broad: str):
    reveal_type(getattr(example, name))  # revealed: int | str
    reveal_type(getattr(example, missing))  # revealed: Any
    reveal_type(getattr(example, broad))  # revealed: Any
```

## Defaults and open receivers

A descriptor may raise `AttributeError`, causing `getattr` to return its default even when that
attribute is declared. Supplied defaults remain part of the result.

```py
class Example:
    @property
    def value(self) -> int:
        raise AttributeError("unavailable")

def _(example: Example):
    reveal_type(getattr(example, "value"))  # revealed: int
    reveal_type(getattr(example, "value", None))  # revealed: int | None
```

An undeclared attribute can exist on a subclass. Static lookup failure does not establish that the
default is the only possible result.

```py
class Base: ...

class Child(Base):
    extra: int = 1

def _(value: Base):
    reveal_type(getattr(value, "extra", None))  # revealed: Any | None
    reveal_type(getattr(value, "extra"))  # revealed: Any

class Other: ...

def _(value: Child | Other):
    reveal_type(getattr(value, "extra", None))  # revealed: Any | None
```

## Empty collection defaults

A finite member type provides context for a fresh empty list or dictionary default, including
`Iterable` and `Mapping` fields. This does not establish that the attribute exists or prevent a
property from raising `AttributeError`; the default remains a possible result.

```py
from collections.abc import Iterable, Mapping

class Collections:
    items: list[str]
    iterable: Iterable[str]
    mapping: Mapping[str, Iterable[str]]

    @property
    def unavailable(self) -> list[str]:
        raise AttributeError("unavailable")

def _(value: Collections, fallback: bytes):
    reveal_type(getattr(value, "items", []))  # revealed: list[str]
    reveal_type(getattr(value, "iterable", []))  # revealed: Iterable[str]
    reveal_type(getattr(value, "mapping", {}))  # revealed: Mapping[str, Iterable[str]]
    reveal_type(getattr(value, "unavailable", []))  # revealed: list[str]
    reveal_type(getattr(value, "unavailable", fallback))  # revealed: list[str] | bytes
```

## Typing-only operations

An operation declaration that is unavailable as a runtime attribute does not refine `getattr`.

`operations.pyi`:

```pyi
from typing import type_check_only

class Native:
    @type_check_only
    def __getitem__(self, index: int) -> str: ...
```

`main.py`:

```py
from operations import Native

def _(value: Native):
    reveal_type(getattr(value, "__getitem__", None))  # revealed: Any | None
```

## Shadowed builtin

A function with the same name follows its own declared signature.

```py
def getattr(value: object, name: str) -> bytes:
    return b"custom"

reveal_type(getattr(1, "real"))  # revealed: bytes
```
