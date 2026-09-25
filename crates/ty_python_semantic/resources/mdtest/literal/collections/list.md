# Lists

## Empty list

```py
reveal_type([])  # revealed: list[Unknown]
```

## List of tuples

```py
reveal_type([(1, 2), (3, 4)])  # revealed: list[tuple[int, int]]
```

## List of functions

```py
def a(_: int) -> int:
    return 0

def b(_: int) -> int:
    return 1

x = [a, b]
reveal_type(x)  # revealed: list[(_: int) -> int]
```

The inferred `Callable` type is function-like, i.e. we can still access attributes like `__name__`:

```py
reveal_type(x[0].__name__)  # revealed: str
```

## Mixed list

```py
# revealed: list[int | tuple[int, ...]]
reveal_type([1, (1, 2), (1, 2, 3)])
```

## None promotion

`None` is promoted to `None | Unknown` in list literals when it is the only element type, so that
the inferred type does not overly restrict subsequent mutations of the list.

```py
from typing import Sequence

reveal_type([None])  # revealed: list[None | Unknown]
reveal_type([1, None])  # revealed: list[int | None]
reveal_type([(None,)])  # revealed: list[tuple[None | Unknown]]
reveal_type([[None], [None]])  # revealed: list[list[None | Unknown]]

x: list[int | None] = [None]
reveal_type(x)  # revealed: list[int | None]

y: list[tuple[int | None, ...]] = [(None,)]
reveal_type(y)  # revealed: list[tuple[int | None, ...]]

z: list[Sequence[int | str | None]] = [(None,), [None], (None, None)]
reveal_type(z)  # revealed: list[Sequence[int | str | None]]

xx: list[None] = reveal_type([None])  # revealed: list[None]
reveal_type(xx)  # revealed: list[None]

yy = reveal_type([None])  # revealed: list[None | Unknown]
reveal_type(yy)  # revealed: list[None | Unknown]

# Bare `list` in a type expression is equivalent to `list[Unknown]`
zz: list = [None]  # error: [missing-type-argument]
reveal_type(zz)  # revealed: list[Unknown]

# Promotion only happens if we're in invariant contexts,
# same as with `Literal` types:
reveal_type((1, 2, None))  # revealed: tuple[Literal[1], Literal[2], None]
reveal_type(((((None,),),),))  # revealed: tuple[tuple[tuple[tuple[None]]]]
reveal_type((((([None],),),),))  # revealed: tuple[tuple[tuple[tuple[list[None | Unknown]]]]]

class Foo:
    def __init__(self):
        self.mylist = [None, None, None]

    def method(self):
        self.mylist[0] = 42

reveal_type(Foo().mylist)  # revealed: list[None | Unknown]
```

## List comprehensions

```py
reveal_type([x for x in range(42)])  # revealed: list[int]
```

## Non-generic protocol context

A protocol can provide the element type of a list literal through its method contracts, including
when the protocol itself has no type parameters.

```py
from typing import Protocol, TypeAlias, TypedDict

class Row(TypedDict):
    value: int

class Rows(Protocol):
    def __getitem__(self, index: int, /) -> Row: ...

typed: list[Row] = [{"value": 1}]
forwarded: Rows = typed
literal: Rows = [{"value": 1}]

Alias: TypeAlias = Rows
aliased: Alias = [{"value": 1}]
union: Rows | list[str] = [{"value": 1}]
other_arm: Rows | list[str] = ["value"]

# error: [invalid-assignment]
# error: [invalid-argument-type]
wrong: Rows = [{"value": "bad"}]
# error: [invalid-assignment]
# error: [missing-typed-dict-key]
missing: Rows = [{}]
# error: [invalid-assignment]
# error: [invalid-key]
hidden: Rows = [{"value": 1, "hidden": 2}]

class KeywordRows(Protocol):
    def __getitem__(self, index: int) -> Row: ...

# The list does not accept an index supplied by keyword.
# error: [invalid-assignment]
keyword: KeywordRows = typed
```
