# Sets

## Basic set

```py
reveal_type({1, 2})  # revealed: set[int]
```

## Set of tuples

```py
reveal_type({(1, 2), (3, 4)})  # revealed: set[tuple[int, int]]
```

## Set of functions

```py
def a(_: int) -> int:
    return 0

def b(_: int) -> int:
    return 1

x = {a, b}
reveal_type(x)  # revealed: set[(_: int) -> int]
```

## Mixed set

```py
# revealed: set[int | tuple[int, ...]]
reveal_type({1, (1, 2), (1, 2, 3)})
```

## Set comprehensions

```py
reveal_type({x for x in range(42)})  # revealed: set[int]
```

## Context from later uses

### Invalid writes and aliases

```py
def consume(values: set[str]) -> None: ...
def later() -> set[str]:
    result = set()
    result.add(42)  # error: [invalid-argument-type]
    consume(result)
    return result

def alias(values: set[str]) -> None:
    saved = values
    saved.add(42)  # error: [invalid-argument-type]
```

### Explicit Hashable element type

A `Hashable` element annotation rejects mutable lists.

```py
from collections.abc import Hashable

def later() -> set[Hashable]:
    result = set()
    result.add([])  # error: [invalid-argument-type]
    return result
```
