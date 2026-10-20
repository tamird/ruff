# Singleton elements in mutable collections

## Default widening

An annotation on the element does not constrain future additions to its collection. An annotation on
the collection does.

```py
value: None = None
reveal_type({"marker": value})  # revealed: dict[str, None | Unknown]
markers: dict[str, None] = {"marker": value}
reveal_type(markers)  # revealed: dict[str, None]
```

## Exact inference

```toml
[analysis]
widen-singleton-collection-elements = false
```

```py
from typing import Any

reveal_type({"marker": None})  # revealed: dict[str, None]
reveal_type({key: None for key in ["marker"]})  # revealed: dict[str, None]
reveal_type([None])  # revealed: list[None]
reveal_type({None})  # revealed: set[None]
(*rest,) = (None,)
reveal_type(rest)  # revealed: list[None]

direct = {"marker": None}
direct["marker"] = 1
reveal_type(direct)  # revealed: dict[str, int | None]

original = {"marker": None}
alias = original
alias["marker"] = 1  # error: [invalid-assignment]

def dynamic(value: Any):
    reveal_type({"marker": value})  # revealed: dict[str, Any]
```
