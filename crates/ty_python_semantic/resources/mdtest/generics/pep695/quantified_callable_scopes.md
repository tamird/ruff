# Independent specializations of generic callbacks

Separate comparisons of a generic callback choose independent specializations. Each comparison
retains the relationship between its input and result.

```toml
[environment]
python-version = "3.13"
```

## Callable arguments

```py
from typing import Callable

def identity[T](value: T, /) -> T:
    return value

def pair[A, B](first: Callable[[str], A], second: Callable[[bytes], B]) -> tuple[A, B]:
    raise NotImplementedError

reveal_type(pair(identity, identity))  # revealed: tuple[str, bytes]
result: tuple[str, bytes] = pair(identity, identity)

def integers(value: int, /) -> int:
    return value

pair(identity, integers)  # error: [invalid-argument-type]
```

## Overloaded protocol comparisons

```py
from typing import Protocol, overload

class StringOrBytes[A, B](Protocol):
    @overload
    def __call__(self, value: str, /) -> A: ...
    @overload
    def __call__(self, value: bytes, /) -> B: ...

def identity[T](value: T, /) -> T:
    return value

def infer[A, B](callback: StringOrBytes[A, B]) -> tuple[A, B]:
    raise NotImplementedError

reveal_type(infer(identity))  # revealed: tuple[str, bytes]
result: tuple[str, bytes] = infer(identity)
```

## Finite witnesses retain both outputs

A single callback comparison keeps its scalar and list element specialization together.

```py
from typing import Callable

def make[T: (int, str)]() -> tuple[T, list[T]]:
    raise NotImplementedError

def combine[A, B](callback: Callable[[], tuple[A, list[B]]], sink: Callable[[A, list[B]], None]) -> None:
    pass

def integers(value: int, values: list[int]) -> None:
    pass

def strings(value: str, values: list[str]) -> None:
    pass

def mixed(value: int, values: list[str]) -> None:
    pass

combine(make, integers)
combine(make, strings)
combine(make, mixed)  # error: [invalid-argument-type]
```
