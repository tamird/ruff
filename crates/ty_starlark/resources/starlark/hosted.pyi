class _Typing:
    Any = _Any
    Never = _Never
    Callable = _Callable
    Iterable = _Iterable

typing: _Typing

__all__ = [
    "all",
    "any",
    "bool",
    "dict",
    "enum",
    "fail",
    "float",
    "int",
    "isinstance",
    "len",
    "list",
    "set",
    "sorted",
    "str",
    "tuple",
    "type",
    "typing",
]

class type:
    def __or__(self, other: object, /) -> object: ...
    def __ror__(self, other: object, /) -> object: ...
    def __new__(cls, value: object, /) -> str: ...

class _GenericType:
    def __class_getitem__(cls, item: object, /) -> object: ...

class int(_Int):
    def __new__(cls, value: int | float | bool | str = 0, /, base: int = 0) -> int: ...

class str(_String):
    def split(
        self, sep: str | None = None, maxsplit: int | None = None, /
    ) -> list[str]: ...
    def strip(self, chars: str = ..., /) -> str: ...

class dict[K, V](_Dict[K, V]):
    @_overload
    def get(self, key: K, /) -> V | None: ...
    @_overload
    def get[D](self, key: K, default: D, /) -> V | D: ...

def isinstance(value: object, types: object, /) -> bool: ...
def sorted[T](
    values: _Iterable[T], /, *, key: _Callable[[T], object] = ..., reverse: bool = False
) -> list[T]: ...
def fail(*args: object) -> _Never: ...
def enum(*values: str) -> _Any: ...
