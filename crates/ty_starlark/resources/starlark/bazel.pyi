from typing import Literal as _Literal

__all__ = [
    "abs",
    "all",
    "any",
    "bool",
    "dict",
    "dir",
    "enumerate",
    "fail",
    "float",
    "getattr",
    "hasattr",
    "hash",
    "int",
    "len",
    "list",
    "max",
    "min",
    "print",
    "range",
    "repr",
    "reversed",
    "set",
    "sorted",
    "str",
    "tuple",
    "type",
    "zip",
]

class type:
    def __new__(cls, value: object, /) -> str: ...

class _GenericType: ...

class int(_Int):
    @_overload
    def __new__(cls, value: str, /, base: int = 10) -> int: ...
    @_overload
    def __new__(cls, value: int | float | bool, /) -> int: ...

class str(_String):
    def split(self, /, sep: str, maxsplit: int = ...) -> list[str]: ...
    def strip(self, chars: str | None = None, /) -> str: ...

class dict[K, V](_Dict[K, V]):
    @_overload
    def get(self, key: K, /) -> V | None: ...
    @_overload
    def get[D](self, key: K, /, default: D) -> V | D: ...

def sorted[T](
    values: _Iterable[T],
    /,
    key: _Callable[[T], object] | None = None,
    *,
    reverse: bool = False,
) -> list[T]: ...
def fail(
    *args: object, msg: object = None, attr: str | None = None, sep: str = " "
) -> _Never: ...

# Bazel 9's MethodLibrary defines these modes and result containers:
# https://github.com/bazelbuild/bazel/blob/9.0.0/src/main/java/net/starlark/java/eval/MethodLibrary.java
@_overload
def abs(x: int, /) -> int: ...
@_overload
def abs(x: float, /) -> float: ...
def dir(x: object, /) -> list[str]: ...
def enumerate[T](list: _Iterable[T], start: int = 0) -> list[tuple[int, T]]: ...
def getattr(x: object, name: str, default: object = ..., /) -> _Any: ...
def hasattr(x: object, name: str, /) -> bool: ...
def hash(value: str, /) -> int: ...
def print(*args: object, sep: str = " ") -> None: ...
def repr(x: object, /) -> str: ...
def reversed[T](sequence: _Iterable[T], /) -> list[T]: ...
@_overload
def min[T](
    values: _Iterable[T], /, *, key: _Callable[[T], object] | None = None
) -> T: ...
@_overload
def min[T](
    first: T, second: T, /, *rest: T, key: _Callable[[T], object] | None = None
) -> T: ...
@_overload
def max[T](
    values: _Iterable[T], /, *, key: _Callable[[T], object] | None = None
) -> T: ...
@_overload
def max[T](
    first: T, second: T, /, *rest: T, key: _Callable[[T], object] | None = None
) -> T: ...
@_overload
def zip() -> list[tuple[()]]: ...
@_overload
def zip[T](first: _Iterable[T], /) -> list[tuple[T]]: ...
@_overload
def zip[T, U](first: _Iterable[T], second: _Iterable[U], /) -> list[tuple[T, U]]: ...
@_overload
def zip(*args: _Iterable[_Any]) -> list[tuple[_Any, ...]]: ...

# RangeList is immutable; slicing preserves a range rather than making a list.
class range:
    @_overload
    def __new__(cls, stop: int, /) -> range: ...
    @_overload
    def __new__(cls, start: int, stop: int, step: int = 1, /) -> range: ...
    def __iter__(self) -> _Iterator[int]: ...
    def __len__(self) -> int: ...
    @_overload
    def __getitem__(self, index: int, /) -> int: ...
    @_overload
    def __getitem__(self, index: slice, /) -> range: ...
    def __contains__(self, value: object, /) -> bool: ...

# Bazel globals are selected per file by the frontend, not listed in __all__.
# https://bazel.build/versions/9.0.0/rules/lib/globals/build
# https://bazel.build/versions/9.0.0/reference/be/general
_BazelLabels = list[str] | tuple[str, ...]

class _BazelSelector[T]:
    # Selectors are immutable. Keep T covariant so different branch container
    # types can be converted to the same attribute type by Bazel.
    @_overload
    def __add__(
        self: _BazelSelector[_BazelLabels],
        other: _BazelLabels | _BazelSelector[_BazelLabels],
        /,
    ) -> _BazelSelector[T]: ...
    @_overload
    def __add__(
        self: _BazelSelector[str], other: str | _BazelSelector[str], /
    ) -> _BazelSelector[T]: ...
    @_overload
    def __radd__(
        self: _BazelSelector[_BazelLabels], other: _BazelLabels, /
    ) -> _BazelSelector[T]: ...
    @_overload
    def __radd__(self: _BazelSelector[str], other: str, /) -> _BazelSelector[T]: ...

# None in a select branch requests the attribute's default value.
_BazelConfigurableLabels = _BazelLabels | _BazelSelector[_BazelLabels | None]
_BazelConfigurableString = str | _BazelSelector[str | None]
# Type.BOOLEAN also converts integer literals 0 and 1 for rule/package attributes.
# https://github.com/bazelbuild/bazel/blob/9.0.0/src/main/java/com/google/devtools/build/lib/packages/Type.java
_BazelBool = bool | _Literal[0, 1]
_BazelConfigurableBool = _BazelBool | _BazelSelector[_BazelBool | None]
_BazelConfigurableDict = dict[str, str] | _BazelSelector[dict[str, str] | None]

def glob(
    include: _BazelLabels = ...,
    exclude: _BazelLabels = ...,
    exclude_directories: int = 1,
    allow_empty: bool = ...,
) -> list[str]: ...
def select[T](x: dict[str, T], /, no_match_error: str = "") -> _BazelSelector[T]: ...
def package(
    *,
    default_deprecation: str = "",
    default_package_metadata: _BazelLabels = ...,
    default_applicable_licenses: _BazelLabels = ...,
    default_testonly: _BazelBool = False,
    default_visibility: _BazelLabels = ...,
    features: _BazelLabels = ...,
) -> None: ...
def exports_files(
    srcs: _BazelLabels,
    visibility: _BazelLabels | None = None,
    licenses: _BazelLabels | None = None,
) -> None: ...
def filegroup(
    *,
    name: str,
    srcs: _BazelConfigurableLabels = ...,
    data: _BazelConfigurableLabels = ...,
    aspect_hints: _BazelConfigurableLabels = ...,
    compatible_with: _BazelLabels = ...,
    deprecation: str = "",
    features: _BazelConfigurableLabels = ...,
    licenses: _BazelLabels = ...,
    output_group: _BazelConfigurableString = "",
    package_metadata: _BazelLabels = ...,
    restricted_to: _BazelLabels = ...,
    visibility: _BazelLabels = ...,
    tags: _BazelLabels = ...,
    target_compatible_with: _BazelConfigurableLabels = ...,
    testonly: _BazelBool = False,
) -> None: ...
def genrule(
    *,
    name: str,
    outs: _BazelLabels,
    srcs: _BazelConfigurableLabels = ...,
    tools: _BazelConfigurableLabels = ...,
    aspect_hints: _BazelConfigurableLabels = ...,
    cmd: _BazelConfigurableString = "",
    cmd_bash: _BazelConfigurableString = "",
    cmd_bat: _BazelConfigurableString = "",
    cmd_ps: _BazelConfigurableString = "",
    compatible_with: _BazelLabels = ...,
    deprecation: str = "",
    exec_compatible_with: _BazelLabels = ...,
    exec_group_compatible_with: dict[str, _BazelLabels] = ...,
    exec_properties: _BazelConfigurableDict = ...,
    message: _BazelConfigurableString = "",
    local: _BazelConfigurableBool = False,
    executable: _BazelBool = False,
    features: _BazelConfigurableLabels = ...,
    licenses: _BazelLabels = ...,
    output_licenses: _BazelConfigurableLabels = ...,
    output_to_bindir: _BazelBool = False,
    package_metadata: _BazelLabels = ...,
    restricted_to: _BazelLabels = ...,
    visibility: _BazelLabels = ...,
    tags: _BazelLabels = ...,
    target_compatible_with: _BazelConfigurableLabels = ...,
    testonly: _BazelBool = False,
    toolchains: _BazelLabels = ...,
) -> None: ...
