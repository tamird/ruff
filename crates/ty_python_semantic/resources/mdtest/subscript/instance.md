# Instance subscript

## Successful subscription narrows the receiver

A checked subscription that returns `Never` cannot describe the receiver on normal continuation.
Errors, skipped subscriptions, and caught failures do not establish that fact.

```toml
[environment]
python-version = "3.13"
```

```py
from typing import Any, Callable, Never, overload

class Present:
    def __getitem__(self, key: int) -> int:
        return key

class Absent:
    def __getitem__(self, key: int) -> Never:
        raise KeyError(key)

class Inherited(Present): ...

def statement(value: Present | Absent):
    value[0]
    reveal_type(value)  # revealed: Present

def assignment(value: Present | Absent, key: int):
    result = value[key]
    reveal_type(result)  # revealed: int
    reveal_type(value)  # revealed: Present

def annotated(value: Inherited | Absent):
    result: int = value[0]
    reveal_type(value)  # revealed: Inherited

def iteration(values: list[Present | Absent]):
    for value in values:
        reveal_type(value)  # revealed: Present | Absent
        for item in range(value[0]):
            pass
        reveal_type(value)  # revealed: Present

def skipped(value: Present | Absent, flag: bool):
    flag and value[0]
    reveal_type(value)  # revealed: Present | Absent
    result = value[0] if flag else 0
    reveal_type(value)  # revealed: Present | Absent

def caught(value: Present | Absent):
    try:
        value[0]
        reveal_type(value)  # revealed: Present
    except KeyError:
        reveal_type(value)  # revealed: Present | Absent
    reveal_type(value)  # revealed: Present | Absent

def reassigned(value: Present | Absent):
    value[0]
    value = Absent()
    reveal_type(value)  # revealed: Absent

class Invalid:
    def __getitem__(self, key: str) -> Never:
        raise KeyError(key)

def invalid(value: Present | Invalid):
    value[0]  # error: [invalid-argument-type]
    reveal_type(value)  # revealed: Present | Invalid

class Missing: ...

def missing(value: Present | Missing):
    value[0]  # error: [not-subscriptable]
    reveal_type(value)  # revealed: Present | Missing

class Dynamic:
    def __getitem__(self, key: int) -> Any: ...

def dynamic(value: Present | Dynamic):
    value[0]
    reveal_type(value)  # revealed: Present | Dynamic

class Callback:
    callback: Callable[[], None]
    def __getitem__(self, key: int) -> int:
        self.callback()
        return key

def captured(value: Callback | Absent):
    # A subscription can call reset, so its success concerns the old receiver object.
    def reset():
        nonlocal value
        value = Absent()
    if isinstance(value, Callback):
        value.callback = reset
    value[0]
    reveal_type(value)  # revealed: Callback | Absent

def later_writer(value: Callback | Absent):
    value[0]
    reveal_type(value)  # revealed: Callback | Absent
    def reset():
        nonlocal value
        value = Absent()

def generic_subscription():
    alias = list[int]
    values: alias = []
    reveal_type(values)  # revealed: list[int]

def dependent(values: Present | Absent, flag: bool):
    while flag:
        values[0]
        reveal_type(values)  # revealed: Present
        values = Present() if flag else Absent()
```

## Successful subscription with specialized receivers

```toml
[environment]
python-version = "3.13"
```

```py
from typing import Any, Literal, Never, overload

class Target[T]:
    @overload
    def __getitem__(self: "Target[None]", key: Literal["custom"]) -> Never: ...
    @overload
    def __getitem__(self, key: Literal["custom"]) -> int: ...
    @overload
    def __getitem__(self, key: Literal["default"]) -> int: ...
    def __getitem__(self, key: str) -> int:
        return 0

def custom(value: Target[int] | Target[None]):
    value["custom"]
    reveal_type(value)  # revealed: Target[int]

def default(value: Target[int] | Target[None]):
    value["default"]
    reveal_type(value)  # revealed: Target[int] | Target[None]

def union_key(value: Target[int] | Target[None], key: Literal["custom", "default"]):
    value[key]
    reveal_type(value)  # revealed: Target[int] | Target[None]

def gradual_key(value: Target[int] | Target[None], key: Any):
    value[key]
    reveal_type(value)  # revealed: Target[int] | Target[None]

def loop_key(original: Target[int] | Target[None], flag: bool):
    key: Literal["custom", "default"] = "custom"
    while flag:
        value = original
        value[key]
        reveal_type(value)  # revealed: Target[int] | Target[None]
        key = "default"
```

## Runtime type subscriptions

```toml
[environment]
python-version = "3.13"
```

```py
from typing import Literal, Union

def aliases(bad: int):
    one = Union[int]
    integer = Literal[1]
    string = Literal["x"]
    nested_literal = Literal[Literal[1]]
    nested_type = type[Union[int]]
    local = Literal
    alias = local[1]
    type Generic[T] = list[T]
    specialized = Generic[int]
    doubled = specialized[str]  # error: [not-subscriptable]
    nested = list[bad[0]]  # error: [invalid-type-form]
```

## `__getitem__` unbound

```py
class NotSubscriptable: ...

# snapshot: not-subscriptable
a = NotSubscriptable()[0]
```

```snapshot
error[not-subscriptable]: Cannot subscript object of type `NotSubscriptable` with no `__getitem__` method
 --> src/mdtest_snippet.py:4:5
  |
4 | a = NotSubscriptable()[0]
  |     ^^^^^^^^^^^^^^^^^^^^^
```

## Missing methods with union keys

A missing subscript method is reported once for each receiver type, regardless of how many key
alternatives are checked. Separate expressions and key-specific failures retain their diagnostics.

```py
from typing import Literal

class Missing: ...

class Present:
    def __getitem__(self, key: int) -> str:
        return ""

def missing(value: None, key: int | str):
    value[key]  # error: [not-subscriptable]
    value[key]  # error: [not-subscriptable]

def distinct_receivers(value: Missing | None, key: int | str):
    # error: [not-subscriptable] "object of type `Missing`"
    # error: [not-subscriptable] "object of type `None`"
    value[key]

def class_method(key: int | str):
    Missing[key]  # error: [not-subscriptable] "no `__class_getitem__` method"

def recovery(value: Present | None, key: Literal[0, 1]):
    # error: [not-subscriptable]
    reveal_type(value[key])  # revealed: str | Unknown

def invalid_keys(value: Present, key: str | bytes):
    # error: [invalid-argument-type] "key of type `str`"
    # error: [invalid-argument-type] "key of type `bytes`"
    value[key]
```

## `__getitem__` not callable

```py
class NotSubscriptable:
    __getitem__ = None

# TODO: this would be more user-friendly if the `call-non-callable` diagnostic was
# transformed into a `not-subscriptable` diagnostic with a subdiagnostic explaining
# that this was because `__getitem__` was possibly not callable
#
# error: [call-non-callable] "Method `__getitem__` of type `None | Unknown` may not be callable on object of type `NotSubscriptable`"
a = NotSubscriptable()[0]
```

## Valid `__getitem__`

```py
class Identity:
    def __getitem__(self, index: int) -> int:
        return index

reveal_type(Identity()[0])  # revealed: int
```

## Slice bounds for user-defined `__getitem__`

```py
class IntegerSlices:
    def __getitem__(self, key: slice[int | None, int | None, int | None]) -> str:
        return ""

class ArbitrarySlices:
    def __getitem__(self, key: slice) -> str:
        return ""

def _(
    integer_slices: IntegerSlices,
    arbitrary_slices: ArbitrarySlices,
    bound: object,
    invalid_bound: float,
) -> None:
    integer_slices[invalid_bound:]  # error: [invalid-argument-type]
    arbitrary_slices[bound:bound:bound]
```

## `__getitem__` union

```py
def _(flag: bool):
    class Identity:
        if flag:
            def __getitem__(self, index: int) -> int:
                return index

        else:
            def __getitem__(self, index: int) -> str:
                return str(index)

    reveal_type(Identity()[0])  # revealed: int | str
```

## Enum complement as overloaded `__getitem__` receiver

`overloaded.pyi`:

```pyi
from enum import Enum
from typing import Literal, overload

class Color(Enum):
    RED = 1
    GREEN = 2
    BLUE = 3

    @overload
    def __getitem__(self: Literal[Color.GREEN], index: int) -> int: ...
    @overload
    def __getitem__(self: Literal[Color.BLUE], index: int) -> str: ...
```

```py
from overloaded import Color

def _(color: Color):
    if color is Color.RED:
        return
    reveal_type(color[0])  # revealed: int | str
```

## Enum complement as overloaded subscript mutation receiver

`overloaded.pyi`:

```pyi
from enum import Enum
from typing import Literal, overload

class Color(Enum):
    RED = 1
    GREEN = 2
    BLUE = 3

    @overload
    def __setitem__(self: Literal[Color.GREEN], index: int, value: int) -> None: ...
    @overload
    def __setitem__(self: Literal[Color.BLUE], index: int, value: int) -> None: ...
    @overload
    def __delitem__(self: Literal[Color.GREEN], index: int) -> None: ...
    @overload
    def __delitem__(self: Literal[Color.BLUE], index: int) -> None: ...
```

```py
from typing import Literal

from overloaded import Color

def narrowed(color: Color):
    if color is Color.RED:
        return
    color[0] = 1
    del color[0]

def explicit(color: Literal[Color.GREEN, Color.BLUE]):
    color[0] = 1
    del color[0]
```

## `__getitem__` with invalid index argument

```py
class Identity:
    def __getitem__(self, index: int) -> int:
        return index

a = Identity()
# error: [invalid-argument-type] "Method `__getitem__` of type `bound method Identity.__getitem__(index: int) -> int` cannot be called with key of type `Literal["a"]` on object of type `Identity`"
a["a"]
```

## `__setitem__` with no `__getitem__`

```py
class NoGetitem:
    def __setitem__(self, index: int, value: int) -> None:
        pass

a = NoGetitem()
a[0] = 0
```

## Subscript store with no `__setitem__`

```py
class NoSetitem: ...

a = NoSetitem()
a[0] = 0  # error: "Cannot assign to a subscript on an object of type `NoSetitem`"
```

## `__setitem__` not callable

```py
class NoSetitem:
    __setitem__ = None

a = NoSetitem()
a[0] = 0  # error: "Method `__setitem__` of type `None | Unknown` may not be callable on object of type `NoSetitem`"
```

## Valid `__setitem__` method

```py
class Identity:
    def __setitem__(self, index: int, value: int) -> None:
        pass

a = Identity()
a[0] = 0
```

## `__setitem__` with invalid index argument

```py
class Identity:
    def __setitem__(self, index: int, value: int) -> None:
        pass

a = Identity()
# error: [invalid-assignment] "Invalid subscript assignment with key of type `Literal["a"]` and value of type `Literal[0]` on object of type `Identity`"
a["a"] = 0
```
