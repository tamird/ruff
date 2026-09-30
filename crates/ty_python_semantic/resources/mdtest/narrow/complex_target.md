# Narrowing for complex targets (attribute expressions, subscripts)

We support type narrowing for attributes and subscripts.

## Attribute narrowing

### Basic

```py
from ty_extensions._internal import Unknown

class C:
    x: int | None = None

c = C()

reveal_type(c.x)  # revealed: int | None

if c.x is not None:
    reveal_type(c.x)  # revealed: int
else:
    reveal_type(c.x)  # revealed: None

if c.x is not None:
    c.x = None

reveal_type(c.x)  # revealed: None

c = C()

if c.x is None:
    c.x = 1

reveal_type(c.x)  # revealed: int

class _:
    reveal_type(c.x)  # revealed: int

c = C()

class _:
    if c.x is None:
        c.x = 1
    reveal_type(c.x)  # revealed: int

# TODO: should be `int`
reveal_type(c.x)  # revealed: int | None

class D:
    x = None

def unknown() -> Unknown:
    return 1

d = D()
reveal_type(d.x)  # revealed: None | Unknown
d.x = 1
reveal_type(d.x)  # revealed: Literal[1]
d.x = unknown()
reveal_type(d.x)  # revealed: Unknown

class E:
    x: int | None = None

e = E()

if e.x is not None:
    class _:
        reveal_type(e.x)  # revealed: int
```

Narrowing can be "reset" by assigning to the attribute:

```py
c = C()

if c.x is None:
    reveal_type(c.x)  # revealed: None
    c.x = 1
    reveal_type(c.x)  # revealed: Literal[1]
    c.x = None
    reveal_type(c.x)  # revealed: None

reveal_type(c.x)  # revealed: int | None
```

Narrowing can also be "reset" by assigning to the object:

```py
c = C()

if c.x is None:
    reveal_type(c.x)  # revealed: None
    c = C()
    reveal_type(c.x)  # revealed: int | None

reveal_type(c.x)  # revealed: int | None
```

### Multiple predicates

```py
class C:
    value: str | None

def foo(c: C):
    # The truthiness check `c.value` narrows to `str & ~AlwaysFalsy`.
    # The subsequent `len(c.value)` doesn't narrow further since `str` is not narrowable by len().
    if c.value and len(c.value):  # error: [truthiness-test-of-none-union]
        reveal_type(c.value)  # revealed: str & ~AlwaysFalsy

    # error: [invalid-argument-type] "Argument to function `len` is incorrect: Expected `Sized`, found `str | None`"
    if len(c.value) and c.value:  # error: [truthiness-test-of-none-union]
        reveal_type(c.value)  # revealed: str & ~AlwaysFalsy

    if c.value is None or not len(c.value):
        reveal_type(c.value)  # revealed: str | None
    else:  # c.value is not None and len(c.value)
        # `c.value is not None` narrows to `str`, but `str` is not narrowable by len().
        reveal_type(c.value)  # revealed: str
```

### Generic class

```toml
[environment]
python-version = "3.12"
```

```py
class C[T]:
    x: T
    y: T

    def __init__(self, x: T):
        self.x = x
        self.y = x

def f(a: int | None):
    c = C(a)
    reveal_type(c.x)  # revealed: int | None
    reveal_type(c.y)  # revealed: int | None
    if c.x is not None:
        reveal_type(c.x)  # revealed: int
        # In this case, it may seem like we can narrow it down to `int`,
        # but different values ​​may be reassigned to `x` and `y` in another place.
        reveal_type(c.y)  # revealed: int | None

def g[T](c: C[T]):
    reveal_type(c.x)  # revealed: T@g
    reveal_type(c.y)  # revealed: T@g
    reveal_type(c)  # revealed: C[T@g]

    if isinstance(c.x, int):
        reveal_type(c.x)  # revealed: T@g & int
        reveal_type(c.y)  # revealed: T@g
        reveal_type(c)  # revealed: C[T@g]
    if isinstance(c.x, int) and isinstance(c.y, int):
        reveal_type(c.x)  # revealed: T@g & int
        reveal_type(c.y)  # revealed: T@g & int
        # TODO: Probably better if inferred as `C[T & int]` (mypy and pyright don't support this)
        reveal_type(c)  # revealed: C[T@g]
```

### With intermediate scopes

```py
class C:
    def __init__(self):
        self.x: int | None = None
        self.y: int | None = None

c = C()
reveal_type(c.x)  # revealed: int | None
if c.x is not None:
    reveal_type(c.x)  # revealed: int
    reveal_type(c.y)  # revealed: int | None

if c.x is not None:
    def _():
        reveal_type(c.x)  # revealed: int | None

def _():
    if c.x is not None:
        reveal_type(c.x)  # revealed: int
```

## Subscript narrowing

### Number subscript

```py
def _(t1: tuple[int | None, int | None], t2: tuple[int, int] | tuple[None, None]):
    if t1[0] is not None:
        reveal_type(t1[0])  # revealed: int
        reveal_type(t1[1])  # revealed: int | None

    n = 0
    if t1[n] is not None:
        # Narrowing the individual element type with a non-literal subscript is not supported
        reveal_type(t1[0])  # revealed: int | None
        reveal_type(t1[n])  # revealed: int | None
        reveal_type(t1[1])  # revealed: int | None

    # However, we can still discriminate between tuples in a union using a variable index:
    if t2[n] is not None:
        reveal_type(t2)  # revealed: tuple[int, int]

    if t2[0] is not None:
        reveal_type(t2)  # revealed: tuple[int, int]
        reveal_type(t2[0])  # revealed: int
        reveal_type(t2[1])  # revealed: int
    else:
        reveal_type(t2)  # revealed: tuple[None, None]
        reveal_type(t2[0])  # revealed: None
        reveal_type(t2[1])  # revealed: None

    if t2[0] is None:
        reveal_type(t2)  # revealed: tuple[None, None]
    else:
        reveal_type(t2)  # revealed: tuple[int, int]

    if (first := t2[0]) is not None:
        reveal_type(first)  # revealed: int
        reveal_type(t2)  # revealed: tuple[int, int]
    else:
        reveal_type(first)  # revealed: None
        reveal_type(t2)  # revealed: tuple[None, None]

def _(t3: tuple[int, str] | tuple[None, None] | tuple[bool, bytes]):
    # Narrow to tuples where first element is not None
    if t3[0] is not None:
        reveal_type(t3)  # revealed: tuple[int, str] | tuple[bool, bytes]

    # Narrow to tuples where first element is None
    if t3[0] is None:
        reveal_type(t3)  # revealed: tuple[None, None]

def _(t4: tuple[bool, int] | tuple[bool, str]):
    # Both tuples have bool at index 0, which is not disjoint from True,
    # so neither gets filtered out when checking `is True`
    if t4[0] is True:
        reveal_type(t4)  # revealed: tuple[bool, int] | tuple[bool, str]

def _(t5: tuple[int, None] | tuple[None, int]):
    # Narrow on second element (index 1)
    if t5[1] is not None:
        reveal_type(t5)  # revealed: tuple[None, int]
    else:
        reveal_type(t5)  # revealed: tuple[int, None]

    # Negative index
    if t5[-1] is None:
        reveal_type(t5)  # revealed: tuple[int, None]

def _(t6: tuple[int, ...] | tuple[None, None]):
    # Variadic tuple at index 0 has element type `int` (not a union),
    # so `tuple[None, None]` gets filtered out
    if t6[0] is not None:
        reveal_type(t6)  # revealed: tuple[int, ...]

def _(t6b: tuple[int, ...] | tuple[None, ...]):
    # Both variadic: `int` is disjoint from None, `None` is not disjoint from None
    if t6b[0] is not None:
        reveal_type(t6b)  # revealed: tuple[int, ...]
    else:
        reveal_type(t6b)  # revealed: tuple[None, ...]

def _(t7: tuple[int, int] | tuple[None, None]):
    # Index out of range for both tuples - no narrowing, but errors are emitted
    # error: [index-out-of-bounds] "Index 5 is out of bounds for tuple `tuple[int, int]` with length 2"
    # error: [index-out-of-bounds] "Index 5 is out of bounds for tuple `tuple[None, None]` with length 2"
    if t7[5] is not None:
        reveal_type(t7)  # revealed: tuple[int, int] | tuple[None, None]

def _(t8: tuple[int, int, int] | tuple[None, None]):
    # Index in range for first tuple but out of range for second
    # error: [index-out-of-bounds] "Index 2 is out of bounds for tuple `tuple[None, None]` with length 2"
    if t8[2] is not None:
        reveal_type(t8)  # revealed: tuple[int, int, int] | tuple[None, None]

def _(t9: tuple[int | None, str] | tuple[str, int]):
    # When the element type is a union (like `int | None`), we can't filter
    # out the tuple.
    if t9[0] is not None:
        reveal_type(t9)  # revealed: tuple[int | None, str] | tuple[str, int]
```

### Unpacked Boolean tags

```toml
[environment]
python-version = "3.12"
```

A truthiness test on stable local unpack targets preserves the relationship between a Boolean tag
and its payload. Reassigning either target must not restore the original relationship.

```py
from collections.abc import AsyncIterable
from typing import Literal

def unpacked(item: tuple[Literal[True], dict[str, int]] | tuple[Literal[False], str]):
    flag, payload = item
    if flag:
        reveal_type(payload)  # revealed: dict[str, int]
    else:
        reveal_type(payload)  # revealed: str

type Tagged = tuple[Literal[True], dict[str, int]] | tuple[Literal[False], str]

def aliased(item: Tagged):
    flag, payload = item
    if flag:
        reveal_type(payload)  # revealed: dict[str, int]
    else:
        reveal_type(payload)  # revealed: str

def for_targets(items: list[Tagged]):
    for flag, payload in items:
        if flag:
            reveal_type(payload)  # revealed: dict[str, int]
        else:
            reveal_type(payload)  # revealed: str

async def async_for_targets(items: AsyncIterable[Tagged]):
    async for flag, payload in items:
        if flag:
            reveal_type(payload)  # revealed: dict[str, int]
        else:
            reveal_type(payload)  # revealed: str

def assigned_in_loop(items: list[Tagged]):
    for item in items:
        flag, payload = item
        if flag:
            reveal_type(payload)  # revealed: dict[str, int]
        else:
            reveal_type(payload)  # revealed: str

def replaced_for_payload(items: list[Tagged]) -> dict[str, int]:
    for flag, payload in items:
        payload = "replacement"
        if flag:
            return payload  # error: [invalid-return-type]
    return {}

def deleted_for_payload(items: list[Tagged]):
    for flag, payload in items:
        del payload
        if flag:
            payload  # error: [unresolved-reference]

def replaced_source(item: Tagged):
    flag, payload = item
    item = (False, "replacement")
    if flag:
        reveal_type(payload)  # revealed: dict[str, int]
    else:
        reveal_type(payload)  # revealed: str

def ambiguous(item: tuple[Literal[True], dict[str, int]] | tuple[bool, str]):
    flag, payload = item
    if flag:
        reveal_type(payload)  # revealed: dict[str, int] | str
    else:
        reveal_type(payload)  # revealed: str

def recovery(item: tuple[Literal[True], dict[str, int]] | tuple[Literal[False], str, int]):
    flag, payload = item  # error: [invalid-assignment]
    if flag:
        reveal_type(payload)  # revealed: dict[str, int] | Unknown

def replaced_flag(
    item: tuple[Literal[True], dict[str, int]] | tuple[Literal[False], object],
) -> dict[str, int]:
    flag, payload = item
    flag = True
    if flag:
        return payload  # error: [invalid-return-type]
    return {}

def replaced_payload(
    item: tuple[Literal[True], dict[str, int]] | tuple[Literal[False], object],
) -> dict[str, int]:
    flag, payload = item
    payload = object()
    if flag:
        return payload  # error: [invalid-return-type]
    return {}

def duplicate_targets(
    item: tuple[Literal[True], Literal[False], dict[str, int]] | tuple[Literal[False], Literal[True], str],
) -> dict[str, int]:
    flag, flag, payload = item
    if flag:
        return payload  # error: [invalid-return-type]
    return {}

def loop_write(
    item: tuple[Literal[True], dict[str, int]] | tuple[Literal[False], object],
) -> dict[str, int]:
    flag, payload = item
    for index in range(2):
        if index and flag:
            return payload  # error: [invalid-return-type]
        payload = object()
    return {}

def nested_write(
    item: tuple[Literal[True], dict[str, int]] | tuple[Literal[False], object],
) -> dict[str, int]:
    flag, payload = item
    def replace():
        nonlocal payload
        payload = object()
    replace()
    if flag:
        return payload  # error: [invalid-return-type]
    return {}
```

Comprehension targets retain the relationship within each unpacked item. Rebinding a target in a
later generator prevents projection, and failed outer iteration cannot provide narrowing evidence.

```py
from collections.abc import Iterator

def consume_dict(value: dict[str, int]) -> None: ...
def consume_str(value: str) -> None: ...
def comprehensions(items: list[Tagged]):
    [consume_dict(payload) if flag else consume_str(payload) for flag, payload in items]
    reveal_type([payload for flag, payload in items if flag])  # revealed: list[dict[str, int]]
    reveal_type([payload for flag, payload in items if not flag])  # revealed: list[str]

def replaced_comprehension_flag(items: list[Tagged], flags: list[bool]):
    # error: [invalid-argument-type]
    [consume_dict(payload) for flag, payload in items for flag in flags if flag]

def replaced_comprehension_payload(items: list[Tagged], replacements: list[dict[str, int] | str]):
    # error: [invalid-argument-type]
    [consume_dict(payload) for flag, payload in items for payload in replacements if flag]

class Broken:
    def __iter__(self, required: object) -> Iterator[Tagged]:
        return iter(())

def failed_outer_iteration():
    # error: [not-iterable]
    reveal_type([payload for flag, payload in Broken() if flag])  # revealed: list[dict[str, int] | str]

    for flag, payload in Broken():  # error: [not-iterable]
        if flag:
            reveal_type(payload)  # revealed: dict[str, int] | str
```

### Tagged unions of tuples (equality narrowing)

Narrow unions of tuples based on literal tag elements using `==` comparison:

```py
from typing import Literal

class A: ...
class B: ...
class C: ...

def _(x: tuple[Literal["tag1"], A] | tuple[Literal["tag2"], B, C]):
    if x[0] == "tag1":
        reveal_type(x)  # revealed: tuple[Literal["tag1"], A]
        reveal_type(x[1])  # revealed: A
    else:
        reveal_type(x)  # revealed: tuple[Literal["tag2"], B, C]
        reveal_type(x[1])  # revealed: B
        reveal_type(x[2])  # revealed: C

def _(x: tuple[Literal["tag1"], A] | tuple[Literal["tag2"], B, C]):
    if x[0] != "tag1":
        reveal_type(x)  # revealed: tuple[Literal["tag2"], B, C]
    else:
        reveal_type(x)  # revealed: tuple[Literal["tag1"], A]

def _(x: tuple[Literal["tag1"], A] | tuple[Literal["tag2"], B, C]):
    if (tag := x[0]) == "tag1":
        reveal_type(tag)  # revealed: Literal["tag1"]
        reveal_type(x)  # revealed: tuple[Literal["tag1"], A]
    else:
        reveal_type(tag)  # revealed: Literal["tag2"]
        reveal_type(x)  # revealed: tuple[Literal["tag2"], B, C]

# With int literals
def _(x: tuple[Literal[1], A] | tuple[Literal[2], B]):
    if x[0] == 1:
        reveal_type(x)  # revealed: tuple[Literal[1], A]
    else:
        reveal_type(x)  # revealed: tuple[Literal[2], B]

# With bytes literals
def _(x: tuple[Literal[b"a"], A] | tuple[Literal[b"b"], B]):
    if x[0] == b"a":
        reveal_type(x)  # revealed: tuple[Literal[b"a"], A]
    else:
        reveal_type(x)  # revealed: tuple[Literal[b"b"], B]

# Multiple tuple variants
def _(x: tuple[Literal["a"], A] | tuple[Literal["b"], B] | tuple[Literal["c"], C]):
    if x[0] == "a":
        reveal_type(x)  # revealed: tuple[Literal["a"], A]
    elif x[0] == "b":
        reveal_type(x)  # revealed: tuple[Literal["b"], B]
    else:
        reveal_type(x)  # revealed: tuple[Literal["c"], C]

# Using index 1 instead of 0
def _(x: tuple[A, Literal["tag1"]] | tuple[B, Literal["tag2"]]):
    if x[1] == "tag1":
        reveal_type(x)  # revealed: tuple[A, Literal["tag1"]]
    else:
        reveal_type(x)  # revealed: tuple[B, Literal["tag2"]]

# Works with reversed equality operands too.
def _(x: tuple[Literal["a"], A] | tuple[Literal["b"], B]):
    if "a" == x[0]:
        reveal_type(x)  # revealed: tuple[Literal["a"], A]
    else:
        reveal_type(x)  # revealed: tuple[Literal["b"], B]

# Works with reversed inequality operands too.
def _(x: tuple[Literal["a"], A] | tuple[Literal["b"], B]):
    if "a" != x[0]:
        reveal_type(x)  # revealed: tuple[Literal["b"], B]
    else:
        reveal_type(x)  # revealed: tuple[Literal["a"], A]
```

A tuple can have several literal tags. Matching a different tag rules out that tuple, while
excluding only one of its possible tags leaves it in the union:

```py
def multiple_tags(x: tuple[Literal["a"], int] | tuple[Literal["b", "c"], str]):
    if "a" == x[0]:
        reveal_type(x)  # revealed: tuple[Literal["a"], int]
    else:
        reveal_type(x)  # revealed: tuple[Literal["b", "c"], str]

    if x[0] != "b":
        reveal_type(x)  # revealed: tuple[Literal["a"], int] | tuple[Literal["b", "c"], str]
    else:
        reveal_type(x)  # revealed: tuple[Literal["b", "c"], str]
```

Enum literals are supported as tuple tags, including `IntEnum` literals:

```py
from enum import Enum, IntEnum
from typing import Literal

class Tag(Enum):
    A = 1
    B = 2

def _(x: tuple[Literal[Tag.A], int] | tuple[Literal[Tag.B], str]):
    if x[0] == Tag.A:
        reveal_type(x)  # revealed: tuple[Literal[Tag.A], int]
    else:
        reveal_type(x)  # revealed: tuple[Literal[Tag.B], str]

class IntTag(IntEnum):
    A = 1
    B = 2

def _(x: tuple[Literal[IntTag.A], int] | tuple[Literal[IntTag.B], str]):
    if x[0] == IntTag.A:
        reveal_type(x)  # revealed: tuple[Literal[IntTag.A], int]
    else:
        reveal_type(x)  # revealed: tuple[Literal[IntTag.B], str]
```

An `IntEnum` member compares equal to its integer value. A tuple whose tags are `IntTag.A` or `1`
therefore always matches `1`, and is excluded from the other branch:

```py
def enum_tag_equal_to_integer(
    x: tuple[Literal[IntTag.A, 1], int] | tuple[Literal[1], str] | tuple[Literal[2], bytes],
):
    if x[0] == 1:
        reveal_type(x)  # revealed: tuple[Literal[IntTag.A, 1], int] | tuple[Literal[1], str]
    else:
        reveal_type(x)  # revealed: tuple[Literal[2], bytes]
```

An enum can customize `__ne__` independently of `__eq__`. An ambiguous inequality keeps tuples whose
tag is that enum member in both branches, even when its literal type differs from the comparison
value:

```py
class NeverUnequal(Enum):
    A = 1
    B = 2

    def __ne__(self, other: object) -> bool:
        return False

def custom_inequality(
    x: tuple[Literal[NeverUnequal.A], int] | tuple[Literal["a"], str] | tuple[Literal["b"], bytes],
):
    if "a" != x[0]:
        reveal_type(x)  # revealed: tuple[Literal[NeverUnequal.A], int] | tuple[Literal["b"], bytes]
    else:
        reveal_type(x)  # revealed: tuple[Literal[NeverUnequal.A], int] | tuple[Literal["a"], str]
```

An ambiguous tag keeps its tuple in both branches. Other tuples can still be excluded when their
literal tags make the comparison always true or always false:

```py
def _(x: tuple[Literal["tag1"], A] | tuple[str, B] | tuple[Literal["tag2"], C]):
    if x[0] == "tag1":
        reveal_type(x)  # revealed: tuple[Literal["tag1"], A] | tuple[str, B]
    else:
        reveal_type(x)  # revealed: tuple[str, B] | tuple[Literal["tag2"], C]
```

This also applies when a tag is a union of literal and non-literal types. The non-literal
alternative can compare equal to the tag being checked:

```py
class MatchesAnything:
    def __eq__(self, other: object) -> bool:
        return True

def nonliteral_tag_union(
    x: tuple[Literal["a"], int] | tuple[Literal["b"] | MatchesAnything, str] | tuple[Literal["c"], bytes],
):
    if x[0] == "a":
        reveal_type(x)  # revealed: tuple[Literal["a"], int] | tuple[Literal["b"] | MatchesAnything, str]
    else:
        reveal_type(x)  # revealed: tuple[Literal["b"] | MatchesAnything, str] | tuple[Literal["c"], bytes]
```

An `int` tag can contain a subclass with custom equality, so it can match a string literal. This
preserves the tuple with that tag without preventing narrowing of the literal tags:

```py
def integer_tag(x: tuple[int, A] | tuple[Literal["a"], B] | tuple[Literal["b"], C]):
    if x[0] == "a":
        reveal_type(x)  # revealed: tuple[int, A] | tuple[Literal["a"], B]
    else:
        reveal_type(x)  # revealed: tuple[int, A] | tuple[Literal["b"], C]
```

If the index is out of bounds for any tuple in the union, we also skip narrowing (a diagnostic will
be emitted elsewhere for the out-of-bounds access):

```py
def _(x: tuple[A, Literal["a"]] | tuple[B]):
    # error: [index-out-of-bounds]
    if x[1] == "a":
        # Can't narrow because index 1 is out of bounds for second tuple
        reveal_type(x)  # revealed: tuple[A, Literal["a"]] | tuple[B]
    else:
        reveal_type(x)  # revealed: tuple[A, Literal["a"]] | tuple[B]
```

We can still narrow tuples when non-tuple types are present in the union:

```py
def _(x: tuple[Literal["tag1"], A] | tuple[Literal["tag2"], B] | list[int]):
    if x[0] == "tag1":
        # A list of ints could have int subclasses in it,
        # and int subclasses could have custom `__eq__` methods such that they
        # compare equal to `"tag1"`, so `list[int]` cannot be narrowed out of this
        # union.
        reveal_type(x)  # revealed: tuple[Literal["tag1"], A] | list[int]
```

### Tuple tags with non-literal comparators

A boolean comparison value can match either boolean tag value, but cannot match a string literal:

```py
from typing import Literal

def boolean_comparator(value: tuple[bool, int] | tuple[Literal["other"], str], other: bool):
    if value[0] == other:
        reveal_type(value)  # revealed: tuple[bool, int]
    else:
        reveal_type(value)  # revealed: tuple[bool, int] | tuple[Literal["other"], str]
```

When the comparison value is a union of literals, a matching tuple can have any of those tags. An
unequal comparison can retain every tuple because the comparison value is not fixed:

```py
def union_comparator(
    value: tuple[Literal["a"], int] | tuple[Literal["b"], str] | tuple[Literal["c"], bytes],
    other: Literal["a", "b"],
):
    if other != value[0]:
        reveal_type(value)  # revealed: tuple[Literal["a"], int] | tuple[Literal["b"], str] | tuple[Literal["c"], bytes]
    else:
        reveal_type(value)  # revealed: tuple[Literal["a"], int] | tuple[Literal["b"], str]
```

An intersection can restrict an enum comparison value to some of its members. A tuple with the whole
enum as its tag remains possible, while an excluded member cannot match:

```py
from enum import Enum
from ty_extensions import Intersection, Not

class Color(Enum):
    RED = 0
    GREEN = 1
    BLUE = 2

def intersection_comparator(
    value: tuple[Literal[Color.RED], int] | tuple[Color, str] | tuple[Literal[Color.GREEN], bytes],
    other: Intersection[Color, Not[Literal[Color.RED]]],
):
    if value[0] == other:
        reveal_type(value)  # revealed: tuple[Color, str] | tuple[Literal[Color.GREEN], bytes]
    else:
        reveal_type(value)  # revealed: tuple[Literal[Color.RED], int] | tuple[Color, str] | tuple[Literal[Color.GREEN], bytes]
```

### PEP 695 type aliases

Tuple narrowing also works when the union is defined via a PEP 695 type alias:

```toml
[environment]
python-version = "3.12"
```

```py
from typing import Literal

class A: ...
class B: ...

type TaggedTuple = tuple[Literal["a"], A] | tuple[Literal["b"], B]

def test_equality_narrowing(x: TaggedTuple):
    if x[0] == "a":
        reveal_type(x)  # revealed: tuple[Literal["a"], A]
    else:
        reveal_type(x)  # revealed: tuple[Literal["b"], B]

type NullableTuple = tuple[int, int] | tuple[None, None]

def test_is_narrowing(t: NullableTuple):
    if t[0] is not None:
        reveal_type(t)  # revealed: tuple[int, int]
    else:
        reveal_type(t)  # revealed: tuple[None, None]

# Nested type aliases (an alias referring to another alias) also work:
type InnerTagged = tuple[Literal["a"], A] | tuple[Literal["b"], B]
type OuterTagged = InnerTagged

def test_nested_equality_narrowing(x: OuterTagged):
    if x[0] == "a":
        reveal_type(x)  # revealed: tuple[Literal["a"], A]
    else:
        reveal_type(x)  # revealed: tuple[Literal["b"], B]

type InnerNullable = tuple[int, int] | tuple[None, None]
type OuterNullable = InnerNullable

def test_nested_is_narrowing(t: OuterNullable):
    if t[0] is not None:
        reveal_type(t)  # revealed: tuple[int, int]
    else:
        reveal_type(t)  # revealed: tuple[None, None]
```

### String subscript

```py
def _(d: dict[str, str | None]):
    if d["a"] is not None:
        reveal_type(d["a"])  # revealed: str
        reveal_type(d["b"])  # revealed: str | None
```

## Combined attribute and subscript narrowing

```py
class C:
    def __init__(self):
        self.x: tuple[int | None, int | None] = (None, None)

class D:
    def __init__(self):
        self.c: tuple[C] | None = None

d = D()
if d.c is not None and d.c[0].x[0] is not None:
    reveal_type(d.c[0].x[0])  # revealed: int
```

## Narrowing with negative subscripts

Narrowing should work with negative subscripts like `x[-1]`:

```py
def _(x: list[int | None]):
    if x[-1] is not None:
        reveal_type(x[-1])  # revealed: int

def _(x: list[str | None]):
    if x[-1] is None:
        reveal_type(x[-1])  # revealed: None
    else:
        reveal_type(x[-1])  # revealed: str
```

Nested negative subscripts should also work:

```py
def _(x: list[list[int | None]]):
    if x[-1][-1] is not None:
        reveal_type(x[-1][-1])  # revealed: int
```

Mixed positive and negative subscripts:

```py
def _(x: list[list[int | None]]):
    if x[0][-1] is not None:
        reveal_type(x[0][-1])  # revealed: int

    if x[-1][0] is not None:
        reveal_type(x[-1][0])  # revealed: int
```

Attribute access combined with negative subscripts:

```py
class Container:
    items: list[int | None]

def _(c: Container):
    if c.items[-1] is not None:
        reveal_type(c.items[-1])  # revealed: int
```

Multiple conditions in an `and` chain:

```py
def _(x: list[int | None]):
    # Narrowing should persist through `and` chains
    if x[-1] is not None and x[-1] > 0:
        reveal_type(x[-1])  # revealed: int
```

Negative indices with tuples:

```py
def _(t: tuple[int, str, None] | tuple[None, None, int]):
    if t[-1] is not None:
        reveal_type(t)  # revealed: tuple[None, None, int]
    else:
        reveal_type(t)  # revealed: tuple[int, str, None]

    if t[-3] is not None:
        reveal_type(t)  # revealed: tuple[int, str, None]
```

## Narrowing with explicit positive subscripts

Narrowing should work with explicit positive subscripts like `x[+1]`:

```py
def _(x: list[int | None]):
    if x[+0] is not None:
        reveal_type(x[+0])  # revealed: int

    if x[+1] is not None:
        reveal_type(x[+1])  # revealed: int
```

## Narrowing with boolean subscripts

Narrowing should work with boolean subscripts like `x[True]` and `x[False]`. We treat `bool`
subscripts the same as `int` subscripts because `True` always has the same hash and index value as
`1`, and `False` always has the same hash and index value as `0`:

```py
def _(x: tuple[object, object]):
    if isinstance(x[True], str):
        reveal_type(x[True])  # revealed: str
        reveal_type(x[1])  # revealed: str

def _(x: list[int | None]):
    # x[True] is equivalent to x[1]
    if x[True] is not None:
        reveal_type(x[True])  # revealed: int

    # x[False] is equivalent to x[0]
    if x[False] is not None:
        reveal_type(x[False])  # revealed: int
```

Combined with other subscript types:

```py
def _(x: list[list[int | None]]):
    if x[True][-1] is not None:
        reveal_type(x[True][-1])  # revealed: int

    if x[False][0] is not None:
        reveal_type(x[False][0])  # revealed: int
```

## Narrowing with bytes literal subscripts

Narrowing should work with bytes literal subscripts like `x[b"key"]`:

```py
def _(d: dict[bytes, str | None]):
    if d[b"key"] is not None:
        reveal_type(d[b"key"])  # revealed: str
        reveal_type(d[b"other"])  # revealed: str | None
```

Combined with attribute access:

```py
class Container:
    data: dict[bytes, int | None]

def _(c: Container):
    if c.data[b"key"] is not None:
        reveal_type(c.data[b"key"])  # revealed: int
```

## Constructing tagged tuples after a branch join

```py
from typing import Literal

Tagged = tuple[Literal[True], int] | tuple[Literal[False], str]

def joined(flag: bool) -> Tagged:
    if flag:
        payload = 1
    else:
        payload = "x"
    reveal_type((flag, payload))  # revealed: tuple[Literal[True], Literal[1]] | tuple[Literal[False], Literal["x"]]
    return flag, payload

def branch_local(flag: bool) -> Tagged:
    if flag:
        return True, 1
    else:
        return False, "x"

def narrowed_payload(flag: bool, integer: int | None, text: str | None) -> Tagged:
    if flag:
        payload = integer
    else:
        payload = text
    assert payload is not None
    return flag, payload
```

Reassigning either field or using an independent payload does not establish the tagged contract. A
captured writer can also replace a local after its branch assignment.

```py
from typing import Literal

Tagged = tuple[Literal[True], int] | tuple[Literal[False], str]

def unrelated(flag: bool, payload: int | str) -> Tagged:
    return flag, payload  # error: [invalid-return-type]

def changed_tag(flag: bool) -> Tagged:
    if flag:
        payload = 1
    else:
        payload = "x"
    flag = not flag
    return flag, payload  # error: [invalid-return-type]

def changed_payload(flag: bool, other: int | str) -> Tagged:
    if flag:
        payload = 1
    else:
        payload = "x"
    payload = other
    return flag, payload  # error: [invalid-return-type]

def captured_payload(flag: bool, other: int | str) -> Tagged:
    if flag:
        payload = 1
    else:
        payload = "x"
    def replace():
        nonlocal payload
        payload = other
    replace()
    return flag, payload  # error: [invalid-return-type]

def missing_payload(flag: bool):
    if flag:
        payload = 1
    return flag, payload  # error: [possibly-unresolved-reference]
```

## Constructing tagged tuples within a loop iteration

```py
from typing import Literal

LoopTagged = tuple[Literal[True], int] | tuple[Literal[False], object]

def consume_loop(value: LoopTagged) -> None: ...
def compound_joined(selected: bool, brace: bool) -> None:
    if selected or brace:
        payload = 1
    else:
        payload = "x"
    consume_loop((selected, payload))

def loop_joined(signals: list[bool], brace: bool) -> None:
    selected = False
    for signal in signals:
        if signal:
            selected = True
        if selected or brace:
            payload = 1
        else:
            payload = "x"
        consume_loop((selected, payload))
        selected = False

def loop_changed(signals: list[bool], brace: bool, replacement: bool) -> None:
    selected = False
    for signal in signals:
        if signal:
            selected = True
        if selected or brace:
            payload = 1
        else:
            payload = "x"
        selected = replacement
        consume_loop((selected, payload))  # error: [invalid-argument-type]
        selected = False

def carried_payload(signals: list[bool], refresh: bool) -> None:
    payload: int | str = "x"
    for selected in signals:
        if refresh:
            if selected:
                payload = 1
            else:
                payload = "x"
        consume_loop((selected, payload))  # error: [invalid-argument-type]

def after_while(signals: list[bool], running: bool) -> None:
    payload: int | str = "x"
    selected = False
    while (selected := signals.pop()) == running:
        if selected:
            payload = 1
        else:
            payload = "x"
    consume_loop((selected, payload))  # error: [invalid-argument-type]

def nested_loop(signals: list[bool], replacements: list[bool]) -> None:
    selected = False
    for signal in signals:
        if signal:
            selected = True
        if selected:
            payload = 1
        else:
            payload = "x"
        for selected in replacements:
            pass
        consume_loop((selected, payload))  # error: [invalid-argument-type]
```
