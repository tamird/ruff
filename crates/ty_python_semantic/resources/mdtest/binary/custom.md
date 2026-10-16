# Custom binary operations

## Class instances

```py
from typing import Literal

class Yes:
    def __add__(self, other) -> Literal["+"]:
        return "+"

    def __sub__(self, other) -> Literal["-"]:
        return "-"

    def __mul__(self, other) -> Literal["*"]:
        return "*"

    def __matmul__(self, other) -> Literal["@"]:
        return "@"

    def __truediv__(self, other) -> Literal["/"]:
        return "/"

    def __mod__(self, other) -> Literal["%"]:
        return "%"

    def __pow__(self, other) -> Literal["**"]:
        return "**"

    def __lshift__(self, other) -> Literal["<<"]:
        return "<<"

    def __rshift__(self, other) -> Literal[">>"]:
        return ">>"

    def __or__(self, other) -> Literal["|"]:
        return "|"

    def __xor__(self, other) -> Literal["^"]:
        return "^"

    def __and__(self, other) -> Literal["&"]:
        return "&"

    def __floordiv__(self, other) -> Literal["//"]:
        return "//"

class Sub(Yes): ...
class No: ...

# Yes implements all of the dunder methods.
reveal_type(Yes() + Yes())  # revealed: Literal["+"]
reveal_type(Yes() - Yes())  # revealed: Literal["-"]
reveal_type(Yes() * Yes())  # revealed: Literal["*"]
reveal_type(Yes() @ Yes())  # revealed: Literal["@"]
reveal_type(Yes() / Yes())  # revealed: Literal["/"]
reveal_type(Yes() % Yes())  # revealed: Literal["%"]
reveal_type(Yes() ** Yes())  # revealed: Literal["**"]
reveal_type(Yes() << Yes())  # revealed: Literal["<<"]
reveal_type(Yes() >> Yes())  # revealed: Literal[">>"]
reveal_type(Yes() | Yes())  # revealed: Literal["|"]
reveal_type(Yes() ^ Yes())  # revealed: Literal["^"]
reveal_type(Yes() & Yes())  # revealed: Literal["&"]
reveal_type(Yes() // Yes())  # revealed: Literal["//"]

# Sub inherits Yes's implementation of the dunder methods.
reveal_type(Sub() + Sub())  # revealed: Literal["+"]
reveal_type(Sub() - Sub())  # revealed: Literal["-"]
reveal_type(Sub() * Sub())  # revealed: Literal["*"]
reveal_type(Sub() @ Sub())  # revealed: Literal["@"]
reveal_type(Sub() / Sub())  # revealed: Literal["/"]
reveal_type(Sub() % Sub())  # revealed: Literal["%"]
reveal_type(Sub() ** Sub())  # revealed: Literal["**"]
reveal_type(Sub() << Sub())  # revealed: Literal["<<"]
reveal_type(Sub() >> Sub())  # revealed: Literal[">>"]
reveal_type(Sub() | Sub())  # revealed: Literal["|"]
reveal_type(Sub() ^ Sub())  # revealed: Literal["^"]
reveal_type(Sub() & Sub())  # revealed: Literal["&"]
reveal_type(Sub() // Sub())  # revealed: Literal["//"]

# No does not implement any of the dunder methods.
# error: [unsupported-operator] "Operator `+` is not supported between two objects of type `No`"
reveal_type(No() + No())  # revealed: Unknown
# error: [unsupported-operator] "Operator `-` is not supported between two objects of type `No`"
reveal_type(No() - No())  # revealed: Unknown
# error: [unsupported-operator] "Operator `*` is not supported between two objects of type `No`"
reveal_type(No() * No())  # revealed: Unknown
# error: [unsupported-operator] "Operator `@` is not supported between two objects of type `No`"
reveal_type(No() @ No())  # revealed: Unknown
# error: [unsupported-operator] "Operator `/` is not supported between two objects of type `No`"
reveal_type(No() / No())  # revealed: Unknown
# error: [unsupported-operator] "Operator `%` is not supported between two objects of type `No`"
reveal_type(No() % No())  # revealed: Unknown
# error: [unsupported-operator] "Operator `**` is not supported between two objects of type `No`"
reveal_type(No() ** No())  # revealed: Unknown
# error: [unsupported-operator] "Operator `<<` is not supported between two objects of type `No`"
reveal_type(No() << No())  # revealed: Unknown
# error: [unsupported-operator] "Operator `>>` is not supported between two objects of type `No`"
reveal_type(No() >> No())  # revealed: Unknown
# error: [unsupported-operator] "Operator `|` is not supported between two objects of type `No`"
reveal_type(No() | No())  # revealed: Unknown
# error: [unsupported-operator] "Operator `^` is not supported between two objects of type `No`"
reveal_type(No() ^ No())  # revealed: Unknown
# error: [unsupported-operator] "Operator `&` is not supported between two objects of type `No`"
reveal_type(No() & No())  # revealed: Unknown
# error: [unsupported-operator] "Operator `//` is not supported between two objects of type `No`"
reveal_type(No() // No())  # revealed: Unknown

# Yes does not implement any of the reflected dunder methods.
# error: [unsupported-operator] "Operator `+` is not supported between objects of type `No` and `Yes`"
reveal_type(No() + Yes())  # revealed: Unknown
# error: [unsupported-operator] "Operator `-` is not supported between objects of type `No` and `Yes`"
reveal_type(No() - Yes())  # revealed: Unknown
# error: [unsupported-operator] "Operator `*` is not supported between objects of type `No` and `Yes`"
reveal_type(No() * Yes())  # revealed: Unknown
# error: [unsupported-operator] "Operator `@` is not supported between objects of type `No` and `Yes`"
reveal_type(No() @ Yes())  # revealed: Unknown
# error: [unsupported-operator] "Operator `/` is not supported between objects of type `No` and `Yes`"
reveal_type(No() / Yes())  # revealed: Unknown
# error: [unsupported-operator] "Operator `%` is not supported between objects of type `No` and `Yes`"
reveal_type(No() % Yes())  # revealed: Unknown
# error: [unsupported-operator] "Operator `**` is not supported between objects of type `No` and `Yes`"
reveal_type(No() ** Yes())  # revealed: Unknown
# error: [unsupported-operator] "Operator `<<` is not supported between objects of type `No` and `Yes`"
reveal_type(No() << Yes())  # revealed: Unknown
# error: [unsupported-operator] "Operator `>>` is not supported between objects of type `No` and `Yes`"
reveal_type(No() >> Yes())  # revealed: Unknown
# error: [unsupported-operator] "Operator `|` is not supported between objects of type `No` and `Yes`"
reveal_type(No() | Yes())  # revealed: Unknown
# error: [unsupported-operator] "Operator `^` is not supported between objects of type `No` and `Yes`"
reveal_type(No() ^ Yes())  # revealed: Unknown
# error: [unsupported-operator] "Operator `&` is not supported between objects of type `No` and `Yes`"
reveal_type(No() & Yes())  # revealed: Unknown
# error: [unsupported-operator] "Operator `//` is not supported between objects of type `No` and `Yes`"
reveal_type(No() // Yes())  # revealed: Unknown
```

## Subclass reflections override superclass dunders

```py
from typing import Literal

class Yes:
    def __add__(self, other) -> Literal["+"]:
        return "+"

    def __sub__(self, other) -> Literal["-"]:
        return "-"

    def __mul__(self, other) -> Literal["*"]:
        return "*"

    def __matmul__(self, other) -> Literal["@"]:
        return "@"

    def __truediv__(self, other) -> Literal["/"]:
        return "/"

    def __mod__(self, other) -> Literal["%"]:
        return "%"

    def __pow__(self, other) -> Literal["**"]:
        return "**"

    def __lshift__(self, other) -> Literal["<<"]:
        return "<<"

    def __rshift__(self, other) -> Literal[">>"]:
        return ">>"

    def __or__(self, other) -> Literal["|"]:
        return "|"

    def __xor__(self, other) -> Literal["^"]:
        return "^"

    def __and__(self, other) -> Literal["&"]:
        return "&"

    def __floordiv__(self, other) -> Literal["//"]:
        return "//"

class Sub(Yes):
    def __radd__(self, other) -> Literal["r+"]:
        return "r+"

    def __rsub__(self, other) -> Literal["r-"]:
        return "r-"

    def __rmul__(self, other) -> Literal["r*"]:
        return "r*"

    def __rmatmul__(self, other) -> Literal["r@"]:
        return "r@"

    def __rtruediv__(self, other) -> Literal["r/"]:
        return "r/"

    def __rmod__(self, other) -> Literal["r%"]:
        return "r%"

    def __rpow__(self, other) -> Literal["r**"]:
        return "r**"

    def __rlshift__(self, other) -> Literal["r<<"]:
        return "r<<"

    def __rrshift__(self, other) -> Literal["r>>"]:
        return "r>>"

    def __ror__(self, other) -> Literal["r|"]:
        return "r|"

    def __rxor__(self, other) -> Literal["r^"]:
        return "r^"

    def __rand__(self, other) -> Literal["r&"]:
        return "r&"

    def __rfloordiv__(self, other) -> Literal["r//"]:
        return "r//"

class No:
    def __radd__(self, other) -> Literal["r+"]:
        return "r+"

    def __rsub__(self, other) -> Literal["r-"]:
        return "r-"

    def __rmul__(self, other) -> Literal["r*"]:
        return "r*"

    def __rmatmul__(self, other) -> Literal["r@"]:
        return "r@"

    def __rtruediv__(self, other) -> Literal["r/"]:
        return "r/"

    def __rmod__(self, other) -> Literal["r%"]:
        return "r%"

    def __rpow__(self, other) -> Literal["r**"]:
        return "r**"

    def __rlshift__(self, other) -> Literal["r<<"]:
        return "r<<"

    def __rrshift__(self, other) -> Literal["r>>"]:
        return "r>>"

    def __ror__(self, other) -> Literal["r|"]:
        return "r|"

    def __rxor__(self, other) -> Literal["r^"]:
        return "r^"

    def __rand__(self, other) -> Literal["r&"]:
        return "r&"

    def __rfloordiv__(self, other) -> Literal["r//"]:
        return "r//"

# Subclass reflected dunder methods may take precedence over the superclass's regular dunders,
# depending on the operands' runtime classes.
reveal_type(Yes() + Sub())  # revealed: Literal["r+", "+"]
reveal_type(Yes() - Sub())  # revealed: Literal["r-", "-"]
reveal_type(Yes() * Sub())  # revealed: Literal["r*", "*"]
reveal_type(Yes() @ Sub())  # revealed: Literal["r@", "@"]
reveal_type(Yes() / Sub())  # revealed: Literal["r/", "/"]
reveal_type(Yes() % Sub())  # revealed: Literal["r%", "%"]
reveal_type(Yes() ** Sub())  # revealed: Literal["r**", "**"]
reveal_type(Yes() << Sub())  # revealed: Literal["r<<", "<<"]
reveal_type(Yes() >> Sub())  # revealed: Literal["r>>", ">>"]
reveal_type(Yes() | Sub())  # revealed: Literal["r|", "|"]
reveal_type(Yes() ^ Sub())  # revealed: Literal["r^", "^"]
reveal_type(Yes() & Sub())  # revealed: Literal["r&", "&"]
reveal_type(Yes() // Sub())  # revealed: Literal["r//", "//"]

# But for an unrelated class, the superclass regular dunders are used.
reveal_type(Yes() + No())  # revealed: Literal["+"]
reveal_type(Yes() - No())  # revealed: Literal["-"]
reveal_type(Yes() * No())  # revealed: Literal["*"]
reveal_type(Yes() @ No())  # revealed: Literal["@"]
reveal_type(Yes() / No())  # revealed: Literal["/"]
reveal_type(Yes() % No())  # revealed: Literal["%"]
reveal_type(Yes() ** No())  # revealed: Literal["**"]
reveal_type(Yes() << No())  # revealed: Literal["<<"]
reveal_type(Yes() >> No())  # revealed: Literal[">>"]
reveal_type(Yes() | No())  # revealed: Literal["|"]
reveal_type(Yes() ^ No())  # revealed: Literal["^"]
reveal_type(Yes() & No())  # revealed: Literal["&"]
reveal_type(Yes() // No())  # revealed: Literal["//"]
```

## Classes

Dunder methods defined in a class are available to instances of that class, but not to the class
itself. (For these operators to work on the class itself, they would have to be defined on the
class's type, i.e. `type`.)

```py
from typing import Literal

class Yes:
    def __add__(self, other) -> Literal["+"]:
        return "+"

class Sub(Yes): ...
class No: ...

# snapshot: unsupported-operator
reveal_type(Yes + Yes)  # revealed: Unknown
```

```snapshot
error[unsupported-operator]: Unsupported `+` operation
  --> src/mdtest_snippet.py:11:13
   |
11 | reveal_type(Yes + Yes)  # revealed: Unknown
   |             ---^^^---
   |             |
   |             Both operands have type `<class 'Yes'>`
```

```py
# snapshot: unsupported-operator
reveal_type(Sub + Sub)  # revealed: Unknown
```

```snapshot
error[unsupported-operator]: Unsupported `+` operation
  --> src/mdtest_snippet.py:13:13
   |
13 | reveal_type(Sub + Sub)  # revealed: Unknown
   |             ---^^^---
   |             |
   |             Both operands have type `<class 'Sub'>`
```

```py
# snapshot: unsupported-operator
reveal_type(No + No)  # revealed: Unknown
```

```snapshot
error[unsupported-operator]: Unsupported `+` operation
  --> src/mdtest_snippet.py:15:13
   |
15 | reveal_type(No + No)  # revealed: Unknown
   |             --^^^--
   |             |
   |             Both operands have type `<class 'No'>`
```

## Subclass

```py
from typing import Literal

class Yes:
    def __add__(self, other) -> Literal["+"]:
        return "+"

class Sub(Yes): ...
class No: ...

def yes() -> type[Yes]:
    return Yes

def sub() -> type[Sub]:
    return Sub

def no() -> type[No]:
    return No

# error: [unsupported-operator] "Operator `+` is not supported between two objects of type `type[Yes]`"
reveal_type(yes() + yes())  # revealed: Unknown
# error: [unsupported-operator] "Operator `+` is not supported between two objects of type `type[Sub]`"
reveal_type(sub() + sub())  # revealed: Unknown
# error: [unsupported-operator] "Operator `+` is not supported between two objects of type `type[No]`"
reveal_type(no() + no())  # revealed: Unknown
```

## Function literals

```py
def f():
    pass

# error: [unsupported-operator] "Operator `+` is not supported between two objects of type `def f() -> Unknown`"
reveal_type(f + f)  # revealed: Unknown
# error: [unsupported-operator] "Operator `-` is not supported between two objects of type `def f() -> Unknown`"
reveal_type(f - f)  # revealed: Unknown
# error: [unsupported-operator] "Operator `*` is not supported between two objects of type `def f() -> Unknown`"
reveal_type(f * f)  # revealed: Unknown
# error: [unsupported-operator] "Operator `@` is not supported between two objects of type `def f() -> Unknown`"
reveal_type(f @ f)  # revealed: Unknown
# error: [unsupported-operator] "Operator `/` is not supported between two objects of type `def f() -> Unknown`"
reveal_type(f / f)  # revealed: Unknown
# error: [unsupported-operator] "Operator `%` is not supported between two objects of type `def f() -> Unknown`"
reveal_type(f % f)  # revealed: Unknown
# error: [unsupported-operator] "Operator `**` is not supported between two objects of type `def f() -> Unknown`"
reveal_type(f**f)  # revealed: Unknown
# error: [unsupported-operator] "Operator `<<` is not supported between two objects of type `def f() -> Unknown`"
reveal_type(f << f)  # revealed: Unknown
# error: [unsupported-operator] "Operator `>>` is not supported between two objects of type `def f() -> Unknown`"
reveal_type(f >> f)  # revealed: Unknown
# error: [unsupported-operator] "Operator `|` is not supported between two objects of type `def f() -> Unknown`"
reveal_type(f | f)  # revealed: Unknown
# error: [unsupported-operator] "Operator `^` is not supported between two objects of type `def f() -> Unknown`"
reveal_type(f ^ f)  # revealed: Unknown
# error: [unsupported-operator] "Operator `&` is not supported between two objects of type `def f() -> Unknown`"
reveal_type(f & f)  # revealed: Unknown
# error: [unsupported-operator] "Operator `//` is not supported between two objects of type `def f() -> Unknown`"
reveal_type(f // f)  # revealed: Unknown
```

## Classes from different modules with the same name

We use the fully qualified names in diagnostics if the two classes have the same unqualified name,
but are nonetheless different.

`mod1.py`:

```py
class A: ...
```

`mod2.py`:

```py
import mod1

class A: ...

# snapshot: unsupported-operator
A() + mod1.A()
```

```snapshot
error[unsupported-operator]: Unsupported `+` operation
 --> src/mod2.py:6:1
  |
6 | A() + mod1.A()
  | ---^^^--------
  | |     |
  | |     Has type `mod1.A`
  | Has type `mod2.A`
```

## Generic operator result context

Binary dunder calls use their expression's expected result type, just like explicit method calls.
The context participates in cached resolution and is shared by normal and reflected dispatch.

```toml
[environment]
python-version = "3.13"
```

`tagged.pyi`:

```pyi
from typing import Generic, Literal, Mapping, Sequence, TypeVar

V = TypeVar("V", covariant=True)
K = TypeVar("K", covariant=True, default=object)
L = TypeVar("L")
R = TypeVar("R")

class Tagged(Generic[V, K]):
    def __add__(self: Tagged[Sequence[L], Literal["list"]], other: list[R] | tuple[R, ...], /) -> Tagged[list[L | R], K]: ...
    def __radd__(self: Tagged[Sequence[L], Literal["list"]], other: list[R] | tuple[R, ...], /) -> Tagged[list[L | R], K]: ...

def choose(values: Mapping[str, V]) -> Tagged[V, Literal["list"]]: ...
```

```py
from typing import Any
from tagged import Tagged, choose

left = choose({"condition": ["a"], "default": [42]})
normal: Tagged[list[str | int]] = left + []
reveal_type(normal)  # revealed: Tagged[list[str | int], Literal["list"]]
reflected: Tagged[list[str | int]] = [] + left
reveal_type(reflected)  # revealed: Tagged[list[str | int], Literal["list"]]
wrong: Tagged[list[str]] = normal  # error: [invalid-assignment]

# Different contexts for the same operands must not reuse the first result.
strings = choose({"condition": ["text"]})
narrow: Tagged[list[str]] = strings + []
broad: Tagged[list[str | int]] = strings + []
reveal_type(narrow)  # revealed: Tagged[list[str], Literal["list"]]
reveal_type(broad)  # revealed: Tagged[list[str | int], Literal["list"]]

# The context does not override concrete argument evidence.
bad: Tagged[list[str]] = strings + [42]  # error: [invalid-assignment]

def check(gradual: list[Any]) -> None:
    result: Tagged[list[str]] = strings + gradual
    reveal_type(result)  # revealed: Tagged[list[str], Literal["list"]]
    explicit: Tagged[list[str]] = strings.__add__(gradual)
    reveal_type(explicit)  # revealed: Tagged[list[str], Literal["list"]]
    reveal_type(strings + gradual)  # revealed: Tagged[list[str | Any], Literal["list"]]

# An empty operand without result context remains unconstrained.
reveal_type(strings + [])  # revealed: Tagged[list[str | Unknown], Literal["list"]]
```
