# `lambda` expression

## No parameters

`lambda` expressions can be defined without any parameters.

```py
reveal_type(lambda: 1)  # revealed: () -> Literal[1]

# error: [unresolved-reference]
reveal_type(lambda: a)  # revealed: () -> Unknown
```

## With parameters

Unlike parameters in function definition, the parameters in a `lambda` expression cannot be
annotated.

```py
reveal_type(lambda a: a)  # revealed: (a) -> Unknown
reveal_type(lambda a, b: a + b)  # revealed: (a, b) -> Unknown
```

But, it can have default values:

```py
reveal_type(lambda a=1: a)  # revealed: (a=1) -> Unknown | Literal[1]
reveal_type(lambda a, b=2: a)  # revealed: (a, b=2) -> Unknown
```

And, positional-only parameters:

```py
reveal_type(lambda a, b, /, c: c)  # revealed: (a, b, /, c) -> Unknown
```

And, keyword-only parameters:

```py
reveal_type(lambda a, *, b=2, c: b)  # revealed: (a, *, b=2, c) -> Unknown | Literal[2]
```

And, variadic parameter:

```py
reveal_type(lambda *args: args)  # revealed: (*args) -> tuple[Unknown, ...]
```

And, keyword-variadic parameter:

```py
reveal_type(lambda **kwargs: kwargs)  # revealed: (**kwargs) -> dict[str, Unknown]
```

Mixing all of them together:

```py
# revealed: (a, b, /, c=True, *args, d="default", e=5, **kwargs) -> None
reveal_type(lambda a, b, /, c=True, *args, d="default", e=5, **kwargs: None)
```

## Parameter type

In addition to correctly inferring the `lambda` expression, the parameters should also be inferred
correctly.

Using a parameter with no default value:

```py
lambda x: reveal_type(x)  # revealed: Unknown
```

Using a parameter with default value:

```py
lambda x=1: reveal_type(x)  # revealed: Unknown | Literal[1]
```

Using a variadic parameter:

```py
lambda *args: reveal_type(args)  # revealed: tuple[Unknown, ...]
```

Using a keyword-variadic parameter:

```py
lambda **kwargs: reveal_type(kwargs)  # revealed: dict[str, Unknown]
```

## Nested `lambda` expressions

Here, a `lambda` expression is used as the default value for a parameter in another `lambda`
expression.

```py
reveal_type(lambda a=lambda x, y: 0: 2)  # revealed: (a=...) -> Literal[2]
```

## Defaults in string annotations

`Annotated` metadata can contain lambdas. Names in their default values must still be resolved in
the enclosing string annotation, whose expressions are not part of the module's semantic index.

```py
from typing_extensions import Annotated

def f(value: "Annotated[int, lambda default=int: None]"):
    reveal_type(value)  # revealed: int

# error: [unresolved-reference]
def invalid(value: "Annotated[int, lambda default=missing: None]"): ...
```

Nested lambdas must retain the same context. Dynamic classes created in a default value also need
the original string annotation as their source anchor.

```py
def nested(value: "Annotated[int, lambda outer=(lambda inner=int: None): None]"):
    reveal_type(value)  # revealed: int

def dynamic(value: "Annotated[int, lambda default=type('C', (), {}): None]"):
    reveal_type(value)  # revealed: int
```

## Defaults in stub string annotations

Stub files must preserve the string-annotation context too, including for positional-only and
keyword-only defaults.

```pyi
from typing_extensions import Annotated

value: "Annotated[int, lambda positional=int, /, normal=str, *, keyword=bytes: None]"
reveal_type(value)  # revealed: int
```

## Assignment

This does not enumerate all combinations of parameter kinds as that should be covered by the
[subtype tests for callable types](./../type_properties/is_subtype_of.md#callable).

```py
from typing import Callable

a1: Callable[[], None] = lambda: None
a2: Callable[[int], None] = lambda x: None
a3: Callable[[int, int], None] = lambda x, y, z=1: None
a4: Callable[[int, int], None] = lambda *args: None

# error: [invalid-assignment]
a5: Callable[[], None] = lambda x: None
# error: [invalid-assignment]
a6: Callable[[int], None] = lambda: None

# error: [invalid-assignment]
a7: Callable[[], str] = lambda: 1
```

## Function-like behavior of lambdas

All `lambda` functions are instances of `types.FunctionType` and should have access to the same set
of attributes.

```py
x = lambda y: y

reveal_type(x.__code__)  # revealed: CodeType
reveal_type(x.__name__)  # revealed: str
reveal_type(x.__defaults__)  # revealed: tuple[Any, ...] | None
reveal_type(x.__annotations__)  # revealed: dict[str, Any]
reveal_type(x.__dict__)  # revealed: dict[str, Any]
reveal_type(x.__doc__)  # revealed: str | None
reveal_type(x.__kwdefaults__)  # revealed: dict[str, Any] | None
reveal_type(x.__module__)  # revealed: str
reveal_type(x.__qualname__)  # revealed: str
```

## Named callback context

A callback protocol supplies parameter hints while the lambda preserves its source parameter names
and kinds and its inferred return type. Parameter names and arity remain part of compatibility.

```py
from typing import Protocol

class Transform(Protocol):
    def __call__(self, value: int) -> int: ...

transform: Transform = lambda value: (reveal_type(value), value + 1)[1]  # revealed: int

# error: [invalid-assignment]
wrong_name: Transform = lambda other: 1
# error: [invalid-assignment]
wrong_arity: Transform = lambda: 1
# error: [invalid-assignment]
wrong_result: Transform = lambda value: "bad"
```

## Callback keyword parameters

Keyword-only parameters receive context from the matching parameter name.

```py
from typing import Protocol

class Named(Protocol):
    def __call__(self, *, value: str) -> str: ...

named: Named = lambda *, value: (reveal_type(value), value.upper())[1]  # revealed: str
# error: [invalid-assignment]
wrong_keyword: Named = lambda *, other: "ok"
```

## Callback defaults

An optional callback parameter includes the lambda's actual default in its body input. A callback
that ignores a string default can still return an integer. A required callback context restricts the
inferred callable to calls that supply the argument.

```py
from typing import Callable, Protocol

class OptionalInt(Protocol):
    def __call__(self, value: int = ...) -> int: ...

# error: [invalid-assignment]
wrong_default_result: OptionalInt = lambda value="bad": value
ignored_default: OptionalInt = lambda value="bad": 1
valid_default: OptionalInt = lambda value=1: value
# error: [invalid-assignment]
missing_default: OptionalInt = lambda value: value

class RequiredInt(Protocol):
    def __call__(self, value: int) -> int: ...

required_protocol: RequiredInt = lambda value="bad": value
reveal_type(required_protocol(1))  # revealed: int
# error: [missing-argument]
required_protocol()

def needs_int(value: int) -> int:
    return value

# The default is still checked even though contextual calls supply the argument.
# error: [invalid-argument-type]
checked_default: RequiredInt = lambda value=needs_int("bad"): value
required_callable: Callable[[int], int] = lambda value="bad": value
reveal_type(required_callable)  # revealed: (value: int) -> int
reveal_type(required_callable(1))  # revealed: int
# error: [missing-argument]
reveal_type(required_callable())  # revealed: int

gradual: Callable[..., int] = lambda value="bad": 1
reveal_type(gradual())  # revealed: Literal[1]
```

## Callback variadic parameters

A matching fixed positional prefix lets a homogeneous variadic parameter describe each remaining
argument. The parameter's value in the body is a tuple.

```py
from typing import Protocol

class Collect(Protocol):
    def __call__(self, first: int, /, *attrs: str) -> tuple[str, ...]: ...

collect: Collect = lambda first, *attrs: (
    reveal_type(first),  # revealed: int
    reveal_type(attrs),  # revealed: tuple[str, ...]
    attrs,
)[2]
collect(1)
collect(1, "a", "b")
# error: [invalid-argument-type]
collect(1, "a", 2)

shifted: Collect = lambda *attrs: (reveal_type(attrs), attrs)[1]  # revealed: tuple[Unknown, ...]
```

## Generic callback context

Specialized callback protocols and aliases preserve their parameter types. Multiple useful callback
alternatives remain ambiguous.

```py
from typing import Protocol, TypeAlias, TypeVar

T = TypeVar("T")

class Identity(Protocol[T]):
    def __call__(self, value: T) -> T: ...

IntIdentity: TypeAlias = Identity[int]
identity: IntIdentity | None = lambda value: (reveal_type(value), value)[1]  # revealed: int

class AcceptInt(Protocol):
    def __call__(self, value: int) -> object: ...

class AcceptStr(Protocol):
    def __call__(self, value: str) -> object: ...

ambiguous: AcceptInt | AcceptStr = lambda value: reveal_type(value)  # revealed: Unknown
```

## Callback context selection

Non-callable protocol alternatives do not obscure a useful callable context. Multiple overloads
retain ordinary lambda inference.

```py
from typing import Callable, Protocol, overload

class HasLength(Protocol):
    def __len__(self) -> int: ...

callback: Callable[[int], int] | HasLength = lambda value: (reveal_type(value), value)[1]  # revealed: int

class Overloaded(Protocol):
    @overload
    def __call__(self, value: int) -> int: ...
    @overload
    def __call__(self, value: str) -> str: ...

overloaded: Overloaded = lambda value: (reveal_type(value), value)[1]  # revealed: Unknown
```
