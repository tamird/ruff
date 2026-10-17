# Narrowing using `getattr()`

## Falsy defaults

A truthy result with a falsy default establishes that the attribute exists and is truthy. The
declared value type is preserved.

```py
from typing import final

@final
class WithValue:
    value: int | None

@final
class WithoutValue: ...

def check(value: WithValue | WithoutValue):
    if getattr(value, "value", None):
        reveal_type(value.value)  # revealed: int & ~AlwaysFalsy
    else:
        # error: [unresolved-attribute]
        value.value
```

## Truthy defaults

A falsy result with a truthy default likewise establishes attribute presence. A truthy result could
have come from the default, so it supplies no presence guarantee.

```py
def check(value: object):
    if not getattr(value, "value", True):
        reveal_type(value.value)  # revealed: ~AlwaysTruthy
    else:
        # error: [unresolved-attribute]
        value.value
```

## No default

When no default is supplied, a successful lookup establishes presence in either branch.

```py
def check(value: object):
    if getattr(value, "value"):
        reveal_type(value.value)  # revealed: ~AlwaysFalsy
    else:
        reveal_type(value.value)  # revealed: ~AlwaysTruthy
```

## Unknown defaults and names

A default with unknown truthiness can produce either branch without reading an attribute. A dynamic
name does not identify a particular field.

```py
def check(value: object, default: object, name: str):
    if getattr(value, "value", default):
        # error: [unresolved-attribute]
        value.value
    if getattr(value, name, None):
        # error: [unresolved-attribute]
        value.value
    if getattr(value, "not-an-identifier", None):
        reveal_type(value)  # revealed: object
```

## Nested receivers and invalidation

Presence applies to the receiver used in the lookup. Replacing it invalidates that information.

```py
class Context:
    attributes: object

def nested(context: Context):
    if getattr(context.attributes, "value", None):
        reveal_type(context.attributes.value)  # revealed: ~AlwaysFalsy
        context.attributes = object()
        # error: [unresolved-attribute]
        context.attributes.value

def during_call(value: object):
    if getattr(value, "value", (value := None)):
        reveal_type(value)  # revealed: None
```

## Builtin aliases

The callee's identity determines narrowing, including imported aliases and shadowed names.

```py
from builtins import getattr as lookup

def check(value: object):
    if lookup(value, "value", None):
        reveal_type(value.value)  # revealed: ~AlwaysFalsy

def getattr(value: object, name: str, default: object) -> bool:
    return True

def shadowed(value: object):
    if getattr(value, "value", None):
        # error: [unresolved-attribute]
        value.value
```

## Getters

Successful lookup retains the declared return type of a property or dynamic getter, even when that
getter can also raise `AttributeError`.

```py
class Property:
    @property
    def value(self) -> int | None:
        raise AttributeError("unavailable")

class Dynamic:
    def __getattr__(self, name: str) -> int | None:
        raise AttributeError(name)

def check(value: Property | Dynamic):
    # error: [truthiness-test-of-none-union]
    if getattr(value, "value", None):
        reveal_type(value.value)  # revealed: int
```
