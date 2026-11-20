# Unbound

```toml
[environment]
python-version = "3.13"

[rules]
possibly-unresolved-reference = "error"
```

## Unbound

```py
x = foo  # error: [unresolved-reference] "Name `foo` used when not defined"
foo = 1

# No error `unresolved-reference` diagnostic is reported for `x`. This is
# desirable because we would get a lot of cascading errors even though there
# is only one root cause (the unbound variable `foo`).

# revealed: Unknown
reveal_type(x)
```

Note: in this particular example, one could argue that the most likely error would be a wrong order
of the `x`/`foo` definitions, and so it could be desirable to infer `Literal[1]` for the type of
`x`. On the other hand, there might be a variable `fob` a little higher up in this file, and the
actual error might have been just a typo. Inferring `Unknown` thus seems like the safest option.

## Repeated immutable Boolean guards

A local assigned under `if flag` is defined inside a later `if flag` when the Boolean flag is
unchanged. The same applies to repeated negated tests.

```py
def stable(flag: bool):
    if not flag:
        value = 1
    if not flag:
        print(value)

def stable_in_loop(flag: bool, rows: list[int]):
    for row in rows:
        if not flag:
            value = row
        if not flag:
            print(value)

def choose() -> bool:
    return bool(input())

def assigned():
    flag = choose()
    if flag:
        value = 1
    if flag:
        print(value)

def annotated():
    flag: bool = choose()
    if not not flag:
        value = 1
    if flag:
        print(value)

def exhaustive(flag: bool):
    if flag:
        value = 1
    elif not flag:
        value = 2
    else:
        undefined
    print(value)
    undefined  # error: [unresolved-reference]
```

## Occurrence context

An earlier guard may not dominate later guards and may already have a constant narrowed type.

```py
def nondominating(flag: bool):
    if flag is True:
        if flag:
            pass
    if not flag:
        undefined  # error: [unresolved-reference]

def contextual(flag: bool):
    if flag is True:
        if flag:
            value = 1
        print(value)
    elif not flag:
        other = 2
        print(other)

def narrowing(flag: bool):
    if flag:
        reveal_type(flag)  # revealed: Literal[True]
    else:
        reveal_type(flag)  # revealed: Literal[False]
```

## Bindings that can change

Definition identity does not establish one runtime value when a binding is repeated or captured.

```py
def reassigned(flag: bool):
    if not flag:
        value = 1
    flag = False
    if not flag:
        print(value)  # error: [possibly-unresolved-reference]

def deleted(flag: bool):
    if flag:
        value = 1
    del flag
    if flag:  # error: [unresolved-reference]
        print(value)  # error: [possibly-unresolved-reference]

def repeated_definition():
    for row in range(2):
        flag = bool(input())
        if row == 0:
            if flag:
                value = 1
        elif flag:
            print(value)  # error: [possibly-unresolved-reference]

def captured(flag: bool):
    if flag:
        value = 1
    def reset():
        nonlocal flag
        flag = True
    reset()
    if flag:
        print(value)  # error: [possibly-unresolved-reference]

def late_writer(flag: bool, rows: list[int]):
    def callback():
        pass
    for row in rows:
        if flag:
            value = 1
        callback()
        if flag:
            print(value)  # error: [possibly-unresolved-reference]
        def callback():
            nonlocal flag
            flag = True
```

## Unproved truthiness and unsupported guards

Dynamic values and objects with stateful truthiness retain independent evaluations. Compound
conditions and nonlocal reads also retain their ordinary occurrence-based behavior.

```py
from typing import Any

class Stateful:
    def __bool__(self) -> bool:
        return bool(input())

def stateful(flag: Stateful):
    if flag:
        value = 1
    if flag:
        print(value)  # error: [possibly-unresolved-reference]

def gradual(flag: Any):
    if flag:
        value = 1
    if flag:
        print(value)  # error: [possibly-unresolved-reference]

def unknown(flag):
    if flag:
        value = 1
    if flag:
        print(value)  # error: [possibly-unresolved-reference]

def compound(flag: bool, other: bool):
    if flag and other:
        value = 1
    if flag and other:
        print(value)  # error: [possibly-unresolved-reference]

def outer(flag: bool):
    def inner():
        if flag:
            value = 1
        if flag:
            print(value)  # error: [possibly-unresolved-reference]
```
