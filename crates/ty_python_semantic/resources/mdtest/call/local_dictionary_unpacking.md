# Local dictionary keyword unpacking

## Complete key sets

A fresh local dictionary used only as a direct `**name` argument has a complete key set. Repeated
calls unpack its values without exposing the dictionary itself. Optional parameters absent from the
dictionary therefore receive their defaults.

```py
from typing import TypeVar

T = TypeVar("T")

def consume(tags: list[str], testonly: bool, note: str | None = None): ...
def repeated():
    options = dict(tags=["example"], testonly=True)
    consume(**options)
    consume(**options, note="explicit")
    consume(**options, note=1)  # error: [invalid-argument-type]

    options = {"tags": ["replacement"], "testonly": False}
    consume(**options)
```

Complete entries participate in ordinary argument validation, including required parameters and
duplicate keywords.

```py
def invalid():
    options = dict(tags=[1], testonly=True)
    consume(**options)  # error: [invalid-argument-type]

def duplicate():
    options = dict(tags=["example"], testonly=True)
    consume(**options, testonly=False)  # error: [parameter-already-assigned]

def missing():
    options = dict(tags=["example"])
    consume(**options)  # error: [missing-argument]

def extra():
    options = dict(tags=["example"], testonly=True, extra=1)
    consume(**options)  # error: [unknown-argument]

def empty():
    options = {}
    consume(**options)  # error: [missing-argument]

    options = dict()
    consume(**options)  # error: [missing-argument]

def duplicate_literal_keys():
    options = {"tags": [1], "tags": ["example"], "testonly": True}
    consume(**options)

def first(values: list[T], note: str | None = None) -> T:
    return values[0]

def generic():
    options = dict(values=["example"])
    reveal_type(first(**options))  # revealed: str
```

## Other uses preserve partial observations

Completeness requires every use of the symbol to be a direct keyword expansion, throughout the
function. Aliases, captures, and ordinary arguments can expose the dictionary to mutation. Reads and
direct key writes also use the existing partial observations. This is a conservative source
analysis; dynamically accessing a function's frame or locals is outside its effect model.

```py
def consume(*, note: str | None = None, **kwargs: object): ...
def save(value: object): ...
def argument():
    options = dict(tags=["example"], testonly=True)
    save(options)
    consume(**options)  # error: [invalid-argument-type]

def later_alias():
    options = dict(tags=["example"], testonly=True)
    consume(**options)  # error: [invalid-argument-type]
    alias = options

def assignment():
    options = dict(tags=["example"], testonly=True, note="initial")
    options["note"] = "known"
    consume(**options)
    options["note"] = False
    consume(**options)  # error: [invalid-argument-type]

def deletion():
    options = dict(tags=["example"], testonly=True, note="known")
    del options["note"]
    consume(**options)  # error: [invalid-argument-type]

def method():
    options = dict(tags=["example"], testonly=True)
    options.update(note=True)
    consume(**options)  # error: [invalid-argument-type]
```

Captures and loop-carried escapes apply to the whole symbol, including later allocations.

```py
def capture():
    def nested():
        save(options)
    options = dict(tags=["example"], testonly=True)
    consume(**options)  # error: [invalid-argument-type]

def nonlocal_write():
    def nested():
        nonlocal options
        options = dict(tags=["changed"], testonly=False, note=1)
    options = dict(tags=["example"], testonly=True)
    nested()
    consume(**options)  # error: [invalid-argument-type]

def loop(flag: bool):
    options = dict(tags=["example"], testonly=True)
    while flag:
        save(options)
        options = dict(tags=["next"], testonly=False)
        consume(**options)  # error: [invalid-argument-type]
```

## Assignment and initializer boundaries

The proof uses one reaching, accepted assignment to a single local name. An initializer with
positional inputs, spreads, or computed keys keeps its ordinary dictionary behavior.

```py
def consume(*, note: str | None = None, **kwargs: object): ...
def required(extra: int): ...
def multi_target():
    alias = options = {}
    alias["extra"] = 1
    required(**options)

def branch(flag: bool):
    if flag:
        options = dict(tags=["a"], testonly=True)
    else:
        options = dict(tags=["b"], testonly=False)
    consume(**options)  # error: [invalid-argument-type]

def within_branch(flag: bool):
    if flag:
        options = dict(tags=["a"], testonly=True)
        consume(**options)

def annotated():
    options: dict[str, object] = dict(tags=["example"], testonly=True)
    consume(**options)  # error: [invalid-argument-type]

def rejected(options: dict[str, int]):
    options = dict(tags=["example"], testonly=True)  # error: [invalid-assignment]
    consume(**options)  # error: [invalid-argument-type]
```

Additional constructor inputs and computed keys preserve partial dictionary information.

```py
def positional():
    options = dict({"tags": ["example"]}, testonly=True)
    consume(**options)  # error: [invalid-argument-type]

def spread():
    options = dict(tags=["example"], **{"testonly": True})
    consume(**options)  # error: [invalid-argument-type]

def literal_spread():
    options = {"tags": ["example"], **{"testonly": True}}
    consume(**options)  # error: [invalid-argument-type]

def computed_key(key: str):
    options = {"tags": ["example"], key: True}
    consume(**options)  # error: [invalid-argument-type]
```

Module and class dictionaries are accessible from other code, as are explicit global references.

```py
options = dict(tags=["example"], testonly=True)
consume(**options)  # error: [invalid-argument-type]

class Container:
    options = dict(tags=["example"], testonly=True)
    consume(**options)  # error: [invalid-argument-type]

def global_reference():
    global options
    consume(**options)  # error: [invalid-argument-type]
```

## Shadowed constructors

A function named `dict` may return arbitrary keys, including when called without arguments.

```py
from builtins import dict as Dictionary

def dict(**values: object) -> Dictionary[str, int]:
    return {"extra": 1}

def required(extra: int): ...
def shadowed():
    options = dict()
    required(**options)
```
