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

## String-key assignments

Direct assignments to literal string keys preserve completeness. Existing flow analysis determines
each value and whether the key is always present. Like optional TypedDict keys, a conditional key
can satisfy a required parameter. Its value is checked when it could be supplied. Assignments still
obey the dictionary's inferred value type.

```py
def consume(tags: list[str], testonly: bool, note: list[str] | None = None): ...
def conditional(note: list[str] | None):
    options = dict(tags=["example"], testonly=True)
    if note is not None:
        options["note"] = note
    consume(**options)

def overwrite(flag: bool):
    options = dict(tags=["example"], testonly=True, note=["initial"])
    if flag:
        options["note"] = ["replacement"]
    consume(**options)
    if flag:
        options["note"] = False
    consume(**options)  # error: [invalid-argument-type]

def optional_bad_value(flag: bool):
    options = dict(tags=["example"], testonly=True)
    if flag:
        options["note"] = False
    consume(**options)  # error: [invalid-argument-type]

def optional_unknown_key(flag: bool):
    options = dict(tags=["example"], testonly=True)
    if flag:
        options["extra"] = True
    consume(**options)  # error: [unknown-argument]

def required(value: int, other: int = 0): ...
def optional_required(flag: bool):
    options = dict(other=0)
    if flag:
        options["value"] = 1
        required(**options)
    required(**options)
    options["value"] = 2
    required(**options)

def both_branches(flag: bool):
    options = dict(other=0)
    if flag:
        options["value"] = 1
    else:
        options["value"] = 2
    required(**options)

def optional_duplicate(flag: bool):
    options = dict(tags=["example"], testonly=True)
    if flag:
        options["note"] = ["value"]
    consume(**options, note=["explicit"])  # error: [parameter-already-assigned]
    consume(note=["explicit"], **options)  # error: [parameter-already-assigned]

from typing import TypeVar

T = TypeVar("T")

def first(values: list[T], note: list[str] | None = None) -> T:
    return values[0]

def generic(flag: bool):
    options = dict(values=["example"])
    if flag:
        options["note"] = ["value"]
    reveal_type(first(**options))  # revealed: str
```

Optional keys remain possible matches alongside other unpacked inputs. Duplicate arguments and
values from later open mappings are still checked.

```py
def single(value: int): ...
def other_inputs(
    flag: bool,
    args: tuple[int, ...],
    kwargs: dict[str, int],
    bad_kwargs: dict[str, str],
):
    options = {}
    if flag:
        options["value"] = 1
    single(**options)
    single(*args, **options)  # error: [parameter-already-assigned]
    single(*(1,), **options)  # error: [parameter-already-assigned]
    single(**options, **kwargs)  # error: [parameter-already-assigned]
    # error: [parameter-already-assigned]
    # error: [invalid-argument-type]
    single(**options, **bad_kwargs)
```

TypedDict extra items must also be checked against parameters supplied only conditionally by an
earlier mapping.

```py
from typing_extensions import TypedDict

class ExtraStrings(TypedDict, extra_items=str): ...

def with_default(value: int = 0, **kwargs: object): ...
def extra_items(flag: bool, extra: ExtraStrings):
    options = {}
    if flag:
        options["value"] = 1
    with_default(**options, **extra)  # error: [invalid-argument-type]
```

## Other uses preserve partial observations

Completeness requires every use of the symbol to be a direct keyword expansion or tracked string-key
assignment, throughout the function. Aliases, captures, and ordinary arguments can expose the
dictionary to mutation. Reads also use the existing partial observations. This is a conservative
source analysis; dynamically accessing a function's frame or locals is outside its effect model.

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

def dynamic_key(key: str):
    options = dict(tags=["example"], testonly=True)
    options[key] = True
    consume(**options)  # error: [invalid-argument-type]

def augmented():
    options = dict(tags=["example"], testonly=True)
    options["tags"] += ["other"]
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

## Forwarding through a ParamSpec

Known dictionary keys are divided between a wrapper's own parameters and the target callable.
Conditional keys retain their presence and value constraints after forwarding.

```py
from typing import Callable, ParamSpec

P = ParamSpec("P")

def forward(callback: Callable[P, None], prefix: int, *args: P.args, **kwargs: P.kwargs) -> None:
    callback(*args, **kwargs)

def target(x: int, y: str = "", note: str = "") -> None: ...
def required(x: int, y: str, note: str = "") -> None: ...
def local(flag: bool):
    options = dict(prefix=0, x=1, note="")
    if flag:
        options["y"] = "value"
    forward(target, **options)
    forward(required, **options)
    if flag:
        options["y"] = 1
    forward(target, **options)  # error: [invalid-argument-type]
```
