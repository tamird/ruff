# Dictionary contents at a call

## Assignments and copies

The contents of a fresh dictionary follow its reaching assignment. A shallow copy starts a new
mapping, and explicit keyword values replace the corresponding source entries.

```py
def consume(value: int, note: str = ""): ...
def copies():
    values = {"value": 1, "note": "ok"}
    consume(**values)
    copied = dict(values, note="new")
    consume(**copied)
    copied["value"] = "bad"
    consume(**copied)  # error: [invalid-argument-type]
    consume(**values)
    values = {"note": "missing"}
    consume(**values)  # error: [missing-argument]
```

## Updates and deletions

Direct stores and dictionary methods change the observed values in source order.

```py
def consume(value: int, note: str = ""): ...
def empty(): ...
def mutations():
    values = {"value": 1, "note": "ok"}
    values.update(value="bad")
    consume(**values)  # error: [invalid-argument-type]
    values["value"] = 2
    consume(**values)
    del values["value"]
    consume(**values)  # error: [missing-argument]
    values.clear()
    empty(**values)

def unpacked_target():
    values = {"value": 1}
    _, values["value"] = (0, "bad")  # error: [invalid-assignment]
    consume(**values)  # error: [invalid-argument-type]

def augmented_target():
    def with_other(value: int, other: float): ...
    values = {"value": 1, "other": 0.0}
    values["value"] /= 2
    with_other(**values)  # error: [invalid-argument-type]
```

## Opaque exposure

Passing a dictionary to an ordinary callable leaves key presence uncertain. Known value refinements
remain useful, including values written after exposure; a clear or deletion removes the previous
restriction. Rebinding to a fresh dictionary starts a new object lifetime.

```py
from typing import Any

def opaque(value: Any): ...
def consume(value: int = 0): ...
def empty(): ...
def exposed():
    values = {"extra": 1, "value": "old"}
    opaque(values)
    empty(**values)
    values["value"] = "bad"
    consume(**values)  # error: [invalid-argument-type]
    values.clear()
    consume(**values)
    values["value"] = "bad"
    del values["value"]
    consume(**values)
    values = {"extra": 1}
    empty(**values)  # error: [unknown-argument]

def insertion():
    values = {"value": 1}
    del values["value"]
    opaque(values)
    consume(**values)
```

## Argument evaluation order

A positional dictionary source is copied when the constructor is invoked, after all arguments have
evaluated. A keyword unpack is expanded when that individual argument is evaluated.

```py
def note_only(note: int): ...
def copy_after_pop():
    values = {"extra": 42}
    note_only(**dict(values, note=values.pop("extra")))

def unpack_before_pop():
    values = {"extra": 42}
    note_only(**values, note=values.pop("extra"))  # error: [unknown-argument]
```

## Retained aliases and captures

A saved reference can mutate an object later. A closure that refers to the lexical binding can also
see fresh objects assigned to that binding, whereas a default argument retains its old value.

```py
def empty(): ...
def alias():
    values = {"extra": 1}
    saved = values
    values["extra"] = 2
    saved.clear()
    empty(**values)
    values = {"extra": 1}
    empty(**values)  # error: [unknown-argument]

def bound_method():
    values = {"extra": 1}
    remove = values.clear
    values["extra"] = 2
    remove()
    empty(**values)

def capture():
    values = {"extra": 1}
    def remove():
        values.clear()
    values = {"extra": 2}
    remove()
    empty(**values)

def capture_before_assignment():
    def remove():
        values.clear()
    values = {"extra": 2}
    remove()
    empty(**values)

def default_capture():
    values = {"extra": 1}
    def remove(saved=values):
        saved.clear()
    values = {"extra": 2}
    remove()
    empty(**values)  # error: [unknown-argument]

def retained_keyword():
    values = {"extra": 1}
    saved = dict(payload=values)
    values["extra"] = 2
    saved["payload"].clear()
    empty(**values)

def retained_default():
    values = {"extra": 1}
    saved = values.get("missing", values)
    if isinstance(saved, dict):
        saved.clear()
    empty(**values)
```

## Loop transfers

Effects inside a loop reach later iterations through the ordinary loop header. A store that executes
only on some paths does not establish a required key.

```py
def consume(value: int, note: str = ""): ...
def empty(): ...
def loops(flags: list[bool]):
    values = {"value": 1, "note": "ok"}
    for flag in flags:
        consume(**values)  # error: [invalid-argument-type]
        values.update(value="bad")
    values.clear()
    empty(**values)

def optional(flags: list[bool]):
    values = {}
    for flag in flags:
        values["value"] = 1
    consume(**values)

def fresh_without_capture(flags: list[bool]):
    for flag in flags:
        values = {"extra": 1}
        empty(**values)  # error: [unknown-argument]

def capture_in_loop(flags: list[bool]):
    values = {"extra": 1}
    for flag in flags:
        empty(**values)
        def remove():
            values.clear()
        remove()

def recursive_copies(flags: list[bool]):
    values = {"value": 1}
    for flag in flags:
        values = dict(values)
        consume(**values)
    consume(**values)
```

## Guards and overwrites

Key predicates narrow the corresponding contents values. Later mutations establish new contents
definitions, so a previous predicate or saved boolean cannot narrow the replacement value.

```py
def strings(value: str): ...
def guarded(initial: object):
    values = {"value": initial}
    if isinstance(values["value"], str):
        strings(**values)
        values.update(value=42)
        strings(**values)  # error: [invalid-argument-type]

def saved_predicate(initial: object):
    values = {"value": initial}
    ready = isinstance(values["value"], str)
    values.update(value=42)
    if ready:
        strings(**values)  # error: [invalid-argument-type]

def impossible_guard(initial: object):
    values = {"value": initial}
    values.update(value=42)
    if isinstance(values["value"], str):
        strings(**values)
        strings(**dict(values))
        strings(**{**values})

def impossible_update(initial: object):
    source = {"value": 42}
    target = {"value": initial}
    keywords = {"value": initial}
    if isinstance(source["value"], str):
        target.update(source)
        strings(**target)
        keywords.update(**source)
        strings(**keywords)

def pattern(initial: object):
    values = {"value": initial}
    match values["value"]:
        case str():
            strings(**values)
            values.update(value=42)
            strings(**values)  # error: [invalid-argument-type]

def sequence_pattern(initial: object):
    values = {"value": initial}
    match [values["value"]]:
        case [str()]:
            strings(**values)
            values.update(value=42)
            strings(**values)  # error: [invalid-argument-type]

def other_predicates(initial: object):
    values = {"value": initial}
    if type(values["value"]) is str:
        strings(**values)
    if values["value"].__class__ is str:
        strings(**values)

def unrelated_saved_guard(initial: object):
    def with_other(value: str, other: int): ...
    values = {"value": initial}
    ready = isinstance(values["value"], str)
    values["other"] = 1
    if ready:
        strings(value=values["value"])
        with_other(**values)

def readonly_saved_guard(initial: object):
    values = {"value": initial}
    ready = isinstance(values["value"], str)
    values.get("value")
    if ready:
        strings(**values)

def unrelated_update(initial: object):
    def with_other(value: str, other: int): ...
    values = {"value": initial}
    ready = isinstance(values["value"], str)
    values.update(other=1)
    if ready:
        with_other(**values)

def carried_guard(entries: list[tuple[bool, object]]):
    values = {"value": object()}
    ready = False
    for flag, initial in entries:
        values.update(value=initial)
        if flag:
            ready = isinstance(values["value"], str)
            continue
        if ready:
            strings(**values)  # error: [invalid-argument-type]
```

## Deferred and eager captures

A saved closure or generator can access a later value of its captured binding. Eager comprehension
evaluation and default arguments retain only the object they evaluated.

```py
from typing import Callable

def empty(): ...
def carried_capture(flags: list[bool]):
    callbacks: list[Callable[[], None]] = []
    for flag in flags:
        values = {"extra": 1}
        for callback in callbacks:
            callback()
        empty(**values)
        if flag:
            def remove():
                values.clear()
            callbacks.append(remove)

def deferred_generator():
    values = {"extra": 1}
    pending = (values.clear() for _ in [1])
    values = {"extra": 2}
    next(pending)
    empty(**values)

def eager_comprehension():
    values = {"extra": 1}
    [values.clear() for _ in [1]]
    values = {"extra": 2}
    empty(**values)  # error: [unknown-argument]

def eager_generator_iterable():
    values = {"extra": 1}
    pending = (None for _ in [values.clear()])
    values = {"extra": 2}
    next(pending)
    empty(**values)  # error: [unknown-argument]

values = {"extra": 1}

class BeforeBinding:
    values.clear()
    values = {}

empty(**values)

later = {"extra": 1}

class AfterBinding:
    later = {}
    later.clear()

empty(**later)  # error: [unknown-argument]

shared = {"extra": 1}

def remove_global():
    global shared
    shared.clear()

shared = {"extra": 2}
remove_global()
empty(**shared)

fallback = {"extra": 1}

def enclosing_class():
    fallback = {"extra": 2}
    class Inner:
        fallback.clear()
        fallback = {}

    empty(**fallback)  # error: [unknown-argument]

enclosing_class()
empty(**fallback)
```

## Failed stores and exposure of absent keys

An exception during a store preserves the preceding state. Exposure removes absence evidence,
including absence expressed through a type alias.

```toml
[environment]
python-version = "3.15"
```

```py
from typing import Any, Never, NotRequired, TypedDict

def integers(value: int): ...
def opaque(value: Any): ...
def failed_store():
    values = {"value": 1}
    try:
        values["value"] = "bad"
    except Exception:
        integers(**values)
    else:
        integers(**values)  # error: [invalid-argument-type]

type Gone = Never

class Absent(TypedDict, closed=True):
    value: NotRequired[Gone]

def inserted(source: Absent):
    values = dict(source)
    opaque(values)
    integers(**values)

def deletion_order(other: dict[int, int]):
    def position() -> int:
        return 0
    values = {"extra": 1}
    del values["extra"], other[position(**values)]

def annotation_only():
    values = {"value": 1}
    values["value"]: str  # error: [invalid-type-form]
    integers(**values)
```

## Other store and handoff boundaries

Loop and context-manager targets invalidate preceding dictionary contents even when the target's
assigned value is unavailable to contents inference. A yielded mapping can remain accessible to its
caller after the generator resumes.

```py
from typing import Any

def integers(value: int): ...
def empty(): ...

class Manager:
    def __enter__(self) -> int:
        return 1

    def __exit__(self, *args): ...

def loop_target(rows: list[int]):
    values: dict[str, Any] = {"value": "old"}
    for values["value"] in rows:
        integers(**values)

def with_target():
    values: dict[str, Any] = {"value": "old"}
    with Manager() as values["value"]:
        integers(**values)

def comprehension_target():
    values: dict[str, Any] = {"value": "old"}
    [integers(**values) for values["value"] in [1]]

def nested_deletion(other: dict[int, int]):
    def position() -> int:
        return 0
    values = {"extra": 1}
    del (values["extra"], [other[position(**values)]])
    empty(**values)

def yielded():
    values = {"extra": 1}
    yield values
    values["extra"] = 2
    empty(**values)

def delegated():
    values = {"extra": 1}
    yield from [values]
    values["extra"] = 2
    empty(**values)

def loop_handoff(flags: list[bool]):
    values = {"extra": 1}
    for flag in flags:
        if flag:
            empty(**values)
        yield values
```

## Mapping key domains

Mappings with restricted key types retain ordinary key-sensitive argument matching. Their value type
does not constrain unrelated keyword parameters.

```py
from typing import Literal

def consume(value: int, enabled: bool = False): ...
def finite(values: dict[Literal["value"], int]):
    consume(**values)

def separate_domains(values: dict[Literal["value"], int] | dict[str, bool]):
    consume(**values)

def wrong(values: dict[Literal["value"], str]):
    consume(**values)  # error: [invalid-argument-type]

def absent(values: dict[Literal["other"], int]):
    consume(**values)

def guarded(values: dict[Literal["value"], int | str]):
    if isinstance(values["value"], int):
        consume(**values)  # error: [invalid-argument-type]
```
