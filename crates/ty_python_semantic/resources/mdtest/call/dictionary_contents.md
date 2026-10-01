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

class Holder:
    values: dict[str, int | str]

def shared_members(left: Holder, right: Holder):
    left.values = right.values = {"value": 1}
    right.values["value"] = "bad"
    # error: [invalid-argument-type] "Expected `int`, found `int | str`"
    # error: [invalid-argument-type] "Expected `str`, found `int | str`"
    consume(**left.values)
```

## Nested dictionaries: calls on containing values

Passing or storing a containing value can expose its existing child dictionaries.

```py
def integers(value: int) -> None:
    pass

class Holder:
    inner: dict[str, int | str]

def mutate_outer(outer: dict[str, dict[str, int | str]]) -> None:
    outer["inner"]["value"] = "changed"

def nested_opaque() -> None:
    outer: dict[str, dict[str, int | str]] = {"inner": {"value": 1}}
    integers(**outer["inner"])  # no diagnostic
    mutate_outer(outer)
    integers(**outer["inner"])  # error: [invalid-argument-type]

def nested_alias() -> None:
    outer: dict[str, dict[str, int | str]] = {"inner": {"value": 1}}
    alias = outer
    mutate_outer(alias)
    integers(**outer["inner"])  # error: [invalid-argument-type]

def mutate_holder(holder: Holder) -> None:
    holder.inner["value"] = "changed"

def member_opaque(holder: Holder) -> None:
    holder.inner = {"value": 1}
    integers(**holder.inner)  # no diagnostic
    mutate_holder(holder)
    integers(**holder.inner)  # error: [invalid-argument-type]

def separate_parent(holder: Holder) -> None:
    holder.inner = {"value": 1}
    copied = dict(holder.inner, parent=holder)
    parent = copied["parent"]
    if isinstance(parent, Holder):
        parent.inner["value"] = "changed"
    integers(**holder.inner)  # error: [invalid-argument-type]
```

## Nested dictionaries: readonly and child operations

Discarded readonly results preserve child values. Accessing or passing an admitted builtin child
does not record an escape of its containing object.

```py
def integers(value: int) -> None:
    pass

class Holder:
    inner: dict[str, int | str]

def nested_readonly() -> None:
    outer: dict[str, dict[str, int | str]] = {"inner": {"value": 1}}
    outer["inner"].get("value")
    outer.get("inner")
    outer.copy()
    outer.keys()
    outer.items()
    outer.values()
    dict(outer)
    size = len(outer)
    integers(**outer["inner"])  # no diagnostic

def member_readonly(holder: Holder) -> None:
    holder.inner = {"value": 1}
    holder.inner.get("value")
    value = holder.inner.get("value")
    copied = dict(holder.inner)
    size = len(holder.inner)
    integers(**holder.inner)  # no diagnostic

def member_after_readonly(holder: Holder) -> None:
    holder.inner = {"value": 1}
    holder.inner.get("value")
    holder.inner = {"value": 2}
    integers(**holder.inner)  # no diagnostic

def member_after_scalar_read(holder: Holder) -> None:
    holder.inner = {"value": 1}
    value = holder.inner.get("value")
    holder.inner = {"value": 2}
    integers(**holder.inner)  # no diagnostic

def mutate_inner(values: dict[str, int | str]) -> None:
    values["value"] = "changed"

def member_after_child_call(holder: Holder) -> None:
    holder.inner = {"value": 1}
    mutate_inner(holder.inner)
    holder.inner = {"value": 2}
    integers(**holder.inner)  # no diagnostic
```

## Nested dictionaries: returned children and shallow copies

Consumed return values and views can retain mutable children.

```py
def integers(value: int) -> None:
    pass

def returned_child() -> None:
    outer: dict[str, dict[str, int | str]] = {"inner": {"value": 1}}
    child = outer.get("inner")
    if child is not None:
        child["value"] = "changed"
        integers(**outer["inner"])  # error: [invalid-argument-type]

def shallow_copy() -> None:
    outer: dict[str, dict[str, int | str]] = {"inner": {"value": 1}}
    copied = outer.copy()
    copied["inner"]["value"] = "changed"
    integers(**outer["inner"])  # error: [invalid-argument-type]

def constructor_copy() -> None:
    outer: dict[str, dict[str, int | str]] = {"inner": {"value": 1}}
    copied = dict(outer)
    copied["inner"]["value"] = "changed"
    integers(**outer["inner"])  # error: [invalid-argument-type]

def returned_view() -> None:
    outer: dict[str, dict[str, int | str]] = {"inner": {"value": 1}}
    keys = outer.keys()
    keys.mapping["inner"]["value"] = "changed"
    integers(**outer["inner"])  # error: [invalid-argument-type]
```

## Nested dictionaries: escaped bound methods

A stored or forwarded bound method retains its receiver.

```py
from typing import Callable

def integers(value: int) -> None:
    pass

def mutate_getter(getter: Callable[[str], dict[str, int | str] | None]) -> None:
    child = getter("inner")
    if child is not None:
        child["value"] = "changed"

def bound_method_argument() -> None:
    outer: dict[str, dict[str, int | str]] = {"inner": {"value": 1}}
    mutate_getter(outer.get)
    integers(**outer["inner"])  # error: [invalid-argument-type]

def bound_method_storage() -> None:
    outer: dict[str, dict[str, int | str]] = {"inner": {"value": 1}}
    saved = outer.get
    mutate_getter(saved)
    integers(**outer["inner"])  # error: [invalid-argument-type]
```

## Nested dictionaries: replacement after earlier exposure

Replacing a child does not replace its containing object. A fresh root allocation resets the root,
while rebinding it to an alias does not.

```py
def integers(value: int) -> None:
    pass

class Holder:
    inner: dict[str, int | str]

def replace_after_alias() -> None:
    outer: dict[str, dict[str, int | str]] = {}
    alias = outer
    outer["inner"] = {"value": 1}
    alias["inner"]["value"] = "changed"
    integers(**outer["inner"])  # error: [invalid-argument-type]

def rebind_after_alias() -> None:
    outer: dict[str, dict[str, int | str]] = {}
    alias = outer
    outer = {"inner": {"value": 1}}
    alias["inner"] = {"value": "changed"}
    integers(**outer["inner"])  # no diagnostic

def rebind_to_alias() -> None:
    outer: dict[str, dict[str, int | str]] = {}
    alias = outer
    outer = alias
    outer["inner"] = {"value": 1}
    alias["inner"]["value"] = "changed"
    integers(**outer["inner"])  # error: [invalid-argument-type]

def member_after_alias(holder: Holder) -> None:
    alias = holder
    holder.inner = {"value": 1}
    alias.inner["value"] = "changed"
    integers(**holder.inner)  # error: [invalid-argument-type]

def nested_parent_replacement() -> None:
    outer: dict[str, dict[str, dict[str, int | str]]] = {"inner": {"nested": {}}}
    outer["inner"]["nested"] = {"value": 1}
    integers(**outer["inner"]["nested"])  # no diagnostic

def nested_replacement_after_alias() -> None:
    outer: dict[str, dict[str, dict[str, int | str]]] = {}
    alias = outer
    outer["inner"] = {"nested": {}}
    outer["inner"]["nested"] = {"value": 1}
    alias["inner"]["nested"]["value"] = "changed"
    integers(**outer["inner"]["nested"])  # error: [invalid-argument-type]
```

## Nested dictionaries: loop effects

Loop headers reserve the same affected contents as straight-line calls.

```py
def integers(value: int) -> None:
    pass

def mutate_outer(outer: dict[str, dict[str, int | str]]) -> None:
    outer["inner"]["value"] = "changed"

def loop_parent(count: int) -> None:
    outer: dict[str, dict[str, int | str]] = {"inner": {"value": 1}}
    for _ in range(count):
        mutate_outer(outer)
    integers(**outer["inner"])  # error: [invalid-argument-type]

def loop_readonly(count: int) -> None:
    outer: dict[str, dict[str, int | str]] = {"inner": {"value": 1}}
    for _ in range(count):
        outer.get("inner")
    integers(**outer["inner"])  # no diagnostic
```

## Nested dictionaries: unobserved caller aliases

Ordinary access paths do not relate aliases supplied through separate parameters. If `incoming`
contains `parent`, the mutation below can replace the new child. Ordinary checking retains its value
refinement; implementation validation must still refuse the unsupported contract.

```py
def integers(value: int) -> None:
    pass

def hidden_backreference(parent: dict[str, object], incoming: dict[str, dict[str, object]]) -> None:
    parent["inner"] = dict(incoming)
    other = parent["inner"].get("parent")
    parent["inner"] = {"value": 1}
    if other is not None:
        other["inner"] = {"value": "changed"}
    integers(**parent["inner"])  # no diagnostic
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

## Finite key writes

A write through a union of literal keys changes only those entries. Each possible new key is
optional; a previously present key remains present and retains its previous value as a possibility.

```py
from typing import Any, Literal
from ty_extensions._internal import Unknown

def consume(value: int, left: None = None, right: None = None): ...
def finite(key: Literal["left", "right"]):
    values = {"value": 1}
    values[key] = None
    consume(**values)

def overwritten(key: Literal["value", "left"]):
    values = {"value": 1}
    values[key] = None
    consume(**values)  # error: [invalid-argument-type]
```

Loops may execute zero or multiple writes. Keys outside the finite domain retain their values.

```py
def loop(keys: list[Literal["left", "right"]]):
    values = {"value": 1}
    for key in keys:
        values[key] = None
    consume(**values)

def skipped(key: Literal["value", "left"]):
    values = {"value": 1}
    if False:
        values[key] = None
    consume(**values)
```

Broad or gradual key domains can overwrite other entries.

```py
def broad(key: str):
    values = {"value": 1}
    values[key] = None
    consume(**values)  # error: [invalid-argument-type]

def gradual(key: Any):
    values = {"value": 1}
    values[key] = None
    consume(**values)  # error: [invalid-argument-type]

def unresolved(key: Unknown):
    values = {"value": 1}
    values[key] = None
    consume(**values)  # error: [invalid-argument-type]
```

A deleted key stays absent when every possible write targets another name. Including that key among
the alternatives makes it possibly present again.

```py
def deleted(key: Literal["left", "right"]):
    values = {"value": 1, "left": None}
    values.pop("left")
    values[key] = None
    consume(left=None, **values)  # error: [parameter-already-assigned]

def absent(key: Literal["right", "value"]):
    values = {"value": 1, "left": None}
    values.pop("left")
    values[key] = 2
    def consume_int(value: int, left: None, right: int = 0): ...
    consume_int(left=None, **values)
```

## Closed TypedDict mutations

A closed `TypedDict` describes every possible key. Removing an optional key lets a caller supply
that keyword explicitly. The remaining fields retain their declared value types. These observations
follow ordinary flow narrowing: indirect mutations through untracked aliases are not modeled.

```py
from typing import Callable
from typing_extensions import NotRequired, ReadOnly, TypedDict

class Values(TypedDict, closed=True):
    value: int
    note: NotRequired[str]

def consume(value: int, note: str = ""): ...
def popped(values: Values):
    values.pop("note", None)
    consume(note="replacement", **values)

def deleted(values: Values):
    del values["note"]
    consume(note="replacement", **values)

def conditional(values: Values, remove: bool):
    if remove:
        values.pop("note", None)
    consume(note="replacement", **values)  # error: [parameter-already-assigned]

def reinserted(values: Values):
    values.pop("note", None)
    values["note"] = "again"
    consume(note="replacement", **values)  # error: [parameter-already-assigned]

def updated(values: Values):
    values.pop("note", None)
    values.update(note="again")
    consume(note="replacement", **values)  # error: [parameter-already-assigned]

def wrong_value(values: Values):
    values.pop("note", None)
    values["value"] = "bad"  # error: [invalid-assignment]
    consume(**values)  # error: [invalid-argument-type]
```

Dictionary unions preserve the observed entries of each operand. The resulting copy is independent
of later key writes to its source.

```py
def merged(values: Values):
    values.pop("note", None)
    consume(note="replacement", **(values | {}))
    consume(note="replacement", **({} | values))
    consume(note="replacement", **(values | {} | {}))

def copied(values: Values):
    values.pop("note", None)
    copied = values | {}
    values["note"] = "again"
    consume(note="replacement", **copied)
    consume(note="replacement", **(values | {}))  # error: [parameter-already-assigned]
```

Passing the dictionary to an ordinary callable restores the declared possibilities. A returned value
likewise follows its declared schema; a matching return annotation does not preserve deleted keys.

```py
def exposed(values: Values, mutate: Callable[[Values], None]):
    values.pop("note", None)
    mutate(values)
    consume(note="replacement", **values)  # error: [parameter-already-assigned]

def identity(values: Values) -> Values:
    return values

def returned(values: Values):
    values.pop("note", None)
    consume(note="replacement", **identity(values))  # error: [parameter-already-assigned]
```

Clearing a dictionary removes every key when its schema permits arbitrary deletion.

```py
class OptionalValues(TypedDict, closed=True):
    value: NotRequired[int]
    note: NotRequired[str]

def cleared(values: OptionalValues):
    values.clear()
    consume(value=1, note="replacement", **values)
```

The declared schema still governs whether a write or deletion is valid.

```py
class Restricted(TypedDict, closed=True):
    value: int
    note: ReadOnly[NotRequired[str]]

def restricted(values: Restricted):
    values.pop("value")  # error: [invalid-argument-type]
    del values["note"]  # error: [invalid-argument-type]
```

## Bound method escapes

Passing a bound method to another callable retains its dictionary receiver. A call through a
conditional expression can likewise mutate the receiver before later keyword arguments use it.

```py
from typing import Callable
from typing_extensions import NotRequired, TypedDict

class Values(TypedDict, closed=True):
    note: NotRequired[str]

def consume(note: str): ...
def mutate(update: Callable[..., None]) -> None:
    update(note="again")

def forwarded(values: Values):
    values.pop("note", None)
    mutate(values.update)
    consume(note="replacement", **values)  # error: [parameter-already-assigned]

def conditional(values: Values):
    values.pop("note", None)
    (values.update if True else None)(note="again")
    consume(note="replacement", **values)  # error: [parameter-already-assigned]

def projected(values: Values):
    values.pop("note", None)
    [values.update][0](note="again")
    consume(note="replacement", **values)  # error: [parameter-already-assigned]

def chained(values: Values):
    values.pop("note", None)
    mutate(values.update.__call__)
    consume(note="replacement", **values)  # error: [parameter-already-assigned]

def chained_callee(values: Values):
    values.pop("note", None)
    values.update.__call__.__call__(note="again")
    consume(note="replacement", **values)  # error: [parameter-already-assigned]

def conditional_receiver(values: Values):
    values.pop("note", None)
    (values if True else values).update(note="again")
    consume(note="replacement", **values)  # error: [parameter-already-assigned]

def dictionary_key(values: Values):
    values.pop("note", None)
    next(iter({values.update: 0}))(note="again")
    consume(note="replacement", **values)  # error: [parameter-already-assigned]

def set_element(values: Values):
    values.pop("note", None)
    {values.update}.pop()(note="again")
    consume(note="replacement", **values)  # error: [parameter-already-assigned]
```

An assignment expression still identifies the directly passed object.

```py
def clear(values: dict[str, int]) -> None:
    values.clear()

def empty(): ...
def assigned_argument():
    clear(values := {"extra": 1})
    empty(**values)
```

## Opaque exposure

Passing a dictionary to an ordinary callable leaves key presence uncertain and discards observed
values. Values written after exposure remain useful until the next exposure; a clear or deletion
removes the previous restriction. Rebinding to a fresh dictionary starts a new object lifetime.

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
    values.update(value="bad")
    consume(**values)  # error: [invalid-argument-type]
    opaque(values)
    consume(**values)
    values = {"extra": 1}
    empty(**values)  # error: [unknown-argument]

def insertion():
    values = {"value": 1}
    del values["value"]
    opaque(values)
    consume(**values)
```

An opaque call can replace an earlier value. A lasting dictionary annotation still limits the
replacement type, while an unbounded dictionary loses that value restriction entirely.

```py
def mutate(values: dict[str, int | str]) -> None:
    values["value"] = "changed"

def consume_integer(*, value: int) -> None: ...
def bounded_exposure():
    values: dict[str, int | str] = {"value": 1}
    consume_integer(**values)
    mutate(values)
    consume_integer(**values)  # error: [invalid-argument-type]
    values["value"] = 2
    consume_integer(**values)

def unbounded_exposure():
    values = {"value": "old"}
    opaque(values)
    consume_integer(**values)
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

def mutate_saved(values: dict[str, int | str]) -> None:
    values["value"] = 42

def saved_opaque(initial: int | str) -> None:
    values: dict[str, int | str] = {"value": initial}
    ready = isinstance(values["value"], str)
    mutate_saved(values)
    if ready:
        reveal_type(values["value"])  # revealed: int | str
        strings(values["value"])  # error: [invalid-argument-type]

def saved_readonly(initial: int | str) -> None:
    values: dict[str, int | str] = {"value": initial}
    ready = isinstance(values["value"], str)
    values.get("value")
    if ready:
        reveal_type(values["value"])  # revealed: str
        strings(values["value"])  # no diagnostic

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

## Comprehensions without reachable mutations

A filtered-out dictionary operation does not invalidate an earlier deletion. Filters are evaluated
before their bodies, so a mutation in a filter still changes the captured dictionary.

```py
from typing import Callable
from typing_extensions import NotRequired, TypedDict

class Values(TypedDict, closed=True):
    value: int
    note: NotRequired[str]

def consume(value: int, note: str = ""): ...
def mutate(update: Callable[..., None]) -> None:
    update(note="again")

def filtered(values: Values):
    values.pop("note", None)
    removed = {key: values.pop(key) for key in ("absent",) if key in values}
    consume(note="replacement", **values)
    consume(note="replacement", **(values | removed))

def filter_mutates(values: Values):
    values.pop("note", None)
    [values.pop("absent", None) for _ in [0] if values.update(note="again") is not None]
    consume(note="replacement", **values)  # error: [parameter-already-assigned]

def unknown_method(values: Values):
    values.pop("note", None)
    [values.pop("absent", None) for _ in [0] if values.__setitem__("note", "again") is not None]
    consume(note="replacement", **values)  # error: [parameter-already-assigned]

def forwarded_method(values: Values):
    values.pop("note", None)
    [values.pop("absent", None) for _ in [0] if mutate(values.update) is not None]
    consume(note="replacement", **values)  # error: [parameter-already-assigned]

def projected_method(values: Values):
    values.pop("note", None)
    [values.pop("absent", None) for _ in [0] if [values.update][0](note="again") is not None]
    consume(note="replacement", **values)  # error: [parameter-already-assigned]
```

A live result can retain the dictionary or one of its bound methods even when a mutation elsewhere
in the comprehension is unreachable. Assignment expressions can also publish a captured value.

```py
def retained(values: Values):
    values.pop("note", None)
    saved = [values if True else values.pop("absent", None) for _ in [0]]
    saved[0]["note"] = "again"
    consume(note="replacement", **values)  # error: [parameter-already-assigned]

def retained_method(values: Values):
    values.pop("note", None)
    saved = [values.update if True else values.pop("absent", None) for _ in [0]]
    saved[0](note="again")
    consume(note="replacement", **values)  # error: [parameter-already-assigned]

def retained_container(values: Values):
    values.pop("note", None)
    saved = [{"nested": values} if True else values.pop("absent", None) for _ in [0]]
    saved[0]["nested"]["note"] = "again"
    consume(note="replacement", **values)  # error: [parameter-already-assigned]

def assigned_alias(values: Values):
    values.pop("note", None)
    alias: Values = {"value": 0}
    [0 for _ in [0] if (alias := values) is not None if False if values.pop("absent", None)]
    alias["note"] = "again"
    consume(note="replacement", **values)  # error: [parameter-already-assigned]

def deferred(values: Values):
    values.pop("note", None)
    pending = (values.update(note="again") for _ in [0])
    next(pending)
    consume(note="replacement", **values)  # error: [parameter-already-assigned]
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

## First values of immediate snapshots

An immediate list snapshot preserves the dictionary's observed first value. Overwriting a key
preserves its position. Reading another index uses the ordinary value type.

```py
def first_value(flag: bool):
    values = {"first": None, "other": 1}
    reveal_type(list(values.values())[0])  # revealed: None
    reveal_type(list(values.values())[1])  # revealed: int | None
    values["first"] = 2
    reveal_type(list(values.values())[0])  # revealed: Literal[2]

    if flag:
        values = {"first": None, "other": 1}
    else:
        values = {"other": 1, "first": None}
    reveal_type(list(values.values())[0])  # revealed: None | Literal[1]
```
