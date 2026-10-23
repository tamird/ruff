# Attribute assignment

This test suite demonstrates various kinds of diagnostics that can be emitted in a
`obj.attr = value` assignment.

## Instance attributes with class-level defaults

These can be set on instances and on class objects.

```py
class C:
    attr: int = 0

instance = C()
instance.attr = 1  # fine

C.attr = 1  # fine
```

But if the type is incorrect, we emit an error:

```py
instance.attr = "wrong"  # snapshot: invalid-assignment
```

```snapshot
error[invalid-assignment]: Object of type `Literal["wrong"]` is not assignable to attribute `attr` of type `int`
 --> src/mdtest_snippet.py:8:1
  |
8 | instance.attr = "wrong"  # snapshot: invalid-assignment
  | ^^^^^^^^^^^^^
```

And on the class object:

```py
C.attr = "wrong"  # snapshot: invalid-assignment
```

```snapshot
error[invalid-assignment]: Object of type `Literal["wrong"]` is not assignable to attribute `attr` of type `int`
 --> src/mdtest_snippet.py:9:1
  |
9 | C.attr = "wrong"  # snapshot: invalid-assignment
  | ^^^^^^
```

## Pure instance attributes

These can only be set on instances.

```py
class C:
    def __init__(self):
        self.attr: int = 0

instance = C()
instance.attr = 1  # fine
instance.attr = "wrong"  # error: [invalid-assignment]
```

When trying to set them on class objects, we generate a useful diagnostic that mentions that the
attribute is only available on instances:

```py
C.attr = 1  # snapshot: invalid-attribute-access
```

```snapshot
error[invalid-attribute-access]: Cannot assign to instance attribute `attr` from the class object `<class 'C'>`
 --> src/mdtest_snippet.py:8:1
  |
8 | C.attr = 1  # snapshot: invalid-attribute-access
  | ^^^^^^
```

## Invalid annotated assignment to attribute

Annotated assignments to attributes on method receivers should be validated against their
annotation.

```py
class C:
    def __init__(self):
        self.attr: str = None  # snapshot: invalid-assignment
        self.attr2: int = 1  # fine

    @classmethod
    def initialize(cls):
        cls.class_attr1: str = None  # snapshot: invalid-assignment
        cls.class_attr2: int = 1  # fine
```

```snapshot
error[invalid-assignment]: Object of type `None` is not assignable to `str`
 --> src/mdtest_snippet.py:3:26
  |
3 |         self.attr: str = None  # snapshot: invalid-assignment
  |                    ---   ^^^^ Incompatible value of type `None`
  |                    |
  |                    Declared type


error[invalid-assignment]: Object of type `None` is not assignable to `str`
 --> src/mdtest_snippet.py:8:32
  |
8 |         cls.class_attr1: str = None  # snapshot: invalid-assignment
  |                          ---   ^^^^ Incompatible value of type `None`
  |                          |
  |                          Declared type
```

Annotations on other attribute targets are ignored, and the assignment is checked against the
attribute already declared on the object's type.

```py
class C:
    declared: int

instance = C()

# error: [invalid-type-form] "Type annotations are not allowed on this attribute expression"
# error: [invalid-assignment]
instance.declared: str = "wrong"

# error: [invalid-type-form]
# error: [unresolved-attribute]
instance.missing: str = "wrong"

class Other:
    declared: int

class Static:
    @staticmethod
    def assign(other: Other):
        # error: [invalid-type-form]
        # error: [invalid-assignment]
        other.declared: str = "wrong"

class WithNew:
    declared: int

    def __new__(cls):
        # error: [invalid-type-form]
        # error: [invalid-assignment]
        cls.declared: str = "wrong"
        return super().__new__(cls)
```

## `ClassVar`s

These can only be set on class objects:

```py
from typing import ClassVar

class C:
    attr: ClassVar[int] = 0

C.attr = 1  # fine
C.attr = "wrong"  # error: [invalid-assignment]
```

When trying to set them on instances, we generate a useful diagnostic that mentions that the
attribute is only available on class objects.

```py
instance = C()
instance.attr = 1  # snapshot: invalid-attribute-access
```

```snapshot
error[invalid-attribute-access]: Cannot assign to ClassVar `attr` from an instance of type `C`
 --> src/mdtest_snippet.py:9:1
  |
9 | instance.attr = 1  # snapshot: invalid-attribute-access
  | ^^^^^^^^^^^^^
```

## Unknown attributes

When trying to set an attribute that is not defined, we also emit errors:

```py
class C: ...

C.non_existent = 1  # snapshot: unresolved-attribute
```

```snapshot
error[unresolved-attribute]: Unresolved attribute `non_existent` on type `<class 'C'>`.
 --> src/mdtest_snippet.py:3:1
  |
3 | C.non_existent = 1  # snapshot: unresolved-attribute
  | ^^^^^^^^^^^^^^
```

And on instances:

```py
instance = C()
instance.non_existent = 1  # snapshot: unresolved-attribute
```

```snapshot
error[unresolved-attribute]: Unresolved attribute `non_existent` on type `C`
 --> src/mdtest_snippet.py:5:1
  |
5 | instance.non_existent = 1  # snapshot: unresolved-attribute
  | ^^^^^^^^^^^^^^^^^^^^^
```

## Attributes declared without instance storage

An instance attribute annotation does not create storage. Assigning to an attribute declared on a
slotted class explains that the class has neither a matching slot nor an instance dictionary.

```py
class Slotted:
    value: int
    __slots__ = ()

Slotted().value = 1  # snapshot: missing-slot
```

```snapshot
error[missing-slot]: Cannot assign to attribute `value`: `Slotted` has no slot or instance dictionary
 --> src/mdtest_snippet.py:5:1
  |
5 | Slotted().value = 1  # snapshot: missing-slot
  | ^^^^^^^^^^^^^^^
info: Attribute `value` is declared but is not included in `__slots__`
```

A genuinely undeclared attribute keeps the ordinary unresolved-attribute diagnostic.

```py
Slotted().missing = 1  # error: [unresolved-attribute] "Unresolved attribute `missing` on type `Slotted`"
```

An inherited annotation also does not provide storage for a slotted subclass.

```py
class SlottedChild(Slotted):
    __slots__ = ()

# error: [missing-slot] "Cannot assign to attribute `value`: `SlottedChild` has no slot or instance dictionary"
SlottedChild().value = 1
```

## Possibly-missing attributes

When trying to set an attribute that is not defined in all branches, we emit errors:

```py
def _(flag: bool) -> None:
    class C:
        if flag:
            attr: int = 0

    C.attr = 1  # snapshot: possibly-missing-attribute
```

```snapshot
info[possibly-missing-attribute]: Attribute `attr` may be missing on class `C`
 --> src/mdtest_snippet.py:6:5
  |
6 |     C.attr = 1  # snapshot: possibly-missing-attribute
  |     ^^^^^^
```

And on instances:

```py
    instance = C()
    instance.attr = 1  # snapshot: possibly-missing-attribute
```

```snapshot
info[possibly-missing-attribute]: Attribute `attr` may be missing on object of type `C`
 --> src/mdtest_snippet.py:8:5
  |
8 |     instance.attr = 1  # snapshot: possibly-missing-attribute
  |     ^^^^^^^^^^^^^
```

## Possibly-missing attributes in intersections

An intersection has a member if either positive element requires it. This also applies when writing
through an instance or a class object:

```py
from typing import Final, Protocol
from ty_extensions import Intersection

def condition() -> bool:
    return bool(input())

class Partial:
    if condition():
        field = 1

class Required(Protocol):
    field: int

class RequiredNominal:
    field: int = 1

class RequiredInstance:
    field: int

class RequiredReadonly(Protocol):
    @property
    def field(self) -> int: ...

def write_required(value: Intersection[Partial, Required]) -> None:
    value.field = 1  # no diagnostic

def write_nominal(value: Intersection[Partial, RequiredNominal]) -> None:
    value.field = 1  # no diagnostic

def write_instance(value: Intersection[Partial, RequiredInstance]) -> None:
    value.field = 1  # no diagnostic

def write_required_union(value: Intersection[Partial, Required] | RequiredNominal) -> None:
    value.field = 1  # no diagnostic

def write_class(value: Intersection[type[Partial], RequiredReadonly]) -> None:
    value.field = 1  # no diagnostic

def write_nominal_class(value: Intersection[type[Partial], type[RequiredNominal]]) -> None:
    value.field = 1  # no diagnostic
```

The member's presence does not permit reassignment of a `Final` attribute:

```py
class PartialFinal:
    if condition():
        field: Final[int] = 1

def write_final(value: Intersection[PartialFinal, RequiredReadonly]) -> None:
    value.field = 1  # error: [invalid-assignment]
```

A union still has a possibly-missing member when one element permits its absence:

```py
def write_partial(value: Partial) -> None:
    value.field = 1  # error: [possibly-missing-attribute]

def write_union(value: Partial | Required) -> None:
    value.field = 1  # error: [possibly-missing-attribute]

def read_union(value: Partial | Required) -> int:
    return value.field  # error: [possibly-missing-attribute]
```

A dynamic base does not guarantee that a member exists, even when a conditional declaration supplies
part of its type. An unconditional declaration in the subclass does guarantee presence:

```py
from typing import Any, TypeVar

class DynamicBase(Any):
    tag = 1

class DynamicConditional(DynamicBase):
    if condition():
        field = 1

class DynamicRequired(DynamicBase):
    field: int = 1

def write_dynamic(value: Intersection[Partial, DynamicBase]) -> None:
    value.field = 1  # error: [possibly-missing-attribute]

def write_dynamic_conditional(value: Intersection[Partial, DynamicConditional]) -> None:
    value.field = 1  # error: [possibly-missing-attribute]

def write_dynamic_class(value: Intersection[type[Partial], type[DynamicBase]]) -> None:
    value.field = 1  # error: [possibly-missing-attribute]

def write_dynamic_required(value: Intersection[Partial, DynamicRequired]) -> None:
    value.field = 1  # no diagnostic

T = TypeVar("T", bound=Any)

def write_dynamic_typevar(value: Intersection[Partial, T]) -> None:
    value.field = 1  # error: [possibly-missing-attribute]

def write_dynamic_type(value: Intersection[type[Partial], type[Any]]) -> None:
    value.field = 1  # error: [possibly-missing-attribute]
```

## Possibly-missing attributes with dynamic lookup

Dynamic getters can supply a value for a read without declaring a member that receives writes. An
intersection with another type that also lacks the member preserves the write diagnostic:

```py
from ty_extensions import Intersection

def condition() -> bool:
    return bool(input())

class Partial:
    if condition():
        field = 1

    def __getattribute__(self, name: str) -> int:
        return 1

class Tag:
    tag = 1

def read(value: Intersection[Partial, Tag]) -> int:
    return value.field  # no diagnostic

def write(value: Intersection[Partial, Tag]) -> None:
    value.field = 1  # error: [possibly-missing-attribute]
```

The same applies to a fallback `__getattr__`:

```py
class PartialFallback:
    if condition():
        field = 1

    def __getattr__(self, name: str) -> int:
        return 1

def write_fallback(value: Intersection[PartialFallback, Tag]) -> None:
    value.field = 1  # error: [possibly-missing-attribute]
```

## Data descriptors

When assigning to a data descriptor attribute, we implicitly call the descriptor's `__set__` method.
This can lead to various kinds of diagnostics.

### Invalid argument type

```py
class Descriptor:
    def __set__(self, instance: object, value: int) -> None:
        pass

class C:
    attr: Descriptor = Descriptor()

instance = C()
instance.attr = 1  # fine

instance.attr = "wrong"  # snapshot: invalid-assignment

# Check that the concise diagnostic retains the useful expected and provided types.
# error: [invalid-assignment] "Expected `int`, found `Literal["also wrong"]`"
instance.attr = "also wrong"
```

```snapshot
error[invalid-assignment]: Invalid assignment to data descriptor attribute `attr` on type `C`
  --> src/mdtest_snippet.py:11:17
   |
11 | instance.attr = "wrong"  # snapshot: invalid-assignment
   |                 ^^^^^^^ Expected `int`, found `Literal["wrong"]`
info: Argument to bound method `Descriptor.__set__` is incorrect
info: This assignment implicitly calls `__set__` on a descriptor of type `Descriptor`
info: Method defined here
 --> src/mdtest_snippet.py:2:9
  |
2 |     def __set__(self, instance: object, value: int) -> None:
  |         ^^^^^^^                         ---------- Parameter declared here
```

### Invalid `__set__` method signature

```py
class WrongDescriptor:
    def __set__(self, instance: object, value: int, extra: int) -> None:
        pass

class C:
    attr: WrongDescriptor = WrongDescriptor()

instance = C()

instance.attr = 1  # snapshot: invalid-assignment
```

```snapshot
error[invalid-assignment]: Invalid assignment to data descriptor attribute `attr` on type `C`
  --> src/mdtest_snippet.py:10:1
   |
10 | instance.attr = 1  # snapshot: invalid-assignment
   | ^^^^^^^^^^^^^ No argument provided for required parameter `extra` of bound method `WrongDescriptor.__set__`
info: This assignment implicitly calls `__set__` on a descriptor of type `WrongDescriptor`
info: Parameter declared here
 --> src/mdtest_snippet.py:2:53
  |
2 |     def __set__(self, instance: object, value: int, extra: int) -> None:
  |                                                     ^^^^^^^^^^
```

### Invalid property setter argument type

```py
class Document: ...

class HasDocumentRef:
    @property
    def document(self) -> Document | None: ...
    @document.setter
    def document(self, document: Document) -> None: ...

class Model(HasDocumentRef):
    def detach(self) -> None:
        self.document = None  # snapshot: invalid-assignment

        # Check that the concise diagnostic identifies the actual setter argument mismatch.
        # error: [invalid-assignment] "Expected `Document`, found `None`"
        self.document = None
```

```snapshot
error[invalid-assignment]: Invalid assignment to data descriptor attribute `document` on type `Self@detach`
  --> src/mdtest_snippet.py:11:25
   |
11 |         self.document = None  # snapshot: invalid-assignment
   |                         ^^^^ Expected `Document`, found `None`
info: Argument to function `HasDocumentRef.document` is incorrect
info: This assignment implicitly calls `__set__` on a descriptor of type `property`
info: Function defined here
 --> src/mdtest_snippet.py:7:9
  |
7 |     def document(self, document: Document) -> None: ...
  |         ^^^^^^^^       ------------------ Parameter declared here
```

### Nested argument type

```py
class Descriptor:
    def __set__(self, instance, value: tuple[int, str]) -> None: ...

class C:
    x = Descriptor()

c = C()
c.x = (1, b"")  # snapshot: invalid-assignment
```

```snapshot
error[invalid-assignment]: Invalid assignment to data descriptor attribute `x` on type `C`
 --> src/mdtest_snippet.py:8:7
  |
8 | c.x = (1, b"")  # snapshot: invalid-assignment
  |       ^^^^^^^^ Expected `tuple[int, str]`, found `tuple[Literal[1], Literal[b""]]`
info: Argument to bound method `Descriptor.__set__` is incorrect
info: This assignment implicitly calls `__set__` on a descriptor of type `Descriptor`
info: the second tuple element is not compatible: `Literal[b""]` is not assignable to `str`
info: Method defined here
 --> src/mdtest_snippet.py:2:9
  |
2 |     def __set__(self, instance, value: tuple[int, str]) -> None: ...
  |         ^^^^^^^                 ---------------------- Parameter declared here
```

## Setting attributes on union types

```py
def _(flag: bool) -> None:
    if flag:
        class C1:
            attr: int = 0

    else:
        class C1:
            attr: str = ""

    C1.attr = 1  # snapshot: invalid-assignment

    class C2:
        if flag:
            attr: int = 0
        else:
            attr: str = ""

    # TODO: This should be an error
    C2.attr = 1
```

TODO: The error message here could be improved to explain *why* the assignment fails.

```snapshot
error[invalid-assignment]: Object of type `Literal[1]` is not assignable to attribute `attr` on type `<class 'mdtest_snippet.<locals of function '_'>.C1 @ src/mdtest_snippet.py:3:15'> | <class 'mdtest_snippet.<locals of function '_'>.C1 @ src/mdtest_snippet.py:7:15'>`
  --> src/mdtest_snippet.py:10:5
   |
10 |     C1.attr = 1  # snapshot: invalid-assignment
   |     ^^^^^^^
```
