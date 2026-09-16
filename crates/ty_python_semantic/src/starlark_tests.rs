//! Tests the semantic boundary supplied by a Starlark frontend. Files retain
//! their original text; module identity and resolved loads are explicit inputs.

use indoc::indoc;
use ruff_db::Db as _;
use ruff_db::diagnostic::{Diagnostic, Severity, UnifiedFile};
use ruff_db::files::system_path_to_file;
use ruff_db::parsed::parsed_module;
use ruff_db::system::DbWithWritableSystem;
use ruff_python_ast::name::Name;
use ruff_text_size::Ranged;
use salsa::Setter;
use ty_python_core::program::{Program, ProgramSettings};
use ty_python_core::starlark::{
    StarlarkAvailability, StarlarkEnvironment, StarlarkGlobalDeclaration, StarlarkGlobalKind,
    StarlarkLoad, StarlarkModule, StarlarkModuleRole, StarlarkParameter, StarlarkParameterMode,
    StarlarkType, load_call,
};
use ty_python_core::{ProgramFile, TestProgramDb};

use crate::db::tests::{TestDb, TestDbBuilder};
use crate::lint::{LintSource, RuleSelection};
use crate::{check_file_unwrap, semantic_index};

fn builder() -> TestDbBuilder<'static> {
    TestDbBuilder::new()
        .with_custom_typeshed("/typeshed".into())
        .with_file("/typeshed/stdlib/VERSIONS", "builtins: 3.0-\n")
        .with_file(
            "/typeshed/stdlib/builtins.pyi",
            indoc! {r#"
                class object: ...
                class type: ...
                class int: ...
                class bool: ...
                class str: ...
                class tuple: ...
            "#},
        )
}

fn module(db: &TestDb, path: &str, name: &str) -> anyhow::Result<StarlarkModule> {
    let file = system_path_to_file(db, path)?;
    Ok(StarlarkModule::new(
        db,
        file,
        Name::new(name),
        Box::default(),
        None,
        StarlarkModuleRole::Root,
    ))
}

fn load(db: &TestDb, importer: StarlarkModule, target: StarlarkModule) -> StarlarkLoad {
    let file = ProgramFile::new_starlark(db, importer, db.program());
    let parsed = parsed_module(db, file.python_file(db)).load(db);
    let call = parsed
        .suite()
        .iter()
        .filter_map(|statement| statement.as_expr_stmt())
        .find_map(|statement| load_call(&statement.value))
        .expect("fixture has a load");
    StarlarkLoad {
        range: call.range(),
        module: target,
    }
}

fn check(db: &TestDb, module: StarlarkModule) -> Vec<Diagnostic> {
    check_file_unwrap(db, ProgramFile::new_starlark(db, module, db.program()))
}

fn codes(diagnostics: &[Diagnostic]) -> Vec<String> {
    diagnostics
        .iter()
        .map(|diagnostic| diagnostic.id().to_string())
        .collect()
}

fn native(
    name: &str,
    ty: StarlarkType,
    availability: StarlarkAvailability,
) -> StarlarkGlobalDeclaration {
    StarlarkGlobalDeclaration {
        name: Name::new(name),
        kind: StarlarkGlobalKind::Native {
            parameters: Box::new([StarlarkParameter {
                name: Name::new("value"),
                mode: StarlarkParameterMode::PositionalOnly,
                ty,
                required: true,
            }]),
            return_type: StarlarkType::Str,
            availability,
        },
    }
}

fn host_module(
    db: &mut TestDb,
    path: &str,
    globals: Box<[StarlarkGlobalDeclaration]>,
) -> anyhow::Result<StarlarkModule> {
    let module = module(db, path, path)?;
    let environment = StarlarkEnvironment::new(db, globals);
    module.set_environment(db).to(Some(environment));
    Ok(module)
}

fn host_check(db: &TestDb, module: StarlarkModule) -> Vec<Diagnostic> {
    let python = db.program();
    let program = Program::new_starlark(
        db,
        python.python_platform(db),
        python.resolver_environment(db),
    );
    check_file_unwrap(db, ProgramFile::new_starlark(db, module, program))
}

#[test]
fn starlark_builtin_exports_hide_internal_declarations() -> anyhow::Result<()> {
    let source =
        "object\nslice\n__all__\ndef take(value: int) -> int:\n    return value\ntake(1)\n";
    let db = builder()
        .with_file(
            "/typeshed/stdlib/builtins.pyi",
            indoc! {r#"
                __all__ = ["int"]
                class object: ...
                class type: ...
                class int: ...
                class slice: ...
            "#},
        )
        .with_file("/src/root.star", source)
        .with_file("/src/root.py", source)
        .build()?;
    let root = module(&db, "/src/root.star", "root")?;
    assert_eq!(codes(&host_check(&db, root)), ["unresolved-reference"; 3]);
    let python = system_path_to_file(&db, "/src/root.py")?;
    assert!(check_file_unwrap(&db, ProgramFile::new(&db, python, db.program())).is_empty());
    Ok(())
}

#[test]
fn starlark_annotations_do_not_parse_python_forward_references() -> anyhow::Result<()> {
    let db = builder()
        .with_file(
            "/src/root.star",
            "def take(value: \"int\") -> \"str\":\n    return \"ok\"\n",
        )
        .build()?;
    let root = module(&db, "/src/root.star", "root")?;
    assert_eq!(codes(&host_check(&db, root)), ["invalid-type-form"; 2]);
    assert!(check(&db, root).is_empty());
    Ok(())
}

#[test]
fn starlark_type_annotations_allow_runtime_type_objects() -> anyhow::Result<()> {
    let mut db = builder()
        .with_file(
            "/src/root.star",
            indoc! {r#"
        Item = record(value=int)
        def factory() -> (type, struct):
            return (Item, struct())
        Result, namespace = factory()
        Result(value=1)
        Result.values()
        def accepts(value: Result):
            return value
        def own_type(value: type) -> type:
            return value
        own_type(Item)
        own_type(1)
        def wrong() -> type:
            return 1
    "#},
        )
        .build()?;
    let root = host_module(&mut db, "/src/root.star", record_globals())?;
    let diagnostics = host_check(&db, root);
    assert_eq!(
        codes(&diagnostics),
        ["invalid-argument-type", "invalid-return-type"],
        "{diagnostics:?}"
    );
    Ok(())
}

#[test]
fn starlark_isinstance_uses_type_expressions_and_positive_constraints() -> anyhow::Result<()> {
    let db = builder()
        .with_file(
            "/typeshed/stdlib/builtins.pyi",
            indoc! {r#"
            class object: ...
            class type:
                def __or__(self, other: object, /) -> object: ...
            class int: ...
            class bool: ...
            class str: ...
            class tuple[T]:
                def __getitem__(self, index: int, /) -> T: ...
            class list[T]:
                def __getitem__(self, index: int, /) -> T: ...
            def isinstance(value: object, types: object, /) -> bool: ...
        "#},
        )
        .with_file(
            "/src/root.star",
            indoc! {r#"
            def pair(value: int | tuple[int, str]) -> str:
                if isinstance(value, (int, str)):
                    return value[1]
                return "other"
            def sequence(value: int | list[str]) -> str:
                if isinstance(value, list[str]):
                    return value[0]
                return "other"
            def unknown_type(value: int | str, target: type) -> int:
                if isinstance(value, target):
                    return value
                return value
            isinstance(1, 42)
            isinstance(1, "int")
        "#},
        )
        .build()?;
    let root = module(&db, "/src/root.star", "root")?;
    let diagnostics = host_check(&db, root);
    assert_eq!(
        codes(&diagnostics),
        [
            "invalid-return-type",
            "invalid-return-type",
            "invalid-type-form",
            "invalid-type-form"
        ],
        "{diagnostics:?}"
    );
    Ok(())
}

#[test]
fn starlark_isinstance_excludes_only_known_classes() -> anyhow::Result<()> {
    let mut db = builder()
        .with_file(
            "/typeshed/stdlib/builtins.pyi",
            indoc! {r#"
            class object: ...
            class type:
                def __or__(self, other: object, /) -> object: ...
            class int: ...
            class bool: ...
            class str: ...
            def isinstance(value: object, types: object, /) -> bool: ...
        "#},
        )
        .with_file(
            "/src/root.star",
            indoc! {r#"
            First = record(value=int)
            Second = record(value=str)
            Third = record(value=bool)
            def last(value: First | Second | Third) -> Third:
                if isinstance(value, First):
                    return Third(value=True)
                elif isinstance(value, Second):
                    return Third(value=False)
                else:
                    return value
            def uncertain(value: First | Second | Third, condition: bool) -> Third:
                target = First if condition else Second
                if isinstance(value, target):
                    return Third(value=True)
                return value
        "#},
        )
        .build()?;
    let root = host_module(&mut db, "/src/root.star", record_globals())?;
    let diagnostics = host_check(&db, root);
    assert_eq!(
        codes(&diagnostics),
        ["invalid-return-type"],
        "{diagnostics:?}"
    );
    Ok(())
}

#[test]
fn starlark_variadic_annotations_describe_collected_arguments() -> anyhow::Result<()> {
    let db = builder()
        .with_file(
            "/typeshed/stdlib/builtins.pyi",
            indoc! {r#"
            class object: ...
            class type: ...
            class int: ...
            class bool: ...
            class str: ...
            class tuple[T]:
                def __getitem__(self, index: int, /) -> T: ...
            class dict[K, V]:
                def __getitem__(self, key: K, /) -> V: ...
            def host_values(*values: str) -> str: ...
        "#},
        )
        .with_file(
            "/src/root.star",
            indoc! {r#"
            def strings(*values: tuple[str, ...]) -> tuple[str, ...]:
                return values
            strings("one", "two")
            strings(1)
            def exact(*values: tuple[int, str]) -> str:
                return values[1]
            exact(1, "ok")
            exact(1)
            exact(1, "ok", 3)
            exact("wrong", 1)
            Keywords = dict[str, int]
            def keywords(**values: Keywords) -> dict[str, int]:
                return values
            keywords(one=1, two=2)
            keywords(one="wrong")
            def empty(*values: ()):
                return values
            empty()
            empty(1)
            host_values("one", "two")
            host_values(1)
        "#},
        )
        .build()?;
    let root = module(&db, "/src/root.star", "root")?;
    let diagnostics = host_check(&db, root);
    let mut actual = codes(&diagnostics);
    actual.sort();
    assert_eq!(
        actual,
        [
            "invalid-argument-type",
            "invalid-argument-type",
            "invalid-argument-type",
            "invalid-argument-type",
            "invalid-argument-type",
            "missing-argument",
            "too-many-positional-arguments",
            "too-many-positional-arguments"
        ],
        "{diagnostics:?}"
    );
    Ok(())
}

#[test]
fn starlark_variadic_annotations_report_unsupported_aggregate_forms() -> anyhow::Result<()> {
    let db = builder()
        .with_file(
            "/typeshed/stdlib/builtins.pyi",
            indoc! {r#"
            class object: ...
            class type:
                def __or__(self, other: object, /) -> object: ...
            class int: ...
            class bool: ...
            class str: ...
            class tuple[T]: ...
            class dict[K, V]: ...
        "#},
        )
        .with_file(
            "/src/root.star",
            indoc! {r#"
            def scalar_args(*values: str):
                return values
            def scalar_kwargs(**values: int):
                return values
            def correlated(**values: dict[str, int] | dict[str, str]):
                return values
            def broad(*values: object, **keywords: object):
                return values
            broad(1, "two", value=3)
        "#},
        )
        .build()?;
    let root = module(&db, "/src/root.star", "root")?;
    let diagnostics = host_check(&db, root);
    assert_eq!(
        codes(&diagnostics),
        ["invalid-type-form"; 3],
        "{diagnostics:?}"
    );
    Ok(())
}

#[test]
fn starlark_boolean_operations_do_not_use_integer_fast_paths() -> anyhow::Result<()> {
    let registry = crate::default_lint_registry();
    let mut rules = RuleSelection::from_registry(registry);
    rules.enable(
        registry.get("division-by-zero")?,
        Severity::Error,
        LintSource::File,
    );
    let db = builder()
        .with_rule_selection(rules)
        .with_file(
            "/src/root.star",
            indoc! {r#"
                True + 1
                1 + True
                True | False
                True & False
                True ^ False
                +True
                -True
                ~True
                True / 0
                True < 1
                1 >= False
                False < True
                1 + 2
            "#},
        )
        .build()?;
    let root = module(&db, "/src/root.star", "root")?;
    let diagnostics = host_check(&db, root);
    assert_eq!(
        codes(&diagnostics),
        vec!["unsupported-operator"; 11],
        "{diagnostics:?}"
    );
    let python = check(&db, root);
    assert_eq!(codes(&python), ["division-by-zero"], "{python:?}");
    Ok(())
}

#[test]
fn starlark_boolean_equality_keeps_integer_exports_distinct() -> anyhow::Result<()> {
    let mut db = builder()
        .with_file(
            "/src/root.star",
            "load(\":dep.star\", \"value\")\ndef take(value: int):\n    pass\ntake(value)\n",
        )
        .with_file(
            "/src/dep.star",
            "value = 1\nif True == 1:\n    value = \"wrong\"\nif False != 0:\n    value = 2\n",
        )
        .build()?;
    let root = module(&db, "/src/root.star", "root")?;
    let dep = module(&db, "/src/dep.star", "dep")?;
    let edge = load(&db, root, dep);
    root.set_loads(&mut db).to(Box::new([edge]));
    assert!(host_check(&db, root).is_empty());
    assert_eq!(codes(&check(&db, root)), ["invalid-argument-type"]);
    Ok(())
}

#[test]
fn starlark_strings_have_no_sequence_iteration_fallback() -> anyhow::Result<()> {
    let db = builder()
        .with_file(
            "/typeshed/stdlib/builtins.pyi",
            indoc! {r#"
                class object: ...
                class type: ...
                class int: ...
                class bool: ...
                class tuple: ...
                class Iterator:
                    def __iter__(self) -> Iterator: ...
                    def __next__(self) -> str: ...
                class str:
                    def __getitem__(self, index: int) -> str: ...
                    def elems(self) -> Iterator: ...
            "#},
        )
        .with_file(
            "/src/root.star",
            indoc! {r#"
                for character in "abc":
                    pass
                def iterate(value: str):
                    for character in value:
                        pass
                    for character in value.elems():
                        pass
                    return value[0]
            "#},
        )
        .build()?;
    let root = module(&db, "/src/root.star", "root")?;
    let diagnostics = host_check(&db, root);
    assert_eq!(
        codes(&diagnostics),
        ["not-iterable", "not-iterable"],
        "{diagnostics:?}"
    );
    assert!(check(&db, root).is_empty());
    Ok(())
}

#[test]
fn starlark_type_calls_use_the_declared_string_result() -> anyhow::Result<()> {
    let db = builder()
        .with_file(
            "/typeshed/stdlib/builtins.pyi",
            indoc! {r#"
                class object: ...
                class int: ...
                class bool: ...
                class str: ...
                class tuple: ...
                class type:
                    def __new__(cls, value: object, /) -> str: ...
            "#},
        )
        .with_file(
            "/src/root.star",
            indoc! {r#"
                name = type(1)
                def take(value: str):
                    pass
                take(name)
                def name_of(value: object) -> str:
                    return type(value)
                type()
                alias = type
                take(alias(1))
            "#},
        )
        .build()?;
    let root = module(&db, "/src/root.star", "root")?;
    let diagnostics = host_check(&db, root);
    assert_eq!(codes(&diagnostics), ["missing-argument"], "{diagnostics:?}");
    Ok(())
}

#[test]
fn starlark_tuple_annotations_describe_fixed_tuples() -> anyhow::Result<()> {
    let db = builder()
        .with_file(
            "/src/root.star",
            indoc! {r#"
                def pair() -> (int, str):
                    return (1, "ok")
                def wrong() -> (int, str):
                    return ("wrong", 1)
                def empty() -> ():
                    return ()
            "#},
        )
        .build()?;
    let root = module(&db, "/src/root.star", "root")?;
    let diagnostics = host_check(&db, root);
    assert_eq!(
        codes(&diagnostics),
        ["invalid-return-type"],
        "{diagnostics:?}"
    );
    assert_eq!(codes(&check(&db, root)), vec!["invalid-type-form"; 3]);
    Ok(())
}

#[test]
fn starlark_float_annotations_and_promotion_preserve_exact_types() -> anyhow::Result<()> {
    let mut db = builder()
        .with_file(
            "/typeshed/stdlib/builtins.pyi",
            indoc! {r#"
                class object: ...
                class type: ...
                class int: ...
                class bool: ...
                class str: ...
                class tuple: ...
                class float:
                    def __new__(cls, value: int | float, /) -> float: ...
                class list[T]:
                    def append(self, value: T) -> None: ...
            "#},
        )
        .with_file(
            "/src/root.star",
            indoc! {r#"
                def take(value: float):
                    pass
                take(1)
                take(float(1))
                def wrong() -> float:
                    return 1
                values = [1.5]
                values.append(1)
                Item = record(value=float)
                Item(value=1)
                Item(value=float(1))
            "#},
        )
        .build()?;
    let root = host_module(
        &mut db,
        "/src/root.star",
        Box::new([StarlarkGlobalDeclaration {
            name: Name::new("record"),
            kind: StarlarkGlobalKind::Record,
        }]),
    )?;
    let diagnostics = host_check(&db, root);
    assert_eq!(
        codes(&diagnostics),
        [
            "invalid-argument-type",
            "invalid-return-type",
            "invalid-argument-type",
            "invalid-argument-type"
        ],
        "{diagnostics:?}"
    );
    assert!(check(&db, root).is_empty());
    Ok(())
}

#[test]
fn starlark_iteration_recovers_the_known_union_element_type() -> anyhow::Result<()> {
    let db = builder()
        .with_file(
            "/typeshed/stdlib/builtins.pyi",
            indoc! {r#"
                class object: ...
                class type:
                    def __or__(self, other: object, /) -> object: ...
                class int: ...
                class bool: ...
                class tuple: ...
                class str:
                    def __getitem__(self, index: int) -> str: ...
                class Iterator:
                    def __iter__(self) -> Iterator: ...
                    def __next__(self) -> str: ...
            "#},
        )
        .with_file(
            "/src/root.star",
            indoc! {r#"
                def take(value: int):
                    pass
                def mixed(value: str | Iterator):
                    for element in value:
                        take(element)
            "#},
        )
        .build()?;
    let root = module(&db, "/src/root.star", "root")?;
    let diagnostics = host_check(&db, root);
    assert_eq!(
        codes(&diagnostics),
        ["not-iterable", "invalid-argument-type"],
        "{diagnostics:?}"
    );
    assert_eq!(codes(&check(&db, root)), ["invalid-argument-type"]);
    Ok(())
}

fn record_globals() -> Box<[StarlarkGlobalDeclaration]> {
    [
        ("record", StarlarkGlobalKind::Record),
        (
            "record_with_validator",
            StarlarkGlobalKind::RecordWithValidator,
        ),
        ("field", StarlarkGlobalKind::Field),
        ("struct", StarlarkGlobalKind::Struct),
    ]
    .map(|(name, kind)| StarlarkGlobalDeclaration {
        name: Name::new(name),
        kind,
    })
    .into()
}

#[test]
fn records_share_constructor_binding_and_field_types() -> anyhow::Result<()> {
    let mut db = builder()
        .with_file(
            "/src/root.star",
            indoc! {r#"
        Item = record(value=int, title=field(str, default="untitled"))
        good = Item(value=1)
        Item(value="bad")
        Item(value=True)
        Item()
        Item(1)
        Item(value=1, extra=2)
        def field_value() -> int:
            return good.value
        def wrong_field_value() -> int:
            return good.title
        def wrong_instance() -> Item:
            return 1
    "#},
        )
        .build()?;
    let module = host_module(&mut db, "/src/root.star", record_globals())?;
    let diagnostics = host_check(&db, module);
    let mut actual = codes(&diagnostics);
    actual.sort();
    assert_eq!(
        actual,
        [
            "invalid-argument-type",
            "invalid-argument-type",
            "invalid-return-type",
            "invalid-return-type",
            "missing-argument",
            "missing-argument",
            "too-many-positional-arguments",
            "unknown-argument"
        ],
        "{diagnostics:?}"
    );
    Ok(())
}

#[test]
fn record_defaults_and_nominal_identity_are_checked() -> anyhow::Result<()> {
    let mut db = builder()
        .with_file(
            "/src/root.star",
            indoc! {r#"
        Bad = record(value=field(int, "bad"))
        First = record(value=int)
        Second = record(value=int)
        def accept(value: First) -> First:
            return value
        accept(First(value=1))
        accept(Second(value=1))
        def wrong() -> Second:
            return First(value=1)
    "#},
        )
        .build()?;
    let module = host_module(&mut db, "/src/root.star", record_globals())?;
    let diagnostics = host_check(&db, module);
    let mut actual = codes(&diagnostics);
    actual.sort();
    assert_eq!(
        actual,
        [
            "invalid-argument-type",
            "invalid-argument-type",
            "invalid-return-type"
        ],
        "{diagnostics:?}"
    );
    Ok(())
}

#[test]
fn struct_fields_retain_functions_constructors_and_special_forms() -> anyhow::Result<()> {
    let mut db = builder()
        .with_file(
            "/src/root.star",
            indoc! {r#"
        def identity(value: int) -> int:
            return value
        Item = record(value=int)
        namespace = struct(call=identity, item=Item, forms=struct(record=record, field=field))
        namespace.call(1)
        namespace.call("bad")
        namespace.item(value="bad")
        Other = namespace.forms.record(value=namespace.forms.field(str, "ok"))
        Other()
        Other(value=1)
        def field_value() -> int:
            return namespace.item(value=1).value
    "#},
        )
        .build()?;
    let module = host_module(&mut db, "/src/root.star", record_globals())?;
    let diagnostics = host_check(&db, module);
    assert_eq!(
        codes(&diagnostics),
        [
            "invalid-argument-type",
            "invalid-argument-type",
            "invalid-argument-type"
        ],
        "{diagnostics:?}"
    );
    Ok(())
}

#[test]
fn record_special_forms_follow_lexical_resolution() -> anyhow::Result<()> {
    let mut db = builder()
        .with_file(
            "/src/root.star",
            indoc! {r#"
        make = record
        descriptor = field
        Item = make(value=descriptor(int, 1))
        Item(value="bad")
        def shadow(record: int) -> int:
            return record
        def local_shadow():
            record = struct
            return record(value=1)
        def validate(value):
            return value
        Validated = record_with_validator(validate, value=int)
        Validated(value="bad")
        record_with_validator(1, value=int)
    "#},
        )
        .build()?;
    let module = host_module(&mut db, "/src/root.star", record_globals())?;
    let diagnostics = host_check(&db, module);
    assert_eq!(
        codes(&diagnostics),
        [
            "invalid-argument-type",
            "invalid-argument-type",
            "invalid-argument-type"
        ],
        "{diagnostics:?}"
    );
    Ok(())
}

#[test]
fn record_union_fields_and_unknown_shapes_remain_partial() -> anyhow::Result<()> {
    let mut db = builder()
        .with_file(
            "/src/root.star",
            indoc! {r#"
        Item = record(value=int | str, metadata=struct)
        Item(value=1, metadata=struct())
        Item(value="ok", metadata=1)
        Item(value=True, metadata=struct())
        def dynamic(fields) -> type:
            return record(**fields)
        def accepts_struct(value: struct):
            return value
    "#},
        )
        .build()?;
    let module = host_module(&mut db, "/src/root.star", record_globals())?;
    let diagnostics = host_check(&db, module);
    assert_eq!(
        codes(&diagnostics),
        ["invalid-argument-type"],
        "{diagnostics:?}"
    );
    Ok(())
}

#[test]
fn record_tuple_fields_describe_fixed_element_types() -> anyhow::Result<()> {
    let mut db = builder()
        .with_file(
            "/src/root.star",
            indoc! {r#"
        Item = record(value=(int, str))
        Item(value=(1, "ok"))
        Item(value=1)
        Item(value=("bad", 1))
        Empty = record(value=())
        Empty(value=())
        Empty(value=(1,))
    "#},
        )
        .build()?;
    let module = host_module(&mut db, "/src/root.star", record_globals())?;
    let diagnostics = host_check(&db, module);
    assert_eq!(
        codes(&diagnostics),
        [
            "invalid-argument-type",
            "invalid-argument-type",
            "invalid-argument-type"
        ],
        "{diagnostics:?}"
    );
    Ok(())
}

#[test]
fn loaded_records_keep_logical_identity_and_field_provenance() -> anyhow::Result<()> {
    let source = "Item = record(value=int)\n";
    let mut db = builder()
        .with_file("/src/dep.star", source)
        .with_file(
            "/src/root.star",
            indoc! {r#"
            load(":first", First="Item")
            load(":second", Second="Item")
            def accepts(value: First):
                return value
            accepts(First(value=1))
            accepts(Second(value=1))
            First(value="wrong")
        "#},
        )
        .build()?;
    let root = host_module(&mut db, "/src/root.star", record_globals())?;
    let first = module(&db, "/src/dep.star", "first")?;
    let second = module(&db, "/src/dep.star", "second")?;
    let environment = root.environment(&db);
    first.set_environment(&mut db).to(environment);
    second.set_environment(&mut db).to(environment);
    let root_file = ProgramFile::new_starlark(&db, root, db.program());
    let parsed = parsed_module(&db, root_file.python_file(&db)).load(&db);
    let edges = parsed
        .suite()
        .iter()
        .filter_map(|statement| statement.as_expr_stmt())
        .filter_map(|statement| load_call(&statement.value))
        .zip([first, second])
        .map(|(call, module)| StarlarkLoad {
            range: call.range(),
            module,
        })
        .collect::<Box<[_]>>();
    root.set_loads(&mut db).to(edges);
    let diagnostics = host_check(&db, root);
    assert_eq!(
        codes(&diagnostics),
        ["invalid-argument-type", "invalid-argument-type"],
        "{diagnostics:?}"
    );
    assert!(
        diagnostics[0]
            .annotations()
            .iter()
            .filter_map(|annotation| annotation.get_message())
            .any(|message| message.contains("first.Item") && message.contains("second.Item")),
        "{:?}",
        diagnostics[0]
    );
    let field_origin = diagnostics[1]
        .annotations()
        .iter()
        .chain(
            diagnostics[1]
                .sub_diagnostics()
                .iter()
                .flat_map(ruff_db::diagnostic::SubDiagnostic::annotations),
        )
        .any(|annotation| {
            let span = annotation.get_span();
            span.file() == &UnifiedFile::Ty(first.file(&db))
                && span.range().is_some_and(|range| {
                    &source[range.start().to_usize()..range.end().to_usize()] == "int"
                })
        });
    assert!(field_origin, "{:?}", diagnostics[1]);

    db.write_file("/src/dep.star", "Item = record(value=str)\n")?;
    let diagnostics = host_check(&db, root);
    assert_eq!(
        codes(&diagnostics),
        [
            "invalid-argument-type",
            "invalid-argument-type",
            "invalid-argument-type"
        ],
        "{diagnostics:?}"
    );
    Ok(())
}

#[test]
fn record_constructors_convert_to_regular_callables() -> anyhow::Result<()> {
    let mut db = TestDbBuilder::new()
        .with_file(
            "/src/root.star",
            indoc! {r#"
        from typing import Callable
        Item = record(value=int)
        def accepts(maker: Callable[..., Item]):
            return maker(value=1)
        accepts(Item)
        def wrong() -> int:
            return 1
        accepts(wrong)
    "#},
        )
        .build()?;
    let module = host_module(&mut db, "/src/root.star", record_globals())?;
    let diagnostics = host_check(&db, module);
    assert_eq!(
        codes(&diagnostics),
        ["invalid-argument-type"],
        "{diagnostics:?}"
    );
    Ok(())
}

#[test]
fn native_aliases_use_regular_argument_and_return_checks() -> anyhow::Result<()> {
    let mut db = builder()
        .with_file(
            "/src/root.star",
            indoc! {r#"
        alias = host_hash
        alias(7)
        host_hash(value="wrong mode")
        host_hash()
        host_hash("ok")
        def bad_return() -> int:
            return alias("ok")
        def shadow(host_hash: int) -> int:
            return host_hash
    "#},
        )
        .build()?;
    let module = host_module(
        &mut db,
        "/src/root.star",
        Box::new([native(
            "host_hash",
            StarlarkType::Str,
            StarlarkAvailability::AnyModule,
        )]),
    )?;
    let diagnostics = host_check(&db, module);
    for diagnostic in diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.id().to_string() != "invalid-return-type")
    {
        assert!(
            diagnostic.sub_diagnostics().iter().any(|sub| sub
                .headline_message()
                .contains("Host signature: host_hash(value: str, /) -> str")),
            "{diagnostic:?}"
        );
    }
    let mut actual = codes(&diagnostics);
    actual.sort();
    assert_eq!(
        actual,
        [
            "invalid-argument-type",
            "invalid-return-type",
            "missing-argument",
            "positional-only-parameter-as-kwarg"
        ],
        "{diagnostics:?}"
    );
    Ok(())
}

#[test]
fn native_keyword_defaults_and_callbacks_use_shared_binding() -> anyhow::Result<()> {
    let mut db = builder()
        .with_file(
            "/src/root.star",
            indoc! {r#"
        def callback(value):
            return value
        encode(callback)
        encode(callback, sort_keys=True)
        encode(callback, sort_keys=1)
        encode(1)
        encode(callback, False)
    "#},
        )
        .build()?;
    let module = host_module(
        &mut db,
        "/src/root.star",
        Box::new([StarlarkGlobalDeclaration {
            name: Name::new("encode"),
            kind: StarlarkGlobalKind::Native {
                parameters: Box::new([
                    StarlarkParameter {
                        name: Name::new("value"),
                        mode: StarlarkParameterMode::PositionalOrKeyword,
                        ty: StarlarkType::Callable,
                        required: true,
                    },
                    StarlarkParameter {
                        name: Name::new("sort_keys"),
                        mode: StarlarkParameterMode::KeywordOnly,
                        ty: StarlarkType::Bool,
                        required: false,
                    },
                ]),
                return_type: StarlarkType::Str,
                availability: StarlarkAvailability::AnyModule,
            },
        }]),
    )?;
    let diagnostics = host_check(&db, module);
    let mut actual = codes(&diagnostics);
    actual.sort();
    assert_eq!(
        actual,
        [
            "invalid-argument-type",
            "invalid-argument-type",
            "too-many-positional-arguments"
        ],
        "{diagnostics:?}"
    );
    Ok(())
}

#[test]
fn native_values_are_not_assignable_to_scalar_parameters() -> anyhow::Result<()> {
    let mut db = builder()
        .with_file("/typeshed/stdlib/VERSIONS", "builtins: 3.0-\ntypes: 3.0-\n")
        .with_file(
            "/typeshed/stdlib/types.pyi",
            "class FunctionType: ...\nclass ModuleType: ...\nclass NoneType: ...\n",
        )
        .with_file(
            "/src/root.star",
            "def take(value: int):\n    pass\ntake(host_hash)\n",
        )
        .build()?;
    let module = host_module(
        &mut db,
        "/src/root.star",
        Box::new([native(
            "host_hash",
            StarlarkType::Str,
            StarlarkAvailability::AnyModule,
        )]),
    )?;
    assert_eq!(codes(&host_check(&db, module)), ["invalid-argument-type"]);
    Ok(())
}

#[test]
fn host_availability_follows_resolved_identity_and_module_role() -> anyhow::Result<()> {
    let mut db = builder()
        .with_file(
            "/src/root.star",
            indoc! {r#"
        alias = catalog
        if False:
            alias("ok")
        def delayed(value=alias("ok")):
            alias(7)
        def shadow(catalog):
            catalog("ok")
    "#},
        )
        .build()?;
    let module = host_module(
        &mut db,
        "/src/root.star",
        Box::new([native(
            "catalog",
            StarlarkType::Str,
            StarlarkAvailability::LoadedModuleInitialization,
        )]),
    )?;
    let diagnostics = host_check(&db, module);
    let mut actual = codes(&diagnostics);
    actual.sort();
    assert_eq!(
        actual,
        [
            "invalid-argument-type",
            "unavailable-host-function",
            "unavailable-host-function",
            "unavailable-host-function"
        ],
        "{diagnostics:?}"
    );
    module.set_role(&mut db).to(StarlarkModuleRole::Loaded);
    assert_eq!(codes(&host_check(&db, module)), ["invalid-argument-type"]);
    Ok(())
}

#[test]
fn callable_unions_retain_host_availability() -> anyhow::Result<()> {
    let mut db = builder()
        .with_file(
            "/src/root.star",
            indoc! {r#"
        def invoke(flag: bool):
            selected = catalog if flag else native
            selected("ok")
    "#},
        )
        .build()?;
    let module = host_module(
        &mut db,
        "/src/root.star",
        Box::new([
            native(
                "catalog",
                StarlarkType::Str,
                StarlarkAvailability::LoadedModuleInitialization,
            ),
            native("native", StarlarkType::Str, StarlarkAvailability::AnyModule),
        ]),
    )?;
    assert_eq!(
        codes(&host_check(&db, module)),
        ["unavailable-host-function"]
    );
    Ok(())
}

#[test]
fn native_signatures_track_environment_and_program_changes() -> anyhow::Result<()> {
    let mut db = builder()
        .with_file("/src/root.star", "alias = native\nalias(True)\n")
        .build()?;
    let module = host_module(
        &mut db,
        "/src/root.star",
        Box::new([native(
            "native",
            StarlarkType::Int,
            StarlarkAvailability::AnyModule,
        )]),
    )?;
    assert_eq!(codes(&host_check(&db, module)), ["invalid-argument-type"]);
    let settings = ProgramSettings::empty(db.vendored());
    let standard = Program::from_settings(&db, &settings);
    assert!(check_file_unwrap(&db, ProgramFile::new_starlark(&db, module, standard)).is_empty());
    assert_eq!(codes(&host_check(&db, module)), ["invalid-argument-type"]);
    let Some(environment) = module.environment(&db) else {
        anyhow::bail!("fixture has host declarations")
    };
    environment.set_globals(&mut db).to(Box::new([native(
        "native",
        StarlarkType::Bool,
        StarlarkAvailability::AnyModule,
    )]));
    assert!(host_check(&db, module).is_empty());
    Ok(())
}

#[test]
fn loaded_functions_check_arguments_and_returns_at_original_spans() -> anyhow::Result<()> {
    let root_source = indoc! {r#"
        load(":dep.star", accept="take")
        accept("wrong")
        accept(True)
        accept(1)
    "#};
    let dep_source = indoc! {r#"
        def take(value: int) -> int:
            return "wrong"
    "#};
    let mut db = builder()
        .with_file("/src/root.star", root_source)
        .with_file("/src/dep.star", dep_source)
        .build()?;
    let root = module(&db, "/src/root.star", "//:root.star")?;
    let dep = module(&db, "/src/dep.star", "//:dep.star")?;
    let edge = load(&db, root, dep);
    root.set_loads(&mut db).to(Box::new([edge]));

    let file = ProgramFile::new_starlark(&db, root, db.program());
    let parsed = parsed_module(&db, file.python_file(&db)).load(&db);
    let call = load_call(&parsed.suite()[0].as_expr_stmt().unwrap().value).unwrap();
    let binding = ty_python_core::starlark::load_bindings(call)
        .next()
        .unwrap();
    let definition = semantic_index(&db, file).expect_single_definition(binding.name);
    let focus = definition.kind(&db).target_range(&parsed);
    assert_eq!(
        &root_source[focus.start().to_usize()..focus.end().to_usize()],
        "accept"
    );

    let diagnostics = check(&db, root);
    assert_eq!(
        codes(&diagnostics),
        ["invalid-argument-type", "invalid-argument-type"]
    );
    let arguments: Vec<_> = diagnostics
        .iter()
        .map(|diagnostic| {
            let span = diagnostic.primary_span().unwrap();
            assert_eq!(span.file(), &UnifiedFile::Ty(root.file(&db)));
            let range = span.range().unwrap();
            &root_source[range.start().to_usize()..range.end().to_usize()]
        })
        .collect();
    assert_eq!(arguments, ["\"wrong\"", "True"]);

    let diagnostics = check(&db, dep);
    assert_eq!(codes(&diagnostics), ["invalid-return-type"]);
    let span = diagnostics[0].primary_span().unwrap();
    assert_eq!(span.file(), &UnifiedFile::Ty(dep.file(&db)));
    let range = span.range().unwrap();
    assert_eq!(
        &dep_source[range.start().to_usize()..range.end().to_usize()],
        "\"wrong\""
    );
    Ok(())
}

#[test]
fn load_edges_and_loaded_source_edits_invalidate_importers() -> anyhow::Result<()> {
    let mut db = builder()
        .with_file(
            "/src/root.star",
            indoc! {r#"
                load(":dep.star", "take")
                take(1)
            "#},
        )
        .with_file(
            "/src/int.star",
            indoc! {r#"
                def take(value: int) -> int:
                    return value
            "#},
        )
        .with_file(
            "/src/str.star",
            indoc! {r#"
                def take(value: str) -> str:
                    return value
            "#},
        )
        .build()?;
    let root = module(&db, "/src/root.star", "root")?;
    let int = module(&db, "/src/int.star", "int")?;
    let str = module(&db, "/src/str.star", "str")?;
    let edge = load(&db, root, int);
    root.set_loads(&mut db).to(Box::new([edge]));
    assert!(check(&db, root).is_empty());
    let edge = load(&db, root, str);
    root.set_loads(&mut db).to(Box::new([edge]));
    assert_eq!(codes(&check(&db, root)), ["invalid-argument-type"]);
    db.write_file(
        "/src/str.star",
        indoc! {r#"
            def take(value: int) -> int:
                return value
        "#},
    )?;
    assert!(check(&db, root).is_empty());
    Ok(())
}

#[test]
fn loads_use_final_exports_and_allow_local_shadowing() -> anyhow::Result<()> {
    let mut db = builder()
        .with_file(
            "/src/root.star",
            indoc! {r#"
                load(":dep.star", "value", "take")
                take(value)
                def local(take: int) -> int:
                    return take
                take = 1
                result = take
            "#},
        )
        .with_file(
            "/src/dep.star",
            indoc! {r#"
                value = 1
                value = "final"
                def take(value: str) -> str:
                    return value
            "#},
        )
        .build()?;
    let root = module(&db, "/src/root.star", "root")?;
    let dep = module(&db, "/src/dep.star", "dep")?;
    let edge = load(&db, root, dep);
    root.set_loads(&mut db).to(Box::new([edge]));
    assert!(check(&db, root).is_empty(), "{:?}", check(&db, root));
    Ok(())
}

#[test]
fn module_identity_is_distinct_from_physical_source() -> anyhow::Result<()> {
    let db = builder()
        .with_file(
            "/src/dep.star",
            indoc! {r#"
                def take(value: int) -> int:
                    return value
            "#},
        )
        .build()?;
    let first = module(&db, "/src/dep.star", "first")?;
    let second = module(&db, "/src/dep.star", "second")?;
    let first_file = ProgramFile::new_starlark(&db, first, db.program());
    let second_file = ProgramFile::new_starlark(&db, second, db.program());
    assert_eq!(first_file.python_file(&db), second_file.python_file(&db));
    assert_ne!(first_file, second_file);
    let parsed = parsed_module(&db, first_file.python_file(&db)).load(&db);
    let function = parsed.suite()[0].as_function_def_stmt().unwrap();
    let first_definition = semantic_index(&db, first_file).expect_single_definition(function);
    let second_definition = semantic_index(&db, second_file).expect_single_definition(function);
    assert_ne!(first_definition, second_definition);
    assert_ne!(
        crate::types::binding_type(&db, first_definition),
        crate::types::binding_type(&db, second_definition)
    );
    assert_eq!(
        first_file,
        ProgramFile::new_starlark(&db, first, db.program())
    );
    Ok(())
}

#[test]
fn starlark_has_no_python_implicit_module_globals() -> anyhow::Result<()> {
    let db = builder()
        .with_file("/src/root.star", "value = __file__\n")
        .build()?;
    let root = module(&db, "/src/root.star", "root")?;
    assert_eq!(codes(&check(&db, root)), ["unresolved-reference"]);
    let python = ProgramFile::new(&db, root.file(&db), db.program());
    assert!(check_file_unwrap(&db, python).is_empty());
    Ok(())
}

#[test]
fn loaded_names_require_an_explicit_reexport() -> anyhow::Result<()> {
    let mut db = builder()
        .with_file(
            "/src/root.star",
            indoc! {r#"
                load(":relay.star", "take", "exported")
                exported(1)
            "#},
        )
        .with_file(
            "/src/relay.star",
            indoc! {r#"
                load(":dep.star", "take")
                exported = take
                __all__ = ["take"]
            "#},
        )
        .with_file(
            "/src/dep.star",
            indoc! {r#"
                def take(value: int) -> int:
                    return value
            "#},
        )
        .build()?;
    let root = module(&db, "/src/root.star", "root")?;
    let relay = module(&db, "/src/relay.star", "relay")?;
    let dep = module(&db, "/src/dep.star", "dep")?;
    let edge = load(&db, root, relay);
    root.set_loads(&mut db).to(Box::new([edge]));
    let edge = load(&db, relay, dep);
    relay.set_loads(&mut db).to(Box::new([edge]));
    assert_eq!(codes(&check(&db, root)), ["unresolved-import"]);
    Ok(())
}

#[test]
fn one_source_can_use_distinct_builtin_profiles() -> anyhow::Result<()> {
    let db = builder()
        .with_file(
            "/src/root.star",
            indoc! {r#"
                def take(value: int) -> int:
                    return value
                take(True)
            "#},
        )
        .build()?;
    let root = module(&db, "/src/root.star", "root")?;
    assert_eq!(codes(&check(&db, root)), ["invalid-argument-type"]);

    let settings = ProgramSettings::empty(db.vendored());
    let python_builtins = Program::from_settings(&db, &settings);
    let file = ProgramFile::new_starlark(&db, root, python_builtins);
    assert!(check_file_unwrap(&db, file).is_empty());
    assert_eq!(codes(&check(&db, root)), ["invalid-argument-type"]);
    Ok(())
}

#[test]
fn conditional_exports_report_missing_members_at_the_load_alias() -> anyhow::Result<()> {
    let source = "load(\":dep.star\", selected=\"value\")\n";
    let registry = crate::default_lint_registry();
    let mut rules = RuleSelection::from_registry(registry);
    rules.enable(
        registry.get("possibly-missing-import")?,
        Severity::Error,
        LintSource::File,
    );
    let mut db = builder()
        .with_rule_selection(rules)
        .with_file("/src/root.star", source)
        .with_file(
            "/src/dep.star",
            indoc! {r#"
                def flag() -> bool:
                    return True
                if flag():
                    value = 1
            "#},
        )
        .build()?;
    let root = module(&db, "/src/root.star", "root")?;
    let dep = module(&db, "/src/dep.star", "dep")?;
    let edge = load(&db, root, dep);
    root.set_loads(&mut db).to(Box::new([edge]));
    let diagnostics = check(&db, root);
    assert_eq!(codes(&diagnostics), ["possibly-missing-import"]);
    let range = diagnostics[0].primary_span().unwrap().range().unwrap();
    assert_eq!(
        &source[range.start().to_usize()..range.end().to_usize()],
        "selected"
    );
    Ok(())
}

#[test]
fn unreachable_calls_are_checked_without_changing_live_exports() -> anyhow::Result<()> {
    let source = indoc! {r#"
        load(":dep.star", "take", "value")
        if False:
            take("bad")
        if True:
            pass
        else:
            take("bad")
        def after_return() -> int:
            return 1
            take("bad")
        take(value)
    "#};
    let mut db = builder()
        .with_file("/src/root.star", source)
        .with_file(
            "/src/dep.star",
            indoc! {r#"
                def take(value: int) -> int:
                    return value
                value = 1
                if False:
                    value = "wrong"
                    take("bad")
            "#},
        )
        .build()?;
    let root = module(&db, "/src/root.star", "root")?;
    let dep = module(&db, "/src/dep.star", "dep")?;
    let edge = load(&db, root, dep);
    root.set_loads(&mut db).to(Box::new([edge]));
    let diagnostics = check(&db, root);
    assert_eq!(codes(&diagnostics), ["invalid-argument-type"; 3]);
    for diagnostic in &diagnostics {
        let range = diagnostic.primary_span().unwrap().range().unwrap();
        assert_eq!(
            &source[range.start().to_usize()..range.end().to_usize()],
            "\"bad\""
        );
    }
    assert_eq!(codes(&check(&db, dep)), ["invalid-argument-type"]);
    let python = ProgramFile::new(&db, dep.file(&db), db.program());
    assert!(check_file_unwrap(&db, python).is_empty());
    Ok(())
}

#[test]
fn unreachable_lookup_preserves_local_shadowing() -> anyhow::Result<()> {
    let mut db = builder()
        .with_file(
            "/src/root.star",
            indoc! {r#"
            load(":dep.star", "take")
            def parameter(take: int):
                if False:
                    take("bad")
            def reassigned():
                take = 1
                if False:
                    take("bad")
        "#},
        )
        .with_file(
            "/src/dep.star",
            indoc! {r#"
            def take(value: int) -> int:
                return value
        "#},
        )
        .build()?;
    let root = module(&db, "/src/root.star", "root")?;
    let dep = module(&db, "/src/dep.star", "dep")?;
    let edge = load(&db, root, dep);
    root.set_loads(&mut db).to(Box::new([edge]));
    assert_eq!(codes(&check(&db, root)), ["call-non-callable"; 2]);
    Ok(())
}
