use ruff_db::files::system_path_to_file;
use ruff_db::parsed::parsed_module;
use ruff_db::source::source_text;
use ruff_db::system::DbWithWritableSystem as _;
use ruff_text_size::{TextLen, TextRange};

use super::*;
use crate::db::tests::{TestDb, TestDbBuilder};
use crate::types::definition_resolution::definitions_for_attribute;
use crate::types::ide_support::{
    definitions_for_keyword_argument, inlay_hint_call_argument_details,
};
use crate::types::{
    CheckedArgument, CheckedCall, DictionaryItem, DictionaryItems, KnownClass, Parameter,
    Parameters, Signature,
};
use crate::{HasType, SemanticModel};

#[test]
fn checked_calls_share_dictionary_observations() -> anyhow::Result<()> {
    fn observe<'db>(db: &'db TestDb, call: &CheckedCall<'_, 'db>) -> Option<Type<'db>> {
        if call.declaration()?.name(db)?.as_str() != "observe" {
            return None;
        }
        let Some(DictionaryItems { items, is_complete }) = call.dictionary_argument("value") else {
            return Some(Type::string_literal(db, "unavailable"));
        };
        Some(describe(
            db,
            call.file(),
            DictionaryItems { items, is_complete },
        ))
    }

    fn describe<'db>(
        db: &'db TestDb,
        file: ProgramFile<'db>,
        entries: DictionaryItems<'db>,
    ) -> Type<'db> {
        let DictionaryItems { items, is_complete } = entries;
        let source = source_text(db, file.file(db));
        let env = ProgramEnvironment::from_file(file);
        let mut description = if is_complete { "complete" } else { "partial" }.to_owned();
        // Preserve key order, values, and their source spelling through the public call view.
        for DictionaryItem {
            name,
            ty,
            source: range,
        } in items
        {
            write!(
                description,
                "; {name}: {} at {}",
                ty.display(db, &env),
                &source[range]
            )
            .unwrap();
        }
        Type::string_literal(db, description.as_str())
    }

    let mut db = TestDbBuilder::new()
        .with_file(
            "/src/native.pyi",
            "def observe(value: object) -> str: ...\n",
        )
        .with_file("/src/main.py", "")
        .with_call_result_provider(observe)
        .build()?;
    let file = system_path_to_file(&db, "/src/main.py")?;
    for (source, expected) in [
        ("result = observe({})", "complete"),
        (
            "result = observe({'x': 1, 'y': 2, 'x': 3})",
            "complete; x: Literal[3] at 'x'; y: Literal[2] at 'y'",
        ),
        (
            "key = 'x'\nresult = observe(value={key: 1})",
            "complete; x: Literal[1] at key",
        ),
        (
            "values = {'x': 1}\nresult = observe(values)",
            "partial; x: Literal[1] at 'x'",
        ),
        (
            "values = {'x': 1}\nvalues['x'] = 'new'\nresult = observe(value=values)",
            "partial; x: Literal[\"new\"] at 'x'",
        ),
        (
            "values = {'x': 1}\nvalues = {}\nresult = observe(values)",
            "partial",
        ),
        (
            "values = {'x': 1}\ndel values['x']\nresult = observe(values)",
            "partial",
        ),
        (
            "values = {'x': 1}\nvalues.clear()\nresult = observe(values)",
            "partial; x: Literal[1] at 'x'",
        ),
        (
            "values = {'x': 1}\nif bool():\n    values['y'] = 2\nresult = observe(values)",
            "partial; x: Literal[1] at 'x'",
        ),
        (
            "values = {}\nvalues['inner'] = {'x': 1}\nvalues['inner']['y'] = 2\nresult = observe(values['inner'])",
            "partial; x: Literal[1] at 'x'; y: Literal[2] at 'y'",
        ),
        (
            "values = {'x': 1}\nresult = observe({**values})",
            "unavailable",
        ),
        ("result = observe(1)", "unavailable"),
    ] {
        db.write_file(
            "/src/main.py",
            format!("from native import observe\n{source}\n"),
        )?;
        let diagnostics = db.check_file(file);
        assert!(diagnostics.is_empty(), "{source}: {diagnostics:#?}");
        let result = crate::place::global_symbol(&db, db.program_file(file), "result")
            .place
            .expect_type();
        assert_eq!(result.string_literal_value(&db), Some(expected), "{source}");
    }
    db.write_file("/src/main.py", "from native import observe\ndef nested():\n    values = {'inner': 1}\n    values['second'] = 2\n    return observe(values)\nannotation: \"{'key': int}\"\n")?;
    let file = db.program_file(file);
    let model = SemanticModel::new(&db, file);
    let parsed = parsed_module(&db, file.python_file(&db)).load(&db);
    let [
        ast::Stmt::ImportFrom(_),
        ast::Stmt::FunctionDef(function),
        ast::Stmt::AnnAssign(annotation),
    ] = parsed.suite().as_slice()
    else {
        panic!("expected nested function and annotation");
    };
    let ast::Stmt::Return(statement) = function.body.last().unwrap() else {
        panic!("expected return");
    };
    let ast::Expr::Call(call) = statement.value.as_deref().unwrap() else {
        panic!("expected observe call");
    };
    let [argument] = call.arguments.args.as_ref() else {
        panic!("expected one dictionary argument");
    };
    let entries = model.dictionary_items(argument).unwrap();
    assert_eq!(
        describe(&db, file, entries),
        ast::ExprRef::Call(call).inferred_type(&model).unwrap(),
    );
    let ast::Expr::StringLiteral(annotation) = annotation.annotation.as_ref() else {
        panic!("expected string annotation");
    };
    let (parsed, detached) = model.enter_string_annotation(annotation).unwrap();
    assert!(detached.dictionary_items(&parsed.syntax().body).is_none());
    Ok(())
}

const DECLARATIONS: &str = "\
def make(value: object, required: int = 0) -> object: ...
def make_class(value: object) -> type: ...
class Factory:
    def method(self, value: int, second: str) -> object: ...
factory: Factory
";

fn factory_result<'db>(db: &'db TestDb, call: &CheckedCall<'_, 'db>) -> Option<Type<'db>> {
    let declaration = call.declaration()?;
    if declaration
        .program_file(db)
        .file(db)
        .path(db)
        .as_system_path()?
        .as_str()
        != "/src/native.pyi"
    {
        return None;
    }
    let name = declaration.name(db)?;
    let CheckedArgument::Value { ty, expression } = call.argument("value") else {
        return None;
    };
    let env = ProgramEnvironment::from_file(call.file());
    let (field_type, members) = match name.as_str() {
        "make" => (ty, Box::default()),
        "method" => {
            let CheckedArgument::Value {
                ty: receiver,
                expression: None,
            } = call.argument("self")
            else {
                panic!("bound receiver should retain its type without a source expression");
            };
            assert!(matches!(receiver, Type::NominalInstance(_)));
            assert_eq!(
                Some(ty),
                expression.and_then(|expression| call.expression_type(expression))
            );
            (ty, Box::default())
        }
        "make_class" => {
            let int = KnownClass::Int.to_instance(db, &env);
            let init = Type::function_like_callable(
                db,
                Signature::new(
                    Parameters::standard([
                        Parameter::positional_only(Some(Name::new("self"))),
                        Parameter::keyword_only(Name::new("value")).with_annotated_type(int),
                    ]),
                    Type::none(db, &env),
                ),
            );
            (int, Box::from([(Name::new("__init__"), init)]))
        }
        _ => return None,
    };
    let class = call.class_type(
        db,
        ProvidedClass {
            name: Name::new("Record"),
            bases: Box::default(),
            class_members: members,
            instance_fields: ProvidedInstanceFields {
                fields: Box::from([ProvidedField {
                    name: Name::new("value"),
                    ty: field_type,
                    source: None,
                }]),
                has_dynamic_fields: false,
                data: Some(ProvidedData::new(Name::new("native record"))),
            },
        },
    );
    if name == "make_class" {
        Some(class)
    } else {
        class.to_instance_approximation(db, &env)
    }
}

fn setup(source: &str) -> anyhow::Result<TestDb> {
    TestDbBuilder::new()
        .with_file("/src/native.pyi", DECLARATIONS)
        .with_file("/src/main.py", source)
        .with_call_result_provider(factory_result)
        .build()
}

#[test]
fn source_call_class_matches_factory_result_identity() -> anyhow::Result<()> {
    let db = setup("from native import make\nrecord = make(1)\n")?;
    let file = system_path_to_file(&db, "/src/main.py")?;
    let file = db.program_file(file);
    let module = parsed_module(&db, file.python_file(&db)).load(&db);
    let assignment = module.suite()[1].as_assign_stmt().unwrap();
    let call = assignment.value.as_call_expr().unwrap();
    let model = crate::SemanticModel::new(&db, file);
    let class = model
        .provided_class_at_call(
            call,
            ProvidedClass {
                name: Name::new("Record"),
                bases: Box::default(),
                class_members: Box::default(),
                instance_fields: ProvidedInstanceFields {
                    fields: Box::from([ProvidedField {
                        name: Name::new("value"),
                        ty: Type::int_literal(1),
                        source: None,
                    }]),
                    has_dynamic_fields: false,
                    data: Some(ProvidedData::new(Name::new("native record"))),
                },
            },
        )
        .unwrap();
    let inferred = crate::place::global_symbol(&db, file, "record")
        .place
        .expect_type();
    assert_eq!(
        class.to_instance_approximation(&db, &model.program_environment()),
        Some(inferred)
    );
    Ok(())
}

#[test]
fn supplied_instance_storage_shadows_inherited_defaults_but_not_data_descriptors()
-> anyhow::Result<()> {
    fn derived_factory<'db>(db: &'db TestDb, call: &CheckedCall<'_, 'db>) -> Option<Type<'db>> {
        let name = call.declaration()?.name(db)?;
        let fields = match name.as_str() {
            "make" => Box::from([ProvidedField {
                name: Name::new_static("value"),
                ty: Type::int_literal(1),
                source: None,
            }]),
            "make_open" => Box::default(),
            _ => return None,
        };
        let native = system_path_to_file(db, "/src/native.pyi").ok()?;
        let base = crate::place::global_symbol(db, db.program_file(native), "Base")
            .place
            .expect_type();
        let class = call.class_type(
            db,
            ProvidedClass {
                name: Name::new_static("Derived"),
                bases: Box::from([base]),
                class_members: Box::default(),
                instance_fields: ProvidedInstanceFields {
                    fields,
                    has_dynamic_fields: name == "make_open",
                    data: None,
                },
            },
        );
        class.to_instance_approximation(db, &ProgramEnvironment::from_file(call.file()))
    }

    for (declaration, property) in [
        ("class Base:\n    value: int\n", false),
        ("class Base:\n    def value(self) -> str: ...\n", false),
        (
            "class Base:\n    @property\n    def value(self) -> str: ...\n",
            true,
        ),
    ] {
        let native = format!(
            "{declaration}\nclass Other:\n    def value(self) -> str: ...\ndef make() -> object: ...\ndef make_open() -> object: ...\n"
        );
        let db = TestDbBuilder::new()
            .with_file("/src/native.pyi", &native)
            .with_file(
                "/src/main.py",
                "from native import make, make_open\nstored = make()\nresult = stored.value\nopened = make_open()\nopen_result = opened.value\n",
            )
            .with_call_result_provider(derived_factory)
            .build()?;
        let file = system_path_to_file(&db, "/src/main.py")?;
        let diagnostics = db.check_file(file);
        assert!(diagnostics.is_empty(), "{diagnostics:#?}");
        let file = db.program_file(file);
        let env = ProgramEnvironment::from_file(file);
        let actual = crate::place::global_symbol(&db, file, "result")
            .place
            .expect_type();
        let expected = if property {
            KnownClass::Str.to_instance(&db, &env)
        } else {
            Type::int_literal(1)
        };
        assert_eq!(
            actual,
            expected,
            "{declaration}: {}",
            actual.display(&db, &env)
        );
        let native = db.program_file(system_path_to_file(&db, "/src/native.pyi")?);
        let opened = crate::place::global_symbol(&db, file, "opened")
            .place
            .expect_type();
        let base_member = opened
            .member_lookup_with_policy(
                &db,
                &env,
                "value",
                crate::types::MemberLookupPolicy::NO_INSTANCE_FALLBACK,
            )
            .place
            .expect_type();
        let open_result = crate::place::global_symbol(&db, file, "open_result")
            .place
            .expect_type();
        let expected_open = if property {
            expected
        } else {
            crate::types::UnionType::from_two_elements(&db, &env, Type::unknown(), base_member)
        };
        assert!(
            open_result.is_equivalent_to(&db, &env, expected_open),
            "{declaration}: expected {}, got {}",
            expected_open.display(&db, &env),
            open_result.display(&db, &env),
        );

        let other = crate::place::global_symbol(&db, native, "Other")
            .place
            .expect_type()
            .to_instance_approximation(&db, &env)
            .unwrap();
        let stored = crate::place::global_symbol(&db, file, "stored")
            .place
            .expect_type();
        let mixed = crate::types::UnionType::from_two_elements(&db, &env, stored, other);
        let expected_mixed = crate::types::UnionType::from_two_elements(
            &db,
            &env,
            expected,
            other.member(&db, &env, "value").place.expect_type(),
        );
        let mixed_member = mixed.member(&db, &env, "value");
        let mixed_type = mixed_member.place.expect_type();
        assert!(
            mixed_type.is_equivalent_to(&db, &env, expected_mixed),
            "{declaration}: expected {}, got {}",
            expected_mixed.display(&db, &env),
            mixed_type.display(&db, &env)
        );
        assert!(
            !mixed_member
                .qualifiers
                .contains(crate::types::TypeQualifiers::GUARANTEED_INSTANCE_STORAGE)
        );
    }
    Ok(())
}

#[test]
fn supplied_declarations_preserve_keyword_and_attribute_navigation() -> anyhow::Result<()> {
    fn factory<'db>(db: &'db TestDb, call: &CheckedCall<'_, 'db>) -> Option<Type<'db>> {
        let name = call.declaration()?.name(db)?;
        if name != "make" && name != "make_sourceless" {
            return None;
        }
        let env = ProgramEnvironment::from_file(call.file());
        let native = system_path_to_file(db, "/src/native.pyi").ok()?;
        let base = crate::place::global_symbol(db, db.program_file(native), "Base")
            .place
            .expect_type();
        let source = FileRange::new(
            system_path_to_file(db, "/src/schema.py").ok()?,
            TextRange::new(0.into(), 5.into()),
        );
        let init = Type::function_like_callable(
            db,
            Signature::new(
                Parameters::standard([
                    Parameter::positional_only(Some(Name::new_static("self"))),
                    Parameter::positional_or_keyword(Name::new_static("value"))
                        .with_annotated_type(KnownClass::Int.to_instance(db, &env))
                        .with_source_range(source),
                ]),
                Type::none(db, &env),
            ),
        );
        Some(call.class_type(
            db,
            ProvidedClass {
                name: Name::new_static("Derived"),
                bases: Box::from([base]),
                class_members: Box::from([(Name::new_static("__init__"), init)]),
                instance_fields: ProvidedInstanceFields {
                    fields: Box::from([ProvidedField {
                        name: Name::new_static("value"),
                        ty: Type::int_literal(1),
                        source: (name == "make").then_some(source),
                    }]),
                    has_dynamic_fields: false,
                    data: None,
                },
            },
        ))
    }

    for (base, property, native_member) in [
        ("class Base: pass\n", false, false),
        ("class Base:\n    value: int\n", false, true),
        (
            "class SetterOnly:\n    def __set__(self, instance: object, value: object) -> None: ...\nclass Base:\n    value = SetterOnly()\n",
            false,
            true,
        ),
        (
            "class Base:\n    def value(self) -> str: ...\n",
            false,
            true,
        ),
        (
            "class Base:\n    @property\n    def value(self) -> str: ...\n",
            true,
            true,
        ),
        (
            "class Base:\n    __slots__ = ('value',)\n    value: int\n",
            false,
            true,
        ),
    ] {
        let db = TestDbBuilder::new()
            .with_file(
                "/src/native.pyi",
                &format!("{base}def make() -> type: ...\ndef make_sourceless() -> type: ...\n"),
            )
            .with_file("/src/schema.py", "value = 0\n")
            .with_file(
                "/src/main.py",
                "\
from native import make, make_sourceless
Derived = make()
instance = Derived(value=1)
Sourceless = make_sourceless()
sourceless = Sourceless(value=1)
class ChildMethod(Derived):
    def value(self) -> str: ...
class ChildAnnotation(Derived):
    value: str
class ChildDefault(Derived):
    value = 'native'
class ChildProperty(Derived):
    @property
    def value(self) -> str: ...
child_method: ChildMethod
child_annotation: ChildAnnotation
child_default: ChildDefault
child_property: ChildProperty
Derived(1)
",
            )
            .with_call_result_provider(factory)
            .build()?;
        let file = db.program_file(system_path_to_file(&db, "/src/main.py")?);
        let env = ProgramEnvironment::from_file(file);
        let model = crate::SemanticModel::new(&db, file);
        let module = parsed_module(&db, file.python_file(&db)).load(&db);
        let call = module.suite()[2]
            .as_assign_stmt()
            .unwrap()
            .value
            .as_call_expr()
            .unwrap();
        let source = FileRange::new(
            system_path_to_file(&db, "/src/schema.py")?,
            TextRange::new(0.into(), 5.into()),
        );
        if !native_member {
            let keyword =
                definitions_for_keyword_argument(&model, &call.arguments.keywords[0], call);
            assert_eq!(
                keyword
                    .iter()
                    .map(|definition| definition.focus_range(&db))
                    .collect::<Vec<_>>(),
                [source],
                "{base}"
            );

            let positional_call = module
                .suite()
                .last()
                .unwrap()
                .as_expr_stmt()
                .unwrap()
                .value
                .as_call_expr()
                .unwrap();
            let hints = inlay_hint_call_argument_details(&db, &model, positional_call).unwrap();
            assert_eq!(
                hints.argument_names.get(&0),
                Some(&("value".to_owned(), Some(source)))
            );

            // The ordinary read owner currently treats an intersection of descriptor values as
            // non-data. Navigation must select the same stored field without evaluating getters.
            let native = db.program_file(system_path_to_file(&db, "/src/native.pyi")?);
            let base_instance = crate::place::global_symbol(&db, native, "Base")
                .place
                .expect_type()
                .to_instance_approximation(&db, &env)
                .unwrap();
            let descriptor = crate::types::IntersectionType::from_two_elements(
                &db,
                &env,
                KnownClass::Property.to_instance(&db, &env),
                base_instance,
            );
            assert!(descriptor.is_intersection());
            let class = model
                .provided_class_at_call(
                    call,
                    ProvidedClass {
                        name: Name::new_static("IntersectionField"),
                        bases: Box::default(),
                        class_members: Box::from([(Name::new_static("value"), descriptor)]),
                        instance_fields: ProvidedInstanceFields {
                            fields: Box::from([ProvidedField {
                                name: Name::new_static("value"),
                                ty: Type::int_literal(1),
                                source: Some(source),
                            }]),
                            has_dynamic_fields: false,
                            data: None,
                        },
                    },
                )
                .unwrap();
            let instance = class.to_instance_approximation(&db, &env).unwrap();
            assert_eq!(
                instance.member(&db, &env, "value").place.expect_type(),
                Type::int_literal(1)
            );
            assert_eq!(
                definitions_for_attribute(&db, &env, instance, "value")
                    .iter()
                    .map(|definition| definition.focus_range(&db))
                    .collect::<Vec<_>>(),
                [source]
            );
        }

        for name in ["instance", "sourceless", "Derived"] {
            let receiver = crate::place::global_symbol(&db, file, name)
                .place
                .expect_type();
            if name != "Derived" {
                let actual = receiver.member(&db, &env, "value").place.expect_type();
                let expected = if property {
                    KnownClass::Str.to_instance(&db, &env)
                } else {
                    Type::int_literal(1)
                };
                assert_eq!(
                    actual,
                    expected,
                    "{name}: {}; {base}",
                    actual.display(&db, &env)
                );
            }
            let definitions = definitions_for_attribute(&db, &env, receiver, "value");
            if property || (name == "Derived" && native_member) {
                let [definition] = definitions.as_slice() else {
                    panic!("expected native declaration for {name}: {definitions:?}; {base}");
                };
                assert_eq!(
                    definition.focus_range(&db).file(),
                    system_path_to_file(&db, "/src/native.pyi")?
                );
            } else if name == "instance" {
                assert_eq!(
                    definitions
                        .iter()
                        .map(|definition| definition.focus_range(&db))
                        .collect::<Vec<_>>(),
                    [source],
                    "{base}"
                );
            } else {
                assert!(definitions.is_empty(), "{name}: {definitions:?}; {base}");
            }
        }
        if !native_member {
            for (name, supplied_storage) in [
                ("child_method", true),
                ("child_annotation", false),
                ("child_default", true),
                ("child_property", false),
            ] {
                let receiver = crate::place::global_symbol(&db, file, name)
                    .place
                    .expect_type();
                let actual = receiver.member(&db, &env, "value").place.expect_type();
                let expected = if supplied_storage {
                    Type::int_literal(1)
                } else {
                    KnownClass::Str.to_instance(&db, &env)
                };
                assert_eq!(
                    actual,
                    expected,
                    "{name}: {}; {base}",
                    actual.display(&db, &env)
                );
                let definitions = definitions_for_attribute(&db, &env, receiver, "value");
                let [definition] = definitions.as_slice() else {
                    panic!("expected one source for {name}: {definitions:?}");
                };
                if supplied_storage {
                    assert_eq!(definition.focus_range(&db), source, "{name}; {base}");
                } else {
                    assert_eq!(
                        definition.focus_range(&db).file(),
                        file.file(&db),
                        "{name}; {base}"
                    );
                }
            }
        }
    }
    Ok(())
}

#[test]
fn factory_fields_preserve_callable_values_and_binding_errors() -> anyhow::Result<()> {
    let db = setup(
        "\
from native import make as factory
def increment(x: int) -> int:
    return x + 1
record = factory(increment, required='bad')
result = record.value(1)
record.value('bad')
",
    )?;
    let file = system_path_to_file(&db, "/src/main.py")?;
    let diagnostics = db.check_file(file);
    assert_eq!(
        diagnostics
            .iter()
            .map(|diagnostic| diagnostic.id().as_str())
            .collect::<Vec<_>>(),
        ["invalid-argument-type", "invalid-argument-type"],
        "{diagnostics:#?}"
    );
    let file = db.program_file(file);
    let env = ProgramEnvironment::from_file(file);
    let result = crate::place::global_symbol(&db, file, "result")
        .place
        .ignore_possibly_undefined()
        .unwrap();
    assert_eq!(result, KnownClass::Int.to_instance(&db, &env));
    let record = crate::place::global_symbol(&db, file, "record")
        .place
        .ignore_possibly_undefined()
        .unwrap();
    assert_eq!(
        record
            .provided_data(&db, &env)
            .unwrap()
            .downcast_ref::<Name>(),
        Some(&Name::new("native record"))
    );
    let members = crate::types::list_members::all_members(&db, &env, record);
    assert!(members.iter().any(|member| member.name == "value"));
    Ok(())
}

#[test]
fn factory_method_arguments_skip_the_synthetic_receiver() -> anyhow::Result<()> {
    let db = setup(
        "from native import factory\nresult = factory.method(7, 'second')\nkeyword = factory.method(second='second', value=8)\nfirst: int = result.value\nsecond: int = keyword.value\n",
    )?;
    let file = system_path_to_file(&db, "/src/main.py")?;
    let diagnostics = db.check_file(file);
    assert!(diagnostics.is_empty(), "{diagnostics:#?}");
    Ok(())
}

#[test]
fn uncertain_unpacking_does_not_supply_a_definite_factory_value() -> anyhow::Result<()> {
    let mut db = setup("from native import make\nitems: list[int] = []\nresult = make(*items)\n")?;
    db.write_file(
        "/src/native.pyi",
        "def make(value: object = None) -> object: ...\n",
    )?;
    let file = db.program_file(system_path_to_file(&db, "/src/main.py")?);
    let result = crate::place::global_symbol(&db, file, "result")
        .place
        .ignore_possibly_undefined()
        .unwrap();
    assert_eq!(result, Type::object());
    Ok(())
}

#[test]
fn synthesized_default_keeps_its_source_spelling() -> anyhow::Result<()> {
    let expression = "('préfix' + 'suffix')";
    let db = TestDbBuilder::new()
        .with_file("/src/main.py", expression)
        .build()?;
    let file = system_path_to_file(&db, "/src/main.py")?;
    let env = ProgramEnvironment::from_file(db.program_file(file));
    let signature = Signature::new(
        Parameters::standard([Parameter::keyword_only(Name::new("value"))
            .with_annotated_type(KnownClass::Str.to_instance(&db, &env))
            .with_default(crate::types::ParameterDefault::Source {
                ty: Type::string_literal(&db, "préfixsuffix"),
                source: ruff_db::files::FileRange::new(
                    file,
                    TextRange::up_to(expression.text_len()),
                ),
            })]),
        Type::none(&db, &env),
    );
    assert_eq!(
        signature.display(&db, &env).to_string(),
        "(*, value: str = ('préfix' + 'suffix')) -> None"
    );
    Ok(())
}

#[test]
fn factory_constructors_use_shared_binding_and_distinct_nominal_classes() -> anyhow::Result<()> {
    let db = setup(
        "\
from native import make_class
A = make_class(0)
B = make_class(0)
a = A(value=1)
b = B(value=2)
A(value='bad')
def accept(value: A): ...
accept(b)
",
    )?;
    let file = system_path_to_file(&db, "/src/main.py")?;
    let diagnostics = db.check_file(file);
    assert_eq!(
        diagnostics
            .iter()
            .map(|diagnostic| diagnostic.id().as_str())
            .collect::<Vec<_>>(),
        ["invalid-argument-type", "invalid-argument-type"],
        "{diagnostics:#?}"
    );
    let file = db.program_file(file);
    let env = ProgramEnvironment::from_file(file);
    let a = crate::place::global_symbol(&db, file, "a")
        .place
        .ignore_possibly_undefined()
        .unwrap();
    let b = crate::place::global_symbol(&db, file, "b")
        .place
        .ignore_possibly_undefined()
        .unwrap();
    assert_ne!(a, b);
    assert!(!a.is_assignable_to(&db, &env, b));
    Ok(())
}

#[test]
fn factory_resolution_follows_shadowing_and_loaded_edits() -> anyhow::Result<()> {
    let mut db = setup(
        "\
from native import make
result = make(1)
def make(value: str) -> str: return value
shadowed = make('text')
",
    )?;
    let file = system_path_to_file(&db, "/src/main.py")?;
    let check = |db: &TestDb| {
        let file = db.program_file(file);
        let env = ProgramEnvironment::from_file(file);
        let result = crate::place::global_symbol(db, file, "result")
            .place
            .ignore_possibly_undefined()
            .unwrap();
        assert!(result.provided_data(db, &env).is_some());
        let shadowed = crate::place::global_symbol(db, file, "shadowed")
            .place
            .ignore_possibly_undefined()
            .unwrap();
        assert_eq!(shadowed, KnownClass::Str.to_instance(db, &env));
    };
    check(&db);
    db.write_file("/src/native.pyi", "def make(value: str) -> object: ...\n")?;
    let diagnostics = db.check_file(file);
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.id().as_str() == "invalid-argument-type"),
        "{diagnostics:#?}"
    );
    check(&db);
    Ok(())
}

#[test]
fn callable_metadata_survives_signature_transforms() -> anyhow::Result<()> {
    let db = TestDbBuilder::new().build()?;
    let env = db.program_environment();
    let callable = Type::single_callable(
        &db,
        Signature::new(Parameters::empty(), KnownClass::Int.to_instance(&db, &env)),
    )
    .with_callable_data(&db, ProvidedData::new(Name::new("generated function docs")))
    .unwrap();
    let wrapper = callable
        .map_callable_signatures(
            &db,
            &env,
            crate::types::CallableTypeKind::FunctionLike,
            |signature| signature.with_return_type(KnownClass::Str.to_instance(&db, &env)),
        )
        .unwrap();
    assert_eq!(
        wrapper.provided_data(&db, &env),
        callable.provided_data(&db, &env)
    );
    assert_eq!(
        wrapper
            .provided_data(&db, &env)
            .unwrap()
            .downcast_ref::<Name>(),
        Some(&Name::new("generated function docs")),
    );
    Ok(())
}
use std::fmt::Write;
