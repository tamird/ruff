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
use ty_python_core::starlark::{StarlarkLoad, StarlarkModule, load_call};
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
