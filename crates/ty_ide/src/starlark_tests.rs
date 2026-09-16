//! IDE queries consume the same explicit module identities as Starlark analysis.

use ruff_db::files::system_path_to_file;
use ruff_db::parsed::parsed_module;
use ruff_db::source::source_text;
use ruff_python_ast::name::Name;
use ruff_text_size::Ranged;
use salsa::Setter;
use ty_python_core::ProgramFile;
use ty_python_core::program::Program;
use ty_python_core::starlark::{
    StarlarkEnvironment, StarlarkGlobalDeclaration, StarlarkGlobalKind, StarlarkLoad,
    StarlarkModule, StarlarkModuleRole, load_call,
};
use ty_python_semantic::Db;

use crate::tests::CursorTest;
use crate::{CompletionCapabilities, CompletionSettings, goto_definition, local_completion};

fn module(db: &ty_project::TestDb, path: &str) -> StarlarkModule {
    StarlarkModule::new(
        db,
        system_path_to_file(db, path).expect("fixture source"),
        Name::new(path),
        Box::default(),
        Box::default(),
        None,
        StarlarkModuleRole::Root,
    )
}

fn program_file(db: &ty_project::TestDb, module: StarlarkModule) -> ProgramFile<'_> {
    let python = db.program_file(module.file(db)).program(db);
    let program = Program::new_starlark(
        db,
        python.python_platform(db),
        python.resolver_environment(db),
    );
    ProgramFile::new_starlark(db, module, program)
}

fn set_load(db: &mut ty_project::TestDb, importer: StarlarkModule, target: StarlarkModule) {
    let file = program_file(db, importer);
    let parsed = parsed_module(db, file.python_file(db)).load(db);
    let call = parsed
        .suite()
        .iter()
        .filter_map(|statement| statement.as_expr_stmt())
        .find_map(|statement| load_call(&statement.value))
        .expect("fixture load");
    let range = call.range();
    importer.set_loads(db).to(Box::new([StarlarkLoad {
        range,
        module: target,
    }]));
}

#[test]
fn starlark_completion_uses_runtime_namespace() {
    let mut test = CursorTest::builder()
        .source("/main.star", "visible = 1\n<CURSOR>")
        .source(
            "/__builtins__.pyi",
            "__all__ = ['public']\npublic: int\nhidden: int\n",
        )
        .build();
    let module = module(&test.db, "/main.star");
    let environment = StarlarkEnvironment::new(
        &test.db,
        Box::new([StarlarkGlobalDeclaration {
            name: Name::new("record"),
            kind: StarlarkGlobalKind::Record,
        }]),
    );
    module.set_environment(&mut test.db).to(Some(environment));
    let completions = local_completion(
        &test.db,
        &CompletionSettings::default(),
        CompletionCapabilities::default(),
        program_file(&test.db, module),
        test.cursor.offset,
    );
    let names: Vec<_> = completions.iter().map(|item| item.name.as_str()).collect();
    for name in ["visible", "public", "record", "load", "def", "None"] {
        assert!(names.contains(&name), "missing {name}: {names:?}");
    }
    for name in [
        "hidden",
        "__file__",
        "__builtins__",
        "import",
        "class",
        "async",
        "raise",
    ] {
        assert!(!names.contains(&name), "unexpected {name}: {names:?}");
    }
    assert!(completions.iter().all(|item| item.import.is_none()));
}

#[test]
fn starlark_loaded_definition_uses_final_binding() {
    for source in [
        "load('//pkg:dep.bzl', alias='value')\nali<CURSOR>as\n",
        "load('//pkg:dep.bzl', ali<CURSOR>as='value')\n",
        "load('//pkg:dep.bzl', alias='value<CURSOR>')\n",
    ] {
        let mut test = CursorTest::builder()
            .source("/main.star", source)
            .source(
                "/dep.bzl",
                "value = 1\nvalue = 'final'\nif False:\n    value = False\n",
            )
            .build();
        let importer = module(&test.db, "/main.star");
        let target = module(&test.db, "/dep.bzl");
        set_load(&mut test.db, importer, target);
        let definitions = goto_definition(
            &test.db,
            program_file(&test.db, importer),
            test.cursor.offset,
        )
        .expect("loaded definition");
        let locations: Vec<_> = definitions.value.into_iter().collect();
        assert_eq!(locations.len(), 1, "{locations:?}");
        assert_eq!(locations[0].file(), target.file(&test.db));
        assert_eq!(locations[0].focus_range().start().to_usize(), 10);
    }
}

#[test]
fn starlark_load_label_navigates_to_module() {
    let mut test = CursorTest::builder()
        .source("/main.star", "load('//pk<CURSOR>g:dep.bzl', 'value')\n")
        .source("/dep.bzl", "value = 1\n")
        .build();
    let importer = module(&test.db, "/main.star");
    let target = module(&test.db, "/dep.bzl");
    set_load(&mut test.db, importer, target);
    let definitions = goto_definition(
        &test.db,
        program_file(&test.db, importer),
        test.cursor.offset,
    )
    .expect("load target");
    let locations: Vec<_> = definitions.value.into_iter().collect();
    assert_eq!(locations.len(), 1);
    assert_eq!(locations[0].file(), target.file(&test.db));
    assert_eq!(locations[0].focus_range().start().to_usize(), 0);
}

#[test]
fn starlark_load_navigation_requires_an_export() {
    for (symbol, source) in [
        ("_private", "_private = 1\n"),
        ("value", "load('//other:dep.bzl', 'value')\n"),
    ] {
        let mut test = CursorTest::builder()
            .source(
                "/main.star",
                format!("load('//pkg:dep.bzl', '{symbol}<CURSOR>')\n"),
            )
            .source("/dep.bzl", source)
            .source("/other.bzl", "value = 1\n")
            .build();
        let importer = module(&test.db, "/main.star");
        let target = module(&test.db, "/dep.bzl");
        let other = module(&test.db, "/other.bzl");
        if symbol == "value" {
            set_load(&mut test.db, target, other);
        }
        set_load(&mut test.db, importer, target);
        let definitions = goto_definition(
            &test.db,
            program_file(&test.db, importer),
            test.cursor.offset,
        )
        .expect("load string");
        assert_eq!(definitions.value.into_iter().count(), 0, "{source}");
    }
}

#[test]
fn starlark_record_fields_complete_and_navigate() {
    for (tail, member_expected) in [("item.<CURSOR>", true), ("Item.<CURSOR>", false)] {
        let mut test = CursorTest::builder()
            .source(
                "/main.star",
                format!("Item = record(name=str)\nitem = Item(name='x')\n{tail}\n"),
            )
            .build();
        let module = module(&test.db, "/main.star");
        let environment = StarlarkEnvironment::new(
            &test.db,
            Box::new([StarlarkGlobalDeclaration {
                name: Name::new("record"),
                kind: StarlarkGlobalKind::Record,
            }]),
        );
        module.set_environment(&mut test.db).to(Some(environment));
        let completions = local_completion(
            &test.db,
            &CompletionSettings::default(),
            CompletionCapabilities::default(),
            program_file(&test.db, module),
            test.cursor.offset,
        );
        assert_eq!(
            completions.iter().any(|item| item.name == "name"),
            member_expected,
            "{tail}"
        );
    }
    for tail in ["item.na<CURSOR>me", "Item(na<CURSOR>me='x')"] {
        let mut test = CursorTest::builder()
            .source(
                "/main.star",
                format!("descriptor = field(str)\nOther = record(name=descriptor)\nItem = record(name=descriptor)\nitem = Item(name='x')\n{tail}\n"),
            )
            .build();
        let module = module(&test.db, "/main.star");
        let environment = StarlarkEnvironment::new(
            &test.db,
            Box::new([
                StarlarkGlobalDeclaration {
                    name: Name::new("record"),
                    kind: StarlarkGlobalKind::Record,
                },
                StarlarkGlobalDeclaration {
                    name: Name::new("field"),
                    kind: StarlarkGlobalKind::Field,
                },
            ]),
        );
        module.set_environment(&mut test.db).to(Some(environment));
        let definitions =
            goto_definition(&test.db, program_file(&test.db, module), test.cursor.offset)
                .expect("record field");
        let locations: Vec<_> = definitions.value.into_iter().collect();
        assert_eq!(locations.len(), 1, "{tail}: {locations:?}");
        let range = locations[0].focus_range();
        let text = source_text(&test.db, locations[0].file());
        assert_eq!(&text[range], "name");
        assert_eq!(
            range.start().to_usize(),
            text.as_str().rfind("name=descriptor").unwrap()
        );
    }
}
