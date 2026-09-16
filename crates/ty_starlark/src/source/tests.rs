use ruff_db::diagnostic::{DiagnosticId, Severity};
use ruff_db::files::{File, system_path_to_file};
use ruff_db::system::{DbWithTestSystem as _, DbWithWritableSystem as _};
use ruff_python_ast::PythonVersion;
use ruff_python_parser::{Mode, ParseOptions, parse_unchecked};

use crate::bazel::{BazelLoadError, BazelRepository};
use crate::testing::test_db;

use super::{
    AdmittedBazelSource, BazelAdmissionError, BazelAdmissionFailure, BazelSource,
    BazelSourceAdmission, admit_bazel_source,
};

fn admitted(admission: &BazelSourceAdmission) -> anyhow::Result<&AdmittedBazelSource> {
    match admission {
        BazelSourceAdmission::Admitted(source) => Ok(source),
        BazelSourceAdmission::Opaque(failure) => {
            anyhow::bail!("expected admitted .bzl source, found {failure:?}")
        }
    }
}

fn opaque(admission: &BazelSourceAdmission) -> anyhow::Result<&BazelAdmissionFailure> {
    match admission {
        BazelSourceAdmission::Opaque(failure) => Ok(failure),
        BazelSourceAdmission::Admitted(source) => {
            anyhow::bail!("expected opaque .bzl source, found {source:?}")
        }
    }
}

#[test]
fn admits_entire_plain_bazel_source_without_python_project() -> anyhow::Result<()> {
    let (db, root) = test_db(&[
        ("MODULE.bazel", ""),
        ("pkg/BUILD.bazel", ""),
        (
            "pkg/defs.bzl",
            "def keep_int(value):\n    if value > 0:\n        return value\n    return 0\n\nRESULT = keep_int(1)\n",
        ),
    ])?;
    let file = system_path_to_file(&db, root.join("pkg/defs.bzl"))?;
    let source = BazelSource::new(&db, BazelRepository::new(&db, root), file);
    let admission = admit_bazel_source(&db, source);
    assert_eq!(admitted(admission)?.suite().len(), 2);
    Ok(())
}

#[test]
fn rejects_annotations_in_the_stable_bazel_profile() -> anyhow::Result<()> {
    let (db, root) = test_db(&[
        ("MODULE.bazel", ""),
        ("pkg/BUILD.bazel", ""),
        (
            "pkg/defs.bzl",
            "def keep_int(value: int) -> int:\n    return value\n",
        ),
    ])?;
    let file = system_path_to_file(&db, root.join("pkg/defs.bzl"))?;
    let source = BazelSource::new(&db, BazelRepository::new(&db, root), file);
    assert!(matches!(
        opaque(admit_bazel_source(&db, source))?.reason(),
        BazelAdmissionError::BazelSyntax(_)
    ));
    Ok(())
}

#[test]
fn admits_only_syntactically_placed_plain_loads() -> anyhow::Result<()> {
    let (db, root) = test_db(&[
        ("MODULE.bazel", ""),
        ("pkg/BUILD.bazel", ""),
        (
            "pkg/defs.bzl",
            "\"\"\"Module docs.\"\"\"\nload(\":other.bzl\", \"x\", alias=\"y\")\n\ndef public():\n    return x\n",
        ),
    ])?;
    let file = system_path_to_file(&db, root.join("pkg/defs.bzl"))?;
    let source = BazelSource::new(&db, BazelRepository::new(&db, root), file);
    assert_eq!(admitted(admit_bazel_source(&db, source))?.suite().len(), 3);
    Ok(())
}

#[test]
fn requires_selected_root_package_and_source_ownership() -> anyhow::Result<()> {
    let (mut db, root) = test_db(&[
        ("pkg/defs.bzl", "RESULT = 1\n"),
        ("pkg/sub/MODULE.bazel", ""),
        ("pkg/sub/BUILD.bazel", ""),
        ("pkg/sub/defs.bzl", "RESULT = 2\n"),
        ("pkg/sub/defs.star", "RESULT = 3\n"),
    ])?;
    let file = system_path_to_file(&db, root.join("pkg/defs.bzl"))?;
    let outer = BazelRepository::new(&db, root.clone());
    let source = BazelSource::new(&db, outer, file);
    assert!(matches!(
        opaque(admit_bazel_source(&db, source))?.reason(),
        BazelAdmissionError::InvalidSource(BazelLoadError::InvalidRepository)
    ));

    db.write_file(root.join("MODULE.bazel"), "")?;
    let source = BazelSource::new(&db, BazelRepository::new(&db, root.clone()), file);
    assert!(matches!(
        opaque(admit_bazel_source(&db, source))?.reason(),
        BazelAdmissionError::InvalidSource(BazelLoadError::ImporterOutsidePackage)
    ));
    db.write_file(root.join("pkg/BUILD"), "")?;
    let source = BazelSource::new(&db, BazelRepository::new(&db, root.clone()), file);
    assert_eq!(admitted(admit_bazel_source(&db, source))?.suite().len(), 1);

    let nested_root = root.join("pkg/sub");
    let nested_file = system_path_to_file(&db, nested_root.join("defs.bzl"))?;
    let source = BazelSource::new(&db, BazelRepository::new(&db, root), nested_file);
    assert!(matches!(
        opaque(admit_bazel_source(&db, source))?.reason(),
        BazelAdmissionError::InvalidSource(BazelLoadError::ImporterOutsideRepository)
    ));
    let source = BazelSource::new(
        &db,
        BazelRepository::new(&db, nested_root.clone()),
        nested_file,
    );
    assert_eq!(admitted(admit_bazel_source(&db, source))?.suite().len(), 1);

    let star = system_path_to_file(&db, nested_root.join("defs.star"))?;
    let source = BazelSource::new(&db, BazelRepository::new(&db, nested_root), star);
    assert!(matches!(
        opaque(admit_bazel_source(&db, source))?.reason(),
        BazelAdmissionError::InvalidSource(BazelLoadError::InvalidImporter)
    ));
    Ok(())
}

#[test]
fn rejects_python_only_forms_before_exposing_any_export() -> anyhow::Result<()> {
    let (mut db, root) = test_db(&[
        ("WORKSPACE.bazel", ""),
        ("pkg/BUILD", ""),
        (
            "pkg/defs.bzl",
            "class PythonOnly:\n    pass\n\ndef public() -> int:\n    return 1\n",
        ),
    ])?;
    let path = root.join("pkg/defs.bzl");
    let file = system_path_to_file(&db, &path)?;
    let source = BazelSource::new(&db, BazelRepository::new(&db, root.clone()), file);
    let failure = opaque(admit_bazel_source(&db, source))?;
    assert!(matches!(
        failure.reason(),
        BazelAdmissionError::BazelSyntax("class definitions")
    ));
    assert_eq!(failure.file(), file);
    assert_eq!(
        failure.range().map(|range| range.start().to_usize()),
        Some(0)
    );
    let diagnostic = failure
        .diagnostic()
        .ok_or(anyhow::anyhow!("missing syntax diagnostic"))?;
    assert_eq!(diagnostic.id(), DiagnosticId::InvalidSyntax);
    assert_eq!(diagnostic.severity(), Severity::Error);
    assert_eq!(
        diagnostic.primary_span().map(|span| span.expect_ty_file()),
        Some(file)
    );
    assert_eq!(diagnostic.range(), failure.range());

    db.write_file(&path, "def public():\n    return 1\n")?;
    let source = BazelSource::new(&db, BazelRepository::new(&db, root), file);
    assert_eq!(admitted(admit_bazel_source(&db, source))?.suite().len(), 1);
    Ok(())
}

#[test]
fn parser_recovery_cannot_admit_otherwise_valid_exports() -> anyhow::Result<()> {
    let (db, root) = test_db(&[
        ("REPO.bazel", ""),
        ("pkg/BUILD", ""),
        (
            "pkg/defs.bzl",
            "def broken(:\n    pass\n\ndef public() -> int:\n    return 1\n",
        ),
    ])?;
    let file = system_path_to_file(&db, root.join("pkg/defs.bzl"))?;
    let source = BazelSource::new(&db, BazelRepository::new(&db, root), file);
    let failure = opaque(admit_bazel_source(&db, source))?;
    assert!(matches!(
        failure.reason(),
        BazelAdmissionError::PythonParser(_)
    ));
    assert_eq!(failure.file(), file);
    assert!(failure.range().is_some());
    assert!(failure.diagnostic().is_none());
    Ok(())
}

#[test]
fn valid_mixed_order_starlark_load_is_opaque_with_shared_parser() -> anyhow::Result<()> {
    let (db, root) = test_db(&[
        ("MODULE.bazel", ""),
        ("pkg/BUILD", ""),
        (
            "pkg/defs.bzl",
            "load(\":defs.bzl\", \"x\", alias=\"y\", \"z\")\n\ndef public() -> int:\n    return 1\n",
        ),
    ])?;
    let file = system_path_to_file(&db, root.join("pkg/defs.bzl"))?;
    let source = BazelSource::new(&db, BazelRepository::new(&db, root), file);
    let failure = opaque(admit_bazel_source(&db, source))?;
    assert!(matches!(
        failure.reason(),
        BazelAdmissionError::PythonParser(_)
    ));
    assert!(
        failure
            .reason()
            .to_string()
            .contains("shared Python parser")
    );
    assert_eq!(failure.file(), file);
    assert!(failure.range().is_some());
    assert!(failure.diagnostic().is_none());
    Ok(())
}

#[test]
fn nested_and_late_loads_taint_every_export() -> anyhow::Result<()> {
    for (code, reason) in [
        (
            "def internal():\n    load(\":defs.bzl\", \"symbol\")\n\ndef public():\n    return 1\n",
            "load statements outside the top-level load prefix",
        ),
        (
            "RESULT = 1\nload(\":defs.bzl\", \"symbol\")\n\ndef public():\n    return 1\n",
            "load statements after other top-level statements",
        ),
        (
            "RESULT = load(\":defs.bzl\", \"symbol\")\n\ndef public():\n    return 1\n",
            "load statements outside the top-level load prefix",
        ),
        (
            "\"Module doc\"\nload(\":defs.bzl\", \"x\")\n\"another string\"\nload(\":defs.bzl\", \"y\")\n",
            "load statements after other top-level statements",
        ),
    ] {
        let (db, root) = test_db(&[
            ("MODULE.bazel", ""),
            ("pkg/BUILD", ""),
            ("pkg/defs.bzl", code),
        ])?;
        let file = system_path_to_file(&db, root.join("pkg/defs.bzl"))?;
        let source = BazelSource::new(&db, BazelRepository::new(&db, root), file);
        let failure = opaque(admit_bazel_source(&db, source))?;
        assert!(
            matches!(failure.reason(), BazelAdmissionError::BazelSyntax(found) if *found == reason),
            "expected {reason}, found {:?}",
            failure.reason()
        );
        assert_eq!(failure.file(), file);
        assert!(failure.range().is_some());
    }
    Ok(())
}

#[test]
fn reserved_load_bindings_and_dynamic_load_arguments_taint_source() -> anyhow::Result<()> {
    for (code, reason) in [
        (
            "load = 1\n\ndef public():\n    return 1\n",
            "rebinding the reserved load name",
        ),
        (
            "def load():\n    pass\n\ndef public():\n    return 1\n",
            "rebinding the reserved load name",
        ),
        (
            "RESULT = lambda load: 1\n\ndef public():\n    return 1\n",
            "rebinding the reserved load name",
        ),
        (
            "RESULT = f(load=1)\n\ndef public():\n    return 1\n",
            "the reserved load name as a keyword argument",
        ),
        (
            "RESULT = load\n\ndef public():\n    return 1\n",
            "using the reserved load name as an identifier",
        ),
        (
            "load(\":defs.bzl\", symbol)\n\ndef public():\n    return 1\n",
            "load arguments other than literal strings",
        ),
    ] {
        let (db, root) = test_db(&[("WORKSPACE", ""), ("pkg/BUILD", ""), ("pkg/defs.bzl", code)])?;
        let file = system_path_to_file(&db, root.join("pkg/defs.bzl"))?;
        let source = BazelSource::new(&db, BazelRepository::new(&db, root), file);
        let failure = opaque(admit_bazel_source(&db, source))?;
        assert!(
            matches!(failure.reason(), BazelAdmissionError::BazelSyntax(found) if *found == reason),
            "expected {reason}, found {:?}",
            failure.reason()
        );
    }
    Ok(())
}

#[test]
fn fixed_parser_version_rejects_new_python_syntax() -> anyhow::Result<()> {
    let (db, root) = test_db(&[
        ("MODULE.bazel", ""),
        ("pkg/BUILD", ""),
        (
            "pkg/defs.bzl",
            "def public[T](value: T) -> T:\n    return value\n",
        ),
    ])?;
    let file = system_path_to_file(&db, root.join("pkg/defs.bzl"))?;
    let source = BazelSource::new(&db, BazelRepository::new(&db, root), file);
    let failure = opaque(admit_bazel_source(&db, source))?;
    assert!(matches!(
        failure.reason(),
        BazelAdmissionError::PythonVersion(_)
    ));
    assert_eq!(failure.file(), file);
    assert!(failure.range().is_some());
    assert!(failure.diagnostic().is_none());
    Ok(())
}

#[test]
fn excludes_python_control_flow_and_expressions_anywhere() -> anyhow::Result<()> {
    for (code, reason) in [
        ("if True:\n    RESULT = 1\n", "top-level if statements"),
        ("for x in []:\n    RESULT = x\n", "top-level for statements"),
        ("def f():\n    return 1 < 2 < 3\n", "chained comparisons"),
        (
            "def f(value):\n    return value is None\n",
            "Python identity comparisons",
        ),
        ("def f():\n    return 1e999\n", "non-finite float literals"),
        (
            "def f(value):\n    return value.load\n",
            "the reserved load name as an attribute",
        ),
        ("x = y = 1\n", "chained assignments"),
        ("x = b'bytes'\n", "byte strings"),
        (
            "x = [*values]\n",
            "starred assignment or collection expressions",
        ),
        ("x = {**values}\n", "dictionary unpacking"),
        ("x = 2 ** 3\n", "exponentiation or matrix multiplication"),
        ("x = 2 @ 3\n", "exponentiation or matrix multiplication"),
        ("x[1:] = []\n", "slice assignment"),
        ("x = y[1:, 2]\n", "multidimensional slices"),
        ("return 1\n", "top-level return statements"),
        ("def f():\n    break\n", "loop control outside a for loop"),
        (
            "def f():\n    for x in []:\n        def g():\n            continue\n",
            "loop control outside a for loop",
        ),
        (
            "def f(x, /):\n    return x\n",
            "positional-only parameter separators",
        ),
        (
            "f(*x, y=1)\n",
            "this call argument order or repeated unpacking",
        ),
        (
            "f(*x, *y)\n",
            "this call argument order or repeated unpacking",
        ),
        (
            "f(x=1, x=2)\n",
            "this call argument order or repeated unpacking",
        ),
        (
            "f = lambda x,: x\n",
            "lambda parameters with a trailing comma",
        ),
        ("RESULT: int = 1\n", "annotated variable assignments"),
        ("RESULT = 1,\n", "unparenthesized singleton tuples"),
        (
            "RESULT = 1, 2,\n",
            "unparenthesized tuples with trailing commas",
        ),
        (
            "RESULT = 1, (2),\n",
            "unparenthesized tuples with trailing commas",
        ),
    ] {
        let (db, root) = test_db(&[("WORKSPACE", ""), ("pkg/BUILD", ""), ("pkg/defs.bzl", code)])?;
        let file = system_path_to_file(&db, root.join("pkg/defs.bzl"))?;
        let source = BazelSource::new(&db, BazelRepository::new(&db, root), file);
        let failure = opaque(admit_bazel_source(&db, source))?;
        assert!(
            matches!(failure.reason(), BazelAdmissionError::BazelSyntax(found) if *found == reason),
            "expected {reason}, found {:?}",
            failure.reason()
        );
        assert_eq!(failure.file(), file);
        assert!(failure.range().is_some());
    }
    Ok(())
}

#[test]
fn accepts_parenthesized_trailing_comma_and_bare_pair() -> anyhow::Result<()> {
    for code in [
        "RESULT = [x for x, in [(1,)]]\n",
        "def f():\n    for x, in [(1,)]:\n        pass\n",
        "RESULT = 3.14\n",
        "RESULT = values[1, 2]\n",
        "RESULT = lambda *, x=1: x\n",
        "RESULT = f(1, x=2, *args, **kwargs)\n",
        "def outer():\n    def inner():\n        return 1\n    return inner\n",
        "RESULT = (1,)\n",
        "RESULT = (1, 2,)\n",
        "RESULT = 1, 2\n",
        "RESULT = 1, (2)\n",
    ] {
        let (db, root) = test_db(&[
            ("MODULE.bazel", ""),
            ("pkg/BUILD", ""),
            ("pkg/defs.bzl", code),
        ])?;
        let file = system_path_to_file(&db, root.join("pkg/defs.bzl"))?;
        let source = BazelSource::new(&db, BazelRepository::new(&db, root), file);
        assert_eq!(
            admitted(admit_bazel_source(&db, source))?.suite().len(),
            1,
            "{code}"
        );
    }
    Ok(())
}

#[test]
fn rejects_python_literals_and_indentation_unrecognized_by_bazel_9() -> anyhow::Result<()> {
    for (code, reason, site) in [
        (
            "BAD = \"\\x41\"\nGOOD = 1\n",
            "string escapes not recognized by Bazel 9",
            "\\x41",
        ),
        (
            "BAD = \"\\u0041\"\nGOOD = 1\n",
            "string escapes not recognized by Bazel 9",
            "\\u0041",
        ),
        (
            "# A UTF-8 comment: π\nBAD = \"\\x41\"\nGOOD = 1\n",
            "string escapes not recognized by Bazel 9",
            "\\x41",
        ),
        (
            "BAD = \"\\400\"\nGOOD = 1\n",
            "string escapes not recognized by Bazel 9",
            "\\400",
        ),
        (
            "BAD = 1_0\nGOOD = 1\n",
            "numeric separators not recognized by Bazel 9",
            "1_0",
        ),
        (
            "BAD = 0xA_B\nGOOD = 1\n",
            "numeric separators not recognized by Bazel 9",
            "0xA_B",
        ),
        (
            "BAD = R\"\\x41\"\nGOOD = 1\n",
            "uppercase raw-string prefixes",
            "R\"",
        ),
        (
            "def broken():\n\treturn 1\nGOOD = 1\n",
            "tabs used for Bazel indentation",
            "\t",
        ),
        (
            "GOOD = 1\n\t# Leading whitespace before a comment\n",
            "tabs used for Bazel indentation",
            "\t",
        ),
    ] {
        // Each form parses as Python; the Bazel gate must independently
        // reject it before another binding can contribute a checked type.
        let parsed = parse_unchecked(
            code,
            ParseOptions::from(Mode::Module).with_target_version(PythonVersion::PY310),
        );
        let module = parsed
            .try_into_module()
            .ok_or(anyhow::anyhow!("shared parser did not parse: {code:?}"))?;
        assert!(module.errors().is_empty(), "{code}: {:?}", module.errors());
        let (db, root) = test_db(&[
            ("MODULE.bazel", ""),
            ("pkg/BUILD", ""),
            ("pkg/defs.bzl", code),
        ])?;
        let file = system_path_to_file(&db, root.join("pkg/defs.bzl"))?;
        let source = BazelSource::new(&db, BazelRepository::new(&db, root), file);
        let failure = opaque(admit_bazel_source(&db, source))?;
        assert!(
            matches!(failure.reason(), BazelAdmissionError::BazelSyntax(found) if *found == reason),
            "{code}: {:?}",
            failure.reason()
        );
        assert_eq!(failure.file(), file);
        assert_eq!(
            failure.range().map(|range| range.start().to_usize()),
            code.find(site),
            "{code}"
        );
        let diagnostic = failure.diagnostic().ok_or(anyhow::anyhow!(
            "missing Bazel syntax diagnostic for {code}"
        ))?;
        assert_eq!(diagnostic.id(), DiagnosticId::InvalidSyntax);
        assert_eq!(diagnostic.range(), failure.range());
    }
    Ok(())
}

#[test]
fn rejects_unicode_identifiers_even_when_python_admits_them() -> anyhow::Result<()> {
    for (code, site) in [
        ("def café():\n    return 1\nGOOD = 1\n", "café"),
        ("def 𝒞():\n    return 1\nGOOD = 1\n", "𝒞"),
        ("def public(café):\n    return café\nGOOD = 1\n", "café"),
        ("café = 1\nGOOD = 1\n", "café"),
        ("𝒞 = 1\nGOOD = 1\n", "𝒞"),
        ("def public():\n    return café\nGOOD = 1\n", "café"),
        ("def public(obj):\n    return obj.café\nGOOD = 1\n", "café"),
        ("load(\":defs.bzl\", café=\"public\")\nGOOD = 1\n", "café"),
        ("load(\":defs.bzl\", 𝒞=\"public\")\nGOOD = 1\n", "𝒞"),
    ] {
        let module = parse_unchecked(
            code,
            ParseOptions::from(Mode::Module).with_target_version(PythonVersion::PY310),
        )
        .try_into_module()
        .ok_or(anyhow::anyhow!("shared parser did not parse: {code:?}"))?;
        assert!(module.errors().is_empty(), "{code}: {:?}", module.errors());

        let (db, root) = test_db(&[
            ("MODULE.bazel", ""),
            ("pkg/BUILD", ""),
            ("pkg/defs.bzl", code),
        ])?;
        let file = system_path_to_file(&db, root.join("pkg/defs.bzl"))?;
        let source = BazelSource::new(&db, BazelRepository::new(&db, root), file);
        let failure = opaque(admit_bazel_source(&db, source))?;
        assert!(
            matches!(
                failure.reason(),
                BazelAdmissionError::BazelSyntax("identifiers not recognized by Bazel 9")
            ),
            "{code}: {:?}",
            failure.reason()
        );
        assert_eq!(
            failure.range().map(|range| range.start().to_usize()),
            code.find(site)
        );
        assert_eq!(
            failure.range().map(|range| range.len().to_usize()),
            Some(site.len()),
            "{code}"
        );
    }
    Ok(())
}

#[test]
fn keeps_unicode_strings_and_comments_without_unicode_identifiers() -> anyhow::Result<()> {
    let (db, root) = test_db(&[
        ("MODULE.bazel", ""),
        ("pkg/BUILD", ""),
        (
            "pkg/defs.bzl",
            "# Legitimate Unicode comment: π\nGOOD = \"café\"\n",
        ),
    ])?;
    let file = system_path_to_file(&db, root.join("pkg/defs.bzl"))?;
    let source = BazelSource::new(&db, BazelRepository::new(&db, root), file);
    assert!(matches!(
        admit_bazel_source(&db, source),
        BazelSourceAdmission::Admitted(_)
    ));
    Ok(())
}

#[test]
fn admits_bazel_9_raw_strings_escapes_and_nonindentation_tabs() -> anyhow::Result<()> {
    for code in [
        "VALUE = r\"\\x41\"\nGOOD = 1\n",
        "VALUE = r\"quoted\\\"\"\nGOOD = 1\n",
        "VALUE = r\"one\\\n two\"\nGOOD = 1\n",
        "VALUE = \"\\\\x41\"\nGOOD = 1\n",
        "VALUE = \"\\n\\07\"\nGOOD = 1\n",
        "VALUE = 0xAB\nGOOD = 1\n",
        "VALUE = 1 #\tComment contents\nGOOD = 1\n",
        "VALUE = 1 # \\x41 is comment text\nGOOD = 1\n",
        "VALUE = \"\"\"one\n\tinside a string\n\"\"\"\nGOOD = 1\n",
        "VALUE = \"\"\"one\ntwo\"\"\"\t# trailing comment\nGOOD = 1\n",
        "VALUE = \"\"\"one\r\ntwo\"\"\"\t# trailing comment\r\nGOOD = 1\r\n",
        "VALUE = (\n\t1\n)\nGOOD = 1\n",
        "VALUE = 1\\\n\t+ 2\nGOOD = 1\n",
    ] {
        let (db, root) = test_db(&[
            ("MODULE.bazel", ""),
            ("pkg/BUILD", ""),
            ("pkg/defs.bzl", code),
        ])?;
        let file = system_path_to_file(&db, root.join("pkg/defs.bzl"))?;
        let source = BazelSource::new(&db, BazelRepository::new(&db, root), file);
        assert_eq!(
            admitted(admit_bazel_source(&db, source))?.suite().len(),
            2,
            "{code}"
        );
    }
    Ok(())
}

#[test]
fn docstring_trailing_tabs_leave_the_whole_source_ready() -> anyhow::Result<()> {
    for code in [
        "\"\"\"Module docs\"\"\"\t# trailing comment\nGOOD = 1\n",
        "\"\"\"Module docs\nsecond line\"\"\"\t# trailing comment\nGOOD = 1\n",
    ] {
        let (db, root) = test_db(&[
            ("MODULE.bazel", ""),
            ("pkg/BUILD", ""),
            ("pkg/defs.bzl", code),
        ])?;
        let file = system_path_to_file(&db, root.join("pkg/defs.bzl"))?;
        let source = BazelSource::new(&db, BazelRepository::new(&db, root), file);
        assert_eq!(admitted(admit_bazel_source(&db, source))?.suite().len(), 2);
    }
    Ok(())
}

#[test]
fn lexical_changes_revalidate_the_same_bazel_source_key() -> anyhow::Result<()> {
    let (mut db, root) = test_db(&[
        ("MODULE.bazel", ""),
        ("pkg/BUILD", ""),
        ("pkg/defs.bzl", "GOOD = 1\n"),
    ])?;
    let path = root.join("pkg/defs.bzl");
    let file = system_path_to_file(&db, &path)?;
    let source = BazelSource::new(&db, BazelRepository::new(&db, root.clone()), file);
    assert_eq!(admitted(admit_bazel_source(&db, source))?.suite().len(), 1);

    db.write_file(&path, "BAD = 1_0\nGOOD = 1\n")?;
    let source = BazelSource::new(&db, BazelRepository::new(&db, root.clone()), file);
    let failure = opaque(admit_bazel_source(&db, source))?;
    assert!(matches!(
        failure.reason(),
        BazelAdmissionError::BazelSyntax("numeric separators not recognized by Bazel 9")
    ));

    db.write_file(&path, "GOOD = 1\n")?;
    let source = BazelSource::new(&db, BazelRepository::new(&db, root), file);
    assert_eq!(admitted(admit_bazel_source(&db, source))?.suite().len(), 1);
    Ok(())
}

#[test]
fn read_errors_keep_the_source_opaque_without_a_syntax_span() -> anyhow::Result<()> {
    let (mut db, root) = test_db(&[
        ("MODULE.bazel", ""),
        ("pkg/BUILD", ""),
        ("pkg/defs.bzl", "RESULT = 1\n"),
    ])?;
    let path = root.join("pkg/defs.bzl");
    let file = system_path_to_file(&db, &path)?;
    db.memory_file_system().remove_file(&path)?;
    File::sync_path(&mut db, &path);
    let source = BazelSource::new(&db, BazelRepository::new(&db, root), file);
    let failure = opaque(admit_bazel_source(&db, source))?;
    assert!(matches!(failure.reason(), BazelAdmissionError::Read(_)));
    assert_eq!(failure.range(), None);
    let diagnostic = failure
        .diagnostic()
        .ok_or(anyhow::anyhow!("missing read diagnostic"))?;
    assert_eq!(diagnostic.id(), DiagnosticId::Io);
    assert_eq!(diagnostic.range(), None);
    assert_eq!(
        diagnostic.primary_span().map(|span| span.expect_ty_file()),
        Some(file)
    );
    Ok(())
}
