use anyhow::Context as _;
use ruff_db::diagnostic::{Annotation, Diagnostic, Span, UnifiedFile};
use ruff_db::files::system_path_to_file;
use ruff_text_size::{TextRange, TextSize};

use crate::testing::{TestDb, test_db};

use super::{
    StarCheck, StarDirectLoad, StarFailureReason, StarHostFunction, StarHostParam, StarHostProfile,
    StarIntrinsic, StarLoadBinding, StarModule, StarResolvedGraph, StarSource, StarSpecialForm,
    check_star_graph,
};

const LABEL: &str = "//example:limits.star";
const DECLARATION: &str = "def validate(value):\n    pass\n\nLimitConfig = wrapper_record(validate, max_connections=int)\n";

fn span(text: &str, needle: &str) -> anyhow::Result<TextRange> {
    let start = text
        .find(needle)
        .with_context(|| format!("missing {needle:?} in test source"))?;
    let start = TextSize::new(u32::try_from(start)?);
    let end = start + TextSize::new(u32::try_from(needle.len())?);
    Ok(TextRange::new(start, end))
}

fn slice(text: &str, range: TextRange) -> Option<&str> {
    text.get(range.start().to_usize()..range.end().to_usize())
}

fn profile() -> StarHostProfile {
    StarHostProfile {
        name: "example-star-host-v3".to_string(),
        special_forms: Box::new([
            StarSpecialForm {
                name: "record".to_string(),
                kind: "builtin_record".to_string(),
                validator: "none".to_string(),
                field_types: "named_keyword_type_expressions".to_string(),
            },
            StarSpecialForm {
                name: "wrapper_record".to_string(),
                kind: "record_with_validator".to_string(),
                validator: "first_positional_callable".to_string(),
                field_types: "named_keyword_type_expressions".to_string(),
            },
        ]),
        intrinsics: Box::new([
            StarIntrinsic {
                name: "field".to_string(),
                kind: "field_first_type_optional_default".to_string(),
            },
            StarIntrinsic {
                name: "struct".to_string(),
                kind: "struct_named_members".to_string(),
            },
        ]),
        host_functions: Box::new([]),
    }
}

fn v3_profile() -> StarHostProfile {
    let mut host = profile();
    host.host_functions = Box::new([example_host_function("host_encode")]);
    host
}

fn example_host_function(name: &str) -> StarHostFunction {
    StarHostFunction {
        name: name.to_string(),
        params: Box::new([example_host_param("value", "pos_or_named", true)]),
        returns: "str".to_string(),
        availability: "any_module".to_string(),
    }
}

fn example_host_param(name: &str, mode: &str, required: bool) -> StarHostParam {
    StarHostParam {
        name: name.to_string(),
        mode: mode.to_string(),
        required,
        ty: "str".to_string(),
    }
}

fn native_profile() -> StarHostProfile {
    let mut host = v3_profile();
    let mut encode = example_host_function("host_encode");
    let mut value = example_host_param("value", "pos_or_named", true);
    value.ty = "any".to_string();
    let mut sort_keys = example_host_param("sort_keys", "named_only", false);
    sort_keys.ty = "bool".to_string();
    encode.params = Box::new([value, sort_keys]);
    let hash = example_host_function("host_hash");
    let mut catalog = example_host_function("host_catalog");
    let mut decoder = example_host_param("decoder", "named_only", true);
    decoder.ty = "callable".to_string();
    catalog.params = Box::new([example_host_param("name", "pos_or_named", true), decoder]);
    catalog.returns = "any".to_string();
    catalog.availability = "loaded_module_initialization".to_string();
    let mut modes = example_host_function("host_modes");
    let mut count = example_host_param("count", "pos_or_named", true);
    count.ty = "int".to_string();
    let mut enabled = example_host_param("enabled", "named_only", false);
    enabled.ty = "bool".to_string();
    modes.params = Box::new([example_host_param("base", "pos_only", true), count, enabled]);
    host.host_functions = Box::new([encode, hash, catalog, modes]);
    host
}

fn case(root_source: &str, module_source: &str) -> anyhow::Result<(TestDb, StarResolvedGraph)> {
    let (db, root) = test_db(&[("root.star", root_source), ("limits.star", module_source)])?;
    let root_file = system_path_to_file(&db, root.join("root.star"))?;
    let module_file = system_path_to_file(&db, root.join("limits.star"))?;
    let label_range = span(root_source, &format!("\"{LABEL}\""))?;
    let graph = StarResolvedGraph {
        version: "sty-star-graph-v3".to_string(),
        profile: profile(),
        root: StarSource {
            file: root_file,
            text: root_source.to_string(),
            loads: Box::new([StarDirectLoad {
                module_id: LABEL.to_string(),
                label_range,
                bindings: Box::new([StarLoadBinding {
                    local: "LimitConfig".to_string(),
                    source: "LimitConfig".to_string(),
                }]),
            }]),
        },
        modules: Box::new([StarModule {
            id: LABEL.to_string(),
            source: StarSource {
                file: module_file,
                text: module_source.to_string(),
                loads: Box::new([]),
            },
        }]),
    };
    Ok((db, graph))
}

fn root_only(root_source: &str) -> anyhow::Result<(TestDb, StarResolvedGraph)> {
    let (db, root) = test_db(&[("root.star", root_source)])?;
    let file = system_path_to_file(&db, root.join("root.star"))?;
    Ok((
        db,
        StarResolvedGraph {
            version: "sty-star-graph-v3".to_string(),
            profile: profile(),
            root: StarSource {
                file,
                text: root_source.to_string(),
                loads: Box::new([]),
            },
            modules: Box::new([]),
        },
    ))
}

fn v3_root_only(root_source: &str) -> anyhow::Result<(TestDb, StarResolvedGraph)> {
    let (db, mut graph) = root_only(root_source)?;
    graph.profile = native_profile();
    Ok((db, graph))
}

fn profile_failure(db: &TestDb, graph: &StarResolvedGraph) -> anyhow::Result<()> {
    let StarCheck::Opaque(failure) = check_star_graph(db, graph)? else {
        anyhow::bail!("invalid host profile unexpectedly established source types");
    };
    assert!(matches!(failure.reason(), StarFailureReason::Profile));
    assert_eq!(failure.file(), graph.root.file);
    Ok(())
}

fn checked(db: &TestDb, graph: &StarResolvedGraph) -> anyhow::Result<Vec<Diagnostic>> {
    match check_star_graph(db, graph)? {
        StarCheck::Checked(diagnostics) => Ok(diagnostics),
        StarCheck::Opaque(failure) => anyhow::bail!("graph rejected: {failure:?}"),
    }
}

fn codes(diagnostics: &[Diagnostic]) -> Vec<String> {
    diagnostics
        .iter()
        .map(|diagnostic| diagnostic.id().to_string())
        .collect()
}

#[test]
fn builtin_contracts_accept_starlark_calls_and_annotations() -> anyhow::Result<()> {
    let (db, graph) = root_only(
        r#"
def clone(value: dict[str, int] | list[tuple[str, int]]) -> dict[str, int]:
    return dict(value)
def merged(left: dict[str, int], right: dict[str, int]) -> dict[str, int]:
    return left | right
def less(left: str, right: str) -> bool:
    return left < right
dict({"x": 1})
dict([("x", 1)])
"a b".split(None, None)
"abc".startswith("a", None, None)
"abc".endswith("c", None, None)
" x ".strip()
"aba".replace("a", "b")
sorted([1], key=lambda value: value)
def annotation(value: typing.Iterable[int], callback: typing.Callable[[int], str]) -> typing.Any:
    return callback(1)
def never() -> typing.Never:
    fail("stop")
isinstance([1], list[int])
isinstance((1, "ok"), (int, str))
isinstance(1, typing.Any)
Item = record(value=int)
def factory() -> (type, struct):
    return (Item, struct())
Result, namespace = factory()
Result(value=1)
Result.values()
def accepts(value: Result):
    return value
def collect(*values: tuple[str, ...]) -> tuple[str, ...]:
    return values
collect("one", "two")
def keywords(**values: dict[str, int]) -> dict[str, int]:
    return values
keywords(one=1, two=2)
"#,
    )?;
    let diagnostics = checked(&db, &graph)?;
    assert!(diagnostics.is_empty(), "{diagnostics:?}");
    Ok(())
}

#[test]
fn builtin_contracts_reject_python_only_arguments_and_typing_members() -> anyhow::Result<()> {
    let (db, graph) = root_only(
        r#"
"a b".split(sep=" ")
" x ".strip(chars=" ")
"abc".startswith(prefix="a")
"abc".endswith(suffix="c")
"aba".replace(old="a", new="b")
" x ".strip(None)
"aba".replace("a", "b", None)
sorted([1], key=None)
typing.Protocol
typing.overload
"#,
    )?;
    let diagnostics = checked(&db, &graph)?;
    let mut actual = codes(&diagnostics);
    actual.sort();
    assert_eq!(
        actual,
        [
            "invalid-argument-type",
            "invalid-argument-type",
            "invalid-argument-type",
            "positional-only-parameter-as-kwarg",
            "positional-only-parameter-as-kwarg",
            "positional-only-parameter-as-kwarg",
            "positional-only-parameter-as-kwarg",
            "positional-only-parameter-as-kwarg",
            "positional-only-parameter-as-kwarg",
            "unresolved-attribute",
            "unresolved-attribute"
        ],
        "{diagnostics:?}"
    );
    Ok(())
}

fn annotations(diagnostic: &Diagnostic) -> impl Iterator<Item = &Annotation> {
    diagnostic.annotations().iter().chain(
        diagnostic
            .sub_diagnostics()
            .iter()
            .flat_map(ruff_db::diagnostic::SubDiagnostic::annotations),
    )
}

fn captured_slice(span: &Span) -> Option<&str> {
    let UnifiedFile::Ruff(source) = span.file() else {
        return None;
    };
    slice(source.source_text(), span.range()?)
}

#[test]
fn loaded_record_errors_own_captured_argument_and_declaration_sources() -> anyhow::Result<()> {
    let source = format!(
        "load(\"{LABEL}\", \"LimitConfig\")\nif False:\n    LimitConfig(max_connections=\"wrong\")\n"
    );
    let (db, graph) = case(&source, DECLARATION)?;
    let diagnostics = checked(&db, &graph)?;
    let [diagnostic] = diagnostics.as_slice() else {
        anyhow::bail!("expected one loaded record error: {diagnostics:?}");
    };
    assert_eq!(diagnostic.id().to_string(), "invalid-argument-type");
    assert_eq!(
        captured_slice(&diagnostic.primary_span().context("argument span")?),
        Some("max_connections=\"wrong\"")
    );
    assert!(
        annotations(diagnostic)
            .all(|annotation| matches!(annotation.get_span().file(), UnifiedFile::Ruff(_)))
    );
    assert!(
        annotations(diagnostic).any(|annotation| {
            let span = annotation.get_span();
            let UnifiedFile::Ruff(source) = span.file() else {
                return false;
            };
            source.name().ends_with("limits.star") && captured_slice(span) == Some("int")
        }),
        "{diagnostic:?}"
    );
    Ok(())
}

#[test]
fn empty_host_inventory_still_checks_function_bodies_and_calls() -> anyhow::Result<()> {
    let (db, graph) =
        root_only("def choose(flag: bool) -> int:\n    return \"wrong\"\nchoose(1)\n")?;
    let diagnostics = checked(&db, &graph)?;
    assert_eq!(
        codes(&diagnostics),
        ["invalid-return-type", "invalid-argument-type"],
        "{diagnostics:?}"
    );
    assert!(diagnostics.iter().any(|diagnostic| {
        annotations(diagnostic)
            .any(|annotation| captured_slice(annotation.get_span()) == Some("flag: bool"))
    }));
    Ok(())
}

#[test]
fn host_facts_supply_signature_modes_types_and_availability() -> anyhow::Result<()> {
    let (db, graph) = v3_root_only(
        "host_hash(1)\nhost_encode(\"ok\", sort_keys=1)\nhost_modes(\"ok\", True)\nhost_modes(\"ok\")\ndef decoder(value):\n    return value\nhost_catalog(\"catalog\", decoder=decoder)\n",
    )?;
    let diagnostics = checked(&db, &graph)?;
    let mut actual = codes(&diagnostics);
    actual.sort();
    assert_eq!(
        actual,
        [
            "invalid-argument-type",
            "invalid-argument-type",
            "invalid-argument-type",
            "missing-argument",
            "unavailable-host-function"
        ],
        "{diagnostics:?}"
    );
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic
            .sub_diagnostics()
            .iter()
            .any(|sub| sub.headline_message().contains("Host signature: host_hash"))
    }));
    Ok(())
}

#[test]
fn builtin_declarations_supply_collections_and_starlark_conversions() -> anyhow::Result<()> {
    let (db, graph) = root_only(
        "Item = record(values=list[str], choice=int | str)\nItem(values=[\"ok\"], choice=1)\nItem(values=[1], choice=True)\ndef name(value: typing.Any) -> str:\n    return type(value)\nvalues = sorted([\"a\", \"b\"])\nItem(values=values, choice=\"ok\")\nfor char in \"abc\".elems():\n    Item(values=[char], choice=\"ok\")\n",
    )?;
    let diagnostics = checked(&db, &graph)?;
    assert_eq!(
        codes(&diagnostics),
        ["invalid-argument-type", "invalid-argument-type"],
        "{diagnostics:?}"
    );
    Ok(())
}

#[test]
fn embedded_builtin_locations_are_captured_without_database_handles() -> anyhow::Result<()> {
    let (db, graph) = root_only("len(1)\n")?;
    let diagnostics = checked(&db, &graph)?;
    assert_eq!(
        codes(&diagnostics),
        ["invalid-argument-type"],
        "{diagnostics:?}"
    );
    assert!(
        diagnostics
            .iter()
            .flat_map(annotations)
            .all(|annotation| matches!(annotation.get_span().file(), UnifiedFile::Ruff(_)))
    );
    assert!(
        diagnostics.iter().flat_map(annotations).any(|annotation| {
            let UnifiedFile::Ruff(source) = annotation.get_span().file() else {
                return false;
            };
            source.name() == "builtins.pyi"
        }),
        "{diagnostics:?}"
    );
    Ok(())
}

#[test]
fn v3_requires_recognized_forms_and_intrinsic_facts() -> anyhow::Result<()> {
    let source = "Config = record(value=int)\nConfig(value=\"wrong\")\n";
    let (db, mut graph) = root_only(source)?;
    let diagnostics = checked(&db, &graph)?;
    assert_eq!(codes(&diagnostics), ["invalid-argument-type"]);

    graph.profile.name.clear();
    profile_failure(&db, &graph)?;
    graph.profile = profile();
    graph.profile.intrinsics[0].kind = "field_accepts_any_type".to_string();
    profile_failure(&db, &graph)?;
    graph.profile = profile();
    graph.profile.intrinsics[1].name = "field".to_string();
    profile_failure(&db, &graph)?;
    graph.profile = profile();
    graph.profile.intrinsics = Box::new([]);
    profile_failure(&db, &graph)?;
    graph.profile = profile();
    graph.profile.special_forms[1].field_types = "arbitrary_python_keyword".to_string();
    profile_failure(&db, &graph)?;
    graph.profile = profile();
    graph.profile.special_forms[1].name = "record".to_string();
    profile_failure(&db, &graph)?;
    graph.profile = profile();
    graph.version = "sty-star-graph-v1".to_string();
    profile_failure(&db, &graph)?;
    graph.version = "sty-star-graph-v2".to_string();
    profile_failure(&db, &graph)?;
    graph.version = "sty-star-graph-v4".to_string();
    profile_failure(&db, &graph)?;
    Ok(())
}

#[test]
fn v3_requires_well_formed_portable_host_function_signatures() -> anyhow::Result<()> {
    let source = "VALUE = 1\n";
    let (db, mut graph) = root_only(source)?;
    graph.profile = v3_profile();
    let diagnostics = checked(&db, &graph)?;
    assert!(diagnostics.is_empty());

    for drift in [
        "empty function name",
        "form name collision",
        "intrinsic name collision",
        "duplicate function",
        "unknown return type",
        "unknown availability",
        "empty parameter name",
        "duplicate parameter",
        "unknown parameter mode",
        "unknown parameter type",
        "unsorted parameter modes",
        "required positional after optional",
    ] {
        graph.profile = v3_profile();
        let function = &mut graph.profile.host_functions[0];
        match drift {
            "empty function name" => function.name.clear(),
            "form name collision" => function.name = "record".to_string(),
            "intrinsic name collision" => function.name = "field".to_string(),
            "duplicate function" => {
                graph.profile.host_functions = Box::new([
                    example_host_function("same_native"),
                    example_host_function("same_native"),
                ]);
            }
            "unknown return type" => function.returns = "dynamic_object".to_string(),
            "unknown availability" => function.availability = "always".to_string(),
            "empty parameter name" => function.params[0].name.clear(),
            "duplicate parameter" => {
                function.params = Box::new([
                    example_host_param("value", "pos_or_named", true),
                    example_host_param("value", "named_only", false),
                ]);
            }
            "unknown parameter mode" => function.params[0].mode = "auto".to_string(),
            "unknown parameter type" => function.params[0].ty = "dynamic_object".to_string(),
            "unsorted parameter modes" => {
                function.params = Box::new([
                    example_host_param("option", "named_only", false),
                    example_host_param("value", "pos_or_named", true),
                ]);
            }
            "required positional after optional" => {
                function.params = Box::new([
                    example_host_param("first", "pos_only", false),
                    example_host_param("second", "pos_or_named", true),
                ]);
            }
            _ => anyhow::bail!("unexpected host signature drift {drift}"),
        }
        profile_failure(&db, &graph).with_context(|| drift)?;
    }
    Ok(())
}

#[test]
fn rejects_stale_load_aliases_and_missing_graph_targets_before_analysis() -> anyhow::Result<()> {
    let root_source = format!(
        "load(\"{LABEL}\", \"LimitConfig\")\nif False:\n    LimitConfig(max_connections=\"wrong\")\n"
    );
    let (db, mut graph) = case(&root_source, DECLARATION)?;
    let root_file = graph.root.file;
    graph.root.loads[0].bindings[0].local = "stale".to_string();
    let StarCheck::Opaque(failure) = check_star_graph(&db, &graph)? else {
        anyhow::bail!("stale alias unexpectedly passed graph validation");
    };
    assert_eq!(failure.file(), root_file);
    assert!(matches!(failure.reason(), StarFailureReason::LoadMismatch));
    let label = format!("\"{LABEL}\"");
    assert_eq!(
        slice(&root_source, failure.range().context("missing load range")?),
        Some(label.as_str())
    );

    graph.root.loads[0].bindings[0].local = "LimitConfig".to_string();
    graph.modules = Box::new([]);
    let StarCheck::Opaque(failure) = check_star_graph(&db, &graph)? else {
        anyhow::bail!("unresolved graph edge unexpectedly passed validation");
    };
    assert_eq!(failure.file(), root_file);
    assert!(matches!(
        failure.reason(),
        StarFailureReason::UnresolvedModule
    ));
    Ok(())
}

#[test]
fn parse_recovery_keeps_the_entire_graph_opaque() -> anyhow::Result<()> {
    let root_source = format!(
        "load(\"{LABEL}\", \"LimitConfig\")\nif False:\n    LimitConfig(max_connections=\nGOOD = 1\n"
    );
    let (db, graph) = case(&root_source, DECLARATION)?;
    let StarCheck::Opaque(failure) = check_star_graph(&db, &graph)? else {
        anyhow::bail!("parse recovery exposed apparent source bindings");
    };
    assert_eq!(failure.file(), graph.root.file);
    assert!(failure.range().is_some());
    assert!(matches!(failure.reason(), StarFailureReason::Parser(_)));
    Ok(())
}

#[test]
fn private_import_or_cycle_cannot_supply_a_record_type() -> anyhow::Result<()> {
    let root_source = format!(
        "load(\"{LABEL}\", \"_HiddenConfig\")\nif False:\n    _HiddenConfig(max_connections=\"wrong\")\n"
    );
    let module_source = "_HiddenConfig = record(max_connections=int)\n";
    let (db, mut graph) = case(&root_source, module_source)?;
    let [load] = graph.root.loads.as_mut() else {
        anyhow::bail!("expected the direct root load");
    };
    let [binding] = load.bindings.as_mut() else {
        anyhow::bail!("expected one root load binding");
    };
    binding.local = "_HiddenConfig".to_string();
    binding.source = "_HiddenConfig".to_string();
    let StarCheck::Opaque(failure) = check_star_graph(&db, &graph)? else {
        anyhow::bail!("private imported symbol yielded trusted precision");
    };
    assert_eq!(failure.file(), graph.root.file);
    assert!(matches!(failure.reason(), StarFailureReason::PrivateImport));

    let root_source = format!("load(\"{LABEL}\", \"LimitConfig\")\n");
    let module_source =
        format!("load(\"{LABEL}\", \"LimitConfig\")\nLimitConfig = record(max_connections=int)\n");
    let (db, mut graph) = case(&root_source, &module_source)?;
    let [module] = graph.modules.as_mut() else {
        anyhow::bail!("expected one graph module");
    };
    let module_file = module.source.file;
    module.source.loads = Box::new([StarDirectLoad {
        module_id: LABEL.to_string(),
        label_range: span(&module_source, &format!("\"{LABEL}\""))?,
        bindings: Box::new([StarLoadBinding {
            local: "LimitConfig".to_string(),
            source: "LimitConfig".to_string(),
        }]),
    }]);
    let StarCheck::Opaque(failure) = check_star_graph(&db, &graph)? else {
        anyhow::bail!("cyclic imported symbol yielded trusted precision");
    };
    assert_eq!(failure.file(), module_file);
    assert!(matches!(failure.reason(), StarFailureReason::LoadCycle));
    Ok(())
}

#[test]
fn unsupported_profile_and_duplicate_module_ids_fail_closed() -> anyhow::Result<()> {
    let root_source = format!("load(\"{LABEL}\", \"LimitConfig\")\n");
    let (db, mut graph) = case(&root_source, DECLARATION)?;
    graph.profile.special_forms[1].field_types = "arbitrary_python_keyword".to_string();
    let StarCheck::Opaque(failure) = check_star_graph(&db, &graph)? else {
        anyhow::bail!("unsupported special-form semantics were silently trusted");
    };
    assert!(matches!(failure.reason(), StarFailureReason::Profile));

    graph.profile = profile();
    let [module] = graph.modules.as_ref() else {
        anyhow::bail!("expected one original module");
    };
    graph.modules = Box::new([
        StarModule {
            id: module.id.clone(),
            source: StarSource {
                file: module.source.file,
                text: module.source.text.clone(),
                loads: Box::new([]),
            },
        },
        StarModule {
            id: module.id.clone(),
            source: StarSource {
                file: module.source.file,
                text: module.source.text.clone(),
                loads: Box::new([]),
            },
        },
    ]);
    let StarCheck::Opaque(failure) = check_star_graph(&db, &graph)? else {
        anyhow::bail!("duplicate logical modules were silently trusted");
    };
    assert!(matches!(
        failure.reason(),
        StarFailureReason::DuplicateModule
    ));
    Ok(())
}

#[test]
fn conflicting_snapshots_for_one_physical_file_are_opaque() -> anyhow::Result<()> {
    let root_source = format!(
        "load(\"{LABEL}\", \"LimitConfig\")\nif False:\n    LimitConfig(max_connections=\"wrong\")\n"
    );
    let (db, mut graph) = case(&root_source, DECLARATION)?;
    let physical_file = graph.root.file;
    graph.modules[0].source.file = physical_file;
    let StarCheck::Opaque(failure) = check_star_graph(&db, &graph)? else {
        anyhow::bail!("ambiguous physical source yielded a typed source span");
    };
    assert_eq!(failure.file(), physical_file);
    assert!(matches!(
        failure.reason(),
        StarFailureReason::ConflictingSnapshot
    ));
    Ok(())
}

#[test]
fn different_load_ids_keep_distinct_nominal_types_for_one_physical_file() -> anyhow::Result<()> {
    let first_id = "//example:first.star";
    let second_id = "//example:second.star";
    let root_source = format!(
        "load(\"{first_id}\", first=\"Config\", first_value=\"instance\")\nload(\"{second_id}\", second=\"Config\", second_value=\"instance\")\nHolder = record(item=first)\nif False:\n    Holder(item=first_value)\n    Holder(item=second_value)\n    Holder(item=second(value=\"ok\"))\n"
    );
    let module_source = "Config = record(value=str)\ninstance = Config(value=\"ok\")\n";
    let (db, root) = test_db(&[("root.star", &root_source), ("shared.star", module_source)])?;
    let root_file = system_path_to_file(&db, root.join("root.star"))?;
    let shared_file = system_path_to_file(&db, root.join("shared.star"))?;
    let graph = StarResolvedGraph {
        version: "sty-star-graph-v3".to_string(),
        profile: profile(),
        root: StarSource {
            file: root_file,
            text: root_source.clone(),
            loads: Box::new([
                StarDirectLoad {
                    module_id: first_id.to_string(),
                    label_range: span(&root_source, &format!("\"{first_id}\""))?,
                    bindings: Box::new([
                        StarLoadBinding {
                            local: "first".to_string(),
                            source: "Config".to_string(),
                        },
                        StarLoadBinding {
                            local: "first_value".to_string(),
                            source: "instance".to_string(),
                        },
                    ]),
                },
                StarDirectLoad {
                    module_id: second_id.to_string(),
                    label_range: span(&root_source, &format!("\"{second_id}\""))?,
                    bindings: Box::new([
                        StarLoadBinding {
                            local: "second".to_string(),
                            source: "Config".to_string(),
                        },
                        StarLoadBinding {
                            local: "second_value".to_string(),
                            source: "instance".to_string(),
                        },
                    ]),
                },
            ]),
        },
        modules: Box::new([
            StarModule {
                id: first_id.to_string(),
                source: StarSource {
                    file: shared_file,
                    text: module_source.to_string(),
                    loads: Box::new([]),
                },
            },
            StarModule {
                id: second_id.to_string(),
                source: StarSource {
                    file: shared_file,
                    text: module_source.to_string(),
                    loads: Box::new([]),
                },
            },
        ]),
    };
    let diagnostics = checked(&db, &graph)?;
    assert_eq!(
        codes(&diagnostics),
        ["invalid-argument-type", "invalid-argument-type"],
        "{diagnostics:?}"
    );
    assert_eq!(
        diagnostics
            .iter()
            .filter_map(|diagnostic| diagnostic
                .primary_span()
                .map(|span| captured_slice(&span).map(str::to_string)))
            .collect::<Vec<_>>(),
        [
            Some("item=second_value".to_string()),
            Some("item=second(value=\"ok\")".to_string())
        ]
    );
    for diagnostic in &diagnostics {
        assert!(
            annotations(diagnostic)
                .any(|annotation| captured_slice(annotation.get_span()) == Some("first")),
            "{diagnostic:?}"
        );
        let message = diagnostic.concise_message().to_string();
        assert!(
            message.contains(first_id) && message.contains(second_id),
            "{message}"
        );
    }
    Ok(())
}
