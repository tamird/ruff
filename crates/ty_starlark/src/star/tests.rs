use anyhow::Context as _;
use ruff_db::files::{File, system_path_to_file};
use ruff_text_size::{TextRange, TextSize};

use crate::testing::{TestDb, test_db};

use super::{
    StarAnalysis, StarCheck, StarDirectLoad, StarFailureReason, StarHostFunction, StarHostParam,
    StarHostProfile, StarIntrinsic, StarKnownType, StarLoadBinding, StarModule, StarPrimitive,
    StarResolvedGraph, StarSource, StarSpecialForm, check_star_graph,
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
        name: "example-star-host-v1".to_string(),
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
        intrinsics: Box::new([]),
        host_functions: Box::new([]),
    }
}

fn v2_profile() -> StarHostProfile {
    let mut host = profile();
    host.name = "example-star-host-v2".to_string();
    host.intrinsics = Box::new([
        StarIntrinsic {
            name: "field".to_string(),
            kind: "field_first_type_optional_default".to_string(),
        },
        StarIntrinsic {
            name: "struct".to_string(),
            kind: "struct_named_members".to_string(),
        },
    ]);
    host
}

fn v3_profile() -> StarHostProfile {
    let mut host = v2_profile();
    host.name = "example-star-host-v3".to_string();
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
        version: "sty-star-graph-v1".to_string(),
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
            version: "sty-star-graph-v1".to_string(),
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

fn v2_root_only(root_source: &str) -> anyhow::Result<(TestDb, StarResolvedGraph)> {
    let (db, mut graph) = root_only(root_source)?;
    graph.version = "sty-star-graph-v2".to_string();
    graph.profile = v2_profile();
    Ok((db, graph))
}

fn v3_root_only(root_source: &str) -> anyhow::Result<(TestDb, StarResolvedGraph)> {
    let (db, mut graph) = v2_root_only(root_source)?;
    graph.version = "sty-star-graph-v3".to_string();
    graph.profile = native_profile();
    Ok((db, graph))
}

fn profile_failure(graph: &StarResolvedGraph) -> anyhow::Result<()> {
    let StarCheck::Opaque(failure) = check_star_graph(graph) else {
        anyhow::bail!("invalid host profile unexpectedly established source types");
    };
    assert!(matches!(failure.reason(), StarFailureReason::Profile));
    assert_eq!(failure.file(), graph.root.file);
    Ok(())
}

#[test]
fn v2_requires_recognized_forms_and_intrinsic_facts() -> anyhow::Result<()> {
    let source = "Config = record(value=int)\nConfig(value=\"wrong\")\n";
    let (_db, mut graph) = v2_root_only(source)?;
    let analysis = analyzed(check_star_graph(&graph))?;
    assert_eq!(analysis.checked_arguments(), 1);
    assert_eq!(analysis.problems().len(), 1);

    graph.profile.name.clear();
    profile_failure(&graph)?;
    graph.profile = v2_profile();
    graph.profile.intrinsics[0].kind = "field_accepts_any_type".to_string();
    profile_failure(&graph)?;
    graph.profile = v2_profile();
    graph.profile.intrinsics[1].name = "field".to_string();
    profile_failure(&graph)?;
    graph.profile = v2_profile();
    graph.profile.intrinsics = Box::new([]);
    profile_failure(&graph)?;
    graph.profile = v2_profile();
    graph.profile.special_forms[1].field_types = "arbitrary_python_keyword".to_string();
    profile_failure(&graph)?;
    graph.profile = v2_profile();
    graph.profile.special_forms[1].name = "record".to_string();
    profile_failure(&graph)?;
    graph.profile = v2_profile();
    graph.version = "sty-star-graph-v1".to_string();
    profile_failure(&graph)?;
    graph.version = "sty-star-graph-v2".to_string();
    graph.profile.host_functions = v3_profile().host_functions;
    profile_failure(&graph)?;
    graph.version = "sty-star-graph-v4".to_string();
    profile_failure(&graph)?;
    Ok(())
}

#[test]
fn v3_accepts_an_attested_empty_host_inventory_and_retains_source_checks() -> anyhow::Result<()> {
    let source = "def choose(flag: bool):\n    pass\nchoose(flag=\"wrong\")\n";
    let (_db, mut graph) = v2_root_only(source)?;
    graph.version = "sty-star-graph-v3".to_string();
    let analysis = analyzed(check_star_graph(&graph))?;
    assert_eq!(analysis.checked_arguments(), 1);
    let [problem] = analysis.problems() else {
        anyhow::bail!("empty native inventory lost source def checking: {analysis:?}");
    };
    assert_eq!(problem.related_label(), "parameter annotated");
    assert_eq!(slice(source, problem.related_range()), Some("bool"));
    Ok(())
}

#[test]
fn v3_requires_well_formed_portable_host_function_signatures() -> anyhow::Result<()> {
    let source = "VALUE = 1\n";
    let (_db, mut graph) = v2_root_only(source)?;
    graph.version = "sty-star-graph-v3".to_string();
    graph.profile = v3_profile();
    let analysis = analyzed(check_star_graph(&graph))?;
    assert!(analysis.problems().is_empty());

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
        profile_failure(&graph).with_context(|| drift)?;
    }
    Ok(())
}

#[test]
fn v3_checks_native_scalars_and_infers_only_valid_nested_returns() -> anyhow::Result<()> {
    let source = concat!(
        "Config = record(label=str, count=int)\n",
        "if False:\n",
        "    host_hash(value=7)\n",
        "    host_encode(value=unknown(), sort_keys=7)\n",
        "    host_modes(\"ok\", count=7, enabled=\"wrong\")\n",
        "    Config(count=host_hash(\"ok\"))\n",
        "    Config(label=host_hash(host_encode(value=unknown(), sort_keys=True)))\n",
        "    Config(label=host_hash(7))\n",
        "    Config(label=host_hash(host_encode(value=unknown(), sort_keys=\"wrong\")))\n",
        "    Config(label=host_encode(value=unknown()))\n",
    );
    let (_db, graph) = v3_root_only(source)?;
    let analysis = analyzed(check_star_graph(&graph))?;
    let [field] = analysis.problems() else {
        anyhow::bail!("known native return should prove one wrong field: {analysis:?}");
    };
    assert_eq!(field.field(), "count");
    assert_eq!(field.expected().to_string(), "int");
    assert_eq!(field.actual().to_string(), "str");
    assert_eq!(slice(source, field.range()), Some("host_hash(\"ok\")"));
    let [hash, sort_keys, modes, nested_hash, nested_sort_keys] = analysis.native_problems() else {
        anyhow::bail!("expected only independently proven native errors: {analysis:?}");
    };
    for (problem, source_span, message, signature) in [
        (
            hash,
            "7",
            "host_hash parameter value, expected str, got int",
            "host_hash(value: str) -> str",
        ),
        (
            sort_keys,
            "7",
            "host_encode parameter sort_keys, expected bool, got int",
            "host_encode(value: any, *, sort_keys: bool (optional)) -> str",
        ),
        (
            modes,
            "\"wrong\"",
            "host_modes parameter enabled, expected bool, got str",
            "host_modes(base: str, /, count: int, *, enabled: bool (optional)) -> str",
        ),
        (
            nested_hash,
            "7",
            "host_hash parameter value, expected str, got int",
            "host_hash(value: str) -> str",
        ),
        (
            nested_sort_keys,
            "\"wrong\"",
            "host_encode parameter sort_keys, expected bool, got str",
            "host_encode(value: any, *, sort_keys: bool (optional)) -> str",
        ),
    ] {
        assert_eq!(problem.file(), graph.root.file);
        assert_eq!(slice(source, problem.range()), Some(source_span));
        assert_eq!(problem.to_string(), message);
        assert_eq!(problem.signature(), signature);
    }
    assert!(analysis.checked_arguments() >= 9);
    assert!(analysis.unproved_arguments() >= 2);
    Ok(())
}

#[test]
fn v3_native_calls_abstain_when_parameter_mapping_is_unproved() -> anyhow::Result<()> {
    let source = concat!(
        "Config = record(value=int)\n",
        "if False:\n",
        "    Config(value=host_hash())\n",
        "    Config(value=host_encode(1, True))\n",
        "    Config(value=host_encode(value=1, extra=True))\n",
        "    Config(value=host_hash(*values))\n",
        "    Config(value=host_modes(base=\"ok\", count=7))\n",
    );
    let (_db, graph) = v3_root_only(source)?;
    let analysis = analyzed(check_star_graph(&graph))?;
    assert!(analysis.problems().is_empty(), "{analysis:?}");
    assert!(analysis.native_problems().is_empty(), "{analysis:?}");
    assert!(analysis.unproved_arguments() >= 6);
    Ok(())
}

#[test]
fn v3_catalog_proof_requires_eager_loaded_module_and_known_callback() -> anyhow::Result<()> {
    let root_source = format!(
        "load(\"{LABEL}\", \"LimitConfig\")\nif False:\n    host_catalog(name=7, decoder=unknown())\n    LimitConfig(value=True)\n"
    );
    let module_source = concat!(
        "LimitConfig = record(value=bool)\n",
        "def decode(value):\n    pass\n",
        "host_catalog(name=\"ready\", decoder=decode)\n",
        "host_catalog(name=7, decoder=decode)\n",
        "host_catalog(name=\"ready\", decoder=unknown())\n",
        "LimitConfig(value=host_catalog(name=\"ready\", decoder=decode))\n",
        "def delayed():\n    host_catalog(name=7, decoder=decode)\n    host_hash(7)\n",
    );
    let (_db, mut graph) = case(&root_source, module_source)?;
    graph.version = "sty-star-graph-v3".to_string();
    graph.profile = native_profile();
    let analysis = analyzed(check_star_graph(&graph))?;
    assert!(analysis.problems().is_empty(), "{analysis:?}");
    let [problem, deferred_hash] = analysis.native_problems() else {
        anyhow::bail!("only available loaded calls have proven native inputs: {analysis:?}");
    };
    assert_eq!(problem.file(), graph.modules[0].source.file);
    assert_eq!(slice(module_source, problem.range()), Some("7"));
    assert_eq!(
        problem.to_string(),
        "host_catalog parameter name, expected str, got int"
    );
    assert_eq!(
        problem.signature(),
        "host_catalog(name: str, *, decoder: callable) -> any"
    );
    assert_eq!(deferred_hash.file(), graph.modules[0].source.file);
    assert_eq!(slice(module_source, deferred_hash.range()), Some("7"));
    assert_eq!(
        deferred_hash.to_string(),
        "host_hash parameter value, expected str, got int"
    );
    assert!(analysis.unproved_arguments() >= 2);
    Ok(())
}

#[test]
fn v3_native_globals_require_stable_module_and_lexical_bindings() -> anyhow::Result<()> {
    let source = concat!(
        "def parameter(host_hash):\n    host_hash(7)\n",
        "def local():\n    host_hash = unknown()\n    host_hash(7)\n",
        "def unshadowed():\n    host_encode(value=\"ok\", sort_keys=7)\n",
        "if False:\n    host_hash(7)\n",
    );
    let (_db, graph) = v3_root_only(source)?;
    let analysis = analyzed(check_star_graph(&graph))?;
    let [hash, encode] = analysis.native_problems() else {
        anyhow::bail!("lexically shadowed native calls were checked: {analysis:?}");
    };
    assert_eq!(slice(source, encode.range()), Some("7"));
    assert_eq!(slice(source, hash.range()), Some("7"));
    assert_eq!(
        encode.to_string(),
        "host_encode parameter sort_keys, expected bool, got int"
    );
    assert_eq!(
        hash.to_string(),
        "host_hash parameter value, expected str, got int"
    );

    let source = "host_hash(7)\nhost_hash = unknown()\nhost_hash(7)\n";
    let (_db, graph) = v3_root_only(source)?;
    assert!(
        analyzed(check_star_graph(&graph))?
            .native_problems()
            .is_empty(),
        "unstable module binding was treated as native"
    );
    let source = format!("load(\"{LABEL}\", host_hash=\"LimitConfig\")\nhost_hash(value=7)\n");
    let (_db, mut graph) = case(&source, "LimitConfig = record(value=int)\n")?;
    graph.root.loads[0].bindings[0].local = "host_hash".to_string();
    graph.version = "sty-star-graph-v3".to_string();
    graph.profile = native_profile();
    let analysis = analyzed(check_star_graph(&graph))?;
    assert!(analysis.native_problems().is_empty(), "{analysis:?}");
    assert!(analysis.problems().is_empty(), "{analysis:?}");
    Ok(())
}

#[test]
fn v2_field_type_expressions_prove_primitive_union_and_nominal_lists() -> anyhow::Result<()> {
    let source = concat!(
        "Left = record(code=int)\n",
        "Right = record(code=int)\n",
        "Config = record(\n",
        "    count=field(int, default=0),\n",
        "    flag=field(bool, False),\n",
        "    maybe=field(Left | None, default=None),\n",
        "    items=field(list[Left]),\n",
        "    unknown=field(Missing, default=make_value()),\n",
        ")\n",
        "if False:\n",
        "    Config(count=\"wrong\", flag=\"wrong\", maybe=Right(code=1), items=[Right(code=1)], unknown=\"wrong\")\n",
        "Config(count=1, flag=True, maybe=None, items=[Left(code=1)])\n",
    );
    let (_db, graph) = v2_root_only(source)?;
    let analysis = analyzed(check_star_graph(&graph))?;
    assert_eq!(analysis.checked_arguments(), 11);
    assert_eq!(analysis.unproved_arguments(), 1);
    let [count, flag, maybe, items] = analysis.problems() else {
        anyhow::bail!("expected four field mismatches: {analysis:?}");
    };
    for (problem, field, related, expected, actual) in [
        (count, "count", "int", "int", "str"),
        (flag, "flag", "bool", "bool", "str"),
        (maybe, "maybe", "Left | None", "Left | None", "Right"),
        (items, "items", "list[Left]", "list[Left]", "list[Right]"),
    ] {
        assert_eq!(problem.file(), graph.root.file);
        assert_eq!(problem.related_file(), graph.root.file);
        assert_eq!(problem.field(), field);
        assert_eq!(slice(source, problem.related_range()), Some(related));
        assert_eq!(problem.expected().to_string(), expected);
        assert_eq!(problem.actual().to_string(), actual);
    }
    assert_eq!(slice(source, count.range()), Some("\"wrong\""));
    assert_eq!(slice(source, maybe.range()), Some("Right(code=1)"));
    assert_eq!(slice(source, items.range()), Some("[Right(code=1)]"));
    Ok(())
}

#[test]
fn v2_field_annotation_resolves_a_loaded_nominal_record() -> anyhow::Result<()> {
    let source = format!(
        "load(\"{LABEL}\", \"Left\", \"Right\")\nConfig = record(value=field(Left))\nConfig(value=Right(code=1))\n"
    );
    let module_source = "Left = record(code=int)\nRight = record(code=int)\n";
    let (_db, mut graph) = case(&source, module_source)?;
    graph.version = "sty-star-graph-v2".to_string();
    graph.profile = v2_profile();
    graph.root.loads[0].bindings = Box::new([
        StarLoadBinding {
            local: "Left".to_string(),
            source: "Left".to_string(),
        },
        StarLoadBinding {
            local: "Right".to_string(),
            source: "Right".to_string(),
        },
    ]);
    let analysis = analyzed(check_star_graph(&graph))?;
    assert_eq!(analysis.checked_arguments(), 2);
    let [problem] = analysis.problems() else {
        anyhow::bail!("expected a mismatched loaded nominal record: {analysis:?}");
    };
    assert_eq!(problem.file(), graph.root.file);
    assert_eq!(problem.related_file(), graph.root.file);
    assert_eq!(slice(&source, problem.range()), Some("Right(code=1)"));
    assert_eq!(slice(&source, problem.related_range()), Some("Left"));
    assert_eq!(problem.expected().to_string(), "Left");
    assert_eq!(problem.actual().to_string(), "Right");
    Ok(())
}

#[test]
fn native_field_proof_requires_v2_and_leaves_unknown_values_unproved() -> anyhow::Result<()> {
    let source = concat!(
        "Config = record(value=field(int, default=make_value()))\n",
        "Config(value=make_value())\n",
        "Config(value=\"wrong\")\n",
    );
    let (_db, v1) = root_only(source)?;
    let analysis = analyzed(check_star_graph(&v1))?;
    assert!(analysis.problems().is_empty());
    assert_eq!(analysis.checked_arguments(), 0);
    assert_eq!(analysis.unproved_arguments(), 2);

    let (_db, v2) = v2_root_only(source)?;
    let analysis = analyzed(check_star_graph(&v2))?;
    assert_eq!(analysis.checked_arguments(), 1);
    assert_eq!(analysis.unproved_arguments(), 1);
    let [problem] = analysis.problems() else {
        anyhow::bail!("expected the known string mismatch: {analysis:?}");
    };
    assert_eq!(slice(source, problem.range()), Some("\"wrong\""));
    assert_eq!(slice(source, problem.related_range()), Some("int"));
    Ok(())
}

#[test]
fn shadowed_or_unrecognized_field_calls_do_not_prove_annotations() -> anyhow::Result<()> {
    for source in [
        "field = 0\nConfig = record(value=field(int))\nConfig(value=\"wrong\")\n",
        "Config = record(value=field(int))\nfield = 0\nConfig(value=\"wrong\")\n",
        "def field(typ):\n    pass\nConfig = record(value=field(int))\nConfig(value=\"wrong\")\n",
        "Config = record(value=field(int, unexpected=0))\nConfig(value=\"wrong\")\n",
        "Config = record(value=field(int, 0, default=0))\nConfig(value=\"wrong\")\n",
        "Config = record(value=field(Missing))\nConfig(value=\"wrong\")\n",
    ] {
        let (_db, graph) = v2_root_only(source)?;
        let analysis = analyzed(check_star_graph(&graph))?;
        assert!(analysis.problems().is_empty(), "{source}: {analysis:?}");
        assert_eq!(analysis.checked_arguments(), 0, "{source}");
        assert_eq!(analysis.unproved_arguments(), 1, "{source}");
    }

    let source = format!(
        "load(\"{LABEL}\", \"field\")\nConfig = record(value=field(int))\nConfig(value=\"wrong\")\n"
    );
    let (_db, mut graph) = case(&source, "field = record(value=int)\n")?;
    graph.version = "sty-star-graph-v2".to_string();
    graph.profile = v2_profile();
    graph.root.loads[0].bindings[0].local = "field".to_string();
    graph.root.loads[0].bindings[0].source = "field".to_string();
    let analysis = analyzed(check_star_graph(&graph))?;
    assert!(analysis.problems().is_empty());
    assert_eq!(analysis.checked_arguments(), 0);
    assert_eq!(analysis.unproved_arguments(), 1);
    Ok(())
}

#[test]
fn attested_struct_members_resolve_record_calls_and_explicit_aliases() -> anyhow::Result<()> {
    let source = concat!(
        "Repository = record(name=str)\n",
        "images = struct(repository=Repository, computed=make_value())\n",
        "repository = images.repository\n",
        "nested = struct(images=images)\n",
        "images.repository(name=7)\n",
        "repository(name=7)\n",
        "nested.images.repository(name=7)\n",
        "images.computed(name=7)\n",
    );
    let (_db, v1) = root_only(source)?;
    let analysis = analyzed(check_star_graph(&v1))?;
    assert!(analysis.problems().is_empty());
    assert_eq!(analysis.checked_arguments(), 0);

    let (_db, v2) = v2_root_only(source)?;
    let analysis = analyzed(check_star_graph(&v2))?;
    assert_eq!(analysis.checked_arguments(), 3);
    let [direct, alias, nested] = analysis.problems() else {
        anyhow::bail!("expected three proven struct member calls: {analysis:?}");
    };
    for (problem, constructor) in [
        (direct, "images.repository"),
        (alias, "repository"),
        (nested, "nested.images.repository"),
    ] {
        assert_eq!(problem.constructor(), constructor);
        assert_eq!(problem.field(), "name");
        assert_eq!(problem.file(), v2.root.file);
        assert_eq!(problem.related_file(), v2.root.file);
        assert_eq!(slice(source, problem.range()), Some("7"));
        assert_eq!(slice(source, problem.related_range()), Some("str"));
    }
    Ok(())
}

#[test]
fn loaded_struct_keeps_module_field_locations() -> anyhow::Result<()> {
    let root_source = format!("load(\"{LABEL}\", \"images\")\nimages.repository(name=7)\n");
    let module_source = "Repository = record(name=str)\nimages = struct(repository=Repository)\n";
    let (_db, mut graph) = case(&root_source, module_source)?;
    graph.version = "sty-star-graph-v2".to_string();
    graph.profile = v2_profile();
    graph.root.loads[0].bindings[0].local = "images".to_string();
    graph.root.loads[0].bindings[0].source = "images".to_string();
    let (root_file, module_file) = files(&graph)?;
    let analysis = analyzed(check_star_graph(&graph))?;
    let [problem] = analysis.problems() else {
        anyhow::bail!("expected loaded struct member mismatch: {analysis:?}");
    };
    assert_eq!(analysis.checked_arguments(), 1);
    assert_eq!(problem.file(), root_file);
    assert_eq!(problem.related_file(), module_file);
    assert_eq!(problem.constructor(), "images.repository");
    assert_eq!(slice(&root_source, problem.range()), Some("7"));
    assert_eq!(slice(module_source, problem.related_range()), Some("str"));
    Ok(())
}

#[test]
fn struct_members_follow_source_order_and_decline_unproved_sources() -> anyhow::Result<()> {
    let source = concat!(
        "Repository = record(name=str)\n",
        "images.repository(name=7)\n",
        "images = struct(repository=Repository)\n",
        "images.repository(name=7)\n",
    );
    let (_db, graph) = v2_root_only(source)?;
    let analysis = analyzed(check_star_graph(&graph))?;
    assert_eq!(analysis.checked_arguments(), 1);
    let [problem] = analysis.problems() else {
        anyhow::bail!("expected only the call following the struct binding: {analysis:?}");
    };
    assert_eq!(slice(source, problem.range()), Some("7"));
    let second_call = source
        .rfind("images.repository(name=7)")
        .ok_or_else(|| anyhow::anyhow!("source-order test lacks the second call"))?;
    assert_eq!(
        problem.range().start().to_usize(),
        second_call + "images.repository(name=".len(),
    );

    for source in [
        "Repository = record(name=str)\nstruct = missing\nimages = struct(repository=Repository)\nimages.repository(name=7)\n",
        "Repository = record(name=str)\nimages = struct(Repository, repository=Repository)\nimages.repository(name=7)\n",
        "Repository = record(name=str)\nimages = struct(repository=Repository, **extra)\nimages.repository(name=7)\n",
        "Repository = record(name=str)\nimages = struct(repository=make_value())\nimages.repository(name=7)\n",
        "Repository = record(name=str)\nimages = struct(repository=Repository)\nimages = struct(repository=make_value())\nimages.repository(name=7)\n",
    ] {
        let (_db, graph) = v2_root_only(source)?;
        let analysis = analyzed(check_star_graph(&graph))?;
        assert!(analysis.problems().is_empty(), "{source}: {analysis:?}");
        assert_eq!(analysis.checked_arguments(), 0, "{source}");
    }
    Ok(())
}

#[test]
fn v2_source_function_checks_known_positional_and_named_annotations() -> anyhow::Result<()> {
    let source = concat!(
        "def choose(flag: bool, count: int, name: str | None):\n",
        "    pass\n",
        "choose(\"wrong\", count=\"wrong\", name=7)\n",
    );
    let (_db, v1) = root_only(source)?;
    let analysis = analyzed(check_star_graph(&v1))?;
    assert!(analysis.problems().is_empty());
    assert_eq!(analysis.checked_arguments(), 0);

    let (_db, v2) = v2_root_only(source)?;
    let analysis = analyzed(check_star_graph(&v2))?;
    assert_eq!(analysis.checked_arguments(), 3);
    let [flag, count, name] = analysis.problems() else {
        anyhow::bail!("expected three annotated parameter mismatches: {analysis:?}");
    };
    for (problem, parameter, annotation, expected, actual) in [
        (flag, "flag", "bool", "bool", "str"),
        (count, "count", "int", "int", "str"),
        (name, "name", "str | None", "str | None", "int"),
    ] {
        assert_eq!(problem.constructor(), "choose");
        assert_eq!(problem.field(), parameter);
        assert_eq!(problem.related_label(), "parameter annotated");
        assert_eq!(problem.related_file(), v2.root.file);
        assert_eq!(slice(source, problem.related_range()), Some(annotation));
        assert_eq!(problem.expected().to_string(), expected);
        assert_eq!(problem.actual().to_string(), actual);
    }
    assert_eq!(slice(source, flag.range()), Some("\"wrong\""));
    assert_eq!(slice(source, name.range()), Some("7"));
    assert_eq!(
        flag.to_string(),
        "choose parameter flag, expected bool, got str"
    );
    Ok(())
}

#[test]
fn v2_loaded_struct_function_checks_known_nominal_union_and_list_arguments() -> anyhow::Result<()> {
    let root_source = format!(
        "load(\"{LABEL}\", \"api\")\napi.submit(flag=\"bad\", owner=api.make_right(), items=[api.make_right()])\n"
    );
    let module_source = concat!(
        "Left = record(code=int)\n",
        "Right = record(code=int)\n",
        "def make_right() -> Right:\n",
        "    return Right(code=1)\n",
        "def _submit(flag: bool, owner: Left, items: list[Left | None]):\n",
        "    pass\n",
        "api = struct(submit=_submit, make_right=make_right)\n",
    );
    let (_db, mut graph) = case(&root_source, module_source)?;
    graph.version = "sty-star-graph-v2".to_string();
    graph.profile = v2_profile();
    graph.root.loads[0].bindings[0].local = "api".to_string();
    graph.root.loads[0].bindings[0].source = "api".to_string();
    let (root_file, module_file) = files(&graph)?;
    let analysis = analyzed(check_star_graph(&graph))?;
    assert_eq!(analysis.checked_arguments(), 4);
    let [flag, owner, items] = analysis.problems() else {
        anyhow::bail!("expected three loaded function mismatches: {analysis:?}");
    };
    for (problem, parameter, annotation, expected, actual) in [
        (flag, "flag", "bool", "bool", "str"),
        (owner, "owner", "Left", "Left", "Right"),
        (
            items,
            "items",
            "list[Left | None]",
            "list[Left | None]",
            "list[Right]",
        ),
    ] {
        assert_eq!(problem.file(), root_file);
        assert_eq!(problem.related_file(), module_file);
        assert_eq!(problem.constructor(), "api.submit");
        assert_eq!(problem.field(), parameter);
        assert_eq!(
            slice(module_source, problem.related_range()),
            Some(annotation)
        );
        assert_eq!(problem.expected().to_string(), expected);
        assert_eq!(problem.actual().to_string(), actual);
    }
    assert_eq!(slice(&root_source, flag.range()), Some("\"bad\""));
    assert_eq!(slice(&root_source, owner.range()), Some("api.make_right()"));
    Ok(())
}

#[test]
fn source_function_calls_accept_known_scalar_nominal_union_and_list_values() -> anyhow::Result<()> {
    let source = concat!(
        "Left = record(value=int)\n",
        "ResourceBuilder = typing.Callable[[int], Left]\n",
        "def make_left() -> Left:\n",
        "    return Left(value=1)\n",
        "def submit(owner: Left | None, items: list[Left | None], flag: bool, count: int, name: str, callback: ResourceBuilder):\n",
        "    pass\n",
        "submit(owner=make_left(), items=[make_left(), None], flag=True, count=1, name=\"ok\", callback=make_left)\n",
    );
    let (_db, graph) = v2_root_only(source)?;
    let analysis = analyzed(check_star_graph(&graph))?;
    assert!(analysis.problems().is_empty(), "{analysis:?}");
    assert_eq!(analysis.checked_arguments(), 6);
    assert_eq!(analysis.unproved_arguments(), 1);
    Ok(())
}

#[test]
fn source_function_signatures_follow_order_and_leave_unknown_annotations_unproved()
-> anyhow::Result<()> {
    let source = concat!(
        "check(flag=\"bad\")\n",
        "def check(flag: bool):\n",
        "    pass\n",
        "check(flag=\"bad\")\n",
    );
    let (_db, graph) = v2_root_only(source)?;
    let analysis = analyzed(check_star_graph(&graph))?;
    assert_eq!(analysis.checked_arguments(), 1);
    let [problem] = analysis.problems() else {
        anyhow::bail!("expected only the call following the function definition: {analysis:?}");
    };
    let second_call = source
        .rfind("check(flag=\"bad\")")
        .ok_or_else(|| anyhow::anyhow!("source-order test lacks the later call"))?;
    assert_eq!(
        problem.range().start().to_usize(),
        second_call + "check(flag=".len()
    );

    for source in [
        "def check(flag: bool):\n    pass\ncheck = missing\ncheck(flag=\"bad\")\n",
        "def check(flag: Missing):\n    pass\ncheck(flag=7)\n",
        "def check(*values: int):\n    pass\ncheck(\"bad\")\n",
        "def check(flag: bool):\n    pass\ncheck(flag=\"bad\", flag_again=7)\n",
        "def check(flag: bool):\n    pass\ncheck(\"bad\", flag=7)\n",
    ] {
        let (_db, graph) = v2_root_only(source)?;
        let analysis = analyzed(check_star_graph(&graph))?;
        assert!(analysis.problems().is_empty(), "{source}: {analysis:?}");
        assert_eq!(analysis.checked_arguments(), 0, "{source}");
    }
    Ok(())
}

#[test]
fn source_functions_with_unknown_returns_do_not_supply_nominal_precision() -> anyhow::Result<()> {
    let source = concat!(
        "Known = record(value=int)\n",
        "def unknown() -> Missing:\n",
        "    return 7\n",
        "def take(item: Known):\n",
        "    pass\n",
        "take(item=unknown())\n",
    );
    let (_db, graph) = v2_root_only(source)?;
    let analysis = analyzed(check_star_graph(&graph))?;
    assert!(analysis.problems().is_empty());
    assert_eq!(analysis.checked_arguments(), 0);
    assert_eq!(analysis.unproved_arguments(), 1);
    Ok(())
}

#[test]
fn malformed_source_function_calls_do_not_establish_known_return_types() -> anyhow::Result<()> {
    let source = concat!(
        "Left = record(value=int)\n",
        "Right = record(value=int)\n",
        "def make_right(flag: bool) -> Right:\n",
        "    return Right(value=1)\n",
        "def take(item: Left):\n",
        "    pass\n",
        "take(item=make_right(unexpected=7))\n",
        "take(item=make_right(*unknown))\n",
        "take(item=make_right())\n",
    );
    let (_db, graph) = v2_root_only(source)?;
    let analysis = analyzed(check_star_graph(&graph))?;
    assert!(analysis.problems().is_empty());
    assert_eq!(analysis.checked_arguments(), 1);
    assert_eq!(analysis.unproved_arguments(), 5);
    Ok(())
}

#[test]
fn deferred_source_functions_check_stable_loads_without_borrowing_local_names() -> anyhow::Result<()>
{
    let root_source = format!(
        "load(\"{LABEL}\", \"api\")\n\
         def shadow_parameter(api):\n    api.submit(flag=\"wrong\")\n\
         def shadow_local():\n    api.submit(flag=\"wrong\")\n    api = computed()\n\
         def shadow_nested():\n    def api():\n        pass\n    api.submit(flag=\"wrong\")\n\
         def live():\n    [api.submit(flag=\"wrong\") for api in values]\n    f = lambda api: api.submit(flag=\"wrong\")\n    api.submit(flag=\"wrong\")\n    api.submit(flag=True)\n"
    );
    let module_source = "Api = record(flag=bool)\napi = struct(submit=Api)\n";
    let (_db, mut graph) = case(&root_source, module_source)?;
    graph.root.loads[0].bindings[0].local = "api".to_string();
    graph.root.loads[0].bindings[0].source = "api".to_string();
    let v1 = analyzed(check_star_graph(&graph))?;
    assert_eq!(v1.checked_arguments(), 0);
    assert!(v1.problems().is_empty());

    graph.version = "sty-star-graph-v2".to_string();
    graph.profile = v2_profile();
    let (root_file, module_file) = files(&graph)?;
    let analysis = analyzed(check_star_graph(&graph))?;
    assert_eq!(analysis.checked_arguments(), 2);
    let [problem] = analysis.problems() else {
        anyhow::bail!("expected only the stable deferred loaded call: {analysis:?}");
    };
    assert_eq!(problem.file(), root_file);
    assert_eq!(problem.related_file(), module_file);
    assert_eq!(problem.constructor(), "api.submit");
    assert_eq!(problem.related_label(), "field declared");
    assert_eq!(slice(module_source, problem.related_range()), Some("bool"));
    let live_body = root_source
        .split_once("def live():")
        .ok_or_else(|| anyhow::anyhow!("deferred fixture lacks live function"))?
        .1;
    let start = root_source.len() - live_body.len();
    assert!(problem.range().start().to_usize() >= start);
    assert_eq!(slice(&root_source, problem.range()), Some("\"wrong\""));
    Ok(())
}

#[test]
fn deferred_resources_use_loaded_source_function_annotations_with_unknown_context()
-> anyhow::Result<()> {
    let root_source = format!(
        "load(\"{LABEL}\", \"workloads\")\n\
         def _resources(context: RenderContext):\n    workloads.deployment(context=context, cpu=7)\n"
    );
    let module_source = concat!(
        "def _deployment(context: RenderContext, cpu: str):\n",
        "    pass\n",
        "workloads = struct(deployment=_deployment)\n",
    );
    let (_db, mut graph) = case(&root_source, module_source)?;
    graph.version = "sty-star-graph-v2".to_string();
    graph.profile = v2_profile();
    graph.root.loads[0].bindings[0].local = "workloads".to_string();
    graph.root.loads[0].bindings[0].source = "workloads".to_string();
    let (root_file, module_file) = files(&graph)?;
    let analysis = analyzed(check_star_graph(&graph))?;
    assert_eq!(analysis.checked_arguments(), 1);
    assert_eq!(analysis.unproved_arguments(), 1);
    let [problem] = analysis.problems() else {
        anyhow::bail!("expected one deferred resources argument mismatch: {analysis:?}");
    };
    assert_eq!(problem.file(), root_file);
    assert_eq!(problem.related_file(), module_file);
    assert_eq!(problem.constructor(), "workloads.deployment");
    assert_eq!(problem.field(), "cpu");
    assert_eq!(problem.related_label(), "parameter annotated");
    assert_eq!(slice(&root_source, problem.range()), Some("7"));
    assert_eq!(slice(module_source, problem.related_range()), Some("str"));

    let positive = root_source.replace("cpu=7", "cpu=\"1\"");
    let (_db, mut graph) = case(&positive, module_source)?;
    graph.version = "sty-star-graph-v2".to_string();
    graph.profile = v2_profile();
    graph.root.loads[0].bindings[0].local = "workloads".to_string();
    graph.root.loads[0].bindings[0].source = "workloads".to_string();
    let analysis = analyzed(check_star_graph(&graph))?;
    assert!(analysis.problems().is_empty(), "{analysis:?}");
    assert_eq!(analysis.checked_arguments(), 1);
    assert_eq!(analysis.unproved_arguments(), 1);
    Ok(())
}

fn analyzed(result: StarCheck) -> anyhow::Result<StarAnalysis> {
    match result {
        StarCheck::Partial(analysis) => Ok(analysis),
        StarCheck::Opaque(failure) => {
            anyhow::bail!("expected a bounded analysis, got {failure:?}")
        }
    }
}

fn files(graph: &StarResolvedGraph) -> anyhow::Result<(File, File)> {
    let [module] = graph.modules.as_ref() else {
        anyhow::bail!("expected one test module");
    };
    Ok((graph.root.file, module.source.file))
}

#[test]
fn reports_wrong_primitive_field_in_dead_top_level_branch() -> anyhow::Result<()> {
    let root_source = format!(
        "load(\"{LABEL}\", \"LimitConfig\")\n\nif False:\n    LimitConfig(max_connections=\"wrong\")\n"
    );
    let (_db, graph) = case(&root_source, DECLARATION)?;
    let (root_file, declaration_file) = files(&graph)?;
    let analysis = analyzed(check_star_graph(&graph))?;
    let [problem] = analysis.problems() else {
        anyhow::bail!("expected one dead-branch type problem: {analysis:?}");
    };
    assert_eq!(analysis.checked_arguments(), 1);
    assert_eq!(analysis.unproved_arguments(), 0);
    assert_eq!(problem.file(), root_file);
    assert_eq!(problem.related_file(), declaration_file);
    assert_eq!(slice(&root_source, problem.range()), Some("\"wrong\""));
    assert_eq!(slice(DECLARATION, problem.related_range()), Some("int"));
    assert_eq!(problem.constructor(), "LimitConfig");
    assert_eq!(problem.field(), "max_connections");
    assert_eq!(
        problem.actual(),
        &StarKnownType::Primitive(StarPrimitive::Str)
    );
    assert_eq!(
        problem.expected(),
        &StarKnownType::Primitive(StarPrimitive::Int)
    );
    assert_eq!(
        problem.to_string(),
        "LimitConfig.max_connections, expected int, got str"
    );
    Ok(())
}

#[test]
fn reports_dead_branch_mismatch_in_a_loaded_module_with_owning_files() -> anyhow::Result<()> {
    let usage_id = "//example:usage.star";
    let root_source = format!("load(\"{usage_id}\", \"Flag\")\n0\n");
    let usage_source = format!(
        "load(\"{LABEL}\", \"LimitConfig\")\nFlag = 1\nif False:\n    LimitConfig(max_connections=\"wrong\")\n"
    );
    let (db, root) = test_db(&[
        ("root.star", &root_source),
        ("limits.star", DECLARATION),
        ("usage.star", &usage_source),
    ])?;
    let root_file = system_path_to_file(&db, root.join("root.star"))?;
    let limits_file = system_path_to_file(&db, root.join("limits.star"))?;
    let usage_file = system_path_to_file(&db, root.join("usage.star"))?;
    let graph = StarResolvedGraph {
        version: "sty-star-graph-v1".to_string(),
        profile: profile(),
        root: StarSource {
            file: root_file,
            text: root_source.clone(),
            loads: Box::new([StarDirectLoad {
                module_id: usage_id.to_string(),
                label_range: span(&root_source, &format!("\"{usage_id}\""))?,
                bindings: Box::new([StarLoadBinding {
                    local: "Flag".to_string(),
                    source: "Flag".to_string(),
                }]),
            }]),
        },
        modules: Box::new([
            StarModule {
                id: LABEL.to_string(),
                source: StarSource {
                    file: limits_file,
                    text: DECLARATION.to_string(),
                    loads: Box::new([]),
                },
            },
            StarModule {
                id: usage_id.to_string(),
                source: StarSource {
                    file: usage_file,
                    text: usage_source.clone(),
                    loads: Box::new([StarDirectLoad {
                        module_id: LABEL.to_string(),
                        label_range: span(&usage_source, &format!("\"{LABEL}\""))?,
                        bindings: Box::new([StarLoadBinding {
                            local: "LimitConfig".to_string(),
                            source: "LimitConfig".to_string(),
                        }]),
                    }]),
                },
            },
        ]),
    };
    let analysis = analyzed(check_star_graph(&graph))?;
    let [problem] = analysis.problems() else {
        anyhow::bail!("expected loaded-source mismatch: {analysis:?}");
    };
    assert_eq!(problem.file(), usage_file);
    assert_eq!(problem.related_file(), limits_file);
    assert_eq!(slice(&usage_source, problem.range()), Some("\"wrong\""));
    assert_eq!(slice(DECLARATION, problem.related_range()), Some("int"));
    assert_eq!(analysis.checked_arguments(), 1);
    Ok(())
}

#[test]
fn valid_literal_passes_and_unknown_argument_remains_unproved() -> anyhow::Result<()> {
    let root_source = format!(
        "load(\"{LABEL}\", \"LimitConfig\")\ncurrent = 5\n\nif False:\n    LimitConfig(max_connections=4)\n    LimitConfig(max_connections=current)\n"
    );
    let (_db, graph) = case(&root_source, DECLARATION)?;
    let analysis = analyzed(check_star_graph(&graph))?;
    assert!(analysis.problems().is_empty());
    assert_eq!(analysis.checked_arguments(), 1);
    assert_eq!(analysis.unproved_arguments(), 1);
    Ok(())
}

#[test]
fn builtin_record_declares_the_same_named_primitive_fields() -> anyhow::Result<()> {
    let root_source = format!(
        "load(\"{LABEL}\", alias=\"LimitConfig\")\nif False:\n    alias(max_connections=\"wrong\")\n"
    );
    let module_source = "LimitConfig = record(max_connections=int)\n";
    let (_db, mut graph) = case(&root_source, module_source)?;
    graph.root.loads[0].bindings[0].local = "alias".to_string();
    let analysis = analyzed(check_star_graph(&graph))?;
    let [problem] = analysis.problems() else {
        anyhow::bail!("expected builtin record field mismatch: {analysis:?}");
    };
    assert_eq!(problem.constructor(), "alias");
    assert_eq!(slice(module_source, problem.related_range()), Some("int"));
    Ok(())
}

#[test]
fn primitive_fields_remain_proved_in_mixed_records() -> anyhow::Result<()> {
    let root_source = format!(
        "load(\"{LABEL}\", \"LimitConfig\")\nif False:\n    LimitConfig(limit=\"wrong\", other=None, tags=[])\n"
    );
    let module_source =
        "Other = record(value=str)\nLimitConfig = record(limit=int, other=Other, tags=list[str])\n";
    let (_db, graph) = case(&root_source, module_source)?;
    let analysis = analyzed(check_star_graph(&graph))?;
    let [primitive, nominal] = analysis.problems() else {
        anyhow::bail!("expected primitive and nominal field mismatches: {analysis:?}");
    };
    assert_eq!(primitive.field(), "limit");
    assert_eq!(slice(&root_source, primitive.range()), Some("\"wrong\""));
    assert_eq!(slice(module_source, primitive.related_range()), Some("int"));
    assert_eq!(nominal.field(), "other");
    assert_eq!(slice(&root_source, nominal.range()), Some("None"));
    assert_eq!(slice(module_source, nominal.related_range()), Some("Other"));
    assert_eq!(analysis.checked_arguments(), 2);
    assert_eq!(analysis.unproved_arguments(), 1);
    Ok(())
}

#[test]
fn same_shaped_records_keep_distinct_declared_types() -> anyhow::Result<()> {
    let root_source = format!(
        "load(\"{LABEL}\", \"Envelope\", \"Right\")\nif False:\n    Envelope(item=Right(value=\"right\"))\n"
    );
    let module_source =
        "Left = record(value=str)\nRight = record(value=str)\nEnvelope = record(item=Left)\n";
    let (_db, mut graph) = case(&root_source, module_source)?;
    graph.root.loads[0].bindings = Box::new([
        StarLoadBinding {
            local: "Envelope".to_string(),
            source: "Envelope".to_string(),
        },
        StarLoadBinding {
            local: "Right".to_string(),
            source: "Right".to_string(),
        },
    ]);
    let analysis = analyzed(check_star_graph(&graph))?;
    let [problem] = analysis.problems() else {
        anyhow::bail!("expected distinct nominal record mismatch: {analysis:?}");
    };
    assert_eq!(problem.field(), "item");
    assert_eq!(
        slice(&root_source, problem.range()),
        Some("Right(value=\"right\")")
    );
    assert_eq!(slice(module_source, problem.related_range()), Some("Left"));
    assert_eq!(problem.expected().to_string(), "Left");
    assert_eq!(problem.actual().to_string(), "Right");
    Ok(())
}

#[test]
fn nominal_unions_and_list_literals_check_each_known_alternative() -> anyhow::Result<()> {
    let root_source = format!(
        "load(\"{LABEL}\", \"Left\", \"Right\", \"Envelope\")\nunknown = native_value()\nif False:\n    Envelope(choice=None, slots=[Left(value=\"ok\"), None])\n    Envelope(choice=Left(value=\"ok\"), slots=[Left(value=\"ok\")])\n    Envelope(choice=Right(value=\"bad\"), slots=[Right(value=\"bad\")])\n    Envelope(choice=unknown, slots=[])\n"
    );
    let module_source = "Left = record(value=str)\nRight = record(value=str)\nOptional = Left | None\nEnvelope = record(choice=Optional, slots=list[Optional])\n";
    let (_db, mut graph) = case(&root_source, module_source)?;
    graph.root.loads[0].bindings = Box::new([
        StarLoadBinding {
            local: "Left".to_string(),
            source: "Left".to_string(),
        },
        StarLoadBinding {
            local: "Right".to_string(),
            source: "Right".to_string(),
        },
        StarLoadBinding {
            local: "Envelope".to_string(),
            source: "Envelope".to_string(),
        },
    ]);
    let analysis = analyzed(check_star_graph(&graph))?;
    let [choice, slots] = analysis.problems() else {
        anyhow::bail!("expected two nominal mismatches: {analysis:?}");
    };
    assert_eq!(choice.field(), "choice");
    assert_eq!(slots.field(), "slots");
    assert_eq!(choice.expected().to_string(), "Left | None");
    assert_eq!(slots.expected().to_string(), "list[Left | None]");
    assert_eq!(choice.actual().to_string(), "Right");
    assert_eq!(slots.actual().to_string(), "list[Right]");
    assert_eq!(analysis.unproved_arguments(), 2);
    Ok(())
}

#[test]
fn root_local_record_is_visible_only_after_its_source_declaration() -> anyhow::Result<()> {
    let source = "if False:\n    Local(item=Other(value=\"x\"))\nOther = record(value=str)\nLocal = record(item=Other)\nif False:\n    Local(item=\"wrong\")\n";
    let (_db, graph) = root_only(source)?;
    let analysis = analyzed(check_star_graph(&graph))?;
    let [problem] = analysis.problems() else {
        anyhow::bail!("expected only the call after local declaration: {analysis:?}");
    };
    assert_eq!(problem.field(), "item");
    assert_eq!(slice(source, problem.range()), Some("\"wrong\""));
    assert_eq!(problem.expected().to_string(), "Other");
    Ok(())
}

#[test]
fn different_load_ids_keep_distinct_nominal_types_for_one_physical_file() -> anyhow::Result<()> {
    let first_id = "//example:first.star";
    let second_id = "//example:second.star";
    let root_source = format!(
        "load(\"{first_id}\", first=\"Config\")\nload(\"{second_id}\", second=\"Config\")\nHolder = record(item=first)\nif False:\n    Holder(item=second(value=\"ok\"))\n"
    );
    let module_source = "Config = record(value=str)\n";
    let (db, root) = test_db(&[("root.star", &root_source), ("shared.star", module_source)])?;
    let root_file = system_path_to_file(&db, root.join("root.star"))?;
    let shared_file = system_path_to_file(&db, root.join("shared.star"))?;
    let graph = StarResolvedGraph {
        version: "sty-star-graph-v1".to_string(),
        profile: profile(),
        root: StarSource {
            file: root_file,
            text: root_source.clone(),
            loads: Box::new([
                StarDirectLoad {
                    module_id: first_id.to_string(),
                    label_range: span(&root_source, &format!("\"{first_id}\""))?,
                    bindings: Box::new([StarLoadBinding {
                        local: "first".to_string(),
                        source: "Config".to_string(),
                    }]),
                },
                StarDirectLoad {
                    module_id: second_id.to_string(),
                    label_range: span(&root_source, &format!("\"{second_id}\""))?,
                    bindings: Box::new([StarLoadBinding {
                        local: "second".to_string(),
                        source: "Config".to_string(),
                    }]),
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
    let analysis = analyzed(check_star_graph(&graph))?;
    let [problem] = analysis.problems() else {
        anyhow::bail!("expected distinct logical load identities: {analysis:?}");
    };
    assert_eq!(problem.file(), root_file);
    assert_eq!(problem.related_file(), root_file);
    assert_eq!(slice(&root_source, problem.related_range()), Some("first"));
    assert_eq!(problem.expected().to_string(), "Config");
    assert_eq!(problem.actual().to_string(), "Config");
    let message = problem.to_string();
    assert!(message.contains(first_id), "{message}");
    assert!(message.contains(second_id), "{message}");
    Ok(())
}

#[test]
fn transitive_import_keeps_the_original_record_identity_and_type_alias() -> anyhow::Result<()> {
    let base_id = "//example:base.star";
    let alias_id = "//example:alias.star";
    let base_source = "Base = record(value=str)\n";
    let alias_source =
        format!("load(\"{base_id}\", \"Base\")\nAgain = Base\nOptional = Again | None\n");
    let root_source = format!(
        "load(\"{alias_id}\", \"Again\", \"Optional\")\nLocal = record(item=Optional)\nif False:\n    Local(item=Again(value=\"ok\"))\n    Local(item=None)\n    Local(item=\"wrong\")\n"
    );
    let (db, root) = test_db(&[
        ("root.star", &root_source),
        ("base.star", base_source),
        ("alias.star", &alias_source),
    ])?;
    let root_file = system_path_to_file(&db, root.join("root.star"))?;
    let base_file = system_path_to_file(&db, root.join("base.star"))?;
    let alias_file = system_path_to_file(&db, root.join("alias.star"))?;
    let graph = StarResolvedGraph {
        version: "sty-star-graph-v1".to_string(),
        profile: profile(),
        root: StarSource {
            file: root_file,
            text: root_source.clone(),
            loads: Box::new([StarDirectLoad {
                module_id: alias_id.to_string(),
                label_range: span(&root_source, &format!("\"{alias_id}\""))?,
                bindings: Box::new([
                    StarLoadBinding {
                        local: "Again".to_string(),
                        source: "Again".to_string(),
                    },
                    StarLoadBinding {
                        local: "Optional".to_string(),
                        source: "Optional".to_string(),
                    },
                ]),
            }]),
        },
        modules: Box::new([
            StarModule {
                id: alias_id.to_string(),
                source: StarSource {
                    file: alias_file,
                    text: alias_source.clone(),
                    loads: Box::new([StarDirectLoad {
                        module_id: base_id.to_string(),
                        label_range: span(&alias_source, &format!("\"{base_id}\""))?,
                        bindings: Box::new([StarLoadBinding {
                            local: "Base".to_string(),
                            source: "Base".to_string(),
                        }]),
                    }]),
                },
            },
            StarModule {
                id: base_id.to_string(),
                source: StarSource {
                    file: base_file,
                    text: base_source.to_string(),
                    loads: Box::new([]),
                },
            },
        ]),
    };
    let analysis = analyzed(check_star_graph(&graph))?;
    let [problem] = analysis.problems() else {
        anyhow::bail!("expected one wrong argument after transitive import: {analysis:?}");
    };
    assert_eq!(problem.expected().to_string(), "Base | None");
    assert_eq!(problem.actual().to_string(), "str");
    assert_eq!(slice(&root_source, problem.range()), Some("\"wrong\""));
    assert_eq!(
        slice(&root_source, problem.related_range()),
        Some("Optional")
    );
    Ok(())
}

#[test]
fn bare_loaded_binding_is_not_reexported_without_a_host_attestation() -> anyhow::Result<()> {
    let base_id = "//example:base.star";
    let alias_id = "//example:alias.star";
    let base_source = "Base = record(value=str)\n";
    let alias_source = format!("load(\"{base_id}\", \"Base\")\n");
    let root_source = format!("load(\"{alias_id}\", \"Base\")\nif False:\n    Base(value=5)\n");
    let (db, root) = test_db(&[
        ("root.star", &root_source),
        ("base.star", base_source),
        ("alias.star", &alias_source),
    ])?;
    let root_file = system_path_to_file(&db, root.join("root.star"))?;
    let base_file = system_path_to_file(&db, root.join("base.star"))?;
    let alias_file = system_path_to_file(&db, root.join("alias.star"))?;
    let graph = StarResolvedGraph {
        version: "sty-star-graph-v1".to_string(),
        profile: profile(),
        root: StarSource {
            file: root_file,
            text: root_source.clone(),
            loads: Box::new([StarDirectLoad {
                module_id: alias_id.to_string(),
                label_range: span(&root_source, &format!("\"{alias_id}\""))?,
                bindings: Box::new([StarLoadBinding {
                    local: "Base".to_string(),
                    source: "Base".to_string(),
                }]),
            }]),
        },
        modules: Box::new([
            StarModule {
                id: alias_id.to_string(),
                source: StarSource {
                    file: alias_file,
                    text: alias_source.clone(),
                    loads: Box::new([StarDirectLoad {
                        module_id: base_id.to_string(),
                        label_range: span(&alias_source, &format!("\"{base_id}\""))?,
                        bindings: Box::new([StarLoadBinding {
                            local: "Base".to_string(),
                            source: "Base".to_string(),
                        }]),
                    }]),
                },
            },
            StarModule {
                id: base_id.to_string(),
                source: StarSource {
                    file: base_file,
                    text: base_source.to_string(),
                    loads: Box::new([]),
                },
            },
        ]),
    };
    let analysis = analyzed(check_star_graph(&graph))?;
    assert!(analysis.problems().is_empty(), "{analysis:?}");
    assert_eq!(analysis.checked_arguments(), 0);
    Ok(())
}

#[test]
fn nominal_constructor_names_in_deferred_lexical_scopes_are_unproved() -> anyhow::Result<()> {
    let root_source = format!(
        "load(\"{LABEL}\", \"Envelope\", \"Right\")\ndef unused(Envelope):\n    return Envelope(item=Right(value=\"wrong\"))\ncallback = lambda Envelope: Envelope(item=Right(value=\"wrong\"))\n"
    );
    let module_source =
        "Left = record(value=str)\nRight = record(value=str)\nEnvelope = record(item=Left)\n";
    let (_db, mut graph) = case(&root_source, module_source)?;
    graph.root.loads[0].bindings = Box::new([
        StarLoadBinding {
            local: "Envelope".to_string(),
            source: "Envelope".to_string(),
        },
        StarLoadBinding {
            local: "Right".to_string(),
            source: "Right".to_string(),
        },
    ]);
    let analysis = analyzed(check_star_graph(&graph))?;
    assert!(analysis.problems().is_empty(), "{analysis:?}");
    assert_eq!(analysis.checked_arguments(), 0);
    Ok(())
}

#[test]
fn declaration_rebinding_or_shadowed_builtin_cannot_lend_a_false_type() -> anyhow::Result<()> {
    let root_source = format!(
        "load(\"{LABEL}\", \"LimitConfig\")\nif False:\n    LimitConfig(max_connections=\"wrong\")\n"
    );
    for module_source in [
        "def validate(value):\n    pass\nLimitConfig = wrapper_record(validate, max_connections=int)\nLimitConfig = wrapper_record(validate, max_connections=str)\n",
        "def validate(value):\n    pass\nint = str\nLimitConfig = wrapper_record(validate, max_connections=int)\n",
        "def validate(value):\n    pass\nwrapper_record = record\nLimitConfig = wrapper_record(validate, max_connections=int)\n",
    ] {
        let (_db, graph) = case(&root_source, module_source)?;
        let analysis = analyzed(check_star_graph(&graph))?;
        assert!(
            analysis.problems().is_empty(),
            "shadowed declaration must remain unproved: {analysis:?}"
        );
        assert_eq!(analysis.checked_arguments(), 0);
    }
    Ok(())
}

#[test]
fn record_validator_must_be_a_preceding_unshadowed_function() -> anyhow::Result<()> {
    let root_source = format!(
        "load(\"{LABEL}\", \"LimitConfig\")\nif False:\n    LimitConfig(max_connections=\"wrong\")\n"
    );
    for module_source in [
        "LimitConfig = wrapper_record(0, max_connections=int)\n",
        "LimitConfig = wrapper_record(validate, max_connections=int)\ndef validate(value):\n    pass\n",
        "def validate(value):\n    pass\nvalidate = 0\nLimitConfig = wrapper_record(validate, max_connections=int)\n",
    ] {
        let (_db, graph) = case(&root_source, module_source)?;
        let analysis = analyzed(check_star_graph(&graph))?;
        assert!(analysis.problems().is_empty());
        assert_eq!(analysis.checked_arguments(), 0);
    }
    Ok(())
}

#[test]
fn root_alias_rebinding_and_function_parameter_shadow_do_not_leak_types() -> anyhow::Result<()> {
    let root_source = format!(
        "load(\"{LABEL}\", \"LimitConfig\")\nif False:\n    LimitConfig = another\n    LimitConfig(max_connections=\"wrong\")\n"
    );
    let (_db, graph) = case(&root_source, DECLARATION)?;
    let analysis = analyzed(check_star_graph(&graph))?;
    assert!(analysis.problems().is_empty());
    assert_eq!(analysis.checked_arguments(), 0);

    let root_source = format!(
        "load(\"{LABEL}\", \"LimitConfig\")\n\ndef unused(LimitConfig):\n    return LimitConfig(max_connections=\"wrong\")\n"
    );
    let (_db, graph) = case(&root_source, DECLARATION)?;
    let analysis = analyzed(check_star_graph(&graph))?;
    assert!(analysis.problems().is_empty());
    assert_eq!(analysis.checked_arguments(), 0);
    Ok(())
}

#[test]
fn comprehension_and_lambda_bindings_do_not_borrow_loaded_constructor_types() -> anyhow::Result<()>
{
    let root_source = format!(
        "load(\"{LABEL}\", \"LimitConfig\")\nvalues = []\nignored = [LimitConfig(max_connections=\"wrong\") for LimitConfig in values]\ncallback = lambda LimitConfig: LimitConfig(max_connections=\"wrong\")\n"
    );
    let (_db, graph) = case(&root_source, DECLARATION)?;
    let analysis = analyzed(check_star_graph(&graph))?;
    assert!(analysis.problems().is_empty());
    assert_eq!(analysis.checked_arguments(), 0);
    Ok(())
}

#[test]
fn later_root_local_constructor_cannot_type_an_earlier_call() -> anyhow::Result<()> {
    let root_source = "if False:\n    LocalConfig(max_connections=\"wrong\")\nLocalConfig = record(max_connections=int)\n";
    let (_db, graph) = root_only(root_source)?;
    let analysis = analyzed(check_star_graph(&graph))?;
    assert!(analysis.problems().is_empty());
    assert_eq!(analysis.checked_arguments(), 0);
    Ok(())
}

#[test]
fn rejects_stale_load_aliases_and_missing_graph_targets_before_analysis() -> anyhow::Result<()> {
    let root_source = format!(
        "load(\"{LABEL}\", \"LimitConfig\")\nif False:\n    LimitConfig(max_connections=\"wrong\")\n"
    );
    let (_db, mut graph) = case(&root_source, DECLARATION)?;
    let root_file = graph.root.file;
    graph.root.loads[0].bindings[0].local = "stale".to_string();
    let StarCheck::Opaque(failure) = check_star_graph(&graph) else {
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
    let StarCheck::Opaque(failure) = check_star_graph(&graph) else {
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
    let (_db, graph) = case(&root_source, DECLARATION)?;
    let StarCheck::Opaque(failure) = check_star_graph(&graph) else {
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
    let (_db, mut graph) = case(&root_source, module_source)?;
    let [load] = graph.root.loads.as_mut() else {
        anyhow::bail!("expected the direct root load");
    };
    let [binding] = load.bindings.as_mut() else {
        anyhow::bail!("expected one root load binding");
    };
    binding.local = "_HiddenConfig".to_string();
    binding.source = "_HiddenConfig".to_string();
    let StarCheck::Opaque(failure) = check_star_graph(&graph) else {
        anyhow::bail!("private imported symbol yielded trusted precision");
    };
    assert_eq!(failure.file(), graph.root.file);
    assert!(matches!(failure.reason(), StarFailureReason::PrivateImport));

    let root_source = format!("load(\"{LABEL}\", \"LimitConfig\")\n");
    let module_source =
        format!("load(\"{LABEL}\", \"LimitConfig\")\nLimitConfig = record(max_connections=int)\n");
    let (_db, mut graph) = case(&root_source, &module_source)?;
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
    let StarCheck::Opaque(failure) = check_star_graph(&graph) else {
        anyhow::bail!("cyclic imported symbol yielded trusted precision");
    };
    assert_eq!(failure.file(), module_file);
    assert!(matches!(failure.reason(), StarFailureReason::LoadCycle));
    Ok(())
}

#[test]
fn unsupported_profile_and_duplicate_module_ids_fail_closed() -> anyhow::Result<()> {
    let root_source = format!("load(\"{LABEL}\", \"LimitConfig\")\n");
    let (_db, mut graph) = case(&root_source, DECLARATION)?;
    graph.profile.special_forms[1].field_types = "arbitrary_python_keyword".to_string();
    let StarCheck::Opaque(failure) = check_star_graph(&graph) else {
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
    let StarCheck::Opaque(failure) = check_star_graph(&graph) else {
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
    let (_db, mut graph) = case(&root_source, DECLARATION)?;
    let physical_file = graph.root.file;
    graph.modules[0].source.file = physical_file;
    let StarCheck::Opaque(failure) = check_star_graph(&graph) else {
        anyhow::bail!("ambiguous physical source yielded a typed source span");
    };
    assert_eq!(failure.file(), physical_file);
    assert!(matches!(
        failure.reason(),
        StarFailureReason::ConflictingSnapshot
    ));
    Ok(())
}
