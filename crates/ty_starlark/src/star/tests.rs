use anyhow::Context as _;
use ruff_db::files::{File, system_path_to_file};
use ruff_text_size::{TextRange, TextSize};

use crate::testing::{TestDb, test_db};

use super::{
    StarAnalysis, StarCheck, StarDirectLoad, StarFailureReason, StarHostProfile, StarIntrinsic,
    StarKnownType, StarLoadBinding, StarModule, StarPrimitive, StarResolvedGraph, StarSource,
    StarSpecialForm, check_star_graph,
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
    graph.version = "sty-star-graph-v3".to_string();
    profile_failure(&graph)?;
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
