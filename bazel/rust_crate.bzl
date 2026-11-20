"""First-party glue; Cargo and crate_universe own dependency versions and features."""

load("@crates//:defs.bzl", "aliases", "all_crate_deps", "crate_edition")
load("@ruff_workspace_metadata//:crates.bzl", "CRATES")
load("@rules_rust//cargo:defs.bzl", "cargo_build_script", "cargo_toml_env_vars", "extract_cargo_lints")
load("@rules_rust//rust:defs.bzl", "rust_binary", "rust_library", "rust_proc_macro", "rust_test")

load(":cargo_metadata.bzl", "cargo_metadata_files")
load(":mdtest.bzl", "mdtest_suite")

# Match harness concurrency to the CPU reservation instead of host CPU discovery.
RUST_TEST_CPUS = 8
RUST_TEST_ENV = {
    "INSTA_UPDATE": "no",
    "INSTA_WORKSPACE_ROOT": ".",
    "RAYON_NUM_THREADS": str(RUST_TEST_CPUS),
    "RUST_TEST_THREADS": str(RUST_TEST_CPUS),
}

def _features(package):
    features = CRATES[package]["features"]
    conditional = features.get("selects", {})
    if not conditional:
        return features.get("common", [])
    return features.get("common", []) + select(
        {"@rules_rust//rust/platform:" + triple: values for triple, values in conditional.items()} | {
            "//conditions:default": [],
        },
    )

def rust_crate(
        name,
        deps = [],
        proc_macro_deps = [],
        compile_data = [],
        rustc_env = {},
        toolchains = [],
        build_deps = [],
        build_dev_deps = False,
        build_data = [],
        build_compile_data = [],
        unit_test = False,
        test_deps = [],
        test_data = [],
        binaries = {}):
    """Declare a workspace library, selected binaries, and an optional unit-test harness."""
    cargo_metadata_files()
    package = native.package_name()
    crate = CRATES[package]
    features = _features(package)
    cargo_toml_env_vars(
        name = "cargo_env",
        src = "Cargo.toml",
        workspace = "//:Cargo.toml",
    )
    extract_cargo_lints(
        name = "cargo_lints",
        manifest = "Cargo.toml",
        workspace = "//:Cargo.toml",
    )
    if crate["build_script"]:
        cargo_build_script(
            name = "build_script",
            srcs = [crate["build_script"]],
            crate_root = crate["build_script"],
            crate_features = features,
            edition = crate_edition(),
            aliases = aliases(build = True, build_proc_macro = True, normal_dev = build_dev_deps),
            deps = all_crate_deps(build = True, normal_dev = build_dev_deps) + build_deps,
            proc_macro_deps = all_crate_deps(build_proc_macro = True),
            data = build_data,
            compile_data = build_compile_data,
            rustc_env_files = [":cargo_env"],
        )
    rule = rust_proc_macro if crate["proc_macro"] else rust_library
    attributes = dict(
        crate_name = crate["crate_name"],
        srcs = native.glob(["src/**/*.rs"]),
        crate_root = crate["crate_root"],
        crate_features = features,
        edition = crate_edition(),
        version = CRATES[package]["version"],
        aliases = aliases(normal = True, proc_macro = True),
        deps = all_crate_deps(normal = True) + deps + ([":build_script"] if crate["build_script"] else []),
        proc_macro_deps = all_crate_deps(proc_macro = True) + proc_macro_deps,
        compile_data = compile_data,
        rustc_env = rustc_env,
        toolchains = toolchains,
        rustc_env_files = [":cargo_env"],
        lint_config = ":cargo_lints",
        visibility = ["//visibility:public"],
    )
    rule(name = name, **attributes)
    for binary, crate_root in binaries.items():
        rust_binary(
            name = binary,
            **(attributes | {
                "crate_name": binary.replace("-", "_"),
                "crate_root": crate_root,
                "deps": attributes["deps"] + [":" + name],
            })
        )
    if unit_test:
        rust_test(
            name = "unit_tests",
            crate = ":" + name,
            lint_config = ":cargo_lints",
            aliases = aliases(normal = True, proc_macro = True, normal_dev = True, proc_macro_dev = True),
            deps = all_crate_deps(normal_dev = True) + test_deps,
            proc_macro_deps = all_crate_deps(proc_macro_dev = True),
            data = test_data,
            env = RUST_TEST_ENV,
            visibility = ["//visibility:public"],
            exec_properties = {
                "test.EstimatedComputeUnits": str(RUST_TEST_CPUS),
                "test.EstimatedMemory": "8GB",
            },
        )


def rust_mdtest(name, deps, data, fixture_roots, suite_name):
    """Build one native harness and distribute its declared fixtures as tests."""
    test_options = {
        "env": RUST_TEST_ENV,
        "exec_properties": {"test.EstimatedComputeUnits": str(RUST_TEST_CPUS), "test.EstimatedMemory": "16GB"},
        "timeout": "long",
    }
    rust_test(
        name = name,
        srcs = ["tests/mdtest.rs"],
        crate_root = "tests/mdtest.rs",
        edition = crate_edition(),
        use_libtest_harness = False,
        args = ["--test-threads={}".format(RUST_TEST_CPUS)],
        crate_features = _features(native.package_name()),
        lint_config = ":cargo_lints",
        aliases = aliases(normal = True, normal_dev = True, proc_macro = True, proc_macro_dev = True),
        deps = all_crate_deps(normal = True, normal_dev = True) + deps,
        proc_macro_deps = all_crate_deps(proc_macro = True, proc_macro_dev = True),
        rustc_env = {"CARGO_MANIFEST_DIR": native.package_name()},
        rustc_env_files = [":cargo_env"],
        data = data,
        tags = ["manual"],
        visibility = ["//visibility:public"],
        **test_options
    )
    mdtest_suite(
        name = suite_name,
        harness = ":" + name,
        data = data,
        fixture_roots = fixture_roots,
        test_cpus = RUST_TEST_CPUS,
        test_options = test_options,
    )
