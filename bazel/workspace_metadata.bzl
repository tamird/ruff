"""Expose Cargo-resolved workspace features to first-party Rust targets."""

def _resolved_features(crate, conditions):
    features = crate["common_attrs"].get("crate_features", [])
    # The canonical lock compacts unconditional Select values to a list.
    if type(features) == "list":
        return {"common": features, "selects": {}}
    common = features["common"]
    by_triple = {}
    for condition, values in features["selects"].items():
        if condition not in conditions:
            fail("Unknown crate_universe feature condition: " + condition)
        # Use the generator's cfg interpretation, including overlapping conditions.
        for triple in conditions[condition]:
            selected = by_triple.setdefault(triple, {})
            for feature in values:
                if feature not in common:
                    selected[feature] = True
    return {
        "common": common,
        "selects": {triple: sorted(values) for triple, values in by_triple.items()},
    }

def _metadata_impl(ctx):
    # Resolve the hub first: crate_universe may refresh its renderer metadata.
    ctx.read(ctx.attr.hub)
    metadata = json.decode(ctx.read(ctx.attr.lockfile))
    crates = {}
    for crate_id, package in metadata["workspace_members"].items():
        crate = metadata["crates"][crate_id]
        libraries = []
        script = None
        for target in crate["targets"]:
            if "BuildScript" in target:
                script = target["BuildScript"]["crate_root"]
            for kind in ["Library", "ProcMacro"]:
                if kind in target:
                    libraries.append((target[kind], kind == "ProcMacro"))
        if not libraries:
            continue
        if len(libraries) != 1:
            fail("Expected one library target for " + package)
        library, proc_macro = libraries[0]
        crates[package] = {
            "features": _resolved_features(crate, metadata["conditions"]),
            "version": crate["version"],
            "crate_name": library["crate_name"],
            "crate_root": library["crate_root"],
            "proc_macro": proc_macro,
            "build_script": script,
        }
    ctx.file("BUILD.bazel", "exports_files([\"crates.bzl\"])\n")
    ctx.file(
        "crates.bzl",
        "CRATES = " + repr(crates) + "\nWORKSPACE_MEMBERS = " + repr(sorted(metadata["workspace_members"].values())) + "\n",
    )

_metadata = repository_rule(
    implementation = _metadata_impl,
    attrs = {
        "hub": attr.label(mandatory = True, allow_single_file = True),
        "lockfile": attr.label(mandatory = True, allow_single_file = True),
    },
)

def _extension_impl(ctx):
    for module in ctx.modules:
        for tag in module.tags.from_cargo:
            _metadata(name = tag.name, hub = tag.hub, lockfile = tag.lockfile)

workspace_metadata = module_extension(
    implementation = _extension_impl,
    tag_classes = {
        "from_cargo": tag_class(attrs = {
            "name": attr.string(mandatory = True),
            "hub": attr.label(mandatory = True),
            "lockfile": attr.label(mandatory = True),
        }),
    },
)
