"""Independent Markdown test actions backed by one native harness binary."""

load("@rules_shell//shell:sh_test.bzl", "sh_test")

def _selector_inventory_impl(ctx):
    inventory = ctx.actions.declare_file(ctx.label.name + ".txt")
    ctx.actions.write(inventory, "\n".join(ctx.attr.selectors) + "\n")
    return [DefaultInfo(files = depset([inventory]))]

_selector_inventory = rule(
    implementation = _selector_inventory_impl,
    attrs = {"selectors": attr.string_list(mandatory = True)},
)

def mdtest_suite(name, harness, data, fixture_roots, test_cpus, test_options):
    """Derive exact native selectors from the harness's declared source roots.

    fixture_roots maps native test function names to package-relative directories.
    The inventory test checks this declaration against the native harness itself.
    test_options carries the shared Bazel test environment, resources and timeout.
    """
    if not fixture_roots:
        fail("No Markdown fixture roots declared")
    selectors = {}
    targets = {}
    for function, root in sorted(fixture_roots.items()):
        prefix = root + "/"
        found = False
        for path in sorted(data):
            if not path.startswith(prefix) or not path.endswith(".md"):
                continue
            found = True
            selector = function + "::" + path[len(prefix):]
            if selector in selectors:
                fail("Duplicate Markdown selector: {}".format(selector))
            target = name + "/" + selector.replace("::", "/")
            if target in targets:
                fail("Markdown target collision: {} and {}".format(targets[target], selector))
            selectors[selector] = target
            targets[target] = selector
        if not found:
            fail("Markdown root has no fixtures: {}".format(root))

    tests = []
    for selector, target in sorted(selectors.items()):
        sh_test(
            name = target,
            srcs = ["//bazel:mdtest_fixture.sh"],
            args = ["fixture", "$(rootpath {})".format(harness), selector, str(test_cpus)],
            data = [harness],
            visibility = ["//visibility:public"],
            **test_options
        )
        tests.append(":" + target)

    inventory_data = name + "_selectors"
    _selector_inventory(
        name = inventory_data,
        selectors = sorted(selectors),
    )
    inventory_test = name + "_inventory"
    sh_test(
        name = inventory_test,
        srcs = ["//bazel:mdtest_fixture.sh"],
        args = [
            "inventory",
            "$(rootpath {})".format(harness),
            "$(rootpath :{})".format(inventory_data),
            str(test_cpus),
        ],
        data = [harness, ":" + inventory_data],
        **test_options
    )
    native.test_suite(
        name = name,
        tests = tests + [":" + inventory_test],
        visibility = ["//visibility:public"],
    )
