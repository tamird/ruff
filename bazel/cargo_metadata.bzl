"""Workspace manifest inputs for Cargo-aware lint queries."""

def cargo_metadata_files(extra_roots = []):
    """Expose manifest and conventional Cargo target roots without compiling them."""
    native.filegroup(
        name = "cargo_metadata_files",
        srcs = ["Cargo.toml"] + native.glob([
            "build.rs",
            "src/lib.rs",
            "src/main.rs",
            "src/bin/*.rs",
            "src/bin/*/main.rs",
            "benches/*.rs",
            "benches/*/main.rs",
            "examples/*.rs",
            "examples/*/main.rs",
            "tests/*.rs",
            "tests/*/main.rs",
        ], allow_empty = True) + extra_roots,
        visibility = ["//visibility:public"],
    )
