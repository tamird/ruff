# Native ty builds with Bazel

The Bazel targets use the existing Ruff Cargo workspace and Cargo.lock.
crate_universe resolves third-party dependencies, aliases, editions and features.
Its canonical `cargo-bazel.json` rendering metadata also supplies first-party
features. Workspace dependency edges are declared in the small crate BUILD files.
Do not edit either generated lock file by hand or create a separate Cargo workspace.

The Rust toolchain matches rust-toolchain.toml (currently 1.100.0).
Qualification selects `cargo-dev` explicitly: optimization level 1, line-table
debug information and LTO off, as declared by Cargo.toml's development profile.
The package-specific optimization level 3 overrides for Insta, Similar and Salsa
are carried through crate_universe annotations with development assertions and
overflow checks preserved. The explicit profile also enables both checks,
matching Cargo's development defaults. Default fastbuild otherwise retains the
upstream unoptimized toolchain behavior; select `cargo-dev` for qualification. This does not claim release or dbg profile
parity. The core unit target is:

```sh
bb remote --git_fetch_url=https://github.com/tamird/ruff.git test --config=buildbuddy --config=cargo-dev --lockfile_mode=error //crates/ty_python_core:unit_tests
```

`bb login` selects the authorized personal BuildBuddy account. Keys do not belong
in rc files or command arguments. The `buildbuddy` profile selects separate Linux
AMD64 execution and target platforms, a digest-pinned worker image and the
hermetic Zig C toolchain. Remote Bazel also moves loading and dependency analysis
off the local machine. Use the CLI's default Git workspace mirroring when testing
uncommitted changes; selecting run_from_commit instead tests that clean commit.

For dependency updates, run the canonical generator remotely:

```sh
bb remote --git_fetch_url=https://github.com/tamird/ruff.git build --config=buildbuddy --config=cargo-dev --lockfile_mode=update --repo_env=CARGO_BAZEL_REPIN=1 //bazel:dependency_metadata
```

Review the downloaded `resolved-cargo-bazel.json` before copying it to
`bazel/cargo-bazel.json`. Cargo.lock remains the Cargo dependency authority.
The module lock is written when Bazel finishes; the metadata snapshot target
exports that completed file for review. Run this step without
`CARGO_BAZEL_REPIN` or the repin command's `--repo_env` override, so the committed
module lock records the normal environment:

```sh
bb remote --git_fetch_url=https://github.com/tamird/ruff.git run --config=buildbuddy --config=cargo-dev --lockfile_mode=update //bazel:metadata_snapshot
```

Qualification commands use `--lockfile_mode=error` after these normal-environment
generator outputs have been reviewed and imported; a passing build must not rely
on an automatic module-lock update.

The semantic, Markdown and IDE harnesses are also available:

```sh
bb remote --git_fetch_url=https://github.com/tamird/ruff.git test --config=buildbuddy --config=cargo-dev --lockfile_mode=error //crates/ty_python_semantic:unit_tests //crates/ty_python_semantic:mdtests //crates/ty_ide:unit_tests
```

All harnesses reject snapshot changes (`INSTA_UPDATE=no`). Snapshot files and
Markdown resources are declared runfiles; the Markdown harness resolves its
manifest directory at runtime. The `mdtests` suite gives each Markdown fixture
its own test action, reusing one compiled native harness and its shared runfiles.
Its generated selector inventory must exactly match the native `--list` output.
Each action verifies one registered selector and one executed test, preserving
native failures. The shared runfiles can still invalidate several test actions
when a fixture changes; they are not separate fixture trees.

Select a fixture by its generated target, for example:

```sh
bb remote --git_fetch_url=https://github.com/tamird/ruff.git test --config=buildbuddy --config=cargo-dev --lockfile_mode=error //crates/ty_python_semantic:mdtests/mdtest/annotations/union.md
```

Canonical fixture actions reject extra native arguments, Bazel `--test_filter`,
inner-section filters and external-dependency mode. Default external cases remain skipped. For filtered
diagnostics, the explicit manual `mdtest` aggregate target retains the native CLI:

```sh
bb remote --git_fetch_url=https://github.com/tamird/ruff.git test --config=buildbuddy --config=cargo-dev --lockfile_mode=error //crates/ty_python_semantic:mdtest --test_arg=--exact --test_arg=mdtest::annotations/union.md
```

Use the suite for whole-Markdown qualification so fixtures run in separate
processes. Unit targets retain their normal Rust test filters. A passing core
test does not qualify the semantic, Markdown or IDE suites. External Markdown
cases use the separate network-backed gate below.

Formatting and Clippy use the same declared crate graph and the workspace's
`rustfmt.toml`, `clippy.toml` and Cargo lint declarations:

```sh
bb remote --git_fetch_url=https://github.com/tamird/ruff.git test --config=buildbuddy --config=cargo-dev --lockfile_mode=error //:ty_format
bb remote --git_fetch_url=https://github.com/tamird/ruff.git test --config=buildbuddy --config=cargo-dev --lockfile_mode=error --@rules_rust//rust/settings:clippy_flags=-Dwarnings //:ty_clippy
```

The annotation renderer's native feature-name lints query Cargo metadata. Its
Bazel action declares the canonical Cargo/Rustc tools, workspace manifests and
Cargo target roots, and runs Cargo offline with `--no-deps`. The workspace member
list comes from crate_universe; no separate dependency graph or feature-policy
validator is maintained.

These are selected ty targets, not a replacement for the repository's full
workspace qualification. Parser fixture tests and the remaining workspace unit
and corpus targets still need their own declared inputs and targets. External
Markdown cases use the separate gate below.

External-dependency cases use an explicit network-backed gate:

```sh
bb remote --git_fetch_url=https://github.com/tamird/ruff.git test --config=buildbuddy --config=cargo-dev --lockfile_mode=error --cache_test_results=no //crates/ty_python_semantic:mdtest_external
```

Use `bb remote` for this gate: a direct local Bazel invocation would install its
Python fixtures on the local machine. Rust compilation still uses RBE. The wrapper
is Linux AMD64 only; its `no-remote`, `no-cache` and `requires-network` tags run
fixture setup on the Remote Bazel frontend with network access and avoid cached
results. The command also disables Bazel's test-result cache explicitly.

The UV executable is a content-pinned official release. The native fixture
installer requires the checked-in `uv.lock` files and verifies their package
hashes through `uv sync --locked`. Python is selected by each fixture's existing
version requirement; this is not a fully hermetic or pinned-interpreter test.
It uses UV's normal managed caches, not a separate workspace or cache directory.

`datatest-stable` 0.3.3 ignores symlinked files during directory discovery. The
narrow crate annotation admits file links while keeping directory-link traversal
disabled. `//bazel:datatest_file_links` uses the actual Markdown binary to check
file links, broken links and a directory cycle. Remove the dependency patch when
a native datatest release has this behavior; retain the integration control.

The Markdown harness receives `--test-threads=8`, matching its eight-CPU execution
estimate. Pinned libtest-mimic 0.8.1 otherwise uses
`std::thread::available_parallelism()` and does not read `RUST_TEST_THREADS`.
Unit tests also set the standard Rust test environment limit, and Rayon is
bounded to the same budget. The existing per-Markdown-fixture Rayon pool remains
one thread. These scheduling bounds do not change fixtures or solver limits.
The repository's required changed-file hooks run in the mirrored Git checkout:

```sh
bb remote --git_fetch_url=https://github.com/tamird/ruff.git run --config=buildbuddy --config=cargo-dev --lockfile_mode=error //bazel:qualification_hooks -- <each-changed-file>
```

Pass every changed path. This network-backed command uses the pinned UV and
canonical Rust formatter, then delegates to the existing locked `prek` hooks.
It runs uncached on the Remote Bazel frontend through `bb remote`; it does not
make hook installation hermetic or replace the Rust test and Clippy gates.
