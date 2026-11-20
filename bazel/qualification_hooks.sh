#!/usr/bin/env bash
set -euo pipefail

runfiles="${RUNFILES_DIR:-$0.runfiles}"
runfiles="$(cd -- "$runfiles" && pwd -P)"
uv="$runfiles/$1"
rustfmt="$runfiles/$2"
shift 2
if [[ $# -eq 0 ]]; then
    echo "Pass every changed file to the repository's qualification hooks." >&2
    exit 64
fi
if [[ ! -x "$uv" || ! -x "$rustfmt" ]]; then
    echo "The declared UV and rustfmt executables are missing from runfiles." >&2
    exit 1
fi
: "${BUILD_WORKSPACE_DIRECTORY:?Run this target with bazel run in the mirrored checkout}"
export PATH="$(dirname -- "$rustfmt"):$PATH"
cd -- "$BUILD_WORKSPACE_DIRECTORY"
exec "$uv" run --only-dev --locked prek run --files "$@"
