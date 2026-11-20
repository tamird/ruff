#!/usr/bin/env bash
set -euo pipefail

mdtest="$1"
uv="$2"
shift 2
# Bazel rootpath arguments resolve from the test's directory-based runfiles root.
uv_directory="$(cd -- "$(dirname -- "$uv")" && pwd -P)"
export PATH="$uv_directory:$PATH"
exec "$mdtest" "$@"
