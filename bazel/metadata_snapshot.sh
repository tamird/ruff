#!/usr/bin/env bash
set -euo pipefail
cd "$BUILD_WORKSPACE_DIRECTORY"
bazel mod deps --lockfile_mode=update
printf 'BEGIN_MODULE_LOCK\n'
base64 "$BUILD_WORKSPACE_DIRECTORY/MODULE.bazel.lock"
printf 'END_MODULE_LOCK\n'
sha256sum "$BUILD_WORKSPACE_DIRECTORY/MODULE.bazel.lock"
