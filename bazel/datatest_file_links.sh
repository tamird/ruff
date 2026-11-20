#!/usr/bin/env bash
set -euo pipefail

mdtest="$PWD/$1"
fixture="$PWD/$2"
work_directory="$(mktemp -d "$TEST_TMPDIR/datatest-links.XXXXXX")"
trap 'rm -rf -- "$work_directory"' EXIT
resources="$work_directory/crates/ty_python_semantic/resources"
mkdir -p -- "$resources/mdtest" "$resources/lint_docs"
ln -s -- "$fixture" "$resources/mdtest/linked.md"
ln -s -- "$fixture" "$resources/lint_docs/invalid-argument-type.md"
ln -s -- "$resources/missing.md" "$resources/mdtest/broken.md"
ln -s -- "$resources/mdtest" "$resources/mdtest/cycle"

# Discovery must include file links, skip broken links and avoid directory cycles.
__DATATEST_CWD="$work_directory" "$mdtest" --test-threads=2 --list > "$work_directory/list.txt"
cat "$work_directory/list.txt"
grep -Fx 'mdtest::linked.md: test' "$work_directory/list.txt"
grep -Fx 'lint_doc::invalid-argument-type.md: test' "$work_directory/list.txt"
if [[ "$(grep -c ': test$' "$work_directory/list.txt")" != 2 ]]; then
    printf 'Expected exactly the two linked fixtures.\n' >&2
    exit 1
fi
__DATATEST_CWD="$work_directory" "$mdtest" --test-threads=2
