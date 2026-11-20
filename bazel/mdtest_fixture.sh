#!/usr/bin/env bash
set -euo pipefail

fail() {
    printf '%s\n' "$*" >&2
    exit 2
}

[[ "$#" == 4 ]] || fail "Use the canonical fixture target without extra test arguments; use :mdtest for filtered diagnostics."
mode="$1"
harness="$2"
selection="$3"
threads="$4"
[[ -z "${MDTEST_TEST_FILTER:-}" ]] || fail "MDTEST_TEST_FILTER selects inner sections; use :mdtest for filtered diagnostics."
[[ -z "${TESTBRIDGE_TEST_ONLY:-}" ]] || fail "Bazel --test_filter is not a fixture selector; use :mdtest with --test_arg for filtered diagnostics."
[[ "${MDTEST_EXTERNAL:-0}" == 0 ]] || fail "Use :mdtest_external through bb remote for network-backed fixtures."

case "$mode" in
    fixture)
        # Pinned libtest-mimic prints exactly '<name>: test' for this list.
        # Comparing strings keeps dots and other selector characters literal.
        listed="$("$harness" --color=never --exact "$selection" --list)"
        [[ "$listed" == "$selection: test" ]] || fail "Expected exactly one native fixture: $selection; listed: $listed"
        printf 'Running native fixture: %s\n' "$selection"
        log="${TEST_TMPDIR:?Bazel must provide the test temporary directory}/native-fixture.log"
        status=0
        "$harness" --color=never --format=pretty --test-threads="$threads" --exact "$selection" > "$log" 2>&1 || status=$?
        completed=0
        while IFS= read -r line || [[ -n "$line" ]]; do
            printf '%s\n' "$line"
            if [[ "$line" == "test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; "* ]]; then
                completed=$((completed + 1))
            fi
        done < "$log"
        if [[ "$status" == 0 && "$completed" != 1 ]]; then
            fail "The native harness did not report exactly one executed fixture: $selection"
        fi
        exit "$status"
        ;;
    inventory)
        expected=()
        while IFS= read -r selector; do
            [[ -n "$selector" ]] || fail "The generated fixture inventory contains an empty selector."
            expected+=("$selector")
        done < "$selection"
        [[ "${#expected[@]}" -gt 0 ]] || fail "The generated fixture inventory is empty."

        listed="$("$harness" --color=never --list)"
        actual=()
        while IFS= read -r line; do
            [[ "$line" == *": test" ]] || fail "Unexpected native fixture listing: $line"
            actual+=("${line%": test"}")
        done <<< "$listed"
        [[ "${#actual[@]}" == "${#expected[@]}" ]] || fail "Fixture counts differ: generated ${#expected[@]}, native ${#actual[@]}."

        # Check both directions and multiplicities, without treating names as patterns.
        for selector in "${expected[@]}"; do
            matches=0
            for native in "${actual[@]}"; do
                if [[ "$selector" == "$native" ]]; then
                    matches=$((matches + 1))
                fi
            done
            [[ "$matches" == 1 ]] || fail "Expected one native occurrence of $selector; found $matches."
        done
        for selector in "${actual[@]}"; do
            matches=0
            for generated in "${expected[@]}"; do
                if [[ "$selector" == "$generated" ]]; then
                    matches=$((matches + 1))
                fi
            done
            [[ "$matches" == 1 ]] || fail "Expected one generated occurrence of $selector; found $matches."
        done
        printf 'Verified %s native fixture selectors.\n' "${#actual[@]}"
        ;;
    *)
        fail "Unknown fixture wrapper mode: $mode"
        ;;
esac
