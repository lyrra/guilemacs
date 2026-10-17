#!/bin/sh
# Run tests for mod/ modules with plain Guile, without the Emacs binary.

set -eu

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo_root=$(dirname -- "$(dirname -- "$script_dir")")

if ! command -v guile >/dev/null 2>&1; then
    echo "$0: guile is required but was not found on PATH" >&2
    exit 127
fi

status=0

run_suite () {
    suite=$1
    printf '\n=== %s ===\n' "$suite"
    if GUILEMACS_ROOT="$repo_root" \
        guile -L "$repo_root/mod" "$script_dir/$suite"; then
        return 0
    else
        status=1
        return 0
    fi
}

run_suite sequences-tests.scm
run_suite standalone-tests.scm

exit "$status"
