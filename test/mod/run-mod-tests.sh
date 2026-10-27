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

# Each suite pins its own expected case count and exits non-zero when the
# count drops, so this runner does not need a second pin (cr.org of the M59
# imp-5 round, F3: the round file is reused, so name the round).
# GUILE_AUTO_COMPILE=0: auto-compile writes .go cache files and prints
# warnings into the captured output (cr.org of the M59 imp-5 round, N3: the
# tool/run-tests.sh rule).
run_suite () {
    suite=$1
    printf '\n=== %s ===\n' "$suite"
    if GUILEMACS_ROOT="$repo_root" GUILE_AUTO_COMPILE=0 \
        guile -L "$repo_root/mod" "$script_dir/$suite"; then
        return 0
    else
        status=1
        return 0
    fi
}

run_suite sequences-tests.scm
run_suite standalone-tests.scm
run_suite faces-tests.scm
run_suite loading-stops-tests.scm

exit "$status"
