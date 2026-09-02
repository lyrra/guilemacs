#!/bin/sh

# the env file should set the GUILE variable
# which points to the installed guile-elisp
. ./env.sh

export PATH="$GUILE/bin:$PATH"
export LD_LIBRARY_PATH="$GUILE/lib"

export HOME=/nonexistent
export LANG=en_US.UTF-8
export EMACS_TEST_DIRECTORY="`pwd`/test"

# HOME=/nonexistent prevents Guile from writing its auto-compile (.go) cache.
# With auto-compile enabled, every module load emits a "<file> failed:" warning
# (not prefixed with ";;;", so the harness does not filter it) that leaks into
# the captured output of whichever test is running, producing nondeterministic
# spurious failures.  Disable auto-compilation to keep the harness output clean.
export GUILE_AUTO_COMPILE=0

cd test

guile -L ../tool -l ../tool/run-tests.scm -e main -- $*
