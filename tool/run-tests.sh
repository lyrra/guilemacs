#!/bin/sh

# the env file should set the GUILE variable
# which points to the installed guile-elisp
. ./env.sh

export PATH="$GUILE/bin:$PATH"
export LD_LIBRARY_PATH="$GUILE/lib"

export HOME=/nonexistent
export LANG=en_US.UTF-8
export EMACS_TEST_DIRECTORY="`pwd`/test"

cd test

guile -L ../tool -l ../tool/run-tests.scm -e main -- $*
