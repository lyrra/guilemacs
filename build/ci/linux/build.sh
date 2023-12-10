#!/usr/bin/env bash

set -e

#export GUILE_SYSTEM_COMPILED_PATH=/usr/lib/x86_64-linux-gnu/guile/3.0/ccache
#export CFLAGS="-fsanitize=address -fno-omit-frame-pointer"
#export CXXFLAGS="-fsanitize=address -fno-omit-frame-pointer"

echo "Build Linux Guilemacs"

./autogen.sh

./configure --prefix=$instdir --enable-internal-debug --without-modules --without-thread s --without-xft --with-gif=no --with-tiff=no --with-jpeg=no --with-gnutls=no --with-jpeg=no --without-lcms2 --without-cairo

make V=1

make check V=1

make install

make clean

make distclean

