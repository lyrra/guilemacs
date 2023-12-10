#!/usr/bin/env bash

set -e

cd ..
pwd

I=/usr/local

tar cvf guilemacs.tar.xz $I/bin/emacs $I/share/emacs .

