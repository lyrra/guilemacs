#!/usr/bin/env bash

set -e

ls -ltr 

I=/usr/local

tar cvf guilemacs.tar.xz $I/bin/emacs $I/share/emacs .

