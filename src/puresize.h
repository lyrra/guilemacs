/* How much read-only Lisp storage a dumped Emacs needs.
   Copyright (C) 1993, 2001-2019 Free Software Foundation, Inc.

This file is part of GNU Emacs.

GNU Emacs is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or (at
your option) any later version.

GNU Emacs is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with GNU Emacs.  If not, see <https://www.gnu.org/licenses/>.  */

#ifndef EMACS_PURESIZE_H
#define EMACS_PURESIZE_H

#include "lisp.h"

INLINE_HEADER_BEGIN

#define CHECK_IMPURE(obj, scmobj) ((void) 0)

#define PURE_P(obj) 0

#endif // EMACS_PURESIZE_H
