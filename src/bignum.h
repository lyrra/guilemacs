/* Big numbers for Emacs.

Copyright 2018-2025 Free Software Foundation, Inc.

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

/* Include this header only if access to bignum internals is needed.  */

#ifndef BIGNUM_H
#define BIGNUM_H

#include <gmp.h>
#include "lisp.h"

/* Compile with -DFASTER_BIGNUM=0 to disable common optimizations and
   allow easier testing of some slow-path code.  */
#ifndef FASTER_BIGNUM
# define FASTER_BIGNUM 1
#endif

/* Number of data bits in a limb.  */
#ifndef GMP_NUMB_BITS
enum { GMP_NUMB_BITS = TYPE_WIDTH (mp_limb_t) };
#endif

struct Lisp_Bignum
{
  struct vectorlike_header header;
  mpz_t value;
} GCALIGNED_STRUCT;

extern Lisp_Object bignum_to_guile_bignum (Lisp_Object num);

#endif /* BIGNUM_H */
