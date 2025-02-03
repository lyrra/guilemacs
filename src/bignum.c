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

#include <config.h>

#include "bignum.h"

#include "lisp.h"

#include <math.h>
#include <stdlib.h>

Lisp_Object
bignum_to_guile_bignum (Lisp_Object num)
{
  if (BIGNUMP (num)) {
    emacs_abort ();
  } else {
    return num;
  }
}

/* Return D, converted to a Lisp integer.  Discard any fraction.
   Signal an error if D cannot be converted.  */
Lisp_Object
double_to_integer (double d)
{
  return scm_inexact_to_exact (scm_round_number (scm_from_double (d)));
}

intmax_t
check_integer_range (Lisp_Object x, intmax_t lo, intmax_t hi)
{
  CHECK_INTEGER (x);
  intmax_t i;
  if (! (integer_to_intmax (x, &i) && lo <= i && i <= hi))
    args_out_of_range_3 (x, make_int (lo), make_int (hi));
  return i;
}

/* Check that X is a Lisp integer in the range 0..HI.
   Return X's value as an uintmax_t.  */

uintmax_t
check_uinteger_max (Lisp_Object x, uintmax_t hi)
{
  CHECK_INTEGER (x);
  uintmax_t i;
  if (! (integer_to_uintmax (x, &i) && i <= hi))
    args_out_of_range_3 (x, make_fixnum (0), make_uint (hi));
  return i;
}

/* Check that X is a Lisp integer no greater than INT_MAX,
   and return its value or zero, whichever is greater.  */

int
check_int_nonnegative (Lisp_Object x)
{
  CHECK_INTEGER (x);
  return NILP (Fnatnump (x)) ? 0 : check_integer_range (x, 0, INT_MAX);
}
