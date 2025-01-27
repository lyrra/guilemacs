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

/* mpz global temporaries.  Making them global saves the trouble of
   properly using mpz_init and mpz_clear on temporaries even when
   storage is exhausted.  Admittedly this is not ideal.  An mpz value
   in a temporary is made permanent by mpz_swapping it with a bignum's
   value.  Although typically at most two temporaries are needed,
   rounddiv_q and rounding_driver both need four and time_arith needs
   five.  */

mpz_t mpz[5];

Lisp_Object
bignum_to_guile_bignum (Lisp_Object num)
{
  if (BIGNUMP (num)) {
    mpz_t const *z = bignum_integer (&mpz[0], num);
    return scm_from_mpz (*z);
  } else {
    return num;
  }
}

static void *
xrealloc_for_gmp (void *ptr, size_t ignore, size_t size)
{
  return xrealloc (ptr, size);
}

static void
xfree_for_gmp (void *ptr, size_t ignore)
{
  xfree (ptr);
}

void
init_bignum (void)
{
  eassert (mp_bits_per_limb == GMP_NUMB_BITS);
  integer_width = 1 << 16;

  /* FIXME: The Info node `(gmp) Custom Allocation' states: "No error
     return is allowed from any of these functions, if they return
     then they must have performed the specified operation. [...]
     There's currently no defined way for the allocation functions to
     recover from an error such as out of memory, they must terminate
     program execution.  A 'longjmp' or throwing a C++ exception will
     have undefined results."  But xmalloc and xrealloc do call
     'longjmp'.  */
  mp_set_memory_functions (xmalloc, xrealloc_for_gmp, xfree_for_gmp);

  for (int i = 0; i < ARRAYELTS (mpz); i++)
    mpz_init (mpz[i]);
}

/* Return D, converted to a Lisp integer.  Discard any fraction.
   Signal an error if D cannot be converted.  */
Lisp_Object
double_to_integer (double d)
{
  return scm_inexact_to_exact (scm_round_number (scm_from_double (d)));
}

/* Return a Lisp integer equal to mpz[0], which has BITS bits and which
   must not be in fixnum range.  Set mpz[0] to a junk value.  */
static Lisp_Object
make_bignum_bits (size_t bits)
{
  /* The documentation says integer-width should be nonnegative, so
     comparing it to BITS works even though BITS is unsigned.  Treat
     integer-width as if it were at least twice the machine integer width,
     so that timefns.c can safely use bignums for double-precision
     timestamps.  */
  if (integer_width < bits && 2 * max (INTMAX_WIDTH, UINTMAX_WIDTH) < bits)
    overflow_error ();

  struct Lisp_Bignum *b = ALLOCATE_PLAIN_PSEUDOVECTOR (struct Lisp_Bignum,
						       PVEC_BIGNUM);
  mpz_init (b->value);
  mpz_swap (b->value, mpz[0]);
  return make_lisp_ptr (b, Lisp_Vectorlike);
}

/* Return a Lisp integer equal to mpz[0], which must not be in fixnum range.
   Set mpz[0] to a junk value.  */
static Lisp_Object
make_bignum (void)
{
  return make_bignum_bits (mpz_sizeinbase (mpz[0], 2));
}

/* Return a Lisp integer with value taken from mpz[0].
   Set mpz[0] to a junk value.  */
Lisp_Object
make_integer_mpz (void)
{
  if (FASTER_BIGNUM && mpz_fits_slong_p (mpz[0]))
    {
      long int v = mpz_get_si (mpz[0]);
      //if (!FIXNUM_OVERFLOW_P (v)) //FIX: guilemacs, no FIXNUM_OVERFLOW_P
	return make_fixnum (v);
    }

  size_t bits = mpz_sizeinbase (mpz[0], 2);

  if (! (FASTER_BIGNUM
	 //&& FIXNUM_OVERFLOW_P (LONG_MIN)  //FIX: guilemacs, no FIXNUM_OVERFLOW_P
	 //&& FIXNUM_OVERFLOW_P (LONG_MAX)) //FIX: guilemacs, no FIXNUM_OVERFLOW_P
	 )
      && bits <= FIXNUM_BITS)
    {
      EMACS_INT v = 0;
      int i = 0, shift = 0;

      do
	{
	  EMACS_INT limb = mpz_getlimbn (mpz[0], i++);
	  v += limb << shift;
	  shift += GMP_NUMB_BITS;
	}
      while (shift < bits);

      if (mpz_sgn (mpz[0]) < 0)
	v = -v;

      return make_fixnum (v);
    }

  return make_bignum_bits (bits);
}

/* If Z fits into *PI, store its value there and return true.
   Return false otherwise.  */
bool
mpz_to_intmax (mpz_t const z, intmax_t *pi)
{
  if (FASTER_BIGNUM)
    {
      if (mpz_fits_slong_p (z))
	{
	  *pi = mpz_get_si (z);
	  return true;
	}
      if (LONG_MIN <= INTMAX_MIN && INTMAX_MAX <= LONG_MAX)
	return false;
    }

  ptrdiff_t bits = mpz_sizeinbase (z, 2);
  bool negative = mpz_sgn (z) < 0;

  if (bits < INTMAX_WIDTH)
    {
      intmax_t v = 0;
      int i = 0, shift = 0;

      do
	{
	  intmax_t limb = mpz_getlimbn (z, i++);
	  v += limb << shift;
	  shift += GMP_NUMB_BITS;
	}
      while (shift < bits);

      *pi = negative ? -v : v;
      return true;
    }
  if (bits == INTMAX_WIDTH && INTMAX_MIN < -INTMAX_MAX && negative
      && mpz_scan1 (z, 0) == INTMAX_WIDTH - 1)
    {
      *pi = INTMAX_MIN;
      return true;
    }
  return false;
}

/* Check that X is a Lisp integer in the range LO..HI.
   Return X's value as an intmax_t.  */

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
