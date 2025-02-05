/* Primitive operations on floating point for GNU Emacs Lisp interpreter.

Copyright (C) 1988, 1993-1994, 1999, 2001-2025 Free Software Foundation,
Inc.

Author: Wolfgang Rupprecht (according to ack.texi)

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


/* C89 requires only the following math.h functions, and Emacs omits
   the starred functions since we haven't found a use for them:
   acos, asin, atan, atan2, ceil, cos, *cosh, exp, fabs, floor, fmod,
   frexp, ldexp, log, log10 [via (log X 10)], *modf, pow, sin, *sinh,
   sqrt, tan, *tanh.

   C99, C11 and C17 require the following math.h functions in addition to
   the C89 functions.  Of these, Emacs currently exports only the
   starred ones to Lisp, since we haven't found a use for the others.
   Also, it uses the ones marked "+" internally:
   acosh, atanh, cbrt, copysign (implemented by signbit), erf, erfc,
   exp2, expm1, fdim, fma, fmax, fmin, fpclassify, hypot, +ilogb,
   +isfinite, isgreater, isgreaterequal, +isinf, isless, islessequal,
   islessgreater, *isnan, isnormal, isunordered, lgamma, log1p, *log2
   [via (log X 2)], logb (approximately; implemented by frexp),
   +lrint/llrint, +lround/llround, nan, nearbyint, nextafter,
   nexttoward, remainder, remquo, *rint, round, scalbln, +scalbn,
   +signbit, tgamma, *trunc.

   C23 requires many more math.h functions.  Emacs does not yet export
   or use them.

   The C standard also requires functions for float and long double
   that are not listed above.  Of these functions, Emacs uses only the
   following internally: fabsf, powf, sprintf.
 */

#include <config.h>

#include "lisp.h"

#include <math.h>

/* Emacs needs proper handling of +/-inf; correct printing as well as
   important packages depend on it.  Make sure the user didn't specify
   -ffinite-math-only, either directly or implicitly with -Ofast or
   -ffast-math.  */
#if defined __FINITE_MATH_ONLY__ && __FINITE_MATH_ONLY__
 #error Emacs cannot be built with -ffinite-math-only
#endif

/* Check that X is a floating point number.  */

static void
CHECK_FLOAT (Lisp_Object x)
{
  CHECK_TYPE (FLOATP (x), Qfloatp, x);
}

/* Extract a Lisp number as a `double', or signal an error.  */

double
extract_float (Lisp_Object num)
{
  CHECK_NUMBER (num);
  return XFLOATINT (num);
}

/* Although the substitute does not work on NaNs, it is good enough
   for platforms lacking the signbit macro.  */
#ifndef signbit
# define signbit(x) ((x) < 0 || (IEEE_FLOATING_POINT && !(x) && 1 / (x) < 0))
#endif

DEFUN ("copysign", Fcopysign, Scopysign, 2, 2, 0,
       doc: /* Copy sign of X2 to value of X1, and return the result.
Cause an error if X1 or X2 is not a float.  */)
  (Lisp_Object x1, Lisp_Object x2)
{
  double f1, f2;

  CHECK_FLOAT (x1);
  CHECK_FLOAT (x2);

  f1 = XFLOAT_DATA (x1);
  f2 = XFLOAT_DATA (x2);

  /* Use signbit instead of copysign, to avoid calling make_float when
     the result is X1.  */
  return signbit (f1) != signbit (f2) ? make_float (-f1) : x1;
}

DEFUN ("frexp", Ffrexp, Sfrexp, 1, 1, 0,
       doc: /* Get significand and exponent of a floating point number.
Breaks the floating point number X into its binary significand SGNFCAND
\(a floating point value between 0.5 (included) and 1.0 (excluded))
and an integral exponent EXP for 2, such that:

  X = SGNFCAND * 2^EXP

The function returns the cons cell (SGNFCAND . EXP).
If X is zero, both parts (SGNFCAND and EXP) are zero.  */)
  (Lisp_Object x)
{
  double f = extract_float (x);
  int exponent;
  double sgnfcand = frexp (f, &exponent);
  return Fcons (make_float (sgnfcand), make_fixnum (exponent));
}

DEFUN ("ldexp", Fldexp, Sldexp, 2, 2, 0,
       doc: /* Return SGNFCAND * 2**EXPONENT, as a floating point number.
EXPONENT must be an integer.   */)
  (Lisp_Object sgnfcand, Lisp_Object exponent)
{
  CHECK_FIXNUM (exponent);
  int e = min (max (INT_MIN, XFIXNUM (exponent)), INT_MAX);
  return make_float (ldexp (extract_float (sgnfcand), e));
}

DEFUN ("float", Ffloat, Sfloat, 1, 1, 0,
       doc: /* Return the floating point number equal to ARG.  */)
  (register Lisp_Object arg)
{
  CHECK_NUMBER (arg);
  /* If ARG is a float, give 'em the same float back.  */
  return FLOATP (arg) ? arg : make_float (XFLOATINT (arg));
}

DEFUN ("logb", Flogb, Slogb, 1, 1, 0,
       doc: /* Returns largest integer <= the base 2 log of the magnitude of ARG.
This is the same as the exponent of a float.  */)
  (Lisp_Object arg)
{
  EMACS_INT value;
  CHECK_NUMBER (arg);

  if (FLOATP (arg) || FIXNUMP (arg) || GUILEBIGNUMP (arg))
    {
      Lisp_Object x = scm_divide (scm_log (arg), scm_log (10)); // 10 = make_fixnum (2)
      return scm_inexact_to_exact (scm_round_number (x));
    }
  emacs_abort ();
}

/* Return the integer exponent E such that D * FLT_RADIX**E (i.e.,
   scalbn (D, E)) is an integer that has precision equal to D and is
   representable as a double.

   Return DBL_MANT_DIG - DBL_MIN_EXP (the maximum possible valid
   scale) if D is zero or tiny.  Return one greater than that if
   D is infinite, and two greater than that if D is a NaN.  */

int
double_integer_scale (double d)
{
  int exponent = ilogb (d);
#ifdef HAIKU
  /* On Haiku, the values returned by ilogb are nonsensical when
     confronted with tiny numbers, inf, or NaN, which breaks the trick
     used by code on other platforms, so we have to test for each case
     manually, and return the appropriate value.  */
  if (exponent == FP_ILOGB0)
    {
      if (isnan (d))
	return (DBL_MANT_DIG - DBL_MIN_EXP) + 2;
      if (isinf (d))
	return (DBL_MANT_DIG - DBL_MIN_EXP) + 1;

      return (DBL_MANT_DIG - DBL_MIN_EXP);
    }
#endif
  return (DBL_MIN_EXP - 1 <= exponent && exponent < INT_MAX
	  ? DBL_MANT_DIG - 1 - exponent
	  : (DBL_MANT_DIG - DBL_MIN_EXP
	     + (isnan (d) ? 2 : exponent == INT_MAX)));
}

#ifndef HAVE_TRUNC
double
trunc (double d)
{
  return (d < 0 ? ceil : floor) (d);
}
#endif

Lisp_Object
fmod_float (Lisp_Object x, Lisp_Object y)
{
  double f1 = XFLOATINT (x);
  double f2 = XFLOATINT (y);

  f1 = fmod (f1, f2);

  /* If the "remainder" comes out with the wrong sign, fix it.  */
  if (f2 < 0 ? f1 > 0 : f1 < 0)
    f1 += f2;

  return make_float (f1);
}

void
syms_of_floatfns (void)
{
#include "floatfns.x"
}
