/* Storage allocation and gc for GNU Emacs Lisp interpreter.

Copyright (C) 1985-1986, 1988, 1993-1995, 1997-2022 Free Software
Foundation, Inc.

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

#include <errno.h>
#include <stdint.h>
#include <stdlib.h>
#include <signal.h>		/* For SIGABRT, SIGDANGER.  */

#ifdef HAVE_PTHREAD
#include <pthread.h>
#endif

#include <gc.h>

#include "lisp.h"
#include "bignum.h"
#include "dispextern.h"
#include "intervals.h"
#include "sheap.h"
#include "sysstdio.h"
#include "systime.h"
#include "character.h"
#include "buffer.h"
#include "window.h"
#include "keyboard.h"
#include "frame.h"
#include "termhooks.h"		/* For struct terminal.  */
#ifdef HAVE_WINDOW_SYSTEM
#include TERM_HEADER
#endif /* HAVE_WINDOW_SYSTEM */

#include <flexmember.h>
#include <verify.h>
#include <execinfo.h>           /* For backtrace.  */

#ifdef HAVE_LINUX_SYSINFO
#include <sys/sysinfo.h>
#endif

#ifdef MSDOS
#include "dosfns.h"		/* For dos_memory_info.  */
#endif

#ifdef HAVE_MALLOC_H
# include <malloc.h>
#endif

#if (defined ENABLE_CHECKING \
     && defined HAVE_VALGRIND_VALGRIND_H && !defined USE_VALGRIND)
# define USE_VALGRIND 1
#endif

#if USE_VALGRIND
#include <valgrind/valgrind.h>
#include <valgrind/memcheck.h>
#endif

#include <unistd.h>
#include <fcntl.h>

#ifdef USE_GTK
# include "gtkutil.h"
#endif
#ifdef WINDOWSNT
#include "w32.h"
#include "w32heap.h"	/* for sbrk */
#endif

#if defined DOUG_LEA_MALLOC || defined HAVE_UNEXEC

/* Allocator-related actions to do just before and after unexec.  */

void
alloc_unexec_pre (void)
{
# ifdef DOUG_LEA_MALLOC
  malloc_state_ptr = malloc_get_state ();
  if (!malloc_state_ptr)
    fatal ("malloc_get_state: %s", strerror (errno));
# endif
}

void
alloc_unexec_post (void)
{
# ifdef DOUG_LEA_MALLOC
  free (malloc_state_ptr);
# endif
}

# ifdef GNU_LINUX

/* The address where the heap starts.  */
void *
my_heap_start (void)
{
  static void *start;
  if (! start)
    start = sbrk (0);
  return start;
}
# endif

#endif

/* Global variables.  */
struct emacs_globals globals;

/* Points to memory space allocated as "spare", to be freed if we run
   out of memory. */

static void *spare_memory;

/* Amount of spare memory to keep in large reserve block, or to see
   whether this much is available when malloc fails on a larger request.  */

#define SPARE_MEMORY (1 << 15)

const char *pending_malloc_warning;

static Lisp_Object make_pure_vector (ptrdiff_t);

#if !defined REL_ALLOC || defined SYSTEM_MALLOC || defined HYBRID_MALLOC
static void refill_memory_reserve (void);
#endif
static Lisp_Object make_empty_string (int);
extern Lisp_Object which_symbols (Lisp_Object, EMACS_INT) EXTERNALLY_VISIBLE;

static void
XFLOAT_INIT (Lisp_Object f, double n)
{
  XFLOAT (f)->data = n;
}

/* Account for allocation of NBYTES in the heap.  This is a separate
   function to avoid hassles with implementation-defined conversion
   from unsigned to signed types.  */
static void
tally_consing (ptrdiff_t nbytes)
{
  consing_until_gc -= nbytes;
}

#ifdef DOUG_LEA_MALLOC
static bool
pointers_fit_in_lispobj_p (void)
{
  return (UINTPTR_MAX <= VAL_MAX) || USE_LSB_TAG;
}

static bool
mmap_lisp_allowed_p (void)
{
  /* If we can't store all memory addresses in our lisp objects, it's
     risky to let the heap use mmap and give us addresses from all
     over our address space.  We also can't use mmap for lisp objects
     if we might dump: unexec doesn't preserve the contents of mmapped
     regions.  */
  return pointers_fit_in_lispobj_p () && !will_dump_with_unexec_p ();
}
#endif


/************************************************************************
				Malloc
 ************************************************************************/

#if defined SIGDANGER || (!defined SYSTEM_MALLOC && !defined HYBRID_MALLOC)

/* Function malloc calls this if it finds we are near exhausting storage.  */

void
malloc_warning (const char *str)
{
  pending_malloc_warning = str;
}

#endif

/* Display an already-pending malloc warning.  */

void
display_malloc_warning (void)
{
  call3 (intern ("display-warning"),
	 intern ("alloc"),
	 build_string (pending_malloc_warning),
	 intern (":emergency"));
  pending_malloc_warning = 0;
}

/* Called if we can't allocate relocatable space for a buffer.  */

void
buffer_memory_full (ptrdiff_t nbytes)
{
  /* If buffers use the relocating allocator, no need to free
     spare_memory, because we may have plenty of malloc space left
     that we could get, and if we don't, the malloc that fails will
     itself cause spare_memory to be freed.  If buffers don't use the
     relocating allocator, treat this like any other failing
     malloc.  */

#ifndef REL_ALLOC
  memory_full (nbytes);
#else
  /* This used to call error, but if we've run out of memory, we could
     get infinite recursion trying to build the string.  */
  xsignal (Qnil, Vmemory_signal_data);
#endif
}


/* Alignment needed for memory blocks that are allocated via malloc
   and that contain Lisp objects.  On typical hosts malloc already
   aligns sufficiently, but extra work is needed on oddball hosts
   where Emacs would crash if malloc returned a non-GCALIGNED pointer.  */
enum { LISP_ALIGNMENT = alignof (union { union emacs_align_type x;
					 GCALIGNED_UNION_MEMBER }) };
verify (LISP_ALIGNMENT % GCALIGNMENT == 0);

/* True if malloc (N) is known to return storage suitably aligned for
   Lisp objects whenever N is a multiple of LISP_ALIGNMENT.  In
   practice this is true whenever alignof (max_align_t) is also a
   multiple of LISP_ALIGNMENT.  This works even for buggy platforms
   like MinGW circa 2020, where alignof (max_align_t) is 16 even though
   the malloc alignment is only 8, and where Emacs still works because
   it never does anything that requires an alignment of 16.  */
enum { MALLOC_IS_LISP_ALIGNED = alignof (max_align_t) % LISP_ALIGNMENT == 0 };

/* Like GC_MALLOC but check for no memory and block interrupt input.  */

void *
xmalloc (size_t size)
{
  void *val = GC_MALLOC (size);

  if (!val && size)
    memory_full (size);
  return val;
}

/* Like the above, but zeroes out the memory just allocated.  */

void *
xzalloc (size_t size)
{
  void *val = xmalloc (size);

  if (!val && size)
    memory_full (size);
  return val;
}

/* Like GC_REALLOC but check for no memory.  */

void *
xrealloc (void *block, size_t size)
{
  void *val = GC_REALLOC (block, size);
  if (!val && size)
    memory_full (size);
  return val;
}

void
xfree (void *block)
{
}

/* Allocate pointerless memory.  */

void *
xmalloc_atomic (size_t size)
{
  void *val = GC_MALLOC_ATOMIC (size);
  if (! val && size)
    memory_full (size);
  return val;
}

void *
xzalloc_atomic (size_t size)
{
  return xmalloc_atomic (size);
}

void *
xrealloc_atomic (void *block, size_t size)
{
  void *val = GC_REALLOC(block, size); // FIX-20230211-LAV: GC_REALLOC_ATOMIC doesn't exist in bdw-gc?!
  if (! val && size)
    memory_full (size);
  return val;
}


/* Allocate uncollectable memory.  */

void *
xmalloc_uncollectable (size_t size)
{
  void *val = GC_MALLOC_UNCOLLECTABLE (size);
  if (! val && size)
    memory_full (size);
  return val;
}

/* Allocate memory, but if memory is exhausted, return NULL instead of
   signalling an error.  */

void *
xmalloc_unsafe (size_t size)
{
  return GC_MALLOC (size);
}

/* Allocate pointerless memory, but if memory is exhausted, return
   NULL instead of signalling an error.  */

void *
xmalloc_atomic_unsafe (size_t size)
{
  return GC_MALLOC_ATOMIC (size);
}

/* Other parts of Emacs pass large int values to allocator functions
   expecting ptrdiff_t.  This is portable in practice, but check it to
   be safe.  */
verify (INT_MAX <= PTRDIFF_MAX);


/* Allocate an array of NITEMS items, each of size ITEM_SIZE.
   Signal an error on memory exhaustion.  */

void *
xnmalloc (ptrdiff_t nitems, ptrdiff_t item_size)
{
  eassert (0 <= nitems && 0 < item_size);
  ptrdiff_t nbytes;
  if (INT_MULTIPLY_WRAPV (nitems, item_size, &nbytes) || SIZE_MAX < nbytes)
    memory_full (SIZE_MAX);
  return xmalloc (nbytes);
}

/* Like xnmalloc for pointerless objects.  */

void *
xnmalloc_atomic (ptrdiff_t nitems, ptrdiff_t item_size)
{
  eassert (0 <= nitems && 0 < item_size);
  if (min (PTRDIFF_MAX, SIZE_MAX) / item_size < nitems)
    memory_full (SIZE_MAX);
  return xmalloc_atomic (nitems * item_size);
}

/* Reallocate an array PA to make it of NITEMS items, each of size ITEM_SIZE.
   Signal an error on memory exhaustion.  */

void *
xnrealloc (void *pa, ptrdiff_t nitems, ptrdiff_t item_size)
{
  eassert (0 <= nitems && 0 < item_size);
  ptrdiff_t nbytes;
  if (INT_MULTIPLY_WRAPV (nitems, item_size, &nbytes) || SIZE_MAX < nbytes)
    memory_full (SIZE_MAX);
  return xrealloc (pa, nbytes);
}


/* Grow PA, which points to an array of *NITEMS items, and return the
   location of the reallocated array, updating *NITEMS to reflect its
   new size.  The new array will contain at least NITEMS_INCR_MIN more
   items, but will not contain more than NITEMS_MAX items total.
   ITEM_SIZE is the size of each item, in bytes.

   ITEM_SIZE and NITEMS_INCR_MIN must be positive.  *NITEMS must be
   nonnegative.  If NITEMS_MAX is -1, it is treated as if it were
   infinity.

   If PA is null, then allocate a new array instead of reallocating
   the old one.

   If memory exhaustion occurs, set *NITEMS to zero if PA is null, and
   signal an error (i.e., do not return).

   Thus, to grow an array A without saving its old contents, do
   { xfree (A); A = NULL; A = xpalloc (NULL, &AITEMS, ...); }.
   The A = NULL avoids a dangling pointer if xpalloc exhausts memory
   and signals an error, and later this code is reexecuted and
   attempts to free A.  */

void *
xpalloc (void *pa, ptrdiff_t *nitems, ptrdiff_t nitems_incr_min,
	 ptrdiff_t nitems_max, ptrdiff_t item_size)
{
  ptrdiff_t n0 = *nitems;
  eassume (0 < item_size && 0 < nitems_incr_min && 0 <= n0 && -1 <= nitems_max);

  /* The approximate size to use for initial small allocation
     requests.  This is the largest "small" request for the GNU C
     library malloc.  */
  enum { DEFAULT_MXFAST = 64 * sizeof (size_t) / 4 };

  /* If the array is tiny, grow it to about (but no greater than)
     DEFAULT_MXFAST bytes.  Otherwise, grow it by about 50%.
     Adjust the growth according to three constraints: NITEMS_INCR_MIN,
     NITEMS_MAX, and what the C language can represent safely.  */

  ptrdiff_t n, nbytes;
  if (INT_ADD_WRAPV (n0, n0 >> 1, &n))
    n = PTRDIFF_MAX;
  if (0 <= nitems_max && nitems_max < n)
    n = nitems_max;

  ptrdiff_t adjusted_nbytes
    = ((INT_MULTIPLY_WRAPV (n, item_size, &nbytes) || SIZE_MAX < nbytes)
       ? min (PTRDIFF_MAX, SIZE_MAX)
       : nbytes < DEFAULT_MXFAST ? DEFAULT_MXFAST : 0);
  if (adjusted_nbytes)
    {
      n = adjusted_nbytes / item_size;
      nbytes = adjusted_nbytes - adjusted_nbytes % item_size;
    }

  if (! pa)
    *nitems = 0;
  if (n - n0 < nitems_incr_min
      && (INT_ADD_WRAPV (n0, nitems_incr_min, &n)
	  || (0 <= nitems_max && nitems_max < n)
	  || INT_MULTIPLY_WRAPV (n, item_size, &nbytes)))
    memory_full (SIZE_MAX);
  pa = xrealloc (pa, nbytes);
  *nitems = n;
  return pa;
}


/* Like strdup, but uses xmalloc.  */

char *
xstrdup (const char *s)
{
  ptrdiff_t size;
  eassert (s);
  size = strlen (s) + 1;
  return memcpy (xmalloc_atomic (size), s, size);
}

/* Like above, but duplicates Lisp string to C string.  */

char *
xlispstrdup (Lisp_Object string)
{
  ptrdiff_t size = SBYTES (string) + 1;
  return memcpy (xmalloc_atomic (size), SSDATA (string), size);
}

/* Assign to *PTR a copy of STRING, freeing any storage *PTR formerly
   pointed to.  If STRING is null, assign it without copying anything.
   Allocate before freeing, to avoid a dangling pointer if allocation
   fails.  */

void
dupstring (char **ptr, char const *string)
{
  char *old = *ptr;
  *ptr = string ? xstrdup (string) : 0;
  xfree (old);
}


/* Like putenv, but (1) use the equivalent of xmalloc and (2) the
   argument is a const pointer.  */

void
xputenv (char const *string)
{
  if (putenv ((char *) string) != 0)
    memory_full (0);
}

/***********************************************************************
			 Interval Allocation
 ***********************************************************************/

/* Return a new interval.  */

INTERVAL
make_interval (void)
{
  INTERVAL val = xmalloc (sizeof (struct interval));
  RESET_INTERVAL (val);
  return val;
}

/***********************************************************************
			  String Allocation
 ***********************************************************************/

/* Initialize string allocation.  Called from init_alloc_once.  */

static void
init_strings (void)
{
  empty_unibyte_string = make_empty_string (0);
  empty_multibyte_string = make_empty_string (1);
}

/* Return a new Lisp_String.  */

static Lisp_Object
allocate_string (void)
{
  return scm_make_smob (lisp_string_tag);
}

/* Set up Lisp_String S for holding NCHARS characters, NBYTES bytes,
   plus a NUL byte at the end.  Allocate an sdata structure for S, and
   set S->data to its `u.data' member.  Store a NUL byte at the end of
   S->data.  Set S->size to NCHARS and S->size_byte to NBYTES.  Free
   S->data if it was initially non-null.  */

void
allocate_string_data (Lisp_Object string,
		      EMACS_INT nchars, EMACS_INT nbytes)
{
  struct Lisp_String *s = (void *) SCM_SMOB_DATA (string);
  unsigned char *data;

  if (STRING_BYTES_BOUND < nbytes)
    string_overflow ();

  data = GC_MALLOC_ATOMIC (nbytes + 1);
  s->data = data;
  s->size = nchars;
  s->size_byte = nbytes;
  s->data[nbytes] = '\0';
}

void
string_overflow (void)
{
  error ("Maximum string size exceeded");
}

static Lisp_Object
make_empty_string (int multibyte)
{
  Lisp_Object string;

  string = allocate_string ();
  allocate_string_data (string, 0, 0);
  if (! multibyte)
    STRING_SET_UNIBYTE (string);

  return string;
}

DEFUN ("make-string", Fmake_string, Smake_string, 2, 3, 0,
       doc: /* Return a newly created string of length LENGTH, with INIT in each element.
LENGTH must be an integer.
INIT must be an integer that represents a character.
If optional argument MULTIBYTE is non-nil, the result will be
a multibyte string even if INIT is an ASCII character.  */)
  (Lisp_Object length, Lisp_Object init, Lisp_Object multibyte)
{
  register Lisp_Object val;
  int c;
  EMACS_INT nbytes;

  CHECK_FIXNAT (length);
  CHECK_CHARACTER (init);

  c = XFIXNAT (init);
  if (ASCII_CHAR_P (c) && NILP (multibyte))
    {
      nbytes = XFIXNUM (length);
      val = make_uninit_string (nbytes);
      if (nbytes)
	{
          memset (SDATA (val), c, nbytes);
          SDATA (val)[nbytes] = 0;
	}
    }
  else
    {
      unsigned char str[MAX_MULTIBYTE_LENGTH];
      ptrdiff_t len = CHAR_STRING (c, str);
      EMACS_INT string_len = XFIXNUM (length);
      unsigned char *p, *beg, *end;

      if (INT_MULTIPLY_WRAPV (len, string_len, &nbytes))
        string_overflow ();
      val = make_uninit_multibyte_string (string_len, nbytes);
      for (beg = SDATA (val), p = beg, end = beg + nbytes; p < end; p += len)
        {
          /* First time we just copy `str' to the data of `val'.  */
          if (p == beg)
            memcpy (p, str, len);
          else
            {
              /* Next time we copy largest possible chunk from
              initialized to uninitialized part of `val'.  */
              len = min (p - beg, end - p);
              memcpy (p, beg, len);
            }
        }
      if (nbytes)
        *p = 0;
    }

  return val;
}

/* Fill A with 1 bits if INIT is non-nil, and with 0 bits otherwise.
   Return A.  */

Lisp_Object
bool_vector_fill (Lisp_Object a, Lisp_Object init)
{
  EMACS_INT nbits = bool_vector_size (a);
  if (0 < nbits)
    {
      unsigned char *data = bool_vector_uchar_data (a);
      int pattern = NILP (init) ? 0 : (1 << BOOL_VECTOR_BITS_PER_CHAR) - 1;
      ptrdiff_t nbytes = bool_vector_bytes (nbits);
      int last_mask = ~ (~0u << ((nbits - 1) % BOOL_VECTOR_BITS_PER_CHAR + 1));
      memset (data, pattern, nbytes - 1);
      data[nbytes - 1] = pattern & last_mask;
    }
  return a;
}

/* Return a newly allocated, uninitialized bool vector of size NBITS.  */

Lisp_Object
make_uninit_bool_vector (EMACS_INT nbits)
{
  Lisp_Object val;
  EMACS_INT words = bool_vector_words (nbits);
  EMACS_INT word_bytes = words * sizeof (bits_word);
  EMACS_INT needed_elements = ((bool_header_size - header_size + word_bytes
				+ word_size - 1)
			       / word_size);
  struct Lisp_Bool_Vector *p
    = (struct Lisp_Bool_Vector *) allocate_vector (needed_elements);
  XSETVECTOR (val, p);
  XSETPVECTYPESIZE (XVECTOR (val), PVEC_BOOL_VECTOR, 0, 0);
  p->size = nbits;

  /* Clear padding at the end.  */
  if (words)
    p->data[words - 1] = 0;

  return val;
}

DEFUN ("make-bool-vector", Fmake_bool_vector, Smake_bool_vector, 2, 2, 0,
       doc: /* Return a new bool-vector of length LENGTH, using INIT for each element.
LENGTH must be a number.  INIT matters only in whether it is t or nil.  */)
  (Lisp_Object length, Lisp_Object init)
{
  Lisp_Object val;

  CHECK_FIXNAT (length);
  val = make_uninit_bool_vector (XFIXNAT (length));
  return bool_vector_fill (val, init);
}

DEFUN ("bool-vector", Fbool_vector, Sbool_vector, 0, MANY, 0,
       doc: /* Return a new bool-vector with specified arguments as elements.
Any number of arguments, even zero arguments, are allowed.
usage: (bool-vector &rest OBJECTS)  */)
  (ptrdiff_t nargs, Lisp_Object *args)
{
  ptrdiff_t i;
  Lisp_Object vector;

  vector = make_uninit_bool_vector (nargs);
  for (i = 0; i < nargs; i++)
    bool_vector_set (vector, i, !NILP (args[i]));

  return vector;
}

/* Make a string from NBYTES bytes at CONTENTS, and compute the number
   of characters from the contents.  This string may be unibyte or
   multibyte, depending on the contents.  */

Lisp_Object
make_string (const char *contents, ptrdiff_t nbytes)
{
  register Lisp_Object val;
  ptrdiff_t nchars, multibyte_nbytes;

  parse_str_as_multibyte ((const unsigned char *) contents, nbytes,
			  &nchars, &multibyte_nbytes);
  if (nbytes == nchars || nbytes != multibyte_nbytes)
    /* CONTENTS contains no multibyte sequences or contains an invalid
       multibyte sequence.  We must make unibyte string.  */
    val = make_unibyte_string (contents, nbytes);
  else
    val = make_multibyte_string (contents, nchars, nbytes);
  return val;
}


/* Make an unibyte string from LENGTH bytes at CONTENTS.  */

Lisp_Object
make_unibyte_string (const char *contents, ptrdiff_t length)
{
  register Lisp_Object val;
  val = make_uninit_string (length);
  memcpy (SDATA (val), contents, length);
  return val;
}


/* Make a multibyte string from NCHARS characters occupying NBYTES
   bytes at CONTENTS.  */

Lisp_Object
make_multibyte_string (const char *contents,
		       ptrdiff_t nchars, ptrdiff_t nbytes)
{
  register Lisp_Object val;
  val = make_uninit_multibyte_string (nchars, nbytes);
  memcpy (SDATA (val), contents, nbytes);
  return val;
}


/* Make a string from NCHARS characters occupying NBYTES bytes at
   CONTENTS.  It is a multibyte string if NBYTES != NCHARS.  */

Lisp_Object
make_string_from_bytes (const char *contents,
			ptrdiff_t nchars, ptrdiff_t nbytes)
{
  register Lisp_Object val;
  val = make_uninit_multibyte_string (nchars, nbytes);
  memcpy (SDATA (val), contents, nbytes);
  if (SBYTES (val) == SCHARS (val))
    STRING_SET_UNIBYTE (val);
  return val;
}


/* Make a string from NCHARS characters occupying NBYTES bytes at
   CONTENTS.  The argument MULTIBYTE controls whether to label the
   string as multibyte.  If NCHARS is negative, it counts the number of
   characters by itself.  */

Lisp_Object
make_specified_string (const char *contents,
		       ptrdiff_t nchars, ptrdiff_t nbytes, bool multibyte)
{
  Lisp_Object val;

  if (nchars < 0)
    {
      if (multibyte)
	nchars = multibyte_chars_in_text ((const unsigned char *) contents,
					  nbytes);
      else
	nchars = nbytes;
    }
  val = make_uninit_multibyte_string (nchars, nbytes);
  memcpy (SDATA (val), contents, nbytes);
  if (!multibyte)
    STRING_SET_UNIBYTE (val);
  return val;
}


/* Return an unibyte Lisp_String set up to hold LENGTH characters
   occupying LENGTH bytes.  */

Lisp_Object
make_uninit_string (EMACS_INT length)
{
  Lisp_Object val;

  if (!length)
    return empty_unibyte_string;
  val = make_uninit_multibyte_string (length, length);
  STRING_SET_UNIBYTE (val);
  return val;
}

/* Return a multibyte Lisp_String set up to hold NCHARS characters
   which occupy NBYTES bytes.  */

Lisp_Object
make_uninit_multibyte_string (EMACS_INT nchars, EMACS_INT nbytes)
{
  Lisp_Object string;

  if (nchars < 0)
    emacs_abort ();
  if (!nbytes)
    return empty_multibyte_string;

  string = allocate_string ();
  ((struct Lisp_String *) SCM_SMOB_DATA (string))->intervals = NULL;
  allocate_string_data (string, nchars, nbytes);
  return string;
}

/* Print arguments to BUF according to a FORMAT, then return
   a Lisp_String initialized with the data from BUF.  */

Lisp_Object
make_formatted_string (char *buf, const char *format, ...)
{
  va_list ap;
  int length;

  va_start (ap, format);
  length = vsprintf (buf, format, ap);
  va_end (ap);
  return make_string (buf, length);
}


/***********************************************************************
			   Float Allocation
 ***********************************************************************/

/* Return a new float object with value FLOAT_VALUE.  */

Lisp_Object
make_float (double float_value)
{
  return scm_from_double (float_value);
}


/***********************************************************************
			   Cons Allocation
 ***********************************************************************/

DEFUN ("cons", Fcons, Scons, 2, 2, 0,
       doc: /* Create a new cons, give it CAR and CDR as components, and return it.  */)
  (Lisp_Object car, Lisp_Object cdr)
{
  return scm_cons (car, cdr);
}

/* Make a list of 1, 2, 3, 4 or 5 specified objects.  */

Lisp_Object
list1 (Lisp_Object arg1)
{
  return Fcons (arg1, Qnil);
}

Lisp_Object
list2 (Lisp_Object arg1, Lisp_Object arg2)
{
  return Fcons (arg1, Fcons (arg2, Qnil));
}


Lisp_Object
list3 (Lisp_Object arg1, Lisp_Object arg2, Lisp_Object arg3)
{
  return Fcons (arg1, Fcons (arg2, Fcons (arg3, Qnil)));
}

Lisp_Object
list4 (Lisp_Object arg1, Lisp_Object arg2, Lisp_Object arg3, Lisp_Object arg4)
{
  return Fcons (arg1, Fcons (arg2, Fcons (arg3, Fcons (arg4, Qnil))));
}

Lisp_Object
list5 (Lisp_Object arg1, Lisp_Object arg2, Lisp_Object arg3, Lisp_Object arg4,
       Lisp_Object arg5)
{
  return Fcons (arg1, Fcons (arg2, Fcons (arg3, Fcons (arg4,
						       Fcons (arg5, Qnil)))));
}

/* Make a list of COUNT Lisp_Objects, where ARG is the first one.
   Use CONS to construct the pairs.  AP has any remaining args.  */
static Lisp_Object
cons_listn (ptrdiff_t count, Lisp_Object arg,
	    Lisp_Object (*cons) (Lisp_Object, Lisp_Object), va_list ap)
{
  eassume (0 < count);
  Lisp_Object val = cons (arg, Qnil);
  Lisp_Object tail = val;
  for (ptrdiff_t i = 1; i < count; i++)
    {
      Lisp_Object elem = cons (va_arg (ap, Lisp_Object), Qnil);
      XSETCDR (tail, elem);
      tail = elem;
    }
  return val;
}

/* Make a list of COUNT Lisp_Objects, where ARG1 is the first one.  */
Lisp_Object
listn (ptrdiff_t count, Lisp_Object arg1, ...)
{
  va_list ap;
  va_start (ap, arg1);
  Lisp_Object val = cons_listn (count, arg1, Fcons, ap);
  va_end (ap);
  return val;
}

/* Make a pure list of COUNT Lisp_Objects, where ARG1 is the first one.  */
Lisp_Object
pure_listn (ptrdiff_t count, Lisp_Object arg1, ...)
{
  va_list ap;
  va_start (ap, arg1);
  Lisp_Object val = cons_listn (count, arg1, pure_cons, ap);
  va_end (ap);
  return val;
}

DEFUN ("list", Flist, Slist, 0, MANY, 0,
       doc: /* Return a newly created list with specified arguments as elements.
Allows any number of arguments, including zero.
usage: (list &rest OBJECTS)  */)
  (ptrdiff_t nargs, Lisp_Object *args)
{
  register Lisp_Object val;
  val = Qnil;

  while (nargs > 0)
    {
      nargs--;
      val = Fcons (args[nargs], val);
    }
  return val;
}


DEFUN ("make-list", Fmake_list, Smake_list, 2, 2, 0,
       doc: /* Return a newly created list of length LENGTH, with each element being INIT.  */)
  (Lisp_Object length, Lisp_Object init)
{
  Lisp_Object val = Qnil;
  CHECK_FIXNAT (length);

  for (EMACS_INT size = XFIXNAT (length); 0 < size; size--)
    {
      val = Fcons (init, val);
      rarely_quit (size);
    }

  return val;
}



/***********************************************************************
			   Vector Allocation
 ***********************************************************************/

/* The only vector with 0 slots, allocated from pure space.  */

Lisp_Object zero_vector;

/* Called once to initialize vector allocation.  */

static void
init_vectors (void)
{
  struct Lisp_Vector *p = xmalloc (header_size);

  SCM_NEWSMOB (p->header.self, lisp_vectorlike_tag, p);
  p->header.size = 0;
  XSETVECTOR (zero_vector, p);
}

/* Value is a pointer to a newly allocated Lisp_Vector structure
   with room for LEN Lisp_Objects.  LEN must be zero or positive.
 */

static struct Lisp_Vector *
allocate_vectorlike (ptrdiff_t len)
{
  struct Lisp_Vector *p;

  if (len == 0)
    p = XVECTOR (zero_vector);
  else
    {
      p = xmalloc (header_size + len * word_size);
      SCM_NEWSMOB (p->header.self, lisp_vectorlike_tag, p);
    }

  return p;
}


/* Allocate a vector with LEN slots.  */

struct Lisp_Vector *
allocate_vector (ptrdiff_t len)
{
  if (len == 0)
    return XVECTOR (zero_vector);
  struct Lisp_Vector *v = allocate_vectorlike (len);
  v->header.size = len;
  return v;
}


/* Allocate other vector-like structures.  */

struct Lisp_Vector *
allocate_pseudovector (int memlen, int lisplen,
                       int zerolen, enum pvec_type tag)
{
  /* Catch bogus values.  */
  enum { size_max = (1 << PSEUDOVECTOR_SIZE_BITS) - 1 };
  enum { rest_max = (1 << PSEUDOVECTOR_REST_BITS) - 1 };
  eassert (0 <= tag && tag <= PVEC_FONT);
  eassert (0 <= lisplen && lisplen <= zerolen && zerolen <= memlen);
  eassert (lisplen <= size_max);
  eassert (memlen <= size_max + rest_max);

  struct Lisp_Vector *v = allocate_vectorlike (memlen);
  /* Only the first LISPLEN slots will be traced normally by the GC.  */
  for (int i = 0; i < lisplen; ++i)
    v->contents[i] = Qnil;

  XSETPVECTYPESIZE (v, tag, lisplen, memlen - lisplen);
  return v;
}

struct buffer *
allocate_buffer (void)
{
  struct buffer *b = xmalloc (sizeof *b);

  SCM_NEWSMOB (b->header.self, lisp_vectorlike_tag, b);
  BUFFER_PVEC_INIT (b);
  /* Put B on the chain of all buffers including killed ones.  */
  b->next = all_buffers;
  all_buffers = b;
  /* Note that the rest fields of B are not initialized.  */
  return b;
}


/* Allocate a record with COUNT slots.  COUNT must be positive, and
   includes the type slot.  */

static struct Lisp_Vector *
allocate_record (EMACS_INT count)
{
  if (count > PSEUDOVECTOR_SIZE_MASK)
    error ("Attempt to allocate a record of %"pI"d slots; max is %d",
	   count, PSEUDOVECTOR_SIZE_MASK);
  struct Lisp_Vector *p = allocate_vectorlike (count);
  p->header.size = count;
  XSETPVECTYPE (p, PVEC_RECORD);
  return p;
}

DEFUN ("make-record", Fmake_record, Smake_record, 3, 3, 0,
       doc: /* Create a new record.
TYPE is its type as returned by `type-of'; it should be either a
symbol or a type descriptor.  SLOTS is the number of non-type slots,
each initialized to INIT.  */)
  (Lisp_Object type, Lisp_Object slots, Lisp_Object init)
{
  CHECK_FIXNAT (slots);
  EMACS_INT size = XFIXNAT (slots) + 1;
  struct Lisp_Vector *p = allocate_record (size);
  p->contents[0] = type;
  for (ptrdiff_t i = 1; i < size; i++)
    p->contents[i] = init;
  return make_lisp_ptr (p, Lisp_Vectorlike);
}

static Lisp_Object make_clear_string (EMACS_INT, bool);
static Lisp_Object make_clear_multibyte_string (EMACS_INT, EMACS_INT, bool);

DEFUN ("record", Frecord, Srecord, 1, MANY, 0,
       doc: /* Create a new record.
TYPE is its type as returned by `type-of'; it should be either a
symbol or a type descriptor.  SLOTS is used to initialize the record
slots with shallow copies of the arguments.
usage: (record TYPE &rest SLOTS) */)
  (ptrdiff_t nargs, Lisp_Object *args)
{
  struct Lisp_Vector *p = allocate_record (nargs);
  memcpy (p->contents, args, nargs * sizeof *args);
  return make_lisp_ptr (p, Lisp_Vectorlike);
}


DEFUN ("make-vector", Fmake_vector, Smake_vector, 2, 2, 0,
       doc: /* Return a newly created vector of length LENGTH, with each element being INIT.
See also the function `vector'.  */)
  (Lisp_Object length, Lisp_Object init)
{
  CHECK_TYPE (FIXNATP (length) && XFIXNAT (length) <= PTRDIFF_MAX,
	      Qwholenump, length);
  return make_vector (XFIXNAT (length), init);
}

/* Return a new vector of length LENGTH with each element being INIT.  */

Lisp_Object
make_vector (ptrdiff_t length, Lisp_Object init)
{
  struct Lisp_Vector *p = allocate_vector (length);
  for (ptrdiff_t i = 0; i < length; i++)
    p->contents[i] = init;
  return make_lisp_ptr (p, Lisp_Vectorlike);
}

DEFUN ("vector", Fvector, Svector, 0, MANY, 0,
       doc: /* Return a newly created vector with specified arguments as elements.
Allows any number of arguments, including zero.
usage: (vector &rest OBJECTS)  */)
  (ptrdiff_t nargs, Lisp_Object *args)
{
  Lisp_Object val = make_uninit_vector (nargs);
  struct Lisp_Vector *p = XVECTOR (val);
  for (ptrdiff_t i = 0; i < nargs; i++)
    p->contents[i] = args[i];
  return val;
}

void
make_byte_code (struct Lisp_Vector *v)
{
  /* Don't allow the global zero_vector to become a byte code object.  */
  eassert (0 < v->header.size);

  if (v->header.size > 1 && STRINGP (v->contents[1])
      && STRING_MULTIBYTE (v->contents[1]))
    /* BYTECODE-STRING must have been produced by Emacs 20.2 or the
       earlier because they produced a raw 8-bit string for byte-code
       and now such a byte-code string is loaded as multibyte while
       raw 8-bit characters converted to multibyte form.  Thus, now we
       must convert them back to the original unibyte form.  */
    v->contents[1] = Fstring_as_unibyte (v->contents[1]);
  XSETPVECTYPE (v, PVEC_COMPILED);
}

DEFUN ("make-byte-code", Fmake_byte_code, Smake_byte_code, 4, MANY, 0,
       doc: /* Create a byte-code object with specified arguments as elements.
The arguments should be the ARGLIST, bytecode-string BYTE-CODE, constant
vector CONSTANTS, maximum stack size DEPTH, (optional) DOCSTRING,
and (optional) INTERACTIVE-SPEC.
The first four arguments are required; at most six have any
significance.
The ARGLIST can be either like the one of `lambda', in which case the arguments
will be dynamically bound before executing the byte code, or it can be an
integer of the form NNNNNNNRMMMMMMM where the 7bit MMMMMMM specifies the
minimum number of arguments, the 7-bit NNNNNNN specifies the maximum number
of arguments (ignoring &rest) and the R bit specifies whether there is a &rest
argument to catch the left-over arguments.  If such an integer is used, the
arguments will not be dynamically bound but will be instead pushed on the
stack before executing the byte-code.
usage: (make-byte-code ARGLIST BYTE-CODE CONSTANTS DEPTH &optional DOCSTRING INTERACTIVE-SPEC &rest ELEMENTS)  */)
  (ptrdiff_t nargs, Lisp_Object *args)
{
  Lisp_Object val = make_uninit_vector (nargs);
  struct Lisp_Vector *p = XVECTOR (val);

  /* We used to purecopy everything here, if purify-flag was set.  This worked
     OK for Emacs-23, but with Emacs-24's lexical binding code, it can be
     dangerous, since make-byte-code is used during execution to build
     closures, so any closure built during the preload phase would end up
     copied into pure space, including its free variables, which is sometimes
     just wasteful and other times plainly wrong (e.g. those free vars may want
     to be setcar'd).  */

  for (int i = 0; i < nargs; i++)
    p->contents[i] = args[i];
  make_byte_code (p);
  XSETCOMPILED (val, p);
  return val;
}



#if 0
DEFUN ("make-record", Fmake_record, Smake_record, 3, 3, 0,
       doc: /* Create a new record.
TYPE is its type as returned by `type-of'; it should be either a
symbol or a type descriptor.  SLOTS is the number of non-type slots,
each initialized to INIT.  */)
  (Lisp_Object type, Lisp_Object slots, Lisp_Object init)
{
  CHECK_NATNUM (slots);
  EMACS_INT size = XFASTINT (slots) + 1;
  struct Lisp_Vector *p = allocate_record (size);
  p->contents[0] = type;
  for (ptrdiff_t i = 1; i < size; i++)
    p->contents[i] = init;
  return make_lisp_ptr (p, Lisp_Vectorlike);
}


DEFUN ("record", Frecord, Srecord, 1, MANY, 0,
       doc: /* Create a new record.
TYPE is its type as returned by `type-of'; it should be either a
symbol or a type descriptor.  SLOTS is used to initialize the record
slots with shallow copies of the arguments.
usage: (record TYPE &rest SLOTS) */)
  (ptrdiff_t nargs, Lisp_Object *args)
{
  struct Lisp_Vector *p = allocate_record (nargs);
  memcpy (p->contents, args, nargs * sizeof *args);
  return make_lisp_ptr (p, Lisp_Vectorlike);
}
#endif

/***********************************************************************
			   Symbol Allocation
 ***********************************************************************/

DEFUN ("make-symbol", Fmake_symbol, Smake_symbol, 1, 1, 0,
       doc: /* Return a newly allocated uninterned symbol whose name is NAME.
Its value is void, and its function definition and property list are nil.  */)
  (Lisp_Object name)
{
  Lisp_Object val;
  CHECK_STRING (name);
  val = scm_make_symbol (scm_from_utf8_stringn (SSDATA (name),
                                                SBYTES (name)));
  return val;
}



Lisp_Object
make_misc_ptr (void *a)
{
  struct Lisp_Misc_Ptr *p = ALLOCATE_PLAIN_PSEUDOVECTOR (struct Lisp_Misc_Ptr,
							 PVEC_MISC_PTR);
  p->pointer = a;
  return make_lisp_ptr (p, Lisp_Vectorlike);
}

/* Return a new overlay with specified START, END and PLIST.  */

Lisp_Object
build_overlay (Lisp_Object start, Lisp_Object end, Lisp_Object plist)
{
  struct Lisp_Overlay *p = ALLOCATE_PSEUDOVECTOR (struct Lisp_Overlay, plist,
						  PVEC_OVERLAY);
  Lisp_Object overlay = make_lisp_ptr (p, Lisp_Vectorlike);
  OVERLAY_START (overlay) = start;
  OVERLAY_END (overlay) = end;
  set_overlay_plist (overlay, plist);
  p->next = NULL;
  return overlay;
}

DEFUN ("make-marker", Fmake_marker, Smake_marker, 0, 0, 0,
       doc: /* Return a newly allocated marker which does not point at any place.  */)
  (void)
{
  struct Lisp_Marker *p = ALLOCATE_PLAIN_PSEUDOVECTOR (struct Lisp_Marker,
						       PVEC_MARKER);
  p->buffer = 0;
  p->bytepos = 0;
  p->charpos = 0;
  p->next = NULL;
  p->insertion_type = 0;
  p->need_adjustment = 0;
  return make_lisp_ptr (p, Lisp_Vectorlike);
}

/* Return a newly allocated marker which points into BUF
   at character position CHARPOS and byte position BYTEPOS.  */

Lisp_Object
build_marker (struct buffer *buf, ptrdiff_t charpos, ptrdiff_t bytepos)
{
  /* No dead buffers here.  */
  eassert (BUFFER_LIVE_P (buf));

  /* Every character is at least one byte.  */
  eassert (charpos <= bytepos);

  struct Lisp_Marker *m = ALLOCATE_PLAIN_PSEUDOVECTOR (struct Lisp_Marker,
						       PVEC_MARKER);
  m->buffer = buf;
  m->charpos = charpos;
  m->bytepos = bytepos;
  m->insertion_type = 0;
  m->need_adjustment = 0;
  m->next = BUF_MARKERS (buf);
  BUF_MARKERS (buf) = m;
  return make_lisp_ptr (m, Lisp_Vectorlike);
}


/* Return a newly created vector or string with specified arguments as
   elements.  If all the arguments are characters that can fit
   in a string of events, make a string; otherwise, make a vector.

   Any number of arguments, even zero arguments, are allowed.  */

Lisp_Object
make_event_array (ptrdiff_t nargs, Lisp_Object *args)
{
  ptrdiff_t i;

  for (i = 0; i < nargs; i++)
    /* The things that fit in a string
       are characters that are in 0...127,
       after discarding the meta bit and all the bits above it.  */
    if (!FIXNUMP (args[i])
	|| (XFIXNUM (args[i]) & ~(-CHAR_META)) >= 0200)
      return Fvector (nargs, args);

  /* Since the loop exited, we know that all the things in it are
     characters, so we can make a string.  */
  {
    Lisp_Object result;

    result = Fmake_string (make_fixnum (nargs), make_fixnum (0), Qnil);
    for (i = 0; i < nargs; i++)
      {
	SSET (result, i, XFIXNUM (args[i]));
	/* Move the meta bit to the right place for a string char.  */
	if (XFIXNUM (args[i]) & CHAR_META)
	  SSET (result, i, SREF (result, i) | 0x80);
      }

    return result;
  }
}



/************************************************************************
			   Memory Full Handling
 ************************************************************************/


/* Called if xmalloc (NBYTES) returns zero.  If NBYTES == SIZE_MAX,
   there may have been size_t overflow so that xmalloc was never
   called, or perhaps xmalloc was invoked successfully but the
   resulting pointer had problems fitting into a tagged EMACS_INT.  In
   either case this counts as memory being full even though xmalloc
   did not fail.  */

void
memory_full (size_t nbytes)
{
  /* This used to call error, but if we've run out of memory, we could
     get infinite recursion trying to build the string.  */
  xsignal (Qnil, Vmemory_signal_data);
}


/***********************************************************************
                 Pure Storage Compatibility Functions
 ***********************************************************************/

<<<<<<< HEAD
/* Return a string allocated in pure space.  DATA is a buffer holding
   NCHARS characters, and NBYTES bytes of string data.  MULTIBYTE
   means make the result string multibyte.

   Must get an error if pure storage is full, since if it cannot hold
   a large string it may be able to hold conses that point to that
   string; then the string is not protected from gc.  */
||||||| parent of eacc3830799 (remove pure storage support)
/* Allocate room for SIZE bytes from pure Lisp storage and return a
   pointer to it.  TYPE is the Lisp type for which the memory is
   allocated.  TYPE < 0 means it's not used for a Lisp object,
   and that the result should have an alignment of -TYPE.  */

static void *
pure_alloc (size_t size, int type)
{
  void *result = xmalloc(size);
  if (!result)
    memory_full (size);
  return result;
}

<<<<<<< variant A
    case Lisp_Vectorlike:
      {
	register struct Lisp_Vector *ptr = XVECTOR (obj);

	if (vector_marked_p (ptr))
	  break;

        enum pvec_type pvectype
          = PSEUDOVECTOR_TYPE (ptr);

#ifdef GC_CHECK_MARKED_OBJECTS
        if (!pdumper_object_p (po) && !SUBRP (obj) && !main_thread_p (po))
          {
	    m = mem_find (po);
	    if (m == MEM_NIL)
	      emacs_abort ();
	    if (m->type == MEM_TYPE_VECTORLIKE)
	      CHECK_LIVE (live_large_vector_p, MEM_TYPE_VECTORLIKE);
	    else
	      CHECK_LIVE (live_small_vector_p, MEM_TYPE_VECTOR_BLOCK);
          }
#endif

	switch (pvectype)
	  {
	  case PVEC_BUFFER:
	    mark_buffer ((struct buffer *) ptr);
            break;

          case PVEC_COMPILED:
            /* Although we could treat this just like a vector, mark_compiled
               returns the COMPILED_CONSTANTS element, which is marked at the
               next iteration of goto-loop here.  This is done to avoid a few
               recursive calls to mark_object.  */
            obj = mark_compiled (ptr);
            if (!NILP (obj))
              goto loop;
            break;

          case PVEC_FRAME:
            mark_frame (ptr);
            break;

          case PVEC_WINDOW:
            mark_window (ptr);
            break;

	  case PVEC_HASH_TABLE:
            mark_hash_table (ptr);
	    break;

	  case PVEC_CHAR_TABLE:
	  case PVEC_SUB_CHAR_TABLE:
	    mark_char_table (ptr, (enum pvec_type) pvectype);
	    break;

          case PVEC_BOOL_VECTOR:
            /* bool vectors in a dump are permanently "marked", since
               they're in the old section and don't have mark bits.
               If we're looking at a dumped bool vector, we should
               have aborted above when we called vector_marked_p, so
               we should never get here.  */
            eassert (!pdumper_object_p (ptr));
            set_vector_marked (ptr);
            break;

          case PVEC_OVERLAY:
	    mark_overlay (XOVERLAY (obj));
	    break;

	  case PVEC_SUBR:
	    break;

	  case PVEC_FREE:
	    emacs_abort ();

	  default:
	    /* A regular vector, or a pseudovector needing no special
	       treatment.  */
	    mark_vectorlike (&ptr->header);
	  }
      }
      break;
>>>>>>> variant B
####### Ancestor
    case Lisp_Vectorlike:
      {
	register struct Lisp_Vector *ptr = XVECTOR (obj);

	if (vector_marked_p (ptr))
	  break;

    case Lisp_Float:
      CHECK_ALLOCATED_AND_LIVE (live_float_p, MEM_TYPE_FLOAT);
      break;

        enum pvec_type pvectype
          = PSEUDOVECTOR_TYPE (ptr);

        if (pvectype != PVEC_SUBR &&
            pvectype != PVEC_BUFFER &&
            !main_thread_p (po))
          CHECK_LIVE (live_vector_p);

	switch (pvectype)
	  {
	  case PVEC_BUFFER:
	    mark_buffer ((struct buffer *) ptr);
            break;

          case PVEC_COMPILED:
            /* Although we could treat this just like a vector, mark_compiled
               returns the COMPILED_CONSTANTS element, which is marked at the
               next iteration of goto-loop here.  This is done to avoid a few
               recursive calls to mark_object.  */
            obj = mark_compiled (ptr);
            if (!NILP (obj))
              goto loop;
            break;

          case PVEC_FRAME:
            mark_frame (ptr);
            break;

          case PVEC_WINDOW:
            mark_window (ptr);
            break;

	  case PVEC_HASH_TABLE:
            mark_hash_table (ptr);
	    break;

	  case PVEC_CHAR_TABLE:
	  case PVEC_SUB_CHAR_TABLE:
	    mark_char_table (ptr, (enum pvec_type) pvectype);
	    break;

          case PVEC_BOOL_VECTOR:
            /* bool vectors in a dump are permanently "marked", since
               they're in the old section and don't have mark bits.
               If we're looking at a dumped bool vector, we should
               have aborted above when we called vector_marked_p(), so
               we should never get here.  */
            eassert (!pdumper_object_p (ptr));
            set_vector_marked (ptr);
            break;

          case PVEC_OVERLAY:
	    mark_overlay (XOVERLAY (obj));
	    break;

	  case PVEC_SUBR:
	    break;

	  case PVEC_FREE:
	    emacs_abort ();

	  default:
	    /* A regular vector, or a pseudovector needing no special
	       treatment.  */
	    mark_vectorlike (&ptr->header);
	  }
      }
      break;
======= end

#ifdef HAVE_UNEXEC

/* Print a warning if PURESIZE is too small.  */

void
check_pure_size (void)
{
  if (pure_bytes_used_before_overflow)
    message (("emacs:0:Pure Lisp storage overflow (approx. %"pI"d"
	      " bytes needed)"),
	     pure_bytes_used + pure_bytes_used_before_overflow);
}
#endif


/* Return a string allocated in pure space.  DATA is a buffer holding
   NCHARS characters, and NBYTES bytes of string data.  MULTIBYTE
   means make the result string multibyte.

   Must get an error if pure storage is full, since if it cannot hold
   a large string it may be able to hold conses that point to that
   string; then the string is not protected from gc.  */
=======
void
check_pure_size (void)
{
  return;
}
>>>>>>> eacc3830799 (remove pure storage support)

Lisp_Object
make_pure_string (const char *data,
		  ptrdiff_t nchars, ptrdiff_t nbytes, bool multibyte)
{
  return make_specified_string (data, nchars, nbytes, multibyte);
}

Lisp_Object
make_pure_c_string (const char *data, ptrdiff_t nchars)
{
  return build_string (data);
}

Lisp_Object
pure_cons (Lisp_Object car, Lisp_Object cdr)
{
  return Fcons (car, cdr);
}

DEFUN ("purecopy", Fpurecopy, Spurecopy, 1, 1, 0,
       doc: /* Return OBJ.  */)
  (register Lisp_Object obj)
{
  return obj;
}

/***********************************************************************
			  Protection from GC
 ***********************************************************************/

DEFUN ("garbage-collect", Fgarbage_collect, Sgarbage_collect, 0, 0, "",
       doc: /* Reclaim storage for Lisp objects no longer needed.
Garbage collection happens automatically if you cons more than
`gc-cons-threshold' bytes of Lisp data since previous garbage collection.
`garbage-collect' normally returns a list with info on amount of space in use,
where each entry has the form (NAME SIZE USED FREE), where:
- NAME is a symbol describing the kind of objects this entry represents,
- SIZE is the number of bytes used by each one,
- USED is the number of those objects that were found live in the heap,
- FREE is the number of those objects that are not live but that Emacs
  keeps around for future allocations (maybe because it does not know how
  to return them to the OS).
However, if there was overflow in pure space, `garbage-collect'
returns nil, because real GC can't be done.
See Info node `(elisp)Garbage Collection'.  */)
  (void)
{
  GC_gcollect ();
  return Qt;
}


#ifdef ENABLE_CHECKING

bool suppress_checking;

void
die (const char *msg, const char *file, int line)
{
  fprintf (stderr, "\r\n%s:%d: Emacs fatal error: assertion failed: %s\r\n",
	   file, line, msg);
  terminate_due_to_signal (SIGABRT, INT_MAX);
}

#endif /* ENABLE_CHECKING */

#if defined (ENABLE_CHECKING) && USE_STACK_LISP_OBJECTS

/* Stress alloca with inconveniently sized requests and check
   whether all allocated areas may be used for Lisp_Object.  */

NO_INLINE static void
verify_alloca (void)
{
  int i;
  enum { ALLOCA_CHECK_MAX = 256 };
  /* Start from size of the smallest Lisp object.  */
  for (i = sizeof (struct Lisp_Cons); i <= ALLOCA_CHECK_MAX; i++)
    {
      void *ptr = alloca (i);
      make_lisp_ptr (ptr, Lisp_Cons);
    }
}

#else /* not ENABLE_CHECKING && USE_STACK_LISP_OBJECTS */

#define verify_alloca() ((void) 0)

#endif /* ENABLE_CHECKING && USE_STACK_LISP_OBJECTS */

/* Initialization.  */

static void init_alloc_once_for_pdumper (void);

static int
print_lisp_string (SCM obj, SCM port, scm_print_state *pstate)
{
  scm_c_write (port, "#<elisp-string \"", 16);
  scm_c_write (port, XSTRING (obj)->data, STRING_BYTES (XSTRING (obj)));
  scm_c_write (port, "\">", 2);
  return 0;
}

void
init_alloc_once (void)
{
  lisp_misc_tag = scm_make_smob_type ("elisp-misc", 0);
  lisp_string_tag = scm_make_smob_type ("elisp-string",
                                        sizeof (struct Lisp_String));
  scm_set_smob_print (lisp_string_tag, print_lisp_string);
  lisp_vectorlike_tag = scm_make_smob_type ("elisp-vectorlike", 0);

  init_strings ();
  init_vectors ();
}

static void
init_alloc_once_for_pdumper (void)
{
}

void
init_alloc (void)
{
}

void
syms_of_alloc (void)
{
#include "alloc.x"

  DEFVAR_INT ("gc-cons-threshold", gc_cons_threshold,
	      doc: /* Number of bytes of consing between garbage collections.
Garbage collection can happen automatically once this many bytes have been
allocated since the last garbage collection.  All data types count.

Garbage collection happens automatically only when `eval' is called.

By binding this temporarily to a large number, you can effectively
prevent garbage collection during a part of the program.
See also `gc-cons-percentage'.  */);

  DEFVAR_LISP ("gc-cons-percentage", Vgc_cons_percentage,
	       doc: /* Portion of the heap used for allocation.
Garbage collection can happen automatically once this portion of the heap
has been allocated since the last garbage collection.
If this portion is smaller than `gc-cons-threshold', this is ignored.  */);
  Vgc_cons_percentage = make_float (0.1);

  DEFVAR_INT ("pure-bytes-used", pure_bytes_used,
	      doc: /* Number of bytes of shareable Lisp data allocated so far.  */);

  DEFVAR_LISP ("purify-flag", Vpurify_flag,
	       doc: /* Non-nil means loading Lisp code in order to dump an executable.
This means that certain objects should be allocated in shared (pure) space.
It can also be set to a hash-table, in which case this table is used to
do hash-consing of the objects allocated to pure space.  */);

  DEFVAR_BOOL ("garbage-collection-messages", garbage_collection_messages,
	       doc: /* Non-nil means display messages at start and end of garbage collection.  */);
  garbage_collection_messages = 0;

  DEFVAR_LISP ("post-gc-hook", Vpost_gc_hook,
	       doc: /* Hook run after garbage collection has finished.  */);
  Vpost_gc_hook = Qnil;
  DEFSYM (Qpost_gc_hook, "post-gc-hook");

  DEFVAR_LISP ("memory-signal-data", Vmemory_signal_data,
	       doc: /* Precomputed `signal' argument for memory-full error.  */);
  /* We build this in advance because if we wait until we need it, we might
     not be able to allocate the memory to hold it.  */
  Vmemory_signal_data
    = pure_list (Qerror,
		 build_pure_c_string ("Memory exhausted--use"
				      " M-x save-some-buffers then"
				      " exit and restart Emacs"));

  DEFVAR_LISP ("memory-full", Vmemory_full,
	       doc: /* Non-nil means Emacs cannot get much more Lisp memory.  */);
  Vmemory_full = Qnil;

  DEFSYM (Qgc_cons_threshold, "gc-cons-threshold");
  DEFSYM (Qchar_table_extra_slots, "char-table-extra-slots");

  DEFVAR_INT ("integer-width", integer_width,
	      doc: /* Maximum number N of bits in safely-calculated integers.
Integers with absolute values less than 2**N do not signal a range error.
N should be nonnegative.  */);

}

#ifdef HAVE_X_WINDOWS
enum defined_HAVE_X_WINDOWS { defined_HAVE_X_WINDOWS = true };
#else
enum defined_HAVE_X_WINDOWS { defined_HAVE_X_WINDOWS = false };
#endif

/* When compiled with GCC, GDB might say "No enum type named
   pvec_type" if we don't have at least one symbol with that type, and
   then xbacktrace could fail.  Similarly for the other enums and
   their values.  Some non-GCC compilers don't like these constructs.  */
#ifdef __GNUC__
union
{
  enum CHARTAB_SIZE_BITS CHARTAB_SIZE_BITS;
  //enum char_table_specials char_table_specials;
  enum char_bits char_bits;
  enum DEFAULT_HASH_SIZE DEFAULT_HASH_SIZE;
  enum Lisp_Bits Lisp_Bits;
  enum Lisp_Compiled Lisp_Compiled;
  enum maxargs maxargs;
  enum MAX_ALLOCA MAX_ALLOCA;
  enum More_Lisp_Bits More_Lisp_Bits;
  enum pvec_type pvec_type;
  enum defined_HAVE_X_WINDOWS defined_HAVE_X_WINDOWS;
} const EXTERNALLY_VISIBLE gdb_make_enums_visible = {0};
#endif	/* __GNUC__ */

