/* Storage allocation and gc for GNU Emacs Lisp interpreter.

Copyright (C) 1985-2025 Free Software Foundation, Inc.

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
#include "dispextern.h"
#include "intervals.h"
#include "sysstdio.h"
#include "systime.h"
#include "character.h"
#include "buffer.h"
#include "window.h"
#include "keyboard.h"
#include "frame.h"
#include "termhooks.h"		/* For struct terminal.  */
#include "itree.h"
#ifdef HAVE_WINDOW_SYSTEM
#include TERM_HEADER
#endif /* HAVE_WINDOW_SYSTEM */

/* FIX-guilemacs: Removed Android platform code - using pure Guile approach */

#ifdef HAVE_TREE_SITTER
#include "treesit.h"
#endif

#include <flexmember.h>
#include <verify.h>
#include <execinfo.h>           /* For backtrace.  */

#if (defined ENABLE_CHECKING \
     && defined HAVE_VALGRIND_VALGRIND_H && !defined USE_VALGRIND)
# define USE_VALGRIND 1
#endif

#if USE_VALGRIND
#include <valgrind/valgrind.h>
#include <valgrind/memcheck.h>
#endif

/* AddressSanitizer exposes additional functions for manually marking
   memory as poisoned/unpoisoned.  When ASan is enabled and the needed
   header is available, memory is poisoned when:

   * An ablock is freed (lisp_align_free), or ablocks are initially
   allocated (lisp_align_malloc).
   * An interval_block is initially allocated (make_interval).
   * A dead INTERVAL is put on the interval free list
   (sweep_intervals).
   * A sdata is marked as dead (sweep_strings, pin_string).
   * An sblock is initially allocated (allocate_string_data).
   * A string_block is initially allocated (allocate_string).
   * A dead string is put on string_free_list (sweep_strings).
   * A float_block is initially allocated (make_float).
   * A dead float is put on float_free_list.
   * A cons_block is initially allocated (Fcons).
   * A dead cons is put on cons_free_list (sweep_cons).
   * A dead vector is put on vector_free_list (setup_on_free_list),
   or a new vector block is allocated (allocate_vector_from_block).
   Accordingly, objects reused from the free list are unpoisoned.

   This feature can be disabled with the run-time flag
   `allow_user_poisoning' set to zero.  */
#if ADDRESS_SANITIZER && defined HAVE_SANITIZER_ASAN_INTERFACE_H \
  && !defined GC_ASAN_POISON_OBJECTS
# define GC_ASAN_POISON_OBJECTS 1
# include <sanitizer/asan_interface.h>
#else
# define GC_ASAN_POISON_OBJECTS 0
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

static struct Lisp_Vector *
allocate_clear_vector (ptrdiff_t len, bool clearit);

/* Default value of gc_cons_threshold (see below).  */

#define GC_DEFAULT_THRESHOLD (100000 * word_size)

/* Global variables.  */
struct emacs_globals globals;

/* maybe_gc collects garbage if this goes negative.  */

EMACS_INT consing_until_gc;

/* True during GC.  */

bool gc_in_progress;

/* System byte and object counts reported by GC.  */

/* Assume byte counts fit in uintptr_t and object counts fit into
   intptr_t.  */
typedef uintptr_t byte_ct;
typedef intptr_t object_ct;

/* Large-magnitude value for a threshold count, which fits in EMACS_INT.
   Using only half the EMACS_INT range avoids overflow hassles.
   There is no need to fit these counts into fixnums.  */
#define HI_THRESHOLD (EMACS_INT_MAX / 2)

/* Number of live and free conses etc. counted by the most-recent GC.  */

static struct gcstat
{
  object_ct total_conses, total_free_conses;
  object_ct total_symbols, total_free_symbols;
  object_ct total_strings, total_free_strings;
  byte_ct total_string_bytes;
  object_ct total_vectors, total_vector_slots, total_free_vector_slots;
  object_ct total_floats, total_free_floats;
  object_ct total_intervals, total_free_intervals;
  object_ct total_buffers;

  /* Size of the ancillary arrays of live hash-table and obarray objects.
     The objects themselves are not included (counted as vectors above).  */
  byte_ct total_hash_table_bytes;
} gcstat;

/* Points to memory space allocated as "spare", to be freed if we run
   out of memory. */

static void *spare_memory;

/* Amount of spare memory to keep in large reserve block, or to see
   whether this much is available when malloc fails on a larger request.  */

#define SPARE_MEMORY (1 << 15)

/* If nonzero, this is a warning delivered by malloc and not yet
   displayed.  */

const char *pending_malloc_warning;

/* Phase 0 vector migration instrumentation hooks.  */
static bool vector_phase0_noting;

static void
phase0_note_elisp_vector_allocation (const char *who, ptrdiff_t len)
{
  if (!guilemacs_warn_on_elisp_vector_allocation
      && !guilemacs_error_on_elisp_vector_allocation)
    return;

  if (vector_phase0_noting)
    return;

  if (!who || !*who)
    who = "unknown";

  vector_phase0_noting = true;

  if (guilemacs_warn_on_elisp_vector_allocation)
    message ("[guilemacs] plain elisp vector allocation via %s (len=%"pD"d)",
             who, len);

  vector_phase0_noting = false;

  if (guilemacs_error_on_elisp_vector_allocation)
    emacs_abort ();
}

/* Hook run after GC has finished.  */

#if !defined REL_ALLOC || defined SYSTEM_MALLOC || defined HYBRID_MALLOC
static void refill_memory_reserve (void);
#endif
static Lisp_Object make_empty_string (int);
extern Lisp_Object which_symbols (Lisp_Object, EMACS_INT) EXTERNALLY_VISIBLE;


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
  call3 (Qdisplay_warning,
	 Qalloc,
	 build_string (pending_malloc_warning),
	 QCemergency);
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

/* A common multiple of the positive integers A and B.  Ideally this
   would be the least common multiple, but there's no way to do that
   as a constant expression in C, so do the best that we can easily do.  */
#define COMMON_MULTIPLE(a, b) \
  ((a) % (b) == 0 ? (a) : (b) % (a) == 0 ? (b) : (a) * (b))

/* Like GC_MALLOC but check for no memory.  */

void *
xmalloc (size_t size)
{
  void *val = GC_MALLOC (size);
  if (!val)
    memory_full (size);
  return val;
}

/* Like the above, but zeroes out the memory just allocated.  */

void *
xzalloc (size_t size)
{
  void *val = xmalloc (size);
  memset (val, 0, size);
  return val;
}

/* Like GC_REALLOC but check for no memory.  */

void *
xrealloc (void *block, size_t size)
{
  void *val = GC_REALLOC (block, size);
  if (!val)
    memory_full (size);
  return val;
}

void
xfree (void *block)
{
  return;
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
static_assert (INT_MAX <= PTRDIFF_MAX);


/* Allocate an array of NITEMS items, each of size ITEM_SIZE.
   Signal an error on memory exhaustion.  */

void *
xnmalloc (ptrdiff_t nitems, ptrdiff_t item_size)
{
  eassert (0 <= nitems && 0 < item_size);
  ptrdiff_t nbytes;
  if (ckd_mul (&nbytes, nitems, item_size) || SIZE_MAX < nbytes)
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
  if (ckd_mul (&nbytes, nitems, item_size) || SIZE_MAX < nbytes)
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
  if (ckd_add (&n, n0, n0 >> 1))
    n = PTRDIFF_MAX;
  if (0 <= nitems_max && nitems_max < n)
    n = nitems_max;

  ptrdiff_t adjusted_nbytes
    = ((ckd_mul (&nbytes, n, item_size) || SIZE_MAX < nbytes)
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
      && (ckd_add (&n, n0, nitems_incr_min)
	  || (0 <= nitems_max && nitems_max < n)
	  || ckd_mul (&nbytes, n, item_size)))
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


#if GC_ASAN_POISON_OBJECTS
# define ASAN_POISON_INTERVAL_BLOCK(b)         \
  __asan_poison_memory_region ((b)->intervals, \
			       sizeof ((b)->intervals))
# define ASAN_UNPOISON_INTERVAL_BLOCK(b)         \
  __asan_unpoison_memory_region ((b)->intervals, \
				 sizeof ((b)->intervals))
# define ASAN_POISON_INTERVAL(i) \
  __asan_poison_memory_region (i, sizeof *(i))
# define ASAN_UNPOISON_INTERVAL(i) \
  __asan_unpoison_memory_region (i, sizeof *(i))
#else
# define ASAN_POISON_INTERVAL_BLOCK(b) ((void) 0)
# define ASAN_UNPOISON_INTERVAL_BLOCK(b) ((void) 0)
# define ASAN_POISON_INTERVAL(i) ((void) 0)
# define ASAN_UNPOISON_INTERVAL(i) ((void) 0)
#endif

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

#if GC_ASAN_POISON_OBJECTS
/* Prepare s for denoting a free sdata struct, i.e, poison all bytes
   in the flexible array member, except the first SDATA_OFFSET bytes.
   This is only effective for strings of size n where n > sdata_size(n).
 */
# define ASAN_PREPARE_DEAD_SDATA(s, size)                          \
  do {                                                             \
    __asan_poison_memory_region (s, sdata_size (size));		   \
    __asan_unpoison_memory_region (&(s)->string,		   \
				   sizeof (struct Lisp_String *)); \
    __asan_unpoison_memory_region (&SDATA_NBYTES (s),		   \
				   sizeof SDATA_NBYTES (s));	   \
   } while (false)
/* Prepare s for storing string data for NBYTES bytes.  */
# define ASAN_PREPARE_LIVE_SDATA(s, nbytes) \
  __asan_unpoison_memory_region (s, sdata_size (nbytes))
# define ASAN_POISON_SBLOCK_DATA(b, size) \
  __asan_poison_memory_region ((b)->data, size)
# define ASAN_POISON_STRING_BLOCK(b) \
  __asan_poison_memory_region ((b)->strings, STRING_BLOCK_SIZE)
# define ASAN_UNPOISON_STRING_BLOCK(b) \
  __asan_unpoison_memory_region ((b)->strings, STRING_BLOCK_SIZE)
# define ASAN_POISON_STRING(s) \
  __asan_poison_memory_region (s, sizeof *(s))
# define ASAN_UNPOISON_STRING(s) \
  __asan_unpoison_memory_region (s, sizeof *(s))
#else
# define ASAN_PREPARE_DEAD_SDATA(s, size) ((void) 0)
# define ASAN_PREPARE_LIVE_SDATA(s, nbytes) ((void) 0)
# define ASAN_POISON_SBLOCK_DATA(b, size) ((void) 0)
# define ASAN_POISON_STRING_BLOCK(b) ((void) 0)
# define ASAN_UNPOISON_STRING_BLOCK(b) ((void) 0)
# define ASAN_POISON_STRING(s) ((void) 0)
# define ASAN_UNPOISON_STRING(s) ((void) 0)
#endif

/* Return a new Lisp_String.  */

static Lisp_Object
allocate_string (void)
{
  return scm_make_smob (lisp_string_tag);
}


/* Set up Lisp_String S for holding NCHARS characters, NBYTES bytes,
   plus a NUL byte at the end.  Allocate an sdata structure DATA for
   S, and set S->u.s.data to SDATA->u.data.  Store a NUL byte at the
   end of S->u.s.data.  Set S->u.s.size to NCHARS and S->u.s.size_byte
   to NBYTES.  Free S->u.s.data if it was initially non-null.

   If CLEARIT, also clear the other bytes of S->u.s.data.  */

void
allocate_string_data (Lisp_Object string,
		      EMACS_INT nchars, EMACS_INT nbytes, bool clearit)
{
  struct Lisp_String *s = (void *) SCM_SMOB_DATA (string);
  unsigned char *data;

  if (STRING_BYTES_BOUND < nbytes)
    string_overflow ();

  data = GC_MALLOC_ATOMIC (nbytes + 1);
  if (clearit)
    memset (data, 0, nbytes + 1);
  s->u.s.data = data;
  s->u.s.size = nchars;
  s->u.s.size_byte = nbytes;
  s->u.s.data[nbytes] = '\0';
}

/* Reallocate multibyte STRING data when a single character is replaced.
   The character is at byte offset CIDX_BYTE in the string.
   The character being replaced is CLEN bytes long,
   and the character that will replace it is NEW_CLEN bytes long.
   Return the address where the caller should store the new character.  */

unsigned char *
resize_string_data (Lisp_Object string, ptrdiff_t cidx_byte,
                    int clen, int new_clen)
{
  eassume (STRING_MULTIBYTE (string));
  struct Lisp_String *lstr = XSTRING(string);
  ptrdiff_t nchars = SCHARS (string);
  ptrdiff_t nbytes = SBYTES (string);
  ptrdiff_t new_nbytes = nbytes + (new_clen - clen);
  unsigned char *data = SDATA (string);
  unsigned char *new_charaddr;

  if (nbytes == new_nbytes)
    {
      /* No need to reallocate, as the size change falls within the
	 alignment slop.  */
      XSTRING (string)->u.s.size_byte = new_nbytes;
      new_charaddr = data + cidx_byte;
      memmove (new_charaddr + new_clen, new_charaddr + clen,
               nbytes - (cidx_byte + (clen - 1)));
    }
  else
    {
      allocate_string_data (XSTRING (string), nchars, new_nbytes, false);
      unsigned char *new_data = SDATA (string);
      new_charaddr = new_data + cidx_byte;
      memcpy (new_charaddr + new_clen, data + cidx_byte + clen,
              nbytes - (cidx_byte + clen));
      memcpy (new_data, data, cidx_byte);
    }

  clear_string_char_byte_cache ();
  return new_charaddr;
}

void
string_overflow (void)
{
  error ("Maximum string size exceeded");
}

static Lisp_Object
make_empty_string (int multibyte)
{
  return scm_from_utf8_string ("");
}

DEFUN ("make-string", Fmake_string, Smake_string, 2, 3, 0,
       doc: /* Return a newly created string of length LENGTH, with INIT in each element.
LENGTH must be an integer.
INIT must be an integer that represents a character.
If optional argument MULTIBYTE is non-nil, the result will be
a multibyte string even if INIT is an ASCII character.  */)
  (Lisp_Object length, Lisp_Object init, Lisp_Object multibyte)
{
  Lisp_Object val;
  EMACS_INT nbytes;

  CHECK_FIXNAT (length);
  CHECK_CHARACTER (init);

  return scm_make_string (length, scm_c_make_char (XFIXNUM (init)));
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

/* Return a newly allocated, bool vector of size NBITS.  If CLEARIT,
   clear its slots; otherwise the vector's slots are uninitialized.  */

Lisp_Object
make_clear_bool_vector (EMACS_INT nbits, bool clearit)
{
  eassert (0 <= nbits && nbits <= BOOL_VECTOR_LENGTH_MAX);
  Lisp_Object val;
  ptrdiff_t words = bool_vector_words (nbits);
  ptrdiff_t word_bytes = words * sizeof (bits_word);
  ptrdiff_t needed_elements = ((bool_header_size - header_size + word_bytes
				+ word_size - 1)
			       / word_size);
  struct Lisp_Bool_Vector *p
    = (struct Lisp_Bool_Vector *) allocate_clear_vector (needed_elements,
							 clearit);
  /* Clear padding at end; but only if necessary, to avoid polluting the
     data cache.  */
  if (!clearit && nbits % BITS_PER_BITS_WORD != 0)
    p->data[words - 1] = 0;

  XSETVECTOR (val, p);
  XSETPVECTYPESIZE (XVECTOR (val), PVEC_BOOL_VECTOR, 0, 0);
  p->size = nbits;
  return val;
}

/* Return a newly allocated, uninitialized bool vector of size NBITS.  */

Lisp_Object
make_uninit_bool_vector (EMACS_INT nbits)
{
  return make_clear_bool_vector (nbits, false);
}

DEFUN ("make-bool-vector", Fmake_bool_vector, Smake_bool_vector, 2, 2, 0,
       doc: /* Return a new bool-vector of length LENGTH, using INIT for each element.
LENGTH must be a number.  INIT matters only in whether it is t or nil.  */)
  (Lisp_Object length, Lisp_Object init)
{
  CHECK_FIXNAT (length);
  EMACS_INT len = XFIXNAT (length);
  if (BOOL_VECTOR_LENGTH_MAX < len)
    memory_full (SIZE_MAX);
  Lisp_Object val = make_clear_bool_vector (len, NILP (init));
  return NILP (init) ? val : bool_vector_fill (val, init);
}

DEFUN ("bool-vector", Fbool_vector, Sbool_vector, 0, MANY, 0,
       doc: /* Return a new bool-vector with specified arguments as elements.
Allows any number of arguments, including zero.
usage: (bool-vector &rest OBJECTS)  */)
  (ptrdiff_t nargs, Lisp_Object *args)
{
  if (BOOL_VECTOR_LENGTH_MAX < nargs)
    memory_full (SIZE_MAX);
  Lisp_Object vector = make_clear_bool_vector (nargs, true);
  for (ptrdiff_t i = 0; i < nargs; i++)
    if (!NILP (args[i]))
      bool_vector_set (vector, i, true);
  return vector;
}

/* Make a string from NBYTES bytes at CONTENTS, and compute the number
   of characters from the contents.  This string may be unibyte or
   multibyte, depending on the contents.  */

Lisp_Object
make_string (const char *contents, ptrdiff_t nbytes)
{
  return scm_from_utf8_stringn (contents, nbytes);
}

/* Make a unibyte string from LENGTH bytes at CONTENTS.  */

Lisp_Object
make_unibyte_string (const char *contents, ptrdiff_t length)
{
  /* GuilEmacs: For unibyte strings, use Latin-1 encoding to preserve all byte values.
     UTF-8 encoding would fail for binary data containing invalid UTF-8 sequences. */
  return scm_from_latin1_stringn (contents, length);
}


/* Make a multibyte string from NCHARS characters occupying NBYTES
   bytes at CONTENTS.  */

Lisp_Object
make_multibyte_string (const char *contents,
		       ptrdiff_t nchars, ptrdiff_t nbytes)
{
  // FIX-guilemacs: for safety, should use nchars
  if (nchars != nbytes)
    emacs_abort ();
  return scm_from_utf8_stringn (contents, nbytes);
}

/* Make a string from NCHARS characters occupying NBYTES bytes at
   CONTENTS.  It is a multibyte string if NBYTES != NCHARS.  */

Lisp_Object
make_string_from_bytes (const char *contents,
			ptrdiff_t nchars, ptrdiff_t nbytes)
{
  // FIX-guilemacs: any nasty edge-cases? use something like guile bytevector->string ?
  emacs_abort ();
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
  if (nchars < 0)
    {
      return scm_from_utf8_stringn (contents, nbytes);
    }
  return scm_from_utf8_stringn (contents, nbytes);
}

/* Return a unibyte Lisp_String set up to hold LENGTH characters
   occupying LENGTH bytes.  */

Lisp_Object
make_uninit_string (EMACS_INT length)
{
  return scm_c_make_string (length, SCM_UNDEFINED);
}

/* Return a multibyte Lisp_String set up to hold NCHARS characters
   which occupy NBYTES bytes.  */

Lisp_Object
make_uninit_multibyte_string (EMACS_INT nchars, EMACS_INT nbytes)
{
  // FIX-guilemacs: what if nchars /= nbytes ?
  return scm_c_make_string (nchars, scm_c_make_char (32));
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

ptrdiff_t vectorlike_nbytes (const struct vectorlike_header *hdr)
{
  return NULL;
}

/* Value is a pointer to a newly allocated Lisp_Vector structure
   with room for LEN Lisp_Objects.  */

static struct Lisp_Vector *
allocate_vectorlike (ptrdiff_t len, bool clearit)
{
  struct Lisp_Vector *p;

  if (len == 0)
    p = XVECTOR (zero_vector);
  else
    {
      /* Optimize: Integrate with Guile's GC for better memory management */
      p = xmalloc (header_size + len * word_size);
      if (clearit)
        {
          /* Zero the header */
          memset (p, 0, header_size);
          /* Initialize all slots to Qnil (not zero, since nil is not 0 in Guile) */
          for (ptrdiff_t i = 0; i < len; i++)
            p->contents[i] = Qnil;
        }
      SCM_NEWSMOB (p->header.self, lisp_vectorlike_tag, p);

      /* Register with Guile GC for coordinated collection */
      scm_gc_register_allocation (sizeof (struct Lisp_Vector) + len * word_size);
    }

  return p;
}


/* Allocate a vector with LEN slots.  If CLEARIT, clear its slots;
   otherwise the vector's slots are uninitialized.  */

static struct Lisp_Vector *
allocate_clear_vector (ptrdiff_t len, bool clearit)
{
  if (len == 0)
    return XVECTOR (zero_vector);
  struct Lisp_Vector *v = allocate_vectorlike (len, clearit);
  v->header.size = len;
  return v;
}

/* Allocate a vector with LEN uninitialized slots.  */

struct Lisp_Vector *
allocate_vector (ptrdiff_t len)
{
  phase0_note_elisp_vector_allocation (__func__, len);
  return allocate_clear_vector (len, false);
}

/* Allocate a vector with LEN nil slots.  */

struct Lisp_Vector *
allocate_nil_vector (ptrdiff_t len)
{
  phase0_note_elisp_vector_allocation (__func__, len);
  return allocate_clear_vector (len, true);
}


/* Allocate other vector-like structures.  */

struct Lisp_Vector *
allocate_pseudovector (int memlen, int lisplen,
		       int zerolen, enum pvec_type tag)
{
  /* Catch bogus values.  */
  enum { size_max = (1 << PSEUDOVECTOR_SIZE_BITS) - 1 };
  enum { rest_max = (1 << PSEUDOVECTOR_REST_BITS) - 1 };
  eassert (0 <= tag && tag <= PVEC_TAG_MAX);
  eassert (0 <= lisplen && lisplen <= zerolen && zerolen <= memlen);
  eassert (lisplen <= size_max);
  eassert (memlen <= size_max + rest_max);

  struct Lisp_Vector *v = allocate_vectorlike (memlen, false);
  /* Only the first LISPLEN slots will be traced normally by the GC.
     If Qnil is nonzero, clear the non-Lisp data separately.  */
  memsetnil (v->contents, zerolen);
  memset (v->contents + lisplen, 0, (zerolen - lisplen) * word_size);

  XSETPVECTYPESIZE (v, tag, lisplen, memlen - lisplen);
  return v;
}

struct buffer *
allocate_buffer (void)
{
  struct buffer *b
    = ALLOCATE_PSEUDOVECTOR (struct buffer, cursor_in_non_selected_windows_,
			     PVEC_BUFFER);

  SCM_NEWSMOB (b->header.self, lisp_vectorlike_tag, b);
  BUFFER_PVEC_INIT (b);
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
  struct Lisp_Vector *p = allocate_vectorlike (count, false);
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
  Lisp_Object record;
  CHECK_FIXNAT (slots);
  EMACS_INT size = XFIXNAT (slots) + 1;
  struct Lisp_Vector *p = allocate_record (size);
  p->contents[0] = type;
  for (ptrdiff_t i = 1; i < size; i++)
    p->contents[i] = init;
  XSETRECORD (record, p);
  return record;
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
  Lisp_Object record;
  XSETRECORD (record, p);
  return record;
}


DEFUN ("make-vector", Fmake_vector, Smake_vector, 2, 2, 0,
       doc: /* Return a newly created vector of length LENGTH, with each element being INIT.
See also the function `vector'.  */)
  (Lisp_Object length, Lisp_Object init)
{
  CHECK_TYPE (FIXNATP (length) && XFIXNAT (length) <= PTRDIFF_MAX,
	      Qwholenump, length);
  /* Create Scheme vector to match [1 2 3] literals and (vector ...) function.
     This ensures all three vector creation methods produce compatible types. */
  ptrdiff_t len = XFIXNAT (length);
  Lisp_Object vector = scm_c_make_vector (len, init);
  return vector;
}

/* Return a new vector of length LENGTH with each element being INIT.
   FIX-guilemacs: For now, keep returning Guile vectors to match reader behavior.
   This will be fully migrated in later phases. */

Lisp_Object
make_vector (ptrdiff_t length, Lisp_Object init)
{
  eassert (length >= 0);
  return scm_c_make_vector (length, init);
}

DEFUN ("vector", Fvector, Svector, 0, MANY, 0,
       doc: /* Return a newly created vector with specified arguments as elements.
Allows any number of arguments, including zero.
usage: (vector &rest OBJECTS)  */)
  (ptrdiff_t nargs, Lisp_Object *args)
{
  /* Create Scheme vector for consistency with vector literals [1 2 3] */
  Lisp_Object val = scm_c_make_vector (nargs, SCM_UNDEFINED);
  for (ptrdiff_t i = 0; i < nargs; i++)
    scm_c_vector_set_x (val, i, args[i]);
  return val;
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
  if (! ((FIXNUMP (args[CLOSURE_ARGLIST])
	  || CONSP (args[CLOSURE_ARGLIST])
	  || NILP (args[CLOSURE_ARGLIST]))
	 && STRINGP (args[CLOSURE_CODE])
	 && !STRING_MULTIBYTE (args[CLOSURE_CODE])
	 && VECTORP (args[CLOSURE_CONSTANTS])
	 && FIXNATP (args[CLOSURE_STACK_DEPTH])))
    error ("Invalid byte-code object");

  /* Bytecode must be immovable.  */
  //pin_string (args[CLOSURE_CODE]);

  /* We used to purecopy everything here, if purify-flag was set.  This worked
     OK for Emacs-23, but with Emacs-24's lexical binding code, it can be
     dangerous, since make-byte-code is used during execution to build
     closures, so any closure built during the preload phase would end up
     copied into pure space, including its free variables, which is sometimes
     just wasteful and other times plainly wrong (e.g. those free vars may want
     to be setcar'd).  */
  Lisp_Object val = Fvector (nargs, args);
  XSETPVECTYPE (XVECTOR (val), PVEC_CLOSURE);
  return val;
}

DEFUN ("make-closure", Fmake_closure, Smake_closure, 1, MANY, 0,
       doc: /* Create a byte-code closure from PROTOTYPE and CLOSURE-VARS.
Return a copy of PROTOTYPE, a byte-code object, with CLOSURE-VARS
replacing the elements in the beginning of the constant-vector.
usage: (make-closure PROTOTYPE &rest CLOSURE-VARS) */)
  (ptrdiff_t nargs, Lisp_Object *args)
{
  Lisp_Object protofun = args[0];
  CHECK_TYPE (CLOSUREP (protofun), Qbyte_code_function_p, protofun);

  /* Create a copy of the constant vector, filling it with the closure
     variables in the beginning.  (The overwritten part should just
     contain placeholder values.) */
  Lisp_Object proto_constvec = AREF (protofun, CLOSURE_CONSTANTS);
  ptrdiff_t constsize = ASIZE (proto_constvec);
  ptrdiff_t nvars = nargs - 1;
  if (nvars > constsize)
    error ("Closure vars do not fit in constvec");
  Lisp_Object constvec = make_uninit_elisp_vector (constsize);
  for (ptrdiff_t i = 0; i < nvars; i++)
    ASET (constvec, i, args[1 + i]);
  for (ptrdiff_t i = nvars; i < constsize; i++)
    ASET (constvec, i, AREF (proto_constvec, i));

  /* Return a copy of the prototype function with the new constant vector. */
  ptrdiff_t protosize = PVSIZE (protofun);
  struct Lisp_Vector *v = allocate_vectorlike (protosize, false);
  v->header = XVECTOR (protofun)->header;
  memcpy (v->contents, XVECTOR (protofun)->contents, protosize * word_size);
  v->contents[CLOSURE_CONSTANTS] = constvec;
  return make_lisp_ptr (v, Lisp_Vectorlike);
}


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

  val = scm_make_symbol (name);
  return val;
}



Lisp_Object
make_misc_ptr (void *a)
{
  struct Lisp_Misc_Ptr *p = ALLOCATE_PLAIN_PSEUDOVECTOR (struct Lisp_Misc_Ptr,
							 PVEC_MISC_PTR);
  p->pointer = a;
  return p->header.self;
}

Lisp_Object
make_excursion (Lisp_Object marker, Lisp_Object window)
{
  struct Lisp_Excursion *p = ALLOCATE_PSEUDOVECTOR (struct Lisp_Excursion, marker,
						    PVEC_EXCURSION);
  p->marker = marker;
  p->window = window;
  return p->header.self;
}

/* Return a new overlay with specified START, END and PLIST.  */

Lisp_Object
build_overlay (bool front_advance, bool rear_advance,
               Lisp_Object plist)
{
  struct Lisp_Overlay *p = ALLOCATE_PSEUDOVECTOR (struct Lisp_Overlay, plist,
						  PVEC_OVERLAY);
  Lisp_Object overlay = make_lisp_ptr (p, Lisp_Vectorlike);
  struct itree_node *node = xmalloc (sizeof (*node));
  itree_node_init (node, front_advance, rear_advance, overlay);
  p->interval = node;
  p->buffer = NULL;
  set_overlay_plist (overlay, plist);
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

   Allows any number of arguments, including zero.  */

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

DEFUN ("make-finalizer", Fmake_finalizer, Smake_finalizer, 1, 1, 0,
       doc: /* Make a finalizer that will run FUNCTION.
FUNCTION will be called after garbage collection when the returned
finalizer object becomes unreachable.  If the finalizer object is
reachable only through references from finalizer objects, it does not
count as reachable for the purpose of deciding whether to run
FUNCTION.  FUNCTION will be run once per finalizer object.  */)
  (Lisp_Object function)
{
  return Qnil;
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
  if (!initialized)
    fatal ("memory exhausted");

  /* Do not go into hysterics merely because a large request failed.  */
  bool enough_free_memory = false;
  if (SPARE_MEMORY < nbytes)
    {
      void *p = xmalloc_atomic_unsafe (SPARE_MEMORY);
      if (p)
	{
	  xfree (p);
	  enough_free_memory = true;
	}
    }

  if (! enough_free_memory)
    {
      Vmemory_full = Qt;

      /* The first time we get here, free the spare memory.  */
      if (spare_memory)
        {
          xfree (spare_memory);
          spare_memory = NULL;
        }
    }

  /* This used to call error, but if we've run out of memory, we could
     get infinite recursion trying to build the string.  */
  xsignal (Qnil, Vmemory_signal_data);
}

/* If we released our reserve (due to running out of memory),
   and we have a fair amount free once again,
   try to set aside another reserve in case we run out once more.

   This is called when a relocatable block is freed in ralloc.c,
   and also directly from this file, in case we're not using ralloc.c.  */

void
refill_memory_reserve (void)
{
  if (spare_memory == NULL)
    spare_memory = xmalloc_atomic_unsafe (SPARE_MEMORY);

  if (spare_memory)
    Vmemory_full = Qnil;
}

/* Determine whether it is safe to access memory at address P.  */
static int
valid_pointer_p (void *p)
{
#ifdef WINDOWSNT
  return w32_valid_pointer_p (p, 16);
#else

  if (ADDRESS_SANITIZER)
    return p ? -1 : 0;

  int fd[2];
  static int under_rr_state;

  if (!under_rr_state)
    under_rr_state = getenv ("RUNNING_UNDER_RR") ? -1 : 1;
  if (under_rr_state < 0)
    return under_rr_state;

  /* Obviously, we cannot just access it (we would SEGV trying), so we
     trick the o/s to tell us whether p is a valid pointer.
     Unfortunately, we cannot use NULL_DEVICE here, as emacs_write may
     not validate p in that case.  */

  if (emacs_pipe (fd) == 0)
    {
      bool valid = emacs_write (fd[1], p, 16) == 16;
      emacs_close (fd[1]);
      emacs_close (fd[0]);
      return valid;
    }

  return -1;
#endif
}

/* Return 2 if OBJ is a killed or special buffer object, 1 if OBJ is a
   valid lisp object, 0 if OBJ is NOT a valid lisp object, or -1 if we
   cannot validate OBJ.  This function can be quite slow, and is used
   only in debugging.  */

int
valid_lisp_object_p (Lisp_Object obj)
{
  if (SCM_IMP (obj))
    return 1;

  void* p = (void *) SCM2PTR (obj);

  if (p == &buffer_defaults || p == &buffer_local_symbols)
    return 2;

  return valid_pointer_p (p);
}

/* Like xmalloc, but makes allocation count toward the total consing.
   Return NULL for a zero-sized allocation.  */
void *
hash_table_alloc_bytes (ptrdiff_t nbytes)
{
  if (nbytes == 0)
    return NULL;
  return xmalloc (nbytes);
}

/* Like xfree, but makes allocation count toward the total consing.  */
void
hash_table_free_bytes (void *p, ptrdiff_t nbytes)
{
  xfree (p);
}


/***********************************************************************
                 Pure Storage Compatibility Functions
 ***********************************************************************/

Lisp_Object
make_pure_string (const char *data,
		  ptrdiff_t nchars, ptrdiff_t nbytes, bool multibyte)
{
  return make_specified_string (data, nchars, nbytes, multibyte);
}

Lisp_Object
make_pure_c_string (const char *data, ptrdiff_t nchars)
{
  return scm_from_utf8_stringn (data, nchars);
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

void
staticpro (Lisp_Object const *varaddress)
{
}

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

However, if there was overflow in pure space, and Emacs was dumped
using the \"unexec\" method, `garbage-collect' returns nil, because
real GC can't be done.

Note that calling this function does not guarantee that absolutely all
unreachable objects will be garbage-collected.  Emacs uses a
mark-and-sweep garbage collector, but is conservative when it comes to
collecting objects in some circumstances.

For further details, see Info node `(elisp)Garbage Collection'.  */)
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
      //make_lisp_ptr (ptr, Lisp_Cons);
    }
}

#else /* not ENABLE_CHECKING && USE_STACK_LISP_OBJECTS */

#define verify_alloca() ((void) 0)

#endif /* ENABLE_CHECKING && USE_STACK_LISP_OBJECTS */

static int
print_lisp_string (SCM obj, SCM port, scm_print_state *pstate)
{
  scm_c_write (port, "#<elisp-string \"", 16);
  scm_c_write (port, XSTRING (obj)->u.s.data, STRING_BYTES (XSTRING (obj)));
  scm_c_write (port, "\">", 2);
  return 0;
}

/* Initialization.  */

scm_t_bits lisp_misc_tag;
scm_t_bits lisp_string_tag;
scm_t_bits lisp_vectorlike_tag;

void
init_alloc_once (void)
{
  gc_cons_threshold = GC_DEFAULT_THRESHOLD;
  /* Even though Qt's contents are not set up, its address is known.  */
  Vpurify_flag = Qt;

  lisp_misc_tag = scm_make_smob_type ("elisp-misc", 0);
  lisp_string_tag = scm_make_smob_type ("elisp-string",
                                        sizeof (struct Lisp_String));
  scm_set_smob_print (lisp_string_tag, print_lisp_string);
  lisp_vectorlike_tag = scm_make_smob_type ("elisp-vectorlike", 0);

#ifdef DOUG_LEA_MALLOC
  mallopt (M_TRIM_THRESHOLD, 128 * 1024); /* Trim threshold.  */
  mallopt (M_MMAP_THRESHOLD, 64 * 1024);  /* Mmap threshold.  */
  mallopt (M_MMAP_MAX, MMAP_MAX_AREAS);   /* Max. number of mmap'ed areas.  */
#endif

  refill_memory_reserve ();

  verify_alloca ();
  init_strings ();
  init_vectors ();
}

void
init_alloc (void)
{
  Vgc_elapsed = make_float (0.0);
  gcs_done = 0;
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
prevent garbage collection during a part of the program.  But be
sure to get back to the normal value soon enough, to avoid system-wide
memory pressure, and never use a too-high value for prolonged periods
of time.
See also `gc-cons-percentage'.  */);

  DEFVAR_LISP ("gc-cons-percentage", Vgc_cons_percentage,
	       doc: /* Portion of the heap used for allocation.
Garbage collection can happen automatically once this portion of the heap
has been allocated since the last garbage collection.

By binding this temporarily to a large number, you can effectively
prevent garbage collection during a part of the program.  But be
sure to get back to the normal value soon enough, to avoid system-wide
memory pressure, and never use a too-high value for prolonged periods
of time.

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

  DEFVAR_BOOL ("guilemacs-warn-on-elisp-vector-allocation",
               guilemacs_warn_on_elisp_vector_allocation,
               doc: /* Non-nil enables Phase 0 instrumentation that logs whenever C code allocates
plain elisp vectors (struct Lisp_Vector).  Use while migrating to Guile vectors to
spot legacy allocation sites.  */);
  guilemacs_warn_on_elisp_vector_allocation = 0;

  DEFVAR_BOOL ("guilemacs-error-on-elisp-vector-allocation",
               guilemacs_error_on_elisp_vector_allocation,
               doc: /* Non-nil enables Phase 0 instrumentation that aborts when C code allocates
plain elisp vectors (struct Lisp_Vector).  Intended for CI/ERT gating once legacy
sites have been audited.  */);
  guilemacs_error_on_elisp_vector_allocation = 0;

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

  DEFVAR_LISP ("gc-elapsed", Vgc_elapsed,
	       doc: /* Accumulated time elapsed in garbage collections.
The time is in seconds as a floating point value.  */);
  DEFVAR_INT ("gcs-done", gcs_done,
              doc: /* Accumulated number of garbage collections done.  */);

  DEFVAR_INT ("integer-width", integer_width,
	      doc: /* Maximum number N of bits in safely-calculated integers.
Integers with absolute values less than 2**N do not signal a range error.
N should be nonnegative.  */);
  DEFSYM (Qalloc, "alloc");
  DEFSYM (QCemergency, ":emergency");
}

/* The below is for being able to do platform-specific stuff in .gdbinit
   without risking error messages from GDB about missing types and
   variables on other platforms.  */
#ifdef HAVE_X_WINDOWS
enum defined_HAVE_X_WINDOWS { defined_HAVE_X_WINDOWS = true };
#else
enum defined_HAVE_X_WINDOWS { defined_HAVE_X_WINDOWS = false };
#endif

#ifdef HAVE_PGTK
enum defined_HAVE_PGTK { defined_HAVE_PGTK = true };
#else
enum defined_HAVE_PGTK { defined_HAVE_PGTK = false };
#endif

#ifdef WINDOWSNT
enum defined_WINDOWSNT { defined_WINDOWSNT = true };
#else
enum defined_WINDOWSNT { defined_WINDOWSNT = false };
#endif

/* When compiled with GCC, GDB might say "No enum type named
   pvec_type" if we don't have at least one symbol with that type, and
   then xbacktrace could fail.  Similarly for the other enums and
   their values.  Some non-GCC compilers don't like these constructs.  */
#ifdef __GNUC__
extern union enums_for_gdb
{
  enum CHARTAB_SIZE_BITS CHARTAB_SIZE_BITS;
  enum char_table_specials char_table_specials;
  enum char_bits char_bits;
  enum DEFAULT_HASH_SIZE DEFAULT_HASH_SIZE;
  enum Lisp_Bits Lisp_Bits;
  enum Lisp_Closure Lisp_Closure;
  enum maxargs maxargs;
  enum MAX_ALLOCA MAX_ALLOCA;
  enum More_Lisp_Bits More_Lisp_Bits;
  enum pvec_type pvec_type;
  enum defined_HAVE_X_WINDOWS defined_HAVE_X_WINDOWS;
  enum defined_HAVE_PGTK defined_HAVE_PGTK;
  enum defined_WINDOWSNT defined_WINDOWSNT;
} const gdb_make_enums_visible;
union enums_for_gdb const EXTERNALLY_VISIBLE gdb_make_enums_visible = {0};
#endif	/* __GNUC__ */
