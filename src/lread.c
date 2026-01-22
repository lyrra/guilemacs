/* Lisp parsing and input streams.

Copyright (C) 1985-1989, 1993-1995, 1997-2025 Free Software Foundation,
Inc.

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

/* Tell globals.h to define tables needed by init_obarray.  */
#define DEFINE_SYMBOLS

#include <config.h>
#include "sysstdio.h"
#include <stdlib.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <sys/file.h>
#include <errno.h>
#include <locale.h>
#include <math.h>
#include <stat-time.h>
#include "lisp.h"
#include "guile_fns.h"
#include "dispextern.h"
#include "intervals.h"
#include "character.h"
#include "buffer.h"
#include "charset.h"
#include <epaths.h>
#include "commands.h"
#include "keyboard.h"
#include "systime.h"
#include "termhooks.h"
#include "blockinput.h"
#include <c-ctype.h>
#include <vla.h>
#include "guile.h"

#ifdef MSDOS
#include "msdos.h"
#endif

#ifdef HAVE_NS
#include "nsterm.h"
#endif

#include <unistd.h>
#include <fcntl.h>

/* File descriptor abstraction - used only for path resolution via openp().
   GuilEmacs uses SCM ports for actual file I/O, not file descriptors. */
#define lread_fd	int
#define lread_fd_cmp(n) (fd == (n))
#define lread_fd_p	(fd >= 0)
#define lread_close	emacs_close

#if IEEE_FLOATING_POINT
# include <ieee754.h>
# ifndef INFINITY
#  define INFINITY ((union ieee754_double) {.ieee = {.exponent = -1}}.d)
# endif
#else
# ifndef INFINITY
#  define INFINITY HUGE_VAL
# endif
#endif

/* Return the digit that CHARACTER stands for in the given BASE.
   Return -1 if CHARACTER is out of range for BASE,
   and -2 if CHARACTER is not valid for any supported BASE.  */
static int
digit_to_number (int character, int base)
{
  int digit;

  if ('0' <= character && character <= '9')
    digit = character - '0';
  else if ('a' <= character && character <= 'z')
    digit = character - 'a' + 10;
  else if ('A' <= character && character <= 'Z')
    digit = character - 'A' + 10;
  else
    return -2;

  return digit < base ? digit : -1;
}

Lisp_Object
intern_driver (Lisp_Object string, Lisp_Object obarray);

static SCM obarrays;

/* Phase 7+: Enhanced Guile Reader Integration - Additional control */
static bool use_guile_reader_aggressive = false;

/* The objects or placeholders read with the #n=object form.

   A hash table maps a number to either a placeholder (while the
   object is still being parsed, in case it's referenced within its
   own definition) or to the completed object.  With small integers
   for keys, it's effectively little more than a vector, but it'll
   manage any needed resizing for us.

   The variable must be reset to an empty hash table before all
   top-level calls to read0.  In between calls, it may be an empty
   hash table left unused from the previous call (to reduce
   allocations), or nil.  */
static Lisp_Object read_objects_map;

/* The recursive objects read with the #n=object form.

   Objects that might have circular references are stored here, so
   that recursive substitution knows not to keep processing them
   multiple times.

   Only objects that are completely processed, including substituting
   references to themselves (but not necessarily replacing
   placeholders for other objects still being read), are stored.

   A hash table is used for efficient lookups of keys.  We don't care
   what the value slots hold.  The variable must be set to an empty
   hash table before all top-level calls to read0.  In between calls,
   it may be an empty hash table left unused from the previous call
   (to reduce allocations), or nil.  */
static Lisp_Object read_objects_completed;

/* File and lookahead for get-file-char to read from.  Used by Fload.  */
/* Reader context structure - eliminates global state */
struct reader_context
{
  /* The input port for Guile integration.  */
  SCM port;

  /* Lookahead byte count.  */
  signed char lookahead;

  /* Lookahead bytes, in reverse order.  Keep these here because it is
     not portable to ungetc more than one byte at a time.  */
  unsigned char buf[MAX_MULTIBYTE_LENGTH - 1];
};

/* Global pointer for general reader compatibility.

   The file-specific reading path (fread0 and related functions) no longer
   uses this global - they pass context explicitly via parameters.

   This global remains only for the general reader functions (readchar,
   unreadchar, readbyte) when called with Qget_file_char. These functions
   are part of the general reader infrastructure that handles multiple
   source types (buffers, strings, files, etc.) and would require major
   refactoring to eliminate the global completely.

   TODO: Eliminate when refactoring the general reader infrastructure. */
static struct reader_context *infile;

/* Helper function to create Guile port from filename */
static SCM
file_to_guile_port (const char *filename)
{
  if (!filename)
    return SCM_BOOL_F;

  /* Open file directly with Guile instead of converting from FILE* */
  SCM filename_scm = scm_from_locale_string (filename);
  SCM mode_scm = scm_from_latin1_string ("r");

  SCM port = scm_open_file (filename_scm, mode_scm);

  /* Set the port encoding to UTF-8 to handle Unicode characters correctly */
  if (!scm_is_false (port))
    scm_set_port_encoding_x (port, scm_from_latin1_string ("UTF-8"));

  return port;
}

/* For use within read-from-string (this reader is non-reentrant!!)  */
static ptrdiff_t read_from_string_index;
static ptrdiff_t read_from_string_limit;


/* A list of file names for files being loaded in Fload.  Used to
   check for recursive loads.  */

static Lisp_Object Vloads_in_progress;

static void readevalloop (Lisp_Object, Lisp_Object, bool,
                          Lisp_Object, Lisp_Object,
                          Lisp_Object, Lisp_Object);
static void readevalloop_load (SCM port, Lisp_Object sourcename);

/* Load-specific helper function declarations */
static void elisp_skip_load_whitespace_from_c_context (struct reader_context *ctx);
static void elisp_skip_load_comment_from_c_context (struct reader_context *ctx);
static Lisp_Object elisp_read_with_load_function_from_c_context (struct reader_context *ctx);
static Lisp_Object elisp_load_read_next_expression_from_c_context (struct reader_context *ctx);
static void elisp_load_read_eval_loop_from_c_context (struct reader_context *ctx, bool printflag);
static Lisp_Object elisp_normalize_load_path_from_c_context (Lisp_Object sourcename);


/* Function that reads one byte from the current source READCHARFUN
   or unreads one byte.  If the integer argument C is -1, it returns
   one read byte, or -1 when there's no more byte in the source.  If C
   is 0 or positive, it unreads C, and the return value is not
   interesting.  */

static int freadchar (struct reader_context *);
static void funreadchar (struct reader_context *, int);

/* Handle unreading and rereading of characters.
   Write READCHAR to read a character,
   UNREAD(c) to unread c to be read again.

   These macros correctly read/unread multibyte characters.  */

#define READCHAR readchar (readcharfun, NULL)
#define UNREAD(c) unreadchar (readcharfun, c)

/* File reading now uses infile->lookahead buffer instead of global unread_char */

static int
readchar (Lisp_Object readcharfun, bool *multibyte)
{
  Lisp_Object tem;
  register int c;
  unsigned char buf[MAX_MULTIBYTE_LENGTH];
  int i, len;

  if (multibyte)
    *multibyte = 1;  /* Always multibyte in GuilEmacs */

  if (BUFFERP (readcharfun))
    {
      register struct buffer *inbuffer = XBUFFER (readcharfun);

      ptrdiff_t pt_byte = BUF_PT_BYTE (inbuffer);

      if (! BUFFER_LIVE_P (inbuffer))
	return -1;

      if (pt_byte >= BUF_ZV_BYTE (inbuffer))
	return -1;

      /* GuilEmacs: All buffers are UTF-8, no need to check multibyte flag */
      unsigned char *p = BUF_BYTE_ADDRESS (inbuffer, pt_byte);
      int clen;
      c = string_char_and_length (p, &clen);
      pt_byte += clen;
      SET_BUF_PT_BOTH (inbuffer, BUF_PT (inbuffer) + 1, pt_byte);

      return c;
    }
  else if (MARKERP (readcharfun))
    {
      register struct buffer *inbuffer = XMARKER (readcharfun)->buffer;

      ptrdiff_t bytepos = marker_byte_position (readcharfun);

      if (bytepos >= BUF_ZV_BYTE (inbuffer))
	return -1;

      /* GuilEmacs: All buffers are UTF-8, no need to check multibyte flag */
      unsigned char *p = BUF_BYTE_ADDRESS (inbuffer, bytepos);
      int clen;
      c = string_char_and_length (p, &clen);
      bytepos += clen;

      XMARKER (readcharfun)->bytepos = bytepos;
      XMARKER (readcharfun)->charpos++;

      return c;
    }
  else if (STRINGP (readcharfun))
    {
      if (read_from_string_index >= read_from_string_limit)
	c = -1;
      else
        {
          c = SREF (readcharfun, read_from_string_index);
          read_from_string_index++;
        }
      return c;
    }
  else if (EQ (readcharfun, Qget_file_char))
    {
      /* Reading from file - use freadchar directly with global infile */
      return freadchar (infile);
    }
  else
    {
      /* Custom read function */
      tem = call0 (readcharfun);

      if (NILP (tem))
        return -1;
      return XFIXNUM (tem);
    }
}

/* Unread the character C in the way appropriate for the stream READCHARFUN.
   If the stream is a user function, call it with the char as argument.  */

static void
unreadchar (Lisp_Object readcharfun, int c)
{
  if (c == -1)
    /* Don't back up the pointer if we're unreading the end-of-input mark,
       since readchar didn't advance it when we read it.  */
    ;
  else if (BUFFERP (readcharfun))
    {
      struct buffer *b = XBUFFER (readcharfun);
      ptrdiff_t charpos = BUF_PT (b);
      ptrdiff_t bytepos = BUF_PT_BYTE (b);

      /* GuilEmacs: All buffers are UTF-8 */
      bytepos -= buf_prev_char_len (b, bytepos);
      SET_BUF_PT_BOTH (b, charpos - 1, bytepos);
    }
  else if (MARKERP (readcharfun))
    {
      struct buffer *b = XMARKER (readcharfun)->buffer;
      ptrdiff_t bytepos = XMARKER (readcharfun)->bytepos;

      XMARKER (readcharfun)->charpos--;
      /* GuilEmacs: All buffers are UTF-8 */
      bytepos -= buf_prev_char_len (b, bytepos);
      XMARKER (readcharfun)->bytepos = bytepos;
    }
  else if (STRINGP (readcharfun))
    {
      read_from_string_index--;
    }
  else if (EQ (readcharfun, Qget_file_char))
    {
      /* For file reading, use infile->lookahead buffer */
      eassert (infile && infile->lookahead < sizeof infile->buf);
      infile->buf[infile->lookahead++] = c;
    }
  else
    call1 (readcharfun, make_fixnum (c));
}


/* Signal Qinvalid_read_syntax error.
   S is error string of length N (if > 0)  */

static AVOID
invalid_syntax_lisp (Lisp_Object s, Lisp_Object readcharfun)
{
  if (BUFFERP (readcharfun))
    {
      ptrdiff_t line, column;

      /* Get the line/column in the readcharfun buffer.  */
      {
	dynwind_begin ();

	record_unwind_protect_excursion ();
	set_buffer_internal (XBUFFER (readcharfun));
	line = count_lines (BEGV_BYTE, PT_BYTE) + 1;
	column = current_column ();
	dynwind_end ();
      }

      xsignal2 (Qinvalid_read_syntax,
	       list3 (s, make_fixnum (line), make_fixnum (column)),
                Qnil);
    }
  else
    xsignal2 (Qinvalid_read_syntax, s, Qnil);
}

static AVOID
invalid_syntax (const char *s, Lisp_Object readcharfun)
{
  invalid_syntax_lisp (build_string (s), readcharfun);
}

/* An in-progress substitution of OBJECT for PLACEHOLDER.  */
struct subst
{
  Lisp_Object object;
  Lisp_Object placeholder;

  /* Hash table of subobjects of OBJECT that might be circular.  If
     Qt, all such objects might be circular.  */
  Lisp_Object completed;

  /* List of subobjects of OBJECT that have already been visited.  */
  Lisp_Object seen;
};

static Lisp_Object read_internal_start (Lisp_Object, Lisp_Object,
                                        Lisp_Object, bool);
static Lisp_Object read0 (Lisp_Object, bool);
static Lisp_Object fread0 (SCM port);
static Lisp_Object elisp_parse_with_eof_check_from_c_context (SCM port, int);

/* Phase 6: Guile Reader Migration - Forward declarations */
static SCM guile_reader_error_handler (void *data, SCM key, SCM args);
static SCM buffer_to_guile_port (Lisp_Object buffer);

Lisp_Object elisp_read_from_port (Lisp_Object port);

/* Adapter functions for file reading through reader_context */
static int
file_read_char (void *context)
{
  struct reader_context *ctx = (struct reader_context *) context;
  return freadchar (ctx);
}

static void
file_unread_char (void *context, int c)
{
  struct reader_context *ctx = (struct reader_context *) context;
  funreadchar (ctx, c);
}

static Lisp_Object substitute_object_recurse (struct subst *, Lisp_Object);
static void substitute_in_interval (INTERVAL, void *);


/* Get a character from the tty.  */

/* Read input events until we get one that's acceptable for our purposes.

   If NO_SWITCH_FRAME, switch-frame events are stashed
   until we get a character we like, and then stuffed into
   unread_switch_frame.

   If ASCII_REQUIRED, check function key events to see
   if the unmodified version of the symbol has a Qascii_character
   property, and use that character, if present.

   If ERROR_NONASCII, signal an error if the input we
   get isn't an ASCII character with modifiers.  If it's false but
   ASCII_REQUIRED is true, just re-read until we get an ASCII
   character.

   If INPUT_METHOD, invoke the current input method
   if the character warrants that.

   If SECONDS is a number, wait that many seconds for input, and
   return Qnil if no input arrives within that time.

   If text conversion is enabled and ASCII_REQUIRED, temporarily
   disable any input method which wants to perform edits, unless
   `disable-inhibit-text-conversion'.  */

static Lisp_Object
read_filtered_event (bool no_switch_frame, bool ascii_required,
		     bool error_nonascii, bool input_method, Lisp_Object seconds)
{
  Lisp_Object val, delayed_switch_frame;
  struct timespec end_time;

#ifdef HAVE_WINDOW_SYSTEM
  if (display_hourglass_p)
    cancel_hourglass ();
#endif

#ifdef HAVE_TEXT_CONVERSION
  dynwind_begin ();

  /* Don't use text conversion when trying to just read a
     character.  */

  if (ascii_required && !disable_inhibit_text_conversion)
    {
      disable_text_conversion ();
      record_unwind_protect_void (resume_text_conversion);
    }
#endif

  delayed_switch_frame = Qnil;

  /* Compute timeout.  */
  if (NUMBERP (seconds))
    {
      double duration = XFLOATINT (seconds);
      struct timespec wait_time = dtotimespec (duration);
      end_time = timespec_add (current_timespec (), wait_time);
    }

  /* Read until we get an acceptable event.  */
 retry:
  do
    val = read_char (0, Qnil, (input_method ? Qnil : Qt), 0,
		     NUMBERP (seconds) ? &end_time : NULL);
  while (FIXNUMP (val) && XFIXNUM (val) == -2); /* wrong_kboard_jmpbuf */

  if (BUFFERP (val))
    goto retry;

  /* `switch-frame' events are put off until after the next ASCII
     character.  This is better than signaling an error just because
     the last characters were typed to a separate minibuffer frame,
     for example.  Eventually, some code which can deal with
     switch-frame events will read it and process it.  */
  if (no_switch_frame
      && EVENT_HAS_PARAMETERS (val)
      && EQ (EVENT_HEAD_KIND (EVENT_HEAD (val)), Qswitch_frame))
    {
      delayed_switch_frame = val;
      goto retry;
    }

  if (ascii_required && !(NUMBERP (seconds) && NILP (val)))
    {
      /* Convert certain symbols to their ASCII equivalents.  */
      if (SYMBOLP (val))
	{
	  Lisp_Object tem, tem1;
	  tem = Fget (val, Qevent_symbol_element_mask);
	  if (!NILP (tem))
	    {
	      tem1 = Fget (Fcar (tem), Qascii_character);
	      /* Merge this symbol's modifier bits
		 with the ASCII equivalent of its basic code.  */
	      if (!NILP (tem1))
		XSETFASTINT (val, XFIXNUM (tem1) | XFIXNUM (Fcar (Fcdr (tem))));
	    }
	}

      /* If we don't have a character now, deal with it appropriately.  */
      if (!FIXNUMP (val))
	{
	  if (error_nonascii)
	    {
	      Vunread_command_events = list1 (val);
	      error ("Non-character input-event");
	    }
	  else
	    goto retry;
	}
    }

  if (! NILP (delayed_switch_frame))
    unread_switch_frame = delayed_switch_frame;

#if 0

#ifdef HAVE_WINDOW_SYSTEM
  if (display_hourglass_p)
    start_hourglass ();
#endif

#endif

#ifdef HAVE_TEXT_CONVERSION
  dynwind_end ();
#else
#endif
  return val;
}

DEFUN ("read-char", Fread_char, Sread_char, 0, 3, 0,
       doc: /* Read a character event from the command input (keyboard or macro).
It is returned as a number.
If the event has modifiers, they are resolved and reflected in the
returned character code if possible (e.g. C-SPC yields 0 and C-a yields 97).
If some of the modifiers cannot be reflected in the character code, the
returned value will include those modifiers, and will not be a valid
character code: it will fail the `characterp' test.  Use `event-basic-type'
to recover the character code with the modifiers removed.

If the user generates an event which is not a character (i.e. a mouse
click or function key event), `read-char' signals an error.  As an
exception, switch-frame events are put off until non-character events
can be read.
If you want to read non-character events, or ignore them, call
`read-event' or `read-char-exclusive' instead.

If the optional argument PROMPT is non-nil, display that as a prompt.
If PROMPT is nil or the string \"\", the key sequence/events that led
to the current command is used as the prompt.

If the optional argument INHERIT-INPUT-METHOD is non-nil and some
input method is turned on in the current buffer, that input method
is used for reading a character.

If the optional argument SECONDS is non-nil, it should be a number
specifying the maximum number of seconds to wait for input.  If no
input arrives in that time, return nil.  SECONDS may be a
floating-point value.

If `inhibit-interaction' is non-nil, this function will signal an
`inhibited-interaction' error.  */)
  (Lisp_Object prompt, Lisp_Object inherit_input_method, Lisp_Object seconds)
{
  Lisp_Object val;

  barf_if_interaction_inhibited ();

  if (! NILP (prompt))
    {
      cancel_echoing ();
      message_with_string ("%s", prompt, 0);
    }
  val = read_filtered_event (1, 1, 1, ! NILP (inherit_input_method), seconds);

  return (NILP (val) ? Qnil
	  : make_fixnum (char_resolve_modifier_mask (XFIXNUM (val))));
}

DEFUN ("read-event", Fread_event, Sread_event, 0, 3, 0,
       doc: /* Read an event object from the input stream.

If you want to read non-character events, consider calling `read-key'
instead.  `read-key' will decode events via `input-decode-map' that
`read-event' will not.  On a terminal this includes function keys such
as <F7> and <RIGHT>, or mouse events generated by `xterm-mouse-mode'.

If the optional argument PROMPT is non-nil, display that as a prompt.
If PROMPT is nil or the string \"\", the key sequence/events that led
to the current command is used as the prompt.

If the optional argument INHERIT-INPUT-METHOD is non-nil and some
input method is turned on in the current buffer, that input method
is used for reading a character.

If the optional argument SECONDS is non-nil, it should be a number
specifying the maximum number of seconds to wait for input.  If no
input arrives in that time, return nil.  SECONDS may be a
floating-point value.

If `inhibit-interaction' is non-nil, this function will signal an
`inhibited-interaction' error.  */)
  (Lisp_Object prompt, Lisp_Object inherit_input_method, Lisp_Object seconds)
{
  barf_if_interaction_inhibited ();

  if (! NILP (prompt))
    {
      cancel_echoing ();
      message_with_string ("%s", prompt, 0);
    }
  return read_filtered_event (0, 0, 0, ! NILP (inherit_input_method), seconds);
}

DEFUN ("read-char-exclusive", Fread_char_exclusive, Sread_char_exclusive, 0, 3, 0,
       doc: /* Read a character event from the command input (keyboard or macro).
It is returned as a number.  Non-character events are ignored.
If the event has modifiers, they are resolved and reflected in the
returned character code if possible (e.g. C-SPC yields 0 and C-a yields 97).
If some of the modifiers cannot be reflected in the character code, the
returned value will include those modifiers, and will not be a valid
character code: it will fail the `characterp' test.  Use `event-basic-type'
to recover the character code with the modifiers removed.

If the optional argument PROMPT is non-nil, display that as a prompt.
If PROMPT is nil or the string \"\", the key sequence/events that led
to the current command is used as the prompt.

If the optional argument INHERIT-INPUT-METHOD is non-nil and some
input method is turned on in the current buffer, that input method
is used for reading a character.

If the optional argument SECONDS is non-nil, it should be a number
specifying the maximum number of seconds to wait for input.  If no
input arrives in that time, return nil.  SECONDS may be a
floating-point value.

If `inhibit-interaction' is non-nil, this function will signal an
`inhibited-interaction' error.  */)
  (Lisp_Object prompt, Lisp_Object inherit_input_method, Lisp_Object seconds)
{
  Lisp_Object val;

  barf_if_interaction_inhibited ();

  if (! NILP (prompt))
    {
      cancel_echoing ();
      message_with_string ("%s", prompt, 0);
    }

  val = read_filtered_event (1, 1, 0, ! NILP (inherit_input_method), seconds);

  return (NILP (val) ? Qnil
	  : make_fixnum (char_resolve_modifier_mask (XFIXNUM (val))));
}



typedef enum {
  Cookie_None,			/* no cookie */
  Cookie_Dyn,			/* explicit dynamic binding */
  Cookie_Lex			/* explicit lexical binding */
} lexical_cookie_t;

/* Determine if the lisp code read using READCHARFUN defines a
   `lexical-binding' file variable return its value.
   After returning, the stream is positioned following the first line,
   if it is a comment or #! line, otherwise nothing is read.  */

static lexical_cookie_t
lisp_file_lexical_cookie (Lisp_Object readcharfun)
{
  int ch = READCHAR;

  if (ch == '#')
    {
      ch = READCHAR;
      if (ch != '!')
        {
          UNREAD (ch);
          UNREAD ('#');
          return Cookie_None;
        }
      while (ch != '\n' && ch != EOF)
        ch = READCHAR;
      if (ch == '\n') ch = READCHAR;
      /* It is OK to leave the position after a #! line, since
	 that is what read0 does.  */
    }

  if (ch != ';')
    /* The first line isn't a comment, just give up.  */
    {
      UNREAD (ch);
      return Cookie_None;
    }
  else
    /* Look for an appropriate file-variable in the first line.  */
    {
      lexical_cookie_t rv = Cookie_None;
      enum {
	NOMINAL, AFTER_FIRST_DASH, AFTER_ASTERIX
      } beg_end_state = NOMINAL;
      bool in_file_vars = 0;

#define UPDATE_BEG_END_STATE(ch)
  if (beg_end_state == NOMINAL)
    beg_end_state = (ch == '-' ? AFTER_FIRST_DASH : NOMINAL);
  else if (beg_end_state == AFTER_FIRST_DASH)
    beg_end_state = (ch == '*' ? AFTER_ASTERIX : NOMINAL);
  else if (beg_end_state == AFTER_ASTERIX)
    {
      if (ch == '-')
	in_file_vars = !in_file_vars;
      beg_end_state = NOMINAL;
    }

      /* Skip until we get to the file vars, if any.  */
      do
	{
	  ch = READCHAR;
	  UPDATE_BEG_END_STATE (ch);
	}
      while (!in_file_vars && ch != '\n' && ch != EOF);

      while (in_file_vars)
	{
	  char var[100], val[100];
	  unsigned i;

	  ch = READCHAR;

	  /* Read a variable name.  */
	  while (ch == ' ' || ch == '\t')
	    ch = READCHAR;

	  i = 0;
	  beg_end_state = NOMINAL;
	  while (ch != ':' && ch != '\n' && ch != EOF && in_file_vars)
	    {
	      if (i < sizeof var - 1)
		var[i++] = ch;
	      UPDATE_BEG_END_STATE (ch);
	      ch = READCHAR;
	    }

	  /* Stop scanning if no colon was found before end marker.  */
	  if (!in_file_vars || ch == '\n' || ch == EOF)
	    break;

	  while (i > 0 && (var[i - 1] == ' ' || var[i - 1] == '\t'))
	    i--;
	  var[i] = '\0';

	  if (ch == ':')
	    {
	      /* Read a variable value.  */
	      ch = READCHAR;

	      while (ch == ' ' || ch == '\t')
		ch = READCHAR;

	      i = 0;
	      beg_end_state = NOMINAL;
	      while (ch != ';' && ch != '\n' && ch != EOF && in_file_vars)
		{
		  if (i < sizeof val - 1)
		    val[i++] = ch;
		  UPDATE_BEG_END_STATE (ch);
		  ch = READCHAR;
		}
	      if (! in_file_vars)
		/* The value was terminated by an end-marker, which remove.  */
		i -= 3;
	      while (i > 0 && (val[i - 1] == ' ' || val[i - 1] == '\t'))
		i--;
	      val[i] = '\0';

	      if (strcmp (var, "lexical-binding") == 0)
		/* This is it...  */
		{
		  rv = strcmp (val, "nil") != 0 ? Cookie_Lex : Cookie_Dyn;
		  break;
		}
	    }
	}

      while (ch != '\n' && ch != EOF)
	ch = READCHAR;

      return rv;
    }
}

/* Callback for record_unwind_protect.  Restore the old load list OLD,
   after loading a file successfully.  */

static void
record_load_unwind (Lisp_Object old)
{
  Vloads_in_progress = old;
}

/* Check if a file (by base name) is currently being loaded via C's load.
   Used by autoload-do-load to detect circular autoloads.  */
bool
file_in_loads_in_progress (const char *basename)
{
  for (Lisp_Object tail = Vloads_in_progress; CONSP (tail); tail = XCDR (tail))
    {
      Lisp_Object path = XCAR (tail);
      if (STRINGP (path))
        {
          const char *pathstr = SDATA (path);
          /* Check if path ends with /basename.el or /basename */
          size_t pathlen = strlen (pathstr);
          size_t baselen = strlen (basename);
          if (pathlen > baselen)
            {
              const char *suffix = pathstr + pathlen - baselen;
              if ((suffix[-1] == '/' || suffix[-1] == '\\')
                  && strcmp (suffix, basename) == 0)
                return true;
              /* Also check with .el suffix */
              if (pathlen > baselen + 3
                  && strcmp (pathstr + pathlen - 3, ".el") == 0)
                {
                  suffix = pathstr + pathlen - baselen - 3;
                  if ((suffix[-1] == '/' || suffix[-1] == '\\')
                      && strncmp (suffix, basename, baselen) == 0)
                    return true;
                }
            }
        }
    }
  return false;
}

DEFUN ("get-load-suffixes", Fget_load_suffixes, Sget_load_suffixes, 0, 0, 0,
       doc: /* Return the suffixes that `load' should try if a suffix is
required.
This uses the variables `load-suffixes' and `load-file-rep-suffixes'.  */)
  (void)
{
  /* MIGRATED TO SCHEME: List processing logic moved to Scheme for better maintainability */
  SCM get_suffixes_func = scm_c_private_ref ("emacs-elisp runtime",
                                             "elisp-get-load-suffixes");
  return scm_call_0 (get_suffixes_func);
}

/* Return true if STRING ends with SUFFIX.  */
bool
suffix_p (Lisp_Object string, const char *suffix)
{
  SCM suffix_scm = scm_from_utf8_string (suffix);
  return scm_is_true (scm_string_suffix_p (suffix_scm, string,
                                           SCM_UNDEFINED, SCM_UNDEFINED,
                                           SCM_UNDEFINED, SCM_UNDEFINED));
}

/* Compute the filename we want in `load-history' and `load-file-name'.  */

static Lisp_Object
compute_found_effective (Lisp_Object found)
{
  SCM effective_func = scm_c_private_ref ("emacs-elisp runtime",
                                         "elisp-compute-found-effective");
  return scm_call_1 (effective_func, found);
}

static void
loadhist_initialize (Lisp_Object filename)
{
  SCM loadhist_func = scm_c_private_ref ("emacs-elisp runtime",
                                        "elisp-loadhist-initialize");
  Lisp_Object binding = scm_call_1 (loadhist_func, filename);
  specbind (Qcurrent_load_list, binding);
}

static void
sync_guile_reader (struct reader_context *ctx)
{
  if (ctx->lookahead > 1) {
    fprintf(stderr, "sync_guile_reader: lookahead is too large: %d\n", ctx->lookahead);
    emacs_abort ();
  }
  if (ctx->lookahead < 0) {
    fprintf(stderr, "sync_guile_reader: lookahead is negative (!?): %d\n", ctx->lookahead);
    emacs_abort ();
  }

  if (ctx->lookahead) {
    scm_ungetc (ctx->buf[ctx->lookahead - 1], ctx->port);
    ctx->lookahead = 0;
  }
}

Lisp_Object
save_match_data_load (Lisp_Object file, Lisp_Object noerror,
		      Lisp_Object nomessage, Lisp_Object nosuffix,
		      Lisp_Object must_suffix)
{
  /* MIGRATED TO SCHEME: Match data protection wrapper */
  dynwind_begin ();
  record_unwind_save_match_data ();

  SCM wrapper_func = scm_c_private_ref ("emacs-elisp runtime",
                                        "elisp-load-with-match-data-protection");
  Lisp_Object result = scm_call_5 (wrapper_func, file, noerror, nomessage, nosuffix, must_suffix);

  dynwind_end ();
  return result;
}

static bool
complete_filename_p (Lisp_Object pathname)
{
  SCM complete_func = scm_c_private_ref ("emacs-elisp runtime",
                                        "elisp-complete-filename?");
  SCM result = scm_call_1 (complete_func, pathname);
  return !NILP (result);
}

DEFUN ("locate-file-internal", Flocate_file_internal, Slocate_file_internal, 2, 4, 0,
       doc: /* Search for FILENAME through PATH.
Returns the file's name in absolute form, or nil if not found.
If SUFFIXES is non-nil, it should be a list of suffixes to append to
file name when searching.
If non-nil, PREDICATE is used instead of `file-readable-p'.
PREDICATE can also be an integer to pass to the faccessat(2) function,
in which case file-name-handlers are ignored.
This function will normally skip directories, so if you want it to find
directories, make sure the PREDICATE function returns `dir-ok' for them.  */)
  (Lisp_Object filename, Lisp_Object path, Lisp_Object suffixes, Lisp_Object predicate)
{
  Lisp_Object file;
  int fd = openp (path, filename, suffixes, &file, predicate, false, true,
		  NULL);
  if (NILP (predicate) && fd >= 0)
    emacs_close (fd);
  return file;
}

#ifdef HAVE_NATIVE_COMP
static bool
maybe_swap_for_eln1 (Lisp_Object src_name, Lisp_Object eln_name,
		     Lisp_Object *filename, int *fd, struct timespec mtime)
{
  struct stat eln_st;
  int eln_fd = emacs_open (SSDATA (ENCODE_FILE (eln_name)), O_RDONLY, 0);

  if (eln_fd > 0)
    {
      if (sys_fstat (eln_fd, &eln_st) || S_ISDIR (eln_st.st_mode))
	emacs_close (eln_fd);
      else
	{
	  struct timespec eln_mtime = get_stat_mtime (&eln_st);
	  if (timespec_cmp (eln_mtime, mtime) >= 0)
	    {
	      emacs_close (*fd);
	      *fd = eln_fd;
	      *filename = eln_name;
	      /* Store the eln -> el relation.  */
	      Fputhash (Ffile_name_nondirectory (eln_name),
			src_name, Vcomp_eln_to_el_h);
	      return true;
	    }
	  else
	    emacs_close (eln_fd);
	}
    }

  return false;
}
#endif

/* Look for a suitable .eln file to be loaded in place of FILENAME.
   If found replace the content of FILENAME and FD. */

static void
maybe_swap_for_eln (bool no_native, Lisp_Object *filename, int *fd,
		    struct timespec mtime)
{
#ifdef HAVE_NATIVE_COMP

  if (no_native
      || load_no_native)
    Fputhash (*filename, Qt, V_comp_no_native_file_h);
  else
    Fremhash (*filename, V_comp_no_native_file_h);

  if (no_native
      || load_no_native
      || !suffix_p (*filename, ".elc"))
    return;

  /* Search eln in the eln-cache directories.  */
  Lisp_Object eln_path_tail = Vnative_comp_eln_load_path;
  Lisp_Object src_name =
    Fsubstring (*filename, Qnil, make_fixnum (-1));
  if (NILP (Ffile_exists_p (src_name)))
    {
      src_name = concat2 (src_name, build_string (".gz"));
      if (NILP (Ffile_exists_p (src_name)))
	{
	  if (!NILP (find_symbol_value (
		       Qnative_comp_warning_on_missing_source)))
	    {
	      /* If we have an installation without any .el files,
		 there's really no point in giving a warning here,
		 because that will trigger a cascade of warnings.  So
		 just do a sanity check and refuse to do anything if we
		 can't find even central .el files.  */
	      if (NILP (Flocate_file_internal (build_string ("simple.el"),
					       Vload_path,
					       Qnil, Qnil)))
		return;
	      Vdelayed_warnings_list
		= Fcons (list2
			 (Qnative_compiler,
			  CALLN (Fformat,
				 build_string ("Cannot look up .eln file "
					       "for %s because no source "
					       "file was found for it"),
				 *filename)),
			 Vdelayed_warnings_list);
	      return;
	    }
	}
    }
  Lisp_Object eln_rel_name = Fcomp_el_to_eln_rel_filename (src_name);

  Lisp_Object dir = Qnil;
  FOR_EACH_TAIL_SAFE (eln_path_tail)
    {
      dir = XCAR (eln_path_tail);
      Lisp_Object eln_name =
	Fexpand_file_name (eln_rel_name,
			   Fexpand_file_name (Vcomp_native_version_dir, dir));
      if (maybe_swap_for_eln1 (src_name, eln_name, filename, fd, mtime))
	return;
    }

  /* Look also in preloaded subfolder of the last entry in
     `comp-eln-load-path'.  */
  dir = Fexpand_file_name (build_string ("preloaded"),
			   Fexpand_file_name (Vcomp_native_version_dir,
					      dir));
  maybe_swap_for_eln1 (src_name, Fexpand_file_name (eln_rel_name, dir),
		       filename, fd, mtime);
#endif
}

/* Search for a file whose name is STR, looking in directories
   in the Lisp list PATH, and trying suffixes from SUFFIX.
   On success, return a file descriptor (or 1 or -2 as described below).
   On failure, return -1 and set errno.

   SUFFIXES is a list of strings containing possible suffixes.
   The empty suffix is automatically added if the list is empty.

   PREDICATE t means the files are binary.
   PREDICATE non-nil and non-t means don't open the files,
   just look for one that satisfies the predicate.  In this case,
   return -2 on success.  The predicate can be a lisp function or
   an integer to pass to `access' (in which case file-name-handlers
   are ignored).

   If STOREPTR is nonzero, it points to a slot where the name of
   the file actually found should be stored as a Lisp string.
   nil is stored there on failure.

   If the file we find is remote, return -2
   but store the found remote file name in *STOREPTR.

   If NEWER is true, try all SUFFIXes and return the result for the
   newest file that exists.  Does not apply to remote files,
   platform-specific files, or if a non-nil and non-t PREDICATE is
   specified.

   If NO_NATIVE is true do not try to load native code.

   If PLATFORM is non-NULL and the file being loaded lies in a special
   directory, such as the Android `/assets' directory, return a handle
   to that directory in *PLATFORM instead of a file descriptor; in
   that case, value is -3.  */

int
openp (Lisp_Object path, Lisp_Object str, Lisp_Object suffixes,
       Lisp_Object *storeptr, Lisp_Object predicate, bool newer,
       bool no_native, void **platform)
{
  ptrdiff_t fn_size = 100;
  char buf[100];
  char *fn = buf;
  bool absolute;
  ptrdiff_t want_length;
  Lisp_Object filename;
  Lisp_Object string, tail, encoded_fn, save_string;
  ptrdiff_t max_suffix_len = 0;
  int last_errno = ENOENT;
  int save_fd = -1;
  USE_SAFE_ALLOCA;

  /* The last-modified time of the newest matching file found.
     Initialize it to something less than all valid timestamps.  */
  struct timespec save_mtime = make_timespec (TYPE_MINIMUM (time_t), -1);

  CHECK_STRING (str);

  tail = suffixes;
  FOR_EACH_TAIL_SAFE (tail)
    {
      CHECK_STRING_CAR (tail);
      max_suffix_len = max (max_suffix_len,
			    SBYTES (XCAR (tail)));
    }

  string = filename = encoded_fn = save_string = Qnil;

  if (storeptr)
    *storeptr = Qnil;

  absolute = complete_filename_p (str);

  AUTO_LIST1 (just_use_str, Qnil);
  if (NILP (path))
    path = just_use_str;

  /* Go through all entries in the path and see whether we find the
     executable. */
  FOR_EACH_TAIL_SAFE (path)
   {
    ptrdiff_t baselen, prefixlen;

    if (EQ (path, just_use_str))
      filename = str;
    else
      filename = Fexpand_file_name (str, XCAR (path));
    if (!complete_filename_p (filename))
      /* If there are non-absolute elts in PATH (eg ".").  */
      /* Of course, this could conceivably lose if luser sets
	 default-directory to be something non-absolute...  */
      {
	filename = Fexpand_file_name (filename, BVAR (current_buffer, directory));
	if (!complete_filename_p (filename))
	  /* Give up on this path element!  */
	  continue;
      }

    /* Calculate maximum length of any filename made from
       this path element/specified file name and any possible suffix.  */
    want_length = max_suffix_len + SBYTES (filename);
    if (fn_size <= want_length)
      {
	fn_size = 100 + want_length;
	fn = SAFE_ALLOCA (fn_size);
      }

    /* Copy FILENAME's data to FN but remove starting /: if any.  */
    prefixlen = ((SCHARS (filename) > 2
		  && guile_path_starts_with (filename, "/:"))
		 ? 2 : 0);
    baselen = SBYTES (filename) - prefixlen;
    memcpy (fn, SDATA (filename) + prefixlen, baselen);

    /* Loop over suffixes.  */
    AUTO_LIST1 (empty_string_only, build_string(""));
    tail = NILP (suffixes) ? empty_string_only : suffixes;
    FOR_EACH_TAIL_SAFE (tail)
      {
	Lisp_Object suffix = XCAR (tail);
	ptrdiff_t fnlen, lsuffix = SBYTES (suffix);
	Lisp_Object handler;

	/* Make complete filename by appending SUFFIX.  */
	memcpy (fn + baselen, SDATA (suffix), lsuffix + 1);
	fnlen = baselen + lsuffix;

	/* Check that the file exists and is not a directory.  */
	/* We used to only check for handlers on non-absolute file names:
	   if (absolute)
	   handler = Qnil;
	   else
	   handler = Ffind_file_name_handler (filename, Qfile_exists_p);
	   It's not clear why that was the case and it breaks things like
	   (load "/bar.el") where the file is actually "/bar.el.gz".  */
	/* GuilEmacs: All strings are UTF-8, including file names */
        string = build_string (fn);
	handler = Ffind_file_name_handler (string, Qfile_exists_p);
	if ((!NILP (handler) || (!NILP (predicate) && !EQ (predicate, Qt)))
	    && !FIXNATP (predicate))
	  {
	    bool exists;
	    if (NILP (predicate) || EQ (predicate, Qt))
	      exists = !NILP (Ffile_readable_p (string));
	    else
	      {
		Lisp_Object tmp = call1 (predicate, string);
		if (NILP (tmp))
		  exists = false;
		else if (EQ (tmp, Qdir_ok)
			 || NILP (Ffile_directory_p (string)))
		  exists = true;
		else
		  {
		    exists = false;
		    last_errno = EISDIR;
		  }
	      }

	    if (exists)
	      {
		/* We succeeded; return this descriptor and filename.  */
		if (storeptr)
		  *storeptr = string;
		SAFE_FREE ();
		return -2;
	      }
	  }
	else
	  {
	    int fd;
	    const char *pfn;
	    struct stat st;

	    encoded_fn = ENCODE_FILE (string);
	    pfn = SSDATA (encoded_fn);

	    /* Check that we can access or open it.  */
	    if (FIXNATP (predicate))
	      {
		fd = -1;
		if (INT_MAX < XFIXNAT (predicate))
		  last_errno = EINVAL;
		else if (sys_faccessat (AT_FDCWD, pfn, XFIXNAT (predicate),
					AT_EACCESS)
			 == 0)
		  {
		    if (file_directory_p (encoded_fn))
		      last_errno = EISDIR;
		    else if (errno == ENOENT || errno == ENOTDIR)
		      fd = 1;
		    else
		      last_errno = errno;
		  }
		else if (! (errno == ENOENT || errno == ENOTDIR))
		  last_errno = errno;
	      }
	    else
	      {
                /*  In some systems (like Windows) finding out if a
                    file exists is cheaper to do than actually opening
                    it.  Only open the file when we are sure that it
                    exists.  */
#ifdef WINDOWSNT
                if (sys_faccessat (AT_FDCWD, pfn, R_OK, AT_EACCESS))
                  fd = -1;
                else
#endif
		  {
#if !defined USE_ANDROID_ASSETS
		    fd = emacs_open (pfn, O_RDONLY, 0);
#else
		    if (platform)
		      {
			platform_fd = android_open_asset (pfn, O_RDONLY, 0);

			if (platform_fd.asset
			    && platform_fd.asset != (void *) -1)
			  {
			    *storeptr = string;
			    goto handle_platform_fd;
			  }

			if (platform_fd.asset == (void *) -1)
			  fd = -1;
			else
			  fd = platform_fd.fd;
		      }
		    else
		      fd = emacs_open (pfn, O_RDONLY, 0);
#endif
		  }

		if (fd < 0)
		  {
		    if (! (errno == ENOENT || errno == ENOTDIR))
		      last_errno = errno;
		  }
		else
		  {
		    int err = (sys_fstat (fd, &st) != 0 ? errno
			       : S_ISDIR (st.st_mode) ? EISDIR : 0);
		    if (err)
		      {
			last_errno = err;
			emacs_close (fd);
			fd = -1;
		      }
		  }
	      }

	    if (fd >= 0)
	      {
		if (newer && !FIXNATP (predicate))
		  {
		    struct timespec mtime = get_stat_mtime (&st);

		    if (timespec_cmp (mtime, save_mtime) <= 0)
		      emacs_close (fd);
		    else
		      {
			if (0 <= save_fd)
			  emacs_close (save_fd);
			save_fd = fd;
			save_mtime = mtime;
			save_string = string;
		      }
		  }
		else
		  {
		    maybe_swap_for_eln (no_native, &string, &fd,
					get_stat_mtime (&st));
		    /* We succeeded; return this descriptor and filename.  */
		    if (storeptr)
		      *storeptr = string;
		    SAFE_FREE ();
		    return fd;
		  }
	      }

	    /* No more suffixes.  Return the newest.  */
	    if (0 <= save_fd && ! CONSP (XCDR (tail)))
	      {
		maybe_swap_for_eln (no_native, &save_string, &save_fd,
				    save_mtime);
		if (storeptr)
		  *storeptr = save_string;
		SAFE_FREE ();
		return save_fd;
	      }
	  }
      }
    if (absolute)
      break;
   }

  SAFE_FREE ();
  errno = last_errno;
  return -1;

#ifdef USE_ANDROID_ASSETS
 handle_platform_fd:

  /* Here, openp found a platform specific file descriptor.  It can't
     be a directory under Android, so return it in *PLATFORM and then
     -3 as the file descriptor.  */
  *platform = platform_fd.asset;
  return -3;
#endif
}




/* Signal an `end-of-file' error, if possible with file name
   information.  */

static AVOID
end_of_file_error (void)
{
  if (STRINGP (Vload_true_file_name))
    xsignal1 (Qend_of_file, Vload_true_file_name);

  xsignal0 (Qend_of_file);
}

/* GuilEmacs: All strings are UTF-8, unibyte parameter is ignored.
   READFUN, if non-nil, is used instead of `read'.

   START, END specify region to read in current buffer (from eval-region).
   If the input is not from a buffer, they must be nil.  */

static void
readevalloop (Lisp_Object readcharfun,
	      Lisp_Object sourcename,
	      bool printflag,
	      Lisp_Object unibyte, /* Ignored - kept for API compatibility */
	      Lisp_Object readfun,
	      Lisp_Object start, Lisp_Object end)
{
  int c;
  Lisp_Object val;
  dynwind_begin ();
  struct buffer *b = 0;
  bool continue_reading_p;
  Lisp_Object lex_bound;
  /* True if reading an entire buffer.  */
  bool whole_buffer = 0;
  /* True on the first time around.  */
  bool first_sexp = 1;

  if (!NILP (sourcename))
    CHECK_STRING (sourcename);

  Lisp_Object compile_fn = 0;

  if (MARKERP (readcharfun))
    {
      if (NILP (start))
	start = readcharfun;
    }

  if (BUFFERP (readcharfun))
    b = XBUFFER (readcharfun);
  else if (MARKERP (readcharfun))
    b = XMARKER (readcharfun)->buffer;

  /* We assume START is nil when input is not from a buffer.  */
  if (! NILP (start) && !b)
    emacs_abort ();

  specbind (Qstandard_input, readcharfun);
  /* Note: load_convert_to_unibyte logic removed - pure UTF-8 strings only */

  /* If lexical binding is active (either because it was specified in
     the file's header, or via a buffer-local variable), create an empty
     lexical environment, otherwise, turn off lexical binding.  */
  lex_bound = find_symbol_value (Qlexical_binding);
  specbind (Qinternal_interpreter_environment,
	    (NILP (lex_bound) || BASE_EQ (lex_bound, Qunbound)
	     ? Qnil : list1 (Qt)));
  specbind (Qmacroexp__dynvars, Vmacroexp__dynvars);

  /* Ensure sourcename is absolute, except whilst preloading.  */
  if (!NILP (sourcename) && !NILP (Ffile_name_absolute_p (sourcename)))
    sourcename = Fexpand_file_name (sourcename, Qnil);

  loadhist_initialize (sourcename);

  continue_reading_p = 1;
  while (continue_reading_p)
    {
      dynwind_begin ();

      if (b != 0 && !BUFFER_LIVE_P (b))
	error ("Reading from killed buffer");

      if (!NILP (start))
	{
	  /* Switch to the buffer we are reading from.  */
	  record_unwind_protect_excursion ();
	  set_buffer_internal (b);

	  /* Save point in it.  */
	  record_unwind_protect_excursion ();
	  /* Save ZV in it.  */
	  record_unwind_protect (save_restriction_restore, save_restriction_save ());
	  labeled_restrictions_remove_in_current_buffer ();
	  /* Those get unbound after we read one expression.  */

	  /* Set point and ZV around stuff to be read.  */
	  Fgoto_char (start);
	  if (!NILP (end))
	    Fnarrow_to_region (make_fixnum (BEGV), end);

	  /* Just for cleanliness, convert END to a marker
	     if it is an integer.  */
	  if (FIXNUMP (end))
	    end = Fpoint_max_marker ();
	}

      /* On the first cycle, we can easily test here
	 whether we are reading the whole buffer.  */
      if (b && first_sexp)
	whole_buffer = (BUF_PT (b) == BUF_BEG (b) && BUF_ZV (b) == BUF_Z (b));

    read_next:
      c = READCHAR;
      if (c == ';')
	{
	  while ((c = READCHAR) != '\n' && c != -1);
	  goto read_next;
	}
      if (c < 0)
	{
	  dynwind_end ();
	  break;
	}

      /* Ignore whitespace here, so we can detect eof.  */
      if (c == ' ' || c == '\t' || c == '\n' || c == '\f' || c == '\r'
	  || c == NO_BREAK_SPACE)
	goto read_next;
      UNREAD (c);

      if (! HASH_TABLE_P (read_objects_map)
	  || XHASH_TABLE (read_objects_map)->count)
	read_objects_map
	  = make_hash_table (&hashtest_eq, DEFAULT_HASH_SIZE, Weak_None, false);
      if (! HASH_TABLE_P (read_objects_completed)
	  || XHASH_TABLE (read_objects_completed)->count)
	read_objects_completed
	  = make_hash_table (&hashtest_eq, DEFAULT_HASH_SIZE, Weak_None, false);
      if (!NILP (Vpurify_flag) && c == '(')
	val = read0 (readcharfun, false);
      else
	{
	  if (!NILP (readfun))
	    {
	      val = call1 (readfun, readcharfun);

	      /* If READCHARFUN has set point to ZV, we should
	         stop reading, even if the form read sets point
		 to a different value when evaluated.  */
	      if (BUFFERP (readcharfun))
		{
		  struct buffer *buf = XBUFFER (readcharfun);
		  if (BUF_PT (buf) == BUF_ZV (buf))
		    continue_reading_p = 0;
		}
	    }
	  else if (! NILP (Vload_read_function))
	    val = call1 (Vload_read_function, readcharfun);
	  else
            {
	      val = read_internal_start (readcharfun, Qnil, Qnil, false);
            }
	}
      /* Empty hashes can be reused; otherwise, reset on next call.  */
      if (HASH_TABLE_P (read_objects_map)
	  && XHASH_TABLE (read_objects_map)->count > 0)
	read_objects_map = Qnil;
      if (HASH_TABLE_P (read_objects_completed)
	  && XHASH_TABLE (read_objects_completed)->count > 0)
	read_objects_completed = Qnil;

      if (!NILP (start) && continue_reading_p)
	start = Fpoint_marker ();

      /* Restore saved point and BEGV.  */
      dynwind_end ();

      val = eval_sub (val);

      if (printflag)
	{
	  Vvalues = Fcons (val, Vvalues);
	  if (EQ (Vstandard_output, Qt))
	    Fprin1 (val, Qnil, Qnil);
	  else
	    Fprint (val, Qnil);
	}
    }


  dynwind_end ();
}

/* File-specific version of readevalloop, used by LOAD (from file) only.

   ARCHITECTURAL SPLIT:
   - readevalloop(): General reading from any source (strings, buffers, functions)
   - readevalloop_load(): File-specific reading, isolated for future SCM port migration

   This function uses fread_internal_start() which provides the isolation point
   for Phase 2 migration to SCM ports.
 */
/* UNIBYTE handling removed - GuilEmacs uses pure UTF-8 strings only.
   READFUN, if non-nil, is used instead of `read'.

   START, END specify region to read in current buffer (from eval-region).
   If the input is not from a buffer, they must be nil.  */

/* File reading function for isolated file loading */
static int
freadchar (struct reader_context *ctx)
{
  register int c;

  /* File reading only - no buffer/string/function complexity */
  eassert (ctx);
  /* Check lookahead buffer first */
  if (ctx->lookahead)
    c = ctx->buf[--ctx->lookahead];
  else
    {
      /* Read from SCM port */
      eassert (!scm_is_false (ctx->port));
      int ch = scm_getc (ctx->port);
      c = (ch == EOF ? -1 : ch);
    }

  if (c < 0)
    return c;

  /* SCM port returns complete UTF-8 codepoints */
  return c;
}

/* Simplified file unread - no readcharfun parameter needed */
void
funreadchar (struct reader_context *ctx, int c)
{
  /* For file reading, use ctx->lookahead buffer directly */
  if (c != -1)
    {
      eassert (ctx && ctx->lookahead < sizeof ctx->buf);
      ctx->buf[ctx->lookahead++] = c;
    }
}

/* SCM port version of lexical cookie detection - currently unused */
#if 0
static lexical_cookie_t
lisp_file_lexical_cookie_scm_port (struct reader_context *ctx)
{
  eassert (ctx && !scm_is_false (ctx->port));

  int ch = freadchar(ctx);

  if (ch == EOF) return Cookie_None;

  if (ch == '#')
    {
      ch = freadchar(ctx);
      if (ch != '!')
        {
          funreadchar (ctx, ch);
          funreadchar (ctx, '#');
          return Cookie_None;
        }
      while (ch != '\n' && ch != EOF)
        ch = freadchar (ctx);
      if (ch == '\n') ch = freadchar (ctx);
      /* It is OK to leave the position after a #! line, since
	 that is what read0 does.  */
    }

  if (ch != ';')
    /* The first line isn't a comment, just give up.  */
    {
      funreadchar (ctx, ch);
      return Cookie_None;
    }
  else
    /* Look for an appropriate file-variable in the first line.  */
    {
      lexical_cookie_t rv = Cookie_None;
      enum {
	NOMINAL, AFTER_FIRST_DASH, AFTER_ASTERIX
      } beg_end_state = NOMINAL;
      bool in_file_vars = 0;

#define UPDATE_BEG_END_STATE2(ch)
  if (beg_end_state == NOMINAL)
    beg_end_state = (ch == '-' ? AFTER_FIRST_DASH : NOMINAL);
  else if (beg_end_state == AFTER_FIRST_DASH)
    beg_end_state = (ch == '*' ? AFTER_ASTERIX : NOMINAL);
  else if (beg_end_state == AFTER_ASTERIX)
    beg_end_state = (ch == '-' ? AFTER_FIRST_DASH : NOMINAL);

      while (ch != '\n' && ch != EOF)
	{
	  UPDATE_BEG_END_STATE2 (ch);
	  if (in_file_vars)
	    {
	      if (c_isspace (ch))
		ch = freadchar (ctx);
	      else if (ch == 'l')
		{
		  if (freadchar (ctx) == 'e'
		      && freadchar (ctx) == 'x'
		      && freadchar (ctx) == 'i'
		      && freadchar (ctx) == 'c'
		      && freadchar (ctx) == 'a'
		      && freadchar (ctx) == 'l'
		      && freadchar (ctx) == '-'
		      && freadchar (ctx) == 'b'
		      && freadchar (ctx) == 'i'
		      && freadchar (ctx) == 'n'
		      && freadchar (ctx) == 'd'
		      && freadchar (ctx) == 'i'
		      && freadchar (ctx) == 'n'
		      && freadchar (ctx) == 'g')
		    {
		      ch = freadchar (ctx);
		      if (c_isspace (ch))
			{
			  while (c_isspace (ch))
			    ch = freadchar (ctx);
			  if (ch == ':')
			    {
			      while (c_isspace (ch = freadchar (ctx)))
				;
			      if (ch == 't' || ch == 'T')
				rv = Cookie_Lex;
			    }
			}
		    }
		  ch = freadchar (ctx);
		}
	      else
		ch = freadchar (ctx);
	    }
	  else if (ch == '-' && beg_end_state == AFTER_ASTERIX)
	    in_file_vars = 1;
	  else
	    ch = freadchar (ctx);
	}
#undef UPDATE_BEG_END_STATE2
      return rv;
    }
}
#endif /* 0 - lisp_file_lexical_cookie_scm_port unused */

static Lisp_Object
fread_internal_start (SCM port)
{
  int c = scm_getc (port);

  SCM fread0_with_char_func = scm_c_private_ref ("emacs-elisp runtime",
                                                 "elisp-fread0-with-char-from-c");
  return scm_call_2 (fread0_with_char_func, scm_from_int (c), port);
}

static void
readevalloop_load (SCM port, Lisp_Object sourcename)
{
  /* MINIMIZED: Following fread_internal_start pattern - minimal C wrapper */

  SCM readevalloop_load_func = scm_c_private_ref ("emacs-elisp runtime",
                                                  "elisp-readevalloop-load-from-port");
  scm_call_2 (readevalloop_load_func, port, sourcename);
}

DEFUN ("eval-buffer", Feval_buffer, Seval_buffer, 0, 5, "",
       doc: /* Execute the accessible portion of current buffer as Lisp code.
You can use \\[narrow-to-region] to limit the part of buffer to be evaluated.
When called from a Lisp program (i.e., not interactively), this
function accepts up to five optional arguments:
BUFFER is the buffer to evaluate (nil means use current buffer),
 or a name of a buffer (a string).
PRINTFLAG controls printing of output by any output functions in the
 evaluated code, such as `print', `princ', and `prin1':
  a value of nil means discard it; anything else is the stream to print to.
  See Info node `(elisp)Output Streams' for details on streams.
FILENAME specifies the file name to use for `load-history'.
UNIBYTE is obsolete and ignored (GuilEmacs uses UTF-8 for all strings).
DO-ALLOW-PRINT, if non-nil, specifies that output functions in the
 evaluated code should work normally even if PRINTFLAG is nil, in
 which case the output is displayed in the echo area.

This function ignores the current value of the `lexical-binding'
variable.  Instead it will heed any
  -*- lexical-binding: t -*-
settings in the buffer, and if there is no such setting, the buffer
will be evaluated without lexical binding.

This function preserves the position of point.  */)
  (Lisp_Object buffer, Lisp_Object printflag, Lisp_Object filename,
   Lisp_Object unibyte, Lisp_Object do_allow_print)
{
  dynwind_begin ();
  Lisp_Object tem, buf;

  if (NILP (buffer))
    buf = Fcurrent_buffer ();
  else
    buf = Fget_buffer (buffer);
  if (NILP (buf))
    error ("No such buffer");

  if (NILP (printflag) && NILP (do_allow_print))
    tem = Qsymbolp;
  else
    tem = printflag;

  if (NILP (filename))
    filename = BVAR (XBUFFER (buf), filename);

  specbind (Qeval_buffer_list, Fcons (buf, Veval_buffer_list));
  specbind (Qstandard_output, tem);
  record_unwind_protect_excursion ();
  BUF_TEMP_SET_PT (XBUFFER (buf), BUF_BEGV (XBUFFER (buf)));
  specbind (Qlexical_binding,
	    lisp_file_lexical_cookie (buf) == Cookie_Lex ? Qt : Qnil);
  BUF_TEMP_SET_PT (XBUFFER (buf), BUF_BEGV (XBUFFER (buf)));
  readevalloop (buf, filename,
		!NILP (printflag), unibyte, Qnil, Qnil, Qnil);
  dynwind_end ();

  return Qnil;
}

DEFUN ("eval-region", Feval_region, Seval_region, 2, 4, "r",
       doc: /* Execute the region as Lisp code.
When called from programs, expects two arguments,
giving starting and ending indices in the current buffer
of the text to be executed.
Programs can pass third argument PRINTFLAG which controls output:
 a value of nil means discard it; anything else is stream for printing it.
 See Info node `(elisp)Output Streams' for details on streams.
Also the fourth argument READ-FUNCTION, if non-nil, is used
instead of `read' to read each expression.  It gets one argument
which is the input stream for reading characters.

This function does not move point.  */)
  (Lisp_Object start, Lisp_Object end, Lisp_Object printflag, Lisp_Object read_function)
{
  /* FIXME: Do the eval-sexp-add-defvars dance!  */
  dynwind_begin ();
  Lisp_Object tem, cbuf;

  cbuf = Fcurrent_buffer ();

  if (NILP (printflag))
    tem = Qsymbolp;
  else
    tem = printflag;
  specbind (Qstandard_output, tem);
  specbind (Qeval_buffer_list, Fcons (cbuf, Veval_buffer_list));

  /* `readevalloop' calls functions which check the type of start and end.  */
  readevalloop (cbuf, BVAR (XBUFFER (cbuf), filename),
		!NILP (printflag), Qnil, read_function,
		start, end);

  dynwind_end ();
  return Qnil;
}


DEFUN ("read", Fread, Sread, 0, 1, 0,
       doc: /* Read one Lisp expression as text from STREAM, return as Lisp object.
If STREAM is nil, use the value of `standard-input' (which see).
STREAM or the value of `standard-input' may be:
 a buffer (read from point and advance it)
 a marker (read from where it points and advance it)
 a function (call it with no arguments for each character,
     call it with a char as argument to push a char back)
 a string (takes text from string, starting at the beginning)
 t (read text line using minibuffer and use it, or read from
    standard input in batch mode).  */)
  (Lisp_Object stream)
{
  if (NILP (stream))
    stream = Vstandard_input;
  if (EQ (stream, Qt))
    stream = Qread_char;
  if (EQ (stream, Qread_char))
    /* FIXME: ?! This is used when the reader is called from the
       minibuffer without a stream, as in (read).  But is this feature
       ever used, and if so, why?  IOW, will anything break if this
       feature is removed !?  */
    return call1 (Qread_minibuffer,
		  build_string ("Lisp expression: "));

  return read_internal_start (stream, Qnil, Qnil, false);
}

DEFUN ("read-positioning-symbols", Fread_positioning_symbols,
       Sread_positioning_symbols, 0, 1, 0,
       doc: /* Read one Lisp expression as text from STREAM, return as Lisp object.
Convert each occurrence of a symbol into a "symbol with pos" object.

If STREAM is nil, use the value of `standard-input' (which see).
STREAM or the value of `standard-input' may be:
 a buffer (read from point and advance it)
 a marker (read from where it points and advance it)
 a function (call it with no arguments for each character,
     call it with a char as argument to push a char back)
 a string (takes text from string, starting at the beginning)
 t (read text line using minibuffer and use it, or read from
    standard input in batch mode).  */)
  (Lisp_Object stream)
{
  if (NILP (stream))
    stream = Vstandard_input;
  if (EQ (stream, Qt))
    stream = Qread_char;
  if (EQ (stream, Qread_char))
    /* FIXME: ?! When is this used !?  */
    return call1 (Qread_minibuffer,
		  build_string ("Lisp expression: "));

  return read_internal_start (stream, Qnil, Qnil, true);
}

DEFUN ("read-from-string", Fread_from_string, Sread_from_string, 1, 3, 0,
       doc: /* Read one Lisp expression which is represented as text by STRING.
Returns a cons: (OBJECT-READ . FINAL-STRING-INDEX).
FINAL-STRING-INDEX is an integer giving the position of the next
remaining character in STRING.  START and END optionally delimit
a substring of STRING from which to read;  they default to 0 and
\(length STRING) respectively.  Negative values are counted from
the end of STRING.  */)
  (Lisp_Object string, Lisp_Object start, Lisp_Object end)
{
  Lisp_Object ret;
  CHECK_STRING (string);
  /* `read_internal_start' sets `read_from_string_index'.  */
  ret = read_internal_start (string, start, end, false);
  return Fcons (ret, make_fixnum (read_from_string_index));
}

/* File-specific error handling functions */
static AVOID
finvalid_syntax (const char *s)
{
  invalid_syntax (s, Qget_file_char);
}

static AVOID
finvalid_radix_integer (EMACS_INT radix)
{
  char buf[64];
  int n = snprintf (buf, sizeof buf, "integer, radix %"pI"d", radix);
  eassert (n < sizeof buf);
  finvalid_syntax (buf);
}

/* Conservative fread0 helper - moves EOF checking to Scheme */
static Lisp_Object
elisp_parse_with_eof_check_from_c_context (SCM port, int c)
{
  SCM eof_check_func = scm_c_private_ref ("emacs-elisp runtime",
                                          "elisp-parse-with-eof-check");
  SCM result = scm_call_2 (eof_check_func, scm_from_int (c), port);

  return result;
}

/* Load-specific helper functions for readevalloop_load migration */

static void
elisp_skip_load_whitespace_from_c_context (struct reader_context *ctx)
{
  SCM skip_ws_func = scm_c_private_ref ("emacs reader",
                                        "elisp-skip-load-whitespace-from-port");
  sync_guile_reader (ctx);
  scm_call_1 (skip_ws_func, ctx->port);
  ctx->lookahead = 0;
}

static void
elisp_skip_load_comment_from_c_context (struct reader_context *ctx)
{
  SCM skip_comment_func = scm_c_private_ref ("emacs-elisp runtime",
                                             "elisp-skip-load-comment-from-port");
  sync_guile_reader (ctx);
  scm_call_1 (skip_comment_func, ctx->port);
  ctx->lookahead = 0;
}

static Lisp_Object
elisp_read_with_load_function_from_c_context (struct reader_context *ctx)
{
  SCM load_read_func = scm_c_private_ref ("emacs-elisp runtime",
                                          "elisp-read-with-load-function-from-port");
  sync_guile_reader (ctx);
  SCM result = scm_call_1 (load_read_func, ctx->port);
  ctx->lookahead = 0;
  return result;
}

static Lisp_Object
elisp_load_read_next_expression_from_c_context (struct reader_context *ctx)
{
  SCM read_next_func = scm_c_private_ref ("emacs-elisp runtime",
                                          "elisp-load-read-next-expression-from-port");
  sync_guile_reader (ctx);
  SCM result = scm_call_1 (read_next_func, ctx->port);
  ctx->lookahead = 0;

  /* Check if we got EOF - return NULL to indicate EOF to the caller */
  if (scm_is_eq (result, scm_from_latin1_symbol ("eof")))
    return NULL; /* NULL indicates EOF - let caller handle appropriately */

  return result;
}

static void
elisp_load_read_eval_loop_from_c_context (struct reader_context *ctx, bool printflag)
{
  SCM loop_func = scm_c_private_ref ("emacs-elisp runtime",
                                     "elisp-load-read-eval-loop-from-port");
  sync_guile_reader (ctx);
  scm_call_2 (loop_func, ctx->port, printflag ? SCM_BOOL_T : SCM_BOOL_F);
  ctx->lookahead = 0;
}

static Lisp_Object
elisp_normalize_load_path_from_c_context (Lisp_Object sourcename)
{
  SCM normalize_func = scm_c_private_ref ("emacs-elisp runtime",
                                          "elisp-normalize-load-path");
  return scm_call_1 (normalize_func, sourcename);
}

DEFUN ("elisp-loadhist-initialize", Felisp_loadhist_initialize,
       Selisp_loadhist_initialize, 1, 1, 0,
       doc: /* Initialize load history for SOURCENAME.
This wraps the C loadhist_initialize function for Scheme access. */)
  (Lisp_Object sourcename)
{
  loadhist_initialize (sourcename);
  return Qt;
}

Lisp_Object
elisp_read_from_port (Lisp_Object port)
{
  return fread0 (port);
}

/* Enhanced Guile Reader with Error Handling */
static SCM
guile_reader_error_handler (void *data, SCM key, SCM args)
{
  Lisp_Object readcharfun = (Lisp_Object) data;

  /* Convert Guile exception to Emacs error */
  if (scm_is_eq (key, scm_from_latin1_symbol ("read-error")))
    {
      /* Extract error message from Guile exception
         The args list contains: (port message-template format-args extra-data)
         We just use object->string on the whole args to avoid format interpretation issues */
      SCM msg = scm_call_1 (scm_c_public_ref ("guile", "object->string"), args);
      char *error_msg = scm_to_utf8_string (msg);

      /* Signal Emacs error with Guile's error message */
      signal_error ("Guile reader error", build_string (error_msg));
      free (error_msg);
    }
  else if (scm_is_eq (key, scm_from_latin1_symbol ("end-of-file")))
    {
      end_of_file_error ();
    }
  else
    {
      /* Generic Guile exception */
      char *key_str = scm_to_utf8_string (scm_symbol_to_string (key));
      signal_error ("Guile exception in reader", build_string (key_str));
      free (key_str);
    }

  return SCM_UNSPECIFIED;
}

/* Function to set up the global context we need in toplevel read
   calls.  START and END only used when STREAM is a string.
   LOCATE_SYMS true means read symbol occurrences as symbols with
   position.  */
static Lisp_Object
read_internal_start (Lisp_Object stream, Lisp_Object start, Lisp_Object end,
                     bool locate_syms)
{
  Lisp_Object retval;

  /* We can get called from readevalloop which may have set these
     already.  */
  if (! HASH_TABLE_P (read_objects_map)
      || XHASH_TABLE (read_objects_map)->count)
    read_objects_map
      = make_hash_table (&hashtest_eq, DEFAULT_HASH_SIZE, Weak_None, false);
  if (! HASH_TABLE_P (read_objects_completed)
      || XHASH_TABLE (read_objects_completed)->count)
    read_objects_completed
      = make_hash_table (&hashtest_eq, DEFAULT_HASH_SIZE, Weak_None, false);

  if (STRINGP (stream)
      || ((CONSP (stream) && STRINGP (XCAR (stream)))))
    {
      ptrdiff_t startval, endval;
      Lisp_Object string;

      if (STRINGP (stream))
	string = stream;
      else
	string = XCAR (stream);

      validate_subarray (string, start, end, SCHARS (string),
			 &startval, &endval);

      read_from_string_index = startval;
      read_from_string_limit = endval;
    }

  retval = read0 (stream, locate_syms);
  if (HASH_TABLE_P (read_objects_map)
      && XHASH_TABLE (read_objects_map)->count > 0)
    read_objects_map = Qnil;
  if (HASH_TABLE_P (read_objects_completed)
      && XHASH_TABLE (read_objects_completed)->count > 0)
    read_objects_completed = Qnil;
  return retval;
}

/* Grow a read buffer BUF that contains OFFSET useful bytes of data,
   by at least MAX_MULTIBYTE_LENGTH bytes.  Update *BUF_ADDR and
   *BUF_SIZE accordingly; 0 <= OFFSET <= *BUF_SIZE.  If *BUF_ADDR is
   initially null, BUF is on the stack: copy its data to the new heap
   buffer.  Otherwise, BUF must equal *BUF_ADDR and can simply be
   reallocated.  Either way, remember the heap allocation (which is at
   pdl slot COUNT) so that it can be freed when unwinding the stack.*/

static char *
grow_read_buffer (char *buf, ptrdiff_t offset,
		  char **buf_addr, ptrdiff_t *buf_size)
{
  char *p = xpalloc (*buf_addr, buf_size, MAX_MULTIBYTE_LENGTH, -1, 1);
  if (!*buf_addr)
    {
      memcpy (p, buf, offset);
    }
  *buf_addr = p;
  return p;
}

/* Return the scalar value that has the Unicode character name NAME.
   Raise 'invalid-read-syntax' if there is no such character.  */
static int
character_name_to_code (char const *name, ptrdiff_t name_len,
			Lisp_Object readcharfun)
{
  /* For "U+XXXX", pass the leading '+' to string_to_number to reject
     monstrosities like "U+-0000".  */
  ptrdiff_t len = name_len - 1;
  Lisp_Object code
    = (name[0] == 'U' && name[1] == '+'
       ? string_to_number (name + 1, 16, &len)
       : call2 (Qchar_from_name, scm_from_utf8_stringn (name, name_len), Qt));

  if (! RANGED_FIXNUMP (0, code, MAX_UNICODE_CHAR)
      || len != name_len - 1
      || char_surrogate_p (XFIXNUM (code)))
    {
      AUTO_STRING (format, "\\N{%s}");
      AUTO_STRING_WITH_LEN (namestr, name, name_len);
      invalid_syntax_lisp (CALLN (Fformat, format, namestr), readcharfun);
    }

  return XFIXNUM (code);
}

/* Bound on the length of a Unicode character name.  As of
   Unicode 9.0.0 the maximum is 83, so this should be safe.  */
enum { UNICODE_CHARACTER_NAME_LENGTH_BOUND = 200 };

/* Read a character escape sequence, assuming we just read a backslash
   and one more character (next_char).  */
static int
read_char_escape (Lisp_Object readcharfun, int next_char)
{
  int modifiers = 0;
  ptrdiff_t ncontrol = 0;
  int chr;

 again: ;
  int c = next_char;
  int unicode_hex_count;
  int mod;

  switch (c)
    {
    case -1:
      end_of_file_error ();

    case 'a': chr = '\a'; break; // audible bell
    case 'b': chr = '\b'; break; // backspace
    case 'd': chr =  127; break; // delete
    case 'e': chr =   27; break; // escape
    case 'f': chr = '\f'; break; // form feed
    case 'n': chr = '\n'; break; // newline
    case 'r': chr = '\r'; break; // carriage return
    case 't': chr = '\t'; break; // horizontal tab
    case 'v': chr = '\v'; break; // vertical tab

    case '\n':
      /* ?\LF is an error; it's probably a user mistake.  */
      error ("Invalid escape char syntax: \\<newline>");

    /* \M-x etc: set modifier bit and parse the char to which it applies,
       allowing for chains such as \M-\S-\A-\H-\s-\C-q.  */
    case 'M': mod = meta_modifier;  goto mod_key;
    case 'S': mod = shift_modifier; goto mod_key;
    case 'H': mod = hyper_modifier; goto mod_key;
    case 'A': mod = alt_modifier;   goto mod_key;
    case 's': mod = super_modifier; goto mod_key;

    mod_key:
      {
	int c1 = READCHAR;
	if (c1 != '-')
	  {
	    if (c == 's')
	      {
		/* \s not followed by a hyphen is SPC.  */
		UNREAD (c1);
		chr = ' ';
		break;
	      }
	    else
	      /* \M, \S, \H, \A not followed by a hyphen is an error.  */
	      error ("Invalid escape char syntax: \\%c not followed by -", c);
	  }
	modifiers |= mod;
	c1 = READCHAR;
	if (c1 == '\\')
	  {
	    next_char = READCHAR;
	    goto again;
	  }
	chr = c1;
	break;
      }

    /* Control modifiers (\C-x or \^x) are messy and not actually idempotent.
       For example, ?\C-\C-a = ?\C-\001 = 0x4000001.
       Keep a count of them and apply them separately.  */
    case 'C':
      {
	int c1 = READCHAR;
	if (c1 != '-')
	  error ("Invalid escape char syntax: \\%c not followed by -", c);
      }
      FALLTHROUGH;
    /* The prefixes \C- and \^ are equivalent.  */
    case '^':
      {
	ncontrol++;
	int c1 = READCHAR;
	if (c1 == '\\')
	  {
	    next_char = READCHAR;
	    goto again;
	  }
	chr = c1;
	break;
      }

    /* 1-3 octal digits.  Values in 0x80..0xff are encoded as raw bytes.  */
    case '0': case '1': case '2': case '3':
    case '4': case '5': case '6': case '7':
      {
	int i = c - '0';
	int count = 0;
	while (count < 2)
	  {
	    int c = READCHAR;
	    if (c < '0' || c > '7')
	      {
		UNREAD (c);
		break;
	      }
	    i = (i << 3) + (c - '0');
	    count++;
	  }

	if (i >= 0x80 && i < 0x100)
	  i = BYTE8_TO_CHAR (i);
	chr = i;
	break;
      }

    /* 1 or more hex digits.  Values may encode modifiers.
       Values in 0x80..0xff using 2 hex digits are encoded as raw bytes.  */
    case 'x':
      {
	unsigned int i = 0;
	int count = 0;
	while (1)
	  {
	    int c = READCHAR;
	    int digit = char_hexdigit (c);
	    if (digit < 0)
	      {
		UNREAD (c);
		break;
	      }
	    i = (i << 4) + digit;
	    /* Allow hex escapes as large as ?\xfffffff, because some
	       packages use them to denote characters with modifiers.  */
	    if (i > (CHAR_META | (CHAR_META - 1)))
	      error ("Hex character out of range: \\x%x...", i);
	    count += count < 3;
	  }

	if (count == 0)
	  error ("Invalid escape char syntax: \\x not followed by hex digit");
	if (count < 3 && i >= 0x80)
	  i = BYTE8_TO_CHAR (i);
	modifiers |= i & CHAR_MODIFIER_MASK;
	chr = i & ~CHAR_MODIFIER_MASK;
	break;
      }

    /* 8-digit Unicode hex escape: \UHHHHHHHH */
    case 'U':
      unicode_hex_count = 8;
      goto unicode_hex;

    /* 4-digit Unicode hex escape: \uHHHH */
    case 'u':
      unicode_hex_count = 4;
    unicode_hex:
      {
	unsigned int i = 0;
	for (int count = 0; count < unicode_hex_count; count++)
	  {
	    int c = READCHAR;
	    if (c < 0)
	      error ("Malformed Unicode escape: \\%c%x",
		     unicode_hex_count == 4 ? 'u' : 'U', i);
	    int digit = char_hexdigit (c);
	    if (digit < 0)
	      error ("Non-hex character used for Unicode escape: %c (%d)",
		     c, c);
	    i = (i << 4) + digit;
	  }
	if (i > 0x10FFFF)
	  error ("Non-Unicode character: 0x%x", i);
	chr = i;
	break;
      }

    /* Named character: \N{name} */
    case 'N':
      {
        int c = READCHAR;
        if (c != '{')
          invalid_syntax ("Expected opening brace after \\N", readcharfun);
        char name[UNICODE_CHARACTER_NAME_LENGTH_BOUND + 1];
        bool whitespace = false;
        ptrdiff_t length = 0;
        while (true)
          {
            int c = READCHAR;
            if (c < 0)
              end_of_file_error ();
            if (c == '}')
              break;
            if (c >= 0x80)
              {
                AUTO_STRING (format,
                             "Invalid character U+%04X in character name");
		invalid_syntax_lisp (CALLN (Fformat, format,
					    make_fixed_natnum (c)),
				     readcharfun);
              }
            /* Treat multiple adjacent whitespace characters as a
               single space character.  This makes it easier to use
               character names in e.g. multi-line strings.  */
            if (c_isspace (c))
              {
                if (whitespace)
                  continue;
                c = ' ';
                whitespace = true;
              }
            else
              whitespace = false;
            name[length++] = c;
            if (length >= sizeof name)
              invalid_syntax ("Character name too long", readcharfun);
          }
        if (length == 0)
          invalid_syntax ("Empty character name", readcharfun);
	name[length] = '\0';

	/* character_name_to_code can invoke read0, recursively.
	   This is why read0 needs to be re-entrant.  */
	chr = character_name_to_code (name, length, readcharfun);
	break;
      }

    default:
      chr = c;
      break;
    }
  eassert (chr >= 0 && chr < (1 << CHARACTERBITS));

  /* Apply Control modifiers, using the rules:
     \C-X = ascii_ctrl(nomod(X)) | mods(X)  if nomod(X) is one of:
                                                A-Z a-z ? @ [ \ ] ^ _

            X | ctrl_modifier               otherwise

     where
         nomod(c) = c without modifiers
	 mods(c)  = the modifiers of c
         ascii_ctrl(c) = 127       if c = '?'
                         c & 0x1f  otherwise
  */
  while (ncontrol > 0)
    {
      if ((chr >= '@' && chr <= '_') || (chr >= 'a' && chr <= 'z'))
	chr &= 0x1f;
      else if (chr == '?')
	chr = 127;
      else
	modifiers |= ctrl_modifier;
      ncontrol--;
    }

  return chr | modifiers;
}

/* File-specific version of character_name_to_code - uses file error handling */
static int
fcharacter_name_to_code (char const *name, ptrdiff_t name_len)
{
  /* For "U+XXXX", pass the leading '+' to string_to_number to reject
     monstrosities like "U+-0000".  */
  ptrdiff_t len = name_len - 1;
  Lisp_Object code
    = (name[0] == 'U' && name[1] == '+'
       ? string_to_number (name + 1, 16, &len)
       : call2 (Qchar_from_name, scm_from_utf8_stringn (name, name_len), Qt));

  if (! RANGED_FIXNUMP (0, code, MAX_UNICODE_CHAR)
      || len != name_len - 1
      || char_surrogate_p (XFIXNUM (code)))
    {
      AUTO_STRING (format, "\\N{%s}");
      AUTO_STRING_WITH_LEN (namestr, name, name_len);
      finvalid_syntax (SSDATA (CALLN (Fformat, format, namestr)));
    }

  return XFIXNUM (code);
}

static void
invalid_radix_integer (EMACS_INT radix, Lisp_Object readcharfun)
{
  char buf[64];
  int n = snprintf (buf, sizeof buf, "integer, radix %"pI"d", radix);
  eassert (n < sizeof buf);
  invalid_syntax (buf, readcharfun);
}

/* Read an integer in radix RADIX using READCHARFUN to read
   characters.  RADIX must be in the interval [2..36].
   Value is the integer read.
   Signal an error if encountering invalid read syntax.  */

static Lisp_Object
read_integer (Lisp_Object readcharfun, int radix)
{
  /* Phase 8D: Use our enhanced Guile integer parsing functions */

  char stackbuf[64];
  char *read_buffer = stackbuf;
  ptrdiff_t read_buffer_size = sizeof stackbuf;
  char *p = read_buffer;
  char *heapbuf = NULL;
  int valid = -1; /* 1 if valid, 0 if not, -1 if incomplete.  */

  dynwind_begin();

  /* Add radix prefix for better Guile compatibility */
  if (radix == 16)
    {
      *p++ = '#';
      *p++ = 'x';
    }
  else if (radix == 8)
    {
      *p++ = '#';
      *p++ = 'o';
    }
  else if (radix == 2)
    {
      *p++ = '#';
      *p++ = 'b';
    }

  int c = READCHAR;
  if (c == '-' || c == '+')
    {
      *p++ = c;
      c = READCHAR;
    }

  if (c == '0')
    {
      *p++ = c;
      valid = 1;

      /* Ignore redundant leading zeros, so the buffer doesn't
	 fill up with them.  */
      do
	c = READCHAR;
      while (c == '0');
    }

  for (int digit; (digit = digit_to_number (c, radix)) >= -1; )
    {
      if (digit == -1)
	valid = 0;
      if (valid < 0)
	valid = 1;
      /* Allow 1 extra byte for the \0.  */
      if (p + 1 == read_buffer + read_buffer_size)
	{
	  ptrdiff_t offset = p - read_buffer;
	  read_buffer = grow_read_buffer (read_buffer, offset,
					  &heapbuf, &read_buffer_size);
	  p = read_buffer + offset;
	}
      *p++ = c;
      c = READCHAR;
    }

  UNREAD (c);

  if (valid != 1)
    invalid_radix_integer (radix, readcharfun);

  *p = '\0';

  /* Try Guile integer parsing first for enhanced functionality */
  Lisp_Object str = build_string (read_buffer);
  Lisp_Object guile_result = guile_parse_integer_string (str, radix);
  if (!NILP (guile_result))
    {
      dynwind_end();
      return guile_result;
    }

  /* Fallback to traditional parsing if Guile is not available */
  Lisp_Object tem = string_to_number (read_buffer, radix, NULL);
  dynwind_end();
  return tem;
}


/* Read a character literal (preceded by `?').  */
static Lisp_Object
read_char_literal (Lisp_Object readcharfun)
{
  int ch = READCHAR;
  if (ch < 0)
    end_of_file_error ();

  /* Accept `single space' syntax like (list ? x) where the
     whitespace character is SPC or TAB.
     Other literal whitespace like NL, CR, and FF are not accepted,
     as there are well-established escape sequences for these.  */
  if (ch == ' ' || ch == '\t')
    return make_fixnum (ch);

  if (ch == '\\')
    ch = read_char_escape (readcharfun, READCHAR);

  int modifiers = ch & CHAR_MODIFIER_MASK;
  ch &= ~CHAR_MODIFIER_MASK;
  if (CHAR_BYTE8_P (ch))
    ch = CHAR_TO_BYTE8 (ch);
  ch |= modifiers;

  int nch = READCHAR;
  UNREAD (nch);
  if (nch <= 32
      || nch == '"' || nch == '\'' || nch == ';' || nch == '('
      || nch == ')' || nch == '['  || nch == ']' || nch == '#'
      || nch == '?' || nch == '`'  || nch == ',' || nch == '.')
    return make_fixnum (ch);

  invalid_syntax ("?", readcharfun);
}

/* Read a string literal (preceded by '"'). */
static Lisp_Object
read_string_literal (Lisp_Object readcharfun)
{
  /* Build the string by processing escape sequences in C */
  char stackbuf[1024];
  char *read_buffer = stackbuf;
  ptrdiff_t read_buffer_size = sizeof stackbuf;
  char *heapbuf = NULL;
  char *p = read_buffer;
  char *end = read_buffer + read_buffer_size;

  dynwind_begin ();

  int ch;
  while ((ch = READCHAR) >= 0 && ch != '"')
    {
      if (end - p < MAX_MULTIBYTE_LENGTH + 1)
	{
	  ptrdiff_t offset = p - read_buffer;
	  read_buffer = grow_read_buffer (read_buffer, offset,
					  &heapbuf, &read_buffer_size);
	  p = read_buffer + offset;
	  end = read_buffer + read_buffer_size;
	}

      /* Handle escape sequences */
      if (ch == '\\')
	{
	  ch = READCHAR;
	  if (ch < 0)
	    end_of_file_error ();

	  /* Handle string continuation: backslash-newline is ignored */
	  if (ch == '\n')
	    continue;

	  /* Process Elisp escape sequences */
	  ch = read_char_escape (readcharfun, ch);
	}

      /* Store the character (handle modifiers if present) */
      int modifiers = ch & CHAR_MODIFIER_MASK;
      ch &= ~CHAR_MODIFIER_MASK;

      /* For strings, meta modifier sets bit 7, not bit 27 */
      if (modifiers & CHAR_META)
	ch |= 0x80;

      if (CHAR_BYTE8_P (ch))
	*p++ = CHAR_TO_BYTE8 (ch);
      else if (ch < 128)
	*p++ = ch;
      else
	p += CHAR_STRING (ch, (unsigned char *) p);
    }

  if (ch < 0)
    end_of_file_error ();

  /* Create a Guile string from the processed buffer */
  Lisp_Object result = scm_from_utf8_stringn (read_buffer, p - read_buffer);

  dynwind_end ();

  return result;
}

/* Make a hash table from the constructor plist.  */
static Lisp_Object
hash_table_from_plist (Lisp_Object plist)
{
  Lisp_Object params[4 * 2];
  Lisp_Object *par = params;

  /* This is repetitive but fast and simple.  */
#define ADDPARAM(name) \
  do { \
    Lisp_Object val = plist_get (plist, Q##name); \
    if (!NILP (val)) \
      { \
	*par++ = QC##name; \
	*par++ = val; \
      } \
  } while (0)

  ADDPARAM (test);
  ADDPARAM (weakness);
  ADDPARAM (purecopy);

  Lisp_Object data = plist_get (plist, Qdata);
  if (!(NILP (data) || CONSP (data)))
    error ("Hash table data is not a list");
  ptrdiff_t data_len = list_length (data);
  if (data_len & 1)
    error ("Hash table data length is odd");
  *par++ = QCsize;
  *par++ = make_fixnum (data_len / 2);

  /* Now use params to make a new hash table and fill it.  */
  Lisp_Object ht = Fmake_hash_table (par - params, params);

  while (!NILP (data))
    {
      Lisp_Object key = XCAR (data);
      data = XCDR (data);
      Lisp_Object val = XCAR (data);
      Fputhash (key, val, ht);
      data = XCDR (data);
    }

  return ht;
}

static Lisp_Object
record_from_list (Lisp_Object elems)
{
  ptrdiff_t size = list_length (elems);
  Lisp_Object obj = Fmake_record (XCAR (elems),
				  make_fixnum (size - 1),
				  Qnil);
  Lisp_Object tl = XCDR (elems);
  for (int i = 1; i < size; i++)
    {
      ASET (obj, i, XCAR (tl));
      tl = XCDR (tl);
    }
  return obj;
}

/* Turn a reversed list into a vector.  */
static Lisp_Object
vector_from_rev_list (Lisp_Object elems)
{
  ptrdiff_t size = list_length (elems);
  Lisp_Object obj = make_nil_elisp_vector (size);

  /* Populate the elisp vector with elements from the reversed list */
  for (ptrdiff_t i = size - 1; i >= 0; i--)
    {
      if (i < 0 || i >= size)
        break;

      if (!elems || !CONSP (elems))
        {
          /* List ended prematurely, remaining elements stay as nil */
          break;
        }

      Lisp_Object car_val = Qnil;
      Lisp_Object cdr_val = Qnil;
      if (scm_is_pair (elems))
        {
          car_val = scm_car (elems);
          cdr_val = scm_cdr (elems);
        }
      ASET (obj, i, car_val);
      elems = cdr_val;
    }
  return obj;
}



static Lisp_Object
char_table_from_rev_list (Lisp_Object elems, Lisp_Object readcharfun)
{
  Lisp_Object obj = vector_from_rev_list (elems);
  if (ASIZE (obj) < CHAR_TABLE_STANDARD_SLOTS)
    invalid_syntax ("Invalid size char-table", readcharfun);
  XSETPVECTYPE (XVECTOR (obj), PVEC_CHAR_TABLE);
  return obj;

}

static Lisp_Object
sub_char_table_from_rev_list (Lisp_Object elems, Lisp_Object readcharfun)
{
  /* A sub-char-table can't be read as a regular vector because of two
     C integer fields.  */
  elems = Fnreverse (elems);
  ptrdiff_t size = list_length (elems);
  if (size < 2)
    error ("Invalid size of sub-char-table");

  if (!RANGED_FIXNUMP (1, XCAR (elems), 3))
    error ("Invalid depth in sub-char-table");
  int depth = XFIXNUM (XCAR (elems));

  if (chartab_size[depth] != size - 2)
    error ("Invalid size in sub-char-table");
  elems = XCDR (elems);

  if (!RANGED_FIXNUMP (0, XCAR (elems), MAX_CHAR))
    error ("Invalid minimum character in sub-char-table");
  int min_char = XFIXNUM (XCAR (elems));
  elems = XCDR (elems);

  Lisp_Object tbl = make_uninit_sub_char_table (depth, min_char);
  for (int i = 0; i < size - 2; i++)
    {
      XSUB_CHAR_TABLE (tbl)->contents[i] = XCAR (elems);
      elems = XCDR (elems);
    }
  return tbl;
}

static Lisp_Object
string_props_from_rev_list (Lisp_Object elems, Lisp_Object readcharfun)
{
  elems = Fnreverse (elems);
  if (NILP (elems) || !STRINGP (XCAR (elems)))
    invalid_syntax ("#", readcharfun);
  Lisp_Object obj = XCAR (elems);
  for (Lisp_Object tl = XCDR (elems); !NILP (tl);)
    {
      Lisp_Object beg = XCAR (tl);
      tl = XCDR (tl);
      if (NILP (tl))
	invalid_syntax ("Invalid string property list", readcharfun);
      Lisp_Object end = XCAR (tl);
      tl = XCDR (tl);
      if (NILP (tl))
	invalid_syntax ("Invalid string property list", readcharfun);
      Lisp_Object plist = XCAR (tl);
      tl = XCDR (tl);
      Fset_text_properties (beg, end, plist, obj);
    }
  return obj;
}

/* Read a bool vector (preceded by "#&").  */
static Lisp_Object
read_bool_vector (Lisp_Object readcharfun)
{
  EMACS_INT length = 0;
  for (;;)
    {
      int c = READCHAR;
      if (c < '0' || c > '9')
	{
	  if (c != '"')
	    invalid_syntax ("#&", readcharfun);
	  break;
	}
      if (ckd_mul (&length, length, 10)
	  || ckd_add (&length, length, c - '0'))
	invalid_syntax ("#&", readcharfun);
    }
  if (BOOL_VECTOR_LENGTH_MAX < length)
    invalid_syntax ("#&", readcharfun);

  ptrdiff_t size_in_chars = bool_vector_bytes (length);
  Lisp_Object str = read_string_literal (readcharfun);
#if 0
  if (STRING_MULTIBYTE (str)
      || !(size_in_chars == SCHARS (str)
	   /* We used to print 1 char too many when the number of bits
	      was a multiple of 8.  Accept such input in case it came
	      from an old version.  */
	   || length == (SCHARS (str) - 1) * BOOL_VECTOR_BITS_PER_CHAR))
    invalid_syntax ("#&...", readcharfun);
#endif

  Lisp_Object obj = make_uninit_bool_vector (length);
  unsigned char *data = bool_vector_uchar_data (obj);
  memcpy (data, SDATA (str), size_in_chars);
  /* Clear the extraneous bits in the last byte.  */
  if (length != size_in_chars * BOOL_VECTOR_BITS_PER_CHAR)
    data[size_in_chars - 1] &= (1 << (length % BOOL_VECTOR_BITS_PER_CHAR)) - 1;
  return obj;
}

static void
skip_space_and_comments (Lisp_Object readcharfun)
{
  int c;
  do
    {
      c = READCHAR;
      if (c == ';')
	do
	  c = READCHAR;
	while (c >= 0 && c != '\n');
      if (c < 0)
	end_of_file_error ();
    }
  while (c <= 32 || c == NO_BREAK_SPACE);
  UNREAD (c);
}

/* When an object is read, the type of the top read stack entry indicates
   the syntactic context.  */
enum read_entry_type
{
				/* preceding syntactic context */
  RE_list_start,		/* "(" */

  RE_list,			/* "(" (+ OBJECT) */
  RE_list_dot,			/* "(" (+ OBJECT) "." */

  RE_vector,			/* "[" (* OBJECT) */
  RE_record,			/* "#s(" (* OBJECT) */
  RE_char_table,		/* "#^[" (* OBJECT) */
  RE_sub_char_table,		/* "#^^[" (* OBJECT) */
  RE_string_props,		/* "#(" (* OBJECT) */

  RE_special,			/* "'" | "#'" | "`" | "," | ",@" */

  RE_numbered,			/* "#" (+ DIGIT) "=" */
};

struct read_stack_entry
{
  enum read_entry_type type;
  union {
    /* RE_list, RE_list_dot */
    struct {
      Lisp_Object head;		/* first cons of list */
      Lisp_Object tail;		/* last cons of list */
    } list;

    /* RE_vector, RE_record, RE_char_table, RE_sub_char_table,
       RE_string_props */
    struct {
      Lisp_Object elems;	/* list of elements in reverse order */
      bool old_locate_syms;	/* old value of locate_syms */
    } vector;

    /* RE_special */
    struct {
      Lisp_Object symbol;	/* symbol from special syntax */
    } special;

    /* RE_numbered */
    struct {
      Lisp_Object number;	/* number as a fixnum */
      Lisp_Object placeholder;	/* placeholder object */
    } numbered;
  } u;
};

struct read_stack
{
  struct read_stack_entry *stack;  /* base of stack */
  ptrdiff_t size;		   /* allocated size in entries */
  ptrdiff_t sp;			   /* current number of entries */
};

static struct read_stack rdstack = {NULL, 0, 0};

void
mark_lread (void)
{
}

static inline struct read_stack_entry *
read_stack_top (void)
{
  eassume (rdstack.sp > 0);
  return &rdstack.stack[rdstack.sp - 1];
}

static inline struct read_stack_entry *
read_stack_pop (void)
{
  eassume (rdstack.sp > 0);
  return &rdstack.stack[--rdstack.sp];
}

static inline bool
read_stack_empty_p (ptrdiff_t base_sp)
{
  return rdstack.sp <= base_sp;
}

NO_INLINE static void
grow_read_stack (void)
{
  struct read_stack *rs = &rdstack;
  eassert (rs->sp == rs->size);
  rs->stack = xpalloc (rs->stack, &rs->size, 1, -1, sizeof *rs->stack);
  eassert (rs->sp < rs->size);
}

static inline void
read_stack_push (struct read_stack_entry e)
{
  if (rdstack.sp >= rdstack.size)
    grow_read_stack ();
  rdstack.stack[rdstack.sp++] = e;
}

static void
read_stack_reset (intmax_t sp)
{
  eassert (sp <= rdstack.sp);
  rdstack.sp = sp;
}

#define READ_AND_BUFFER(c) \
  c = READCHAR; \
  if (c < 0) \
    INVALID_SYNTAX_WITH_BUFFER (); \
  p += CHAR_STRING (c, (unsigned char *) p); \
  if (end - p < MAX_MULTIBYTE_LENGTH + 1) \
    { \
       offset = p - read_buffer; \
       emacs_abort (); \
       p = read_buffer + offset; \
       end = read_buffer + read_buffer_size; \
    }

#define INVALID_SYNTAX_WITH_BUFFER() \
  { \
    *p = 0; \
    invalid_syntax (read_buffer, readcharfun); \
  }

#define FINVALID_SYNTAX_WITH_BUFFER() \
  { \
    *p = 0; \
    finvalid_syntax (read_buffer); \
  }

/* Phase 6: Buffer-based Guile Reader Support */
static SCM
buffer_to_guile_port (Lisp_Object buffer)
{
  /* Convert buffer content to Guile string port for reading
     This enables Guile reader for buffer-based input */

  struct buffer *buf;

  if (BUFFERP (buffer))
    {
      buf = XBUFFER (buffer);
    }
  else
    {
      /* Use current buffer if no specific buffer provided */
      buf = current_buffer;
    }

  /* Extract buffer content as string */
  Lisp_Object buffer_string;
  ptrdiff_t start_pos = BUF_BEGV (buf);
  ptrdiff_t end_pos = BUF_ZV (buf);

  /* Create string from buffer range */
  buffer_string = make_buffer_string (start_pos, end_pos, true);

  /* Convert to Guile string port */
  return scm_open_input_string (buffer_string);
}

/* Enhanced read function with buffer support for Guile reader */
DEFUN ("read-from-buffer-guile", Fread_from_buffer_guile, Sread_from_buffer_guile, 0, 1, 0,
       doc: /* Read one Lisp expression from BUFFER using Guile reader.
If BUFFER is nil, read from the current buffer.
Returns the expression read from the buffer content. */)
  (Lisp_Object buffer)
{
  /* Phase 6: Buffer-based Guile reading capability */

  if (!NILP (buffer))
    CHECK_BUFFER (buffer);

  /* Convert buffer to Guile port */
  SCM port = buffer_to_guile_port (buffer);

  /* Read with error handling */
  SCM result = scm_c_catch (SCM_BOOL_T,
                            (scm_t_catch_body) scm_read, port,
                            (scm_t_catch_handler) guile_reader_error_handler, buffer,
                            NULL, NULL);

  /* Handle EOF */
  if (scm_is_eq (result, SCM_EOF_VAL))
    {
      scm_close_input_port (port);
      end_of_file_error ();
    }

  scm_close_input_port (port);
  return result;
}

/* Read a Lisp object.
   If LOCATE_SYMS is true, symbols are read with position.  */
static Lisp_Object
read0 (Lisp_Object readcharfun, bool locate_syms)
{
  /* FIX-guilemacs: Enhanced Guile reader migration - temporarily disabled for debugging */
#if 0
  if (STRINGP (readcharfun))
    {
      /* Use Guile reader for string input - more robust than C reader */
      SCM port = scm_open_input_string (readcharfun);
      /* Phase 8: Set UTF-8 encoding for proper symbol handling */
      scm_set_port_encoding_x (port, scm_from_utf8_string ("UTF-8"));

      /* Read with comprehensive error handling */
      SCM result = scm_c_catch (SCM_BOOL_T,
                                (scm_t_catch_body) scm_read, port,
                                (scm_t_catch_handler) guile_reader_error_handler, readcharfun,
                                NULL, NULL);

      /* Handle EOF */
      if (scm_is_eq (result, SCM_EOF_VAL))
        end_of_file_error ();

      return result;
    }
#endif
  /* Buffer reader disabled during bootstrap - use fallback C reader */
#if 0
  else if (BUFFERP (readcharfun))
    {
      /* Use Guile reader for buffer input */
      SCM port = buffer_to_guile_port (readcharfun);
      scm_set_port_encoding_x (port, scm_from_utf8_string ("UTF-8"));

      SCM result = scm_c_catch (SCM_BOOL_T,
                                (scm_t_catch_body) scm_read, port,
                                (scm_t_catch_handler) guile_reader_error_handler, readcharfun,
                                NULL, NULL);

      if (scm_is_eq (result, SCM_EOF_VAL))
        end_of_file_error ();

      return result;
    }
#endif

  /* Use original C reader for all input types */
  char stackbuf[64];
  char *read_buffer = stackbuf;
  ptrdiff_t read_buffer_size = sizeof stackbuf;
  ptrdiff_t offset;
  char *heapbuf = NULL;

  dynwind_begin ();
  ptrdiff_t base_sp = rdstack.sp;
  record_unwind_protect_intmax (read_stack_reset, base_sp);

  bool uninterned_symbol;
  bool skip_shorthand;

  /* Read an object into `obj'.  */
 read_obj: ;
  Lisp_Object obj;
  int c = READCHAR;
  if (c < 0)
    end_of_file_error ();

  switch (c)
    {
    case '(':
      read_stack_push ((struct read_stack_entry) {.type = RE_list_start});
      goto read_obj;

    case ')':
      if (read_stack_empty_p (base_sp))
	invalid_syntax (")", readcharfun);
      switch (read_stack_top ()->type)
	{
	case RE_list_start:
	  read_stack_pop ();
	  obj = Qnil;
	  break;
	case RE_list:
	  obj = read_stack_pop ()->u.list.head;
	  break;
	case RE_record:
	  {
	    locate_syms = read_stack_top ()->u.vector.old_locate_syms;
	    Lisp_Object elems = Fnreverse (read_stack_pop ()->u.vector.elems);
	    if (NILP (elems))
	      invalid_syntax ("#s", readcharfun);

	    if (BASE_EQ (XCAR (elems), Qhash_table))
	      obj = hash_table_from_plist (XCDR (elems));
	    else
	      obj = record_from_list (elems);
	    break;
	  }
	case RE_string_props:
	  locate_syms = read_stack_top ()->u.vector.old_locate_syms;
	  obj = string_props_from_rev_list (read_stack_pop () ->u.vector.elems,
					    readcharfun);
	  break;
	default:
	  invalid_syntax (")", readcharfun);
	}
      break;

    case '[':
      read_stack_push ((struct read_stack_entry) {
	  .type = RE_vector,
	  .u.vector.elems = Qnil,
	  .u.vector.old_locate_syms = locate_syms,
	});
      /* FIXME: should vectors be read with locate_syms=false?  */
      goto read_obj;

    case ']':
      if (read_stack_empty_p (base_sp))
	invalid_syntax ("]", readcharfun);
      switch (read_stack_top ()->type)
	{
	case RE_vector:
	  locate_syms = read_stack_top ()->u.vector.old_locate_syms;
	  obj = vector_from_rev_list (read_stack_pop ()->u.vector.elems);
	  break;
	case RE_char_table:
	  locate_syms = read_stack_top ()->u.vector.old_locate_syms;
	  obj = char_table_from_rev_list (read_stack_pop ()->u.vector.elems,
					  readcharfun);
	  break;
	case RE_sub_char_table:
	  locate_syms = read_stack_top ()->u.vector.old_locate_syms;
	  obj = sub_char_table_from_rev_list (read_stack_pop ()->u.vector.elems,
					      readcharfun);
	  break;
	default:
	  invalid_syntax ("]", readcharfun);
	  break;
	}
      break;

    case '#':
      {
	char *p = read_buffer;
	char *end = read_buffer + read_buffer_size;

	*p++ = '#';
	int ch;
	READ_AND_BUFFER (ch);

	switch (ch)
	  {
	  case '\'':
	    /* #'X -- special syntax for (function X) */
	    read_stack_push ((struct read_stack_entry) {
		.type = RE_special,
		.u.special.symbol = Qfunction,
	      });
	    goto read_obj;

	  case '#':
	    /* ## -- the empty symbol */
	    obj = Fintern (build_string(""), Qnil);
	    break;

	  case 's':
	    /* #s(...) -- a record or hash-table */
	    READ_AND_BUFFER (ch);
	    if (ch != '(')
	      {
		UNREAD (ch);
		INVALID_SYNTAX_WITH_BUFFER ();
	      }
	    read_stack_push ((struct read_stack_entry) {
		.type = RE_record,
		.u.vector.elems = Qnil,
		.u.vector.old_locate_syms = locate_syms,
	      });
	    locate_syms = false;
	    goto read_obj;

	  case '^':
	    /* #^[...]  -- char-table
	       #^^[...] -- sub-char-table */
	    READ_AND_BUFFER (ch);
	    if (ch == '^')
	      {
		ch = READCHAR;
		if (ch == '[')
		  {
		    read_stack_push ((struct read_stack_entry) {
			.type = RE_sub_char_table,
			.u.vector.elems = Qnil,
			.u.vector.old_locate_syms = locate_syms,
		      });
		    locate_syms = false;
		    goto read_obj;
		  }
		else
		  {
		    UNREAD (ch);
		    INVALID_SYNTAX_WITH_BUFFER ();
		  }
	      }
	    else if (ch == '[')
	      {
		read_stack_push ((struct read_stack_entry) {
		    .type = RE_char_table,
		    .u.vector.elems = Qnil,
		    .u.vector.old_locate_syms = locate_syms,
		  });
		locate_syms = false;
		goto read_obj;
	      }
	    else
	      {
		UNREAD (ch);
		INVALID_SYNTAX_WITH_BUFFER ();
	      }
	    break;

	  case '(':
	    /* #(...) -- string with properties */
	    read_stack_push ((struct read_stack_entry) {
		.type = RE_string_props,
		.u.vector.elems = Qnil,
		.u.vector.old_locate_syms = locate_syms,
	      });
	    locate_syms = false;
	    goto read_obj;

	  case '[':
	    /* #[...] -- byte-code (not supported in Guile reader) */
	    invalid_syntax ("Emacs bytecode syntax not supported", readcharfun);

	  case '&':
	    /* #&N"..." -- bool-vector */
	    obj = read_bool_vector (readcharfun);
	    break;

	  case '!':
	    /* #! appears at the beginning of an executable file.
	       Skip the rest of the line.  */
	    {
	      int c;
	      do
		c = READCHAR;
	      while (c >= 0 && c != '\n');
	      goto read_obj;
	    }

	  case 'x':
	  case 'X':
	    obj = read_integer (readcharfun, 16);
	    break;

	  case 'o':
	  case 'O':
	    obj = read_integer (readcharfun, 8);
	    break;

	  case 'b':
	  case 'B':
	    obj = read_integer (readcharfun, 2);
	    break;

	  case '@':
	    /* #@NUMBER syntax removed - not needed for Guile reader */
	    invalid_syntax ("#@", readcharfun);
	    break;

	  case '$':
	    /* #$ -- reference to lazy-loaded string */
	    obj = Vload_file_name;
	    break;

	  case ':':
	    /* #:X -- uninterned symbol */
	    c = READCHAR;
	    if (c <= 32 || c == NO_BREAK_SPACE
		|| c == '"' || c == '\'' || c == ';' || c == '#'
		|| c == '(' || c == ')'  || c == '[' || c == ']'
		|| c == '`' || c == ',')
	      {
		/* No symbol character follows: this is the empty symbol.  */
		UNREAD (c);
		obj = Fmake_symbol (build_string(""));
		break;
	      }
	    uninterned_symbol = true;
	    skip_shorthand = false;
	    goto read_symbol;

	  case '_':
	    /* #_X -- symbol without shorthand */
	    c = READCHAR;
	    if (c <= 32 || c == NO_BREAK_SPACE
		|| c == '"' || c == '\'' || c == ';' || c == '#'
		|| c == '(' || c == ')'  || c == '[' || c == ']'
		|| c == '`' || c == ',')
	      {
		/* No symbol character follows: this is the empty symbol.  */
		UNREAD (c);
		obj = Fintern (build_string(""), Qnil);
		break;
	      }
	    uninterned_symbol = false;
	    skip_shorthand = true;
	    goto read_symbol;

	  default:
	    if (ch >= '0' && ch <= '9')
	      {
		/* #N=OBJ or #N# -- first read the number N */
		EMACS_INT n = ch - '0';
		int c;
		for (;;)
		  {
		    READ_AND_BUFFER (c);
		    if (c < '0' || c > '9')
		      break;
		    if (ckd_mul (&n, n, 10)
			|| ckd_add (&n, n, c - '0'))
		      INVALID_SYNTAX_WITH_BUFFER ();
		  }
		if (c == 'r' || c == 'R')
		  {
		    /* #NrDIGITS -- radix-N number */
		    if (n < 0 || n > 36)
		      invalid_radix_integer (n, readcharfun);
		    obj = read_integer (readcharfun, n);
		    break;
		  }
		else if (n <= MOST_POSITIVE_FIXNUM && !NILP (Vread_circle))
		  {
		    if (c == '=')
		      {
			/* #N=OBJ -- assign number N to OBJ */
			Lisp_Object placeholder = Fcons (Qnil, Qnil);

			struct Lisp_Hash_Table *h
			  = XHASH_TABLE (read_objects_map);
			Lisp_Object number = make_fixnum (n);
			hash_hash_t hash;
			ptrdiff_t i = hash_lookup_get_hash (h, number, &hash);
			if (i >= 0)
			  /* Not normal, but input could be malformed.  */
			  set_hash_value_slot (h, i, placeholder);
			else
			  hash_put (h, number, placeholder, hash);
			read_stack_push ((struct read_stack_entry) {
			    .type = RE_numbered,
			    .u.numbered.number = number,
			    .u.numbered.placeholder = placeholder,
			  });
			goto read_obj;
		      }
		    else if (c == '#')
		      {
			/* #N# -- reference to numbered object */
			struct Lisp_Hash_Table *h
			  = XHASH_TABLE (read_objects_map);
			ptrdiff_t i = hash_lookup (h, make_fixnum (n));
			if (i < 0)
			  {
			    FINVALID_SYNTAX_WITH_BUFFER ();
			  }
			obj = HASH_VALUE (h, i);
			break;
		      }
		    else
		      INVALID_SYNTAX_WITH_BUFFER ();
		  }
		else
		  INVALID_SYNTAX_WITH_BUFFER ();
	      }
	    else
	      INVALID_SYNTAX_WITH_BUFFER ();
	  }
	break;
      }

    case '?':
      obj = read_char_literal (readcharfun);
      break;

    case '"':
      obj = read_string_literal (readcharfun);
      break;

    case '\'':
      read_stack_push ((struct read_stack_entry) {
	  .type = RE_special,
	  .u.special.symbol = Qquote,
	});
      goto read_obj;

    case '`':
      read_stack_push ((struct read_stack_entry) {
	  .type = RE_special,
	  .u.special.symbol = Qbackquote,
	});
      goto read_obj;

    case ',':
      {
	int ch = READCHAR;
	Lisp_Object sym;
	if (ch == '@')
	  sym = Qcomma_at;
	else
	  {
	    if (ch >= 0)
	      UNREAD (ch);
	    sym = Qcomma;
	  }
	read_stack_push ((struct read_stack_entry) {
	    .type = RE_special,
	    .u.special.symbol = sym,
	  });
	goto read_obj;
      }

    case ';':
      {
	int c;
	do
	  c = READCHAR;
	while (c >= 0 && c != '\n');
	goto read_obj;
      }

    case '.':
      {
	int nch = READCHAR;
	UNREAD (nch);
	if (nch <= 32 || nch == NO_BREAK_SPACE
	    || nch == '"' || nch == '\'' || nch == ';'
	    || nch == '(' || nch == '[' || nch == '#'
	    || nch == '?' || nch == '`' || nch == ',')
	  {
	    if (!read_stack_empty_p (base_sp)
		&& read_stack_top ()->type ==  RE_list)
	      {
		read_stack_top ()->type = RE_list_dot;
		goto read_obj;
	      }
	    invalid_syntax (".", readcharfun);
	  }
      }
      /* may be a number or symbol starting with a dot */
      FALLTHROUGH;

    default:
      if (c <= 32 || c == NO_BREAK_SPACE)
	goto read_obj;

      uninterned_symbol = false;
      skip_shorthand = false;
      /* symbol or number */
    read_symbol:
      {
	char *p = read_buffer;
	char *end = read_buffer + read_buffer_size;
	bool quoted = false;

	do
	  {
	    if (end - p < MAX_MULTIBYTE_LENGTH + 1)
	      {
		ptrdiff_t offset = p - read_buffer;
		read_buffer = grow_read_buffer (read_buffer, offset,
						&heapbuf, &read_buffer_size);
		p = read_buffer + offset;
		end = read_buffer + read_buffer_size;
	      }

	    if (c == '\\')
	      {
		c = READCHAR;
		if (c < 0)
		  end_of_file_error ();
		quoted = true;
	      }

	    p += CHAR_STRING (c, (unsigned char *) p);
	    c = READCHAR;
	  }
	while (c > 32
	       && c != NO_BREAK_SPACE
	       && (c >= 128
		   || !(   c == '"' || c == '\'' || c == ';' || c == '#'
			|| c == '(' || c == ')'  || c == '[' || c == ']'
			|| c == '`' || c == ',')));

	*p = 0;
	ptrdiff_t nbytes = p - read_buffer;
	UNREAD (c);

	/* Only attempt to parse the token as a number if it starts as one.  */
	char c0 = read_buffer[0];
	if (((c0 >= '0' && c0 <= '9') || c0 == '.' || c0 == '-' || c0 == '+')
	    && !quoted && !uninterned_symbol && !skip_shorthand)
	  {
	    ptrdiff_t len;
	    Lisp_Object result = string_to_number (read_buffer, 10, &len);
	    if (!NILP (result) && len == nbytes)
	      {
		obj = result;
		break;
	      }
	  }

	/* symbol, possibly uninterned */
	ptrdiff_t nchars = multibyte_chars_in_text ((unsigned char *)read_buffer, nbytes);
	Lisp_Object result;
	if (uninterned_symbol)
	  {
	    Lisp_Object name
	      = (!NILP (Vpurify_flag)
		 ? make_pure_string (read_buffer, nchars, nbytes, true)
		 : make_specified_string (read_buffer, nchars, nbytes,
					  true));
	    result = Fmake_symbol (name);
	  }
	else
	  {
	    /* Don't create the string object for the name unless
	       we're going to retain it in a new symbol.

		 Like intern_1 but supports multibyte names.  */
	      Lisp_Object obarray = check_obarray (Vobarray);
		{
		  Lisp_Object name
		    = make_specified_string (read_buffer, nchars, nbytes,
					     true);
		  result = intern_driver (name, obarray);
		}
	    }

	obj = result;
	break;
      }
    }

  /* We have read an object in `obj'.  Use the stack to decide what to
     do with it.  */
  while (rdstack.sp > base_sp)
    {
      struct read_stack_entry *e = read_stack_top ();
      switch (e->type)
	{
	case RE_list_start:
	  e->type = RE_list;
	  e->u.list.head = e->u.list.tail = Fcons (obj, Qnil);
	  goto read_obj;

	case RE_list:
	  {
	    Lisp_Object tl = Fcons (obj, Qnil);
	    XSETCDR (e->u.list.tail, tl);
	    e->u.list.tail = tl;
	    goto read_obj;
	  }

	case RE_list_dot:
	  {
	    skip_space_and_comments (readcharfun);
	    int ch = READCHAR;
	    if (ch != ')')
	      invalid_syntax ("expected )", readcharfun);
	    XSETCDR (e->u.list.tail, obj);
	    read_stack_pop ();
	    obj = e->u.list.head;

	    break;
	  }

	case RE_vector:
	case RE_record:
	case RE_char_table:
	case RE_sub_char_table:
	case RE_string_props:
	  e->u.vector.elems = Fcons (obj, e->u.vector.elems);
	  goto read_obj;

	case RE_special:
	  read_stack_pop ();
	  obj = list2 (e->u.special.symbol, obj);
	  break;

	case RE_numbered:
	  {
	    read_stack_pop ();
	    Lisp_Object placeholder = e->u.numbered.placeholder;
	    if (CONSP (obj))
	      {
		if (BASE_EQ (obj, placeholder))
		  /* Catch silly games like #1=#1# */
		  finvalid_syntax ("nonsensical self-reference");

		/* Optimization: since the placeholder is already
		   a cons, repurpose it as the actual value.
		   This allows us to skip the substitution below,
		   since the placeholder is already referenced
		   inside OBJ at the appropriate places.  */
		Fsetcar (placeholder, XCAR (obj));
		Fsetcdr (placeholder, XCDR (obj));

		struct Lisp_Hash_Table *h2
		  = XHASH_TABLE (read_objects_completed);
		hash_hash_t hash;
		ptrdiff_t i = hash_lookup_get_hash (h2, placeholder, &hash);
		eassert (i < 0);
		hash_put (h2, placeholder, Qnil, hash);
		obj = placeholder;
	      }
	    else
	      {
		/* If it can be recursive, remember it for future
		   substitutions.  */
		if (!SYMBOLP (obj) && !NUMBERP (obj)
		    && !(STRINGP (obj) && !string_intervals (obj)))
		  {
		    struct Lisp_Hash_Table *h2
		      = XHASH_TABLE (read_objects_completed);
		    hash_hash_t hash;
		    ptrdiff_t i = hash_lookup_get_hash (h2, obj, &hash);
		    eassert (i < 0);
		    hash_put (h2, obj, Qnil, hash);
		  }

		/* Now put it everywhere the placeholder was...  */
		Flread__substitute_object_in_subtree (obj, placeholder,
						      read_objects_completed);

		/* ...and #n# will use the real value from now on.  */
		struct Lisp_Hash_Table *h = XHASH_TABLE (read_objects_map);
		hash_hash_t hash;
		ptrdiff_t i = hash_lookup_get_hash (h, e->u.numbered.number,
						    &hash);
		eassert (i >= 0);
		set_hash_value_slot (h, i, obj);
	      }
	    break;
	  }
	}
    }

  dynwind_end ();
  return obj;
}

/* like read0, but used by LOAD only
 */
Lisp_Object
fread0 (SCM port)
{
  int c = scm_getc (port);
  return elisp_parse_with_eof_check_from_c_context (port, c);
}

DEFUN ("lread--substitute-object-in-subtree",
       Flread__substitute_object_in_subtree,
       Slread__substitute_object_in_subtree, 3, 3, 0,
       doc: /* In OBJECT, replace every occurrence of PLACEHOLDER with OBJECT.
COMPLETED is a hash table of objects that might be circular, or is t
if any object might be circular.  */)
  (Lisp_Object object, Lisp_Object placeholder, Lisp_Object completed)
{
  struct subst subst = { object, placeholder, completed, Qnil };
  Lisp_Object check_object = substitute_object_recurse (&subst, object);

  /* The returned object here is expected to always eq the
     original.  */
  if (!EQ (check_object, object))
    error ("Unexpected mutation error in reader");
  return Qnil;
}

static Lisp_Object
substitute_object_recurse (struct subst *subst, Lisp_Object subtree)
{
  /* If we find the placeholder, return the target object.  */
  if (EQ (subst->placeholder, subtree))
    return subst->object;

  /* For common object types that can't contain other objects, don't
     bother looking them up; we're done.  */
  if (SYMBOLP (subtree)
      || (STRINGP (subtree) && !string_intervals (subtree))
      || NUMBERP (subtree))
    return subtree;

  /* If we've been to this node before, don't explore it again.  */
  if (!NILP (Fmemq (subtree, subst->seen)))
    return subtree;

  /* If this node can be the entry point to a cycle, remember that
     we've seen it.  It can only be such an entry point if it was made
     by #n=, which means that we can find it as a value in
     COMPLETED.  */
  if (EQ (subst->completed, Qt)
      || hash_lookup (XHASH_TABLE (subst->completed), subtree) >= 0)
    subst->seen = Fcons (subtree, subst->seen);

  /* Recurse according to subtree's type.
     Every branch must return a Lisp_Object.  */
  if (VECTORLIKEP (subtree))
    {
	ptrdiff_t i = 0, length = 0;
	if (BOOL_VECTOR_P (subtree))
	  return subtree;		/* No sub-objects anyway.  */
	else if (CHAR_TABLE_P (subtree) || SUB_CHAR_TABLE_P (subtree)
		 || CLOSUREP (subtree) || HASH_TABLE_P (subtree)
		 || RECORDP (subtree))
	  length = PVSIZE (subtree);
	else if (PLAIN_VECTORP (subtree))
	  length = ASIZE (subtree);
	else
	  /* An unknown pseudovector may contain non-Lisp fields, so we
	     can't just blindly traverse all its fields.  We used to call
	     `Flength' which signaled `sequencep', so I just preserved this
	     behavior.  */
	  wrong_type_argument (Qsequencep, subtree);

	if (SUB_CHAR_TABLE_P (subtree))
	  i = 2;
	for ( ; i < length; i++)
	  ASET (subtree, i,
		substitute_object_recurse (subst, AREF (subtree, i)));

      return subtree;
    }
  else if (CONSP (subtree))
    {
      XSETCAR (subtree, substitute_object_recurse (subst, XCAR (subtree)));
      XSETCDR (subtree, substitute_object_recurse (subst, XCDR (subtree)));
      return subtree;
    }
  else if (STRINGP (subtree))
    {
	/* Check for text properties in each interval.
	   substitute_in_interval contains part of the logic.  */

	INTERVAL root_interval = string_intervals (subtree);
	traverse_intervals_noorder (root_interval,
				    substitute_in_interval, subst);
	return subtree;
    }
  else
    /* Other types don't recurse any further.  */
    return subtree;
}

/*  Helper function for substitute_object_recurse.  */
static void
substitute_in_interval (INTERVAL interval, void *arg)
{
  set_interval_plist (interval,
		      substitute_object_recurse (arg, interval->plist));
}


#if !IEEE_FLOATING_POINT
/* Strings that stand in for +NaN, -NaN, respectively.  */
static Lisp_Object not_a_number[2];
#endif

/* Convert the initial prefix of STRING to a number, assuming base BASE.
   If the prefix has floating point syntax and BASE is 10, return a
   nearest float; otherwise, if the prefix has integer syntax, return
   the integer; otherwise, return nil.  (On antique platforms that lack
   support for NaNs, if the prefix has NaN syntax return a Lisp object that
   will provoke an error if used as a number.)  If PLEN, set *PLEN to the
   length of the numeric prefix if there is one, otherwise *PLEN is
   unspecified.  */

Lisp_Object
string_to_number (char const *string, int base, ptrdiff_t *plen)
{
  char const *cp = string;
  bool float_syntax = false;
  double value = 0;

  /* Negate the value ourselves.  This treats 0, NaNs, and infinity properly on
     IEEE floating point hosts, and works around a formerly-common bug where
     atof ("-0.0") drops the sign.  */
  bool negative = *cp == '-';
  bool positive = *cp == '+';

  bool signedp = negative | positive;
  cp += signedp;

  enum { INTOVERFLOW = 1, LEAD_INT = 2, TRAIL_INT = 4, E_EXP = 16 };
  int state = 0;
  int leading_digit = digit_to_number (*cp, base);
  uintmax_t n = leading_digit;
  if (leading_digit >= 0)
    {
      state |= LEAD_INT;
      for (int digit; 0 <= (digit = digit_to_number (*++cp, base)); )
	{
	  if (INT_MULTIPLY_OVERFLOW (n, base))
	    state |= INTOVERFLOW;
	  n *= base;
	  if (INT_ADD_OVERFLOW (n, digit))
	    state |= INTOVERFLOW;
	  n += digit;
	}
    }
  char const *after_digits = cp;
  if (*cp == '.')
    {
      cp++;
    }

  if (base == 10)
    {
      if ('0' <= *cp && *cp <= '9')
	{
	  state |= TRAIL_INT;
	  do
	    cp++;
	  while ('0' <= *cp && *cp <= '9');
	}
      if (*cp == 'e' || *cp == 'E')
	{
	  char const *ecp = cp;
	  cp++;
	  if (*cp == '+' || *cp == '-')
	    cp++;
	  if ('0' <= *cp && *cp <= '9')
	    {
	      state |= E_EXP;
	      do
		cp++;
	      while ('0' <= *cp && *cp <= '9');
	    }
	  else if (cp[-1] == '+'
		   && cp[0] == 'I' && cp[1] == 'N' && cp[2] == 'F')
	    {
	      state |= E_EXP;
	      cp += 3;
	      value = INFINITY;
	    }
	  else if (cp[-1] == '+'
		   && cp[0] == 'N' && cp[1] == 'a' && cp[2] == 'N')
	    {
	      state |= E_EXP;
	      cp += 3;
#if IEEE_FLOATING_POINT
	      union ieee754_double u
		= { .ieee_nan = { .exponent = 0x7ff, .quiet_nan = 1,
				  .mantissa0 = n >> 31 >> 1, .mantissa1 = n }};
	      value = u.d;
#else
	      if (plen)
		*plen = cp - string;
	      return not_a_number[negative];
#endif
	    }
	  else
	    cp = ecp;
	}

      /* A float has digits after the dot or an exponent.
	 This excludes numbers like "1." which are lexed as integers. */
      float_syntax = ((state & TRAIL_INT)
		      || ((state & LEAD_INT) && (state & E_EXP)));
    }

  if (plen)
    *plen = cp - string;

  /* Return a float if the number uses float syntax.  */
  if (float_syntax)
    {
      /* Convert to floating point, unless the value is already known
	 because it is infinite or a NaN.  */
      if (! value)
	value = atof (string + signedp);
      return make_float (negative ? -value : value);
    }

  /* Return nil if the number uses invalid syntax.  */
  if (! (state & LEAD_INT))
    return Qnil;

  /* Fast path if the integer (san sign) fits in uintmax_t.  */
  if (! (state & INTOVERFLOW))
    {
      if (!negative)
	return make_uint (n);
      if (-MOST_NEGATIVE_FIXNUM < n)
        {
	  return scm_product(scm_from_int (-1), scm_from_uintmax (n));
        }
      EMACS_INT signed_n = n;
      return make_fixnum (-signed_n);
    }

  /* Trim any leading "+" and trailing nondigits, then return a bignum.  */
  string += positive;
  if (!*after_digits)
    {
      return scm_string_to_number (scm_from_locale_string (string), make_fixnum(base));
    }
  ptrdiff_t trimmed_len = after_digits - string;
  USE_SAFE_ALLOCA;
  char *trimmed = SAFE_ALLOCA (trimmed_len + 1);
  memcpy (trimmed, string, trimmed_len);
  trimmed[trimmed_len] = '\0';
  Lisp_Object result = scm_string_to_number (scm_from_locale_string (trimmed), make_fixnum(base));
  SAFE_FREE ();
  return result;
}

Lisp_Object
string_to_number_Ls (Lisp_Object ls, int base, ptrdiff_t *plen)
{
  char *str = scm_to_locale_string (ls);
  Lisp_Object ret = string_to_number (str, base, plen);
  free (str);
  return ret;
}

/* Reduce an EMACS_UINT hash value to hash_hash_t.  */
hash_hash_t
reduce_emacs_uint_to_hash_hash (EMACS_UINT x)
{
  verify (sizeof x <= 2 * sizeof (hash_hash_t));
  return (sizeof x == sizeof (hash_hash_t)
	  ? x
	  : x ^ (x >> (8 * (sizeof x - sizeof (hash_hash_t)))));
}

/* Reduce HASH to a value BITS wide.  */
ptrdiff_t
knuth_hash (hash_hash_t hash, unsigned bits)
{
  /* Knuth multiplicative hashing, tailored for 32-bit indices
     (avoiding a 64-bit multiply).  */
  uint32_t alpha = 2654435769;	/* 2**32/phi */
  /* Note the cast to uint64_t, to make it work for bits=0.  */
  return (uint64_t)((uint32_t)hash * alpha) >> (32 - bits);
}

Lisp_Object
intern_driver (Lisp_Object string, Lisp_Object obarray)
{
  return Fintern (string, obarray);
}


static Lisp_Object initial_obarray;

/* Scheme obarray module integration.
   After bootstrap, we delegate to (emacs obarray) for all obarray operations.
   This provides a single source of truth for symbol tracking. */

static bool obarray_scheme_ready = false;
static SCM obarray_intern_fn = SCM_BOOL_F;
static SCM obarray_find_symbol_fn = SCM_BOOL_F;
static SCM obarray_mapatoms_fn = SCM_BOOL_F;
static SCM obarray_register_fn = SCM_BOOL_F;
static SCM obarray_unintern_fn = SCM_BOOL_F;
static SCM obarray_clear_fn = SCM_BOOL_F;

/* Callback to migrate bootstrap symbols to Scheme */
static Lisp_Object
migrate_symbol_to_scheme (void *data, Lisp_Object key, Lisp_Object sym)
{
  (void)data;
  /* Register this symbol in Scheme's *global-symbols* */
  scm_call_2 (obarray_register_fn, key, sym);
  return SCM_UNSPECIFIED;
}

/* Initialize Scheme obarray module references.
   Called once after Scheme is fully loaded. */
static void
init_obarray_scheme (void)
{
  if (obarray_scheme_ready)
    return;

  SCM module = scm_c_resolve_module ("emacs obarray");
  if (scm_is_false (module))
    return;  /* Module not yet available */

  SCM var;

  var = scm_c_module_lookup (module, "obarray-intern");
  if (scm_is_true (var) && scm_variable_bound_p (var))
    obarray_intern_fn = scm_variable_ref (var);

  var = scm_c_module_lookup (module, "obarray-find-symbol");
  if (scm_is_true (var) && scm_variable_bound_p (var))
    obarray_find_symbol_fn = scm_variable_ref (var);

  var = scm_c_module_lookup (module, "obarray-mapatoms");
  if (scm_is_true (var) && scm_variable_bound_p (var))
    obarray_mapatoms_fn = scm_variable_ref (var);

  var = scm_c_module_lookup (module, "register-symbol!");
  if (scm_is_true (var) && scm_variable_bound_p (var))
    obarray_register_fn = scm_variable_ref (var);

  var = scm_c_module_lookup (module, "obarray-unintern");
  if (scm_is_true (var) && scm_variable_bound_p (var))
    obarray_unintern_fn = scm_variable_ref (var);

  var = scm_c_module_lookup (module, "obarray-clear");
  if (scm_is_true (var) && scm_variable_bound_p (var))
    obarray_clear_fn = scm_variable_ref (var);

  /* All functions must be available */
  if (scm_is_true (obarray_intern_fn) &&
      scm_is_true (obarray_find_symbol_fn) &&
      scm_is_true (obarray_mapatoms_fn) &&
      scm_is_true (obarray_register_fn) &&
      scm_is_true (obarray_unintern_fn) &&
      scm_is_true (obarray_clear_fn))
    {
      obarray_scheme_ready = true;

      /* Migrate bootstrap symbols from C hash table to Scheme.
         This ensures symbols created before Scheme was ready
         are visible to mapatoms. */
      Lisp_Object ht = obhash (initial_obarray);
      scm_hash_for_each (make_c_closure (migrate_symbol_to_scheme, NULL, 2, 0), ht);
    }
}

static bool
is_global_obarray (Lisp_Object obarray)
{
  return EQ (obarray, initial_obarray) || EQ (obarray, Vobarray);
}

Lisp_Object
obhash (Lisp_Object obarray)
{
  /* For vanilla Guile: return a hash table for the obarray */
  Lisp_Object tem = scm_hashq_get_handle (obarrays, obarray);
  if (SCM_UNLIKELY (scm_is_false (tem)))
    {
      /* Create a new hash table for this obarray */
      Lisp_Object ht = scm_make_hash_table (scm_from_int (67));
      tem = scm_hashq_create_handle_x (obarrays, obarray, ht);
    }
  return scm_cdr (tem);
}

static Lisp_Object make_obarray (unsigned bits);

/* Get an error if OBARRAY is not an obarray.
   If it is one, return it.  */

Lisp_Object
check_obarray_slow (Lisp_Object obarray)
{
  /* For compatibility, we accept vectors whose first element is 0,
     and store an obarray object there.  */
  if ((PLAIN_VECTORP (obarray)) && ASIZE (obarray) > 0)
    {
      //FIX: obsolete old-style obarrays
      return obarray;
      Lisp_Object obj = AREF (obarray, 0);
      if (OBARRAYP (obj))
	return obj;
      if (BASE_EQ (obj, make_fixnum (0)))
	{
	  /* Put an actual obarray object in the first slot.
	     The rest of the vector remains unused.  */
	  obj = make_obarray (0);
	  ASET (obarray, 0, obj);
	  return obj;
	}
    }
  // we really dont care about obarray, because it is only used as a hash-key
  // to the real obarray that lies in guile
  return obarray;
  /* Reset Vobarray to the standard obarray for nicer error handling. */
  if (BASE_EQ (Vobarray, obarray)) Vobarray = initial_obarray;

  wrong_type_argument (Qobarrayp, obarray);
}

/* Intern the C string STR: return a symbol with that name,
   interned in the current obarray.  */

Lisp_Object
intern_1 (const char *str, ptrdiff_t len)
{
  Lisp_Object obarray = check_obarray (Vobarray);
	/* The above `oblookup' was done on the basis of nchars==nbytes, so
	   the string has to be unibyte.  */

  return intern_driver (scm_from_utf8_stringn (str, len), obarray);
}

Lisp_Object
intern_c_string_1 (const char *str, ptrdiff_t len)
{
  Lisp_Object s = make_pure_c_string (str, len);
  if (!s) printf("WARNING, zero string\n");
  return Fintern (s, initial_obarray);
  //return Fintern (make_pure_c_string (str, len), initial_obarray);
}

/* Intern STR of NBYTES bytes and NCHARS characters in the default obarray.  */
Lisp_Object
intern_c_multibyte (const char *str, ptrdiff_t nchars, ptrdiff_t nbytes)
{
  Lisp_Object obarray = check_obarray (Vobarray);
  return intern_driver (make_multibyte_string (str, nchars, nbytes),
			obarray);
}


static Lisp_Object
intern_initial_c_string (const char *cstr)
{
  Lisp_Object string = scm_from_utf8_string (cstr);
  /* FIX-20250121-guilemacs: Use string->symbol for vanilla Guile */
  Lisp_Object sym = scm_string_to_symbol (string);

  /* Handle keyword symbols (starting with ':') */
  size_t len = strlen (cstr);
  if (len > 0 && cstr[0] == ':')
    {
      SET_SYMBOL_TRAPPED (XSYMBOL (sym), SYMBOL_NOWRITE);
      SET_SYMBOL_REDIRECT (XSYMBOL (sym), SYMBOL_PLAINVAL);
      SET_SYMBOL_VAL (XSYMBOL (sym), sym);
    }

  /* Add to obarray's hash table for mapatoms support.
     Use string as key, symbol as value (same format as custom obarrays).
     Also increment initial_obarray count for accurate display. */
  Lisp_Object ht = obhash (initial_obarray);
  Lisp_Object existing = scm_hash_ref (ht, string, SCM_BOOL_F);
  if (scm_is_false (existing))
    {
      scm_hash_set_x (ht, string, sym);
      XOBARRAY (initial_obarray)->count++;
    }

  if (!sym) {
    printf("ouch! sym is zero\n");
  }
  return sym;
}

DEFUN ("find-symbol", Ffind_symbol, Sfind_symbol, 1, 2, 0,
       doc: /* find-symbol */)
     (Lisp_Object string, Lisp_Object obarray)
{
  Lisp_Object tem;
  bool is_global;

  obarray = check_obarray (NILP (obarray) ? Vobarray : obarray);
  CHECK_STRING (string);

  /* Unwrap emacs-string wrappers before passing to Guile */
  Lisp_Object raw_string = unwrap_emacs_string (string);
  is_global = is_global_obarray (obarray);

  /* Try to use Scheme module if ready */
  init_obarray_scheme ();
  if (obarray_scheme_ready)
    {
      /* Delegate to Scheme: (obarray-find-symbol string obarray-or-nil)
         Returns multiple values: (symbol found?) */
      Lisp_Object ob_arg = is_global ? Qnil : obhash (obarray);
      return scm_call_2 (obarray_find_symbol_fn, raw_string, ob_arg);
    }

  /* Bootstrap fallback */
  if (is_global)
    {
      /* Global obarray: string->symbol always succeeds in Guile */
      tem = scm_string_to_symbol (raw_string);
      if (EQ (tem, Qnil_))
        tem = Qnil;
      else if (EQ (tem, Qt_))
        tem = Qt;
      return scm_values (scm_list_2 (tem, Qt));
    }
  else
    {
      /* Custom obarray: look up in hash table */
      Lisp_Object ht = obhash (obarray);
      tem = scm_hash_ref (ht, raw_string, SCM_BOOL_F);
      if (scm_is_true (tem))
        {
          if (EQ (tem, Qnil_))
            tem = Qnil;
          else if (EQ (tem, Qt_))
            tem = Qt;
          return scm_values (scm_list_2 (tem, Qt));
        }
      else
        return scm_values (scm_list_2 (Qnil, Qnil));
    }
}


DEFUN ("intern", Fintern, Sintern, 1, 2, 0,
       doc: /* Return the canonical symbol whose name is STRING.
If there is none, one is created by this function and returned.
A second optional argument specifies the obarray to use;
it defaults to the value of `obarray'.  */)
  (Lisp_Object string, Lisp_Object obarray)
{
  Lisp_Object sym;
  bool is_global;

  obarray = check_obarray (NILP (obarray) ? Vobarray : obarray);
  CHECK_STRING (string);

  /* Unwrap emacs-string wrappers before passing to Guile */
  Lisp_Object raw_string = unwrap_emacs_string (string);
  is_global = is_global_obarray (obarray);

  /* Try to use Scheme module if ready */
  init_obarray_scheme ();
  if (obarray_scheme_ready)
    {
      /* Delegate to Scheme: (obarray-intern string obarray-or-nil) */
      Lisp_Object ob_arg = is_global ? Qnil : obhash (obarray);
      sym = scm_call_2 (obarray_intern_fn, raw_string, ob_arg);

      /* Post-process keywords in C (need access to XSYMBOL macros) */
      if (SYMBOLP (sym) && is_global
          && scm_c_string_length (raw_string) > 0
          && guile_string_starts_with_char (raw_string, ':'))
        {
          SET_SYMBOL_TRAPPED (XSYMBOL (sym), SYMBOL_NOWRITE);
          SET_SYMBOL_REDIRECT (XSYMBOL (sym), SYMBOL_PLAINVAL);
          SET_SYMBOL_VAL (XSYMBOL (sym), sym);
        }

      return sym;
    }

  /* Bootstrap fallback: Scheme not ready yet, use C implementation */
  if (is_global)
    {
      /* Special case: "nil" and "t" must return canonical elisp values */
      size_t len = scm_c_string_length (raw_string);
      if (len == 3)
        {
          char buf[4];
          scm_to_locale_stringbuf (raw_string, buf, 4);
          buf[3] = '\0';
          if (strcmp (buf, "nil") == 0)
            return Qnil;
        }
      else if (len == 1)
        {
          char buf[2];
          scm_to_locale_stringbuf (raw_string, buf, 2);
          buf[1] = '\0';
          if (buf[0] == 't')
            return Qt;
        }

      /* Global obarray: use Guile's string->symbol */
      sym = scm_string_to_symbol (raw_string);

      /* Handle keyword symbols */
      if (scm_c_string_length (raw_string)
          && guile_string_starts_with_char (raw_string, ':'))
        {
          SET_SYMBOL_TRAPPED (XSYMBOL (sym), SYMBOL_NOWRITE);
          SET_SYMBOL_REDIRECT (XSYMBOL (sym), SYMBOL_PLAINVAL);
          SET_SYMBOL_VAL (XSYMBOL (sym), sym);
        }

      /* Track in C-side hash table (for bootstrap, before Scheme takes over) */
      Lisp_Object ht = obhash (obarray);
      Lisp_Object existing = scm_hash_ref (ht, raw_string, SCM_BOOL_F);
      if (scm_is_false (existing))
        {
          scm_hash_set_x (ht, raw_string, sym);
          XOBARRAY (obarray)->count++;
        }
    }
  else
    {
      /* Custom obarray: use hash table */
      Lisp_Object ht = obhash (obarray);

      /* First check if already interned */
      Lisp_Object tem = scm_hash_ref (ht, raw_string, SCM_BOOL_F);
      if (scm_is_true (tem))
        return tem;

      /* Create unique symbol for custom obarray */
      static long obarray_symbol_counter = 0;
      char unique_name[256];
      snprintf (unique_name, sizeof(unique_name), "__ob%ld_%s",
                obarray_symbol_counter++,
                scm_to_utf8_string (raw_string));
      sym = scm_string_to_symbol (scm_from_utf8_string (unique_name));

      /* Store in hash table with original string as key */
      scm_hash_set_x (ht, raw_string, sym);
    }

  return sym;
}

DEFUN ("intern-soft", Fintern_soft, Sintern_soft, 1, 2, 0,
       doc: /* Return the canonical symbol named NAME, or nil if none exists.
NAME may be a string or a symbol.  If it is a symbol, that exact
symbol is searched for.
A second optional argument specifies the obarray to use;
it defaults to the value of `obarray'.  */)
  (Lisp_Object name, Lisp_Object obarray)
{
  register Lisp_Object tem, string, mv, found;

  string = SYMBOLP (name) ? SYMBOL_NAME (name) : name;
  mv = Ffind_symbol (string, obarray);
  tem = scm_c_value_ref (mv, 0);
  found = scm_c_value_ref (mv, 1);

  if (NILP (found) || (SYMBOLP (name) && !EQ (name, tem)))
    return Qnil;
  else
    return tem;
}

DEFUN ("unintern", Funintern, Sunintern, 2, 2, 0,
       doc: /* Delete the symbol named NAME, if any, from OBARRAY.
The value is t if a symbol was found and deleted, nil otherwise.
NAME may be a string or a symbol.  If it is a symbol, that symbol
is deleted, if it belongs to OBARRAY--no other symbol is deleted.
OBARRAY, if nil, defaults to the value of the variable `obarray'.  */)
  (Lisp_Object name, Lisp_Object obarray)
{
  Lisp_Object string;
  bool is_global;

  if (NILP (obarray))
    obarray = Vobarray;
  obarray = check_obarray (obarray);

  if (SYMBOLP (name))
    string = SYMBOL_NAME (name);
  else
    {
      CHECK_STRING (name);
      string = name;
    }

  Lisp_Object raw_string = unwrap_emacs_string (string);
  is_global = is_global_obarray (obarray);

  /* Try to use Scheme module if ready */
  init_obarray_scheme ();
  if (obarray_scheme_ready)
    {
      Lisp_Object ob_arg = is_global ? Qnil : obhash (obarray);
      Lisp_Object result = scm_call_2 (obarray_unintern_fn, raw_string, ob_arg);
      return scm_is_true (result) ? Qt : Qnil;
    }

  /* Bootstrap fallback */
  if (is_global)
    {
      /* Cannot unintern from Guile's global symbol table */
      return Qnil;
    }
  else
    {
      /* Custom obarray: remove from hash table */
      Lisp_Object ht = obhash (obarray);
      Lisp_Object existing = scm_hash_ref (ht, raw_string, SCM_BOOL_F);

      if (scm_is_false (existing))
        return Qnil;

      /* If name is a symbol, verify it matches */
      if (SYMBOLP (name) && !EQ (name, existing))
        return Qnil;

      scm_hash_remove_x (ht, raw_string);
      return Qt;
    }
}

struct map_obarray_data
{
  Lisp_Object obarray;
  void (*fn) (Lisp_Object, Lisp_Object);
  Lisp_Object arg;
};

/* Hash table iteration callback for vanilla Guile */
static Lisp_Object
map_obarray_hash_inner (void *data, Lisp_Object key, Lisp_Object value)
{
  struct map_obarray_data *modata = data;
  /* value is the symbol, key is the string name */
  modata->fn (value, modata->arg);
  return SCM_UNSPECIFIED;
}

static struct Lisp_Obarray *
allocate_obarray (void)
{
  return ALLOCATE_PLAIN_PSEUDOVECTOR (struct Lisp_Obarray, PVEC_OBARRAY);
}

/* Callback for Scheme obarray iteration */
static Lisp_Object
map_obarray_scheme_callback (void *data_ptr, Lisp_Object sym)
{
  struct map_obarray_data *data = data_ptr;
  data->fn (sym, data->arg);
  return SCM_UNSPECIFIED;
}

void
map_obarray (Lisp_Object obarray, void (*fn) (Lisp_Object, Lisp_Object), Lisp_Object arg)
{
  struct map_obarray_data data = { .obarray = obarray,
                                   .fn = fn,
                                   .arg = arg };
  bool is_global;

  CHECK_OBARRAY (obarray);
  is_global = is_global_obarray (obarray);

  /* Try to use Scheme module if ready */
  init_obarray_scheme ();
  if (obarray_scheme_ready)
    {
      /* Delegate to Scheme: (obarray-mapatoms proc obarray-or-nil)
         The Scheme side uses *global-symbols* as single source of truth. */
      Lisp_Object ob_arg = is_global ? Qnil : obhash (obarray);
      Lisp_Object callback = make_c_closure (map_obarray_scheme_callback, &data, 1, 0);
      scm_call_2 (obarray_mapatoms_fn, callback, ob_arg);
      return;
    }

  /* Bootstrap fallback: use C-side hash tables */
  Lisp_Object ht = obhash (obarray);
  scm_hash_for_each (make_c_closure (map_obarray_hash_inner, &data, 2, 0), ht);

  /* For the global obarray during bootstrap, also iterate symbols
     from the Scheme-side runtime modules. */
  if (is_global)
    {
      Lisp_Object runtime_module = scm_c_resolve_module ("emacs-elisp runtime");
      Lisp_Object for_each_sym = scm_c_module_lookup (runtime_module,
                                                      "for-each-elisp-symbol");
      if (scm_is_true (for_each_sym) && scm_variable_bound_p (for_each_sym))
        {
          Lisp_Object for_each_fn = scm_variable_ref (for_each_sym);
          Lisp_Object callback = make_c_closure (map_obarray_scheme_callback,
                                                 &data, 1, 0);
          scm_call_1 (for_each_fn, callback);
        }
    }
}

static Lisp_Object
make_obarray (unsigned bits)
{
  struct Lisp_Obarray *o = allocate_obarray ();
  o->count = 0;
  o->size_bits = bits;
  ptrdiff_t size = (ptrdiff_t)1 << bits;
  o->buckets = hash_table_alloc_bytes (size * sizeof *o->buckets);
  for (ptrdiff_t i = 0; i < size; i++)
    o->buckets[i] = make_fixnum (0);
  return make_lisp_obarray (o);
}

static void
mapatoms_1 (Lisp_Object sym, Lisp_Object function)
{
  call1 (function, sym);
}

DEFUN ("mapatoms", Fmapatoms, Smapatoms, 1, 2, 0,
       doc: /* Call FUNCTION on every symbol in OBARRAY.
OBARRAY defaults to the value of `obarray'.  */)
  (Lisp_Object function, Lisp_Object obarray)
{
  if (NILP (obarray)) obarray = Vobarray;
  obarray = check_obarray (obarray);

  map_obarray (obarray, mapatoms_1, function);
  return Qnil;
}

DEFUN ("obarray-make", Fobarray_make, Sobarray_make, 0, 1, 0,
       doc: /* Return a new obarray of size SIZE.
The obarray will grow to accommodate any number of symbols; the size, if
given, is only a hint for the expected number.  */)
  (Lisp_Object size)
{
  return make_obarray (128); // FIX: obarray_default_bits;
}

DEFUN ("obarrayp", Fobarrayp, Sobarrayp, 1, 1, 0,
       doc: /* Return t iff OBJECT is an obarray.  */)
  (Lisp_Object object)
{
  return OBARRAYP (object) ? Qt : Qnil;
}

DEFUN ("obarray-clear", Fobarray_clear, Sobarray_clear, 1, 1, 0,
       doc: /* Remove all symbols from OBARRAY.  */)
  (Lisp_Object obarray)
{
  bool is_global = is_global_obarray (obarray);

  /* Try to use Scheme module if ready */
  init_obarray_scheme ();
  if (obarray_scheme_ready)
    {
      Lisp_Object ob_arg = is_global ? Qnil : obhash (obarray);
      scm_call_1 (obarray_clear_fn, ob_arg);
      return Qnil;
    }

  /* Bootstrap fallback */
  if (is_global)
    {
      /* Cannot clear Guile's global symbol table */
      return Qnil;
    }

  /* Clear the hash table for custom obarray */
  Lisp_Object ht = obhash (obarray);
  scm_hash_clear_x (ht);
  return Qnil;
}

DEFUN ("internal--obarray-buckets",
       Finternal__obarray_buckets, Sinternal__obarray_buckets, 1, 1, 0,
       doc: /* Symbols in each bucket of OBARRAY.  Internal use only.  */)
    (Lisp_Object obarray)
{
  emacs_abort ();
}

void
init_obarray_once (void)
{
  Vobarray = make_obarray (15);
  initial_obarray = Vobarray;
  staticpro (&initial_obarray);

  obarrays = scm_make_hash_table (SCM_UNDEFINED);
  /* Initialize the global obarray's hash table
     for tracking symbols (needed for mapatoms on vanilla Guile). */
  scm_hashq_set_x (obarrays, Vobarray, scm_c_make_hash_table (8192));

  for (int i = 0; i < ARRAYELTS (lispsym); i++)
    lispsym[i].u.s.self_ = intern_initial_c_string (defsym_name[i]);

  DEFSYM (Qunbound, "unbound");
  //SET_SYMBOL_VAL (XSYMBOL (Qnil), Qnil);
  //make_symbol_constant (Qnil);
  DEFSYM (Qt, "t");
  DEFSYM (Qnil_, "nil");
  DEFSYM (Qt_, "t");
  //SET_SYMBOL_VAL (XSYMBOL (Qt), Qt);
  //make_symbol_constant (Qt);

  lispsym[iQnil].u.s.self_ = SCM_ELISP_NIL;
  lispsym[iQt].u.s.self_ = SCM_BOOL_T;

  fprintf(stderr, "DEBUG: Qnil = %p, Qt = %p\n", (void*)Qnil, (void*)Qt);
  fprintf(stderr, "DEBUG: SCM_ELISP_NIL = %p, SCM_BOOL_T = %p\n", (void*)SCM_ELISP_NIL, (void*)SCM_BOOL_T);

  //Qnil_ = intern_c_string ("nil");
  //define_symbol (Qnil_, "nil");
  //SET_SYMBOL_VAL (XSYMBOL (Qnil_), Qnil);
  //SET_SYMBOL_CONSTANT (XSYMBOL (Qnil_), 1);
  //SET_SYMBOL_DECLARED_SPECIAL (XSYMBOL (Qnil_), 1);

  //Qt_ = intern_c_string ("t");
  //define_symbol (Qt_, "t");
  //SET_SYMBOL_VAL (XSYMBOL (Qt_), Qt);
  //SET_SYMBOL_CONSTANT (XSYMBOL (Qt_), 1);
  //SET_SYMBOL_DECLARED_SPECIAL (XSYMBOL (Qt_), 1);

  lispsym[iQunbound].u.s.self_ = scm_c_public_ref ("emacs-elisp runtime", "unbound");
  SET_SYMBOL_VAL (XSYMBOL (Qunbound), Qunbound);

  //for (int i = 0; i <  ARRAYELTS (lispsym); i++)
  //  define_symbol (builtin_lisp_symbol (i), defsym_name[i], Vobarray);

  /* Qt is correct even if not dumping.  loadup.el will set to nil at end.  */
  Vpurify_flag = Qt;

  DEFSYM (Qvariable_documentation, "variable-documentation");
}


void
defsubr (const char *lname, scm_t_subr gsubr_fn, short min_args, short max_args, const char *intspec)
{
  Lisp_Object sym = intern_c_string (lname);
  Lisp_Object fn;
  switch (max_args)
    {
    case MANY:
      fn = scm_c_make_gsubr (lname, 0, 0, 1, gsubr_fn);
      break;
    case UNEVALLED:
      fn = Fcons (Qspecial_operator,
                  scm_c_make_gsubr (lname, 0, 0, 1, gsubr_fn));
      break;
    default:
      fn = scm_c_make_gsubr (lname, min_args, max_args - min_args, 0, gsubr_fn);
      break;
    }
  set_symbol_function (sym, fn);
  if (intspec)
    {
      Lisp_Object tem = ((*intspec != '(')
                         ? build_string (intspec)
                         : Fcar (Fread_from_string (build_string (intspec),
                                                    Qnil, Qnil)));
      scm_set_procedure_property_x (fn, Qinteractive_form, tem);
    }
}

/* Define an "integer variable"; a symbol whose value is forwarded to a
   C variable of type intmax_t.  Sample call (with "xx" to fool make-docfile):
   DEFxxVAR_INT ("emacs-priority", &emacs_priority, "Documentation");  */
void
defvar_int (struct Lisp_Intfwd const *i_fwd, char const *namestring)
{
  Lisp_Object sym = intern_c_string (namestring);
  SET_SYMBOL_DECLARED_SPECIAL (XSYMBOL (sym), 1);
  SET_SYMBOL_REDIRECT (XSYMBOL (sym), SYMBOL_FORWARDED);
  SET_SYMBOL_FWD (XSYMBOL (sym), i_fwd);
}

/* Similar but define a variable whose value is t if 1, nil if 0.  */
void
defvar_bool (struct Lisp_Boolfwd const *b_fwd, char const *namestring)
{
  Lisp_Object sym = intern_c_string (namestring);
  SET_SYMBOL_DECLARED_SPECIAL (XSYMBOL (sym), 1);
  SET_SYMBOL_REDIRECT (XSYMBOL (sym), SYMBOL_FORWARDED);
  SET_SYMBOL_FWD (XSYMBOL (sym), b_fwd);
  Vbyte_boolean_vars = Fcons (sym, Vbyte_boolean_vars);
}

/* Similar but define a variable whose value is the Lisp Object stored
   at address.  Two versions: with and without gc-marking of the C
   variable.  The nopro version is used when that variable will be
   gc-marked for some other reason, since marking the same slot twice
   can cause trouble with strings.  */
void
defvar_lisp_nopro (struct Lisp_Objfwd const *o_fwd, char const *namestring)
{
  Lisp_Object sym = intern_c_string (namestring);
  SET_SYMBOL_DECLARED_SPECIAL (XSYMBOL (sym), 1);
  SET_SYMBOL_REDIRECT (XSYMBOL (sym), SYMBOL_FORWARDED);
  SET_SYMBOL_FWD (XSYMBOL (sym), o_fwd);
}

void
defvar_lisp (struct Lisp_Objfwd const *o_fwd, char const *namestring)
{
  defvar_lisp_nopro (o_fwd, namestring);
  staticpro (o_fwd->objvar);
}

/* Similar but define a variable whose value is the Lisp Object stored
   at a particular offset in the current kboard object.  */

void
defvar_kboard (struct Lisp_Kboard_Objfwd const *ko_fwd, char const *namestring)
{
  Lisp_Object sym = intern_c_string (namestring);
  SET_SYMBOL_DECLARED_SPECIAL (XSYMBOL (sym), 1);
  SET_SYMBOL_REDIRECT (XSYMBOL (sym), SYMBOL_FORWARDED);
  SET_SYMBOL_FWD (XSYMBOL (sym), ko_fwd);
}

/* Check that the elements of lpath exist.  */

static void
load_path_check (Lisp_Object lpath)
{
  Lisp_Object path_tail;

  /* The only elements that might not exist are those from
     PATH_LOADSEARCH, EMACSLOADPATH.  Anything else is only added if
     it exists.  */
  for (path_tail = lpath; !NILP (path_tail); path_tail = XCDR (path_tail))
    {
      Lisp_Object dirfile;
      dirfile = Fcar (path_tail);
      if (STRINGP (dirfile))
        {
          dirfile = Fdirectory_file_name (dirfile);
          if (! file_accessible_directory_p (dirfile))
            dir_warning ("Lisp directory", XCAR (path_tail));
        }
    }
}

/* Return the default load-path, to be used if EMACSLOADPATH is unset.
   This does not include the standard site-lisp directories
   under the installation prefix (i.e., PATH_SITELOADSEARCH),
   but it does (unless no_site_lisp is set) include site-lisp
   directories in the source/build directories if those exist and we
   are running uninstalled.

   Uses the following logic:
   The remainder is what happens when dumping is about to happen:
   If dumping, just use PATH_DUMPLOADSEARCH.
   Otherwise use PATH_LOADSEARCH.

   If !initialized, then just return PATH_DUMPLOADSEARCH.
   If initialized:
   If Vinstallation_directory is not nil (ie, running uninstalled):
   If installation-dir/lisp exists and not already a member,
   we must be running uninstalled.  Reset the load-path
   to just installation-dir/lisp.  (The default PATH_LOADSEARCH
   refers to the eventual installation directories.  Since we
   are not yet installed, we should not use them, even if they exist.)
   If installation-dir/lisp does not exist, just add
   PATH_DUMPLOADSEARCH at the end instead.
   Add installation-dir/site-lisp (if !no_site_lisp, and exists
   and not already a member) at the front.
   If installation-dir != source-dir (ie running an uninstalled,
   out-of-tree build) AND install-dir/src/Makefile exists BUT
   install-dir/src/Makefile.in does NOT exist (this is a sanity
   check), then repeat the above steps for source-dir/lisp, site-lisp.  */

static Lisp_Object
load_path_default (void)
{
  Lisp_Object lpath = Qnil;
  bool initialized_or_cannot_dump = false;

  lpath = decode_env_path (0, PATH_DUMPLOADSEARCH, 0);

  if (initialized_or_cannot_dump)
    {
      Lisp_Object tem, tem1;

      /* Add to the path the lisp subdir of the installation
         dir, if it is accessible.  Note: in out-of-tree builds,
         this directory is empty save for Makefile.  */
      tem = Fexpand_file_name (build_string ("lisp"),
                               Vinstallation_directory);
      tem1 = Ffile_accessible_directory_p (tem);
      if (!NILP (tem1))
        {
          if (NILP (Fmember (tem, lpath)))
            {
              /* We are running uninstalled.  The default load-path
                 points to the eventual installed lisp directories.
                 We should not use those now, even if they exist,
                 so start over from a clean slate.  */
              lpath = list1 (tem);
            }
        }
      else
        /* That dir doesn't exist, so add the build-time
           Lisp dirs instead.  */
        {
          Lisp_Object dump_path =
            decode_env_path (0, PATH_DUMPLOADSEARCH, 0);
          lpath = nconc2 (lpath, dump_path);
        }

      /* Add site-lisp under the installation dir, if it exists.  */
      if (!no_site_lisp)
        {
          tem = Fexpand_file_name (build_string ("site-lisp"),
                                   Vinstallation_directory);
          tem1 = Ffile_accessible_directory_p (tem);
          if (!NILP (tem1))
            {
              if (NILP (Fmember (tem, lpath)))
                lpath = Fcons (tem, lpath);
            }
        }

      /* If Emacs was not built in the source directory,
         and it is run from where it was built, add to load-path
         the lisp and site-lisp dirs under that directory.  */

      if (NILP (Fequal (Vinstallation_directory, Vsource_directory)))
        {
          Lisp_Object tem2;

          tem = Fexpand_file_name (build_string ("src/Makefile"),
                                   Vinstallation_directory);
          tem1 = Ffile_exists_p (tem);

          /* Don't be fooled if they moved the entire source tree
             AFTER dumping Emacs.  If the build directory is indeed
             different from the source dir, src/Makefile.in and
             src/Makefile will not be found together.  */
          tem = Fexpand_file_name (build_string ("src/Makefile.in"),
                                   Vinstallation_directory);
          tem2 = Ffile_exists_p (tem);
          if (!NILP (tem1) && NILP (tem2))
            {
              tem = Fexpand_file_name (build_string ("lisp"),
                                       Vsource_directory);

              if (NILP (Fmember (tem, lpath)))
                lpath = Fcons (tem, lpath);

              if (!no_site_lisp)
                {
                  tem = Fexpand_file_name (build_string ("site-lisp"),
                                           Vsource_directory);
                  tem1 = Ffile_accessible_directory_p (tem);
                  if (!NILP (tem1))
                    {
                      if (NILP (Fmember (tem, lpath)))
                        lpath = Fcons (tem, lpath);
                    }
                }
            }
        } /* Vinstallation_directory != Vsource_directory */

    } /* if Vinstallation_directory */

  return lpath;
}

void
init_lread (void)
{
  /* Set Vsource_directory before calling load_path_default.  */
  Vsource_directory
    = Fexpand_file_name (build_string ("../"),
			 Fcar (decode_env_path (0, PATH_DUMPLOADSEARCH, 0)));

  /* First, set Vload_path.  */

  bool use_loadpath = true;

  if (use_loadpath && egetenv ("EMACSLOADPATH"))
    {
      Vload_path = decode_env_path ("EMACSLOADPATH", 0, 1);

      /* Check (non-nil) user-supplied elements.  */
      load_path_check (Vload_path);

      /* If no nils in the environment variable, use as-is.
         Otherwise, replace any nils with the default.  */
      if (! NILP (Fmemq (Qnil, Vload_path)))
        {
          Lisp_Object elem, elpath = Vload_path;
          Lisp_Object default_lpath = load_path_default ();

          /* Check defaults, before adding site-lisp.  */
          load_path_check (default_lpath);

          /* Add the site-lisp directories to the front of the default.  */
          if (!no_site_lisp && PATH_SITELOADSEARCH[0] != '\0')
            {
              Lisp_Object sitelisp;
              sitelisp = decode_env_path (0, PATH_SITELOADSEARCH, 0);
              if (! NILP (sitelisp))
                default_lpath = nconc2 (sitelisp, default_lpath);
            }

          Vload_path = Qnil;

          /* Replace nils from EMACSLOADPATH by default.  */
          while (CONSP (elpath))
            {
              elem = XCAR (elpath);
              elpath = XCDR (elpath);
              Vload_path = CALLN (Fappend, Vload_path,
				  NILP (elem) ? default_lpath : list1 (elem));
            }
        }                       /* Fmemq (Qnil, Vload_path) */
    }
  else
    {
      Vload_path = load_path_default ();

      /* Check before adding site-lisp directories.
         The install should have created them, but they are not
         required, so no need to warn if they are absent.
         Or we might be running before installation.  */
      load_path_check (Vload_path);

      /* Add the site-lisp directories at the front.  */
      if (!no_site_lisp && PATH_SITELOADSEARCH[0] != '\0')
        {
          Lisp_Object sitelisp;
          sitelisp = decode_env_path (0, PATH_SITELOADSEARCH, 0);
          if (! NILP (sitelisp)) Vload_path = nconc2 (sitelisp, Vload_path);
        }
    }

  Vvalues = Qnil;

  load_in_progress = 0;
  Vload_file_name = Qnil;
  Vload_true_file_name = Qnil;
  Vstandard_input = Qt;
  Vloads_in_progress = Qnil;
}

/* Print a warning that directory intended for use USE and with name
   DIRNAME cannot be accessed.  On entry, errno should correspond to
   the access failure.  Print the warning on stderr and put it in
   *Messages*.  */

void
dir_warning (char const *use, Lisp_Object dirname)
{
  static char const format[] = "Warning: %s '%s': %s\n";
  char *diagnostic = emacs_strerror (errno);
  fprintf (stderr, format, use, SSDATA (ENCODE_SYSTEM (dirname)), diagnostic);

  /* Don't log the warning before we've initialized!!  */
  if (initialized)
    {
      ptrdiff_t diaglen = strlen (diagnostic);
      AUTO_STRING_WITH_LEN (diag, diagnostic, diaglen);
      if (! NILP (Vlocale_coding_system))
	{
	  Lisp_Object s
	    = code_convert_string_norecord (diag, Vlocale_coding_system, false);
	  diagnostic = SSDATA (s);
	  diaglen = SBYTES (s);
	}
      USE_SAFE_ALLOCA;
      char *buffer = SAFE_ALLOCA (sizeof format - 3 * (sizeof "%s" - 1)
				  + strlen (use) + SBYTES (dirname) + diaglen);
      ptrdiff_t message_len = esprintf (buffer, format, use, SSDATA (dirname),
					diagnostic);
      message_dolog (buffer, message_len, 0);
      SAFE_FREE ();
    }
}

void
syms_of_lread (void)
{
#include "lread.x"

  DEFVAR_LISP ("obarray", Vobarray,
	       doc: /* Symbol table for use by `intern' and `read'.
It is a vector whose length ought to be prime for best results.
The vector's contents don't make sense if examined from Lisp programs;
to find all the symbols in an obarray, use `mapatoms'.  */);

  DEFVAR_LISP ("values", Vvalues,
	       doc: /* List of values of all expressions which were read, evaluated and printed.
Order is reverse chronological.
This variable is obsolete as of Emacs 28.1 and should not be used.  */);
  SET_SYMBOL_DECLARED_SPECIAL (XSYMBOL (intern ("values")), false);

  DEFVAR_LISP ("standard-input", Vstandard_input,
	       doc: /* Stream for read to get input from.
See documentation of `read' for possible values.  */);
  Vstandard_input = Qt;

  DEFVAR_LISP ("read-circle", Vread_circle,
	       doc: /* Non-nil means read recursive structures using #N= and #N# syntax.  */);
  Vread_circle = Qt;

  DEFVAR_LISP ("load-path", Vload_path,
	       doc: /* List of directories to search for files to load.
Each element is a string (directory file name) or nil (meaning
`default-directory').
This list is consulted by the `require' function.
Initialized during startup as described in Info node `(elisp)Library Search'.
Use `directory-file-name' when adding items to this path.  However, Lisp
programs that process this list should tolerate directories both with
and without trailing slashes.  */);

  DEFVAR_LISP ("load-suffixes", Vload_suffixes,
	       doc: /* List of suffixes for Emacs Lisp files and dynamic modules.
This list includes suffixes for both compiled and source Emacs Lisp files.
This list should not include the empty string.
`load' and related functions try to append these suffixes, in order,
to the specified file name if a suffix is allowed or required.  */);
  Vload_suffixes = list1 (build_pure_c_string (".el"));
#ifdef HAVE_MODULES
  Vload_suffixes = Fcons (build_pure_c_string (MODULES_SUFFIX), Vload_suffixes);
#ifdef MODULES_SECONDARY_SUFFIX
  Vload_suffixes =
    Fcons (build_pure_c_string (MODULES_SECONDARY_SUFFIX), Vload_suffixes);
#endif
#endif
  DEFVAR_LISP ("module-file-suffix", Vmodule_file_suffix,
	       doc: /* Suffix of loadable module file, or nil if modules are not supported.  */);
#ifdef HAVE_MODULES
  Vmodule_file_suffix = build_pure_c_string (MODULES_SUFFIX);
#else
  Vmodule_file_suffix = Qnil;
#endif

  DEFVAR_LISP ("dynamic-library-suffixes", Vdynamic_library_suffixes,
	       doc: /* A list of suffixes for loadable dynamic libraries.  */);

#ifndef MSDOS
  Vdynamic_library_suffixes
    = Fcons (build_pure_c_string (DYNAMIC_LIB_SECONDARY_SUFFIX), Qnil);
  Vdynamic_library_suffixes
    = Fcons (build_pure_c_string (DYNAMIC_LIB_SUFFIX),
	     Vdynamic_library_suffixes);
#else
  Vdynamic_library_suffixes = Qnil;
#endif

  DEFVAR_LISP ("load-file-rep-suffixes", Vload_file_rep_suffixes,
	       doc: /* List of suffixes that indicate representations of
the same file.
This list should normally start with the empty string.

Enabling Auto Compression mode appends the suffixes in
`jka-compr-load-suffixes' to this list and disabling Auto Compression
mode removes them again.  `load' and related functions use this list to
determine whether they should look for compressed versions of a file
and, if so, which suffixes they should try to append to the file name
in order to do so.  However, if you want to customize which suffixes
the loading functions recognize as compression suffixes, you should
customize `jka-compr-load-suffixes' rather than the present variable.  */);
  Vload_file_rep_suffixes = list1 (build_string(""));

  DEFVAR_BOOL ("load-in-progress", load_in_progress,
	       doc: /* Non-nil if inside of `load'.  */);
  DEFSYM (Qload_in_progress, "load-in-progress");

  DEFVAR_LISP ("after-load-alist", Vafter_load_alist,
	       doc: /* An alist of functions to be evalled when particular files are loaded.
Each element looks like (REGEXP-OR-FEATURE FUNCS...).

REGEXP-OR-FEATURE is either a regular expression to match file names, or
a symbol (a feature name).

When `load' is run and the file-name argument matches an element's
REGEXP-OR-FEATURE, or when `provide' is run and provides the symbol
REGEXP-OR-FEATURE, the FUNCS in the element are called.

An error in FUNCS does not undo the load, but does prevent calling
the rest of the FUNCS.  */);
  Vafter_load_alist = Qnil;

  DEFVAR_LISP ("load-history", Vload_history,
	       doc: /* Alist mapping loaded file names to symbols and features.
Each alist element should be a list (FILE-NAME ENTRIES...), where
FILE-NAME is the name of a file that has been loaded into Emacs.
The file name is absolute and true (i.e. it doesn't contain symlinks).
As an exception, one of the alist elements may have FILE-NAME nil,
for symbols and features not associated with any file.

The remaining ENTRIES in the alist element describe the functions and
variables defined in that file, the features provided, and the
features required.  Each entry has the form `(provide . FEATURE)',
`(require . FEATURE)', `(defun . FUNCTION)', `(defface . SYMBOL)',
 `(define-type . SYMBOL)', or `(cl-defmethod METHOD SPECIALIZERS)'.
In addition, entries may also be single symbols,
which means that symbol was defined by `defvar' or `defconst'.

During preloading, the file name recorded is relative to the main Lisp
directory.  These file names are converted to absolute at startup.  */);
  Vload_history = Qnil;

  DEFVAR_LISP ("load-file-name", Vload_file_name,
	       doc: /* Full name of file being loaded by `load'.

In case of native code being loaded this is indicating the
corresponding bytecode filename.  Use `load-true-file-name' to obtain
the .eln filename.  */);
  Vload_file_name = Qnil;

  DEFVAR_LISP ("load-true-file-name", Vload_true_file_name,
	       doc: /* Full name of file being loaded by `load'.  */);
  Vload_true_file_name = Qnil;

  DEFVAR_LISP ("user-init-file", Vuser_init_file,
	       doc: /* File name, including directory, of user's initialization file.
If the file loaded had extension `.elc', and the corresponding source file
exists, this variable contains the name of source file, suitable for use
by functions like `custom-save-all' which edit the init file.
While Emacs loads and evaluates any init file, value is the real name
of the file, regardless of whether or not it has the `.elc' extension.  */);
  Vuser_init_file = Qnil;

  DEFVAR_LISP ("current-load-list", Vcurrent_load_list,
	       doc: /* Used for internal purposes by `load'.  */);
  Vcurrent_load_list = Qnil;

  DEFVAR_LISP ("load-read-function", Vload_read_function,
	       doc: /* Function used for reading expressions.
It is used by `load' and `eval-region'.

Called with a single argument (the stream from which to read).
The default is to use the function `read'.  */);
  DEFSYM (Qread, "read");
  Vload_read_function = Qread;

  DEFVAR_LISP ("load-source-file-function", Vload_source_file_function,
	       doc: /* Function called in `load' to load an Emacs Lisp source file.
The value should be a function for doing code conversion before
reading a source file.  It can also be nil, in which case loading is
done without any code conversion.

If the value is a function, it is called with four arguments,
FULLNAME, FILE, NOERROR, NOMESSAGE.  FULLNAME is the absolute name of
the file to load, FILE is the non-absolute name (for messages etc.),
and NOERROR and NOMESSAGE are the corresponding arguments passed to
`load'.  The function should return t if the file was loaded.  */);
  Vload_source_file_function = Qnil;

  DEFVAR_LISP ("source-directory", Vsource_directory,
	       doc: /* Directory in which Emacs sources were found when Emacs was built.
You cannot count on them to still be there!  */);

  DEFVAR_LISP ("preloaded-file-list", Vpreloaded_file_list,
	       doc: /* List of files that were preloaded (when dumping Emacs).  */);
  Vpreloaded_file_list = Qnil;

  DEFVAR_LISP ("byte-boolean-vars", Vbyte_boolean_vars,
	       doc: /* List of all DEFVAR_BOOL variables, used by the byte code optimizer.  */);
  Vbyte_boolean_vars = Qnil;

  DEFVAR_BOOL ("load-dangerous-libraries", load_dangerous_libraries,
	       doc: /* Non-nil means load dangerous compiled Lisp files.
Some versions of XEmacs use different byte codes than Emacs.  These
incompatible byte codes can make Emacs crash when it tries to execute
them.  */);
  load_dangerous_libraries = 0;

  DEFVAR_BOOL ("force-load-messages", force_load_messages,
	       doc: /* Non-nil means force printing messages when loading Lisp files.
This overrides the value of the NOMESSAGE argument to `load'.  */);
  force_load_messages = 0;

  DEFVAR_LISP ("bytecomp-version-regexp", Vbytecomp_version_regexp,
	       doc: /* Regular expression matching safe to load compiled Lisp files.
When Emacs loads a compiled Lisp file, it reads the first 512 bytes
from the file, and matches them against this regular expression.
When the regular expression matches, the file is considered to be safe
to load.  */);
  Vbytecomp_version_regexp
    = build_pure_c_string
        ("^;;;.\\(?:in Emacs version\\|bytecomp version FSF\\)");

  DEFSYM (Qlexical_binding, "lexical-binding");
  DEFVAR_LISP ("lexical-binding", Vlexical_binding,
	       doc: /* Whether to use lexical binding when evaluating code.
Non-nil means that the code in the current buffer should be evaluated
with lexical binding.
This variable is automatically set from the file variables of an
interpreted Lisp file read using `load'.  Unlike other file local
variables, this must be set in the first line of a file.  */);
  Vlexical_binding = Qnil;
  Fmake_variable_buffer_local (Qlexical_binding);

  DEFVAR_LISP ("eval-buffer-list", Veval_buffer_list,
	       doc: /* List of buffers being read from by calls to `eval-buffer' and `eval-region'.  */);
  Veval_buffer_list = Qnil;


  DEFVAR_BOOL ("load-prefer-newer", load_prefer_newer,
               doc: /* Non-nil means `load' prefers the newest version of a file.
This applies when a filename suffix is not explicitly specified and
`load' is trying various possible suffixes (see `load-suffixes' and
`load-file-rep-suffixes').  Normally, it stops at the first file
that exists unless you explicitly specify one or the other.  If this
option is non-nil, it checks all suffixes and uses whichever file is
newest.
Note that if you customize this, obviously it will not affect files
that are loaded before your customizations are read!  */);
  load_prefer_newer = 1;

  DEFVAR_BOOL ("load-no-native", load_no_native,
               doc: /* Non-nil means not to load native code unless explicitly requested.

To load a `.eln' file when this variable is non-nil, use `(load FILE)'
where FILE is the filename of the eln file, including the .eln extension.
`load-no-native' non-nil will also make Emacs not load native code
through `require'.  */);
  load_no_native = false;

  /* Vsource_directory was initialized in init_lread.  */

  DEFSYM (Qcurrent_load_list, "current-load-list");
  DEFSYM (Qstandard_input, "standard-input");
  DEFSYM (Qread_char, "read-char");
  DEFSYM (Qget_file_char, "get-file-char");
  DEFSYM (Qbackquote, "`");
  DEFSYM (Qcomma, ",");
  DEFSYM (Qcomma_at, ",@");

#if !IEEE_FLOATING_POINT
  for (int negative = 0; negative < 2; negative++)
    {
      not_a_number[negative] = build_pure_c_string (&"-0.0e+NaN"[!negative]);
      staticpro (&not_a_number[negative]);
    }
#endif

  DEFSYM (Qinhibit_file_name_operation, "inhibit-file-name-operation");
  DEFSYM (Qascii_character, "ascii-character");
  DEFSYM (Qfunction, "function");
  DEFSYM (Qload, "load");
  DEFSYM (Qload_file_name, "load-file-name");
  DEFSYM (Qload_true_file_name, "load-true-file-name");
  DEFSYM (Qeval_buffer_list, "eval-buffer-list");
  DEFSYM (Qdir_ok, "dir-ok");
  DEFSYM (Qdo_after_load_evaluation, "do-after-load-evaluation");

  staticpro (&read_objects_map);
  read_objects_map = Qnil;
  staticpro (&read_objects_completed);
  read_objects_completed = Qnil;

  Vloads_in_progress = Qnil;
  staticpro (&Vloads_in_progress);

  DEFSYM (Qhash_table, "hash-table");
  DEFSYM (Qdata, "data");
  DEFSYM (Qtest, "test");
  DEFSYM (Qsize, "size");
  DEFSYM (Qpurecopy, "purecopy");
  DEFSYM (Qweakness, "weakness");

  DEFSYM (Qchar_from_name, "char-from-name");

  DEFVAR_LISP ("read-symbol-shorthands", Vread_symbol_shorthands,
          doc: /* Alist of known symbol-name shorthands.
This variable's value can only be set via file-local variables.
See Info node `(elisp)Shorthands' for more details.  */);
  Vread_symbol_shorthands = Qnil;
  DEFSYM (Qobarray_cache, "obarray-cache");
  DEFSYM (Qobarrayp, "obarrayp");

  DEFSYM (Qmacroexp__dynvars, "macroexp--dynvars");
  DEFVAR_LISP ("macroexp--dynvars", Vmacroexp__dynvars,
        doc:   /* List of variables declared dynamic in the current scope.
Only valid during macro-expansion.  Internal use only. */);
  Vmacroexp__dynvars = Qnil;

  DEFSYM (Qinternal_macroexpand_for_load,
	  "internal-macroexpand-for-load");
  DEFSYM (Qread_minibuffer, "read-minibuffer");

  /* Unified Reader Architecture - Main unified reader function
     Currently dispatches to existing functions for gradual migration.
     Ready for full implementation to eliminate 1,200+ lines of duplicated parsing logic. */
  /* Note: Implementation added as static function before syms_of_lread */
}
