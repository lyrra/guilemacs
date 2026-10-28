/* Terminal control module for terminals described by TERMCAP
   Copyright (C) 1985-1987, 1993-1995, 1998, 2000-2025 Free Software
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

/* New redisplay, TTY faces by Gerd Moellmann <gerd@gnu.org>.  */

#include <config.h>
#include <errno.h>
#include <fcntl.h>
#include <stdlib.h>
#include <sys/file.h>
#include <sys/time.h>
#include <unistd.h>

#include "lisp.h"
#include "termchar.h"
#include "tparam.h"
#include "character.h"
#include "buffer.h"
#include "charset.h"
#include "coding.h"
#include "composite.h"
#include "keyboard.h"
#include "frame.h"
#include "disptab.h"
#include "termhooks.h"
#include "dispextern.h"
#include "window.h"
#include "keymap.h"
#include "blockinput.h"
#include "syssignal.h"
#include "sysstdio.h"
#include "guile.h"
#ifdef MSDOS
#include "msdos.h"
static int been_here = -1;
#endif

#ifdef USE_X_TOOLKIT
#include "../lwlib/lwlib.h"
#endif

#include "cm.h"
#include "menu.h"

/* The name of the default console device.  */
#ifdef WINDOWSNT
#include "w32term.h"
#endif

#ifndef HAVE_ANDROID

static void tty_set_scroll_region (struct frame *f, int start, int stop);
static void turn_on_face (struct frame *f, struct face *face);
static void turn_off_face (struct frame *f, struct face *face);
static void tty_turn_off_highlight (struct tty_display_info *);
static void tty_background_highlight (struct tty_display_info *tty);
/* M52 imp-5: the bell / cursor / update-end dispatchers.  tty_ring_bell
   and tty_update_end sit above the imp-4 forward-declaration block, so
   their dispatchers (and the m52_cap_string_1 prototype they resolve
   their key with) must be declared here, before the hubs.  The m52_ /
   _scheme name reuses no static helper (docs/kb.org
   =term-hub-helper-name-collision=).  */
static Lisp_Object m52_tty_ring_bell_scheme (Lisp_Object, Lisp_Object);
static Lisp_Object m52_tty_hide_cursor_scheme (Lisp_Object);
static Lisp_Object m52_tty_show_cursor_scheme (Lisp_Object, Lisp_Object);
static Lisp_Object m52_tty_background_highlight_scheme (Lisp_Object);
static Lisp_Object m52_tty_highlight_if_desired_scheme (Lisp_Object);
static Lisp_Object m52_tty_update_end_scheme (Lisp_Object);
static Lisp_Object m52_tty_set_terminal_modes_scheme (Lisp_Object, Lisp_Object,
						      Lisp_Object);
static Lisp_Object m52_tty_reset_terminal_modes_scheme (void);
static Lisp_Object m52_tty_cursor_to_scheme (Lisp_Object, Lisp_Object, Lisp_Object,
					     Lisp_Object, Lisp_Object, Lisp_Object);
static Lisp_Object m52_tty_raw_cursor_to_scheme (Lisp_Object, Lisp_Object,
						 Lisp_Object, Lisp_Object,
						 Lisp_Object, Lisp_Object);
static Lisp_Object m52_tty_clear_to_end_scheme (Lisp_Object);
static Lisp_Object m52_tty_clear_frame_scheme (Lisp_Object);
static Lisp_Object m52_tty_clear_end_of_line_scheme (Lisp_Object, Lisp_Object,
						     Lisp_Object, Lisp_Object);
static Lisp_Object m52_tty_set_terminal_window_scheme (Lisp_Object, Lisp_Object,
						       Lisp_Object);
static Lisp_Object m52_tty_set_scroll_region_scheme (Lisp_Object, Lisp_Object,
						     Lisp_Object, Lisp_Object,
						     Lisp_Object, Lisp_Object,
						     Lisp_Object);
static Lisp_Object m52_tty_delete_glyphs_scheme (Lisp_Object, Lisp_Object,
						 Lisp_Object);
static Lisp_Object m52_tty_ins_del_lines_scheme (Lisp_Object, Lisp_Object,
						 Lisp_Object, Lisp_Object,
						 Lisp_Object, Lisp_Object,
						 Lisp_Object, Lisp_Object,
						 Lisp_Object);
static bool m52_tty_step_args_1 (Lisp_Object, int *, int);
static bool m52_tty_step_tag_p (Lisp_Object, const char *);
static const char *m52_cap_string_1 (struct tty_display_info *, Lisp_Object);
/* M54 imp-4: the input stream TAB policy dispatcher.  The call site
   (init_tty, src/term.c :5030) sits above the M54 imp-2 / imp-3
   dispatcher block, so the prototype must be declared here, before the
   call site.  The m54_tty_tabs_ name reuses no static helper
   (docs/kb.org =term-hub-helper-name-collision=).  */
static Lisp_Object m54_tty_tabs_verdict_scheme (Lisp_Object, Lisp_Object);
/* M58 imp-4: the Group B color-mode DECISION dispatchers.  The call
   sites (tty_setup_colors, set_tty_color_mode) come later in this
   file, so the prototypes are declared here.  The m58_tty_color_
   names reuse no static helper (docs/kb.org
   =term-hub-helper-name-collision=).  */
static Lisp_Object m58_tty_color_mode_tag_scheme (Lisp_Object);
static Lisp_Object m58_tty_color_mode_changed_scheme (Lisp_Object,
						      Lisp_Object);
static void clear_tty_hooks (struct terminal *terminal);
static void set_tty_hooks (struct terminal *terminal);
static void dissociate_if_controlling_tty (int fd);
static void delete_tty (struct terminal *);

#endif /* !HAVE_ANDROID */

static AVOID maybe_fatal (bool, struct terminal *, const char *, const char *,
			  ...)
  ATTRIBUTE_FORMAT_PRINTF (3, 5) ATTRIBUTE_FORMAT_PRINTF (4, 5);
static AVOID vfatal (const char *, va_list) ATTRIBUTE_FORMAT_PRINTF (1, 0);

#ifndef HAVE_ANDROID

#define OUTPUT(tty, a)                                          \
  emacs_tputs (tty, a,                                        \
               FRAME_TOTAL_LINES (XFRAME (selected_frame)) - curY (tty),	\
               cmputc)

#define OUTPUT1(tty, a) emacs_tputs (tty, a, 1, cmputc)
#define OUTPUTL(tty, a, lines) emacs_tputs (tty, a, lines, cmputc)

#define OUTPUT_IF(tty, a)                                               \
  do {                                                                  \
    if (a)                                                              \
      OUTPUT (tty, a);							\
  } while (0)

#define OUTPUT1_IF(tty, a) \
  do { if (a) emacs_tputs (tty, a, 1, cmputc); } while (0)

#endif

/* Display space properties.  */

/* Chain of all tty device parameters.  */
struct tty_display_info *tty_list;

/* Meaning of bits in no_color_video.  Each bit set means that the
   corresponding attribute cannot be combined with colors.  */

enum no_color_bit
{
  NC_STANDOUT		 = 1 << 0,
  NC_UNDERLINE		 = 1 << 1,
  NC_REVERSE		 = 1 << 2,
  NC_ITALIC		 = 1 << 3,
  NC_DIM		 = 1 << 4,
  NC_BOLD		 = 1 << 5,
  NC_STRIKE_THROUGH	 = 1 << 6,
  NC_PROTECT		 = 1 << 7
};

/* internal state */

#ifndef HAVE_ANDROID

/* The largest frame width in any call to calculate_costs.  */

static int max_frame_cols;

#endif



#ifdef HAVE_GPM
#include <sys/fcntl.h>

/* The device for which we have enabled gpm support (or NULL).  */
struct tty_display_info *gpm_tty = NULL;

/* Last recorded mouse coordinates.  */
static Lisp_Object last_mouse_frame;
static int last_mouse_x, last_mouse_y;
#endif /* HAVE_GPM */

/* The M61 imp-2 ordered-path hubs of the normal glyph path.  The bell,
   the terminal modes and tty_update_end flush the output stream far above
   the M61 block of this file, so the hub must be declared here.  The
   definitions are in that block; section 3 of milestone.org gives the
   order contract.  */
static ptrdiff_t m61_tty_handle_flush_1 (struct tty_display_info *);

#ifndef HAVE_ANDROID

/* Ring the bell on a tty. */

static void
tty_ring_bell (struct frame *f)
{
  struct tty_display_info *tty = FRAME_TTY (f);

  if (tty->output)
    {
      /* The bell selection runs in Scheme: the returned KEY is either
         "visible-bell" or "bell".  C resolves the key and keeps the
         OUTPUT call and the fflush.  */
      Lisp_Object key
        = m52_tty_ring_bell_scheme (make_fixnum (visible_bell),
                                    make_fixnum (tty->TS_visible_bell != NULL));
      if (!NILP (key))
        OUTPUT (tty, m52_cap_string_1 (tty, key));
      /* M61 imp-2: Scheme checks that the handle is open; C keeps the
         fflush and its position.  */
      (void) m61_tty_handle_flush_1 (tty);
    }
}

/* Set up termcap modes for Emacs. */

static void
tty_send_additional_strings (struct terminal *terminal, Lisp_Object sym)
{
  /* Use only accessors like CDR_SAFE and assq_no_quit to avoid any
     form of quitting or signaling an error, since this function can
     run as part of the "emergency escape" procedure invoked in the
     middle of GC, where quitting means crashing (Bug#17406).  */
  if (! terminal->name)
    return;
  struct tty_display_info *tty = terminal->display_info.tty;

  for (Lisp_Object extra_codes
	 = CDR_SAFE (assq_no_quit (sym, terminal->param_alist));
       CONSP (extra_codes);
       extra_codes = XCDR (extra_codes))
    {
      Lisp_Object string = XCAR (extra_codes);
      if (STRINGP (string))
        {
	  fwrite (SDATA (string), 1, SBYTES (string), tty->output);
          if (tty->termscript)
	    fwrite (SDATA (string), 1, SBYTES (string), tty->termscript);
        }
    }
}

static void
tty_set_terminal_modes (struct terminal *terminal)
{
  struct tty_display_info *tty = terminal->display_info.tty;

  if (tty->output)
    {
      /* The setup step selection runs in Scheme: the returned list holds
	 the ordered steps.  A KEY step is a plain string; the "newlines"
	 marker is a plain list.  C routes each step to its mechanism,
	 keeps the output stream, and keeps the fflush.  */
      /* Read the frame line count only when the newline fallback runs,
	 as the original C did, so the termcap-modes branch never reads
	 the count explicitly; OUTPUT_IF still computes it for padding.  */
      Lisp_Object steps
	= m52_tty_set_terminal_modes_scheme
	    (make_fixnum (tty->TS_termcap_modes != NULL),
	     make_fixnum (tty->TS_termcap_modes
			  ? 0 : FRAME_TOTAL_LINES (XFRAME (selected_frame))),
	     make_fixnum (visible_cursor));
      for (; CONSP (steps); steps = XCDR (steps))
	{
	  Lisp_Object step = XCAR (steps);
	  if (STRINGP (step))
	    OUTPUT_IF (tty, m52_cap_string_1 (tty, step));
	  else if (m52_tty_step_tag_p (step, "newlines"))
	    {
	      /* Output enough newlines to scroll all the old screen
		 contents off the screen, so it won't be overwritten and
		 lost.  */
	      EMACS_INT i, n = XFIXNUM (XCAR (XCDR (step)));
	      current_tty = tty;
	      for (i = 0; i < n; i++)
		cmputc ('\n');
	    }
	}
      losecursor (tty);
      tty_send_additional_strings (terminal, Qtty_mode_set_strings);
      /* M61 imp-2: Scheme checks that the handle is open; C keeps the
         fflush and its position.  */
      (void) m61_tty_handle_flush_1 (tty);
    }
}

/* Reset termcap modes before exiting Emacs. */

static void
tty_reset_terminal_modes (struct terminal *terminal)
{
  struct tty_display_info *tty = terminal->display_info.tty;

  if (tty->output)
    {
      tty_send_additional_strings (terminal, Qtty_mode_reset_strings);
      tty_turn_off_highlight (tty);
      tty_turn_off_insert (tty);
      /* The fixed reset steps run in Scheme: the returned list holds the
	 4 KEY steps and the "raw-cr" marker.  C routes each step to its
	 mechanism and keeps the output stream and the fflush.  */
      Lisp_Object steps = m52_tty_reset_terminal_modes_scheme ();
      for (; CONSP (steps); steps = XCDR (steps))
	{
	  Lisp_Object step = XCAR (steps);
	  if (STRINGP (step))
	    OUTPUT_IF (tty, m52_cap_string_1 (tty, step));
	  else if (m52_tty_step_tag_p (step, "raw-cr"))
	    {
	      /* Output raw CR so kernel can track the cursor hpos.  */
	      current_tty = tty;
	      cmputc ('\r');
	    }
	}
      /* M61 imp-2: Scheme checks that the handle is open; C keeps the
         fflush and its position.  */
      (void) m61_tty_handle_flush_1 (tty);
    }
}

/* Flag the end of a display update on a termcap terminal. */

static void
tty_update_end (struct frame *f)
{
  struct tty_display_info *tty = FRAME_TTY (f);

  /* The step selection runs in Scheme: the returned list holds the
     ordered step tags.  C routes each step to its hub and keeps the
     fflush.  The plain cursor_off_p boolean crosses the layer, never
     the window.  */
  Lisp_Object steps
    = m52_tty_update_end_scheme (make_fixnum (XWINDOW (selected_window)->cursor_off_p));
  for (; CONSP (steps); steps = XCDR (steps))
    {
      Lisp_Object s = XCAR (steps);
      if (scm_is_true (scm_string_equal_p (s, scm_from_utf8_string ("show-cursor"))))
        tty_show_cursor (tty);
      else if (scm_is_true (scm_string_equal_p (s, scm_from_utf8_string ("off-insert"))))
        tty_turn_off_insert (tty);
      else if (scm_is_true (scm_string_equal_p (s, scm_from_utf8_string ("background"))))
        tty_background_highlight (tty);
    }
  /* M61 imp-2: Scheme checks that the handle is open; C keeps the
     fflush and its position.  */
  (void) m61_tty_handle_flush_1 (tty);
}

/* The implementation of set_terminal_window for termcap frames. */

static void
tty_set_terminal_window (struct frame *f, int size)
{
  struct tty_display_info *tty = FRAME_TTY (f);
  int a[4];
  Lisp_Object steps
    = m52_tty_set_terminal_window_scheme (make_fixnum (size),
					  make_fixnum (FRAME_TOTAL_LINES (f)),
					  make_fixnum (FRAME_SCROLL_REGION_OK (f) != 0));
  /* M52 imp-8: the height and the scroll-region choice run in Scheme.
     A MARKER "set-window" HERE means "write tty->specified_window = w";
     it is NOT the "set-window" capability key.  C keeps the state
     write and the tty_set_scroll_region call.  */
  for (; CONSP (steps); steps = XCDR (steps))
    {
      Lisp_Object s = XCAR (steps);
      a[0] = a[1] = a[2] = a[3] = 0;
      if (m52_tty_step_tag_p (s, "set-window"))
	{
	  m52_tty_step_args_1 (s, a, 1);
	  tty->specified_window = a[0];   /* C keeps the state write */
	}
      else if (m52_tty_step_tag_p (s, "scroll-region"))
	{
	  m52_tty_step_args_1 (s, a, 2);
	  tty_set_scroll_region (f, a[0], a[1]);  /* keep this C call */
	}
    }
}

static void
tty_set_scroll_region (struct frame *f, int start, int stop)
{
  char *buf;
  struct tty_display_info *tty = FRAME_TTY (f);
  int a[4];
  const char *str;
  Lisp_Object step
    = m52_tty_set_scroll_region_scheme (make_fixnum (start), make_fixnum (stop),
					make_fixnum (FRAME_TOTAL_LINES (f)),
					make_fixnum (FRAME_COLS (f)),
					make_fixnum (tty->TS_set_scroll_region != NULL),
					make_fixnum (tty->TS_set_scroll_region_1 != NULL),
					make_fixnum (tty->TS_set_window != NULL));
  /* M52 imp-8: the form choice runs in Scheme.  The MARKER carries the
     tparam args; a trailing arg that the form does not use stays 0,
     because C zeroes A first.  C keeps tparam, OUTPUT, xfree, and
     losecursor.  */
  a[0] = a[1] = a[2] = a[3] = 0;
  if (m52_tty_step_tag_p (step, "scroll-region") && tty->TS_set_scroll_region)
    str = tty->TS_set_scroll_region;
  else if (m52_tty_step_tag_p (step, "scroll-region-1") && tty->TS_set_scroll_region_1)
    str = tty->TS_set_scroll_region_1;
  else if (m52_tty_step_tag_p (step, "set-window"))
    str = tty->TS_set_window;
  else
    /* Defensive fallback, not a new policy guard: the Scheme procedure
       returns only the 3 tags above, so this arm is dead today.  It
       keeps STR set, so an unexpected tag cannot reach tparam with an
       uninitialised STR, which is undefined behaviour.  Keep the line:
       it costs nothing and it keeps the guarantee in one place.  Do
       not remove it without a replacement.  */
    return;
  m52_tty_step_args_1 (step, a, 4);
  buf = tparam (str, 0, 0, a[0], a[1], a[2], a[3]);
  OUTPUT (tty, buf);
  xfree (buf);
  losecursor (tty);
}


/* M52 imp-4: the insert / highlight state-flip dispatchers.  They are
   defined with the imp-3 block (near the m52_caps table) and call the
   pure policy procedures of (emacs tty-output).  These forward
   declarations keep the hubs below independent of the definition
   order; the m52_cap_string_1 prototype lets the rewired hubs resolve
   the KEY before that imp-3 helper is defined.  The m52_ / _scheme name
   reuses no static helper (docs/kb.org
   =term-hub-helper-name-collision=).  */
static Lisp_Object m52_tty_turn_on_insert_scheme (Lisp_Object);
static Lisp_Object m52_tty_turn_off_insert_scheme (Lisp_Object);
static Lisp_Object m52_tty_turn_off_highlight_scheme (Lisp_Object);
static Lisp_Object m52_tty_turn_on_highlight_scheme (Lisp_Object);
static Lisp_Object m52_tty_toggle_highlight_scheme (Lisp_Object);
static const char *m52_cap_string_1 (struct tty_display_info *, Lisp_Object);

static void
tty_turn_on_insert (struct tty_display_info *tty)
{
  Lisp_Object key
    = m52_tty_turn_on_insert_scheme (make_fixnum (tty->insert_mode));
  if (!NILP (key))
    OUTPUT (tty, m52_cap_string_1 (tty, key));
  tty->insert_mode = 1;
}

void
tty_turn_off_insert (struct tty_display_info *tty)
{
  Lisp_Object key
    = m52_tty_turn_off_insert_scheme (make_fixnum (tty->insert_mode));
  if (!NILP (key))
    OUTPUT (tty, m52_cap_string_1 (tty, key));
  tty->insert_mode = 0;
}

/* Handle highlighting.  */

static void
tty_turn_off_highlight (struct tty_display_info *tty)
{
  Lisp_Object key
    = m52_tty_turn_off_highlight_scheme (make_fixnum (tty->standout_mode));
  if (!NILP (key))
    OUTPUT_IF (tty, m52_cap_string_1 (tty, key));
  tty->standout_mode = 0;
}

static void
tty_turn_on_highlight (struct tty_display_info *tty)
{
  Lisp_Object key
    = m52_tty_turn_on_highlight_scheme (make_fixnum (tty->standout_mode));
  if (!NILP (key))
    OUTPUT_IF (tty, m52_cap_string_1 (tty, key));
  tty->standout_mode = 1;
}

static void
tty_toggle_highlight (struct tty_display_info *tty)
{
  /* The direction decision runs in Scheme: the returned KEY is either
     the "on" key or the "off" key.  C routes on that key and keeps the
     two-way shape (one OUTPUT_IF and one state write per direction).  */
  Lisp_Object key
    = m52_tty_toggle_highlight_scheme (make_fixnum (tty->standout_mode));
  if (NILP (key))
    return;
  const char *cap = m52_cap_string_1 (tty, key);
  if (scm_is_true (scm_string_equal_p (key,
				       scm_from_utf8_string ("standout-mode"))))
    {
      OUTPUT_IF (tty, cap);
      tty->standout_mode = 1;
    }
  else
    {
      OUTPUT_IF (tty, cap);
      tty->standout_mode = 0;
    }
}


/* Make cursor invisible.  */

void
tty_hide_cursor (struct tty_display_info *tty)
{
#ifdef WINDOWSNT
  /* FIX-20261009-guilemacs: the MS-Windows console cursor arm is out of
     scope; it stays C.  */
  if (tty->cursor_hidden == 0)
    {
      tty->cursor_hidden = 1;
      w32con_hide_cursor ();
    }
#else
  /* The hide decision runs in Scheme: the returned list holds the
     "cursor-invisible" key, or nil when the cursor is already hidden.
     C tests the whole list, keeps the state write, and keeps the
     OUTPUT_IF call.  */
  Lisp_Object keys
    = m52_tty_hide_cursor_scheme (make_fixnum (tty->cursor_hidden));
  if (NILP (keys))
    return;
  tty->cursor_hidden = 1;
  for (; CONSP (keys); keys = XCDR (keys))
    OUTPUT_IF (tty, m52_cap_string_1 (tty, XCAR (keys)));
#endif
}


/* Ensure that cursor is visible.  */

void
tty_show_cursor (struct tty_display_info *tty)
{
#ifdef WINDOWSNT
  /* FIX-20261009-guilemacs: the MS-Windows console cursor arm is out of
     scope; it stays C.  */
  if (tty->cursor_hidden)
    {
      tty->cursor_hidden = 0;
      w32con_show_cursor ();
    }
#else
  /* The show decision runs in Scheme: the returned list holds
     "cursor-normal", and "cursor-visible" when visible_cursor is on,
     or nil when the cursor is already shown.  C tests the whole list,
     keeps the state write, and keeps each OUTPUT_IF call.  */
  Lisp_Object keys
    = m52_tty_show_cursor_scheme (make_fixnum (tty->cursor_hidden),
                                  make_fixnum (visible_cursor));
  if (NILP (keys))
    return;
  tty->cursor_hidden = 0;
  for (; CONSP (keys); keys = XCDR (keys))
    OUTPUT_IF (tty, m52_cap_string_1 (tty, XCAR (keys)));
#endif
}


/* Set standout mode to the state it should be in for
   empty space inside windows.  What this is,
   depends on the user option inverse-video.  */

static void
tty_background_highlight (struct tty_display_info *tty)
{
  /* The direction decision runs in Scheme: the returned KEY is either
     the "on" key or the "off" key.  C routes on that key and keeps the
     two-way call to the imp-4 hub.  */
  Lisp_Object key
    = m52_tty_background_highlight_scheme (make_fixnum (inverse_video));
  if (scm_is_true (scm_string_equal_p (key,
				       scm_from_utf8_string ("standout-mode"))))
    tty_turn_on_highlight (tty);
  else
    tty_turn_off_highlight (tty);
}

/* Set standout mode to the mode specified for the text to be output.  */

static void
tty_highlight_if_desired (struct tty_display_info *tty)
{
  /* The direction decision runs in Scheme: the returned KEY is either
     the "on" key or the "off" key.  C routes on that key and keeps the
     two-way call to the imp-4 hub.  */
  Lisp_Object key
    = m52_tty_highlight_if_desired_scheme (make_fixnum (inverse_video));
  if (scm_is_true (scm_string_equal_p (key,
				       scm_from_utf8_string ("standout-mode"))))
    tty_turn_on_highlight (tty);
  else
    tty_turn_off_highlight (tty);
}


/* Move cursor to row/column position VPOS/HPOS.  HPOS/VPOS are
   frame-relative coordinates.  */

static void
tty_cursor_to (struct frame *f, int vpos, int hpos)
{
  struct tty_display_info *tty = FRAME_TTY (f);

  /* Detect the case where we are called from reset_sys_modes
     and the costs have never been calculated.  Do nothing.  */
  if (! tty->costs_set)
    return;

  /* The move / no-move decision and the conditional resets run in
     Scheme: the returned list is nil on no move, else the ordered
     steps.  C routes each step to its mechanism and keeps the cmgoto.  */
  Lisp_Object steps
    = m52_tty_cursor_to_scheme (make_fixnum (curY (tty)), make_fixnum (curX (tty)),
				make_fixnum (vpos), make_fixnum (hpos),
				make_fixnum (tty->TF_standout_motion),
				make_fixnum (tty->TF_insmode_motion));
  if (NILP (steps))
    return;
  for (; CONSP (steps); steps = XCDR (steps))
    {
      Lisp_Object step = XCAR (steps);
      if (m52_tty_step_tag_p (step, "background"))
	tty_background_highlight (tty);
      else if (m52_tty_step_tag_p (step, "off-insert"))
	tty_turn_off_insert (tty);
      else if (m52_tty_step_tag_p (step, "move"))
	cmgoto (tty, XFIXNUM (XCAR (XCDR (step))),
		XFIXNUM (XCAR (XCDR (XCDR (step)))));
    }
}

/* Similar but don't take any account of the wasted characters.  */

static void
tty_raw_cursor_to (struct frame *f, int row, int col)
{
  struct tty_display_info *tty = FRAME_TTY (f);

  /* The same shape as tty_cursor_to, with the target ROW / COL.  */
  Lisp_Object steps
    = m52_tty_raw_cursor_to_scheme (make_fixnum (curY (tty)), make_fixnum (curX (tty)),
				    make_fixnum (row), make_fixnum (col),
				    make_fixnum (tty->TF_standout_motion),
				    make_fixnum (tty->TF_insmode_motion));
  if (NILP (steps))
    return;
  for (; CONSP (steps); steps = XCDR (steps))
    {
      Lisp_Object step = XCAR (steps);
      if (m52_tty_step_tag_p (step, "background"))
	tty_background_highlight (tty);
      else if (m52_tty_step_tag_p (step, "off-insert"))
	tty_turn_off_insert (tty);
      else if (m52_tty_step_tag_p (step, "move"))
	cmgoto (tty, XFIXNUM (XCAR (XCDR (step))),
		XFIXNUM (XCAR (XCDR (XCDR (step)))));
    }
}

/* Erase operations */

/* Clear from cursor to end of frame on a termcap device. */

static void
tty_clear_to_end (struct frame *f)
{
  register int i;
  struct tty_display_info *tty = FRAME_TTY (f);

  /* The selection runs in Scheme: the returned step is the KEY
     "clear-to-bottom", or the MARKER ("clear-loop").  C keeps the
     background highlight, OUTPUT, and the per-row loop.  */
  Lisp_Object step
    = m52_tty_clear_to_end_scheme (make_fixnum (tty->TS_clr_to_bottom != NULL));
  if (STRINGP (step))
    {
      tty_background_highlight (tty);
      OUTPUT (tty, m52_cap_string_1 (tty, step));
    }
  else if (m52_tty_step_tag_p (step, "clear-loop"))
    {
      for (i = curY (tty); i < FRAME_TOTAL_LINES (f); i++)
	{
	  cursor_to (f, i, 0);
	  clear_end_of_line (f, FRAME_COLS (f));
	}
    }
}

/* Clear an entire termcap frame. */

static void
tty_clear_frame (struct frame *f)
{
  struct tty_display_info *tty = FRAME_TTY (f);

  /* The selection runs in Scheme: the returned step is the KEY
     "clear-frame", or the MARKER ("clear-frame-fallback").  C keeps the
     background highlight, OUTPUT, cmat, and the fallback.  */
  Lisp_Object step
    = m52_tty_clear_frame_scheme (make_fixnum (tty->TS_clr_frame != NULL));
  if (STRINGP (step))
    {
      tty_background_highlight (tty);
      OUTPUT (tty, m52_cap_string_1 (tty, step));
      cmat (tty, 0, 0);
    }
  else if (m52_tty_step_tag_p (step, "clear-frame-fallback"))
    {
      cursor_to (f, 0, 0);
      clear_to_end (f);
    }
}

/* An implementation of clear_end_of_line for termcap frames.

   Note that the cursor may be moved, on terminals lacking a `ce' string.  */

static void
tty_clear_end_of_line (struct frame *f, int first_unused_hpos)
{
  register int i;
  struct tty_display_info *tty = FRAME_TTY (f);

  /* The 2 guards and the capability selection run in Scheme: the
     returned step is #nil when a guard holds, else the KEY "clear-line"
     or the MARKER ("clear-line-hard").  C reads the state before the
     background highlight (the original order), keeps the background
     highlight, OUTPUT1, the AutoWrap edge, the putc loop, and cmplus.  */
  Lisp_Object step
    = m52_tty_clear_end_of_line_scheme (make_fixnum (tty->costs_set),
					make_fixnum (curX (tty)),
					make_fixnum (first_unused_hpos),
					make_fixnum (tty->TS_clr_line != NULL));
  if (NILP (step))
    return;
  tty_background_highlight (tty);
  if (STRINGP (step))
    {
      OUTPUT1 (tty, m52_cap_string_1 (tty, step));
    }
  else if (m52_tty_step_tag_p (step, "clear-line-hard"))
    {			/* have to do it the hard way */
      tty_turn_off_insert (tty);

      /* Do not write in last row last col with Auto-wrap on. */
      if (AutoWrap (tty)
          && curY (tty) == FrameRows (tty) - 1
	  && first_unused_hpos == FrameCols (tty))
	first_unused_hpos--;

      for (i = curX (tty); i < first_unused_hpos; i++)
	{
	  if (tty->termscript)
	    putc (' ', tty->termscript);
	  putc (' ', tty->output);
	}
      cmplus (tty, first_unused_hpos - curX (tty));
    }
}

/* Buffers to store the source and result of code conversion for terminal.  */
static unsigned char *encode_terminal_src;
static unsigned char *encode_terminal_dst;
/* Allocated sizes of the above buffers.  */
static ptrdiff_t encode_terminal_src_size;
static ptrdiff_t encode_terminal_dst_size;

/* Encode SRC_LEN glyphs starting at SRC to terminal output codes.
   Set CODING->produced to the byte-length of the resulting byte
   sequence, and return a pointer to that byte sequence.  */

unsigned char *
encode_terminal_code (struct glyph *src, int src_len,
		      struct coding_system *coding)
{
  struct glyph *src_end = src + src_len;
  unsigned char *buf;
  ptrdiff_t nchars, nbytes, required;
  ptrdiff_t tlen = GLYPH_TABLE_LENGTH;
  register Lisp_Object *tbase = GLYPH_TABLE_BASE;
  Lisp_Object charset_list;

  /* Allocate sufficient size of buffer to store all characters in
     multibyte-form.  But, it may be enlarged on demand if
     Vglyph_table contains a string or a composite glyph is
     encountered.  */
  if (ckd_mul (&required, src_len, MAX_MULTIBYTE_LENGTH))
    memory_full (SIZE_MAX);
  if (encode_terminal_src_size < required)
    encode_terminal_src = xpalloc (encode_terminal_src,
				   &encode_terminal_src_size,
				   required - encode_terminal_src_size,
				   -1, sizeof *encode_terminal_src);

  charset_list = coding_charset_list (coding);

  buf = encode_terminal_src;
  nchars = 0;
  while (src < src_end)
    {
      if (src->type == COMPOSITE_GLYPH)
	{
	  struct composition *cmp;
	  Lisp_Object gstring UNINIT;
	  int i;

	  nbytes = buf - encode_terminal_src;
	  if (src->u.cmp.automatic)
	    {
	      cmp = NULL;
	      gstring = composition_gstring_from_id (src->u.cmp.id);
	      required = src->slice.cmp.to - src->slice.cmp.from + 1;
	    }
	  else
	    {
	      cmp = composition_table[src->u.cmp.id];
	      required = cmp->glyph_len;
	    }
	  required *= MAX_MULTIBYTE_LENGTH;

	  if (encode_terminal_src_size - nbytes < required)
	    {
	      encode_terminal_src =
		xpalloc (encode_terminal_src, &encode_terminal_src_size,
			 required - (encode_terminal_src_size - nbytes),
			 -1, 1);
	      buf = encode_terminal_src + nbytes;
	    }

	  if (!cmp)
	    for (i = src->slice.cmp.from; i <= src->slice.cmp.to; i++)
	      {
		Lisp_Object g = LGSTRING_GLYPH (gstring, i);
		int c = LGLYPH_CHAR (g);

		if (! char_charset (c, charset_list, NULL))
		  c = '?';
		buf += CHAR_STRING (c, buf);
		nchars++;
	      }
	  else
	    for (i = 0; i < cmp->glyph_len; i++)
	      {
		int c = COMPOSITION_GLYPH (cmp, i);

		/* TAB in a composition means display glyphs with
		   padding space on the left or right.  */
		if (c == '\t')
		  continue;
		if (char_charset (c, charset_list, NULL))
		  {
		    if (CHARACTER_WIDTH (c) == 0
			&& i > 0 && COMPOSITION_GLYPH (cmp, i - 1) == '\t')
		      /* Should be left-padded */
		      {
			buf += CHAR_STRING (' ', buf);
			nchars++;
		      }
		  }
		else
		  c = '?';
		buf += CHAR_STRING (c, buf);
		nchars++;
	      }
	}
      /* We must skip glyphs to be padded for a wide character.  */
      else if (! CHAR_GLYPH_PADDING_P (*src))
	{
	  GLYPH g;
	  int c UNINIT;
	  Lisp_Object string;

	  string = Qnil;
	  SET_GLYPH_FROM_CHAR_GLYPH (g, src[0]);

	  if (GLYPH_INVALID_P (g) || GLYPH_SIMPLE_P (tbase, tlen, g))
	    {
	      /* This glyph doesn't have an entry in Vglyph_table.  */
	      c = src->u.ch;
	    }
	  else
	    {
	      /* This glyph has an entry in Vglyph_table,
		 so process any alias before testing for simpleness.  */
	      GLYPH_FOLLOW_ALIASES (tbase, tlen, g);

	      if (GLYPH_SIMPLE_P (tbase, tlen, g))
		/* We set the multi-byte form of a character in G
		   (that should be an ASCII character) at WORKBUF.  */
		c = GLYPH_CHAR (g);
	      else
		/* We have a string in Vglyph_table.  */
		string = tbase[GLYPH_CHAR (g)];
	    }

	  if (NILP (string))
	    {
	      nbytes = buf - encode_terminal_src;
	      if (encode_terminal_src_size - nbytes < MAX_MULTIBYTE_LENGTH)
		{
		  encode_terminal_src =
		    xpalloc (encode_terminal_src, &encode_terminal_src_size,
			     MAX_MULTIBYTE_LENGTH, -1, 1);
		  buf = encode_terminal_src + nbytes;
		}
	      if (CHAR_BYTE8_P (c)
		  || char_charset (c, charset_list, NULL))
		{
		  /* Store the multibyte form of C at BUF.  */
		  buf += CHAR_STRING (c, buf);
		  nchars++;
		}
	      else
		{
		  /* C is not encodable.  */
		  *buf++ = '?';
		  nchars++;
		  while (src + 1 < src_end && CHAR_GLYPH_PADDING_P (src[1]))
		    {
		      *buf++ = '?';
		      nchars++;
		      src++;
		    }
		}
	    }
	  else
	    {
	      if (! STRING_MULTIBYTE (string))
		string = string_to_multibyte (string);
	      nbytes = buf - encode_terminal_src;
	      if (encode_terminal_src_size - nbytes < SBYTES (string))
		{
		  encode_terminal_src =
		    xpalloc (encode_terminal_src, &encode_terminal_src_size,
			     (SBYTES (string)
			      - (encode_terminal_src_size - nbytes)),
			     -1, 1);
		  buf = encode_terminal_src + nbytes;
		}
	      memcpy (buf, SDATA (string), SBYTES (string));
	      buf += SBYTES (string);
	      nchars += SCHARS (string);
	    }
	}
      src++;
    }

  if (nchars == 0)
    {
      coding->produced = 0;
      return NULL;
    }

  nbytes = buf - encode_terminal_src;
  coding->source = encode_terminal_src;
  if (encode_terminal_dst_size == 0)
    {
      encode_terminal_dst = xrealloc (encode_terminal_dst,
				      encode_terminal_src_size);
      encode_terminal_dst_size = encode_terminal_src_size;
    }
  coding->destination = encode_terminal_dst;
  coding->dst_bytes = encode_terminal_dst_size;
  encode_coding_object (coding, Qnil, 0, 0, nchars, nbytes, Qnil);
  /* coding->destination may have been reallocated.  */
  encode_terminal_dst = coding->destination;
  encode_terminal_dst_size = coding->dst_bytes;

  return (encode_terminal_dst);
}

#else /* !HAVE_ANDROID */

unsigned char *
encode_terminal_code (struct glyph *src, int src_len,
		      struct coding_system *coding)
{
  /* Text terminals are simply not supported on Android.  */
  coding->produced = 0;
  return NULL;
}

#endif /* HAVE_ANDROID */

/* --- M61 imp-1: the opaque per-TTY handle -------------------------- */

/* FIX-20261027-guilemacs: M61 imp-1 -- ONE opaque Scheme value per TTY
   (docs/m61-plan.org, milestone.org section 4).  Scheme holds a plain
   fixnum identity, and this static table maps that identity to the
   struct tty_display_info *.  The pointer never crosses the seam: no
   Lisp_Object, char *, FILE *, or struct is passed to Scheme, and the
   Scheme layer passes a number only.  The identity registers when the
   tty is created (init_tty) and drops at the terminal-death path
   (delete_tty), so the table never holds a dangling pointer.

   An identity is NEVER reused: m61_tty_handle_next only increases, so a
   handle that named a dead tty answers -EBADF and can not alias a new
   tty.

   FIX-20261027-guilemacs: the table has a FIXED capacity
   (M61_HANDLE_MAX).  A session with more text terminals than that runs
   the same write mechanism directly (m61_tty_output_write_1), so the
   limit costs no byte and no ordering (see m61_tty_handle_write_1).  A
   growable table is a later act; the handle contract does not
   change.  */

#define M61_HANDLE_MAX 16

static struct
{
  int identity;
  struct tty_display_info *tty;
} m61_tty_handles[M61_HANDLE_MAX];

static int m61_tty_handle_next = 1;

/* Resolve the M52 DEVICE convention (a terminal object, a frame, or nil
   for the selected frame) to its tty.  The definition is below, next to
   the M52 leaves; the resolver leaf --tty-handle is the ONE bootstrap
   step that still accepts a Lisp DEVICE, because a Scheme caller must
   have a way to name a TTY before it holds an identity.  */
static struct tty_display_info *m52_tty_of_device_1 (Lisp_Object);

/* The after-write verdict of one output write (M54 imp-2).  Both output
   writers -- the M61 handle path above and the M52 byte path below --
   ask through this ONE helper, so C keeps ONE decision site for the
   output stream (the M54 imp-2 rule).  The definition is in the M54
   block of this file.  */
static Lisp_Object m54_tty_write_verdict_1 (size_t, size_t, int);
static bool m54_tty_write_gives_up_p (Lisp_Object);

/* The ONE termscript verdict site of the M54 block of this file.  Imp-2
   reports a hard failure of a glyph termscript copy through it, so the
   definition sits below this point.  */
static void m54_tty_termscript_verdict (size_t, size_t, int, bool);

/* The Scheme POLICY dispatcher of the routed normal write: ask
   (emacs tty-output) tty-handle-write-all-borrowed for the write of
   IDENTITY with BYTES.  Scheme checks that the handle is open and it
   retries a short write (brief.org section 3); C keeps the mechanism.
   The definition is below, next to the leaf.  */
static Lisp_Object m61_tty_handle_write_scheme (Lisp_Object, Lisp_Object);

/* The Scheme POLICY dispatcher of the routed flush: ask (emacs
   tty-output) tty-handle-flush-borrowed for the open-handle check of
   IDENTITY.  C keeps the fflush and its position.  M61 imp-2.  */
static Lisp_Object m61_tty_handle_flush_scheme (Lisp_Object);

/* The Scheme POLICY dispatcher of the routed termscript copy: ask (emacs
   tty-output) tty-handle-termscript-borrowed to copy the BYTES of
   IDENTITY to the termscript stream.  M61 imp-2.  */
static Lisp_Object m61_tty_handle_termscript_scheme (Lisp_Object,
						     Lisp_Object);

/* ONE guarded Scheme call shape, shared by the 3 M61 dispatchers
   (brief.org section 6.4).  Do not add a second shape.

   A Scheme raise runs a non-local exit.  With no catch it leaves through
   the C frame of the caller, and that frame holds block_input at the 3
   glyph hubs, so the input block stays held.  scm_c_catch stops the exit
   here, and the handler answers a plain SCM_BOOL_F, so the C caller sees
   "no answer" and reports -EIO.

   SCM_CALL_1 and SCM_CALL_2 stay INSIDE the body: a plain scm_call_2
   loses the c_to_scheme_crossings count that debug-guile-cross-count
   reports.

   The argument count is the plain field NARGS, not a sentinel value: the
   flush dispatcher takes 1 argument, the write and the termscript
   dispatchers take 2.  SCM_UNDEFINED is Guile's undefined value only
   (cr1.org CR13).

   FIX-20261028-guilemacs: the write dispatcher had no guard before this
   act (brief.org section 6.4).  */
struct m61_tty_scheme_call
{
  SCM proc;
  Lisp_Object a, b;
  int nargs;
};

static Lisp_Object
m61_tty_scheme_body (void *data)
{
  struct m61_tty_scheme_call *call = data;

  if (call->nargs == 1)
    return SCM_CALL_1 (call->proc, call->a);

  return SCM_CALL_2 (call->proc, call->a, call->b);
}

/* The raise handler makes NO Lisp call: a Lisp call from here can raise a
   second time while the first exit is not finished.  */
static Lisp_Object
m61_tty_scheme_raise_handler (void *data, SCM key, SCM args)
{
  (void) data;
  (void) key;
  (void) args;
  return SCM_BOOL_F;
}

/* The 1-argument form (the flush dispatcher).  A second form of the SAME
   shape, so the arity stays readable and 1 sentinel value carries 1
   meaning (cr1.org CR13).  */
static Lisp_Object
m61_tty_scheme_guard_1 (SCM proc, Lisp_Object a)
{
  struct m61_tty_scheme_call call = { proc, a, SCM_UNDEFINED, 1 };

  return scm_c_catch (SCM_BOOL_T, m61_tty_scheme_body, &call,
		      m61_tty_scheme_raise_handler, NULL, NULL, NULL);
}

/* The 2-argument form (the write and the termscript dispatchers).  */
static Lisp_Object
m61_tty_scheme_guard_2 (SCM proc, Lisp_Object a, Lisp_Object b)
{
  struct m61_tty_scheme_call call = { proc, a, b, 2 };

  return scm_c_catch (SCM_BOOL_T, m61_tty_scheme_body, &call,
		      m61_tty_scheme_raise_handler, NULL, NULL, NULL);
}

/* Register TTY and return its plain identity, or -ENOSPC when the table
   is full, or -EBADF when TTY is NULL.  A second call for the same TTY
   answers the same identity.  */
static int
m61_tty_handle_register_1 (struct tty_display_info *tty)
{
  int free_slot = -1;

  if (!tty)
    return -EBADF;

  for (int i = 0; i < M61_HANDLE_MAX; i++)
    {
      if (m61_tty_handles[i].tty == tty && m61_tty_handles[i].identity)
	return m61_tty_handles[i].identity;
      if (free_slot < 0 && !m61_tty_handles[i].tty)
	free_slot = i;
    }

  if (free_slot < 0)
    return -ENOSPC;

  m61_tty_handles[free_slot].identity = m61_tty_handle_next++;
  m61_tty_handles[free_slot].tty = tty;
  return m61_tty_handles[free_slot].identity;
}

/* Drop the identity of TTY.  Runs at the terminal-death path, before the
   struct is freed.  */
static void
m61_tty_handle_drop_1 (struct tty_display_info *tty)
{
  for (int i = 0; i < M61_HANDLE_MAX; i++)
    if (tty && m61_tty_handles[i].tty == tty)
      {
	m61_tty_handles[i].tty = NULL;
	m61_tty_handles[i].identity = 0;
      }
}

/* Resolve the plain IDENTITY to its tty, or NULL when the table holds no
   entry for it (a closed or unknown handle).  */
static struct tty_display_info *
m61_tty_handle_of_identity_1 (int identity)
{
  if (identity <= 0)
    return NULL;

  for (int i = 0; i < M61_HANDLE_MAX; i++)
    if (m61_tty_handles[i].identity == identity)
      return m61_tty_handles[i].tty;

  return NULL;
}

/* Write LEN bytes at BYTES to the output stream of the tty TTY and
   return the =fwrite= count, or the negated errno of a hard failure that
   Scheme gives up on.  This is the mechanism of the handle path.

   C keeps the FILE *, the fwrite, the clearerr, and the order.  The
   after-write DECISION (retry / give-up) is the M54 imp-2 Scheme
   verdict, so a short write is reported as its count and only a give-up
   returns the negated errno.  The termscript copy and every fflush point
   stay at their call sites (M61 imp-2).  */
static ptrdiff_t
m61_tty_output_write_1 (struct tty_display_info *tty,
			const unsigned char *bytes, size_t len)
{
  if (!tty)
    return -EBADF;
  if (!tty->output)
    return -EINVAL;

  size_t written = fwrite (bytes, 1, len, tty->output);
  int out_err = errno;
  bool failed = ferror (tty->output) != 0;
  clearerr (tty->output);

  if (written < len && failed)
    {
      int e = out_err ? out_err : EIO;
      Lisp_Object verdict = m54_tty_write_verdict_1 (written, len, e);
      /* m54_tty_write_gives_up_p answers true for a nil verdict too (no
	 Scheme runtime), so this writer and the M52 writer below report
	 the SAME -e on a hard error (brief.org section 3).  */
      if (m54_tty_write_gives_up_p (verdict))
	return -e;
    }

  return (ptrdiff_t) written;
}

/* Resolve the plain IDENTITY, then run the write mechanism.  Return
   -EBADF for a closed or unknown identity.  This is the body of the leaf
   --tty-handle-write.  */
static ptrdiff_t
m61_tty_handle_write_bytes_1 (int identity, const unsigned char *bytes,
			      size_t len)
{
  struct tty_display_info *tty = m61_tty_handle_of_identity_1 (identity);

  if (!tty)
    return -EBADF;

  return m61_tty_output_write_1 (tty, bytes, len);
}

/* The hub entry point: write the encoded bytes of the normal glyph path
   through the handle IDENTITY of TTY, with the plain Guile bytevector BV
   that the caller built ONCE for the whole glyph run (imp-2 shares it
   with the termscript copy).  The CALLER registers the identity, so a
   full identity table builds NO bytevector for nothing (cr1.org CR14).
   C calls the Scheme policy procedure with plain values only.  Scheme
   checks that the handle is open and RETRIES a short write through
   tty-handle-write-all, so no byte of the glyph run is lost; C keeps the
   FILE *, the fwrite, the clearerr and the order (brief.org section 3).

   FIX-20261027-guilemacs: the bytevector is ONE allocation per glyph
   run inside block_input (cr1.org CR14).  A moving barrier (a shared
   bytevector) is a later act; the copy is the price of the plain-value
   seam.

   FIX-20261028-guilemacs: before the Guile runtime exists, and when the
   identity table is full, run the SAME write mechanism directly
   (m61_tty_output_write_1), so no byte is lost and the order holds.

   FIX-20261028-guilemacs: a #f answer is the guard's "no answer", so the
   SAME mechanism runs here and no byte is lost on a Scheme raise
   (brief.org section 5.2).  The doubling risk of this fallback is
   declared in milestone.org section 5.  */
static ptrdiff_t
m61_tty_handle_write_1 (struct tty_display_info *tty, int identity,
			Lisp_Object bv, const unsigned char *bytes, size_t len)
{
  if (identity < 0 || !guile_runtime_up ())
    return m61_tty_output_write_1 (tty, bytes, len);

  Lisp_Object rc = m61_tty_handle_write_scheme (make_fixnum (identity), bv);

  /* The guard answers SCM_BOOL_F when a Scheme raise is stopped, so a #f
     answer means "no answer" and the mechanism runs.  Any OTHER
     non-fixnum answer is a hard failure: do NOT write again, because the
     bytes may already be on the stream (brief.org section 5.2).  */
  if (scm_is_false (rc))
    return m61_tty_output_write_1 (tty, bytes, len);

  if (!FIXNUMP (rc))
    return -EIO;

  return (ptrdiff_t) XFIXNUM (rc);
}

/* Copy LEN bytes at BYTES to the termscript stream of TTY and return the
   =fwrite= count, or the negated errno of a hard failure.  The TRUE copy
   count always leaves through COPIED, also on a hard failure, so the M54
   verdict gets the measured count and not a literal 0 (cr1.org CR4).
   The errno leaves as a plain value in the ANSWER (cr.org F3).
   A session with no termscript stream is legal: COPIED is 0 and the
   answer is 0, a plain count and NOT an error.  C keeps the FILE *, the
   fwrite, the error flag, the errno and the clearerr.  */
static ptrdiff_t
m61_tty_output_termscript_1 (struct tty_display_info *tty,
			     const unsigned char *bytes, size_t len,
			     size_t *copied)
{
  size_t n;

  *copied = 0;
  if (!tty)
    return -EBADF;
  if (!tty->termscript)
    return 0;

  n = fwrite (bytes, 1, len, tty->termscript);
  *copied = n;
  int err = errno;
  bool failed = ferror (tty->termscript) != 0;
  clearerr (tty->termscript);

  if (n < len && failed)
    return -(err ? err : EIO);

  return (ptrdiff_t) n;
}

/* The termscript copy of one glyph run through the handle IDENTITY of
   TTY, with the SAME plain Guile bytevector BV that the output write
   used.  Scheme owns the closed-use check; C keeps the FILE * and the
   fwrite.  COPIED carries the true count to the caller (cr1.org CR4).

   FIX-20261028-guilemacs: the `!tty->termscript' pre-test is a STATE
   check in C.  It stays because a session without a termscript stream
   would otherwise cross into Scheme for nothing inside block_input.  The
   limit is declared in milestone.org section 5 (cr1.org CR10).  */
static ptrdiff_t
m61_tty_handle_termscript_1 (struct tty_display_info *tty, int identity,
			     Lisp_Object bv, const unsigned char *bytes,
			     size_t len, size_t *copied)
{
  *copied = 0;

  if (!tty || !tty->termscript || identity < 0 || !guile_runtime_up ())
    return m61_tty_output_termscript_1 (tty, bytes, len, copied);

  Lisp_Object rc = m61_tty_handle_termscript_scheme (make_fixnum (identity),
						     bv);

  if (!FIXNUMP (rc))
    {
      /* A #f answer is the guard's "no answer": run the mechanism, so no
	 byte is lost on a Scheme raise.  */
      if (scm_is_false (rc))
	return m61_tty_output_termscript_1 (tty, bytes, len, copied);
      return -EIO;
    }

  ptrdiff_t n = (ptrdiff_t) XFIXNUM (rc);
  if (n > 0)
    *copied = (size_t) n;

  return n;
}

/* ONE glyph run of the ordered output path: build ONE plain bytevector,
   then run the output write, then the termscript copy of the same bytes.
   The order is the contract (milestone.org section 3).

   cr1.org CR11: this hub READS both answers, but the write answer keeps
   its imp-1 behavior and is still not reported in this act.  A hard
   failure of the termscript copy can not restore the bytes, so it is
   recorded through the ONE M54 termscript verdict site instead of being
   dropped.  */
static void
m61_tty_handle_glyph_run_1 (struct tty_display_info *tty,
			    const unsigned char *bytes, size_t len)
{
  Lisp_Object bv = SCM_BOOL_F;
  int identity = -1;
  size_t copied_bytes = 0;
  ptrdiff_t written, copied;

  if (guile_runtime_up ())
    identity = m61_tty_handle_register_1 (tty);

  if (identity > 0)
    {
      bv = scm_c_make_bytevector (len);
      memcpy (SCM_BYTEVECTOR_CONTENTS (bv), bytes, len);
    }

  written = m61_tty_handle_write_1 (tty, identity, bv, bytes, len);
  copied = m61_tty_handle_termscript_1 (tty, identity, bv, bytes, len,
					&copied_bytes);

  (void) written;
  /* The verdict gets the MEASURED copy count (cr1.org CR4) and the errno
     as a plain value (cr.org F3).  A short copy with a clear error flag is
     reported too: the bytes of the 2 streams must agree (cr1.org CR12).
     No termscript stream is not a short copy.  */
  if (copied < 0)
    m54_tty_termscript_verdict (copied_bytes, len, (int) -copied, true);
  else if (tty && tty->termscript && copied_bytes < len)
    m54_tty_termscript_verdict (copied_bytes, len, 0, false);
}

/* Flush the output stream of TTY and return 0, or the negated errno of a
   hard failure (-EBADF when TTY is NULL, -EINVAL when it holds no output
   stream).  This is the mechanism of the flush of the ordered output
   path.  C keeps the FILE * and the fflush.  */
static ptrdiff_t
m61_tty_output_flush_1 (struct tty_display_info *tty)
{
  if (!tty)
    return -EBADF;
  if (!tty->output)
    return -EINVAL;

  if (fflush (tty->output) != 0)
    return -(errno ? errno : EIO);

  return 0;
}

/* Flush the output stream of TTY through its handle.  Scheme checks
   that the handle is open; C keeps the fflush and its position.  Before
   the Guile runtime exists, and when the identity table is full, run the
   same mechanism directly.  */
static ptrdiff_t
m61_tty_handle_flush_1 (struct tty_display_info *tty)
{
  int identity;

  if (!guile_runtime_up ())
    return m61_tty_output_flush_1 (tty);

  identity = m61_tty_handle_register_1 (tty);
  if (identity < 0)
    return m61_tty_output_flush_1 (tty);

  Lisp_Object rc = m61_tty_handle_flush_scheme (make_fixnum (identity));

  /* A flush is idempotent, so a non-fixnum answer costs NO byte: run the
     mechanism.  Without this fallback 1 Scheme raise would stop every
     later flush of the session, with no report (cr1.org CR3, brief.org
     section 5.2).  */
  if (!FIXNUMP (rc))
    return m61_tty_output_flush_1 (tty);

  return (ptrdiff_t) XFIXNUM (rc);
}

/* The ONE Scheme dispatcher of the routed normal write (brief.org
   section 3).  It resolves the module procedure one time (the M52 imp-4
   idiom), then passes plain values only: a fixnum identity and a Guile
   bytevector.  Scheme owns the state check and the retry, and it calls
   back into the leaf --tty-handle-write for the mechanism.  The call
   runs inside the ONE guard shape m61_tty_scheme_guard_2.  */
static Lisp_Object
m61_tty_handle_write_scheme (Lisp_Object identity, Lisp_Object bytes)
{
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs tty-output",
                             "tty-handle-write-all-borrowed");
  return m61_tty_scheme_guard_2 (proc, identity, bytes);
}

/* The ONE Scheme dispatcher of the routed flush (M61 imp-2).  IDENTITY is
   the plain fixnum identity, and the procedure takes it ALONE: the arity
   is the guard form m61_tty_scheme_guard_1, not a sentinel argument
   (cr1.org CR13).  */
static Lisp_Object
m61_tty_handle_flush_scheme (Lisp_Object identity)
{
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs tty-output",
                             "tty-handle-flush-borrowed");
  return m61_tty_scheme_guard_1 (proc, identity);
}

/* The ONE Scheme dispatcher of the routed termscript copy (brief.org
   section 3).  It passes the plain fixnum identity and the bytevector.  */
static Lisp_Object
m61_tty_handle_termscript_scheme (Lisp_Object identity, Lisp_Object bytes)
{
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs tty-output",
                             "tty-handle-termscript-borrowed");
  return m61_tty_scheme_guard_2 (proc, identity, bytes);
}

DEFUN ("--tty-handle-write", Fc_tty_handle_write, Sc_tty_handle_write,
       2, 2, 0,
       doc: /* FIX-20261027-guilemacs: Internal: M61 imp-1 -- write the
plain bytevector BYTES to the output stream of the per-TTY handle
IDENTITY (docs/m61-plan.org section 3.1).

IDENTITY is a plain fixnum that names an entry of the static C identity
table; it is not a pointer, not a byte offset, and not a descriptor.
C owns the struct tty_display_info and its FILE *output stream, so no
Lisp_Object, char *, FILE *, or struct crosses the layer
(docs/kb.org =passthrough-leaf-is-not-a-port=).

Return a plain fixnum: the =fwrite= count, or a negative fixnum holding
the negated errno (-EBADF when the identity is closed or unknown,
-EINVAL when BYTES is not a bytevector or the tty holds no output
stream).  A short write is reported as its count, so Scheme decides
retry / give-up through tty-write-verdict.  This leaf writes the output
stream only: the termscript copy and the fflush points stay at their
call sites (M61 imp-2).  */)
  (Lisp_Object identity, Lisp_Object bytes)
{
  if (!FIXNUMP (identity))
    return make_fixnum (-EINVAL);
  if (!scm_is_bytevector (bytes))
    return make_fixnum (-EINVAL);

  return make_fixnum
    (m61_tty_handle_write_bytes_1
     ((int) XFIXNUM (identity),
      (const unsigned char *) SCM_BYTEVECTOR_CONTENTS (bytes),
      scm_c_bytevector_length (bytes)));
}

DEFUN ("--tty-handle-flush", Fc_tty_handle_flush, Sc_tty_handle_flush,
       1, 1, 0,
       doc: /* FIX-20261028-guilemacs: Internal: M61 imp-2 -- flush the
output stream of the per-TTY handle IDENTITY (=fflush=).

IDENTITY is a plain fixnum that names an entry of the static C identity
table; it is not a pointer, not a byte offset, and not a descriptor.  C
owns the struct tty_display_info and its FILE *output stream, so no
Lisp_Object, char *, FILE *, or struct crosses the layer
(docs/kb.org =passthrough-leaf-is-not-a-port=).

Return a plain fixnum: 0 on success, or a negative fixnum holding the
negated errno (-EBADF when the identity is closed or unknown, -EINVAL
when the tty holds no output stream).  Scheme checks that the handle is
open; C keeps the fflush and its position.  */)
  (Lisp_Object identity)
{
  struct tty_display_info *tty;

  if (!FIXNUMP (identity))
    return make_fixnum (-EINVAL);

  tty = m61_tty_handle_of_identity_1 ((int) XFIXNUM (identity));
  if (!tty)
    return make_fixnum (-EBADF);

  return make_fixnum (m61_tty_output_flush_1 (tty));
}

DEFUN ("--tty-handle-termscript", Fc_tty_handle_termscript,
       Sc_tty_handle_termscript, 2, 2, 0,
       doc: /* FIX-20261028-guilemacs: Internal: M61 imp-2 -- copy the
plain bytevector BYTES to the termscript stream of the per-TTY handle
IDENTITY.

IDENTITY is a plain fixnum that names an entry of the static C identity
table.  C owns the struct tty_display_info and its FILE *termscript
stream.  BYTES must be a bytevector (scm_is_bytevector), not a string.

Return a plain fixnum: the =fwrite= count, or a negative fixnum holding
the negated errno (-EBADF when the identity is closed or unknown,
-EINVAL when BYTES is not a bytevector).  A session with no termscript
stream answers 0: that is a plain count of 0 and NOT an error, because a
tty without tty->termscript is legal.  */)
  (Lisp_Object identity, Lisp_Object bytes)
{
  struct tty_display_info *tty;

  if (!FIXNUMP (identity))
    return make_fixnum (-EINVAL);
  if (!scm_is_bytevector (bytes))
    return make_fixnum (-EINVAL);

  tty = m61_tty_handle_of_identity_1 ((int) XFIXNUM (identity));
  if (!tty)
    return make_fixnum (-EBADF);

  size_t copied = 0;
  ptrdiff_t answer
    = m61_tty_output_termscript_1
    (tty, (const unsigned char *) SCM_BYTEVECTOR_CONTENTS (bytes),
     scm_c_bytevector_length (bytes), &copied);

  return make_fixnum (answer);
}

DEFUN ("--tty-handle", Fc_tty_handle, Sc_tty_handle, 1, 1, 0,
       doc: /* FIX-20261027-guilemacs: Internal: M61 imp-1 -- return the
plain identity of the per-TTY handle of DEVICE.

DEVICE is the M52 convention: a terminal object, a frame, or nil for the
selected frame.  This is the ONE bootstrap step of the handle layer: a
Scheme caller must be able to name a TTY before it holds a number, so
this leaf resolves DEVICE to its tty and registers the identity.  Every
other M61 operation takes the plain fixnum identity only.

Return a plain fixnum: the identity, or a negative fixnum holding the
negated errno (-EBADF when DEVICE does not resolve to a tty, -ENOSPC
when the identity table is full).  docs/m61-plan.org section 3.1.  */)
  (Lisp_Object device)
{
  struct tty_display_info *tty = m52_tty_of_device_1 (device);

  if (!tty)
    return make_fixnum (-EBADF);

  return make_fixnum (m61_tty_handle_register_1 (tty));
}

#ifndef HAVE_ANDROID

/* An implementation of write_glyphs for termcap frames. */

static void
tty_write_glyphs (struct frame *f, struct glyph *string, int len)
{
  struct tty_display_info *tty = FRAME_TTY (f);
  tty_turn_off_insert (tty);
  tty_hide_cursor (tty);

  /* Don't dare write in last column of bottom line, if Auto-Wrap,
     since that would scroll the whole frame on some terminals.  */
  if (AutoWrap (tty)
      && curY (tty) + 1 == FRAME_TOTAL_LINES (f)
      && (curX (tty) + len) == FRAME_COLS (f))
    len --;
  if (len <= 0)
    return;

  cmplus (tty, len);

  /* If terminal_coding does any conversion, use it, otherwise use
     safe_terminal_coding.  We can't use CODING_REQUIRE_ENCODING here
     because it always return 1 if the member src_multibyte is 1.  */
  struct coding_system *coding
    = (FRAME_TERMINAL_CODING (f)->common_flags & CODING_REQUIRE_ENCODING_MASK
       ? FRAME_TERMINAL_CODING (f) : &safe_terminal_coding);

  /* The mode bit CODING_MODE_LAST_BLOCK should be set to 1 only at
     the tail.  */
  coding->mode &= ~CODING_MODE_LAST_BLOCK;

  for (int stringlen = len, n; stringlen; stringlen -= n, string += n)
    {
      /* Identify a run of glyphs with the same face.  */
      int face_id = string->face_id;
      struct frame *face_id_frame = string->frame;

      for (n = 1; n < stringlen; ++n)
	if (string[n].face_id != face_id || string[n].frame != face_id_frame)
	  break;

      /* Turn appearance modes of the face of the run on.  */
      tty_highlight_if_desired (tty);
      struct face *face = FACE_FROM_ID (face_id_frame, face_id);
      turn_on_face (f, face);

      if (n == stringlen)
	/* This is the last run.  */
	coding->mode |= CODING_MODE_LAST_BLOCK;
      unsigned char *conversion_buffer
	= encode_terminal_code (string, n, coding);
      if (coding->produced > 0)
	{
	  block_input ();
	  /* M61 imp-2: ONE bytevector per glyph run, shared by the 2
	     operations.  The order is the contract: the output write
	     first, the termscript copy second.  C keeps the
	     block_input region, the FILE * streams and the clearerr
	     (brief.org section 3).  */
	  m61_tty_handle_glyph_run_1 (tty, conversion_buffer,
				      coding->produced);
	  unblock_input ();
	}

      /* Turn appearance modes off.  */
      turn_off_face (f, face);
      tty_turn_off_highlight (tty);
    }

  cmcheckmagic (tty);
}

#ifndef DOS_NT

static void
tty_write_glyphs_with_face (struct frame *f, struct glyph *string,
			    int len, struct face *face)
{
  unsigned char *conversion_buffer;
  struct coding_system *coding;

  struct tty_display_info *tty = FRAME_TTY (f);

  tty_turn_off_insert (tty);
  tty_hide_cursor (tty);

  /* Don't dare write in last column of bottom line, if Auto-Wrap,
     since that would scroll the whole frame on some terminals.  */

  if (AutoWrap (tty)
      && curY (tty) + 1 == FRAME_TOTAL_LINES (f)
      && (curX (tty) + len) == FRAME_COLS (f))
    len --;
  if (len <= 0)
    return;

  cmplus (tty, len);

  /* If terminal_coding does any conversion, use it, otherwise use
     safe_terminal_coding.  We can't use CODING_REQUIRE_ENCODING here
     because it always return 1 if the member src_multibyte is 1.  */
  coding = (FRAME_TERMINAL_CODING (f)->common_flags & CODING_REQUIRE_ENCODING_MASK
	    ? FRAME_TERMINAL_CODING (f) : &safe_terminal_coding);
  /* The mode bit CODING_MODE_LAST_BLOCK should be set to 1 only at
     the tail.  */
  coding->mode &= ~CODING_MODE_LAST_BLOCK;

  /* Turn appearance modes of the face.  */
  tty_highlight_if_desired (tty);
  turn_on_face (f, face);

  coding->mode |= CODING_MODE_LAST_BLOCK;
  conversion_buffer = encode_terminal_code (string, len, coding);
  if (coding->produced > 0)
    {
      block_input ();
      /* M61 imp-2: ONE bytevector per glyph run, shared by the 2
         operations.  The order is the contract: the output write first,
         the termscript copy second.  C keeps the block_input region, the
         FILE * streams and the clearerr (brief.org section 3).  */
      m61_tty_handle_glyph_run_1 (tty, conversion_buffer,
				  coding->produced);
      unblock_input ();
    }

  /* Turn appearance modes off.  */
  turn_off_face (f, face);
  tty_turn_off_highlight (tty);

  cmcheckmagic (tty);
}

#endif

/* An implementation of insert_glyphs for termcap frames. */

static void
tty_insert_glyphs (struct frame *f, struct glyph *start, int len)
{
  char *buf;
  struct glyph *glyph = NULL;
  unsigned char *conversion_buffer;
  unsigned char space[1];
  struct coding_system *coding;

  struct tty_display_info *tty = FRAME_TTY (f);

  if (tty->TS_ins_multi_chars)
    {
      buf = tparam (tty->TS_ins_multi_chars, 0, 0, len, 0, 0, 0);
      OUTPUT1 (tty, buf);
      xfree (buf);
      if (start)
	write_glyphs (f, start, len);
      return;
    }

  tty_turn_on_insert (tty);
  cmplus (tty, len);

  if (! start)
    space[0] = SPACEGLYPH;

  /* If terminal_coding does any conversion, use it, otherwise use
     safe_terminal_coding.  We can't use CODING_REQUIRE_ENCODING here
     because it always return 1 if the member src_multibyte is 1.  */
  coding = (FRAME_TERMINAL_CODING (f)->common_flags & CODING_REQUIRE_ENCODING_MASK
	    ? FRAME_TERMINAL_CODING (f) : &safe_terminal_coding);
  /* The mode bit CODING_MODE_LAST_BLOCK should be set to 1 only at
     the tail.  */
  coding->mode &= ~CODING_MODE_LAST_BLOCK;

  while (len-- > 0)
    {
      struct face *face = NULL;
      OUTPUT1_IF (tty, tty->TS_ins_char);
      if (!start)
	{
	  conversion_buffer = space;
	  coding->produced = 1;
	}
      else
	{
	  tty_highlight_if_desired (tty);
	  int face_id = start->face_id;
	  struct frame *face_id_frame = start->frame;
	  face = FACE_FROM_ID (face_id_frame, face_id);
	  turn_on_face (f, face);
	  glyph = start;
	  ++start;
	  /* We must open sufficient space for a character which
	     occupies more than one column.  */
	  while (len && CHAR_GLYPH_PADDING_P (*start))
	    {
	      OUTPUT1_IF (tty, tty->TS_ins_char);
	      start++, len--;
	    }

	  if (len <= 0)
	    /* This is the last glyph.  */
	    coding->mode |= CODING_MODE_LAST_BLOCK;

          conversion_buffer = encode_terminal_code (glyph, 1, coding);
	}

      if (coding->produced > 0)
	{
	  block_input ();
	  /* M61 imp-2: ONE bytevector per glyph run, shared by the 2
	     operations.  The order is the contract: the output write
	     first, the termscript copy second.  C keeps the
	     block_input region, the FILE * streams and the clearerr
	     (brief.org section 3).  */
	  m61_tty_handle_glyph_run_1 (tty, conversion_buffer,
				      coding->produced);
	  unblock_input ();
	}

      OUTPUT1_IF (tty, tty->TS_pad_inserted_char);
      if (face)
	{
	  turn_off_face (f, face);
	  tty_turn_off_highlight (tty);
	}
    }

  cmcheckmagic (tty);
}

/* An implementation of delete_glyphs for termcap frames. */

static void
tty_delete_glyphs (struct frame *f, int n)
{
  char *buf;
  register int i;

  struct tty_display_info *tty = FRAME_TTY (f);
  int a[4];
  Lisp_Object steps
    = m52_tty_delete_glyphs_scheme (make_fixnum (n),
				    make_fixnum (tty->delete_in_insert_mode != 0),
				    make_fixnum (tty->TS_del_multi_chars != NULL));
  /* M52 imp-8: the insert-mode branch, the delete form, and the
     end-delete-mode step run in Scheme.  C keeps tty_turn_on_insert /
     tty_turn_off_insert, OUTPUT_IF, tparam, OUTPUT1, and the del_char
     loop.  */
  for (; CONSP (steps); steps = XCDR (steps))
    {
      Lisp_Object s = XCAR (steps);
      a[0] = a[1] = a[2] = a[3] = 0;
      if (STRINGP (s))
	OUTPUT_IF (tty, m52_cap_string_1 (tty, s));   /* the KEY route */
      else if (m52_tty_step_tag_p (s, "on-insert"))
	tty_turn_on_insert (tty);                     /* keep this C call */
      else if (m52_tty_step_tag_p (s, "off-insert"))
	tty_turn_off_insert (tty);                    /* keep this C call */
      else if (m52_tty_step_tag_p (s, "del-multi"))
	{
	  m52_tty_step_args_1 (s, a, 1);
	  buf = tparam (tty->TS_del_multi_chars, 0, 0, a[0], 0, 0, 0);
	  OUTPUT1 (tty, buf);
	  xfree (buf);
	}
      else if (m52_tty_step_tag_p (s, "del-char"))
	{
	  m52_tty_step_args_1 (s, a, 1);
	  for (i = 0; i < a[0]; i++)
	    OUTPUT1 (tty, tty->TS_del_char);          /* keep the loop */
	}
    }
}

/* An implementation of ins_del_lines for termcap frames. */

static void
tty_ins_del_lines (struct frame *f, int vpos, int n)
{
  struct tty_display_info *tty = FRAME_TTY (f);
  const char *multi =
    n > 0 ? tty->TS_ins_multi_lines : tty->TS_del_multi_lines;
  const char *single = n > 0 ? tty->TS_ins_line : tty->TS_del_line;
  const char *scroll = n > 0 ? tty->TS_rev_scroll : tty->TS_fwd_scroll;

  char *buf;
  int a[4];
  /* M52 imp-8: eabs and the 2 guards run in Scheme (pure arithmetic);
     C keeps the guard EFFECT through the NILP route.  The multi /
     single / scroll choice and the args run in Scheme.  C keeps
     raw_cursor_to, tty_background_highlight, tparam, OUTPUT, OUTPUTL,
     the 2 tty_set_scroll_region calls, the TF_teleray curX reset, and
     the trailing cursor_to + clear_to_end.  The a[1] arg is
     specified_window - vpos, the OUTPUTL line count.  */
  Lisp_Object step
    = m52_tty_ins_del_lines_scheme (make_fixnum (vpos), make_fixnum (n),
				    make_fixnum (tty->specified_window),
				    make_fixnum (FRAME_TOTAL_LINES (f)),
				    make_fixnum (FRAME_SCROLL_REGION_OK (f) != 0),
				    make_fixnum (FRAME_MEMORY_BELOW_FRAME (f) != 0),
				    make_fixnum (multi != NULL),
				    make_fixnum (single != NULL),
				    make_fixnum (scroll != NULL));
  if (NILP (step))
    return;                                   /* the guard route */
  a[0] = a[1] = a[2] = a[3] = 0;
  m52_tty_step_args_1 (step, a, 2);
  if (m52_tty_step_tag_p (step, "multi"))
    {
      raw_cursor_to (f, vpos, 0);
      tty_background_highlight (tty);
      buf = tparam (multi, 0, 0, a[0], 0, 0, 0);
      OUTPUT (tty, buf);
      xfree (buf);
    }
  else if (m52_tty_step_tag_p (step, "single"))
    {
      int k = a[0];
      raw_cursor_to (f, vpos, 0);
      tty_background_highlight (tty);
      while (--k >= 0)
        OUTPUT (tty, single);
      if (tty->TF_teleray)
        curX (tty) = 0;
    }
  else if (m52_tty_step_tag_p (step, "scroll"))
    {
      int k = a[0];
      tty_set_scroll_region (f, vpos, tty->specified_window);
      if (n < 0)
        raw_cursor_to (f, tty->specified_window - 1, 0);
      else
        raw_cursor_to (f, vpos, 0);
      tty_background_highlight (tty);
      while (--k >= 0)
        OUTPUTL (tty, scroll, a[1]);
      tty_set_scroll_region (f, 0, tty->specified_window);
    }

  if (!FRAME_SCROLL_REGION_OK (f)
      && FRAME_MEMORY_BELOW_FRAME (f)
      && n < 0)
    {
      cursor_to (f, FRAME_TOTAL_LINES (f) + n, 0);
      clear_to_end (f);
    }
}

/* Compute cost of sending "str", in characters,
   not counting any line-dependent padding.  */

int
string_cost (const char *str)
{
  cost = 0;
#ifndef HAVE_ANDROID
  if (str)
    tputs (str, 0, evalcost);
#endif
  return cost;
}

/* Compute cost of sending "str", in characters,
   counting any line-dependent padding at one line.  */

static int
string_cost_one_line (const char *str)
{
  cost = 0;
#ifndef HAVE_ANDROID
  if (str)
    tputs (str, 1, evalcost);
#endif
  return cost;
}

/* Compute per line amount of line-dependent padding,
   in tenths of characters.  */

int
per_line_cost (const char *str)
{
  cost = 0;
#ifndef HAVE_ANDROID
  if (str)
    tputs (str, 0, evalcost);
  cost = - cost;
  if (str)
    tputs (str, 10, evalcost);
#endif
  return cost;
}

/* char_ins_del_cost[n] is cost of inserting N characters.
   char_ins_del_cost[-n] is cost of deleting N characters.
   The length of this vector is based on max_frame_cols.  */

int *char_ins_del_vector;

#define char_ins_del_cost(f) (&char_ins_del_vector[FRAME_COLS (f)])

static void
calculate_ins_del_char_costs (struct frame *f)
{
  struct tty_display_info *tty = FRAME_TTY (f);
  int ins_startup_cost, del_startup_cost;
  int ins_cost_per_char, del_cost_per_char;
  register int i;
  register int *p;

  if (tty->TS_ins_multi_chars)
    {
      ins_cost_per_char = 0;
      ins_startup_cost = string_cost_one_line (tty->TS_ins_multi_chars);
    }
  else if (tty->TS_ins_char || tty->TS_pad_inserted_char
	   || (tty->TS_insert_mode && tty->TS_end_insert_mode))
    {
      ins_startup_cost = (30 * (string_cost (tty->TS_insert_mode)
				+ string_cost (tty->TS_end_insert_mode))) / 100;
      ins_cost_per_char = (string_cost_one_line (tty->TS_ins_char)
			   + string_cost_one_line (tty->TS_pad_inserted_char));
    }
  else
    {
      ins_startup_cost = 9999;
      ins_cost_per_char = 0;
    }

  if (tty->TS_del_multi_chars)
    {
      del_cost_per_char = 0;
      del_startup_cost = string_cost_one_line (tty->TS_del_multi_chars);
    }
  else if (tty->TS_del_char)
    {
      del_startup_cost = (string_cost (tty->TS_delete_mode)
			  + string_cost (tty->TS_end_delete_mode));
      if (tty->delete_in_insert_mode)
	del_startup_cost /= 2;
      del_cost_per_char = string_cost_one_line (tty->TS_del_char);
    }
  else
    {
      del_startup_cost = 9999;
      del_cost_per_char = 0;
    }

  /* Delete costs are at negative offsets */
  p = &char_ins_del_cost (f)[0];
  for (i = FRAME_COLS (f); --i >= 0;)
    *--p = (del_startup_cost += del_cost_per_char);

  /* Doing nothing is free */
  p = &char_ins_del_cost (f)[0];
  *p++ = 0;

  /* Insert costs are at positive offsets */
  for (i = FRAME_COLS (f); --i >= 0;)
    *p++ = (ins_startup_cost += ins_cost_per_char);
}

#endif

void
calculate_costs (struct frame *frame)
{
  FRAME_COST_BAUD_RATE (frame) = baud_rate;

#ifndef HAVE_ANDROID
  if (FRAME_TERMCAP_P (frame))
    {
      struct tty_display_info *tty = FRAME_TTY (frame);
      register const char *f = (tty->TS_set_scroll_region
				? tty->TS_set_scroll_region
				: tty->TS_set_scroll_region_1);

      FRAME_SCROLL_REGION_COST (frame) = string_cost (f);

      tty->costs_set = 1;

      /* These variables are only used for terminal stuff.  They are
         allocated once for the terminal frame of X-windows emacs, but not
         used afterwards.

         char_ins_del_vector (i.e., char_ins_del_cost) isn't used because
         X turns off char_ins_del_ok. */

      max_frame_cols = max (max_frame_cols, FRAME_COLS (frame));
      if ((min (PTRDIFF_MAX, SIZE_MAX) / sizeof (int) - 1) / 2
	  < max_frame_cols)
	memory_full (SIZE_MAX);

      char_ins_del_vector =
	xrealloc (char_ins_del_vector,
		  (sizeof (int) + 2 * sizeof (int) * max_frame_cols));

      memset (char_ins_del_vector, 0,
	      (sizeof (int) + 2 * sizeof (int) * max_frame_cols));


      if (f && (!tty->TS_ins_line && !tty->TS_del_line))
        do_line_insertion_deletion_costs (frame,
                                          tty->TS_rev_scroll, tty->TS_ins_multi_lines,
                                          tty->TS_fwd_scroll, tty->TS_del_multi_lines,
                                          f, f, 1);
      else
        do_line_insertion_deletion_costs (frame,
                                          tty->TS_ins_line, tty->TS_ins_multi_lines,
                                          tty->TS_del_line, tty->TS_del_multi_lines,
                                          0, 0, 1);

      calculate_ins_del_char_costs (frame);

      /* Don't use TS_repeat if its padding is worse than sending the chars */
      if (tty->TS_repeat
	  && (baud_rate <= 0
	      || per_line_cost (tty->TS_repeat) < 9000 / baud_rate))
        tty->RPov = string_cost (tty->TS_repeat);
      else
        tty->RPov = FRAME_COLS (frame) * 2;

      cmcostinit (FRAME_TTY (frame)); /* set up cursor motion costs */
    }
#endif
}

struct fkey_table
{
  const char *cap, *name;
};

#if !defined DOS_NT && !defined HAVE_ANDROID
  /* Termcap capability names that correspond directly to X keysyms.
     Some of these (marked "terminfo") aren't supplied by old-style
     (Berkeley) termcap entries.  They're listed in X keysym order;
     except we put the keypad keys first, so that if they clash with
     other keys (as on the IBM PC keyboard) they get overridden.
  */

static const struct fkey_table keys[] =
{
  {"kh", "home"},	/* termcap */
  {"kl", "left"},	/* termcap */
  {"ku", "up"},		/* termcap */
  {"kr", "right"},	/* termcap */
  {"kd", "down"},	/* termcap */
  {"%8", "prior"},	/* terminfo */
  {"%5", "next"},	/* terminfo */
  {"@7", "end"},	/* terminfo */
  {"@1", "begin"},	/* terminfo */
  {"*6", "select"},	/* terminfo */
  {"%9", "print"},	/* terminfo */
  {"@4", "execute"},	/* terminfo --- actually the `command' key */
  /*
   * "insert" --- see below
   */
  {"&8", "undo"},	/* terminfo */
  {"%0", "redo"},	/* terminfo */
  {"%7", "menu"},	/* terminfo --- actually the `options' key */
  {"@0", "find"},	/* terminfo */
  {"@2", "cancel"},	/* terminfo */
  {"%1", "help"},	/* terminfo */
  /*
   * "break" goes here, but can't be reliably intercepted with termcap
   */
  {"&4", "reset"},	/* terminfo --- actually `restart' */
  /*
   * "system" and "user" --- no termcaps
   */
  {"kE", "clearline"},	/* terminfo */
  {"kA", "insertline"},	/* terminfo */
  {"kL", "deleteline"},	/* terminfo */
  {"kI", "insertchar"},	/* terminfo */
  {"kD", "deletechar"},	/* terminfo */
  {"kB", "backtab"},	/* terminfo */
  /*
   * "kp_backtab", "kp-space", "kp-tab" --- no termcaps
   */
  {"@8", "kp-enter"},	/* terminfo */
  /*
   * "kp-f1", "kp-f2", "kp-f3" "kp-f4",
   * "kp-multiply", "kp-add", "kp-separator",
   * "kp-subtract", "kp-decimal", "kp-divide", "kp-0";
   * --- no termcaps for any of these.
   */
  {"K4", "kp-1"},	/* terminfo */
  /*
   * "kp-2" --- no termcap
   */
  {"K5", "kp-3"},	/* terminfo */
  /*
   * "kp-4" --- no termcap
   */
  {"K2", "kp-5"},	/* terminfo */
  /*
   * "kp-6" --- no termcap
   */
  {"K1", "kp-7"},	/* terminfo */
  /*
   * "kp-8" --- no termcap
   */
  {"K3", "kp-9"},	/* terminfo */
  /*
   * "kp-equal" --- no termcap
   */
  {"k1", "f1"},
  {"k2", "f2"},
  {"k3", "f3"},
  {"k4", "f4"},
  {"k5", "f5"},
  {"k6", "f6"},
  {"k7", "f7"},
  {"k8", "f8"},
  {"k9", "f9"},

  {"&0", "S-cancel"},    /*shifted cancel key*/
  {"&9", "S-begin"},     /*shifted begin key*/
  {"*0", "S-find"},      /*shifted find key*/
  {"*1", "S-execute"},   /*shifted execute? actually shifted command key*/
  {"*4", "S-delete"},    /*shifted delete-character key*/
  {"*7", "S-end"},       /*shifted end key*/
  {"*8", "S-clearline"}, /*shifted clear-to end-of-line key*/
  {"#1", "S-help"},      /*shifted help key*/
  {"#2", "S-home"},      /*shifted home key*/
  {"#3", "S-insert"},    /*shifted insert-character key*/
  {"#4", "S-left"},      /*shifted left-arrow key*/
  {"%d", "S-menu"},      /*shifted menu? actually shifted options key*/
  {"%c", "S-next"},      /*shifted next key*/
  {"%e", "S-prior"},     /*shifted previous key*/
  {"%f", "S-print"},     /*shifted print key*/
  {"%g", "S-redo"},      /*shifted redo key*/
  {"%i", "S-right"},     /*shifted right-arrow key*/
  {"!3", "S-undo"}       /*shifted undo key*/
  };

static char **term_get_fkeys_address;
static KBOARD *term_get_fkeys_kboard;
static Lisp_Object term_get_fkeys_1 (void);

/* Find the escape codes sent by the function keys for Vinput_decode_map.
   This function scans the termcap function key sequence entries, and
   adds entries to Vinput_decode_map for each function key it finds.  */

static void
term_get_fkeys (char **address, KBOARD *kboard)
{
  /* We run the body of the function (term_get_fkeys_1) and ignore all Lisp
     errors during the call.  The only errors should be from Fdefine_key
     when given a key sequence containing an invalid prefix key.  If the
     termcap defines function keys which use a prefix that is already bound
     to a command by the default bindings, we should silently ignore that
     function key specification, rather than giving the user an error and
     refusing to run at all on such a terminal.  */

  term_get_fkeys_address = address;
  term_get_fkeys_kboard = kboard;
  internal_condition_case (term_get_fkeys_1, Qerror, Fidentity);
}

static Lisp_Object
term_get_fkeys_1 (void)
{
  int i;

  char **address = term_get_fkeys_address;
  KBOARD *kboard = term_get_fkeys_kboard;

  /* This can happen if Emacs is starting up from scratch, or with
     strange options.  */
  if (!KEYMAPP (KVAR (kboard, Vinput_decode_map)))
    kset_input_decode_map (kboard, Fmake_sparse_keymap (Qnil));

  for (i = 0; i < ARRAYELTS (keys); i++)
    {
      char *sequence = tgetstr (keys[i].cap, address);
      if (sequence)
	Fdefine_key (KVAR (kboard, Vinput_decode_map), build_string (sequence),
		     make_elisp_vector (1, intern (keys[i].name)), Qnil);
    }

  /* The uses of the "k0" capability are inconsistent; sometimes it
     describes F10, whereas othertimes it describes F0 and "k;" describes F10.
     We will attempt to politely accommodate both systems by testing for
     "k;", and if it is present, assuming that "k0" denotes F0, otherwise F10.
     */
  {
    const char *k_semi  = tgetstr ("k;", address);
    const char *k0      = tgetstr ("k0", address);
    const char *k0_name = "f10";

    if (k_semi)
      {
	if (k0)
	  /* Define f0 first, so that f10 takes precedence in case the
	     key sequences happens to be the same.  */
	  Fdefine_key (KVAR (kboard, Vinput_decode_map), build_string (k0),
		       make_elisp_vector (1, Qf0), Qnil);
	Fdefine_key (KVAR (kboard, Vinput_decode_map), build_string (k_semi),
		     make_elisp_vector (1, Qf10), Qnil);
      }
    else if (k0)
      Fdefine_key (KVAR (kboard, Vinput_decode_map), build_string (k0),
		   make_elisp_vector (1, intern (k0_name)), Qnil);
  }

  /* Set up cookies for numbered function keys above f10. */
  {
    char fcap[3], fkey[4];

    fcap[0] = 'F'; fcap[2] = '\0';
    for (i = 11; i < 64; i++)
      {
	if (i <= 19)
	  fcap[1] = '1' + i - 11;
	else if (i <= 45)
	  fcap[1] = 'A' + i - 20;
	else
	  fcap[1] = 'a' + i - 46;

	{
	  char *sequence = tgetstr (fcap, address);
	  if (sequence)
	    {
	      sprintf (fkey, "f%d", i);
	      Fdefine_key (KVAR (kboard, Vinput_decode_map),
			   build_string (sequence),
			   make_elisp_vector (1, intern (fkey)),
			   Qnil);
	    }
	}
      }
   }

  /*
   * Various mappings to try and get a better fit.
   */
  {
#define CONDITIONAL_REASSIGN(cap1, cap2, sym)				\
      if (!tgetstr (cap1, address))					\
	{								\
	  char *sequence = tgetstr (cap2, address);			\
	  if (sequence)                                                 \
	    Fdefine_key (KVAR (kboard, Vinput_decode_map), build_string (sequence), \
			 make_elisp_vector (1, intern (sym)), Qnil);	\
	}

      /* if there's no key_next keycap, map key_npage to `next' keysym */
      CONDITIONAL_REASSIGN ("%5", "kN", "next");
      /* if there's no key_prev keycap, map key_ppage to `previous' keysym */
      CONDITIONAL_REASSIGN ("%8", "kP", "prior");
      /* if there's no key_dc keycap, map key_ic to `insert' keysym */
      CONDITIONAL_REASSIGN ("kD", "kI", "insert");
      /* if there's no key_end keycap, map key_ll to 'end' keysym */
      CONDITIONAL_REASSIGN ("@7", "kH", "end");
#undef CONDITIONAL_REASSIGN
  }

  return Qnil;
}
#endif /* not DOS_NT */



/***********************************************************************
		       Character Display Information
 ***********************************************************************/

/* Glyph production must be enabled on Android despite there being no
   TTY frames on that platform, as certain packages (and now, through
   Org, the bootstrap) require that window text measurements be
   available from the initial frame as in batch mode.  */

static void append_glyph (struct it *);
static void append_composite_glyph (struct it *);
static void produce_composite_glyph (struct it *);
static void append_glyphless_glyph (struct it *, int, const char *);
static void produce_glyphless_glyph (struct it *, Lisp_Object);

/* Append glyphs to IT's glyph_row.  Called from produce_glyphs for
   terminal frames if IT->glyph_row != NULL.  IT->char_to_display is
   the character for which to produce glyphs; IT->face_id contains the
   character's face.  Padding glyphs are appended if IT->c has a
   IT->pixel_width > 1.  */

static void
append_glyph (struct it *it)
{
  struct glyph *glyph, *end;
  int i;

  eassert (it->glyph_row);
  glyph = (it->glyph_row->glyphs[it->area]
	   + it->glyph_row->used[it->area]);
  end = it->glyph_row->glyphs[1 + it->area];

  /* If the glyph row is reversed, we need to prepend the glyph rather
     than append it.  */
  if (it->glyph_row->reversed_p && it->area == TEXT_AREA)
    {
      struct glyph *g;
      int move_by = it->pixel_width;

      /* Make room for the new glyphs.  */
      if (move_by > end - glyph) /* don't overstep end of this area */
	move_by = end - glyph;
      for (g = glyph - 1; g >= it->glyph_row->glyphs[it->area]; g--)
	g[move_by] = *g;
      glyph = it->glyph_row->glyphs[it->area];
      end = glyph + move_by;
    }

  /* BIDI Note: we put the glyphs of a "multi-pixel" character left to
     right, even in the REVERSED_P case, since (a) all of its u.ch are
     identical, and (b) the PADDING_P flag needs to be set for the
     leftmost one, because we write to the terminal left-to-right.  */
  for (i = 0;
       i < it->pixel_width && glyph < end;
       ++i)
    {
      glyph->type = CHAR_GLYPH;
      glyph->pixel_width = 1;
      glyph->u.ch = it->char_to_display;
      glyph->frame = it->f;
      glyph->face_id = it->face_id;
      glyph->avoid_cursor_p = it->avoid_cursor_p;
      glyph->multibyte_p = it->multibyte_p;
      glyph->padding_p = i > 0;
      glyph->charpos = CHARPOS (it->position);
      glyph->object = it->object;
      if (it->bidi_p)
	{
	  glyph->resolved_level = it->bidi_it.resolved_level;
	  eassert ((it->bidi_it.type & 7) == it->bidi_it.type);
	  glyph->bidi_type = it->bidi_it.type;
	}
      else
	{
	  glyph->resolved_level = 0;
	  glyph->bidi_type = UNKNOWN_BT;
	}

      ++it->glyph_row->used[it->area];
      ++glyph;
    }
}

/* For external use.  */
void
tty_append_glyph (struct it *it)
{
  append_glyph (it);
}

/* Produce glyphs for the display element described by IT.  *IT
   specifies what we want to produce a glyph for (character, image, ...),
   and where in the glyph matrix we currently are (glyph row and hpos).
   produce_glyphs fills in output fields of *IT with information such as the
   pixel width and height of a character, and maybe output actual glyphs at
   the same time if IT->glyph_row is non-null.  For an overview, see
   the explanation in dispextern.h, before the definition of the
   display_element_type enumeration.

   produce_glyphs also stores the result of glyph width, ascent
   etc. computations in *IT.

   IT->glyph_row may be null, in which case produce_glyphs does not
   actually fill in the glyphs.  This is used in the move_* functions
   in xdisp.c for text width and height computations.

   Callers usually don't call produce_glyphs directly;
   instead they use the macro PRODUCE_GLYPHS.  */

void
produce_glyphs (struct it *it)
{
  /* If a hook is installed, let it do the work.  */

  /* Nothing but characters are supported on terminal frames.  */
  eassert (it->what == IT_CHARACTER
	   || it->what == IT_COMPOSITION
	   || it->what == IT_STRETCH
	   || it->what == IT_GLYPHLESS);

  if (it->what == IT_STRETCH)
    {
      produce_stretch_glyph (it);
      goto done;
    }

  if (it->what == IT_COMPOSITION)
    {
      produce_composite_glyph (it);
      goto done;
    }

  if (it->what == IT_GLYPHLESS)
    {
      produce_glyphless_glyph (it, Qnil);
      goto done;
    }

  if (it->char_to_display >= 040 && it->char_to_display < 0177)
    {
      it->pixel_width = it->nglyphs = 1;
      if (it->glyph_row)
	append_glyph (it);
    }
  else if (it->char_to_display == '\n')
    it->pixel_width = it->nglyphs = 0;
  else if (it->char_to_display == '\t')
    {
      /* wrap-prefix strings are prepended to continuation lines, so
	 the width of tab characters inside should be computed from
	 the start of this screen line rather than as a product of the
	 total width of the physical line being wrapped.  */
      int absolute_x = (it->current_x
			+ (it->string_from_prefix_prop_p
			   /* Subtract the width of the
			      prefix from it->current_x if
			      it exists.  */
			   ? 0 : (it->continuation_lines_width
				  ? (it->continuation_lines_width
				     - it->wrap_prefix_width)
				  : 0)));
      int x0 = absolute_x;
      /* Adjust for line numbers.  */
      if (!NILP (Vdisplay_line_numbers) && it->line_number_produced_p)
	absolute_x -= it->lnum_pixel_width;
      int next_tab_x
	= (((1 + absolute_x + it->tab_width - 1)
	    / it->tab_width)
	   * it->tab_width);
      if (!NILP (Vdisplay_line_numbers) && it->line_number_produced_p)
	next_tab_x += it->lnum_pixel_width;
      int nspaces;

      /* If part of the TAB has been displayed on the previous line
	 which is continued now, continuation_lines_width will have
	 been incremented already by the part that fitted on the
	 continued line.  So, we will get the right number of spaces
	 here.  */
      nspaces = next_tab_x - x0;

      if (it->glyph_row)
	{
	  int n = nspaces;

	  it->char_to_display = ' ';
	  it->pixel_width = it->len = 1;

	  while (n--)
	    append_glyph (it);
	}

      it->pixel_width = nspaces;
      it->nglyphs = nspaces;
    }
  else if (CHAR_BYTE8_P (it->char_to_display))
    {
      /* Coming here means that we must send the raw 8-bit byte as is
	 to the terminal.  Although there's no way to know how many
	 columns it occupies on a screen, it is a good assumption that
	 a single byte code has 1-column width.  */
      it->pixel_width = it->nglyphs = 1;
      if (it->glyph_row)
	append_glyph (it);
    }
  else
    {
      struct terminal *t = FRAME_TERMINAL (it->f);
      Lisp_Object charset_list = t->charset_list, char_glyph;

      if (char_charset (it->char_to_display, charset_list, NULL)
	  && (char_glyph = terminal_glyph_code (t, it->char_to_display),
	      NILP (char_glyph)
	      || (FIXNUMP (char_glyph) && XFIXNUM (char_glyph) >= 0)))
	{
	  it->pixel_width = CHARACTER_WIDTH (it->char_to_display);
	  it->nglyphs = it->pixel_width;
	  if (it->glyph_row)
	    append_glyph (it);
	}
      else
	{
	  Lisp_Object acronym = lookup_glyphless_char_display (-1, it);

	  eassert (it->what == IT_GLYPHLESS);
	  produce_glyphless_glyph (it, acronym);
	}
    }

 done:
  /* Advance current_x by the pixel width as a convenience for
     the caller.  */
  if (it->area == TEXT_AREA)
    {
      it->current_x += it->pixel_width;

      if (it->continuation_lines_width
	  && it->string_from_prefix_prop_p)
	it->wrap_prefix_width = it->current_x;
    }
  it->ascent = it->max_ascent = it->phys_ascent = it->max_phys_ascent = 0;
  it->descent = it->max_descent = it->phys_descent = it->max_phys_descent = 1;
}

/* Append glyphs to IT's glyph_row for the composition IT->cmp_id.
   Called from produce_composite_glyph for terminal frames if
   IT->glyph_row != NULL.  IT->face_id contains the character's
   face.  */

static void
append_composite_glyph (struct it *it)
{
  struct glyph *glyph;

  eassert (it->glyph_row);
  glyph = it->glyph_row->glyphs[it->area] + it->glyph_row->used[it->area];
  if (glyph < it->glyph_row->glyphs[1 + it->area])
    {
      /* If the glyph row is reversed, we need to prepend the glyph
	 rather than append it.  */
      if (it->glyph_row->reversed_p && it->area == TEXT_AREA)
	{
	  struct glyph *g;

	  /* Make room for the new glyph.  */
	  for (g = glyph - 1; g >= it->glyph_row->glyphs[it->area]; g--)
	    g[1] = *g;
	  glyph = it->glyph_row->glyphs[it->area];
	}
      glyph->type = COMPOSITE_GLYPH;
      eassert (it->pixel_width <= SHRT_MAX);
      glyph->pixel_width = it->pixel_width;
      glyph->u.cmp.id = it->cmp_it.id;
      if (it->cmp_it.ch < 0)
	{
	  glyph->u.cmp.automatic = 0;
	  glyph->u.cmp.id = it->cmp_it.id;
	}
      else
	{
	  glyph->u.cmp.automatic = 1;
	  glyph->u.cmp.id = it->cmp_it.id;
	  glyph->slice.cmp.from = it->cmp_it.from;
	  glyph->slice.cmp.to = it->cmp_it.to - 1;
	}

      glyph->avoid_cursor_p = it->avoid_cursor_p;
      glyph->multibyte_p = it->multibyte_p;
      glyph->frame = it->f;
      glyph->face_id = it->face_id;
      glyph->padding_p = false;
      glyph->charpos = CHARPOS (it->position);
      glyph->object = it->object;
      if (it->bidi_p)
	{
	  glyph->resolved_level = it->bidi_it.resolved_level;
	  eassert ((it->bidi_it.type & 7) == it->bidi_it.type);
	  glyph->bidi_type = it->bidi_it.type;
	}
      else
	{
	  glyph->resolved_level = 0;
	  glyph->bidi_type = UNKNOWN_BT;
	}

      ++it->glyph_row->used[it->area];
      ++glyph;
    }
}


/* Produce a composite glyph for iterator IT.  IT->cmp_id is the ID of
   the composition.  We simply produces components of the composition
   assuming that the terminal has a capability to layout/render it
   correctly.  */

static void
produce_composite_glyph (struct it *it)
{
  if (it->cmp_it.ch < 0)
    {
      struct composition *cmp = composition_table[it->cmp_it.id];

      it->pixel_width = cmp->width;
    }
  else
    {
      Lisp_Object gstring = composition_gstring_from_id (it->cmp_it.id);

      it->pixel_width = composition_gstring_width (gstring, it->cmp_it.from,
						   it->cmp_it.to, NULL);
    }
  it->nglyphs = 1;
  if (it->glyph_row)
    append_composite_glyph (it);
}


/* Append a glyph for a glyphless character to IT->glyph_row.  FACE_ID
   is a face ID to be used for the glyph.  What is actually appended
   are glyphs of type CHAR_GLYPH whose characters are in STR (which
   comes from it->nglyphs bytes).  */

static void
append_glyphless_glyph (struct it *it, int face_id, const char *str)
{
  struct glyph *glyph, *end;
  int i;

  eassert (it->glyph_row);
  glyph = it->glyph_row->glyphs[it->area] + it->glyph_row->used[it->area];
  end = it->glyph_row->glyphs[1 + it->area];

  /* If the glyph row is reversed, we need to prepend the glyph rather
     than append it.  */
  if (it->glyph_row->reversed_p && it->area == TEXT_AREA)
    {
      struct glyph *g;
      int move_by = it->pixel_width;

      /* Make room for the new glyphs.  */
      if (move_by > end - glyph) /* don't overstep end of this area */
	move_by = end - glyph;
      for (g = glyph - 1; g >= it->glyph_row->glyphs[it->area]; g--)
	g[move_by] = *g;
      glyph = it->glyph_row->glyphs[it->area];
      end = glyph + move_by;
    }

  if (glyph >= end)
    return;
  glyph->type = CHAR_GLYPH;
  glyph->pixel_width = 1;
  glyph->avoid_cursor_p = it->avoid_cursor_p;
  glyph->multibyte_p = it->multibyte_p;
  glyph->frame = it->f;
  glyph->face_id = face_id;
  glyph->padding_p = false;
  glyph->charpos = CHARPOS (it->position);
  glyph->object = it->object;
  if (it->bidi_p)
    {
      glyph->resolved_level = it->bidi_it.resolved_level;
      eassert ((it->bidi_it.type & 7) == it->bidi_it.type);
      glyph->bidi_type = it->bidi_it.type;
    }
  else
    {
      glyph->resolved_level = 0;
      glyph->bidi_type = UNKNOWN_BT;
    }

  /* BIDI Note: we put the glyphs of characters left to right, even in
     the REVERSED_P case because we write to the terminal
     left-to-right.  */
  for (i = 0; i < it->nglyphs && glyph < end; ++i)
    {
      if (i > 0)
	glyph[0] = glyph[-1];
      glyph->u.ch = str[i];
      ++it->glyph_row->used[it->area];
      ++glyph;
    }
}

/* Produce glyphs for a glyphless character for iterator IT.
   IT->glyphless_method specifies which method to use for displaying
   the character.  See the description of enum
   glyphless_display_method in dispextern.h for the details.

   ACRONYM, if non-nil, is an acronym string for the character.

   The glyphs actually produced are of type CHAR_GLYPH.  */

static void
produce_glyphless_glyph (struct it *it, Lisp_Object acronym)
{
  int len, face_id = merge_glyphless_glyph_face (it);
  char buf[sizeof "\\x" + max (6, (INT_WIDTH + 3) / 4)];
  char const *str = "    ";

  if (it->glyphless_method == GLYPHLESS_DISPLAY_THIN_SPACE)
    {
      /* As there's no way to produce a thin space, we produce a space
	 of canonical width.  */
      len = 1;
    }
  else if (it->glyphless_method == GLYPHLESS_DISPLAY_EMPTY_BOX)
    {
      len = CHARACTER_WIDTH (it->c);
      if (len == 0)
	len = 1;
      else if (len > 4)
	len = 4;
      len = sprintf (buf, "[%.*s]", len, str);
      str = buf;
    }
  else
    {
      if (it->glyphless_method == GLYPHLESS_DISPLAY_ACRONYM)
	{
	  if (! STRINGP (acronym) && CHAR_TABLE_P (Vglyphless_char_display))
	    acronym = CHAR_TABLE_REF (Vglyphless_char_display, it->c);
	  if (CONSP (acronym))
	    acronym = XCDR (acronym);
	  str = STRINGP (acronym) ? SSDATA (acronym) : "";
	  /* A special kludgey feature for single-character acronyms:
	     don't put them in a box, effectively treating them as a
	     replacement character.  */
	  if (STRINGP (acronym) && SCHARS (acronym) == 1)
	    {
	      buf[0] = str[0];
	      len = 1;
	    }
	  else
	    {
	      buf[0] = '[';
	      for (len = 0;
		   len < 6 && str[len] && ASCII_CHAR_P (str[len]); len++)
		buf[1 + len] = str[len];
	      buf[1 + len] = ']';
	      len += 2;
	    }
	}
      else
	{
	  eassert (it->glyphless_method == GLYPHLESS_DISPLAY_HEX_CODE);
	  len = sprintf (buf,
			 (it->c < 0x10000 ? "\\u%04X"
			  : it->c <= MAX_UNICODE_CHAR ? "\\U%06X"
			  : "\\x%06X"),
			 it->c + 0u);
	}
      str = buf;
    }

  it->pixel_width = len;
  it->nglyphs = len;
  if (it->glyph_row)
    append_glyphless_glyph (it, face_id, str);
}


#ifndef HAVE_ANDROID
/***********************************************************************
				TTY Faces
 ***********************************************************************/

/* Value is non-zero if attribute ATTR may be used.  ATTR should be
   one of the enumerators from enum no_color_bit, or a bit set built
   from them.  Some display attributes may not be used together with
   color; the termcap capability `NC' specifies which ones.  */

#define MAY_USE_WITH_COLORS_P(tty, ATTR)                \
  (tty->TN_max_colors > 0				\
   ? (tty->TN_no_color_video & (ATTR)) == 0             \
   : 1)

/* FIX-20261018-guilemacs: M58 imp-3 -- the face-appearance DECISION of
   the three Group A hubs moved to pure procedures of (emacs tty-output):
   tty-face-on-steps, tty-face-off-steps, and tty-capable-p.  C keeps
   every mechanism: the struct face field reads, MAY_USE_WITH_COLORS_P,
   the TS_* / TF_* / TN_* reads, face_tty_specified_color, the strcmp of
   the exit sequences, tparam, the OUTPUT / OUTPUT1 / OUTPUT_IF macros,
   tty_toggle_highlight, the tty->standout_mode clear, and the FILE *
   streams.  C passes plain fixnums only -- one plain list for the
   face-on hub, which needs ten values -- so no Lisp_Object, char *,
   struct face *, or FILE * crosses the seam (docs/kb.org
   =passthrough-leaf-is-not-a-port=, the M42 rule).

   The step protocol extends the M52 vocabulary.  Each step is a plain
   list (TAG ARG...), and C tells the tags apart with
   m52_tty_step_tag_p:

     ("cap1" KEY)          OUTPUT1_IF (tty, m52_cap_string_1 (tty, KEY))
     ("cap" KEY)           OUTPUT_IF  (tty, m52_cap_string_1 (tty, KEY))
     ("tparam" SLOT VALUE) tparam, OUTPUT, xfree
     ("toggle-highlight")  tty_toggle_highlight (tty)
     ("clear-standout")    tty->standout_mode = 0

   OUTPUT and OUTPUT1 are NOT interchangeable: OUTPUT pads with
   FRAME_TOTAL_LINES minus curY, OUTPUT1 uses 1 line, so a swap is a
   silent byte change (brief.org section 5.1 rule 1).  The KEY of a cap step
   MUST match a m52_caps key byte for byte; a mismatch makes
   m52_cap_string_1 return NULL and the hub emits nothing.

   A nil step list (no Scheme runtime) emits nothing.  The inline C
   decision is DELETED, not kept as a second path: a rewire that leaves
   the decision in C is a C dedup, not a port.  */

static Lisp_Object
m58_tty_face_on_scheme (Lisp_Object args)
{
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs tty-output", "tty-face-on-steps");
  return SCM_CALL_1 (proc, args);
}

static Lisp_Object
m58_tty_face_off_scheme (Lisp_Object has_me, Lisp_Object attrs,
			 Lisp_Object has_exit_underline,
			 Lisp_Object me_is_end_standout, Lisp_Object colors,
			 Lisp_Object fg_not_default,
			 Lisp_Object bg_not_default)
{
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs tty-output", "tty-face-off-steps");
  return SCM_CALL_7 (proc, has_me, attrs, has_exit_underline,
		     me_is_end_standout, colors, fg_not_default,
		     bg_not_default);
}

static Lisp_Object
m58_tty_capable_p_scheme (Lisp_Object caps, Lisp_Object presence,
			  Lisp_Object no_color_video, Lisp_Object max_colors)
{
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs tty-output", "tty-capable-p");
  return SCM_CALL_4 (proc, caps, presence, no_color_video, max_colors);
}

/* Run ONE step of a face step list.  This is the MECHANISM only: the
   selection of the step, its order, and its arguments come from
   Scheme.  The tparam slot picks the C-owned capability field; the
   value is the plain fixnum from the step.

   FIX-20261018-guilemacs: F2 of cr.org.  A bare KEY string is NOT a
   step here.  The M52 hubs read a bare string as OUTPUT_IF (the
   frame-padded route); accepting it here as OUTPUT1_IF would give the
   same step list two different meanings in two runners (brief.org
   section 5.1 rule 2).  Every step carries an explicit tag.  */
static void
m58_tty_face_step_run (struct tty_display_info *tty, Lisp_Object step)
{
  int a[2];

  if (m52_tty_step_tag_p (step, "cap1"))
    OUTPUT1_IF (tty, m52_cap_string_1 (tty, CONSP (XCDR (step))
				       ? XCAR (XCDR (step)) : Qnil));
  else if (m52_tty_step_tag_p (step, "cap"))
    OUTPUT_IF (tty, m52_cap_string_1 (tty, CONSP (XCDR (step))
				      ? XCAR (XCDR (step)) : Qnil));
  else if (m52_tty_step_tag_p (step, "tparam"))
    {
      const char *ts = NULL;
      char *p;

      a[0] = a[1] = 0;
      m52_tty_step_args_1 (step, a, 2);
      switch (a[0])
	{
	case 0: ts = tty->TS_set_foreground; break;
	case 1: ts = tty->TS_set_background; break;
	case 2: ts = tty->TF_set_underline_color; break;
	case 3: ts = tty->TF_set_underline_style; break;
	default: break;
	}
      if (ts)
	{
	  p = tparam (ts, NULL, 0, a[1], 0, 0, 0);
	  OUTPUT (tty, p);
	  xfree (p);
	}
    }
  else if (m52_tty_step_tag_p (step, "toggle-highlight"))
    tty_toggle_highlight (tty);
  else if (m52_tty_step_tag_p (step, "clear-standout"))
    tty->standout_mode = 0;
}

/* The plain attrs mask of a face: 1 bold, 2 italic, 4 underline,
   8 strike-through, 16 reverse.  */
static int
m58_face_attrs_mask (struct face *face)
{
  return ((face->tty_bold_p ? 0x01 : 0)
	  | (face->tty_italic_p ? 0x02 : 0)
	  | (face->underline ? 0x04 : 0)
	  | (face->tty_strike_through_p ? 0x08 : 0)
	  | (face->tty_reverse_p ? 0x10 : 0));
}

/* Turn appearances of face FACE_ID on tty frame F on.
   FACE_ID is a realized face ID number, in the face cache.  */

static void
turn_on_face (struct frame *f, struct face *face)
{
  unsigned long fg = face->foreground;
  unsigned long bg = face->background;
  struct tty_display_info *tty = FRAME_TTY (f);
  /* The MAY_USE_WITH_COLORS_P results, evaluated in C: 1 reverse,
     2 bold, 4 italic, 8 underline, 16 strike-through.  */
  int may = ((MAY_USE_WITH_COLORS_P (tty, NC_REVERSE) ? 0x01 : 0)
	     | (MAY_USE_WITH_COLORS_P (tty, NC_BOLD) ? 0x02 : 0)
	     | (MAY_USE_WITH_COLORS_P (tty, NC_ITALIC) ? 0x04 : 0)
	     | (MAY_USE_WITH_COLORS_P (tty, NC_UNDERLINE) ? 0x08 : 0)
	     | (MAY_USE_WITH_COLORS_P (tty, NC_STRIKE_THROUGH) ? 0x10 : 0));
  int colors = tty->TN_max_colors > 0;
  int standout = tty->standout_mode != 0;
  /* Use reverse video if the face specifies that.  The sentinel
     compares stay C.  */
  int reverse
    = (inverse_video
       ? fg == FACE_TTY_DEFAULT_FG_COLOR || bg == FACE_TTY_DEFAULT_BG_COLOR
       : fg == FACE_TTY_DEFAULT_BG_COLOR || bg == FACE_TTY_DEFAULT_FG_COLOR);
  /* FIX-20261018-guilemacs: F1 of cr.org.  Scheme emits
     ("toggle-highlight") from the SAME two plain inputs (the may bit 1
     and the reverse verdict), so C can compute the state AFTER the
     toggle.  The original C called tty_toggle_highlight first and read
     tty->standout_mode afterwards; a stale value swaps the setaf and
     the setab slots for a reverse-video face with an explicit color,
     which is a silent byte change.  */
  int will_toggle = (may & 0x01) && reverse;
  int standout_after = will_toggle ? !standout : standout;
  /* The foreground and background capabilities SWAP while standout is
     on.  C reads both fields and passes the plain verdicts.  */
  const char *fg_slot = standout_after ? tty->TS_set_background
				       : tty->TS_set_foreground;
  const char *bg_slot = standout_after ? tty->TS_set_foreground
				       : tty->TS_set_background;
  /* The capability presence mask: 1 italic, 2 underline-style,
     16 foreground, 32 background, 64 underline-color,
     128 the plain underline route.  */
  int cap = ((tty->TS_enter_italic_mode ? 0x01 : 0)
	     | (tty->TF_set_underline_style ? 0x02 : 0)
	     | (face_tty_specified_color (fg) && fg_slot ? 0x10 : 0)
	     | (face_tty_specified_color (bg) && bg_slot ? 0x20 : 0)
	     | (tty->TF_set_underline_color && face->underline_color
		? 0x40 : 0)
	     | ((face->underline == FACE_UNDERLINE_SINGLE
		 || !tty->TF_set_underline_style) ? 0x80 : 0));

  Lisp_Object steps
    = m58_tty_face_on_scheme
    (scm_list_n (make_fixnum (reverse),
		 make_fixnum (m58_face_attrs_mask (face)),
		 make_fixnum (face->underline),
		 make_fixnum (may),
		 make_fixnum (cap),
		 make_fixnum (colors),
		 make_fixnum (standout_after),
		 /* FIX-20261018-guilemacs: T1 of brief.org section 5.
		    face->foreground, background, and underline_color may hold
		    a FACE_TTY_DEFAULT_* sentinel ((unsigned long) -1 ... -3),
		    which does NOT fit in a fixnum.  The cap mask above already
		    carries the verdict, so a sentinel crosses as 0 and only a
		    specified color crosses as a number.  Every fixnum of the
		    seam obeys this rule.  */
		 make_fixnum (face_tty_specified_color (fg) ? (EMACS_INT) fg : 0),
		 make_fixnum (face_tty_specified_color (bg) ? (EMACS_INT) bg : 0),
		 make_fixnum ((cap & 0x40) ? (EMACS_INT) face->underline_color : 0),
		 SCM_UNDEFINED));

  for (Lisp_Object l = steps; CONSP (l); l = XCDR (l))
    m58_tty_face_step_run (tty, XCAR (l));
}


/* Turn off appearances of face FACE_ID on tty frame F.  */

static void
turn_off_face (struct frame *f, struct face *face)
{
  struct tty_display_info *tty = FRAME_TTY (f);
  int has_me = tty->TS_exit_attribute_mode != NULL;
  /* Capability "me" will turn off appearance modes double-bright,
     half-bright, reverse-video, standout, underline.  It may or may
     not turn off alt-char-mode.  The strcmp stays C.  */
  /* FIX-20261018-guilemacs: T4 of brief.org section 5.  The original C
     ran strcmp (me, se) with NO test on `se', inside the has-me branch.
     The guard below is deliberate: a NULL `se' would make strcmp read
     address 0, which is undefined behavior.  The verdict is 0 when `se'
     is absent, so the ("clear-standout") step is absent too -- the same
     state the emitted bytes produce when no standout was turned on.  */
  int me_is_end_standout
    = (has_me && tty->TS_end_standout_mode
       && strcmp (tty->TS_exit_attribute_mode,
		  tty->TS_end_standout_mode) == 0);
  int fg_not_default
    = (face->foreground != FACE_TTY_DEFAULT_COLOR
       && face->foreground != FACE_TTY_DEFAULT_FG_COLOR);
  int bg_not_default
    = (face->background != FACE_TTY_DEFAULT_COLOR
       && face->background != FACE_TTY_DEFAULT_BG_COLOR);

  Lisp_Object steps
    = m58_tty_face_off_scheme
    (make_fixnum (has_me),
     make_fixnum (m58_face_attrs_mask (face)),
     make_fixnum (tty->TS_exit_underline_mode != NULL),
     make_fixnum (me_is_end_standout),
     make_fixnum (tty->TN_max_colors > 0),
     make_fixnum (fg_not_default),
     make_fixnum (bg_not_default));

  /* Emit the exit sequence BEFORE the color reset (Scheme orders the
     steps).  C keeps the tty->standout_mode clear, as the
     ("clear-standout") step.  */
  for (Lisp_Object l = steps; CONSP (l); l = XCDR (l))
    m58_tty_face_step_run (tty, XCAR (l));
}

#endif /* !HAVE_ANDROID */

/* Return true if the terminal on frame F supports all of the
   capabilities in CAPS simultaneously.  */

bool
tty_capable_p (struct tty_display_info *tty, unsigned int caps)
{
#ifndef HAVE_ANDROID
  /* The verdict runs in Scheme: tty-capable-p takes the requested CAPS
     bits, the plain presence mask, and the TN_no_color_video /
     TN_max_colors values, and returns 0 or 1.  The 7 TTY_CAPABLE_P_TRY
     rows are now ONE table in the Scheme procedure; the inline C chain
     is DELETED (a second copy would be dead policy in C).  The
     presence mask: 1 standout-mode, 2 underline-mode,
     4 underline-style, 8 bold, 16 dim, 32 italic, 64 strike-through.

     FIX-20261018-guilemacs: F3 of cr.org.  There is NO "no Scheme
     runtime" fallback: the module-binding lookup signals an error when
     the module or the binding is absent, so it never yields a
     non-fixnum verdict.  A non-fixnum verdict means a BROKEN module,
     and it answers false: a broken module must not silently claim that
     the terminal is capable.  */
  int presence = ((tty->TS_standout_mode ? 0x01 : 0)
		  | (tty->TS_enter_underline_mode ? 0x02 : 0)
		  | (tty->TF_set_underline_style ? 0x04 : 0)
		  | (tty->TS_enter_bold_mode ? 0x08 : 0)
		  | (tty->TS_enter_dim_mode ? 0x10 : 0)
		  | (tty->TS_enter_italic_mode ? 0x20 : 0)
		  | (tty->TS_enter_strike_through_mode ? 0x40 : 0));
  Lisp_Object verdict
    = m58_tty_capable_p_scheme (make_fixnum (caps),
				make_fixnum (presence),
				make_fixnum (tty->TN_no_color_video),
				make_fixnum (tty->TN_max_colors));

  return (FIXNUMP (verdict) && XFIXNUM (verdict) != 0);
#else
  return false;
#endif
}

/* M58 imp-3, one honest detail: the dim fallback of the italic arm used
   to call emacs_tputs even when TS_enter_dim_mode was NULL.  The
   ("cap1" KEY) route now applies the `if (a)' guard of OUTPUT1_IF
   (:147), so tputs never receives NULL.  No byte changes: the old route
   reached tputs with NULL, and ncurses tputs answers ERR without a byte
   (measured: tputs (NULL) = -1).  The note sits BELOW the hubs.  */

/* FIX-20261005-guilemacs: M48 imp-3 -- the G1 dispatch helpers over the
   terminal-capability policy of (emacs terminal).  The hub reads the
   C-owned field; the module holds the decision; the typed C leaf of
   imp-2 holds the value shape.  Each helper resolves its module
   procedure one time and passes plain values only.  */

static Lisp_Object
tty_display_color_p_scheme (Lisp_Object colors)
{
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs terminal", "term-display-color-p");
  return SCM_CALL_1 (proc, colors);
}

static Lisp_Object
tty_display_color_cells_scheme (Lisp_Object colors)
{
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs terminal", "term-display-color-cells");
  return SCM_CALL_1 (proc, colors);
}

static Lisp_Object
term_type_scheme (Lisp_Object type)
{
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs terminal", "term-type");
  return SCM_CALL_1 (proc, type);
}

static Lisp_Object
controlling_tty_p_scheme (Lisp_Object name, Lisp_Object dev)
{
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs terminal", "term-controlling-tty-p");
  return SCM_CALL_2 (proc, name, dev);
}

/* FIX-20261005-guilemacs: M48 imp-4 -- the G3 dispatch helpers over the
   query / geometry policy of (emacs terminal).  The hub reads the
   C-owned frame fields; the module holds the arithmetic; the typed C
   leaf of imp-2 holds the value shape.  Each helper resolves its module
   procedure one time and passes plain values only.  */

static Lisp_Object
term_frame_geometry_scheme (Lisp_Object left, Lisp_Object top,
			    Lisp_Object width, Lisp_Object height,
			    Lisp_Object ibw, Lisp_Object menu_bar_height,
			    Lisp_Object tab_bar_height,
			    Lisp_Object tool_bar_height,
			    Lisp_Object tool_bar_on_top)
{
  static SCM proc = SCM_UNDEFINED;
  SCM args[9];
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs terminal", "term-frame-geometry");
  args[0] = left; args[1] = top; args[2] = width; args[3] = height;
  args[4] = ibw; args[5] = menu_bar_height; args[6] = tab_bar_height;
  args[7] = tool_bar_height; args[8] = tool_bar_on_top;
  return SCM_CALL_N (proc, args, 9);
}

static Lisp_Object
term_frame_edges_scheme (Lisp_Object left, Lisp_Object top,
			 Lisp_Object width, Lisp_Object height,
			 Lisp_Object ibw, Lisp_Object menu_bar_height,
			 Lisp_Object tab_bar_height,
			 Lisp_Object tool_bar_height,
			 Lisp_Object tool_bar_on_top, Lisp_Object edge_type)
{
  static SCM proc = SCM_UNDEFINED;
  SCM args[10];
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs terminal", "term-frame-edges");
  args[0] = left; args[1] = top; args[2] = width; args[3] = height;
  args[4] = ibw; args[5] = menu_bar_height; args[6] = tab_bar_height;
  args[7] = tool_bar_height; args[8] = tool_bar_on_top; args[9] = edge_type;
  return SCM_CALL_N (proc, args, 10);
}

static Lisp_Object
term_display_pixel_width_scheme (Lisp_Object initial, Lisp_Object width)
{
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs terminal", "term-display-pixel-width");
  return SCM_CALL_2 (proc, initial, width);
}

static Lisp_Object
term_display_pixel_height_scheme (Lisp_Object initial, Lisp_Object height)
{
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs terminal", "term-display-pixel-height");
  return SCM_CALL_2 (proc, initial, height);
}

/* Return non-zero if the terminal is capable to display colors.  */

DEFUN ("tty-display-color-p", Ftty_display_color_p, Stty_display_color_p,
       0, 1, 0,
       doc: /* Return non-nil if the tty device TERMINAL can display colors.

TERMINAL can be a terminal object, a frame, or nil (meaning the
selected frame's terminal).  This function always returns nil if
TERMINAL does not refer to a text terminal.  */)
  (Lisp_Object terminal)
{
  struct terminal *t = decode_tty_terminal (terminal);
  Lisp_Object colors = t ? make_fixnum (t->display_info.tty->TN_max_colors)
                         : Qnil;

  return tty_display_color_p_scheme (colors);
}

/* Return the number of supported colors.  */
DEFUN ("tty-display-color-cells", Ftty_display_color_cells,
       Stty_display_color_cells, 0, 1, 0,
       doc: /* Return the number of colors supported by the tty device TERMINAL.

TERMINAL can be a terminal object, a frame, or nil (meaning the
selected frame's terminal).  This function always returns 0 if
TERMINAL does not refer to a text terminal.  */)
  (Lisp_Object terminal)
{
  struct terminal *t = decode_tty_terminal (terminal);
  Lisp_Object colors = t ? make_fixnum (t->display_info.tty->TN_max_colors)
                         : Qnil;

  return tty_display_color_cells_scheme (colors);
}

#if !defined DOS_NT && !defined HAVE_ANDROID

/* Declare here rather than in the function, as in the rest of Emacs,
   to work around an HPUX compiler bug (?). See
   https://lists.gnu.org/r/emacs-devel/2007-08/msg00410.html  */
static int default_max_colors;
static int default_no_color_video;
static char *default_orig_pair;
static char *default_set_foreground;
static char *default_set_background;

/* FIX-20261019-guilemacs: M58 imp-4 -- the Group B color-mode
   DECISION moved to pure procedures of (emacs tty-output):

     tty-color-mode-tag        the mode canonicalization and the
                               -1 / 0 / 8 scheme choice of
                               tty_setup_colors
     tty-color-mode-changed-p  the change gate of set_tty_color_mode

   C keeps every mechanism: the 3 cap strings (including the TERMINFO
   variants of the 8-color scheme), every TN_* and TS_* write, the
   static default slots, tty_default_color_capabilities save / restore,
   the f->param_alist and tty-color-mode-alist resolve, the
   TYPE_RANGED_FIXNUMP narrowing, the RAW previous_color_mode store,
   safe_calln (Qtty_set_up_initial_frame_faces), and the FILE *
   streams.  C resolves each Lisp value to a plain int and passes
   make_fixnum, so no Lisp_Object, struct frame *, or
   struct tty_display_info * crosses the seam (docs/kb.org
   =passthrough-leaf-is-not-a-port=).

   The inline C decision is DELETED, not kept as a second path: a
   rewire that leaves the decision in C is a C dedup, not a port.  An
   unknown tag, which means a broken or missing module, emits nothing
   and raises no error (the turn_off_face rule).  */

static Lisp_Object
m58_tty_color_mode_tag_scheme (Lisp_Object mode)
{
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs tty-output", "tty-color-mode-tag");
  return SCM_CALL_1 (proc, mode);
}

static Lisp_Object
m58_tty_color_mode_changed_scheme (Lisp_Object mode, Lisp_Object previous)
{
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs tty-output",
			     "tty-color-mode-changed-p");
  return SCM_CALL_2 (proc, mode, previous);
}

/* Save or restore the default color-related capabilities of this
   terminal.  */
static void
tty_default_color_capabilities (struct tty_display_info *tty, bool save)
{

  if (save)
    {
      dupstring (&default_orig_pair, tty->TS_orig_pair);
      dupstring (&default_set_foreground, tty->TS_set_foreground);
      dupstring (&default_set_background, tty->TS_set_background);
      default_max_colors = tty->TN_max_colors;
      default_no_color_video = tty->TN_no_color_video;
    }
  else
    {
      tty->TS_orig_pair = default_orig_pair;
      tty->TS_set_foreground = default_set_foreground;
      tty->TS_set_background = default_set_background;
      tty->TN_max_colors = default_max_colors;
      tty->TN_no_color_video = default_no_color_video;
    }
}

/* Setup one of the standard tty color schemes according to MODE.
   MODE's value is generally the number of colors which we want to
   support; zero means set up for the default capabilities, the ones
   we saw at init_tty time; -1 means turn off color support.  */
static void
tty_setup_colors (struct tty_display_info *tty, int mode)
{
  /* FIX-20261019-guilemacs: the canonicalization and the scheme choice
     come from tty-color-mode-tag.  The body below is the MECHANISM
     only: the cap strings and the TN_* / TS_* writes stay C.  */
  Lisp_Object tag = m58_tty_color_mode_tag_scheme (make_fixnum (mode));

  if (m52_tty_step_tag_p (tag, "none"))
    {
      tty->TN_max_colors = 0;
      tty->TN_no_color_video = 0;
      tty->TS_set_foreground = tty->TS_set_background = tty->TS_orig_pair = NULL;
    }
  else if (m52_tty_step_tag_p (tag, "ansi-8"))
    {
      tty->TS_orig_pair = "\033[0m";
#ifdef TERMINFO
      tty->TS_set_foreground = "\033[3%p1%dm";
      tty->TS_set_background = "\033[4%p1%dm";
#else
      tty->TS_set_foreground = "\033[3%dm";
      tty->TS_set_background = "\033[4%dm";
#endif
      tty->TN_max_colors = 8;
      tty->TN_no_color_video = 0;
    }
  else if (m52_tty_step_tag_p (tag, "default"))
    tty_default_color_capabilities (tty, 0);
  /* An unknown tag means a broken or missing module.  Emit nothing and
     raise no error, as turn_off_face does: the terminal keeps its
     current capabilities.  */
}

void
set_tty_color_mode (struct tty_display_info *tty, struct frame *f)
{
  Lisp_Object tem, val;
  Lisp_Object color_mode;
  int mode;
  Lisp_Object tty_color_mode_alist
    = Fintern_soft (build_string ("tty-color-mode-alist"), Qnil);

  tem = assq_no_quit (Qtty_color_mode, f->param_alist);
  val = CONSP (tem) ? XCDR (tem) : Qnil;

  if (FIXNUMP (val))
    color_mode = val;
  else if (SYMBOLP (tty_color_mode_alist))
    {
      tem = Fassq (val, Fsymbol_value (tty_color_mode_alist));
      color_mode = CONSP (tem) ? XCDR (tem) : Qnil;
    }
  else
    color_mode = Qnil;

  mode = TYPE_RANGED_FIXNUMP (int, color_mode) ? XFIXNUM (color_mode) : 0;

  /* FIX-20261019-guilemacs: the change gate comes from
     tty-color-mode-changed-p, which compares the RAW modes.  A
     non-fixnum verdict means a broken module; a broken module answers
     "no change", so C writes no capability and raises no error.  */
  {
    Lisp_Object changed
      = m58_tty_color_mode_changed_scheme (make_fixnum (mode),
					   make_fixnum (tty->previous_color_mode));

    if (FIXNUMP (changed) && XFIXNUM (changed) != 0)
      {
	tty->previous_color_mode = mode;
	tty_setup_colors (tty , mode);
	/*  This recomputes all the faces given the new color definitions.  */
	safe_calln (Qtty_set_up_initial_frame_faces);
      }
  }
}

#endif /* !DOS_NT && !HAVE_ANDROID */

char *
tty_type_name (Lisp_Object terminal)
{
  struct terminal *t = decode_tty_terminal (terminal);

  return t? t->display_info.tty->type: NULL;
}

DEFUN ("tty-type", Ftty_type, Stty_type, 0, 1, 0,
       doc: /* Return the type of the tty device that TERMINAL uses.
Returns nil if TERMINAL is not on a tty device.

TERMINAL can be a terminal object, a frame, or nil (meaning the
selected frame's terminal).  */)
  (Lisp_Object terminal)
{
  char *name = tty_type_name (terminal);

  return term_type_scheme (name ? build_string (name) : Qnil);
}

DEFUN ("controlling-tty-p", Fcontrolling_tty_p, Scontrolling_tty_p, 0, 1, 0,
       doc: /* Return non-nil if TERMINAL is the controlling tty of the Emacs process.

TERMINAL can be a terminal object, a frame, or nil (meaning the
selected frame's terminal).  This function always returns nil if
TERMINAL is not on a tty device.  */)
  (Lisp_Object terminal)
{
  struct terminal *t = decode_tty_terminal (terminal);
  Lisp_Object name = (t && t->display_info.tty->name)
                     ? build_string (t->display_info.tty->name) : Qnil;
  Lisp_Object dev = (t && t->display_info.tty->name)
                    ? build_string (dev_tty) : Qnil;

  return controlling_tty_p_scheme (name, dev);
}

DEFUN ("tty-no-underline", Ftty_no_underline, Stty_no_underline, 0, 1, 0,
       doc: /* Declare that the tty used by TERMINAL does not handle underlining.
This is used to override the terminfo data, for certain terminals that
do not really do underlining, but say that they do.  This function has
no effect if used on a non-tty terminal.

TERMINAL can be a terminal object, a frame or nil (meaning the
selected frame's terminal).  This function always returns nil if
TERMINAL does not refer to a text terminal.  */)
  (Lisp_Object terminal)
{
  struct terminal *t = decode_live_terminal (terminal);

  if (t->type == output_termcap)
    t->display_info.tty->TS_enter_underline_mode = 0;
  return Qnil;
}

DEFUN ("tty-top-frame", Ftty_top_frame, Stty_top_frame, 0, 1, 0,
       doc: /* Return the topmost terminal frame on TERMINAL.
TERMINAL can be a terminal object, a frame or nil (meaning the
selected frame's terminal).  This function returns nil if TERMINAL
does not refer to a text terminal.  Otherwise, it returns the
top-most frame on the text terminal.  */)
  (Lisp_Object terminal)
{
  struct terminal *t = decode_live_terminal (terminal);

  if (t->type == output_termcap)
    return t->display_info.tty->top_frame;
  return Qnil;
}



DEFUN ("suspend-tty", Fsuspend_tty, Ssuspend_tty, 0, 1, 0,
       doc: /* Suspend the terminal device TTY.

The device is restored to its default state, and Emacs ceases all
access to the tty device.  Frames that use the device are not deleted,
but input is not read from them and if they change, their display is
not updated.

TTY may be a terminal object, a frame, or nil for the terminal device
of the currently selected frame.

This function runs `suspend-tty-functions' after suspending the
device.  The functions are run with one arg, the id of the suspended
terminal device.

`suspend-tty' does nothing if it is called on a device that is already
suspended.

A suspended tty may be resumed by calling `resume-tty' on it.  */)
  (Lisp_Object tty)
{
#ifndef HAVE_ANDROID
  struct terminal *t = decode_tty_terminal (tty);
  FILE *f;

  if (!t)
    error ("Attempt to suspend a non-text terminal device");

  f = t->display_info.tty->input;

  if (f)
    {
      /* First run `suspend-tty-functions' and then clean up the tty
	 state because `suspend-tty-functions' might need to change
	 the tty state.  */
      Lisp_Object term;
      XSETTERMINAL (term, t);
      CALLN (Frun_hook_with_args, Qsuspend_tty_functions, term);

      reset_sys_modes (t->display_info.tty);
      delete_keyboard_wait_descriptor (fileno (f));

#ifndef MSDOS
      if (f != t->display_info.tty->output)
        emacs_fclose (t->display_info.tty->output);
      emacs_fclose (f);
#endif /* !MSDOS */

      t->display_info.tty->input = 0;
      t->display_info.tty->output = 0;

      if (FRAMEP (t->display_info.tty->top_frame))
	{
	  struct frame *top = XFRAME (t->display_info.tty->top_frame);
	  SET_FRAME_VISIBLE (root_frame (top), false);
	}
    }

  /* Clear display hooks to prevent further output.  */
  clear_tty_hooks (t);
#else /* HAVE_ANDROID */
  /* Android doesn't support TTY terminal devices, so unconditionally
     signal.  */
  error ("Attempt to suspend a non-text terminal device");
#endif /* !HAVE_ANDROID */

  return Qnil;
}

DEFUN ("resume-tty", Fresume_tty, Sresume_tty, 0, 1, 0,
       doc: /* Resume the previously suspended terminal device TTY.
The terminal is opened and reinitialized.  Frames that are on the
suspended terminal are revived.

It is an error to resume a terminal while another terminal is active
on the same device.

This function runs `resume-tty-functions' after resuming the terminal.
The functions are run with one arg, the id of the resumed terminal
device.

`resume-tty' does nothing if it is called on a device that is not
suspended.

TTY may be a terminal object, a frame, or nil (meaning the selected
frame's terminal). */)
  (Lisp_Object tty)
{
#ifndef HAVE_ANDROID
  struct terminal *t;
  int fd;

  t = decode_tty_terminal (tty);

  if (!t)
    error ("Attempt to resume a non-text terminal device");

  if (!t->display_info.tty->input)
    {
      if (get_named_terminal (t->display_info.tty->name))
        error ("Cannot resume display while another display is active on the same device");

#ifdef MSDOS
      t->display_info.tty->output = stdout;
      t->display_info.tty->input  = stdin;
#else  /* !MSDOS */
      fd = emacs_open (t->display_info.tty->name, O_RDWR | O_NOCTTY, 0);
      t->display_info.tty->input = t->display_info.tty->output
	= fd < 0 ? 0 : emacs_fdopen (fd, "w+");

      if (! t->display_info.tty->input)
	{
	  int open_errno = errno;
	  emacs_close (fd);
	  report_file_errno ("Cannot reopen tty device",
			     build_string (t->display_info.tty->name),
			     open_errno);
	}

      if (!O_IGNORE_CTTY && strcmp (t->display_info.tty->name, dev_tty) != 0)
        dissociate_if_controlling_tty (fd);
#endif /* MSDOS */

      add_keyboard_wait_descriptor (fd);

      if (FRAMEP (t->display_info.tty->top_frame))
	{
	  struct frame *top = XFRAME (t->display_info.tty->top_frame);
	  struct frame *f = root_frame (top);
	  int width, height;
	  int old_height = FRAME_COLS (f);
	  int old_width = FRAME_TOTAL_LINES (f);

	  /* Check if terminal/window size has changed while the frame
	     was suspended.  */
	  get_tty_size (fileno (t->display_info.tty->input), &width, &height);
	  if (width != old_width || height != old_height)
	    change_frame_size (f, width, height, false, false, false);
	  SET_FRAME_VISIBLE (f, true);
	}

      set_tty_hooks (t);
      init_sys_modes (t->display_info.tty);

      /* Run `resume-tty-functions'.  */
      Lisp_Object term;
      XSETTERMINAL (term, t);
      CALLN (Frun_hook_with_args, Qresume_tty_functions, term);
    }

  set_tty_hooks (t);
#else /* HAVE_ANDROID */
  /* Android doesn't support TTY terminal devices, so unconditionally
     signal.  */
  error ("Attempt to suspend a non-text terminal device");
#endif /* !HAVE_ANDROID */

  return Qnil;
}

#ifndef HAVE_ANDROID

DEFUN ("tty--set-output-buffer-size", Ftty__set_output_buffer_size,
       Stty__set_output_buffer_size, 1, 2, 0, doc:
       /* Set the output buffer size for a TTY.

SIZE zero means use the system's default value.  If SIZE is
non-zero, this also avoids flushing the output stream.

TTY may be a terminal object, a frame, or nil (meaning the selected
frame's terminal).

This function temporarily suspends and resumes the terminal
device.  */)
  (Lisp_Object size, Lisp_Object tty)
{
  if (!TYPE_RANGED_FIXNUMP (size_t, size))
    error ("Invalid output buffer size");
  Fsuspend_tty (tty);
  struct terminal *terminal = decode_tty_terminal (tty);
  terminal->display_info.tty->output_buffer_size = XFIXNUM (size);
  return Fresume_tty (tty);
}

DEFUN ("tty--output-buffer-size", Ftty__output_buffer_size,
       Stty__output_buffer_size, 0, 1, 0, doc:
       /* Return the output buffer size of TTY.

TTY may be a terminal object, a frame, or nil (meaning the selected
frame's terminal).

A value of zero means TTY uses the system's default value.  */)
  (Lisp_Object tty)
{
  struct terminal *terminal = decode_tty_terminal (tty);
  if (terminal)
    return make_fixnum (terminal->display_info.tty->output_buffer_size);
  error ("Not a tty terminal");
}

#endif /* !HAVE_ANDROID */


/***********************************************************************
			       Mouse
 ***********************************************************************/

#if !defined DOS_NT && !defined HAVE_ANDROID

/* Implementation of draw_row_with_mouse_face for TTY/GPM and macOS.  */
void
tty_draw_row_with_mouse_face (struct window *w, struct glyph_row *row,
			      int start_hpos, int end_hpos,
			      enum draw_glyphs_face draw)
{
  int nglyphs = end_hpos - start_hpos;
  struct frame *f = XFRAME (WINDOW_FRAME (w));
  struct tty_display_info *tty = FRAME_TTY (f);
  int face_id = tty->mouse_highlight.mouse_face_face_id;

  if (end_hpos >= row->used[TEXT_AREA])
    nglyphs = row->used[TEXT_AREA] - start_hpos;

  int pos_y = row->y + WINDOW_TOP_EDGE_Y (w);
  int pos_x = row->used[LEFT_MARGIN_AREA] + start_hpos + WINDOW_LEFT_EDGE_X (w);

  /* Save current cursor coordinates.  */
  int save_y = curY (tty);
  int save_x = curX (tty);
  cursor_to (f, pos_y, pos_x);

  if (draw == DRAW_MOUSE_FACE)
    {
      struct glyph *glyph = row->glyphs[TEXT_AREA] + start_hpos;
      struct face *face = FACE_FROM_ID (f, face_id);
      tty_write_glyphs_with_face (f, glyph, nglyphs, face);
    }
  else if (draw == DRAW_NORMAL_TEXT)
    write_glyphs (f, row->glyphs[TEXT_AREA] + start_hpos, nglyphs);

  cursor_to (f, save_y, save_x);
}

#endif

static Lisp_Object
tty_frame_at (int x, int y)
{
  for (Lisp_Object frames = Ftty_frame_list_z_order (Qnil);
       !NILP (frames);
       frames = Fcdr (frames))
    {
      Lisp_Object frame = Fcar (frames);
      struct frame *f = XFRAME (frame);

      if (f->left_pos <= x && x < f->left_pos + f->pixel_width &&
	  f->top_pos <= y && y < f->top_pos + f->pixel_height)
	return frame;
    }

  return Qnil;
}

DEFUN ("tty-frame-at", Ftty_frame_at, Stty_frame_at,
       2, 2, 0,
       doc: /* Return tty frame containing pixel position X, Y.  */)
  (Lisp_Object x, Lisp_Object y)
{
  if (! FIXNUMP (x) || ! FIXNUMP (y))
    /* Coordinates this big can not correspond to any frame.  */
    return Qnil;

  return tty_frame_at (XFIXNUM (x), XFIXNUM (y));
}

#ifdef HAVE_GPM

void
term_mouse_moveto (int x, int y)
{
  /* TODO: how to set mouse position?
  const char *name;
  int fd;
  name = (const char *) ttyname (0);
  fd = emacs_open (name, O_WRONLY, 0);
     SOME_FUNCTION (x, y, fd);
  emacs_close (fd);
  last_mouse_x = x;
  last_mouse_y = y;  */
}

/* Return the current time, as a Time value.  Wrap around on overflow.  */
static Time
current_Time (void)
{
  struct timespec now = current_timespec ();
  Time s_1000 = now.tv_sec;
  s_1000 *= 1000;
  Time ms = now.tv_nsec / 1000000;
  return s_1000 + ms;
}

/* Return the current position of the mouse.

   Set *f to the frame the mouse is in, or zero if the mouse is in no
   Emacs frame.  If it is set to zero, all the other arguments are
   garbage.

   Set *bar_window to Qnil, and *x and *y to the column and
   row of the character cell the mouse is over.

   Set *timeptr to the time the mouse was at the returned position.

   This clears mouse_moved until the next motion
   event arrives.  */
static void
term_mouse_position (struct frame **fp, int insist, Lisp_Object *bar_window,
		     enum scroll_bar_part *part, Lisp_Object *x,
		     Lisp_Object *y, Time *timeptr)
{
  /* If we've gotten no GPM mouse events yet, last_mouse_frame won't be
     set.  Perhaps `gpm-mouse-mode' was never active.  */
  if (!FRAMEP (last_mouse_frame))
    return;

  *fp = XFRAME (last_mouse_frame);
  if (!FRAME_LIVE_P (*fp))
    return;

  (*fp)->mouse_moved = 0;

  *bar_window = Qnil;
  *part = scroll_bar_above_handle;

  XSETINT (*x, last_mouse_x);
  XSETINT (*y, last_mouse_y);
  *timeptr = current_Time ();
}

/* Prepare a mouse-event in *RESULT for placement in the input queue.

   If the event is a button press, then note that we have grabbed
   the mouse.  */

static Lisp_Object
term_mouse_click (struct input_event *result, Gpm_Event *event,
		  struct frame *f)
{
  int i, j;

  result->kind = MOUSE_CLICK_EVENT;
  for (i = 0, j = GPM_B_LEFT; i < 3; i++, j >>= 1 )
    {
      if (event->buttons & j) {
	result->code = i; /* button number */
	break;
      }
    }
  result->timestamp = current_Time ();

  if (event->type & GPM_UP)
    result->modifiers = up_modifier;
  else if (event->type & GPM_DOWN)
    result->modifiers = down_modifier;
  else
    result->modifiers = 0;

  if (event->type & GPM_SINGLE)
    result->modifiers |= click_modifier;

  if (event->type & GPM_DOUBLE)
    result->modifiers |= double_modifier;

  if (event->type & GPM_TRIPLE)
    result->modifiers |= triple_modifier;

  if (event->type & GPM_DRAG)
    result->modifiers |= drag_modifier;

  if (!(event->type & (GPM_MOVE | GPM_DRAG))) {

    /* 1 << KG_SHIFT */
    if (event->modifiers & (1 << 0))
      result->modifiers |= shift_modifier;

    /* 1 << KG_CTRL */
    if (event->modifiers & (1 << 2))
      result->modifiers |= ctrl_modifier;

    /* 1 << KG_ALT || KG_ALTGR */
    if (event->modifiers & (1 << 3)
	|| event->modifiers & (1 << 1))
      result->modifiers |= meta_modifier;
  }

  XSETINT (result->x, event->x);
  XSETINT (result->y, event->y);
  XSETFRAME (result->frame_or_window, f);
  result->arg = Qnil;
  return Qnil;
}

int
handle_one_term_event (struct tty_display_info *tty, const Gpm_Event *event_in)
{
  Lisp_Object frame = tty_frame_at (event_in->x, event_in->y);
  struct frame *f = decode_live_frame (frame);
  Gpm_Event event = *event_in;
  event.x -= f->left_pos;
  event.y -= f->top_pos;

  struct input_event ie;
  int count = 0;

  EVENT_INIT (ie);
  ie.kind = NO_EVENT;
  ie.arg = Qnil;

  if (event.type & (GPM_MOVE | GPM_DRAG))
    {
      /* The pointer must be drawn using screen coordinates (x,y), not
	 frame coordinates.  Use event_in which has an unmodified event
	 directly from GPM.  */
      Gpm_DrawPointer (event_in->x, event_in->y, fileno (tty->output));

      /* Has the mouse moved off the glyph it was on at the last
         sighting?  */
      if (event.x != last_mouse_x || event.y != last_mouse_y)
        {
          /* FIXME: These four lines can not be moved into
             update_mouse_position unless xterm-mouse gets updated to
             generate mouse events via C code.  See
             https://lists.gnu.org/archive/html/emacs-devel/2020-11/msg00163.html */
          last_mouse_frame = frame;
          last_mouse_x = event.x;
          last_mouse_y = event.y;
          f->mouse_moved = 1;

          count += update_mouse_position (f, event.x, event.y);
        }
    }
  else
    {
      f->mouse_moved = 0;
      term_mouse_click (&ie, &event, f);
      ie.arg = tty_handle_tab_bar_click (f, event.x, event.y,
					 (ie.modifiers & down_modifier) != 0, &ie);
      kbd_buffer_store_event (&ie);
      count++;
    }

  return count;
}

DEFUN ("gpm-mouse-start", Fgpm_mouse_start, Sgpm_mouse_start,
       0, 0, 0,
       doc: /* Open a connection to Gpm.
Gpm-mouse can only be activated for one tty at a time.  */)
  (void)
{
  struct frame *f = SELECTED_FRAME ();
  struct tty_display_info *tty
    = ((f)->output_method == output_termcap
       ? (f)->terminal->display_info.tty : NULL);
  Gpm_Connect connection;

  if (!tty)
    error ("Gpm-mouse only works in the GNU/Linux console");
  if (gpm_tty == tty)
    return Qnil;		/* Already activated, nothing to do.  */
  if (gpm_tty)
    error ("Gpm-mouse can only be activated for one tty at a time");

  connection.eventMask = ~0;
  connection.defaultMask = ~GPM_HARD;
  connection.maxMod = ~0;
  connection.minMod = 0;
  gpm_zerobased = 1;

  if (Gpm_Open (&connection, 0) < 0)
    error ("Gpm-mouse failed to connect to the gpm daemon");
  else
    {
      gpm_tty = tty;
      /* `init_sys_modes' arranges for mouse movements sent through gpm_fd
	 to generate SIGIOs.  Apparently we need to call reset_sys_modes
	 before calling init_sys_modes.  */
      reset_sys_modes (tty);
      init_sys_modes (tty);
      add_gpm_wait_descriptor (gpm_fd);
      return Qnil;
    }
}

void
close_gpm (int fd)
{
  if (fd >= 0)
    delete_gpm_wait_descriptor (fd);
  while (Gpm_Close()); /* close all the stack */
  gpm_tty = NULL;
}

DEFUN ("gpm-mouse-stop", Fgpm_mouse_stop, Sgpm_mouse_stop,
       0, 0, 0,
       doc: /* Close a connection to Gpm.  */)
  (void)
{
  struct frame *f = SELECTED_FRAME ();
  struct tty_display_info *tty
    = ((f)->output_method == output_termcap
       ? (f)->terminal->display_info.tty : NULL);

  if (!tty || gpm_tty != tty)
    return Qnil;       /* Not activated on this terminal, nothing to do.  */

  close_gpm (gpm_fd);
  return Qnil;
}
#endif /* HAVE_GPM */


/***********************************************************************
			       Menus
 ***********************************************************************/

#if !defined (MSDOS) && !defined HAVE_ANDROID

/* TTY menu implementation and main ideas are borrowed from msdos.c.

   However, unlike on MSDOS, where the menu text is drawn directly to
   the display video memory, on a TTY we use display_string (see
   display_tty_menu_item in xdisp.c) to put the glyphs produced from
   the menu items into the frame's 'desired_matrix' glyph matrix, and
   then call update_frame_with_menu to deliver the results to the
   glass.  The previous contents of the screen, in the form of the
   current_matrix, is stashed away, and used to restore screen
   contents when the menu selection changes or when the final
   selection is made and the menu should be popped down.

   The idea of this implementation was suggested by Gerd Moellmann.  */

#define TTYM_FAILURE -1
#define TTYM_SUCCESS 1
#define TTYM_NO_SELECT 2
#define TTYM_IA_SELECT 3
#define TTYM_NEXT 4
#define TTYM_PREV 5

/* These hold text of the current and the previous menu help messages.  */
static const char *menu_help_message, *prev_menu_help_message;
/* Pane number and item number of the menu item which generated the
   last menu help message.  */
static int menu_help_paneno, menu_help_itemno;

typedef struct tty_menu_struct
{
  int count;
  char **text;
  struct tty_menu_struct **submenu;
  int *panenumber; /* Also used as enabled flag.  */
  ptrdiff_t allocated;
  int panecount;
  int width;
  const char **help_text;
} tty_menu;

/* Create a brand new menu structure.  */

static tty_menu * ATTRIBUTE_MALLOC
tty_menu_create (void)
{
  return xzalloc (sizeof *tty_menu_create ());
}

/* Allocate some (more) memory for MENU ensuring that there is room for one
   more item.  */

static void
tty_menu_make_room (tty_menu *menu)
{
  if (menu->allocated == menu->count)
    {
      ptrdiff_t allocated = menu->allocated;
      menu->text = xpalloc (menu->text, &allocated, 1, -1, sizeof *menu->text);
      menu->text = xrealloc (menu->text, allocated * sizeof *menu->text);
      menu->submenu = xrealloc (menu->submenu,
				allocated * sizeof *menu->submenu);
      menu->panenumber = xrealloc (menu->panenumber,
				   allocated * sizeof *menu->panenumber);
      menu->help_text = xrealloc (menu->help_text,
				  allocated * sizeof *menu->help_text);
      menu->allocated = allocated;
    }
}

/* Search the given menu structure for a given pane number.  */

static tty_menu *
tty_menu_search_pane (tty_menu *menu, int pane)
{
  int i;
  tty_menu *try;

  for (i = 0; i < menu->count; i++)
    if (menu->submenu[i])
      {
	if (pane == menu->panenumber[i])
	  return menu->submenu[i];
	try = tty_menu_search_pane (menu->submenu[i], pane);
	if (try)
	  return try;
      }
  return (tty_menu *) 0;
}

/* Determine how much screen space a given menu needs.  */

static void
tty_menu_calc_size (tty_menu *menu, int *width, int *height)
{
  int i, h2, w2, maxsubwidth, maxheight;

  maxsubwidth = menu->width;
  maxheight = menu->count;
  for (i = 0; i < menu->count; i++)
    {
      if (menu->submenu[i])
	{
	  tty_menu_calc_size (menu->submenu[i], &w2, &h2);
	  if (w2 > maxsubwidth) maxsubwidth = w2;
	  if (i + h2 > maxheight) maxheight = i + h2;
	}
    }
  *width = maxsubwidth;
  *height = maxheight;
}

static void
mouse_get_xy (int *x, int *y)
{
  Lisp_Object lmx = Qnil, lmy = Qnil;
  Lisp_Object mouse = mouse_position (tty_menu_calls_mouse_position_function);

  if (EQ (selected_frame, XCAR (mouse)))
    {
      lmx = XCAR (XCDR (mouse));
      lmy = XCDR (XCDR (mouse));
    }

  if (!NILP (lmx))
    {
      *x = XFIXNUM (lmx);
      *y = XFIXNUM (lmy);
    }
}

/* Display MENU at (X,Y) using FACES, starting with FIRST_ITEM
   (zero-based).  */

static void
tty_menu_display (tty_menu *menu, int x, int y, int pn, int *faces,
		  int mx, int my, int first_item, bool disp_help)
{
  int i, face, width, enabled, mousehere, row, col;
  struct frame *sf = SELECTED_FRAME ();
  struct tty_display_info *tty = FRAME_TTY (sf);
  /* Don't try to display more menu items than the console can display
     using the available screen lines.  Exclude the echo area line, as
     it will be overwritten by the help-echo anyway.  */
  int max_items = min (menu->count - first_item, FRAME_TOTAL_LINES (sf) - 1 - y);

  menu_help_message = NULL;

  width = menu->width;
  col = cursorX (tty);
  row = cursorY (tty);
  for (i = 0; i < max_items; i++)
    {
      int max_width = width + 2; /* +2 for padding blanks on each side */
      int j = i + first_item;

      if (menu->submenu[j])
	max_width += 2;	/* for displaying " >" after the item */
      enabled
	= (!menu->submenu[j] && menu->panenumber[j]) || (menu->submenu[j]);
      mousehere = (y + i == my && x <= mx && mx < x + max_width);
      face = faces[enabled + mousehere * 2];
      /* Display the menu help string for the i-th menu item even if
	 the menu item is currently disabled.  That's what the GUI
	 code does.  */
      if (disp_help && enabled + mousehere * 2 >= 2)
	{
	  menu_help_message = menu->help_text[j];
	  menu_help_paneno = pn - 1;
	  menu_help_itemno = j;
	}
      /* Take note of the coordinates of the active menu item, to
	 display the cursor there.  */
      if (mousehere)
	{
	  row = y + i;
	  col = x;
	}
      display_tty_menu_item (menu->text[j], max_width, face, x, y + i,
			     menu->submenu[j] != NULL);
    }
  update_frame_with_menu (sf, row, col);
}

/* --------------------------- X Menu emulation ---------------------- */

/* Create a new pane and place it on the outer-most level.  */

static int
tty_menu_add_pane (tty_menu *menu, const char *txt)
{
  int len;

  tty_menu_make_room (menu);
  menu->submenu[menu->count] = tty_menu_create ();
  menu->text[menu->count] = (char *)txt;
  menu->panenumber[menu->count] = ++menu->panecount;
  menu->help_text[menu->count] = NULL;
  menu->count++;

  /* Update the menu width, if necessary.  */
  len = menu_item_width ((const unsigned char *) txt);
  if (len > menu->width)
    menu->width = len;

  return menu->panecount;
}

/* Create a new item in a menu pane.  */

static bool
tty_menu_add_selection (tty_menu *menu, int pane,
			char *txt, bool enable, char const *help_text)
{
  int len;

  if (pane)
    {
      menu = tty_menu_search_pane (menu, pane);
      if (! menu)
	return 0;
    }
  tty_menu_make_room (menu);
  menu->submenu[menu->count] = (tty_menu *) 0;
  menu->text[menu->count] = txt;
  menu->panenumber[menu->count] = enable;
  menu->help_text[menu->count] = help_text;
  menu->count++;

  /* Update the menu width, if necessary.  */
  len = menu_item_width ((const unsigned char *) txt);
  if (len > menu->width)
    menu->width = len;

  return 1;
}

/* Decide where the menu would be placed if requested at (X,Y).  */

static void
tty_menu_locate (tty_menu *menu, int x, int y,
		 int *ulx, int *uly, int *width, int *height)
{
  tty_menu_calc_size (menu, width, height);
  *ulx = x + 1;
  *uly = y;
  *width += 2;
}

struct tty_menu_state
{
  struct glyph_matrix *screen_behind;
  tty_menu *menu;
  int pane;
  int x, y;
};

/* Save away the contents of frame F's current frame matrix, and
   enable all its rows.  Value is a glyph matrix holding the contents
   of F's current frame matrix with all its glyph rows enabled.  */

static struct glyph_matrix *
save_and_enable_current_matrix (struct frame *f)
{
  int i;
  struct glyph_matrix *saved = xzalloc (sizeof *saved);
  saved->nrows = f->current_matrix->nrows;
  saved->rows = xzalloc (saved->nrows * sizeof *saved->rows);

  for (i = 0; i < saved->nrows; ++i)
    {
      struct glyph_row *from = f->current_matrix->rows + i;
      struct glyph_row *to = saved->rows + i;
      ptrdiff_t nbytes = from->used[TEXT_AREA] * sizeof (struct glyph);

      to->glyphs[TEXT_AREA] = xmalloc (nbytes);
      memcpy (to->glyphs[TEXT_AREA], from->glyphs[TEXT_AREA], nbytes);
      to->used[TEXT_AREA] = from->used[TEXT_AREA];
      /* Make sure every row is enabled, or else update_frame will not
	 redraw them.  (Rows that are identical to what is already on
	 screen will not be redrawn anyway.)  */
      to->enabled_p = true;
      to->hash = from->hash;
    }

  return saved;
}

/* Restore the contents of frame F's desired frame matrix from SAVED,
   and free memory associated with SAVED.  */

static void
restore_desired_matrix (struct frame *f, struct glyph_matrix *saved)
{
  for (int i = 0; i < saved->nrows; ++i)
    {
      struct glyph_row *from = saved->rows + i;
      struct glyph_row *to = f->desired_matrix->rows + i;
      ptrdiff_t nbytes = from->used[TEXT_AREA] * sizeof (struct glyph);

      eassert (to->glyphs[TEXT_AREA] != from->glyphs[TEXT_AREA]);
      memcpy (to->glyphs[TEXT_AREA], from->glyphs[TEXT_AREA], nbytes);
      to->used[TEXT_AREA] = from->used[TEXT_AREA];
      to->enabled_p = from->enabled_p;

      bool need_new_hash = false;
      for (int x = 0; x < f->desired_matrix->matrix_w; ++x)
	{
	  struct glyph *glyph = to->glyphs[0] + x;
	  if (!FRAME_LIVE_P (glyph->frame))
	    {
	      glyph->frame = f;
	      glyph->face_id = DEFAULT_FACE_ID;
	      need_new_hash = true;
	    }
	}

      if (need_new_hash)
	to->hash = row_hash (to);
      else
	to->hash = from->hash;
    }
}

static void
free_saved_screen (struct glyph_matrix *saved)
{
  int i;

  if (!saved)
    return;	/* Already freed!  */

  for (i = 0; i < saved->nrows; ++i)
    {
      struct glyph_row *from = saved->rows + i;

      xfree (from->glyphs[TEXT_AREA]);
    }

  xfree (saved->rows);
  xfree (saved);
}

/* Update the display of frame F from its saved contents.  */
static void
screen_update (struct frame *f, struct glyph_matrix *mtx)
{
  restore_desired_matrix (f, mtx);
  update_frame_with_menu (f, -1, -1);
}

typedef enum {
  MI_QUIT_MENU      = -1,
  MI_CONTINUE       = 0,
  MI_ITEM_SELECTED  = 1,
  MI_NEXT_ITEM      = 2,
  MI_PREV_ITEM      = 3,
  MI_SCROLL_FORWARD = 4,
  MI_SCROLL_BACK    = 5
} mi_result;

/* Read user input and return X and Y coordinates where that input
   puts us.  We only consider mouse movement and click events, and
   keyboard movement commands; the rest are ignored.  */
static mi_result
read_menu_input (struct frame *sf, int *x, int *y, int min_y, int max_y,
		 bool *first_time)
{
  if (*first_time)
    {
      *first_time = false;
      sf->mouse_moved = 1;
    }
  else
    {
      Lisp_Object cmd;
      bool usable_input = 1;
      mi_result st = MI_CONTINUE;
      struct tty_display_info *tty = FRAME_TTY (sf);
      Lisp_Object old_track_mouse = track_mouse;

      /* Signal the keyboard reading routines we are displaying a menu
	 on this terminal.  */
      tty->showing_menu = 1;
      /* We want mouse movements be reported by read_menu_command.  */
      track_mouse = Qt;
      do {
	cmd = read_menu_command ();
      } while (NILP (cmd));
      tty->showing_menu = 0;
      track_mouse = old_track_mouse;

      if (EQ (cmd, Qt) || EQ (cmd, Qtty_menu_exit)
	  /* If some input switched frames under our feet, exit the
	     menu, since the menu faces are no longer valid, and the
	     menu is no longer relevant anyway.  */
	  || sf != SELECTED_FRAME ())
	return MI_QUIT_MENU;
      if (EQ (cmd, Qtty_menu_mouse_movement))
	mouse_get_xy (x, y);
      else if (EQ (cmd, Qtty_menu_next_menu))
	{
	  usable_input = 0;
	  st = MI_NEXT_ITEM;
	}
      else if (EQ (cmd, Qtty_menu_prev_menu))
	{
	  usable_input = 0;
	  st = MI_PREV_ITEM;
	}
      else if (EQ (cmd, Qtty_menu_next_item))
	{
	  if (*y < max_y)
	    *y += 1;
	  else
	    st = MI_SCROLL_FORWARD;
	}
      else if (EQ (cmd, Qtty_menu_prev_item))
	{
	  if (*y > min_y)
	    *y -= 1;
	  else
	    st = MI_SCROLL_BACK;
	}
      else if (EQ (cmd, Qtty_menu_select))
	st = MI_ITEM_SELECTED;
      else if (!EQ (cmd, Qtty_menu_ignore))
	usable_input = 0;
      if (usable_input)
	sf->mouse_moved = 1;
      return st;
    }
  return MI_CONTINUE;
}

/* M33 imp-1 - static dispatchers into (emacs terminal).  They are local
   to term.c, so the budgeted keyboard.c surface does not grow.  Each
   caches its SCM proc in a static SCM with the SCM_UNBNDP guard.  The C
   mechanism stays here: the menu select loop and the terminal walk.  */

static void
tty_menu_clear_help (void)
{
  /* Port of the MI_QUIT_MENU arm (term.c:3432-3434).  */
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs terminal", "tty-menu-clear-help!");
  SCM_CALL_0 (proc);
}

static void
tty_menu_discard_mouse_events (void)
{
  /* Port of term.c:3566-3568.  */
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs terminal", "tty-menu-discard-mouse-events!");
  SCM_CALL_0 (proc);
}

/* Display menu, wait for user's response, and return that response.  */
static int
tty_menu_activate (tty_menu *menu, int *pane, int *selidx,
		   int x0, int y0, char **txt,
		   void (*help_callback)(char const *, int, int),
		   bool kbd_navigation)
{
  struct tty_menu_state *state;
  int statecount, x, y, i;
  bool leave, onepane;
  int result UNINIT;
  int title_faces[4];		/* Face to display the menu title.  */
  int faces[4], buffers_num_deleted = 0;
  struct frame *sf = SELECTED_FRAME ();
  struct tty_display_info *tty = FRAME_TTY (sf);
  bool first_time;
  Lisp_Object selectface;
  int first_item = 0;
  int col, row;
  Lisp_Object prev_inhibit_redisplay = Vinhibit_redisplay;
  USE_SAFE_ALLOCA;

  /* Don't allow non-positive x0 and y0, lest the menu will wrap
     around the display.  */
  if (x0 <= 0)
    x0 = 1;
  if (y0 <= 0)
    y0 = 1;

  SAFE_NALLOCA (state, 1, menu->panecount);
  memset (state, 0, sizeof (*state));
  faces[0]
    = lookup_derived_face (NULL, sf, Qtty_menu_disabled_face,
			   DEFAULT_FACE_ID, 1);
  faces[1]
    = lookup_derived_face (NULL, sf, Qtty_menu_enabled_face,
			   DEFAULT_FACE_ID, 1);
  selectface = intern ("tty-menu-selected-face");
  faces[2] = lookup_derived_face (NULL, sf, selectface,
				  faces[0], 1);
  faces[3] = lookup_derived_face (NULL, sf, selectface,
				  faces[1], 1);

  /* Make sure the menu title is always displayed with
     `tty-menu-selected-face', no matter where the mouse pointer is.  */
  for (i = 0; i < 4; i++)
    title_faces[i] = faces[3];

  statecount = 1;

  /* Don't let the title for the "Buffers" popup menu include a
     digit (which is ugly).

     This is a terrible kludge, but I think the "Buffers" case is
     the only one where the title includes a number, so it doesn't
     seem to be necessary to make this more general.  */
  if (strncmp (menu->text[0], "Buffers 1", 9) == 0)
    {
      menu->text[0][7] = '\0';
      buffers_num_deleted = 1;
    }

  /* Inhibit redisplay for as long as the menu is active, to avoid
     messing the screen if some timer calls sit-for or a similar
     function.  */
  Vinhibit_redisplay = Qt;

  /* Force update of the current frame, so that the desired and the
     current matrices are identical.  */
  update_frame_with_menu (sf, -1, -1);
  state[0].menu = menu;
  state[0].screen_behind = save_and_enable_current_matrix (sf);

  /* Display the menu title.  We subtract 1 from x0 and y0 because we
     want to interpret them as zero-based column and row coordinates,
     and also because we want the first item of the menu, not its
     title, to appear at x0,y0.  */
  tty_menu_display (menu, x0 - 1, y0 - 1, 1, title_faces, x0 - 1, y0 - 1, 0, 0);

  /* Turn off the cursor.  Otherwise it shows through the menu
     panes, which is ugly.  */
  col = cursorX (tty);
  row = cursorY (tty);
  tty_hide_cursor (tty);

  if (buffers_num_deleted)
    menu->text[0][7] = ' ';
  onepane = menu->count == 1 && menu->submenu[0];
  if (onepane)
    {
      menu->width = menu->submenu[0]->width;
      state[0].menu = menu->submenu[0];
    }
  else
    {
      state[0].menu = menu;
    }
  state[0].x = x0 - 1;
  state[0].y = y0;
  state[0].pane = onepane;

  x = state[0].x;
  y = state[0].y;
  first_time = true;

  leave = 0;
  while (!leave)
    {
      mi_result input_status;
      int min_y = state[0].y;
      int max_y = min (min_y + state[0].menu->count, FRAME_TOTAL_LINES (sf) - 1) - 1;

      input_status = read_menu_input (sf, &x, &y, min_y, max_y, &first_time);
      if (input_status)
	{
	  leave = 1;
	  switch (input_status)
	    {
	    case MI_QUIT_MENU:
	      /* Remove the last help-echo, so that it doesn't
		 re-appear after "Quit".  M33 imp-1: the decision moved
		 to (emacs terminal) tty-menu-clear-help!.  */
	      tty_menu_clear_help ();
	      result = TTYM_NO_SELECT;
	      break;
	    case MI_NEXT_ITEM:
	      if (kbd_navigation)
		result = TTYM_NEXT;
	      else
		leave = 0;
	      break;
	    case MI_PREV_ITEM:
	      if (kbd_navigation)
		result = TTYM_PREV;
	      else
		leave = 0;
	      break;
	    case MI_SCROLL_FORWARD:
	      if (y - min_y == state[0].menu->count - 1 - first_item)
		{
		  y = min_y;
		  first_item = 0;
		}
	      else
		first_item++;
	      leave = 0;
	      break;
	    case MI_SCROLL_BACK:
	      if (first_item == 0)
		{
		  y = max_y;
		  first_item = state[0].menu->count - 1 - (y - min_y);
		}
	      else
		first_item--;
	      leave = 0;
	      break;
	    default:
	      /* MI_ITEM_SELECTED is handled below, so nothing to do.  */
	      break;
	    }
	}
      if (sf->mouse_moved && input_status != MI_QUIT_MENU)
	{
	  sf->mouse_moved = 0;
	  result = TTYM_IA_SELECT;
	  for (i = 0; i < statecount; i++)
	    if (state[i].x <= x && x < state[i].x + state[i].menu->width + 2)
	      {
		int dy = y - state[i].y + first_item;
		if (0 <= dy && dy < state[i].menu->count)
		  {
		    if (!state[i].menu->submenu[dy])
		      {
			if (state[i].menu->panenumber[dy])
			  result = TTYM_SUCCESS;
			else
			  result = TTYM_IA_SELECT;
		      }
		    *pane = state[i].pane - 1;
		    *selidx = dy;
		    /* We hit some part of a menu, so drop extra menus that
		       have been opened.  That does not include an open and
		       active submenu.  */
		    if (i != statecount - 2
			|| state[i].menu->submenu[dy] != state[i + 1].menu)
		      while (i < statecount - 1)
			{
			  statecount--;
			  screen_update (sf, state[statecount].screen_behind);
			  state[statecount].screen_behind = NULL;
			}
		    if (i == statecount - 1 && state[i].menu->submenu[dy])
		      {
			tty_menu_display (state[i].menu,
					  state[i].x,
					  state[i].y,
					  state[i].pane,
					  faces, x, y, first_item, 1);
			state[statecount].menu = state[i].menu->submenu[dy];
			state[statecount].pane = state[i].menu->panenumber[dy];
			state[statecount].screen_behind
			  = save_and_enable_current_matrix (sf);
			state[statecount].x
			  = state[i].x + state[i].menu->width + 2;
			state[statecount].y = y;
			statecount++;
		      }
		  }
	      }
	  tty_menu_display (state[statecount - 1].menu,
			    state[statecount - 1].x,
			    state[statecount - 1].y,
			    state[statecount - 1].pane,
			    faces, x, y, first_item, 1);
	  /* The call to display help-echo below will move the cursor,
	     so remember its current position as computed by
	     tty_menu_display.  */
	  col = cursorX (tty);
	  row = cursorY (tty);
	}

      /* Display the help-echo message for the currently-selected menu
	 item.  */
      if ((menu_help_message || prev_menu_help_message)
	  && menu_help_message != prev_menu_help_message)
	{
	  help_callback (menu_help_message,
			 menu_help_paneno, menu_help_itemno);
	  /* Move the cursor to the beginning of the current menu
	     item, so that screen readers and other accessibility aids
	     know where the active region is.  */
	  cursor_to (sf, row, col);
	  prev_menu_help_message = menu_help_message;
	}
      /* Both tty_menu_display and help_callback invoke update_end,
	 which calls tty_show_cursor.  Re-hide it, so it doesn't show
	 through the menus.  */
      tty_hide_cursor (tty);
      /* M61 imp-2: Scheme checks that the handle is open; C keeps the
         fflush and its position.  */
      (void) m61_tty_handle_flush_1 (tty);
    }

  sf->mouse_moved = 0;
  screen_update (sf, state[0].screen_behind);
  while (statecount--)
    free_saved_screen (state[statecount].screen_behind);
  tty_show_cursor (tty);	/* Turn cursor back on.  */
  /* M61 imp-2: Scheme checks that the handle is open; C keeps the
     fflush and its position.  */
  (void) m61_tty_handle_flush_1 (tty);

/* Clean up any mouse events that are waiting inside Emacs event queue.
     These events are likely to be generated before the menu was even
     displayed, probably because the user pressed and released the button
     (which invoked the menu) too quickly.  If we don't remove these events,
     Emacs will process them after we return and surprise the user.  */
  /* M33 imp-1: the decision moved to (emacs terminal)
     tty-menu-discard-mouse-events!.  */
  tty_menu_discard_mouse_events ();
  SAFE_FREE ();
  Vinhibit_redisplay = prev_inhibit_redisplay;
  return result;
}

/* Dispose of a menu.  */

static void
tty_menu_destroy (tty_menu *menu)
{
  int i;
  if (menu->allocated)
    {
      for (i = 0; i < menu->count; i++)
	if (menu->submenu[i])
	  tty_menu_destroy (menu->submenu[i]);
      xfree (menu->text);
      xfree (menu->submenu);
      xfree (menu->panenumber);
      xfree (menu->help_text);
    }
  xfree (menu);
  menu_help_message = prev_menu_help_message = NULL;
}

/* Show help HELP_STRING, or clear help if HELP_STRING is null.

   PANE is the pane number, and ITEM is the menu item number in
   the menu (currently not used).  */

static void
tty_menu_help_callback (char const *help_string, int pane, int item)
{
  /* M33 imp-1 - the decision body moved to (emacs terminal)
     tty-menu-help-callback.  This C function keeps the name and the
     fn-pointer signature at term.c:3920 (see brief.org 5.3).  */
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs terminal", "tty-menu-help-callback");
  SCM_CALL_3 (proc,
	      help_string ? build_string (help_string) : Qnil,
	      make_fixnum (pane), make_fixnum (item));
}

struct tty_pop_down_menu
{
  tty_menu *menu;
  struct buffer *buffer;
};

static void
tty_pop_down_menu (void *arg)
{
  struct tty_pop_down_menu *data = arg;

  block_input ();
  tty_menu_destroy (data->menu);
  set_buffer_internal (data->buffer);
  unblock_input ();
}

/* Return the zero-based index of the last menu-bar item on frame F.  */
static int
tty_menu_last_menubar_item (struct frame *f)
{
  int i = 0;

  eassert (FRAME_TERMCAP_P (f) && FRAME_LIVE_P (f));
  if (FRAME_TERMCAP_P (f) && FRAME_LIVE_P (f))
    {
      Lisp_Object items = FRAME_MENU_BAR_ITEMS (f);

      while (i < ASIZE (items))
	{
	  Lisp_Object str;

	  str = AREF (items, i + 1);
	  if (NILP (str))
	    break;
	  i += 4;
	}
      i -= 4;	/* Went one too far!  */
    }
  return i;
}

/* Find in frame F's menu bar the menu item that is next or previous
   to the item at X/Y, and return that item's position in X/Y.  WHICH
   says which one--next or previous--item to look for.  X and Y are
   measured in character cells.  This should only be called on TTY
   frames.  */
static void
tty_menu_new_item_coords (struct frame *f, int which, int *x, int *y)
{
  eassert (FRAME_TERMCAP_P (f) && FRAME_LIVE_P (f));
  if (FRAME_TERMCAP_P (f) && FRAME_LIVE_P (f))
    {
      Lisp_Object items = FRAME_MENU_BAR_ITEMS (f);
      int last_i = tty_menu_last_menubar_item (f);
      int i, prev_x;

      /* This loop assumes a single menu-bar line, and will fail to
	 find an item if it is not in the first line.  Note that
	 make_lispy_event in keyboard.c makes the same assumption.  */
      for (i = 0, prev_x = -1; i < ASIZE (items); i += 4)
	{
	  Lisp_Object pos, str;
	  int ix;

	  str = AREF (items, i + 1);
	  pos = AREF (items, i + 3);
	  if (NILP (str))
	    return;
	  ix = XFIXNUM (pos);
	  if (ix <= *x
	      /* We use <= so the blank between 2 items on a TTY is
		 considered part of the previous item.  */
	      && *x <= ix + menu_item_width (SDATA (str)))
	    {
	      /* Found current item.  Now compute the X coordinate of
		 the previous or next item.  */
	      if (which == TTYM_NEXT)
		{
		  if (i < last_i)
		    *x = XFIXNUM (AREF (items, i + 4 + 3));
		  else
		    *x = 0;	/* Wrap around to the first item.  */
		}
	      else if (prev_x < 0)
		{
		  /* Wrap around to the last item.  */
		  *x = XFIXNUM (AREF (items, last_i + 3));
		}
	      else
		*x = prev_x;
	      return;
	    }
	  prev_x = ix;
	}
    }
}

/* WINDOWSNT uses this as menu_show_hook, see w32console.c.  */
Lisp_Object
tty_menu_show (struct frame *f, int x, int y, int menuflags,
	       Lisp_Object title, const char **error_name)
{
  tty_menu *menu;
  int pane, selidx, lpane, status;
  Lisp_Object entry, pane_prefix;
  char *datap;
  int ulx, uly, width, height;
  int item_x, item_y;
  int dispwidth, dispheight;
  int i, j, lines, maxlines;
  int maxwidth;

  eassert (FRAME_TERMCAP_P (f));

  *error_name = 0;
  if (menu_items_n_panes == 0)
    return Qnil;

  if (menu_items_used <= MENU_ITEMS_PANE_LENGTH)
    {
      *error_name = "Empty menu";
      return Qnil;
    }

  /* Make the menu on that window.  */
  menu = tty_menu_create ();

  dynwind_begin ();

  /* Avoid crashes if, e.g., another client will connect while we
     are in a menu.  */
  temporarily_switch_to_single_kboard (f);

  /* Adjust coordinates to be root-window-relative.  */
  item_x = x += f->left_pos;
  item_y = y += f->top_pos;

  /* Create all the necessary panes and their items.  */
  USE_SAFE_ALLOCA;
  maxwidth = maxlines = lines = i = 0;
  lpane = TTYM_FAILURE;
  while (i < menu_items_used)
    {
      if (EQ (AREF (menu_items, i), Qt))
	{
	  /* Create a new pane.  */
	  Lisp_Object pane_name, prefix;
	  const char *pane_string;

          maxlines = max (maxlines, lines);
          lines = 0;
	  pane_name = AREF (menu_items, i + MENU_ITEMS_PANE_NAME);
	  prefix = AREF (menu_items, i + MENU_ITEMS_PANE_PREFIX);
	  pane_string = (NILP (pane_name)
			 ? "" : SSDATA (pane_name));
	  if ((menuflags & MENU_KEYMAPS) && !NILP (prefix))
	    pane_string++;

	  lpane = tty_menu_add_pane (menu, pane_string);
	  if (lpane == TTYM_FAILURE)
	    {
	      tty_menu_destroy (menu);
	      *error_name = "Can't create pane";
	      entry = Qnil;
	      goto tty_menu_end;
	    }
	  i += MENU_ITEMS_PANE_LENGTH;

	  /* Find the width of the widest item in this pane.  */
	  j = i;
	  while (j < menu_items_used)
	    {
	      Lisp_Object item;
	      item = AREF (menu_items, j);
	      if (EQ (item, Qt))
		break;
	      if (NILP (item))
		{
		  j++;
		  continue;
		}
	      width = SBYTES (item);
	      if (width > maxwidth)
		maxwidth = width;

	      j += MENU_ITEMS_ITEM_LENGTH;
	    }
	}
      /* Ignore a nil in the item list.
	 It's meaningful only for dialog boxes.  */
      else if (EQ (AREF (menu_items, i), Qquote))
	i += 1;
      else
	{
	  /* Create a new item within current pane.  */
	  Lisp_Object item_name, enable, descrip, help;
	  char *item_data;
	  char const *help_string;

	  item_name = AREF (menu_items, i + MENU_ITEMS_ITEM_NAME);
	  enable = AREF (menu_items, i + MENU_ITEMS_ITEM_ENABLE);
	  descrip = AREF (menu_items, i + MENU_ITEMS_ITEM_EQUIV_KEY);
	  help = AREF (menu_items, i + MENU_ITEMS_ITEM_HELP);
	  help_string = STRINGP (help) ? SSDATA (help) : NULL;

	  if (!NILP (descrip))
	    {
	      item_data = SAFE_ALLOCA (maxwidth + SBYTES (descrip) + 1);
	      memcpy (item_data, SSDATA (item_name), SBYTES (item_name));
	      for (j = SCHARS (item_name); j < maxwidth; j++)
		item_data[j] = ' ';
	      memcpy (item_data + j, SSDATA (descrip), SBYTES (descrip));
	      item_data[j + SBYTES (descrip)] = 0;
	    }
	  else
	    item_data = SSDATA (item_name);

	  if (lpane == TTYM_FAILURE
	      || (! tty_menu_add_selection (menu, lpane, item_data,
					    !NILP (enable), help_string)))
	    {
	      tty_menu_destroy (menu);
	      *error_name = "Can't add selection to menu";
	      entry = Qnil;
	      goto tty_menu_end;
	    }
	  i += MENU_ITEMS_ITEM_LENGTH;
          lines++;
	}
    }

  maxlines = max (maxlines, lines);

  /* All set and ready to fly.  */
  dispwidth = f->text_cols;
  dispheight = f->text_lines;
  x = min (x, dispwidth);
  y = min (y, dispheight);
  x = max (x, 1);
  y = max (y, 1);
  tty_menu_locate (menu, x, y, &ulx, &uly, &width, &height);
  if (ulx + width > dispwidth)
    {
      x -= (ulx + width) - dispwidth;
      ulx = dispwidth - width;
    }
  if (uly + height > dispheight)
    {
      y -= (uly + height) - dispheight;
      uly = dispheight - height;
    }

  if (FRAME_HAS_MINIBUF_P (f) && uly + height > dispheight - 2)
    {
      /* Move the menu away of the echo area, to avoid overwriting the
	 menu with help echo messages or vice versa.  */
      if (BUFFERP (echo_area_buffer[0]) && WINDOWP (echo_area_window))
	{
	  y -= WINDOW_TOTAL_LINES (XWINDOW (echo_area_window)) + 1;
	  uly -= WINDOW_TOTAL_LINES (XWINDOW (echo_area_window)) + 1;
	}
      else
	{
	  y -= 2;
	  uly -= 2;
	}
    }

  if (ulx < 0) x -= ulx;
  if (uly < 0) y -= uly;

#if 0
  /* This code doesn't make sense on a TTY, since it can easily annul
     the adjustments above that carefully avoid truncation of the menu
     items.  I think it was written to fix some problem that only
     happens on X11.  */
  if (! for_click)
    {
      /* If position was not given by a mouse click, adjust so upper left
         corner of the menu as a whole ends up at given coordinates.  This
         is what x-popup-menu says in its documentation.  */
      x += width / 2;
      y += 1.5 * height / (maxlines + 2);
    }
#endif

  pane = selidx = 0;

  /* We save and restore the current buffer because tty_menu_activate
     triggers redisplay, which switches buffers at will.  */
  record_unwind_protect_ptr (tty_pop_down_menu,
			     &((struct tty_pop_down_menu)
			       {menu, current_buffer}));

  specbind_guile (Qoverriding_terminal_local_map,
	    Fsymbol_value (Qtty_menu_navigation_map));
  status = tty_menu_activate (menu, &pane, &selidx, x, y, &datap,
			      tty_menu_help_callback,
			      menuflags & MENU_KBD_NAVIGATION);
  entry = pane_prefix = Qnil;

  switch (status)
    {
    case TTYM_SUCCESS:
      /* Find the item number SELIDX in pane number PANE.  */
      i = 0;
      while (i < menu_items_used)
	{
	  if (EQ (AREF (menu_items, i), Qt))
	    {
	      if (pane == 0)
		pane_prefix
		  = AREF (menu_items, i + MENU_ITEMS_PANE_PREFIX);
	      pane--;
	      i += MENU_ITEMS_PANE_LENGTH;
	    }
	  else
	    {
	      if (pane == -1)
		{
		  if (selidx == 0)
		    {
		      entry
			= AREF (menu_items, i + MENU_ITEMS_ITEM_VALUE);
		      if (menuflags & MENU_KEYMAPS)
			{
			  entry = Fcons (entry, Qnil);
			  if (!NILP (pane_prefix))
			    entry = Fcons (pane_prefix, entry);
			}
		      break;
		    }
		  selidx--;
		}
	      i += MENU_ITEMS_ITEM_LENGTH;
	    }
	}
      break;

    case TTYM_NEXT:
    case TTYM_PREV:
      tty_menu_new_item_coords (f, status, &item_x, &item_y);
      entry = Fcons (make_fixnum (item_x), make_fixnum (item_y));
      break;

    case TTYM_FAILURE:
      *error_name = "Can't activate menu";
    case TTYM_IA_SELECT:
      break;
    case TTYM_NO_SELECT:
      /* If the selected frame was changed while we displayed a menu,
	 throw to top level in order to undo any temporary settings
	 made by TTY menu code.  */
      if (f != SELECTED_FRAME ())
	Ftop_level ();
      /* Make "Cancel" equivalent to C-g unless FOR_CLICK (which means
	 the menu was invoked with a mouse event as POSITION).  */
      if (!(menuflags & MENU_FOR_CLICK))
	quit ();
      break;
    }

 tty_menu_end:

  SAFE_FREE ();
  dynwind_end ();
  return entry;
}

#endif	/* !MSDOS && !defined HAVE_ANDROID */



#if !defined MSDOS && !defined HAVE_ANDROID

/***********************************************************************
			    Initialization
 ***********************************************************************/

/* Initialize the tty-dependent part of frame F.  The frame must
   already have its device initialized.  */

void
create_tty_output (struct frame *f)
{
  struct tty_output *t = xzalloc (sizeof *t);

  eassert (FRAME_TERMCAP_P (f));

  t->display_info = FRAME_TERMINAL (f)->display_info.tty;

  f->output_data.tty = t;
}

/* Delete frame F's face cache, and its tty-dependent part.  */

static void
tty_free_frame_resources (struct frame *f)
{
  eassert (FRAME_TERMCAP_P (f));
  free_frame_faces (f);
  xfree (f->output_data.tty);
}

#elif defined MSDOS

/* Delete frame F's face cache.  */

static void
tty_free_frame_resources (struct frame *f)
{
  eassert (FRAME_TERMCAP_P (f) || FRAME_MSDOS_P (f));
  free_frame_faces (f);
}

#endif



#ifndef HAVE_ANDROID

/* Reset the hooks in TERMINAL.  */

static void
clear_tty_hooks (struct terminal *terminal)
{
  terminal->rif = 0;
  terminal->cursor_to_hook = 0;
  terminal->raw_cursor_to_hook = 0;
  terminal->clear_to_end_hook = 0;
  terminal->clear_frame_hook = 0;
  terminal->clear_end_of_line_hook = 0;
  terminal->ins_del_lines_hook = 0;
  terminal->insert_glyphs_hook = 0;
  terminal->write_glyphs_hook = 0;
  terminal->delete_glyphs_hook = 0;
  terminal->ring_bell_hook = 0;
  terminal->reset_terminal_modes_hook = 0;
  terminal->set_terminal_modes_hook = 0;
  terminal->update_begin_hook = 0;
  terminal->update_end_hook = 0;
  terminal->set_terminal_window_hook = 0;
  /* Don't clear the defined_color_hook, as that makes it impossible
     to unload or load a theme when some TTY frame is suspended.  */
  /* terminal->defined_color_hook = 0; */
  terminal->mouse_position_hook = 0;
  terminal->frame_rehighlight_hook = 0;
  terminal->frame_raise_lower_hook = 0;
  terminal->fullscreen_hook = 0;
  terminal->menu_show_hook = 0;
  terminal->set_vertical_scroll_bar_hook = 0;
  terminal->set_horizontal_scroll_bar_hook = 0;
  terminal->condemn_scroll_bars_hook = 0;
  terminal->redeem_scroll_bar_hook = 0;
  terminal->judge_scroll_bars_hook = 0;
  terminal->read_socket_hook = 0;
  terminal->frame_up_to_date_hook = 0;

  /* Leave these two set, or suspended frames are not deleted
     correctly.  */
  terminal->delete_frame_hook = &tty_free_frame_resources;
  terminal->delete_terminal_hook = &delete_tty;
}

/* Initialize hooks in TERMINAL with the values needed for a tty.  */

static void
set_tty_hooks (struct terminal *terminal)
{
  terminal->cursor_to_hook = &tty_cursor_to;
  terminal->raw_cursor_to_hook = &tty_raw_cursor_to;
  terminal->clear_to_end_hook = &tty_clear_to_end;
  terminal->clear_frame_hook = &tty_clear_frame;
  terminal->clear_end_of_line_hook = &tty_clear_end_of_line;
  terminal->ins_del_lines_hook = &tty_ins_del_lines;
  terminal->insert_glyphs_hook = &tty_insert_glyphs;
  terminal->write_glyphs_hook = &tty_write_glyphs;
  terminal->delete_glyphs_hook = &tty_delete_glyphs;
  terminal->ring_bell_hook = &tty_ring_bell;
  terminal->reset_terminal_modes_hook = &tty_reset_terminal_modes;
  terminal->set_terminal_modes_hook = &tty_set_terminal_modes;
  terminal->update_end_hook = &tty_update_end;
#ifdef MSDOS
  terminal->menu_show_hook = &x_menu_show;
#else
  terminal->menu_show_hook = &tty_menu_show;
#endif
  terminal->set_terminal_window_hook = &tty_set_terminal_window;
  terminal->defined_color_hook = &tty_defined_color; /* xfaces.c */
  terminal->read_socket_hook = &tty_read_avail_input; /* keyboard.c */
  terminal->delete_frame_hook = &tty_free_frame_resources;
  terminal->delete_terminal_hook = &delete_tty;

  terminal->frame_raise_lower_hook = tty_raise_lower_frame;
  /* Other hooks are NULL by default.  */
}

/* If FD is the controlling terminal, drop it.  */
static void
dissociate_if_controlling_tty (int fd)
{
  /* If tcgetpgrp succeeds, fd is the controlling terminal,
     so dissociate it by invoking setsid.  */
  if (tcgetpgrp (fd) >= 0 && setsid () < 0)
    {
#ifdef TIOCNOTTY
      /* setsid failed, presumably because Emacs is already a process
	 group leader.  Fall back on the obsolescent way to dissociate
	 a controlling tty.  */
      sigset_t oldset;
      block_tty_out_signal (&oldset);
      ioctl (fd, TIOCNOTTY, 0);
      unblock_tty_out_signal (&oldset);
#endif
    }
}

#endif /* !HAVE_ANDROID */

/* Create a termcap display on the tty device with the given name and
   type.

   If NAME is NULL, then use the controlling tty, i.e., dev_tty.
   Otherwise NAME should be a path to the tty device file,
   e.g. "/dev/pts/7".

   TERMINAL_TYPE is the termcap type of the device, e.g. "vt100".

   If MUST_SUCCEED is true, then all errors are fatal.  This function
   always signals on Android, where text terminals are prohibited by
   system policy (and the required libraries are usually not
   available.)  */

#ifdef HAVE_ANDROID
_Noreturn
#endif

struct terminal *
init_tty (const char *name, const char *terminal_type, bool must_succeed)
{
#ifdef HAVE_ANDROID
  maybe_fatal (must_succeed, 0, "Text terminals are not supported"
	       " under Android", "Text terminals are not supported"
	       " under Android");
#else
  struct tty_display_info *tty = NULL;
  struct terminal *terminal = NULL;
#ifndef DOS_NT
  char *area;
  char **address = &area;
  int status;
  sigset_t oldset;
  bool ctty = false;  /* True if asked to open controlling tty.  */
#endif

  if (!terminal_type)
    maybe_fatal (must_succeed, 0,
                 "Unknown terminal type",
                 "Unknown terminal type");

  if (name == NULL)
    name = dev_tty;
#ifndef DOS_NT
  if (!strcmp (name, dev_tty))
    ctty = 1;
#endif

  /* If we already have a terminal on the given device, use that.  If
     all such terminals are suspended, create a new one instead.  */
  /* XXX Perhaps this should be made explicit by having init_tty
     always create a new terminal and separating terminal and frame
     creation on Lisp level.  */
  terminal = get_named_terminal (name);
  if (terminal)
    return terminal;

  terminal = create_terminal (output_termcap, NULL);
#ifdef MSDOS
  if (been_here > 0)
    maybe_fatal (0, 0, "Attempt to create another terminal %s", "",
		 name, "");
  been_here = 1;
  tty = &the_only_display_info;
#else
  tty = xzalloc (sizeof *tty);
#endif
  tty->top_frame = Qnil;
  tty->next = tty_list;
  tty_list = tty;

  terminal->display_info.tty = tty;
  tty->terminal = terminal;

  /* M61 imp-1: register the plain handle identity of this tty in the
     static identity table (docs/m61-plan.org section 4).  */
  m61_tty_handle_register_1 (tty);

  tty->Wcm = xmalloc (sizeof *tty->Wcm);
  Wcm_clear (tty);

  encode_terminal_src_size = 0;
  encode_terminal_dst_size = 0;


#ifndef DOS_NT
  set_tty_hooks (terminal);

  {
    /* Open the terminal device.  */

    /* If !ctty, don't recognize it as our controlling terminal, and
       don't make it the controlling tty if we don't have one now.

       Alas, O_IGNORE_CTTY is a GNU extension that seems to be only
       defined on Hurd.  On other systems, we need to explicitly
       dissociate ourselves from the controlling tty when we want to
       open a frame on the same terminal.  */
    int flags = O_RDWR | O_NOCTTY | (ctty ? 0 : O_IGNORE_CTTY);
    int fd = emacs_open (name, flags, 0);
    tty->input = tty->output
      = ((fd < 0 || ! isatty (fd))
	 ? NULL
	 : emacs_fdopen (fd, "w+"));

    if (! tty->input)
      {
	char const *diagnostic
	  = (fd < 0) ? "Could not open file: %s" : "Not a tty device: %s";
	emacs_close (fd);
        delete_terminal_internal (terminal);
	maybe_fatal (must_succeed, terminal, diagnostic, diagnostic, name);
      }

    tty->name = xstrdup (name);
    terminal->name = xstrdup (name);

    if (!O_IGNORE_CTTY && !ctty)
      dissociate_if_controlling_tty (fd);
  }

  tty->type = xstrdup (terminal_type);

  add_keyboard_wait_descriptor (fileno (tty->input));

  Wcm_clear (tty);

  /* On some systems, tgetent tries to access the controlling
     terminal.  */
  block_tty_out_signal (&oldset);
  status = tgetent (tty->termcap_term_buffer, terminal_type);
  if (tty->termcap_term_buffer[TERMCAP_BUFFER_SIZE - 1])
    emacs_abort ();
  unblock_tty_out_signal (&oldset);

  if (status < 0)
    {
#ifdef TERMINFO
      maybe_fatal (must_succeed, terminal,
                   "Cannot open terminfo database file",
                   "Cannot open terminfo database file");
#else
      maybe_fatal (must_succeed, terminal,
                   "Cannot open termcap database file",
                   "Cannot open termcap database file");
#endif
    }
  if (status == 0)
    {
      maybe_fatal (must_succeed, terminal,
                   "Terminal type %s is not defined",
                   "Terminal type %s is not defined.\n\
If that is not the actual type of terminal you have,\n\
use the Bourne shell command 'TERM=...; export TERM' (C-shell:\n\
'setenv TERM ...') to specify the correct type.  It may be necessary\n"
#ifdef TERMINFO
"to do 'unset TERMINFO' (C-shell: 'unsetenv TERMINFO') as well.",
#else
"to do 'unset TERMCAP' (C-shell: 'unsetenv TERMCAP') as well.",
#endif
                   terminal_type);
    }

  area = tty->termcap_strings_buffer;
  tty->TS_ins_line = tgetstr ("al", address);
  tty->TS_ins_multi_lines = tgetstr ("AL", address);
  tty->TS_bell = tgetstr ("bl", address);
  BackTab (tty) = tgetstr ("bt", address);
  tty->TS_clr_to_bottom = tgetstr ("cd", address);
  tty->TS_clr_line = tgetstr ("ce", address);
  tty->TS_clr_frame = tgetstr ("cl", address);
  ColPosition (tty) = NULL; /* tgetstr ("ch", address); */
  AbsPosition (tty) = tgetstr ("cm", address);
  CR (tty) = tgetstr ("cr", address);
  tty->TS_set_scroll_region = tgetstr ("cs", address);
  tty->TS_set_scroll_region_1 = tgetstr ("cS", address);
  RowPosition (tty) = tgetstr ("cv", address);
  tty->TS_del_char = tgetstr ("dc", address);
  tty->TS_del_multi_chars = tgetstr ("DC", address);
  tty->TS_del_line = tgetstr ("dl", address);
  tty->TS_del_multi_lines = tgetstr ("DL", address);
  tty->TS_delete_mode = tgetstr ("dm", address);
  tty->TS_end_delete_mode = tgetstr ("ed", address);
  tty->TS_end_insert_mode = tgetstr ("ei", address);
  Home (tty) = tgetstr ("ho", address);
  tty->TS_ins_char = tgetstr ("ic", address);
  tty->TS_ins_multi_chars = tgetstr ("IC", address);
  tty->TS_insert_mode = tgetstr ("im", address);
  tty->TS_pad_inserted_char = tgetstr ("ip", address);
  tty->TS_end_keypad_mode = tgetstr ("ke", address);
  tty->TS_keypad_mode = tgetstr ("ks", address);
  LastLine (tty) = tgetstr ("ll", address);
  Right (tty) = tgetstr ("nd", address);
  Down (tty) = tgetstr ("do", address);
  if (!Down (tty))
    Down (tty) = tgetstr ("nl", address); /* Obsolete name for "do".  */
  if (tgetflag ("bs"))
    Left (tty) = "\b";		  /* Can't possibly be longer!  */
  else				  /* (Actually, "bs" is obsolete...)  */
    Left (tty) = tgetstr ("le", address);
  if (!Left (tty))
    Left (tty) = tgetstr ("bc", address); /* Obsolete name for "le".  */
  tty->TS_pad_char = tgetstr ("pc", address);
  tty->TS_repeat = tgetstr ("rp", address);
  tty->TS_end_standout_mode = tgetstr ("se", address);
  tty->TS_fwd_scroll = tgetstr ("sf", address);
  tty->TS_standout_mode = tgetstr ("so", address);
  tty->TS_rev_scroll = tgetstr ("sr", address);
  tty->Wcm->cm_tab = tgetstr ("ta", address);
  tty->TS_end_termcap_modes = tgetstr ("te", address);
  tty->TS_termcap_modes = tgetstr ("ti", address);
  Up (tty) = tgetstr ("up", address);
  tty->TS_visible_bell = tgetstr ("vb", address);
  tty->TS_cursor_normal = tgetstr ("ve", address);
  tty->TS_cursor_visible = tgetstr ("vs", address);
  tty->TS_cursor_invisible = tgetstr ("vi", address);
  tty->TS_set_window = tgetstr ("wi", address);

  tty->TS_enter_underline_mode = tgetstr ("us", address);
  tty->TS_exit_underline_mode = tgetstr ("ue", address);
  tty->TS_enter_bold_mode = tgetstr ("md", address);
  tty->TS_enter_italic_mode = tgetstr ("ZH", address);
  tty->TS_enter_dim_mode = tgetstr ("mh", address);
  tty->TS_enter_reverse_mode = tgetstr ("mr", address);
  tty->TS_enter_alt_charset_mode = tgetstr ("as", address);
  tty->TS_exit_alt_charset_mode = tgetstr ("ae", address);
  tty->TS_exit_attribute_mode = tgetstr ("me", address);
#ifdef TERMINFO
  tty->TS_enter_strike_through_mode = tigetstr ("smxx");
  if (tty->TS_enter_strike_through_mode == (char *) (intptr_t) -1)
    tty->TS_enter_strike_through_mode = NULL;
#else
  /* FIXME: Is calling tgetstr here for non-terminfo case correct,
     even though "smxx" is more than 2 characters?  */
  tty->TS_enter_strike_through_mode = tgetstr ("smxx", address);
#endif

  MultiUp (tty) = tgetstr ("UP", address);
  MultiDown (tty) = tgetstr ("DO", address);
  MultiLeft (tty) = tgetstr ("LE", address);
  MultiRight (tty) = tgetstr ("RI", address);

  /* SVr4/ANSI color support.  If "op" isn't available, don't support
     color because we can't switch back to the default foreground and
     background.  */
  tty->TS_orig_pair = tgetstr ("op", address);
  if (tty->TS_orig_pair)
    {
      tty->TS_set_foreground = tgetstr ("AF", address);
      tty->TS_set_background = tgetstr ("AB", address);
      if (!tty->TS_set_foreground)
	{
	  /* SVr4.  */
	  tty->TS_set_foreground = tgetstr ("Sf", address);
	  tty->TS_set_background = tgetstr ("Sb", address);
	}

      tty->TN_max_colors = tgetnum ("Co");

#ifdef TERMINFO
      {
	const char *fg = tigetstr ("setf24");
	const char *bg = tigetstr ("setb24");
	/* Non-standard support for 24-bit colors. */
	if (fg && bg
	    && fg != (char *) (intptr_t) -1
	    && bg != (char *) (intptr_t) -1)
	  {
	    tty->TS_set_foreground = fg;
	    tty->TS_set_background = bg;
	    tty->TN_max_colors = 16777216;
	  }
	/* Standard support for 24-bit colors.  */
	else if (tigetflag ("RGB") > 0)
	  {
	    /* If the used Terminfo library supports only 16-bit
	       signed values, tgetnum("Co") and tigetnum("colors")
	       could return 32767.  */
	    tty->TN_max_colors = 16777216;
	  }
	/* Fall back to xterm+direct (semicolon version) if Tc is set
	   (de-facto standard introduced by tmux) or if	requested by
	   the COLORTERM environment variable.  */
	else if ((tigetflag ("Tc") > 0)
		 || ((bg = getenv ("COLORTERM")) != NULL
		     && strcasecmp (bg, "truecolor") == 0))
	  {
	    tty->TS_set_foreground = "\033[%?%p1%{8}%<%t3%p1%d%e38;2;%p1%{65536}%/%d;%p1%{256}%/%{255}%&%d;%p1%{255}%&%d%;m";
	    tty->TS_set_background = "\033[%?%p1%{8}%<%t4%p1%d%e48;2;%p1%{65536}%/%d;%p1%{256}%/%{255}%&%d;%p1%{255}%&%d%;m";
	    tty->TN_max_colors = 16777216;
	  }
      }
#endif

      tty->TN_no_color_video = tgetnum ("NC");
      if (tty->TN_no_color_video == -1)
        tty->TN_no_color_video = 0;
    }

  tty_default_color_capabilities (tty, 1);

  MagicWrap (tty) = tgetflag ("xn");
  /* Since we make MagicWrap terminals look like AutoWrap, we need to have
     the former flag imply the latter.  */
  AutoWrap (tty) = MagicWrap (tty) || tgetflag ("am");
  tty->memory_below_frame = tgetflag ("db");
  tty->TF_hazeltine = tgetflag ("hz");
  tty->must_write_spaces = tgetflag ("in");
  tty->meta_key = tgetflag ("km") || tgetflag ("MT");
  tty->TF_insmode_motion = tgetflag ("mi");
  tty->TF_standout_motion = tgetflag ("ms");
  tty->TF_underscore = tgetflag ("ul");
  tty->TF_teleray = tgetflag ("xt");

  /* Styled underlines.  Support for this is provided either by the
     escape sequence in Smulx or the Su flag.  The latter results in a
     common default escape sequence and is not recommended.  */
#ifdef TERMINFO
  tty->TF_set_underline_style = tigetstr ("Smulx");
  if (tty->TF_set_underline_style == (char *) (intptr_t) -1)
    tty->TF_set_underline_style = NULL;
#else
  tty->TF_set_underline_style = tgetstr ("Smulx", address);
#endif
  if (!tty->TF_set_underline_style && tgetflag ("Su"))
    /* Default to the kitty escape sequence.  See
       https://sw.kovidgoyal.net/kitty/underlines/.  */
    tty->TF_set_underline_style = "\x1b[4:%p1%dm";

  if (tty->TF_set_underline_style)
    /* Standard escape sequence to set the underline color.
       Requires a single parameter, the color index.  */
    tty->TF_set_underline_color = "\x1b[58:2::%p1%{65536}%/%d:%p1%{256}%/%{255}%&%d:%p1%{255}%&%dm";

#else /* DOS_NT */
#ifdef WINDOWSNT
  {
    struct frame *f = XFRAME (selected_frame);
    int height, width;

    initialize_w32_display (terminal, &width, &height);

    FrameRows (tty) = height;
    FrameCols (tty) = width;
    tty->specified_window = height;

    FRAME_VERTICAL_SCROLL_BAR_TYPE (f) = vertical_scroll_bar_none;
    FRAME_HAS_HORIZONTAL_SCROLL_BARS (f) = 0;
    tty->char_ins_del_ok = 1;
    baud_rate = 19200;
  }
#else  /* MSDOS */
  {
    int height, width;
    if (strcmp (terminal_type, "internal") == 0)
      terminal->type = output_msdos_raw;
    initialize_msdos_display (terminal);

    get_tty_size (fileno (tty->input), &width, &height);
    FrameCols (tty) = width;
    FrameRows (tty) = height;
    tty->char_ins_del_ok = 0;
    init_baud_rate (fileno (tty->input));
  }
#endif	/* MSDOS */
  tty->output = stdout;
  tty->input = stdin;
  /* The following two are inaccessible from w32console.c.  */
  terminal->delete_frame_hook = &tty_free_frame_resources;
  terminal->delete_terminal_hook = &delete_tty;

  tty->name = xstrdup (name);
  terminal->name = xstrdup (name);
  tty->type = xstrdup (terminal_type);

  add_keyboard_wait_descriptor (0);

  tty->delete_in_insert_mode = 1;

  UseTabs (tty) = 0;
  tty->scroll_region_ok = 0;

  /* Seems to insert lines when it's not supposed to, messing up the
     display.  In doing a trace, it didn't seem to be called much, so I
     don't think we're losing anything by turning it off.  */
  tty->line_ins_del_ok = 0;

  tty->TN_max_colors = 16;  /* Must be non-zero for tty-display-color-p.  */
#endif	/* DOS_NT */

#ifdef HAVE_GPM
  terminal->mouse_position_hook = term_mouse_position;
#endif
  tty->mouse_highlight.mouse_face_window = Qnil;

  terminal->kboard = allocate_kboard (Qnil);
  terminal->kboard->reference_count++;
  /* Don't let the initial kboard remain current longer than necessary.
     That would cause problems if a file loaded on startup tries to
     prompt in the mini-buffer.  */
  if (current_kboard == initial_kboard)
    current_kboard = terminal->kboard;
#ifndef DOS_NT
  term_get_fkeys (address, terminal->kboard);

  /* Get frame size from system, or else from termcap.  */
  {
    int height, width;
    get_tty_size (fileno (tty->input), &width, &height);
    FrameCols (tty) = width;
    FrameRows (tty) = height;
  }

  if (FrameCols (tty) <= 0)
    FrameCols (tty) = tgetnum ("co");
  if (FrameRows (tty) <= 0)
    FrameRows (tty) = tgetnum ("li");

  if (FrameRows (tty) < 3 || FrameCols (tty) < 3)
    maybe_fatal (must_succeed, terminal,
                 "Screen size %dx%d is too small",
                 "Screen size %dx%d is too small",
                 FrameCols (tty), FrameRows (tty));

  TabWidth (tty) = tgetnum ("tw");

  if (!tty->TS_bell)
    tty->TS_bell = "\07";

  if (!tty->TS_fwd_scroll)
    tty->TS_fwd_scroll = Down (tty);

  PC = tty->TS_pad_char ? *tty->TS_pad_char : 0;

  if (TabWidth (tty) < 0)
    TabWidth (tty) = 8;

/* Turned off since /etc/termcap seems to have :ta= for most terminals
   and newer termcap doc does not seem to say there is a default.
  if (!tty->Wcm->cm_tab)
    tty->Wcm->cm_tab = "\t";
*/

  /* We don't support standout modes that use `magic cookies', so
     turn off any that do.  */
  if (tty->TS_standout_mode && tgetnum ("sg") >= 0)
    {
      tty->TS_standout_mode = 0;
      tty->TS_end_standout_mode = 0;
    }
  if (tty->TS_enter_underline_mode && tgetnum ("ug") >= 0)
    {
      tty->TS_enter_underline_mode = 0;
      tty->TS_exit_underline_mode = 0;
    }

  /* If there's no standout mode, try to use underlining instead.  */
  if (tty->TS_standout_mode == 0)
    {
      tty->TS_standout_mode = tty->TS_enter_underline_mode;
      tty->TS_end_standout_mode = tty->TS_exit_underline_mode;
    }

  /* If no `se' string, try using a `me' string instead.
     If that fails, we can't use standout mode at all.  */
  if (tty->TS_end_standout_mode == 0)
    {
      char *s = tgetstr ("me", address);
      if (s != 0)
        tty->TS_end_standout_mode = s;
      else
        tty->TS_standout_mode = 0;
    }

  if (tty->TF_teleray)
    {
      tty->Wcm->cm_tab = 0;
      /* We can't support standout mode, because it uses magic cookies.  */
      tty->TS_standout_mode = 0;
      /* But that means we cannot rely on ^M to go to column zero!  */
      CR (tty) = 0;
      /* LF can't be trusted either -- can alter hpos.  */
      /* If move at column 0 thru a line with TS_standout_mode.  */
      Down (tty) = 0;
    }

  tty->specified_window = FrameRows (tty);

  if (Wcm_init (tty) == -1)	/* Can't do cursor motion.  */
    {
      maybe_fatal (must_succeed, terminal,
                   "Terminal type \"%s\" is not powerful enough to run Emacs",
                   "Terminal type \"%s\" is not powerful enough to run Emacs.\n\
It lacks the ability to position the cursor.\n\
If that is not the actual type of terminal you have,\n\
use the Bourne shell command 'TERM=...; export TERM' (C-shell:\n\
'setenv TERM ...') to specify the correct type.  It may be necessary\n"
# ifdef TERMINFO
"to do 'unset TERMINFO' (C-shell: 'unsetenv TERMINFO') as well.",
# else /* TERMCAP */
"to do 'unset TERMCAP' (C-shell: 'unsetenv TERMCAP') as well.",
# endif /* TERMINFO */
                   terminal_type);
    }

  if (FrameRows (tty) <= 0 || FrameCols (tty) <= 0)
    maybe_fatal (must_succeed, terminal,
                 "Could not determine the frame size",
                 "Could not determine the frame size");

  tty->delete_in_insert_mode
    = tty->TS_delete_mode && tty->TS_insert_mode
    && !strcmp (tty->TS_delete_mode, tty->TS_insert_mode);

  /* FIX-20261012-guilemacs: M54 imp-4 -- the terminal TAB policy runs
     in Scheme; C keeps the termios query and the state write.  Read the
     plain C value FIRST and keep it, so a nil verdict (no Scheme
     runtime) falls back to the present C behavior and does not force
     UseTabs to 0.  */
  {
    bool tabs_safe = tabs_safe_p (fileno (tty->input));
    Lisp_Object verdict
      = m54_tty_tabs_verdict_scheme (tabs_safe ? Qt : Qnil,
				     make_fixnum (TabWidth (tty)));
    UseTabs (tty)
      = NILP (verdict)
	? (tabs_safe && TabWidth (tty) == 8)
	: (STRINGP (verdict) && SBYTES (verdict) == 4
	   && memcmp (SSDATA (verdict), "tabs", 4) == 0);
  }

  tty->scroll_region_ok
    = (tty->Wcm->cm_abs
       && (tty->TS_set_window || tty->TS_set_scroll_region || tty->TS_set_scroll_region_1));

  tty->line_ins_del_ok
    = (((tty->TS_ins_line || tty->TS_ins_multi_lines)
        && (tty->TS_del_line || tty->TS_del_multi_lines))
       || (tty->scroll_region_ok
           && tty->TS_fwd_scroll && tty->TS_rev_scroll));

  tty->char_ins_del_ok
    = ((tty->TS_ins_char || tty->TS_insert_mode
        || tty->TS_pad_inserted_char || tty->TS_ins_multi_chars)
       && (tty->TS_del_char || tty->TS_del_multi_chars));

  init_baud_rate (fileno (tty->input));

#endif /* not DOS_NT */

  /* Init system terminal modes (RAW or CBREAK, etc.).  */
  init_sys_modes (tty);

  return terminal;
#endif /* !HAVE_ANDROID */
}


static void
vfatal (const char *str, va_list ap)
{
  fputs ("emacs: ", stderr);
  vfprintf (stderr, str, ap);
  if (! (str[0] && str[strlen (str) - 1] == '\n'))
    putc ('\n', stderr);
  exit (1);
}


/* Auxiliary error-handling function for init_tty.
   Delete TERMINAL, then call error or fatal with str1 or str2,
   respectively, according to whether MUST_SUCCEED is true.  */

static void
maybe_fatal (bool must_succeed, struct terminal *terminal,
	     const char *str1, const char *str2, ...)
{
  va_list ap;
  va_start (ap, str2);

#ifndef HAVE_ANDROID
  if (terminal)
    delete_tty (terminal);
#else
  eassert (terminal == NULL);
#endif

  if (must_succeed)
    vfatal (str2, ap);
  else
    verror (str1, ap);
}

void
fatal (const char *str, ...)
{
  va_list ap;
  va_start (ap, str);
  vfatal (str, ap);
}



#ifndef HAVE_ANDROID

/* Delete the given tty terminal, closing all frames on it.  */

static void
delete_tty (struct terminal *terminal)
{
  struct tty_display_info *tty;

  /* Protect against recursive calls.  delete_frame in
     delete_terminal calls us back when it deletes our last frame.  */
  if (!terminal->name)
    return;

  eassert (terminal->type == output_termcap);

  tty = terminal->display_info.tty;

  if (tty == tty_list)
    tty_list = tty->next;
  else
    {
      struct tty_display_info *p;
      for (p = tty_list; p && p->next != tty; p = p->next)
        ;

      if (! p)
        /* This should not happen.  */
        emacs_abort ();

      p->next = tty->next;
      tty->next = 0;
    }

  /* reset_sys_modes needs a valid device, so this call needs to be
     before delete_terminal.  */
  reset_sys_modes (tty);

  delete_terminal (terminal);

  xfree (tty->name);
  xfree (tty->type);

  if (tty->input)
    {
      delete_keyboard_wait_descriptor (fileno (tty->input));
      if (tty->input != stdin)
        emacs_fclose (tty->input);
    }
  if (tty->output && tty->output != stdout && tty->output != tty->input)
    emacs_fclose (tty->output);
  if (tty->termscript)
    emacs_fclose (tty->termscript);

  /* M61 imp-1: drop the handle identity BEFORE the struct is freed, so
     the table never holds a dangling pointer and a use of the dead
     identity answers -EBADF (docs/m61-plan.org section 6).  */
  m61_tty_handle_drop_1 (tty);

  xfree (tty->old_tty);
  xfree (tty->Wcm);
  xfree (tty);
}

#endif

/* Return geometric attributes of FRAME.  According to the value of
   ATTRIBUTES return the outer edges of FRAME (Qouter_edges), the
   native edges of FRAME (Qnative_edges), or the inner edges of frame
   (Qinner_edges).  Any other value means to return the geometry as
   returned by Fx_frame_geometry.  */

static Lisp_Object
tty_frame_geometry (Lisp_Object frame, Lisp_Object attribute)
{
  struct frame *f = decode_live_frame (frame);
  if (FRAME_INITIAL_P (f) || !FRAME_TTY (f))
    return Qnil;

  int native_width = f->pixel_width;
  int native_height = f->pixel_height;

  eassert (FRAME_PARENT_FRAME (f) || (f->left_pos == 0 && f->top_pos == 0));
  int outer_left = f->left_pos;
  int outer_top = f->top_pos;

  int internal_border_width = FRAME_INTERNAL_BORDER_WIDTH (f);
  int menu_bar_height = FRAME_MENU_BAR_HEIGHT (f);
  int tab_bar_height = FRAME_TAB_BAR_HEIGHT (f);
  int tool_bar_height = FRAME_TOOL_BAR_HEIGHT (f);
  bool tool_bar_on_top = EQ (FRAME_TOOL_BAR_POSITION (f), Qtop);

  /* The geometry arithmetic is a decision of Group G3: the module
     (emacs terminal) holds it.  The hub keeps the C-owned frame field
     reads, the edge-type conversion, and the alist build (the symbol
     rule); the leaf returns plain integers only.  */
  if (EQ (attribute, Qouter_edges) || EQ (attribute, Qnative_edges)
      || EQ (attribute, Qinner_edges))
    return term_frame_edges_scheme (make_fixnum (outer_left),
				    make_fixnum (outer_top),
				    make_fixnum (native_width),
				    make_fixnum (native_height),
				    make_fixnum (internal_border_width),
				    make_fixnum (menu_bar_height),
				    make_fixnum (tab_bar_height),
				    make_fixnum (tool_bar_height),
				    tool_bar_on_top ? Qt : Qnil,
				    EQ (attribute, Qinner_edges)
				    ? build_string ("inner")
				    : build_string ("outer"));

  /* Construct list.  */
  {
    Lisp_Object geometry
      = term_frame_geometry_scheme (make_fixnum (outer_left),
				    make_fixnum (outer_top),
				    make_fixnum (native_width),
				    make_fixnum (native_height),
				    make_fixnum (internal_border_width),
				    make_fixnum (menu_bar_height),
				    make_fixnum (tab_bar_height),
				    make_fixnum (tool_bar_height),
				    tool_bar_on_top ? Qt : Qnil);
    EMACS_INT vals[11];
    Lisp_Object tail = geometry;
    int i;

    for (i = 0; i < 11 && CONSP (tail); i++, tail = XCDR (tail))
      vals[i] = FIXNUMP (XCAR (tail)) ? XFIXNUM (XCAR (tail)) : 0;

    return list (Fcons (Qouter_position, Fcons (make_fixnum (vals[0]),
						make_fixnum (vals[1]))),
		 Fcons (Qouter_size,
			Fcons (make_fixnum (vals[2] - vals[0]),
			       make_fixnum (vals[3] - vals[1]))),
		 Fcons (Qouter_border_width, make_fixnum (0)),
		 Fcons (Qexternal_border_size,
			Fcons (make_fixnum (0), make_fixnum (0))),
		 Fcons (Qtitle_bar_size,
			Fcons (make_fixnum (0), make_fixnum (0))),
		 Fcons (Qmenu_bar_external, Qnil),
		 Fcons (Qmenu_bar_size,
			Fcons (make_fixnum (vals[8]),
			       make_fixnum (menu_bar_height))),
		 Fcons (Qtab_bar_size,
			Fcons (make_fixnum (vals[9]),
			       make_fixnum (tab_bar_height))),
		 Fcons (Qtool_bar_external, Qnil),
		 Fcons (Qtool_bar_position, FRAME_TOOL_BAR_POSITION (f)),
		 Fcons (Qtool_bar_size,
			Fcons (make_fixnum (vals[10]),
			       make_fixnum (tool_bar_height))),
		 Fcons (Qinternal_border_width,
			make_fixnum (internal_border_width)));
  }
}

DEFUN ("tty-frame-geometry", Ftty_frame_geometry, Stty_frame_geometry, 0, 1, 0,
       doc: /* Return geometric attributes of terminal frame FRAME.
See also `frame-geometry'.  */)
  (Lisp_Object frame)
{
  return tty_frame_geometry (frame, Qnil);
}

DEFUN ("tty-frame-edges", Ftty_frame_edges, Stty_frame_edges, 0, 2, 0,
       doc: /* Return coordinates of FRAME's edges.
See also `frame-edges'.  */)
  (Lisp_Object frame, Lisp_Object type)
{
  if (!EQ (type, Qouter_edges) && !EQ (type, Qinner_edges))
    type = Qnative_edges;
  return tty_frame_geometry (frame, type);
}

DEFUN ("tty-frame-list-z-order", Ftty_frame_list_z_order,
       Stty_frame_list_z_order, 0, 1, 0,
       doc: /* Return list of Emacs's frames, in Z (stacking) order.
See also `frame-list-z-order'.  */)
  (Lisp_Object frame)
{
  struct frame *f = decode_tty_frame (frame);
  Lisp_Object frames = frames_in_reverse_z_order (f, true);
  return Fnreverse (frames);
}

DEFUN ("tty-frame-restack", Ftty_frame_restack,
       Stty_frame_restack, 2, 3, 0,
       doc: /* Restack FRAME1 below FRAME2 on terminals.
See also `frame-restack'.  */
       attributes: noreturn)
  (Lisp_Object frame1, Lisp_Object frame2, Lisp_Object above)
{
  /* FIXME/tty: tty-frame-restack implementation.  */
  error ("tty-frame-restack is not implemented");
}

static void
tty_display_dimension (Lisp_Object frame, int *width, int *height)
{
  if (!FRAMEP (frame))
    frame = Fselected_frame ();
  struct frame *f = XFRAME (frame);
  switch (f->output_method)
    {
    case output_initial:
      *width = XFIXNUM (term_display_pixel_width_scheme (Qt, Qnil));
      *height = XFIXNUM (term_display_pixel_height_scheme (Qt, Qnil));
      break;
    case output_termcap:
      *width = XFIXNUM (term_display_pixel_width_scheme
			(Qnil, make_fixnum (FrameCols (FRAME_TTY (f)))));
      *height = XFIXNUM (term_display_pixel_height_scheme
			 (Qnil, make_fixnum (FrameRows (FRAME_TTY (f)))));
      break;
    case output_x_window:
    case output_msdos_raw:
    case output_w32:
    case output_ns:
    case output_pgtk:
    case output_haiku:
    case output_android:
    default:
      emacs_abort ();
      break;
    }
}

DEFUN ("tty-display-pixel-width", Ftty_display_pixel_width,
       Stty_display_pixel_width, 0, 1, 0,
       doc: /* Return the width of DISPLAY's screen in pixels.
See also `display-pixel-width'.  */)
  (Lisp_Object display)
{
  int width, height;
  tty_display_dimension (display, &width, &height);
  return make_fixnum (width);
}

DEFUN ("tty-display-pixel-height", Ftty_display_pixel_height,
       Stty_display_pixel_height, 0, 1, 0,
       doc: /* Return the height of DISPLAY's screen in pixels.
See also `display-pixel-height'.  */)
  (Lisp_Object display)
{
  int width, height;
  tty_display_dimension (display, &width, &height);
  return make_fixnum (height);
}

/* FIX-20261005-guilemacs: M48 imp-2.  The typed C leaves over plain
   values for the src/term.c TTY terminal boundary.  Each leaf returns
   one plain value (a boolean, an integer, a string, or a list of plain
   values) and holds the decision of its MOVES block; the caller passes
   plain values in.  The mechanism (the struct tty_display_info and its
   fields, the terminfo handle, the tputs output to the tty fd, and the
   syscalls) stays in C.  imp-2 adds leaves only: it moves no policy.
   imp-3 (G1) and imp-4 (G3) rewire the C hubs onto these leaves and
   delete the inline policy.  See docs/m48-plan.org section 3.3 and
   brief.org section 4.

   Each leaf below ports an unguarded DEFUN of src/term.c, so its body
   carries no #if guard.  A leaf returns plain values only: no char *,
   FILE *, struct tty_display_info *, struct terminal *, or Lisp_Object
   crosses the layer (the M42 rule).  The C hub owns the C-owned field
   read, the frame fields, and the alist build (the symbol rule).  */

/* --- G1: the terminal-capability policy ---------------------------- */

DEFUN ("--term-display-color-p", Fc_term_display_color_p,
       Sc_term_display_color_p, 1, 1, 0,
       doc: /* FIX-20261005-guilemacs: Internal: return a *plain boolean*:
t when the color count COLORS is a positive integer, else nil.  COLORS
is a plain integer, or nil for "not a tty".  M48 imp-2, docs/m48-plan.org
section 3.3.  */)
  (Lisp_Object colors)
{
  return (FIXNUMP (colors) && 0 < XFIXNUM (colors)) ? Qt : Qnil;
}

DEFUN ("--term-display-color-cells", Fc_term_display_color_cells,
       Sc_term_display_color_cells, 1, 1, 0,
       doc: /* FIX-20261005-guilemacs: Internal: return the color count
COLORS as a *plain integer*; nil or a non-integer yields 0.  M48 imp-2,
docs/m48-plan.org section 3.3.  */)
  (Lisp_Object colors)
{
  return make_fixnum (FIXNUMP (colors) ? XFIXNUM (colors) : 0);
}

DEFUN ("--term-type", Fc_term_type, Sc_term_type, 1, 1, 0,
       doc: /* FIX-20261005-guilemacs: Internal: return the terminal type
TYPE as a *plain string*, or nil.  M48 imp-2, docs/m48-plan.org
section 3.3.  */)
  (Lisp_Object type)
{
  return STRINGP (type) ? type : Qnil;
}

DEFUN ("--term-controlling-tty-p", Fc_term_controlling_tty_p,
       Sc_term_controlling_tty_p, 2, 2, 0,
       doc: /* FIX-20261005-guilemacs: Internal: return a *plain boolean*:
t when the tty name NAME equals DEV-TTY, else nil.  Both names cross as
plain strings (the string rule, docs/m48-plan.org section 3.3) and the
leaf runs the compare, so no char * crosses the layer.  M48 imp-2,
docs/m48-plan.org section 3.3.  */)
  (Lisp_Object name, Lisp_Object dev_tty)
{
  return (STRINGP (name) && STRINGP (dev_tty)
	  && SBYTES (name) == SBYTES (dev_tty)
	  && memcmp (SSDATA (name), SSDATA (dev_tty), SBYTES (name)) == 0)
	 ? Qt : Qnil;
}

/* --- G3: the query / geometry policy ------------------------------- */

/* FIX-20261005-guilemacs: M48 imp-6 -- the geometry arithmetic moved to
   (emacs terminal).  The static helper term_frame_geometry_1 and the two
   typed leaves --term-frame-geometry and --term-frame-edges are deleted:
   each was reached through a Scheme pass-through, so the decision never
   left C (docs/m48-port-review.org).  term_frame_geometry_scheme and
   term_frame_edges_scheme now call the module procedure that holds the
   arithmetic.  The C hub keeps decode_live_frame, the FRAME_INITIAL_P /
   FRAME_TTY guard, every frame field read, and the alist build.  */

DEFUN ("--term-display-pixel-width", Fc_term_display_pixel_width,
       Sc_term_display_pixel_width, 2, 2, 0,
       doc: /* FIX-20261005-guilemacs: Internal: return the display width
as a *plain integer*.  When INITIAL (a plain boolean) is non-nil the
leaf returns 80, the output_initial constant; else it returns the plain
integer WIDTH.  D-c: the FrameCols read and the abort stay C.  M48 imp-2,
docs/m48-plan.org section 3.3.  */)
  (Lisp_Object initial, Lisp_Object width)
{
  if (!NILP (initial))
    return make_fixnum (80);
  return make_fixnum (FIXNUMP (width) ? XFIXNUM (width) : 0);
}

DEFUN ("--term-display-pixel-height", Fc_term_display_pixel_height,
       Sc_term_display_pixel_height, 2, 2, 0,
       doc: /* FIX-20261005-guilemacs: Internal: return the display height
as a *plain integer*.  When INITIAL (a plain boolean) is non-nil the
leaf returns 25, the output_initial constant; else it returns the plain
integer HEIGHT.  D-c: the FrameRows read and the abort stay C.  M48 imp-2,
docs/m48-plan.org section 3.3.  */)
  (Lisp_Object initial, Lisp_Object height)
{
  if (!NILP (initial))
    return make_fixnum (25);
  return make_fixnum (FIXNUMP (height) ? XFIXNUM (height) : 0);
}

/* --- M52 imp-3: the TTY output boundary leaves --------------------- */

/* FIX-20261009-guilemacs: M52 imp-3 -- the src/term.c TTY output
   boundary.  These 4 typed leaves cross plain values only: an opaque
   DEVICE handle, a plain capability KEY string, a plain fixnum ARGS
   list, and a plain bytevector.  The C-owned struct tty_display_info
   and its FILE *output / *termscript streams stay in C.  Each leaf
   calls the write mechanism (tparam / fwrite), never a public hub
   (docs/kb.org =leaf-must-call-the-mechanism=).  A leaf returns a
   fixnum byte count, or a negative fixnum holding the negated errno
   (docs/kb.org =leaf-return-shape-preserves-signal=).  C stays the
   single writer of output / termscript; no Guile port owns a FILE *
   (docs/kb.org =passthrough-leaf-is-not-a-port=).  imp-3 moves no
   policy: the selection and the arithmetic stay in C until imp-4.

   F3 (cr1.org, for imp-4): the real termcap output path is the OUTPUT
   macro (src/term.c), which calls emacs_tputs and applies padding.
   m52_tty_emit_cap_1 calls tparam and a raw fwrite, so it does NOT
   apply padding.  imp-3 rewires nothing, so there is no regression
   today.  imp-4 MUST NOT lose the padding behaviour: either call
   emacs_tputs, or record the padding decision in docs/m52-plan.org.  */

/* Resolve the plain DEVICE handle to its struct tty_display_info *, or
   NULL.  m22_tty_of_terminal (src/keyboard.c) is static, so it is not
   reachable here; this decodes through decode_tty_terminal, the same
   mechanism (src/termhooks.h).  The name m52_tty_of_device_1 reuses no
   existing static name (docs/kb.org
   =term-hub-helper-name-collision=).  */
static struct tty_display_info *
m52_tty_of_device_1 (Lisp_Object device)
{
  struct terminal *t = decode_tty_terminal (device);
  return t ? t->display_info.tty : NULL;
}

/* One entry of the capability table: the plain KEY string and the byte
   offset of the matching tty->TS_<cap> member.  imp-3 lists the caps
   the MOVES output blocks use (docs/m52-plan.org section 8.4).  */
struct m52_cap_entry
{
  const char *key;
  size_t offset;
};

#define M52_CAP(key, field) { key, offsetof (struct tty_display_info, field) }
static const struct m52_cap_entry m52_caps[] =
  {
    M52_CAP ("bell", TS_bell),
    M52_CAP ("visible-bell", TS_visible_bell),
    M52_CAP ("clear-to-bottom", TS_clr_to_bottom),
    M52_CAP ("clear-line", TS_clr_line),
    M52_CAP ("clear-frame", TS_clr_frame),
    M52_CAP ("set-scroll-region", TS_set_scroll_region),
    M52_CAP ("set-scroll-region-1", TS_set_scroll_region_1),
    M52_CAP ("set-window", TS_set_window),
    M52_CAP ("insert-mode", TS_insert_mode),
    M52_CAP ("end-insert-mode", TS_end_insert_mode),
    M52_CAP ("standout-mode", TS_standout_mode),
    M52_CAP ("end-standout-mode", TS_end_standout_mode),
    M52_CAP ("cursor-normal", TS_cursor_normal),
    M52_CAP ("cursor-visible", TS_cursor_visible),
    M52_CAP ("cursor-invisible", TS_cursor_invisible),
    M52_CAP ("termcap-modes", TS_termcap_modes),
    M52_CAP ("end-termcap-modes", TS_end_termcap_modes),
    M52_CAP ("keypad-mode", TS_keypad_mode),
    M52_CAP ("end-keypad-mode", TS_end_keypad_mode),
    M52_CAP ("orig-pair", TS_orig_pair),
    M52_CAP ("ins-line", TS_ins_line),
    M52_CAP ("del-line", TS_del_line),
    M52_CAP ("ins-multi-lines", TS_ins_multi_lines),
    M52_CAP ("del-multi-lines", TS_del_multi_lines),
    M52_CAP ("ins-char", TS_ins_char),
    M52_CAP ("ins-multi-chars", TS_ins_multi_chars),
    M52_CAP ("del-char", TS_del_char),
    M52_CAP ("del-multi-chars", TS_del_multi_chars),
    M52_CAP ("delete-mode", TS_delete_mode),
    M52_CAP ("end-delete-mode", TS_end_delete_mode),
    /* M58 imp-3: the 7 NON-parameterized face keys of turn_on_face /
       turn_off_face.  The parameterized strings TS_set_foreground,
       TS_set_background, TF_set_underline_color, and
       TF_set_underline_style are NOT listed: they hold tparam format
       directives, so an emit without tparam changes the bytes.  They
       use the ("tparam" SLOT VALUE) step instead (brief.org section 6).  */
    M52_CAP ("bold", TS_enter_bold_mode),
    M52_CAP ("dim", TS_enter_dim_mode),
    M52_CAP ("italic", TS_enter_italic_mode),
    M52_CAP ("underline", TS_enter_underline_mode),
    M52_CAP ("strike-through", TS_enter_strike_through_mode),
    M52_CAP ("exit-attribute", TS_exit_attribute_mode),
    M52_CAP ("exit-underline", TS_exit_underline_mode)
  };
#undef M52_CAP

/* Look CAP (a plain string, or nil) up in the table and return the
   matching tty->TS_<cap> string, or NULL when TTY is NULL or CAP names
   no known capability.  The absent case yields NULL, so the caller
   emits nothing.  */
static const char *
m52_cap_string_1 (struct tty_display_info *tty, Lisp_Object cap)
{
  if (!tty || !STRINGP (cap))
    return NULL;
  for (size_t i = 0; i < ARRAYELTS (m52_caps); i++)
    if (SBYTES (cap) == strlen (m52_caps[i].key)
	&& memcmp (SSDATA (cap), m52_caps[i].key, SBYTES (cap)) == 0)
      return *(const char **) ((char *) tty + m52_caps[i].offset);
  return NULL;
}

/* --- M54 imp-2: the output after-write verdict dispatcher ------------ */

/* FIX-20261012-guilemacs: M54 imp-2 -- call the pure verdict procedure
   of (emacs tty-output) that holds the after-write DECISION of ONE
   output write: "done" / "retry" / "give-up".  It resolves the module
   procedure one time (the M52 imp-4 idiom), caches it in a static SCM,
   and passes plain fixnums only.  C owns the FILE *, the =fwrite=, the
   =clearerr=, and the return shape; C stays the single writer.  The
   m54_ / _scheme name reuses no static helper (docs/kb.org
   =term-hub-helper-name-collision=).  */

static Lisp_Object
m54_tty_write_verdict_scheme (Lisp_Object written, Lisp_Object len,
			      Lisp_Object err)
{
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs tty-output", "tty-write-verdict");
  return SCM_CALL_3 (proc, written, len, err);
}

/* True when the plain verdict string is "give-up", and true for a nil
   verdict too.  A nil verdict means there is no Scheme runtime, and then
   the present C behavior of BOTH output writers is the give-up behavior:
   report the negated errno (cr.org F4).  Keeping the test here means the
   two writers share ONE decision site.  */
static bool
m54_tty_write_gives_up_p (Lisp_Object verdict)
{
  if (NILP (verdict))
    return true;
  return (STRINGP (verdict)
	  && SBYTES (verdict) == sizeof "give-up" - 1
	  && memcmp (SSDATA (verdict), "give-up", sizeof "give-up" - 1) == 0);
}

/* The ONE site that asks Scheme for the after-write verdict of an output
   write.  WRITTEN is the =fwrite= count, LEN the requested count, and ERR
   the plain errno.  Return the plain verdict value, which the caller
   tests with m54_tty_write_gives_up_p; a nil value means there is no
   Scheme runtime and the present C behavior holds (M61 imp-1 added the
   second caller, the normal glyph write, so the site stays ONE).  */
static Lisp_Object
m54_tty_write_verdict_1 (size_t written, size_t len, int err)
{
  return m54_tty_write_verdict_scheme (make_fixnum (written),
				       make_fixnum (len), make_fixnum (err));
}

/* --- M54 imp-3: the termscript copy decision ------------------------- */

/* FIX-20261012-guilemacs: M54 imp-3 -- a termscript is a COPY of the
   terminal output (src/termchar.h :61).  ONE operation of that copy
   stream moves to Scheme: the after-write DECISION of ONE copy write.
   C keeps the FILE *termscript and the =fwrite=, and it keeps the
   OUTPUT =clearerr= (M54 imp-2).  C stays the single writer, so no port
   and no FILE * crosses the seam.
   The copy votes through the REUSED m54_tty_write_verdict_scheme
   dispatcher (brief.org section 4): the copy and the output share ONE
   verdict procedure, tty-write-verdict.  The plain counts also build
   the imp-2 tty-out-handle in Scheme (brief.org section 9, Option A);
   C does not read the handle, so the handle is BORROWED, not
   transferred.  The m54_tty_termscript_ name reuses no static helper
   (docs/kb.org =term-hub-helper-name-collision=).  */
static Lisp_Object
m54_tty_termscript_handle_scheme (Lisp_Object copied, Lisp_Object len,
                                  Lisp_Object err)
{
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs tty-output", "tty-termscript-copy-handle");
  return SCM_CALL_3 (proc, copied, len, err);
}

/* The after-write DECISION of ONE termscript copy write, borrowed from
   Scheme.  COPIED is the plain =fwrite= count; LEN is the requested
   count; ERR is the errno that the CALLER saved (cr.org F3); FAILED is
   the plain C ferror result.  done / retry / give-up comes from the
   shared tty-write-verdict procedure.  C keeps the OUTPUT count as the
   return value, so the copy verdict never changes the return shape; a
   nil verdict keeps the C behavior, so the result is discarded.  */
static void
m54_tty_termscript_verdict (size_t copied, size_t len, int err, bool failed)
{
  int e = (copied < len && failed) ? (err ? err : EIO) : 0;
  Lisp_Object verdict
    = m54_tty_write_verdict_scheme (make_fixnum (copied), make_fixnum (len),
                                    make_fixnum (e));
  /* Record the plain copy counts in the BORROWED tty-out-handle.  C
     does not read it (borrowed, not transferred).  */
  m54_tty_termscript_handle_scheme (make_fixnum (copied), make_fixnum (len),
                                    make_fixnum (e));
  (void) verdict;
}

/* --- M54 imp-4: the input stream TAB policy dispatcher --------------- */

/* FIX-20261012-guilemacs: M54 imp-4 -- the terminal TAB policy UseTabs
   of ONE tty init (src/term.c :5030).  ONE decision of the
   src/termchar.h INPUT stream (src/termchar.h :51) moves to Scheme.  C
   keeps the mechanism: it calls tabs_safe_p (fileno (tty->input)) (the
   termios read on the C descriptor) and it reads TabWidth (tty) (a plain
   fixnum).  It passes the two PLAIN values (a boolean and a fixnum) to
   Scheme; Scheme owns the pure DECISION and returns the plain string
   "tabs" or "spaces".  C stores the result in UseTabs (tty).  No FILE *,
   no struct tty_display_info *, and no port crosses the seam
   (docs/kb.org =passthrough-leaf-is-not-a-port=).  The dispatcher
   resolves the module procedure one time (the M52 imp-4 idiom), caches
   it in a static SCM, and passes plain values only.  The m54_tty_tabs_
   name reuses no static helper (docs/kb.org
   =term-hub-helper-name-collision=).  */
static Lisp_Object
m54_tty_tabs_verdict_scheme (Lisp_Object tabs_safe, Lisp_Object tab_width)
{
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs tty-output", "tty-tab-verdict");
  return SCM_CALL_2 (proc, tabs_safe, tab_width);
}

/* Write LEN bytes at STR to tty->output and, when set, tty->termscript.
   Return the number of bytes written, or the negated errno on a hard
   failure, or -EINVAL when TTY holds no output stream.  C keeps the
   =clearerr= after each write.  The after-write verdict of a short write
   runs in Scheme (M54 imp-2): tty-write-verdict decides done / retry /
   give-up from the plain counts.  The =FILE *= streams stay C, so no
   port crosses the seam (=passthrough-leaf-is-not-a-port=).  */
static ptrdiff_t
m52_tty_write_1 (struct tty_display_info *tty, const char *str, size_t len)
{
  if (!tty || !tty->output)
    return -EINVAL;
  size_t written = fwrite (str, 1, len, tty->output);
  /* FIX-20261012-guilemacs: M54 imp-3 cr.org F3 -- save the output errno
     before the copy seam, whose Scheme calls can change errno.  */
  int out_err = errno;
  if (tty->termscript)
    {
      size_t copied = fwrite (str, 1, len, tty->termscript);
      int copy_err = errno;
      m54_tty_termscript_verdict (copied, len, copy_err,
				  ferror (tty->termscript) != 0);
    }
  if (written < len && ferror (tty->output))
    {
      int e = out_err ? out_err : EIO;
      Lisp_Object verdict = m54_tty_write_verdict_1 (written, len, e);
      clearerr (tty->output);
      /* The nil (no Scheme runtime) case is inside the helper, so both
	 output writers decide alike (cr.org F4).  */
      if (m54_tty_write_gives_up_p (verdict))
	return -e;
      return (ptrdiff_t) written;
    }
  clearerr (tty->output);
  return (ptrdiff_t) written;
}

/* Emit one capability of TTY.  CAP names a TS_* string; ARGS is a plain
   fixnum list applied through =tparam=.  This is the shared mechanism
   of --tty-emit-cap and --tty-emit-seq.  Return the byte count, or the
   negated errno (-ENOMEM when tparam returns NULL).  */
static ptrdiff_t
m52_tty_emit_cap_1 (struct tty_display_info *tty, Lisp_Object cap,
		    Lisp_Object args)
{
  if (!tty)
    return -EINVAL;
  const char *str = m52_cap_string_1 (tty, cap);
  if (!str)
    return 0;
  int a[4] = { 0, 0, 0, 0 };
  int n = 0;
  for (Lisp_Object l = args; CONSP (l) && n < 4; l = XCDR (l))
    {
      Lisp_Object x = XCAR (l);
      a[n++] = FIXNUMP (x) ? (int) XFIXNUM (x) : 0;
    }
  if (n == 0)
    return m52_tty_write_1 (tty, str, strlen (str));
  char *buf = tparam (str, 0, 0, a[0], a[1], a[2], a[3]);
  ptrdiff_t rc = buf ? m52_tty_write_1 (tty, buf, strlen (buf)) : -ENOMEM;
  xfree (buf);
  return rc;
}

DEFUN ("--tty-emit-cap", Fc_tty_emit_cap, Sc_tty_emit_cap, 3, 3, 0,
       doc: /* FIX-20261009-guilemacs: Internal: emit one termcap
capability of DEVICE.  DEVICE is an opaque plain handle (a terminal
object, a frame, or nil for the selected frame); CAP is a plain string
naming one TS_* capability; ARGS is a plain fixnum list applied through
=tparam=.  C looks up the TS_* string and writes it to the C-owned
output and termscript streams; the char * and the FILE * stay in C
(docs/kb.org =passthrough-leaf-is-not-a-port=).  Return a plain fixnum:
the byte count, or a negative fixnum holding the negated errno (-EINVAL
when DEVICE is nil / does not resolve to a tty, the same shape as
--tty-write-bytes and --tty-flush).  A
short write is reported as its count, so Scheme decides retry / give-up.
M52 imp-3, brief.org section 5.1.  */)
  (Lisp_Object device, Lisp_Object cap, Lisp_Object args)
{
  struct tty_display_info *tty = m52_tty_of_device_1 (device);
  return make_fixnum (m52_tty_emit_cap_1 (tty, cap, args));
}

DEFUN ("--tty-write-bytes", Fc_tty_write_bytes, Sc_tty_write_bytes, 2, 2, 0,
       doc: /* FIX-20261009-guilemacs: Internal: write the plain
bytevector BYTES to the C-owned output and termscript streams of
DEVICE (the bell / newline path).  DEVICE is an opaque plain handle.
C owns the FILE * streams; a Guile port must not own them (docs/kb.org
=passthrough-leaf-is-not-a-port=).  Return a plain fixnum: the byte
count, or a negative fixnum holding the negated errno (-EINVAL when
DEVICE holds no output stream).  M52 imp-3, brief.org section 5.1.  */)
  (Lisp_Object device, Lisp_Object bytes)
{
  struct tty_display_info *tty = m52_tty_of_device_1 (device);
  /* BYTES is a plain Guile bytevector (the same representation the M43
     leaf --tty-get-mode uses for c_cc).  A Guile bytevector carries raw
     bytes, so the bell / newline path never carries a Lisp_Object,
     char *, or FILE * across the layer.  A non-bytevector is a
     programming error.  */
  if (!scm_is_bytevector (bytes))
    return make_fixnum (-EINVAL);
  return make_fixnum
    (m52_tty_write_1 (tty, (const char *) SCM_BYTEVECTOR_CONTENTS (bytes),
		      scm_c_bytevector_length (bytes)));
}

DEFUN ("--tty-flush", Fc_tty_flush, Sc_tty_flush, 1, 1, 0,
       doc: /* FIX-20261009-guilemacs: Internal: flush the C-owned output
stream of DEVICE (=fflush=).  DEVICE is an opaque plain handle.  Return
a plain fixnum: 0 on success, or a negative fixnum holding the negated
errno.  The =tcdrain= drain stays in src/sysdep.c; this leaf does not
move it.  M52 imp-3, brief.org section 5.1.  */)
  (Lisp_Object device)
{
  struct tty_display_info *tty = m52_tty_of_device_1 (device);
  if (!tty || !tty->output)
    return make_fixnum (-EINVAL);
  if (fflush (tty->output) != 0)
    return make_fixnum (-(errno ? errno : EIO));
  return make_fixnum (0);
}

DEFUN ("--tty-emit-seq", Fc_tty_emit_seq, Sc_tty_emit_seq, 2, 2, 0,
       doc: /* FIX-20261009-guilemacs: Internal: apply one ordered
sequence SEQ of (CAP . ARGS) items to DEVICE.  DEVICE is an opaque
plain handle; CAP is a plain string naming one TS_* capability and ARGS
is its plain fixnum list.  This is the thin entry point: it runs the
same mechanism as --tty-emit-cap for each item and adds no policy.  An
item that names no known capability emits nothing.  Return a plain
fixnum: the total byte count, or the negated errno of the first item
that fails hard (-EINVAL when DEVICE is nil / does not resolve to a
tty).  M52 imp-3, brief.org
section 5.1.  */)
  (Lisp_Object device, Lisp_Object seq)
{
  struct tty_display_info *tty = m52_tty_of_device_1 (device);
  ptrdiff_t total = 0;
  for (Lisp_Object l = seq; CONSP (l); l = XCDR (l))
    {
      Lisp_Object item = XCAR (l);
      Lisp_Object cap = CONSP (item) ? XCAR (item) : item;
      Lisp_Object args = CONSP (item) ? XCDR (item) : Qnil;
      ptrdiff_t rc = m52_tty_emit_cap_1 (tty, cap, args);
      if (rc < 0)
	return make_fixnum (rc);
      total += rc;
    }
  return make_fixnum (total);
}

/* --- M52 imp-4: the insert / highlight state-flip dispatchers ------- */

/* FIX-20261009-guilemacs: M52 imp-4 -- call the pure policy procedures
   of (emacs tty-output) that hold the DECISION of the 5 insert /
   highlight hubs.  Each dispatcher resolves its module procedure one
   time (the M48 imp-4 idiom), caches it in a static SCM, and passes a
   plain fixnum flag only.  The returned value is a plain KEY string, or
   nil, which the hub tests with NILP.  The C state write, the FILE *
   streams, and the OUTPUT / OUTPUT_IF padding stay in C.  The m52_ /
   _scheme name reuses no static helper (docs/kb.org
   =term-hub-helper-name-collision=).  */

static Lisp_Object
m52_tty_turn_on_insert_scheme (Lisp_Object insert_mode)
{
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs tty-output", "tty-turn-on-insert-cap");
  return SCM_CALL_1 (proc, insert_mode);
}

static Lisp_Object
m52_tty_turn_off_insert_scheme (Lisp_Object insert_mode)
{
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs tty-output", "tty-turn-off-insert-cap");
  return SCM_CALL_1 (proc, insert_mode);
}

static Lisp_Object
m52_tty_turn_off_highlight_scheme (Lisp_Object standout_mode)
{
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs tty-output", "tty-turn-off-highlight-cap");
  return SCM_CALL_1 (proc, standout_mode);
}

static Lisp_Object
m52_tty_turn_on_highlight_scheme (Lisp_Object standout_mode)
{
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs tty-output", "tty-turn-on-highlight-cap");
  return SCM_CALL_1 (proc, standout_mode);
}

/* M52 imp-5: the bell / cursor / update-end dispatchers.  Each resolves
   its module procedure one time (the M48 imp-4 idiom) and passes plain
   fixnum flags only.  ring_bell returns a plain KEY string; hide_cursor
   and show_cursor return an ordered KEY list, or nil; background and
   highlight_if_desired return a plain KEY string; update_end returns an
   ordered step-tag list.  The C state writes, the FILE * streams, and
   the OUTPUT / OUTPUT_IF padding stay in C.  The m52_ / _scheme name
   reuses no static helper (docs/kb.org
   =term-hub-helper-name-collision=).  */
static Lisp_Object
m52_tty_ring_bell_scheme (Lisp_Object vis_bell, Lisp_Object has_vis_bell)
{
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs tty-output", "tty-ring-bell-cap");
  return SCM_CALL_2 (proc, vis_bell, has_vis_bell);
}

static Lisp_Object
m52_tty_hide_cursor_scheme (Lisp_Object cursor_hidden)
{
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs tty-output", "tty-hide-cursor-cap");
  return SCM_CALL_1 (proc, cursor_hidden);
}

static Lisp_Object
m52_tty_show_cursor_scheme (Lisp_Object cursor_hidden, Lisp_Object vis_cursor)
{
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs tty-output", "tty-show-cursor-cap");
  return SCM_CALL_2 (proc, cursor_hidden, vis_cursor);
}

static Lisp_Object
m52_tty_background_highlight_scheme (Lisp_Object inv_video)
{
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs tty-output", "tty-background-highlight-cap");
  return SCM_CALL_1 (proc, inv_video);
}

static Lisp_Object
m52_tty_highlight_if_desired_scheme (Lisp_Object inv_video)
{
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs tty-output", "tty-highlight-if-desired-cap");
  return SCM_CALL_1 (proc, inv_video);
}

static Lisp_Object
m52_tty_update_end_scheme (Lisp_Object cursor_off_p)
{
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs tty-output", "tty-update-end-steps");
  return SCM_CALL_1 (proc, cursor_off_p);
}

static Lisp_Object
m52_tty_toggle_highlight_scheme (Lisp_Object standout_mode)
{
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs tty-output", "tty-toggle-highlight-cap");
  return SCM_CALL_1 (proc, standout_mode);
}

/* --- M52 imp-6: the terminal-mode / cursor-motion dispatchers ------- */

/* FIX-20261010-guilemacs: M52 imp-6 -- call the pure policy procedures
   of (emacs tty-output) that hold the DECISION of the 4 terminal-mode /
   cursor-motion hubs (tty_set_terminal_modes, tty_reset_terminal_modes,
   tty_cursor_to, tty_raw_cursor_to).  Each dispatcher resolves its
   module procedure one time (the M48 imp-4 idiom), caches it in a
   static SCM, and passes plain fixnums only.  The returned value is an
   ordered step list, or nil.  A KEY step is a plain string; a
   marker step is a plain list.  The C state write, the FILE * streams,
   the OUTPUT / OUTPUT_IF padding, and the cmgoto / newline / raw-CR
   mechanisms stay in C.  The m52_ / _scheme name reuses no static
   helper (docs/kb.org =term-hub-helper-name-collision=).  */

/* Return true when STEP is a plain marker list (TAG ARG...) whose TAG
   equals the plain string TAG.  Used to tell a KEY step (a string)
   apart from a marker step (a list).  */
static bool
m52_tty_step_tag_p (Lisp_Object step, const char *tag)
{
  /* Compare the tag bytes directly, as m52_cap_string_1 does, so the
     redisplay path allocates no Scheme string per step.  Every tag is an
     ASCII literal, so a byte compare equals a string compare.  */
  size_t len = strlen (tag);
  return (CONSP (step) && STRINGP (XCAR (step))
	  && SBYTES (XCAR (step)) == len
	  && memcmp (SSDATA (XCAR (step)), tag, len) == 0);
}

static Lisp_Object
m52_tty_set_terminal_modes_scheme (Lisp_Object has_termcap, Lisp_Object total_lines,
				   Lisp_Object vis_cursor)
{
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs tty-output", "tty-set-terminal-modes-steps");
  return SCM_CALL_3 (proc, has_termcap, total_lines, vis_cursor);
}

static Lisp_Object
m52_tty_reset_terminal_modes_scheme (void)
{
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs tty-output", "tty-reset-terminal-modes-steps");
  return SCM_CALL_0 (proc);
}

static Lisp_Object
m52_tty_cursor_to_scheme (Lisp_Object cur_y, Lisp_Object cur_x, Lisp_Object vpos,
			  Lisp_Object hpos, Lisp_Object standout_motion,
			  Lisp_Object insmode_motion)
{
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs tty-output", "tty-cursor-to-steps");
  return SCM_CALL_6 (proc, cur_y, cur_x, vpos, hpos, standout_motion,
		     insmode_motion);
}

static Lisp_Object
m52_tty_raw_cursor_to_scheme (Lisp_Object cur_y, Lisp_Object cur_x, Lisp_Object row,
			      Lisp_Object col, Lisp_Object standout_motion,
			      Lisp_Object insmode_motion)
{
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs tty-output", "tty-raw-cursor-to-steps");
  return SCM_CALL_6 (proc, cur_y, cur_x, row, col, standout_motion,
		     insmode_motion);
}

/* --- M52 imp-7: the clear dispatchers ------------------------------- */

/* FIX-20261010-guilemacs: M52 imp-7 -- call the pure policy procedures
   of (emacs tty-output) that hold the DECISION of the 3 clear hubs
   (tty_clear_to_end, tty_clear_frame, tty_clear_end_of_line).  Each
   dispatcher resolves its module procedure one time (the M48 imp-4
   idiom), caches it in a static SCM, and passes plain fixnums only.  The
   returned value is ONE step, or nil.  A KEY step is a plain string; a
   marker step is a plain list.  The C state, the FILE * streams, and the
   OUTPUT / OUTPUT1 padding stay in C.  The m52_ / _scheme name reuses no
   static helper (docs/kb.org =term-hub-helper-name-collision=).  */

static Lisp_Object
m52_tty_clear_to_end_scheme (Lisp_Object has_clr_to_bottom)
{
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs tty-output", "tty-clear-to-end-steps");
  return SCM_CALL_1 (proc, has_clr_to_bottom);
}

static Lisp_Object
m52_tty_clear_frame_scheme (Lisp_Object has_clr_frame)
{
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs tty-output", "tty-clear-frame-steps");
  return SCM_CALL_1 (proc, has_clr_frame);
}

static Lisp_Object
m52_tty_clear_end_of_line_scheme (Lisp_Object costs_set, Lisp_Object cur_x,
				  Lisp_Object first_unused_hpos,
				  Lisp_Object has_clr_line)
{
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs tty-output", "tty-clear-end-of-line-steps");
  return SCM_CALL_4 (proc, costs_set, cur_x, first_unused_hpos, has_clr_line);
}

/* --- M52 imp-8: the scroll / window / glyph arithmetic dispatchers --- */

/* FIX-20261010-guilemacs: M52 imp-8 -- call the pure policy procedures
   of (emacs tty-output) that hold the DECISION of the 4 arithmetic hubs
   (tty_set_terminal_window, tty_set_scroll_region, tty_delete_glyphs,
   tty_ins_del_lines).  Each dispatcher resolves its module procedure one
   time (the M48 imp-4 idiom), caches it in a static SCM, and passes
   plain fixnums only.  A returned KEY step is a plain string; a MARKER
   step is a plain list.  C keeps the C-owned state, the FILE * streams,
   tparam, and the OUTPUT / OUTPUT1 / OUTPUTL / OUTPUT_IF padding.  No
   hub emits through --tty-emit-cap (that leaf loses the padding).  The
   m52_ / _scheme name reuses no static helper (docs/kb.org
   =term-hub-helper-name-collision=).  */

/* Fill A[0 .. MAX-1] from the fixnum args of the marker STEP.  The caller
   zeroes A first, so an arg that the form does not use stays 0.  Return
   true when STEP is a list.  */
static bool
m52_tty_step_args_1 (Lisp_Object step, int *a, int max)
{
  int n = 0;
  if (!CONSP (step))
    return false;
  for (Lisp_Object l = XCDR (step); CONSP (l) && n < max; l = XCDR (l))
    {
      Lisp_Object x = XCAR (l);
      a[n++] = FIXNUMP (x) ? (int) XFIXNUM (x) : 0;
    }
  return true;
}

static Lisp_Object
m52_tty_set_terminal_window_scheme (Lisp_Object size, Lisp_Object total_lines,
				    Lisp_Object scroll_ok)
{
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs tty-output", "tty-set-terminal-window-steps");
  return SCM_CALL_3 (proc, size, total_lines, scroll_ok);
}

static Lisp_Object
m52_tty_set_scroll_region_scheme (Lisp_Object start, Lisp_Object stop,
				  Lisp_Object total_lines, Lisp_Object cols,
				  Lisp_Object has_sr, Lisp_Object has_sr1,
				  Lisp_Object has_window)
{
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs tty-output", "tty-set-scroll-region-steps");
  return SCM_CALL_7 (proc, start, stop, total_lines, cols, has_sr, has_sr1,
		     has_window);
}

static Lisp_Object
m52_tty_delete_glyphs_scheme (Lisp_Object n, Lisp_Object delete_in_insert_mode,
			      Lisp_Object has_del_multi_chars)
{
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs tty-output", "tty-delete-glyphs-steps");
  return SCM_CALL_3 (proc, n, delete_in_insert_mode, has_del_multi_chars);
}

static Lisp_Object
m52_tty_ins_del_lines_scheme (Lisp_Object vpos, Lisp_Object n,
			      Lisp_Object specified_window,
			      Lisp_Object total_lines, Lisp_Object scroll_ok,
			      Lisp_Object memory_below, Lisp_Object has_multi,
			      Lisp_Object has_single, Lisp_Object has_scroll)
{
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs tty-output", "tty-ins-del-lines-steps");
  /* The tree uses no SCM_CALL_9 form, so pass the 9 plain fixnums through
     the existing SCM_CALL_N (scm_call_n) form.  */
  SCM args[9];
  args[0] = vpos;          args[1] = n;           args[2] = specified_window;
  args[3] = total_lines;   args[4] = scroll_ok;   args[5] = memory_below;
  args[6] = has_multi;     args[7] = has_single;  args[8] = has_scroll;
  return SCM_CALL_N (proc, args, 9);
}

void
syms_of_term (void)
{
#include "term.x"

  DEFVAR_BOOL ("system-uses-terminfo", system_uses_terminfo,
    doc: /* Non-nil means the system uses terminfo rather than termcap.
This variable can be used by terminal emulator packages.  */);
#if defined TERMINFO || (defined HAVE_ANDROID && !defined ANDROID_STUBIFY)
  system_uses_terminfo = 1;
#else
  system_uses_terminfo = 0;
#endif

  DEFVAR_LISP ("suspend-tty-functions", Vsuspend_tty_functions,
    doc: /* Functions run after suspending a tty.
The functions are run with one argument, the terminal object to be suspended.
See `suspend-tty'.  */);
  Vsuspend_tty_functions = Qnil;


  DEFVAR_LISP ("resume-tty-functions", Vresume_tty_functions,
    doc: /* Functions run after resuming a tty.
The functions are run with one argument, the terminal object that was revived.
See `resume-tty'.  */);
  Vresume_tty_functions = Qnil;

  DEFVAR_BOOL ("visible-cursor", visible_cursor,
	       doc: /* Non-nil means to make the cursor very visible.
This only has an effect when running in a text terminal.
What means \"very visible\" is up to your terminal.  It may make the cursor
bigger, or it may make it blink, or it may do nothing at all.  */);
  visible_cursor = 1;

  DEFVAR_BOOL ("tty-menu-calls-mouse-position-function",
               tty_menu_calls_mouse_position_function,
    doc: /* Non-nil means TTY menu code will call `mouse-position-function'.
This should be set if the function in `mouse-position-function' does not
trigger redisplay.  */);
  tty_menu_calls_mouse_position_function = 0;

#if !defined DOS_NT && !defined HAVE_ANDROID
  default_orig_pair = NULL;
  default_set_foreground = NULL;
  default_set_background = NULL;
#endif /* !DOS_NT && !HAVE_ANDROID */

#ifndef HAVE_ANDROID
  encode_terminal_src = NULL;
  encode_terminal_dst = NULL;
#endif

  DEFSYM (Qtty_mode_set_strings, "tty-mode-set-strings");
  DEFSYM (Qtty_mode_reset_strings, "tty-mode-reset-strings");

#ifndef MSDOS
  DEFSYM (Qtty_menu_next_item, "tty-menu-next-item");
  DEFSYM (Qtty_menu_prev_item, "tty-menu-prev-item");
  DEFSYM (Qtty_menu_next_menu, "tty-menu-next-menu");
  DEFSYM (Qtty_menu_prev_menu, "tty-menu-prev-menu");
  DEFSYM (Qtty_menu_select, "tty-menu-select");
  DEFSYM (Qtty_menu_ignore, "tty-menu-ignore");
  DEFSYM (Qtty_menu_exit, "tty-menu-exit");
  DEFSYM (Qtty_menu_mouse_movement, "tty-menu-mouse-movement");
  DEFSYM (Qtty_menu_navigation_map, "tty-menu-navigation-map");
#endif
  DEFSYM (Qf0, "f0");
  DEFSYM (Qf10, "f10");
  DEFSYM (Qtty_set_up_initial_frame_faces,
	  "tty-set-up-initial-frame-faces");
  DEFSYM (Qsuspend_tty_functions, "suspend-tty-functions");
  DEFSYM (Qresume_tty_functions, "resume-tty-functions");
  DEFSYM (Qtty_menu_disabled_face, "tty-menu-disabled-face");
  DEFSYM (Qtty_menu_enabled_face, "tty-menu-enabled-face");
}
