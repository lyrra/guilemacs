/* Keyboard and mouse input; editor command loop.

Copyright (C) 1985-1989, 1993-1997, 1999-2025 Free Software Foundation,
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

#include <config.h>

#include <sys/stat.h>

#include "lisp.h"
#include "coding.h"
#include "termchar.h"
#include "termopts.h"
#include "frame.h"
#include "termhooks.h"
#include "macros.h"
#include "keyboard.h"
#include "guile_fns.h"
#include "window.h"
#include "commands.h"
#include "character.h"
#include "buffer.h"
#include "dispextern.h"
#include "syntax.h"
#include "intervals.h"
#include "keymap.h"
#include "blockinput.h"
#include "sysstdio.h"
#include "systime.h"
#include "atimer.h"
#include "process.h"
#include "menu.h"

#ifdef HAVE_TEXT_CONVERSION
#include "textconv.h"
#endif /* HAVE_TEXT_CONVERSION */

#ifdef HAVE_ANDROID
#include "android.h"
#endif /* HAVE_ANDROID */

#include "guile.h"
#include <errno.h>

#ifdef HAVE_PTHREAD
#include <pthread.h>
#endif
#ifdef MSDOS
#include "msdos.h"
#include <time.h>
#else /* not MSDOS */
#include <sys/ioctl.h>
#endif /* not MSDOS */

#if defined USABLE_FIONREAD && defined USG5_4
# include <sys/filio.h>
#endif

#include "syssignal.h"

#include <sys/types.h>
#include <unistd.h>
#include <fcntl.h>
#include <math.h>

#include <ignore-value.h>

#include <gc.h> /* for GC_collect_a_little */

#ifdef HAVE_WINDOW_SYSTEM
#include TERM_HEADER
#endif /* HAVE_WINDOW_SYSTEM */

#ifdef WINDOWSNT
char const DEV_TTY[] = "CONOUT$";
#else
char const DEV_TTY[] = "/dev/tty";
#endif
char *dev_tty;	/* set by init_keyboard */

/* Variables for blockinput.h:  */

/* Positive if interrupt input is blocked right now.  */
volatile int interrupt_input_blocked;

/* True means an input interrupt or alarm signal has arrived.
   The maybe_quit function checks this.  */
volatile bool pending_signals;

KBOARD *initial_kboard;
KBOARD *current_kboard;
static KBOARD *all_kboards;

/* True in the single-kboard state, false in the any-kboard state.  */
static bool single_kboard;

#ifdef HAVE_TEXT_CONVERSION

/* True if a key sequence is currently being read.  */
bool reading_key_sequence;

#endif /* HAVE_TEXT_CONVERSION */

/* Minimum allowed size of the recent_keys vector.  */
#define MIN_NUM_RECENT_KEYS (100)

/* Maximum allowed size of the recent_keys vector.  */
#if INTPTR_MAX <= INT_MAX
# define MAX_NUM_RECENT_KEYS (INT_MAX / EMACS_INT_WIDTH / 10)
#else
# define MAX_NUM_RECENT_KEYS (INT_MAX / EMACS_INT_WIDTH)
#endif

/* Index for storing next element into recent_keys.  */
static int recent_keys_index;

/* Total number of elements stored into recent_keys.  */
static int total_keys;

/* Size of the recent_keys vector.  */
static int lossage_limit = 3 * MIN_NUM_RECENT_KEYS;

/* This vector holds the last lossage_limit keystrokes.  */
static Lisp_Object recent_keys;

/* Vector holding the key sequence that invoked the current command.
   It is reused for each command, and it may be longer than the current
   sequence; this_command_key_count indicates how many elements
   actually mean something.
   It's easier to staticpro a single Lisp_Object than an array.  */
Lisp_Object this_command_keys;
ptrdiff_t this_command_key_count;

/* This vector is used as a buffer to record the events that were actually read
   by read_key_sequence.  */
static Lisp_Object raw_keybuf;
static int raw_keybuf_count;

#define GROW_RAW_KEYBUF							\
 if (raw_keybuf_count == ASIZE (raw_keybuf))				\
   raw_keybuf = larger_vector (raw_keybuf, 1, -1)

/* this_single_command_key_start (the number of elements of
   this_command_keys that precede this key sequence) was a C
   file-static; storage now lives in Scheme as a (define)
   variable in (emacs this-command-keys).  Access from C goes
   through the --this-single-command-key-start /
   --set-this-single-command-key-start DEFUN shims, whose bodies
   dispatch into Scheme.  */

/* For longjmp to where kbd input is being done.  */

static Lisp_Object getctag;

/* True while displaying for echoing.   Delays C-g throwing.  */

static bool echoing;

/* Non-null means we can start echoing at the next input pause even
   though there is something in the echo area.  */

static struct kboard *ok_to_echo_at_next_pause;

/* The kboard last echoing, or null for none.  Reset to 0 in
   cancel_echoing.  If non-null, and a current echo area message
   exists, and echo_message_buffer is eq to the current message
   buffer, we know that the message comes from echo_kboard.  */

struct kboard *echo_kboard;

/* The buffer used for echoing.  Set in echo_now, reset in
   cancel_echoing.  */

Lisp_Object echo_message_buffer;

/* Character that causes a quit.  Normally C-g.

   If we are running on an ordinary terminal, this must be an ordinary
   ASCII char, since we want to make it our interrupt character.

   If we are not running on an ordinary terminal, it still needs to be
   an ordinary ASCII char.  This character needs to be recognized in
   the input interrupt handler.  At this point, the keystroke is
   represented as a struct input_event, while the desired quit
   character is specified as a lispy event.  The mapping from struct
   input_events to lispy events cannot run in an interrupt handler,
   and the reverse mapping is difficult for anything but ASCII
   keystrokes.

   FOR THESE ELABORATE AND UNSATISFYING REASONS, quit_char must be an
   ASCII character.  */
int quit_char;

/* Current depth in recursive edits.  */
EMACS_INT command_loop_level;

/* If not Qnil, this is a switch-frame event which we decided to put
   off until the end of a key sequence.  This should be read as the
   next command input, after any unread_command_events.

   read_key_sequence uses this to delay switch-frame events until the
   end of the key sequence; Fread_char uses it to put off switch-frame
   events until a non-ASCII event is acceptable as input.  */
Lisp_Object unread_switch_frame;

/* Last size recorded for a current buffer which is not a minibuffer.  */
static ptrdiff_t last_non_minibuf_size;

uintmax_t num_input_events;
ptrdiff_t point_before_last_command_or_undo;
struct buffer *buffer_before_last_command_or_undo;

/* Value of num_nonmacro_input_events as of last auto save.  */

static intmax_t last_auto_save;

/* The value of point when the last command was started. */
static ptrdiff_t last_point_position;

/* The frame in which the last input event occurred, or Qmacro if the
   last event came from a macro.  We use this to determine when to
   generate switch-frame events.  This may be cleared by functions
   like Fselect_frame, to make sure that a switch-frame event is
   generated by the next character.

   FIXME: This is modified by a signal handler so it should be volatile.
   It's exported to Lisp, though, so it can't simply be marked
   'volatile' here.  */
Lisp_Object internal_last_event_frame;

/* `read_key_sequence' stores here the command definition of the
   key sequence that it reads.  */
static Lisp_Object read_key_sequence_cmd;
static Lisp_Object read_key_sequence_remapped;

/* File in which we write all commands we read.  */
static FILE *dribble;

/* True if input is available.  */
bool input_pending;

/* True if more input was available last time we read an event.

   Since redisplay can take a significant amount of time and is not
   indispensable to perform the user's commands, when input arrives
   "too fast", Emacs skips redisplay.  More specifically, if the next
   command has already been input when we finish the previous command,
   we skip the intermediate redisplay.

   This is useful to try and make sure Emacs keeps up with fast input
   rates, such as auto-repeating keys.  But in some cases, this proves
   too conservative: we may end up disabling redisplay for the whole
   duration of a key repetition, even though we could afford to
   redisplay every once in a while.

   So we "sample" the input_pending flag before running a command and
   use *that* value after running the command to decide whether to
   skip redisplay or not.  This way, we only skip redisplay if we
   really can't keep up with the repeat rate.

   This only makes a difference if the next input arrives while running the
   command, which is very unlikely if the command is executed quickly.
   IOW this tends to avoid skipping redisplay after a long running command
   (which is a case where skipping redisplay is not very useful since the
   redisplay time is small compared to the time it took to run the command).

   A typical use case is when scrolling.  Scrolling time can be split into:
   - Time to do jit-lock on the newly displayed portion of buffer.
   - Time to run the actual scroll command.
   - Time to perform the redisplay.
   Jit-lock can happen either during the command or during the redisplay.
   In the most painful cases, the jit-lock time is the one that dominates.
   Also jit-lock can be tweaked (via jit-lock-defer) to delay its job, at the
   cost of temporary inaccuracy in display and scrolling.
   So without input_was_pending, what typically happens is the following:
   - when the command starts, there's no pending input (yet).
   - the scroll command triggers jit-lock.
   - during the long jit-lock time the next input arrives.
   - at the end of the command, we check input_pending and hence decide to
     skip redisplay.
   - we read the next input and start over.
   End result: all the hard work of jit-locking is "wasted" since redisplay
   doesn't actually happens (at least not before the input rate slows down).
   With input_was_pending redisplay is still skipped if Emacs can't keep up
   with the input rate, but if it can keep up just enough that there's no
   input_pending when we begin the command, then redisplay is not skipped
   which results in better feedback to the user.  */
bool input_was_pending;

/* Circular buffer for pre-read keyboard input.  */

union buffered_input_event kbd_buffer[KBD_BUFFER_SIZE];

/* Pointer to next available character in kbd_buffer.
   If kbd_fetch_ptr == kbd_store_ptr, the buffer is empty.  */
union buffered_input_event *kbd_fetch_ptr;

/* Pointer to next place to store character in kbd_buffer.  */
union buffered_input_event *kbd_store_ptr;

/* The above pair of variables forms a "queue empty" flag.  When we
   enqueue a non-hook event, we increment kbd_store_ptr.  When we
   dequeue a non-hook event, we increment kbd_fetch_ptr.  We say that
   there is input available if the two pointers are not equal.

   Why not just have a flag set and cleared by the enqueuing and
   dequeuing functions?  The code is a bit simpler this way.  */

static void recursive_edit_unwind (Lisp_Object buffer);

static void echo_now (void);
static ptrdiff_t echo_length (void);

static void safe_run_hooks_maybe_narrowed (Lisp_Object, struct window *);

/* Incremented whenever a timer is run.  */
unsigned timers_run;

/* Address (if not 0) of struct timespec to zero out if a SIGIO interrupt
   happens.  */
struct timespec *input_available_clear_time;

/* True means use SIGIO interrupts; false means use CBREAK mode.
   Default is true if INTERRUPT_INPUT is defined.  */
bool interrupt_input;

/* Nonzero while interrupts are temporarily deferred during redisplay.  */
bool interrupts_deferred;

/* The time when Emacs started being idle.  */

static struct timespec timer_idleness_start_time;

/* After Emacs stops being idle, this saves the last value
   of timer_idleness_start_time from when it was idle.  */

static struct timespec timer_last_idleness_start_time;

/* Predefined strings for core device names.  */

static Lisp_Object virtual_core_pointer_name;
static Lisp_Object virtual_core_keyboard_name;

/* If not nil, ID of the last TOUCHSCREEN_END_EVENT to land on the
   menu bar.  */
static Lisp_Object menu_bar_touch_id;


/* Global variable declarations.  */

/* Flags for readable_events.  */
#define READABLE_EVENTS_DO_TIMERS_NOW		(1 << 0)
#define READABLE_EVENTS_FILTER_EVENTS		(1 << 1)
#define READABLE_EVENTS_IGNORE_SQUEEZABLES	(1 << 2)

/* Function for init_keyboard to call with no args (if nonzero).  */
static void (*keyboard_init_hook) (void);

static bool get_input_pending (int);
static bool readable_events (int);
static Lisp_Object read_char_x_menu_prompt (Lisp_Object,
                                            Lisp_Object, bool *);
static Lisp_Object read_char_minibuf_menu_prompt (int, Lisp_Object);
static Lisp_Object make_lispy_event (struct input_event *);
static Lisp_Object make_lispy_movement (struct frame *, Lisp_Object,
                                        enum scroll_bar_part,
                                        Lisp_Object, Lisp_Object,
					Time);
static Lisp_Object make_lispy_switch_frame (Lisp_Object);
static bool help_char_p (Lisp_Object);
static Lisp_Object apply_modifiers (int, Lisp_Object);
static void restore_kboard_configuration (int);
static void handle_interrupt (bool);
static AVOID quit_throw_to_read_char (bool);
static void timer_start_idle (void);
static void timer_stop_idle (void);
static void timer_resume_idle (void);
static void deliver_user_signal (int);
static char *find_user_signal_name (int);
static void store_user_signal_events (void);
static bool is_ignored_event (union buffered_input_event *);

/* Advance or retreat a buffered input event pointer.  */

static union buffered_input_event *
next_kbd_event (union buffered_input_event *ptr)
{
  return ptr == kbd_buffer + KBD_BUFFER_SIZE - 1 ? kbd_buffer : ptr + 1;
}

/* Like EVENT_START, but assume EVENT is an event.
   This pacifies gcc -Wnull-dereference, which might otherwise
   complain about earlier checks that EVENT is indeed an event.  */
static Lisp_Object
xevent_start (Lisp_Object event)
{
  return XCAR (XCDR (event));
}

/* These setters are used only in this file, so they can be private.  */
static void
kset_echo_string (struct kboard *kb, Lisp_Object val)
{
  kb->echo_string_ = val;
}
static void
kset_echo_prompt (struct kboard *kb, Lisp_Object val)
{
  kb->echo_prompt_ = val;
}
static void
kset_kbd_queue (struct kboard *kb, Lisp_Object val)
{
  kb->kbd_queue_ = val;
}
static void
kset_keyboard_translate_table (struct kboard *kb, Lisp_Object val)
{
  kb->Vkeyboard_translate_table_ = val;
}
static void
kset_last_prefix_arg (struct kboard *kb, Lisp_Object val)
{
  kb->Vlast_prefix_arg_ = val;
}
static void
kset_last_repeatable_command (struct kboard *kb, Lisp_Object val)
{
  kb->Vlast_repeatable_command_ = val;
}
static void
kset_local_function_key_map (struct kboard *kb, Lisp_Object val)
{
  kb->Vlocal_function_key_map_ = val;
}
static void
kset_overriding_terminal_local_map (struct kboard *kb, Lisp_Object val)
{
  kb->Voverriding_terminal_local_map_ = val;
}
static void
kset_real_last_command (struct kboard *kb, Lisp_Object val)
{
  kb->Vreal_last_command_ = val;
}
static void
kset_system_key_syms (struct kboard *kb, Lisp_Object val)
{
  kb->system_key_syms_ = val;
}


static bool
echo_keystrokes_p (void)
{
  return (FLOATP (Vecho_keystrokes) ? XFLOAT_DATA (Vecho_keystrokes) > 0.0
	  : FIXNUMP (Vecho_keystrokes) ? XFIXNUM (Vecho_keystrokes) > 0
          : false);
}

/* Add C to the echo string, without echoing it immediately.  C can be
   a character, which is pretty-printed, or a symbol, whose name is
   printed.  */

static void
echo_add_key (Lisp_Object c)
{
  char initbuf[KEY_DESCRIPTION_SIZE + 100];
  ptrdiff_t size = sizeof initbuf;
  char *buffer = initbuf;
  char *ptr = buffer;
  Lisp_Object echo_string = KVAR (current_kboard, echo_string);
  USE_SAFE_ALLOCA;

  if (STRINGP (echo_string) && SCHARS (echo_string) > 0)
    /* Add a space at the end as a separator between keys.  */
    ptr++[0] = ' ';

  /* If someone has passed us a composite event, use its head symbol.  */
  c = EVENT_HEAD (c);

  if (FIXNUMP (c))
    ptr = push_key_description (XFIXNUM (c), ptr);
  else if (SYMBOLP (c))
    {
      Lisp_Object name = SYMBOL_NAME (c);
      ptrdiff_t nbytes = SBYTES (name);

      if (size - (ptr - buffer) < nbytes)
	{
	  ptrdiff_t offset = ptr - buffer;
	  size = max (2 * size, size + nbytes);
	  buffer = SAFE_ALLOCA (size);
	  ptr = buffer + offset;
	}

      ptr += copy_text (SDATA (name), (unsigned char *) ptr, nbytes,
			STRING_MULTIBYTE (name), 1);
    }

  Lisp_Object new_string = make_string (buffer, ptr - buffer);
  if ((NILP (echo_string) || SCHARS (echo_string) == 0)
      && help_char_p (c))
    {
      AUTO_STRING (str, " (Type ? for further options, C-q for quick help)");
      AUTO_LIST2 (props, Qface, Qhelp_key_binding);
      Fadd_text_properties (make_fixnum (7), make_fixnum (8), props, str);
      Fadd_text_properties (make_fixnum (30), make_fixnum (33), props, str);
      new_string = concat2 (new_string, str);
    }

  kset_echo_string (current_kboard,
		    concat2 (echo_string, new_string));
  SAFE_FREE ();
}

/* Temporarily add a dash to the end of the echo string if it's not
   empty, so that it serves as a mini-prompt for the very next
   character.  */

static void
echo_dash (void)
{
  /* Do nothing if not echoing at all.  */
  if (NILP (KVAR (current_kboard, echo_string)))
    return;

  if (!current_kboard->immediate_echo
      && SCHARS (KVAR (current_kboard, echo_string)) == 0)
    return;

  /* Do nothing if we just printed a prompt.  */
  if (STRINGP (KVAR (current_kboard, echo_prompt))
      && (SCHARS (KVAR (current_kboard, echo_prompt))
	  == SCHARS (KVAR (current_kboard, echo_string))))
    return;

  /* Do nothing if we have already put a dash at the end.  */
  if (SCHARS (KVAR (current_kboard, echo_string)) > 1)
    {
      Lisp_Object last_char, prev_char, idx;

      idx = make_fixnum (SCHARS (KVAR (current_kboard, echo_string)) - 2);
      prev_char = Faref (KVAR (current_kboard, echo_string), idx);

      idx = make_fixnum (SCHARS (KVAR (current_kboard, echo_string)) - 1);
      last_char = Faref (KVAR (current_kboard, echo_string), idx);

      if ((XFIXNUM (last_char) == '-' && XFIXNUM (prev_char) != ' ')
	  /* Or a keystroke help message.  */
	  || (echo_keystrokes_help
	      && XFIXNUM (last_char) == ')' && XFIXNUM (prev_char) == 'p'))
	return;
    }

  /* Put a dash at the end of the buffer temporarily,
     but make it go away when the next character is added.  */
  AUTO_STRING (dash, "-");
  kset_echo_string (current_kboard,
		    concat2 (KVAR (current_kboard, echo_string), dash));

  if (echo_keystrokes_help)
    kset_echo_string (current_kboard,
		      calln (Qhelp__append_keystrokes_help,
			     KVAR (current_kboard, echo_string)));

  echo_now ();
}

static void
echo_update (void)
{
  if (current_kboard->immediate_echo)
    {
      ptrdiff_t i;
      Lisp_Object prompt = KVAR (current_kboard, echo_prompt);
      Lisp_Object prefix = call0 (Qinternal_echo_keystrokes_prefix);
      kset_echo_string (current_kboard,
			NILP (prompt) ? prefix
			: NILP (prefix) ? prompt
			: concat2 (prompt, prefix));

      for (i = 0; i < this_command_key_count; i++)
	{
	  Lisp_Object c;

	  c = AREF (this_command_keys, i);
	  if (! (EVENT_HAS_PARAMETERS (c)
		 && EQ (EVENT_HEAD_KIND (EVENT_HEAD (c)), Qmouse_movement)))
	    echo_add_key (c);
	}

      echo_now ();
    }
}

/* Display the current echo string, and begin echoing if not already
   doing so.  */

static void
echo_now (void)
{
  if (!current_kboard->immediate_echo
      /* This test breaks calls that use `echo_now' to display the echo_prompt.
         && echo_keystrokes_p () */)
    {
      current_kboard->immediate_echo = true;
      echo_update ();
      /* Put a dash at the end to invite the user to type more.  */
      echo_dash ();
    }

  echoing = true;
  /* FIXME: Use call (Qmessage) so it can be advised (e.g. emacspeak).  */
  message3_nolog (KVAR (current_kboard, echo_string));
  echoing = false;

  /* Record in what buffer we echoed, and from which kboard.  */
  echo_message_buffer = echo_area_buffer[0];
  echo_kboard = current_kboard;

  if (waiting_for_input && !NILP (Vquit_flag))
    quit_throw_to_read_char (0);
}

/* Turn off echoing, for the start of a new command.  */

void
cancel_echoing (void)
{
  current_kboard->immediate_echo = false;
  kset_echo_prompt (current_kboard, Qnil);
  kset_echo_string (current_kboard, Qnil);
  ok_to_echo_at_next_pause = NULL;
  echo_kboard = NULL;
  echo_message_buffer = Qnil;
}

/* Return the length of the current echo string.  */

static ptrdiff_t
echo_length (void)
{
  return (STRINGP (KVAR (current_kboard, echo_string))
	  ? SCHARS (KVAR (current_kboard, echo_string))
	  : 0);
}

/* Truncate the current echo message to its first LEN chars.
   This and echo_char get used by read_key_sequence when the user
   switches frames while entering a key sequence.  */

static void
echo_truncate (ptrdiff_t nchars)
{
  Lisp_Object es = KVAR (current_kboard, echo_string);
  if (STRINGP (es) && SCHARS (es) > nchars)
    kset_echo_string (current_kboard,
		      Fsubstring (KVAR (current_kboard, echo_string),
				  make_fixnum (0), make_fixnum (nchars)));
  truncate_echo_area (nchars);
}


/* Functions for manipulating this_command_keys.  */
static void
add_command_key (Lisp_Object key)
{
  /* FIX-guilemacs: Defend against this_command_keys becoming corrupted
     (e.g., to a string or invalid object).  */
  if (!VECTORP (this_command_keys))
    {
      this_command_keys = make_nil_elisp_vector (40);
      this_command_key_count = 0;
    }

  if (this_command_key_count >= ASIZE (this_command_keys))
    this_command_keys = larger_vector (this_command_keys, 1, -1);

  ASET (this_command_keys, this_command_key_count, key);
  ++this_command_key_count;
}


Lisp_Object
recursive_edit_1 (void)
{
  dynwind_begin ();
  Lisp_Object val;

  if (command_loop_level > 0)
    {
      specbind_guile (Qstandard_output, Qt);
      specbind_guile (Qstandard_input, Qt);
      specbind_guile (Qsymbols_with_pos_enabled, Qnil);
      specbind_guile (Qprint_symbols_bare, Qnil);
    }

#ifdef HAVE_WINDOW_SYSTEM
  /* The command loop has started an hourglass timer, so we have to
     cancel it here, otherwise it will fire because the recursive edit
     can take some time.  Do not check for display_hourglass_p here,
     because it could already be nil.  */
    cancel_hourglass ();
#endif

  /* This function may have been called from a debugger called from
     within redisplay, for instance by Edebugging a function called
     from fontification-functions.  We want to allow redisplay in
     the debugging session.

     The recursive edit is left with a `(throw exit ...)'.  The `exit'
     tag is not caught anywhere in redisplay, i.e. when we leave the
     recursive edit, the original redisplay leading to the recursive
     edit will be unwound.  The outcome should therefore be safe.  */
  specbind_guile (Qinhibit_redisplay, Qnil);
  redisplaying_p = 0;

  /* This variable stores buffers that have changed so that an undo
     boundary can be added. specbind this so that changes in the
     recursive edit will not result in undo boundaries in buffers
     changed before we entered there recursive edit.
     See Bug #23632.
  */
  specbind_guile (Qundo_auto__undoably_changed_buffers, Qnil);

  /* M7h: the editor command loop body lives in Scheme as
     (emacs command-loop)/command-loop-main.  */
  static SCM cmdloop_proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (cmdloop_proc))
    cmdloop_proc = scm_c_public_ref ("emacs command-loop",
                                     "command-loop-main");
  val = SCM_CALL_0 (cmdloop_proc);
  if (EQ (val, Qt))
    quit ();
  /* Handle throw from read_minibuf when using minibuffer
     while it's active but we're in another window.  */
  if (STRINGP (val))
    xsignal1 (Qerror, val);

  if (FUNCTIONP (val))
    call0 (val);

  dynwind_end ();
  return Qnil;
}

/* When an auto-save happens, record the "time", and don't do again soon.  */

void
record_auto_save (void)
{
  last_auto_save = num_nonmacro_input_events;
}

/* Make an auto save happen as soon as possible at command level.  */

#ifdef SIGDANGER
void
force_auto_save_soon (void)
{
  last_auto_save = - auto_save_interval - 1;
}
#endif

DEFUN ("recursive-edit", Frecursive_edit, Srecursive_edit, 0, 0, "",
       doc: /* Invoke the editor command loop recursively.
To get out of the recursive edit, a command can throw to `exit' -- for
instance (throw \\='exit nil).

The following values (last argument to `throw') can be used when
throwing to \\='exit:

- t causes `recursive-edit' to quit, so that control returns to the
  command loop one level up.

- A string causes `recursive-edit' to signal an error, printing that
  string as the error message.

- A function causes `recursive-edit' to call that function with no
  arguments, and then return normally.

- Any other value causes `recursive-edit' to return normally to the
  function that called it.

This function is called by the editor initialization to begin editing.  */)
  (void)
{
  dynwind_begin ();
  Lisp_Object buffer;

  /* If we enter while input is blocked, don't lock up here.
     This may happen through the debugger during redisplay.  */
  if (input_blocked_p ()) {
    dynwind_end ();
    return Qnil;
  }

  if (command_loop_level >= 0
      && current_buffer != XBUFFER (XWINDOW (selected_window)->contents))
    buffer = Fcurrent_buffer ();
  else
    buffer = Qnil;

  /* Don't do anything interesting between the increment and the
     record_unwind_protect!  Otherwise, we could get distracted and
     never decrement the counter again.  */
  command_loop_level++;
  update_mode_lines = 17;
  record_unwind_protect (recursive_edit_unwind, buffer);

  /* If we leave recursive_edit_1 below with a `throw' for instance,
     like it is done in the splash screen display, we have to
     make sure that we restore single_kboard as command_loop_1
     would have done if it were left normally.  */
  if (command_loop_level > 0)
    temporarily_switch_to_single_kboard (SELECTED_FRAME ());

  recursive_edit_1 ();
  dynwind_end ();
  return Qnil;
}

void
recursive_edit_unwind (Lisp_Object buffer)
{
  if (BUFFERP (buffer))
    Fset_buffer (buffer);

  command_loop_level--;
  update_mode_lines = 18;
}



/* M2 — Foreign-object wrapping for KBOARD*.

   The smob holds a bare KBOARD* in SMOB_DATA.  Ownership stays with
   all_kboards / delete_kboard, so the smob has no finalizer: dropping
   a Scheme handle does not free the underlying struct.  Multiple
   handles can wrap the same pointer — use kboard-eq when identity
   matters.

   See mod/emacs/kboard.scm and docs/keyboard.org §M2.  */

static SCM
make_kboard_smob (KBOARD *kb)
{
  SCM smob;
  SCM_NEWSMOB (smob, kboard_tag, kb);
  return smob;
}


/* M9 — ie-smob: foreign-object wrapping for struct input_event *.

   The smob holds a bare struct input_event * in SMOB_DATA.  Ownership
   stays with kbd_buffer / stack temporaries; the smob has no finalizer.

   Retention guard: make_lispy_event sets SMOB_DATA to NULL after
   SCM_CALL_1 returns; accessors abort on NULL.  The free hook is a
   no-op since the smob owns no heap memory.

   See docs/m9-plan.org §imp-1.1.  */

static SCM
ie_mark (SCM smob)
{
  struct input_event *ev = (struct input_event *) SCM_SMOB_DATA (smob);
  if (ev == NULL)
    return SCM_BOOL_F;
  scm_gc_mark (ev->x);
  scm_gc_mark (ev->y);
  scm_gc_mark (ev->frame_or_window);
  scm_gc_mark (ev->arg);
  return ev->device;
}

static size_t
ie_free (SCM smob)
{
  /* The smob owns no heap memory — SMOB_DATA points into the C event
     queue (or a stack temporary).  Retention violations are caught by
     the NULL-guard in accessors, not here.  */
  return 0;
}

static int
ie_print (SCM smob, SCM port, scm_print_state *pstate)
{
  struct input_event *ev = (struct input_event *) SCM_SMOB_DATA (smob);
  if (ev == NULL)
    {
      scm_puts ("#<input-event (invalidated)>", port);
      return 1;
    }
  scm_puts ("#<input-event ", port);
  scm_uintprint ((scm_t_bits) ev->kind, 10, port);
  scm_putc ('>', port);
  return 1;
}

static SCM
ie_wrap (struct input_event *event)
{
  SCM smob;
  SCM_NEWSMOB (smob, ie_tag, event);
  return smob;
}

static struct input_event *
ie_unwrap (SCM smob)
{
  struct input_event *ev = (struct input_event *) SCM_SMOB_DATA (smob);
  if (ev == NULL)
    emacs_abort ();            /* SMOB used after make_lispy_event returned */
  return ev;
}

#define XIE(scm)    ((struct input_event *) SCM_SMOB_DATA (scm))
#define IEP(scm)    (SCM_SMOB_PREDICATE (ie_tag, (scm)))
#define CHECK_IE(x) \
  do { if (!IEP (x)) wrong_type_argument (Qiep, x); \
       if (!SCM_SMOB_DATA (x)) emacs_abort (); } while (0)

DEFUN ("--ie-kind", Fie_kind, Sie_kind, 1, 1, 0,
       doc: /* Return the event_kind integer of input-event handle IE.

This is the first field-accessor for struct input_event; every
ported make-lispy-event kind-procedure dispatches on this value.
The SMOB must still be live — calling this after the SMOB was
invalidated will abort.  */)
  (Lisp_Object ie)
{
  CHECK_IE (ie);
  return make_fixnum (XIE (ie)->kind);
}

DEFUN ("--ie-code", Fie_code, Sie_code, 1, 1, 0,
       doc: /* Return the code field of input-event handle IE.

For keystroke events this is the character or keysym code; for
mouse events it is the button number.  Unsigned int → fixnum.  */)
  (Lisp_Object ie)
{
  CHECK_IE (ie);
  return make_fixnum (XIE (ie)->code);
}

DEFUN ("--ie-modifiers", Fie_modifiers, Sie_modifiers, 1, 1, 0,
       doc: /* Return the modifiers bitmask of input-event handle IE.

Unsigned int → fixnum.  Use --set-ie-modifiers to mutate (needed
by MOUSE_CLICK double-click promotion).  */)
  (Lisp_Object ie)
{
  CHECK_IE (ie);
  return make_fixnum (XIE (ie)->modifiers);
}

DEFUN ("--ie-part", Fie_part, Sie_part, 1, 1, 0,
       doc: /* Return the scroll-bar-part enum of input-event handle IE.

Used in scroll-bar click events.  Unsigned bitfield → fixnum.  */)
  (Lisp_Object ie)
{
  CHECK_IE (ie);
  return make_fixnum (XIE (ie)->part);
}

DEFUN ("--ie-x", Fie_x, Sie_x, 1, 1, 0,
       doc: /* Return the x field of input-event handle IE.

Lisp_Object — mouse position (pixel or character coords) or HELP_EVENT window.  */)
  (Lisp_Object ie)
{
  CHECK_IE (ie);
  return XIE (ie)->x;
}

DEFUN ("--ie-y", Fie_y, Sie_y, 1, 1, 0,
       doc: /* Return the y field of input-event handle IE.

Lisp_Object — mouse position (pixel or character coords) or HELP_EVENT help form.  */)
  (Lisp_Object ie)
{
  CHECK_IE (ie);
  return XIE (ie)->y;
}

DEFUN ("--ie-frame-or-window", Fie_frame_or_window, Sie_frame_or_window, 1, 1, 0,
       doc: /* Return the frame_or_window field of input-event handle IE.

Lisp_Object — the frame or window associated with this event.  */)
  (Lisp_Object ie)
{
  CHECK_IE (ie);
  return XIE (ie)->frame_or_window;
}

DEFUN ("--ie-arg", Fie_arg, Sie_arg, 1, 1, 0,
       doc: /* Return the arg field of input-event handle IE.

Lisp_Object — auxiliary event data (DBUS arg, XWIDGET arg, etc.).  */)
  (Lisp_Object ie)
{
  CHECK_IE (ie);
  return XIE (ie)->arg;
}

DEFUN ("--ie-device", Fie_device, Sie_device, 1, 1, 0,
       doc: /* Return the device field of input-event handle IE.

Lisp_Object — device name (string) or Qt.  */)
  (Lisp_Object ie)
{
  CHECK_IE (ie);
  return XIE (ie)->device;
}

DEFUN ("--ie-timestamp", Fie_timestamp, Sie_timestamp, 1, 1, 0,
       doc: /* Return the timestamp field of input-event handle IE.

Time (int64, milliseconds) → integer.  Uses INT_TO_INTEGER so
values beyond fixnum range still round-trip correctly.  */)
  (Lisp_Object ie)
{
  CHECK_IE (ie);
  return INT_TO_INTEGER (XIE (ie)->timestamp);
}

/* Mutators — imp-1.3.  */

DEFUN ("--set-ie-modifiers", Fset_ie_modifiers, Sset_ie_modifiers, 2, 2, 0,
       doc: /* Set the modifiers bitmask of input-event handle IE to VAL.

Plain write; the caller is responsible for computing the desired
value (e.g. via `logior' in Scheme).  Returns VAL.  */)
  (Lisp_Object ie, Lisp_Object val)
{
  CHECK_IE (ie);
  CHECK_FIXNAT (val);
  XIE (ie)->modifiers = XFIXNUM (val);
  return val;
}

DEFUN ("--ie-clear", Fie_clear, Sie_clear, 1, 1, 0,
       doc: /* Clear input-event handle IE by setting kind = NO_EVENT.

Mirrors clear_event() (keyboard.c:4529): sets kind to NO_EVENT
only — does not nil the Lisp_Object fields.  Returns IE.  */)
  (Lisp_Object ie)
{
  CHECK_IE (ie);
  XIE (ie)->kind = NO_EVENT;
  return ie;
}

DEFUN ("--ie-kind-from-name", Fie_kind_from_name, Sie_kind_from_name,
       1, 1, 0,
       doc: /* Return the event_kind integer for event symbol NAME, or -1.

Used by (emacs lispy-event) to register per-kind dispatch entries
without hard-coding enum values in Scheme.  Each event symbol
(e.g. `dbus-event') maps to its enum value (e.g. DBUS_EVENT).  */)
  (Lisp_Object name)
{
#ifdef HAVE_DBUS
  if (EQ (name, Qdbus_event)) return make_fixnum (DBUS_EVENT);
#endif
#ifdef THREADS_ENABLED
  if (EQ (name, Qthread_event)) return make_fixnum (THREAD_EVENT);
#endif
#ifdef HAVE_XWIDGETS
  if (EQ (name, Qxwidget_event)) return make_fixnum (XWIDGET_EVENT);
  if (EQ (name, Qxwidget_display_event)) return make_fixnum (XWIDGET_DISPLAY_EVENT);
#endif
#ifdef USE_FILE_NOTIFY
  if (EQ (name, Qfile_notify)) return make_fixnum (FILE_NOTIFY_EVENT);
#endif

  /* Trivial-frame group  */
  if (EQ (name, Qno_event)) return make_fixnum (NO_EVENT);
#ifdef HAVE_WINDOW_SYSTEM
  if (EQ (name, Qdelete_frame)) return make_fixnum (DELETE_WINDOW_EVENT);
  if (EQ (name, Qiconify_frame)) return make_fixnum (ICONIFY_EVENT);
  if (EQ (name, Qmake_frame_visible)) return make_fixnum (DEICONIFY_EVENT);
  if (EQ (name, Qmove_frame)) return make_fixnum (MOVE_FRAME_EVENT);
#endif

  /* Simple-list group (imp-3.3).  */
  if (EQ (name, Qselect_window)) return make_fixnum (SELECT_WINDOW_EVENT);
  if (EQ (name, Qsave_session)) return make_fixnum (SAVE_SESSION_EVENT);
  if (EQ (name, Qconfig_changed_event)) return make_fixnum (CONFIG_CHANGED_EVENT);
  if (EQ (name, Qpreedit_text)) return make_fixnum (PREEDIT_TEXT_EVENT);
#ifdef HAVE_NTGUI
  if (EQ (name, Qend_session)) return make_fixnum (END_SESSION_EVENT);
  if (EQ (name, Qlanguage_change)) return make_fixnum (LANGUAGE_CHANGE_EVENT);
#endif
  if (EQ (name, Quser_signal_event))
    return make_fixnum (USER_SIGNAL_EVENT);

  /* Simple-helper group (imp-4).  */
  if (EQ (name, Qhelp_echo)) return make_fixnum (HELP_EVENT);
  if (EQ (name, Qfocus_in)) return make_fixnum (FOCUS_IN_EVENT);
  if (EQ (name, Qfocus_out)) return make_fixnum (FOCUS_OUT_EVENT);
  if (EQ (name, Qtab_bar)) return make_fixnum (TAB_BAR_EVENT);
  if (EQ (name, Qtool_bar)) return make_fixnum (TOOL_BAR_EVENT);
  if (EQ (name, Qdrag_n_drop)) return make_fixnum (DRAG_N_DROP_EVENT);
#ifdef HAVE_EXT_MENU_BAR
  if (EQ (name, Qmenu_bar)) return make_fixnum (MENU_BAR_EVENT);
#endif
#ifdef USE_TOOLKIT_SCROLL_BARS
  if (EQ (name, Qscroll_bar_click_toolkit))
    return make_fixnum (SCROLL_BAR_CLICK_EVENT);
  if (EQ (name, Qhorizontal_scroll_bar_click_toolkit))
    return make_fixnum (HORIZONTAL_SCROLL_BAR_CLICK_EVENT);
#endif

  /* Keystroke group (imp-5).  */
  if (EQ (name, Qascii_keystroke))
    return make_fixnum (ASCII_KEYSTROKE_EVENT);
  if (EQ (name, Qmultibyte_char_keystroke))
    return make_fixnum (MULTIBYTE_CHAR_KEYSTROKE_EVENT);
  if (EQ (name, Qnon_ascii_keystroke))
    return make_fixnum (NON_ASCII_KEYSTROKE_EVENT);
#ifdef HAVE_NS
  if (EQ (name, Qns_nonkey))
    return make_fixnum (NS_NONKEY_EVENT);
  if (EQ (name, Qns_text_event))
    return make_fixnum (NS_TEXT_EVENT);
#endif
#ifdef HAVE_NTGUI
  if (EQ (name, Qmultimedia_key))
    return make_fixnum (MULTIMEDIA_KEY_EVENT);
#endif

  /* imp-7.2 — wheel events (always compiled in).  */
  if (EQ (name, Qwheel_event))
    return make_fixnum (WHEEL_EVENT);
  if (EQ (name, Qhorizontal_wheel_event))
    return make_fixnum (HORIZ_WHEEL_EVENT);

  /* imp-7.3 — touch/pinch (always compiled in).  */
  if (EQ (name, Qtouch_end))
    return make_fixnum (TOUCH_END_EVENT);
  if (EQ (name, Qpinch))
    return make_fixnum (PINCH_EVENT);

  /* imp-7.4 — touchscreen group (always compiled in).  */
  if (EQ (name, Qtouchscreen_begin))
    return make_fixnum (TOUCHSCREEN_BEGIN_EVENT);
  if (EQ (name, Qtouchscreen_end))
    return make_fixnum (TOUCHSCREEN_END_EVENT);
  if (EQ (name, Qtouchscreen_update))
    return make_fixnum (TOUCHSCREEN_UPDATE_EVENT);

  /* imp-7.5 — mouse click + non-toolkit scroll-bar click.  */
  if (EQ (name, Qmouse_click_event))
    return make_fixnum (MOUSE_CLICK_EVENT);
#ifndef USE_TOOLKIT_SCROLL_BARS
  if (EQ (name, Qscroll_bar_click_event))
    return make_fixnum (SCROLL_BAR_CLICK_EVENT);
  if (EQ (name, Qhorizontal_scroll_bar_click_event))
    return make_fixnum (HORIZONTAL_SCROLL_BAR_CLICK_EVENT);
#endif

  /* More entries added as additional kind groups are ported.  */
  return make_fixnum (-1);
}

DEFUN ("--user-signal-name", Fuser_signal_name, Suser_signal_name,
       1, 1, 0,
       doc: /* Return the interned symbol for user-signal code C.

Wraps find_user_signal_name + intern for the Scheme port of
USER_SIGNAL_EVENT.  Aborts if C is not a registered
user-signal code — matches the original C assertion at
make_lispy_event's USER_SIGNAL_EVENT case.  */)
  (Lisp_Object code)
{
  char *name = find_user_signal_name (XFIXNUM (code));
  if (!name)
    emacs_abort ();
  return intern (name);
}

#ifdef HAVE_NS
DEFUN ("--ns-text-event-symbol", Fns_text_event_symbol,
       Sns_text_event_symbol, 1, 1, 0,
       doc: /* Return the interned symbol for NS text event code C.

Wraps KEY_NS_PUT_WORKING_TEXT / KEY_NS_UNPUT_WORKING_TEXT so the
Scheme handler doesn't need the magic-number constants.  Returns
`ns-put-working-text' or `ns-unput-working-text'.  */)
  (Lisp_Object code)
{
  return intern (XFIXNUM (code) == KEY_NS_PUT_WORKING_TEXT
		 ? "ns-put-working-text"
		 : "ns-unput-working-text");
}
#endif

DEFUN ("--uppercasep", Fuppercasep, Suppercasep, 1, 1, 0,
       doc: /* Return t if character C is upper case.

Uses the current buffer's case tables — thin wrapper around the
uppercasep() inline (src/buffer.h:1563) so Scheme keystroke ports
avoid chaining upcase/downcase DEFUN calls.  */)
  (Lisp_Object c)
{
  CHECK_FIXNUM (c);
  return uppercasep (XFIXNUM (c)) ? Qt : Qnil;
}

DEFUN ("--lowercasep", Flowercasep, Slowercasep, 1, 1, 0,
       doc: /* Return t if character C is lower case.

Uses the current buffer's case tables — thin wrapper around the
lowercasep() inline (src/buffer.h:1571) so Scheme keystroke ports
avoid chaining upcase/downcase DEFUN calls.  */)
  (Lisp_Object c)
{
  CHECK_FIXNUM (c);
  return lowercasep (XFIXNUM (c)) ? Qt : Qnil;
}

#define XKBOARD(scm)    ((KBOARD *) SCM_SMOB_DATA (scm))
#define KBOARDP(scm)    (SCM_SMOB_PREDICATE (kboard_tag, (scm)))
#define CHECK_KBOARD(x) \
  do { if (!KBOARDP (x)) wrong_type_argument (Qkboardp, x); } while (0)

DEFUN ("kboardp", Fkboardp, Skboardp, 1, 1, 0,
       doc: /* Return t if OBJECT is a kboard handle.  */)
  (Lisp_Object object)
{
  return KBOARDP (object) ? Qt : Qnil;
}

DEFUN ("kboard-eq", Fkboard_eq, Skboard_eq, 2, 2, 0,
       doc: /* Return t if A and B wrap the same underlying KBOARD.  */)
  (Lisp_Object a, Lisp_Object b)
{
  CHECK_KBOARD (a);
  CHECK_KBOARD (b);
  return (XKBOARD (a) == XKBOARD (b)) ? Qt : Qnil;
}

DEFUN ("current-kboard", Fcurrent_kboard, Scurrent_kboard, 0, 0, 0,
       doc: /* Return the active KBOARD as a foreign-object handle.  */)
  (void)
{
  return make_kboard_smob (current_kboard);
}

DEFUN ("set-current-kboard", Fset_current_kboard, Sset_current_kboard, 1, 1, 0,
       doc: /* Set the active KBOARD to the one wrapped by KB.  */)
  (Lisp_Object kb)
{
  CHECK_KBOARD (kb);
  current_kboard = XKBOARD (kb);
  return kb;
}

/* Macro generating one getter/setter DEFUN pair per Lisp_Object field
   of struct kboard.  The struct member name is FIELD_; the elisp
   symbol uses LNAME (a string) so we get hyphenated names.  */

#define KBOARD_LISP_FIELD(LNAME, FIELD)                                  \
  DEFUN ("kboard-" LNAME, Fkboard_##FIELD, Skboard_##FIELD, 1, 1, 0,     \
         doc: /* Return KB's FIELD slot.  */)                            \
    (Lisp_Object kb)                                                     \
  {                                                                      \
    CHECK_KBOARD (kb);                                                   \
    return XKBOARD (kb)->FIELD##_;                                       \
  }                                                                      \
  DEFUN ("set-kboard-" LNAME, Fset_kboard_##FIELD, Sset_kboard_##FIELD,  \
         2, 2, 0,                                                        \
         doc: /* Set KB's FIELD slot to VAL.  */)                        \
    (Lisp_Object kb, Lisp_Object val)                                    \
  {                                                                      \
    CHECK_KBOARD (kb);                                                   \
    XKBOARD (kb)->FIELD##_ = val;                                        \
    return val;                                                          \
  }

KBOARD_LISP_FIELD ("overriding-terminal-local-map", Voverriding_terminal_local_map)
KBOARD_LISP_FIELD ("last-command",                  Vlast_command)
KBOARD_LISP_FIELD ("real-last-command",             Vreal_last_command)
KBOARD_LISP_FIELD ("keyboard-translate-table",      Vkeyboard_translate_table)
KBOARD_LISP_FIELD ("last-repeatable-command",       Vlast_repeatable_command)
KBOARD_LISP_FIELD ("prefix-arg",                    Vprefix_arg)
KBOARD_LISP_FIELD ("last-prefix-arg",               Vlast_prefix_arg)
KBOARD_LISP_FIELD ("kbd-queue",                     kbd_queue)
KBOARD_LISP_FIELD ("defining-kbd-macro",            defining_kbd_macro)
KBOARD_LISP_FIELD ("last-kbd-macro",                Vlast_kbd_macro)
KBOARD_LISP_FIELD ("system-key-alist",              Vsystem_key_alist)
KBOARD_LISP_FIELD ("system-key-syms",               system_key_syms)
KBOARD_LISP_FIELD ("window-system",                 Vwindow_system)
KBOARD_LISP_FIELD ("local-function-key-map",        Vlocal_function_key_map)
KBOARD_LISP_FIELD ("input-decode-map",              Vinput_decode_map)
KBOARD_LISP_FIELD ("default-minibuffer-frame",      Vdefault_minibuffer_frame)
KBOARD_LISP_FIELD ("echo-string",                   echo_string)
KBOARD_LISP_FIELD ("echo-prompt",                   echo_prompt)

#undef KBOARD_LISP_FIELD


/* If we're in single_kboard state for kboard KBOARD,
   get out of it.  */

void
not_single_kboard_state (KBOARD *kboard)
{
  if (kboard == current_kboard)
    single_kboard = false;
}

/* Maintain a stack of kboards, so other parts of Emacs
   can switch temporarily to the kboard of a given frame
   and then revert to the previous status.  */

struct kboard_stack
{
  KBOARD *kboard;
  struct kboard_stack *next;
};

static struct kboard_stack *kboard_stack;

void
push_kboard (struct kboard *k)
{
  struct kboard_stack *p = xmalloc (sizeof *p);

  p->next = kboard_stack;
  p->kboard = current_kboard;
  kboard_stack = p;

  current_kboard = k;
}

void
pop_kboard (void)
{
  struct terminal *t;
  struct kboard_stack *p = kboard_stack;
  bool found = false;
  for (t = terminal_list; t; t = t->next_terminal)
    {
      if (t->kboard == p->kboard)
        {
          current_kboard = p->kboard;
          found = true;
          break;
        }
    }
  if (!found)
    {
      /* The terminal we remembered has been deleted.  */
      current_kboard = FRAME_KBOARD (SELECTED_FRAME ());
      single_kboard = false;
    }
  kboard_stack = p->next;
  xfree (p);
}

/* Switch to single_kboard mode, making current_kboard the only KBOARD
  from which further input is accepted.  If F is non-nil, set its
  KBOARD as the current keyboard.

  This function uses record_unwind_protect_int to return to the previous
  state later.

  If Emacs is already in single_kboard mode, and F's keyboard is
  locked, then this function will throw an error.  */

void
temporarily_switch_to_single_kboard (struct frame *f)
{
  bool was_locked = single_kboard;
  if (was_locked)
    {
      if (f != NULL && FRAME_KBOARD (f) != current_kboard)
        /* We can not switch keyboards while in single_kboard mode.
           In rare cases, Lisp code may call `recursive-edit' (or
           `read-minibuffer' or `y-or-n-p') after it switched to a
           locked frame.  For example, this is likely to happen
           when server.el connects to a new terminal while Emacs is in
           single_kboard mode.  It is best to throw an error instead
           of presenting the user with a frozen screen.  */
        error ("Terminal %d is locked, cannot read from it",
               FRAME_TERMINAL (f)->id);
      else
        /* This call is unnecessary, but helps
           `restore_kboard_configuration' discover if somebody changed
           `current_kboard' behind our back.  */
        push_kboard (current_kboard);
    }
  else if (f != NULL)
    current_kboard = FRAME_KBOARD (f);
  single_kboard = true;
  record_unwind_protect_int (restore_kboard_configuration, was_locked);
}

static void
restore_kboard_configuration (int was_locked)
{
  single_kboard = was_locked;
  if (was_locked)
    {
      struct kboard *prev = current_kboard;
      pop_kboard ();
      /* The pop should not change the kboard.  */
      if (single_kboard && current_kboard != prev)
        emacs_abort ();
    }
}


/* M7f — cmd_error ported to (emacs command-loop) cmd-error.  See
   docs/keyboard.org §M7f.  */

/* Take actions on handling an error.  DATA is the data that describes
   the error.

   CONTEXT is a C-string containing ASCII characters only which
   describes the context in which the error happened.  If we need to
   generalize CONTEXT to allow multibyte characters, make it a Lisp
   string.  */

void
cmd_error_internal (Lisp_Object data, const char *context)
{
  /* The immediate context is not interesting for Quits,
     since they are asynchronous.  */
  if (signal_quit_p (data))
    Vsignaling_function = Qnil;

  Vquit_flag = Qnil;
  Vinhibit_quit = Qt;

  /* Use user's specified output function if any.  */
  if (!NILP (Vcommand_error_function))
    call3 (Vcommand_error_function, data,
	   context ? build_string (context) : empty_unibyte_string,
	   Vsignaling_function);

  Vsignaling_function = Qnil;
}

/* `command-error-default-function' (the default value of
   `command-error-function') is provided entirely by Scheme — see
   (emacs command-loop) command-error-default-function.  It is
   registered against its elisp symbol by init-command-loop-
   registrations at prelude/load.scm startup time.  */

/* M7e — primitives exposed to (emacs command-loop) for the outer
   drivers (command_loop_2 / top_level_1 / top_level_2).  See
   docs/keyboard.org §M7e.  */

DEFUN ("--eval-top-level", Fc_eval_top_level, Sc_eval_top_level, 0, 0, 0,
       doc: /* Internal: call Feval (Vtop_level, Qt).  Runs the startup
expression installed at top level — see top_level_2_body in C.  */)
  (void)
{
  return Feval (Vtop_level, Qt);
}

/* M7g — primitives exposed to (emacs command-loop) for the default
   command-error-function port.  See docs/keyboard.org §M7g.  */

DEFUN ("--selected-frame-glyphs-initialized-p",
       Fc_selected_frame_glyphs_initialized_p,
       Sc_selected_frame_glyphs_initialized_p, 0, 0, 0,
       doc: /* Internal: SELECTED_FRAME ()->glyphs_initialized_p as a
predicate.  False before redisplay has run on the selected frame.  */)
  (void)
{
  return SELECTED_FRAME ()->glyphs_initialized_p ? Qt : Qnil;
}

DEFUN ("--selected-frame-initial-p", Fc_selected_frame_initial_p,
       Sc_selected_frame_initial_p, 0, 0, 0,
       doc: /* Internal: FRAME_INITIAL_P (SELECTED_FRAME ()).  True for the
non-displaying bootstrap frame.  */)
  (void)
{
  return FRAME_INITIAL_P (SELECTED_FRAME ()) ? Qt : Qnil;
}

DEFUN ("--daemon-not-yet-running-p", Fc_daemon_not_yet_running_p,
       Sc_daemon_not_yet_running_p, 0, 0, 0,
       doc: /* Internal: t when (IS_DAEMON && !DAEMON_RUNNING) — daemon
mode is configured but the daemon socket isn't accepting yet.  */)
  (void)
{
  return (IS_DAEMON && !DAEMON_RUNNING) ? Qt : Qnil;
}

DEFUN ("--print-error-message", Fc_print_error_message,
       Sc_print_error_message, 4, 4, 0,
       doc: /* Internal: invoke C print_error_message (DATA, STREAM,
CONTEXT, SIGNAL).  DATA is (error-symbol . error-data); STREAM is the
output spec (typically t or `external-debugging-output'); CONTEXT is
a string; SIGNAL is the signaling-function symbol (or nil).  */)
  (Lisp_Object data, Lisp_Object stream, Lisp_Object context,
   Lisp_Object signal)
{
  CHECK_STRING (context);
  print_error_message (data, stream, SSDATA (context), signal);
  return Qnil;
}

DEFUN ("--clear-message-1-0", Fc_clear_message_1_0,
       Sc_clear_message_1_0, 0, 0, 0,
       doc: /* Internal: clear_message (1, 0) — clear the echo area and
the *Messages* tail.  */)
  (void)
{
  clear_message (1, 0);
  return Qnil;
}

DEFUN ("--message-log-maybe-newline", Fc_message_log_maybe_newline,
       Sc_message_log_maybe_newline, 0, 0, 0,
       doc: /* Internal: invoke message_log_maybe_newline.  */)
  (void)
{
  message_log_maybe_newline ();
  return Qnil;
}

DEFUN ("--bitch-at-user", Fc_bitch_at_user, Sc_bitch_at_user, 0, 0, 0,
       doc: /* Internal: invoke bitch_at_user.  */)
  (void)
{
  bitch_at_user ();
  return Qnil;
}

/* M7f — primitives exposed to (emacs command-loop) for the cmd-error
   port.  See docs/keyboard.org §M7f.  */

DEFUN ("--executing-kbd-macro-c-p", Fc_executing_kbd_macro_c_p,
       Sc_executing_kbd_macro_c_p, 0, 0, 0,
       doc: /* Internal: t if the C-side `executing_kbd_macro' shadow
of `Vexecuting_kbd_macro' is non-nil.  Used by cmd-error to detect
in-progress kbd-macro replay.  */)
  (void)
{
  return NILP (executing_kbd_macro) ? Qnil : Qt;
}

DEFUN ("--clear-executing-kbd-macro", Fc_clear_executing_kbd_macro,
       Sc_clear_executing_kbd_macro, 0, 0, 0,
       doc: /* Internal: set both the C-side `executing_kbd_macro' and
the elisp `Vexecuting_kbd_macro' to nil.  Called by cmd-error when
the error is not minibuffer-quit.  */)
  (void)
{
  Vexecuting_kbd_macro = Qnil;
  executing_kbd_macro = Qnil;
  return Qnil;
}

DEFUN ("--executing-kbd-macro-iterations",
       Fc_executing_kbd_macro_iterations,
       Sc_executing_kbd_macro_iterations, 0, 0, 0,
       doc: /* Internal: return the C global `executing_kbd_macro_iterations'
as a fixnum.  */)
  (void)
{
  return make_fixnum (executing_kbd_macro_iterations);
}

DEFUN ("--display-hourglass-p", Fc_display_hourglass_p,
       Sc_display_hourglass_p, 0, 0, 0,
       doc: /* Internal: t if the C-side `display_hourglass_p' bit is
set (window-system builds only).  No-op false on TTY builds.  */)
  (void)
{
#ifdef HAVE_WINDOW_SYSTEM
  return display_hourglass_p ? Qt : Qnil;
#else
  return Qnil;
#endif
}

DEFUN ("--cancel-hourglass", Fc_cancel_hourglass,
       Sc_cancel_hourglass, 0, 0, 0,
       doc: /* Internal: invoke `cancel_hourglass' on window-system builds;
no-op on TTY builds.  */)
  (void)
{
#ifdef HAVE_WINDOW_SYSTEM
  cancel_hourglass ();
#endif
  return Qnil;
}

DEFUN ("--cmd-error-internal", Fc_cmd_error_internal,
       Sc_cmd_error_internal, 2, 2, 0,
       doc: /* Internal: invoke the C cmd_error_internal helper.
DATA is a cons of error-symbol and error-data; CONTEXT is a string
prepended to the message (e.g. "After 3 kbd macro iterations: ").
An empty CONTEXT string is passed through verbatim.  */)
  (Lisp_Object data, Lisp_Object context)
{
  CHECK_STRING (context);
  cmd_error_internal (data, SSDATA (context));
  return Qnil;
}

/* M7h — primitive exposed to (emacs command-loop) for command-loop-main.
   See docs/keyboard.org §M7h.  */

DEFUN ("--clear-executing-kbd-macro-c-only",
       Fc_clear_executing_kbd_macro_c_only,
       Sc_clear_executing_kbd_macro_c_only, 0, 0, 0,
       doc: /* Internal: clear ONLY the C-side `executing_kbd_macro' shadow;
leaves `Vexecuting_kbd_macro' (the elisp defvar) alone.  Matches the
asymmetric behavior of the C command_loop body (which clears the C
shadow but not the elisp var on each loop iteration).  See
docs/keyboard.org §M7h.  */)
  (void)
{
  executing_kbd_macro = Qnil;
  return Qnil;
}

/* Here we catch errors in execution of commands within the
   editing loop, and reenter the editing loop.
   When there is an error, cmd_error runs and returns a non-nil
   value to us.  A value of nil means that command_loop_1 itself
   returned due to end of file (or end of kbd macro).  HANDLERS is a
   list of condition names, passed to internal_condition_case.  */

/* Consolidation: helper used by top-level in (emacs recursive-edit).  */
DEFUN ("--totally-unblock-input", Fc_totally_unblock_input,
       Sc_totally_unblock_input, 0, 0, 0,
       doc: /* Internal: drop the interrupt-input-blocked nesting to zero.
Used by top-level when it enters with input still blocked
(e.g. redisplay trap during tool-bar update).  */)
  (void)
{
  totally_unblock_input ();
  return Qnil;
}

DEFUN ("top-level", Ftop_level, Stop_level, 0, 0, "",
       doc: /* Exit all recursive editing levels.
This also exits all active minibuffers.  */
       attributes: noreturn)
  (void)
{
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs recursive-edit", "top-level");
  SCM_CALL_0 (proc);
  emacs_abort ();  /* unreachable: top-level must throw */
}

static AVOID
user_error (const char *msg)
{
  xsignal1 (Quser_error, build_string (msg));
}

/* M4 — accessor subrs for the C-side counters used by (emacs
   recursive-edit).  Frecursive_edit and its unwind-protect stay C
   for now; only the three trivial DEFUNs (exit/abort/recursion-depth)
   ported.  See docs/keyboard.org §M4.  */

DEFUN ("--command-loop-level", Fcommand_loop_level, Scommand_loop_level, 0, 0, 0,
       doc: /* Internal: current depth in recursive edits.
-1 means not yet inside any command loop.  Modified only by
Frecursive_edit and recursive_edit_unwind in keyboard.c.  */)
  (void)
{
  return make_fixnum (command_loop_level);
}

DEFUN ("--minibuf-level", Fminibuf_level_, Sminibuf_level_, 0, 0, 0,
       doc: /* Internal: current minibuffer-recursion depth from
minibuf.c.  */)
  (void)
{
  return make_fixnum (minibuf_level);
}

/* `exit-recursive-edit' and `abort-recursive-edit' are provided
   entirely by Scheme — see (emacs recursive-edit).  They are
   registered against their elisp symbols by
   init-recursive-edit-registrations at prelude/load.scm startup
   time.  */

/* Restore mouse tracking enablement.  See Finternal_track_mouse for
   the only use of this function.  */

static void
tracking_off (Lisp_Object old_track_mouse)
{
  track_mouse = old_track_mouse;
  if (NILP (old_track_mouse))
    {
      /* Redisplay may have been preempted because there was input
	 available, and it assumes it will be called again after the
	 input has been processed.  If the only input available was
	 the sort that we have just disabled, then we need to call
	 redisplay.  */
      if (!readable_events (READABLE_EVENTS_DO_TIMERS_NOW))
	{
	  redisplay_preserve_echo_area (6);
	  get_input_pending (READABLE_EVENTS_DO_TIMERS_NOW);
	}
    }
}

DEFUN ("internal--track-mouse", Finternal_track_mouse, Sinternal_track_mouse,
       1, 1, 0,
       doc: /* Call BODYFUN with mouse movement events enabled.  */)
  (Lisp_Object bodyfun)
{
  dynwind_begin ();
  Lisp_Object val;

  record_unwind_protect (tracking_off, track_mouse);

  track_mouse = Qt;

  val = call0 (bodyfun);
  dynwind_end ();
  return val;
}

/* If mouse has moved on some frame and we are tracking the mouse,
   return one of those frames.  Return NULL otherwise.

   If ignore_mouse_drag_p is non-zero, ignore (implicit) mouse movement
   after resizing the tool-bar window.  */

bool ignore_mouse_drag_p;

static struct frame *
some_mouse_moved (void)
{
  Lisp_Object tail, frame;

  if (NILP (track_mouse) || ignore_mouse_drag_p)
    return NULL;

  FOR_EACH_FRAME (tail, frame)
    {
      if (XFRAME (frame)->mouse_moved)
	return XFRAME (frame);
    }

  return NULL;
}


/* This is the actual command reading loop,
   sans error-handling encapsulation.  */

enum { READ_KEY_ELTS = 30 };
static int read_key_sequence (Lisp_Object *, Lisp_Object,
                              bool, bool, bool, bool, bool);
static void adjust_point_for_property (ptrdiff_t, bool);

/* M7a — primitives exposed to (emacs command-loop) for the
   command_loop_1 prologue port.  See docs/keyboard.org §M7a.  */

DEFUN ("--cancel-echoing", Fc_cancel_echoing, Sc_cancel_echoing, 0, 0, 0,
       doc: /* Internal: clear echo state on current_kboard.
Wraps the C cancel_echoing helper used by command_loop_1's prologue.  */)
  (void)
{
  cancel_echoing ();
  return Qnil;
}

DEFUN ("--safe-run-hooks", Fc_safe_run_hooks, Sc_safe_run_hooks, 1, 1, 0,
       doc: /* Internal: run HOOK under specbind inhibit-quit=t,
without resizing or narrowing.  Wraps C safe_run_hooks.  */)
  (Lisp_Object hook)
{
  safe_run_hooks (hook);
  return Qnil;
}

DEFUN ("--safe-run-hooks-maybe-narrowed-selected",
       Fc_safe_run_hooks_maybe_narrowed_selected,
       Sc_safe_run_hooks_maybe_narrowed_selected, 1, 1, 0,
       doc: /* Internal: run HOOK under specbind inhibit-quit=t with
maybe-narrowing applied against XWINDOW (selected_window).  Wraps C
safe_run_hooks_maybe_narrowed.  */)
  (Lisp_Object hook)
{
  safe_run_hooks_maybe_narrowed (hook, XWINDOW (selected_window));
  return Qnil;
}

DEFUN ("--resize-echo-area-exactly", Fc_resize_echo_area_exactly,
       Sc_resize_echo_area_exactly, 0, 0, 0,
       doc: /* Internal: resize the echo-area window to fit its current
message.  Wraps xdisp.c resize_echo_area_exactly.  */)
  (void)
{
  resize_echo_area_exactly ();
  return Qnil;
}

DEFUN ("--echo-area-buffer-0-non-empty-p", Fc_echo_area_buffer_0_non_empty_p,
       Sc_echo_area_buffer_0_non_empty_p, 0, 0, 0,
       doc: /* Internal: return t if echo_area_buffer[0] is non-nil.  */)
  (void)
{
  return NILP (echo_area_buffer[0]) ? Qnil : Qt;
}

DEFUN ("--clear-waiting-for-input", Fc_clear_waiting_for_input,
       Sc_clear_waiting_for_input, 0, 0, 0,
       doc: /* Internal: clear the C waiting_for_input flag.  */)
  (void)
{
  waiting_for_input = false;
  return Qnil;
}

/* M7b1 — primitives exposed to (emacs command-loop) for the
   pre-read portion of command_loop_1's main loop body.  See
   docs/keyboard.org §M7b1.  */

DEFUN ("--selected-frame-live-p", Fc_selected_frame_live_p,
       Sc_selected_frame_live_p, 0, 0, 0,
       doc: /* Internal: t if the selected frame is still live.  */)
  (void)
{
  return FRAME_LIVE_P (XFRAME (selected_frame)) ? Qt : Qnil;
}

DEFUN ("--set-buffer-from-selected-window", Fc_set_buffer_from_selected_window,
       Sc_set_buffer_from_selected_window, 0, 0, 0,
       doc: /* Internal: switch current_buffer to the selected window's buffer.
Mirrors the `set_buffer_internal (XBUFFER (XWINDOW (selected_window)->contents))'
calls at top and bottom of command_loop_1's iteration.  */)
  (void)
{
  set_buffer_internal (XBUFFER (XWINDOW (selected_window)->contents));
  return Qnil;
}

DEFUN ("--display-pending-malloc-warnings-loop", Fc_display_pending_malloc_warnings_loop,
       Sc_display_pending_malloc_warnings_loop, 0, 0, 0,
       doc: /* Internal: drain pending_malloc_warning, calling
display_malloc_warning until clear.  */)
  (void)
{
  while (pending_malloc_warning)
    display_malloc_warning ();
  return Qnil;
}

DEFUN ("--clear-ignore-mouse-drag", Fc_clear_ignore_mouse_drag,
       Sc_clear_ignore_mouse_drag, 0, 0, 0,
       doc: /* Internal: clear the C ignore_mouse_drag_p flag.  */)
  (void)
{
  ignore_mouse_drag_p = false;
  return Qnil;
}

DEFUN ("--minibuf-and-echo-area-aligned-p", Fc_minibuf_and_echo_area_aligned_p,
       Sc_minibuf_and_echo_area_aligned_p, 0, 0, 0,
       doc: /* Internal: t when all four conditions hold for the
minibuffer-message timing dance at the top of command_loop_1's iter:
  minibuf_level > 0
  && echo_area_buffer[0] non-nil
  && minibuf_window == echo_area_window
  && Vminibuffer_message_timeout is a number.  */)
  (void)
{
  return (minibuf_level
          && !NILP (echo_area_buffer[0])
          && BASE_EQ (minibuf_window, echo_area_window)
          && NUMBERP (Vminibuffer_message_timeout))
    ? Qt : Qnil;
}

DEFUN ("--resize-mini-window-minibuf-non-shrink",
       Fc_resize_mini_window_minibuf_non_shrink,
       Sc_resize_mini_window_minibuf_non_shrink, 0, 0, 0,
       doc: /* Internal: resize_mini_window (XWINDOW (minibuf_window), false).  */)
  (void)
{
  resize_mini_window (XWINDOW (minibuf_window), false);
  return Qnil;
}

DEFUN ("--quit-char", Fc_quit_char_, Sc_quit_char_, 0, 0, 0,
       doc: /* Internal: return the current C quit_char as a fixnum
(default 7, ASCII C-g).  Used by command_loop_1's minibuffer-timeout
branch when re-queueing a C-g into unread-command-events.  */)
  (void)
{
  return make_fixnum (quit_char);
}

DEFUN ("--set-raw-keybuf-count", Fc_set_raw_keybuf_count, Sc_set_raw_keybuf_count, 1, 1, 0,
       doc: /* Internal: set raw_keybuf_count to N.  Callers run
before the read_key_sequence record-stack push (rks_state_depth==0),
so no <rks-state> mirror is needed here.  */)
  (Lisp_Object n)
{
  CHECK_FIXNAT (n);
  raw_keybuf_count = XFIXNAT (n);
  return Qnil;
}

DEFUN ("--read-key-sequence", Fc_read_key_sequence_, Sc_read_key_sequence_, 0, 0, 0,
       doc: /* Internal: read the next key sequence from the active input source.
Wraps the C read_key_sequence(keybuf, Qnil, false, true, true, false, false)
call used by command_loop_1.  Side effects: read_key_sequence_cmd /
read_key_sequence_remapped get set, raw_keybuf is populated.  When the
returned length is > 0 this subr also sets last_command_event to the
last key in the sequence; on EOF (0) or menu-reject (-1) it leaves
last_command_event alone.  Returns the integer length.  */)
  (void)
{
  Lisp_Object keybuf[READ_KEY_ELTS];
  int i = read_key_sequence (keybuf, Qnil, false, true, true, false, false);
  if (i > 0)
    last_command_event = keybuf[i - 1];
  return make_fixnum (i);
}

DEFUN ("--inc-num-input-keys", Fc_inc_num_input_keys, Sc_inc_num_input_keys, 0, 0, 0,
       doc: /* Internal: increment num_input_keys.  */)
  (void)
{
  ++num_input_keys;
  return Qnil;
}

/* M7b2 — dispatch portion of command_loop_1's while-loop body, including
   pre-command-hook and the command-execute call.  Shared state
   (`prev_buffer', `prev_modiff') was promoted from command_loop_1 locals
   to file-static here so M7b3/M7c can still read them once they move to
   Scheme too.  See docs/keyboard.org §M7b2.  */

static modiff_count cl1_prev_modiff = 0;
static struct buffer *cl1_prev_buffer = NULL;

DEFUN ("--clear-force-start-and-flush-buffer-unchanged",
       Fc_clear_force_start_and_flush_buffer_unchanged,
       Sc_clear_force_start_and_flush_buffer_unchanged, 0, 0, 0,
       doc: /* Internal: if the selected window has force_start set, clear it
and zero BUF_BEG_UNCHANGED/BUF_END_UNCHANGED on its buffer.  No-op
otherwise.  */)
  (void)
{
  if (XWINDOW (selected_window)->force_start)
    {
      struct buffer *b;
      XWINDOW (selected_window)->force_start = 0;
      b = XBUFFER (XWINDOW (selected_window)->contents);
      BUF_BEG_UNCHANGED (b) = BUF_END_UNCHANGED (b) = 0;
    }
  return Qnil;
}

DEFUN ("--read-key-sequence-cmd", Fc_read_key_sequence_cmd,
       Sc_read_key_sequence_cmd, 0, 0, 0,
       doc: /* Internal: return the C-side read_key_sequence_cmd
(the command symbol the last read_key_sequence call resolved to).  */)
  (void)
{
  return read_key_sequence_cmd;
}

DEFUN ("--read-key-sequence-remapped", Fc_read_key_sequence_remapped,
       Sc_read_key_sequence_remapped, 0, 0, 0,
       doc: /* Internal: return the C-side read_key_sequence_remapped
(the post-remap target if `read_key_sequence' followed `command-remapping').  */)
  (void)
{
  return read_key_sequence_remapped;
}

DEFUN ("--set-read-key-sequence-remapped",
       Fc_set_read_key_sequence_remapped,
       Sc_set_read_key_sequence_remapped, 1, 1, 0,
       doc: /* Internal: set the C-side `read_key_sequence_remapped'
to X.  Called by the Scheme done:-block port to install the result
of `command-remapping' on read_key_sequence_cmd.  */)
  (Lisp_Object x)
{
  read_key_sequence_remapped = x;
  return Qnil;
}

DEFUN ("--maybe-quit", Fc_maybe_quit, Sc_maybe_quit, 0, 0, 0,
       doc: /* Internal: call C maybe_quit().  Signals quit if Vquit_flag is set
and inhibit-quit is nil.  */)
  (void)
{
  maybe_quit ();
  return Qnil;
}

DEFUN ("--save-state-for-redisplay-get-pt",
       Fc_save_state_for_redisplay_get_pt,
       Sc_save_state_for_redisplay_get_pt, 0, 0, 0,
       doc: /* Internal: set cl1_prev_buffer = current_buffer,
cl1_prev_modiff = MODIFF, last_point_position = PT.  Return PT as a
fixnum (caller saves it as `last_pt' to restore after command-execute).  */)
  (void)
{
  cl1_prev_buffer = current_buffer;
  cl1_prev_modiff = MODIFF;
  last_point_position = PT;
  return make_fixnum (PT);
}

DEFUN ("--restore-last-point-position", Fc_restore_last_point_position,
       Sc_restore_last_point_position, 1, 1, 0,
       doc: /* Internal: set last_point_position to N.  Used after
command-execute to restore the pre-command PT (which may have been
clobbered by a recursive-edit inside the command).  */)
  (Lisp_Object n)
{
  CHECK_FIXNAT (n);
  last_point_position = XFIXNAT (n);
  return Qnil;
}

DEFUN ("--record-recent-keys-cmd-pseudo-event",
       Fc_record_recent_keys_cmd_pseudo_event,
       Sc_record_recent_keys_cmd_pseudo_event, 1, 1, 0,
       doc: /* Internal: push the (nil . CMD) pseudo-event into the
recent_keys ring, with lossage rotation.  Mirrors the inline block in
command_loop_1 dispatch.  */)
  (Lisp_Object cmd)
{
  total_keys += total_keys < lossage_limit;
  ASET (recent_keys, recent_keys_index, Fcons (Qnil, cmd));
  if (++recent_keys_index >= lossage_limit)
    recent_keys_index = 0;
  return Qnil;
}

DEFUN ("--with-hourglass-protection", Fc_with_hourglass_protection,
       Sc_with_hourglass_protection, 1, 1, 0,
       doc: /* Internal: invoke THUNK inside a dynwind frame that
records cancel_hourglass as the unwind handler and calls start_hourglass
on the way in — but only when HAVE_WINDOW_SYSTEM, display_hourglass_p,
and not inside a kbd macro.  In batch / tty it is a plain
funcall-the-thunk.  Returns whatever THUNK returns.  */)
  (Lisp_Object thunk)
{
#ifdef HAVE_WINDOW_SYSTEM
  dynwind_begin ();
  if (display_hourglass_p && NILP (Vexecuting_kbd_macro))
    {
      record_unwind_protect_void (cancel_hourglass);
      start_hourglass ();
    }
  Lisp_Object r = call0 (thunk);
  dynwind_end ();
  return r;
#else
  return call0 (thunk);
#endif
}

DEFUN ("--save-point-before-last-command-or-undo",
       Fc_save_point_before_last_command_or_undo,
       Sc_save_point_before_last_command_or_undo, 0, 0, 0,
       doc: /* Internal: snapshot point_before_last_command_or_undo = PT
and buffer_before_last_command_or_undo = current_buffer.  Used by undo
machinery to put point into the undo information if needed.  */)
  (void)
{
  point_before_last_command_or_undo = PT;
  buffer_before_last_command_or_undo = current_buffer;
  return Qnil;
}

DEFUN ("--reset-redisplay-tick-state", Fc_reset_redisplay_tick_state,
       Sc_reset_redisplay_tick_state, 0, 0, 0,
       doc: /* Internal: update_redisplay_ticks (0, NULL) +
display_working_on_window_p = false.  Run before command-execute so the
new command isn't charged for the previous command's redisplay cost.  */)
  (void)
{
  update_redisplay_ticks (0, NULL);
  display_working_on_window_p = false;
  return Qnil;
}

DEFUN ("--clear-display-working-on-window-p",
       Fc_clear_display_working_on_window_p,
       Sc_clear_display_working_on_window_p, 0, 0, 0,
       doc: /* Internal: display_working_on_window_p = false.  Called
again after command-execute returns.  */)
  (void)
{
  display_working_on_window_p = false;
  return Qnil;
}

/* M7b3 — primitives exposed to (emacs command-loop) for the
   post-dispatch portion of command_loop_1.  See docs/keyboard.org §M7b3.  */

DEFUN ("--echo-area-window-eq-selected-frame-minibuf-p",
       Fc_echo_area_window_eq_selected_frame_minibuf_p,
       Sc_echo_area_window_eq_selected_frame_minibuf_p, 0, 0, 0,
       doc: /* Internal: t iff `echo_area_window' is the same as
FRAME_MINIBUF_WINDOW (selected_frame).  Used by command_loop_1's
post-dispatch echo-area-resize guard (Bug#34317).  */)
  (void)
{
  return EQ (echo_area_window,
             FRAME_MINIBUF_WINDOW (XFRAME (selected_frame)))
    ? Qt : Qnil;
}

DEFUN ("--current-kboard-immediate-echo-p",
       Fc_current_kboard_immediate_echo_p,
       Sc_current_kboard_immediate_echo_p, 0, 0, 0,
       doc: /* Internal: read current_kboard->immediate_echo (bit field
not covered by the M2 KBOARD_LISP_FIELD generator).  */)
  (void)
{
  return current_kboard->immediate_echo ? Qt : Qnil;
}

DEFUN ("--clear-current-kboard-immediate-echo",
       Fc_clear_current_kboard_immediate_echo,
       Sc_clear_current_kboard_immediate_echo, 0, 0, 0,
       doc: /* Internal: set current_kboard->immediate_echo to false.  */)
  (void)
{
  current_kboard->immediate_echo = false;
  return Qnil;
}

DEFUN ("--echo-now", Fc_echo_now, Sc_echo_now, 0, 0, 0,
       doc: /* Internal: call C echo_now() to refresh the echo display
on current_kboard.  */)
  (void)
{
  echo_now ();
  return Qnil;
}

/* M7b4 — primitives exposed to (emacs command-loop) for the
   mark/region block.  See docs/keyboard.org §M7b4.  */

DEFUN ("--current-buffer-mark-active-p", Fc_current_buffer_mark_active_p,
       Sc_current_buffer_mark_active_p, 0, 0, 0,
       doc: /* Internal: read BVAR (current_buffer, mark_active) as a
non-nil predicate.  The buffer-local `mark-active' variable.  */)
  (void)
{
  return NILP (BVAR (current_buffer, mark_active)) ? Qnil : Qt;
}

DEFUN ("--current-buffer-mark-has-buffer-p",
       Fc_current_buffer_mark_has_buffer_p,
       Sc_current_buffer_mark_has_buffer_p, 0, 0, 0,
       doc: /* Internal: t if XMARKER (BVAR (current_buffer, mark))->buffer
is non-NULL.  Mark-active can be t even when the underlying marker has
no buffer (Bug#7044 guard).  */)
  (void)
{
  return XMARKER (BVAR (current_buffer, mark))->buffer ? Qt : Qnil;
}

DEFUN ("--cl1-prev-buffer-current-p", Fc_cl1_prev_buffer_current_p,
       Sc_cl1_prev_buffer_current_p, 0, 0, 0,
       doc: /* Internal: t if the file-static cl1_prev_buffer (snapshot
captured at the start of this iteration's dispatch) equals
current_buffer.  False ⇒ the command changed buffer.  */)
  (void)
{
  return current_buffer == cl1_prev_buffer ? Qt : Qnil;
}

DEFUN ("--cl1-prev-modiff-current-p", Fc_cl1_prev_modiff_current_p,
       Sc_cl1_prev_modiff_current_p, 0, 0, 0,
       doc: /* Internal: t if the file-static cl1_prev_modiff equals
MODIFF on the current buffer.  False ⇒ the command modified the buffer.  */)
  (void)
{
  return MODIFF == cl1_prev_modiff ? Qt : Qnil;
}

/* M7c — primitives exposed to (emacs command-loop) for the finalize
   block (point adjustment + kbd-macro chars install).  See
   docs/keyboard.org §M7c.  */

DEFUN ("--selected-window-buffer-current-p",
       Fc_selected_window_buffer_current_p,
       Sc_selected_window_buffer_current_p, 0, 0, 0,
       doc: /* Internal: t if XBUFFER (XWINDOW (selected_window)->contents)
equals current_buffer.  False ⇒ the command changed the selected
window's buffer out from under us.  */)
  (void)
{
  return XBUFFER (XWINDOW (selected_window)->contents) == current_buffer
    ? Qt : Qnil;
}

DEFUN ("--last-point-position-ne-pt-p",
       Fc_last_point_position_ne_pt_p,
       Sc_last_point_position_ne_pt_p, 0, 0, 0,
       doc: /* Internal: t if the snapshot last_point_position (captured
at the start of dispatch) differs from current PT.  */)
  (void)
{
  return last_point_position != PT ? Qt : Qnil;
}

DEFUN ("--composition-break-at-point-p",
       Fc_composition_break_at_point_p,
       Sc_composition_break_at_point_p, 0, 0, 0,
       doc: /* Internal: t if the C global composition_break_at_point is
non-zero.  Bound to the elisp `composition-break-at-point' user
option.  */)
  (void)
{
  return composition_break_at_point ? Qt : Qnil;
}

DEFUN ("--last-point-position-in-accessible-p",
       Fc_last_point_position_in_accessible_p,
       Sc_last_point_position_in_accessible_p, 0, 0, 0,
       doc: /* Internal: t if BEGV < last_point_position < ZV in the
current buffer.  */)
  (void)
{
  return (last_point_position > BEGV && last_point_position < ZV)
    ? Qt : Qnil;
}

DEFUN ("--pt-in-accessible-p", Fc_pt_in_accessible_p,
       Sc_pt_in_accessible_p, 0, 0, 0,
       doc: /* Internal: t if BEGV < PT < ZV in the current buffer.  */)
  (void)
{
  return (PT > BEGV && PT < ZV) ? Qt : Qnil;
}

DEFUN ("--composition-adjust-point-lpp-changes-p",
       Fc_composition_adjust_point_lpp_changes_p,
       Sc_composition_adjust_point_lpp_changes_p, 0, 0, 0,
       doc: /* Internal: t if composition_adjust_point (last_point_position,
last_point_position) differs from last_point_position.  Indicates
the last point landed inside a grapheme cluster — display must be
invalidated to recover automatic composition.  */)
  (void)
{
  return (composition_adjust_point (last_point_position, last_point_position)
	  != last_point_position) ? Qt : Qnil;
}

DEFUN ("--composition-adjust-point-pt-changes-p",
       Fc_composition_adjust_point_pt_changes_p,
       Sc_composition_adjust_point_pt_changes_p, 0, 0, 0,
       doc: /* Internal: t if composition_adjust_point (last_point_position,
PT) differs from PT.  Indicates the current point lies inside a
grapheme cluster — display must be invalidated.  */)
  (void)
{
  return (composition_adjust_point (last_point_position, PT) != PT)
    ? Qt : Qnil;
}

DEFUN ("--adjust-point-for-property-cl1",
       Fc_adjust_point_for_property_cl1,
       Sc_adjust_point_for_property_cl1, 0, 0, 0,
       doc: /* Internal: call adjust_point_for_property (last_point_position,
MODIFF != cl1_prev_modiff).  Pulls the modified-flag from the
file-static cl1_prev_modiff snapshot so Scheme doesn't have to
plumb it.  */)
  (void)
{
  adjust_point_for_property (last_point_position, MODIFF != cl1_prev_modiff);
  return Qnil;
}

DEFUN ("--set-windows-or-buffers-changed",
       Fc_set_windows_or_buffers_changed,
       Sc_set_windows_or_buffers_changed, 1, 1, 0,
       doc: /* Internal: set the C global windows_or_buffers_changed to N
(a small integer; only 21 and 39 are used from the finalize
block).  */)
  (Lisp_Object n)
{
  CHECK_FIXNUM (n);
  windows_or_buffers_changed = XFIXNUM (n);
  return Qnil;
}

DEFUN ("--finalize-kbd-macro-chars", Fc_finalize_kbd_macro_chars,
       Sc_finalize_kbd_macro_chars, 0, 0, 0,
       doc: /* Internal: invoke the C finalize_kbd_macro_chars helper that
installs chars successfully executed in the current kbd-macro
recording.  */)
  (void)
{
  finalize_kbd_macro_chars ();
  return Qnil;
}

Lisp_Object
read_menu_command (void)
{
  dynwind_begin ();

  /* We don't want to echo the keystrokes while navigating the
     menus.  */
  specbind_guile (Qecho_keystrokes, make_fixnum (0));

  Lisp_Object keybuf[READ_KEY_ELTS];
  int i = read_key_sequence (keybuf, Qnil, false, true, true, true,
			     false);

  dynwind_end ();

  if (! FRAME_LIVE_P (XFRAME (selected_frame)))
    Fkill_emacs (Qnil, Qnil);
  if (i == 0 || i == -1)
    return Qt;

  return read_key_sequence_cmd;
}

/* Adjust point to a boundary of a region that has such a property
   that should be treated intangible.  For the moment, we check
   `composition', `display' and `invisible' properties.
   LAST_PT is the last position of point.  */

static void
adjust_point_for_property (ptrdiff_t last_pt, bool modified)
{
  ptrdiff_t beg, end;
  Lisp_Object val, overlay, tmp;
  /* When called after buffer modification, we should temporarily
     suppress the point adjustment for automatic composition so that a
     user can keep inserting another character at point or keep
     deleting characters around point.  */
  bool check_composition = ! modified;
  bool check_display = true, check_invisible = true;
  ptrdiff_t orig_pt = PT;

  eassert (XBUFFER (XWINDOW (selected_window)->contents) == current_buffer);

  /* FIXME: cycling is probably not necessary because these properties
     can't be usefully combined anyway.  */
  while (check_composition || check_display || check_invisible)
    {
      /* FIXME: check `intangible'.  */
      if (check_composition
	  && PT > BEGV && PT < ZV
	  && (beg = composition_adjust_point (last_pt, PT)) != PT)
	{
	  SET_PT (beg);
	  check_display = check_invisible = true;
	}
      check_composition = false;
      if (check_display
	  && PT > BEGV && PT < ZV
	  && !NILP (val = get_char_property_and_overlay
		              (make_fixnum (PT), Qdisplay, selected_window,
			       &overlay))
	  && display_prop_intangible_p (val, overlay, PT, PT_BYTE)
	  && (!OVERLAYP (overlay)
	      ? get_property_and_range (PT, Qdisplay, &val, &beg, &end, Qnil)
	      : (beg = OVERLAY_START (overlay),
		 end = OVERLAY_END (overlay)))
	  && (beg < PT /* && end > PT   <- It's always the case.  */
	      || (beg <= PT && STRINGP (val) && SCHARS (val) == 0)))
	{
	  eassert (end > PT);
	  SET_PT (PT < last_pt
		  ? (STRINGP (val) && SCHARS (val) == 0
		     ? max (beg - 1, BEGV)
		     : beg)
		  : end);
	  check_composition = check_invisible = true;
	}
      check_display = false;
      if (check_invisible && PT > BEGV && PT < ZV)
	{
	  int inv;
	  bool ellipsis = false;
	  beg = end = PT;

	  /* Find boundaries `beg' and `end' of the invisible area, if any.  */
	  while (end < ZV
#if 0
		 /* FIXME: We should stop if we find a spot between
		    two runs of `invisible' where inserted text would
		    be visible.  This is important when we have two
		    invisible boundaries that enclose an area: if the
		    area is empty, we need this test in order to make
		    it possible to place point in the middle rather
		    than skip both boundaries.  However, this code
		    also stops anywhere in a non-sticky text-property,
		    which breaks (e.g.) Org mode.  */
		 && (val = Fget_pos_property (make_fixnum (end),
					      Qinvisible, Qnil),
		     TEXT_PROP_MEANS_INVISIBLE (val))
#endif
		 && !NILP (val = get_char_property_and_overlay
		           (make_fixnum (end), Qinvisible, Qnil, &overlay))
		 && (inv = TEXT_PROP_MEANS_INVISIBLE (val)))
	    {
	      ellipsis = ellipsis || inv > 1
		|| (OVERLAYP (overlay)
		    && (!NILP (Foverlay_get (overlay, Qafter_string))
			|| !NILP (Foverlay_get (overlay, Qbefore_string))));
	      tmp = Fnext_single_char_property_change
		(make_fixnum (end), Qinvisible, Qnil, Qnil);
	      end = FIXNATP (tmp) ? XFIXNAT (tmp) : ZV;
	    }
	  while (beg > BEGV
#if 0
		 && (val = Fget_pos_property (make_fixnum (beg),
					      Qinvisible, Qnil),
		     TEXT_PROP_MEANS_INVISIBLE (val))
#endif
		 && !NILP (val = get_char_property_and_overlay
		           (make_fixnum (beg - 1), Qinvisible, Qnil, &overlay))
		 && (inv = TEXT_PROP_MEANS_INVISIBLE (val)))
	    {
	      ellipsis = ellipsis || inv > 1
		|| (OVERLAYP (overlay)
		    && (!NILP (Foverlay_get (overlay, Qafter_string))
			|| !NILP (Foverlay_get (overlay, Qbefore_string))));
	      tmp = Fprevious_single_char_property_change
		(make_fixnum (beg), Qinvisible, Qnil, Qnil);
	      beg = FIXNATP (tmp) ? XFIXNAT (tmp) : BEGV;
	    }

	  /* Move away from the inside area.  */
	  if (beg < PT && end > PT)
	    {
	      SET_PT ((orig_pt == PT && (last_pt < beg || last_pt > end))
		      /* We haven't moved yet (so we don't need to fear
			 infinite-looping) and we were outside the range
			 before (so either end of the range still corresponds
			 to a move in the right direction): pretend we moved
			 less than we actually did, so that we still have
			 more freedom below in choosing which end of the range
			 to go to.  */
		      ? (orig_pt = -1, PT < last_pt ? end : beg)
		      /* We either have moved already or the last point
			 was already in the range: we don't get to choose
			 which end of the range we have to go to.  */
		      : (PT < last_pt ? beg : end));
	      check_composition = check_display = true;
	    }
#if 0 /* This assertion isn't correct, because SET_PT may end up setting
	 the point to something other than its argument, due to
	 point-motion hooks, intangibility, etc.  */
	  eassert (PT == beg || PT == end);
#endif

	  /* Pretend the area doesn't exist if the buffer is not
	     modified.  */
	  if (!modified && !ellipsis && beg < end)
	    {
	      if (last_pt == beg && PT == end && end < ZV)
		(check_composition = check_display = true, SET_PT (end + 1));
	      else if (last_pt == end && PT == beg && beg > BEGV)
		(check_composition = check_display = true, SET_PT (beg - 1));
	      else if (PT == ((PT < last_pt) ? beg : end))
		/* We've already moved as far as we can.  Trying to go
		   to the other end would mean moving backwards and thus
		   could lead to an infinite loop.  */
		;
	      else if (val = Fget_pos_property (make_fixnum (PT),
						Qinvisible, Qnil),
		       TEXT_PROP_MEANS_INVISIBLE (val)
		       && (val = (Fget_pos_property
				  (make_fixnum (PT == beg ? end : beg),
				   Qinvisible, Qnil)),
			   !TEXT_PROP_MEANS_INVISIBLE (val)))
		(check_composition = check_display = true,
		 SET_PT (PT == beg ? end : beg));
	    }
	}
      check_invisible = false;
    }
}

/* Subroutine for safe_run_hooks: run the hook's function.
   ARGS[0] holds the name of the hook, which we don't need here (we only use
   it in the failure case of the internal_condition_case_n).  */

static Lisp_Object
safe_run_hooks_1 (ptrdiff_t nargs, Lisp_Object *args)
{
  eassert (nargs >= 2);
  return Ffuncall (nargs - 1, args + 1);
}

/* Subroutine for safe_run_hooks: handle an error by clearing out the function
   from the hook.  */

static Lisp_Object
safe_run_hooks_error (Lisp_Object error, ptrdiff_t nargs, Lisp_Object *args)
{
  eassert (nargs >= 2);
  AUTO_STRING (format, "Error in %s (%S): %S");
  Lisp_Object hook = args[0];
  Lisp_Object fun = args[1];
  CALLN (Fmessage, format, hook, fun, error);

  if (SYMBOLP (hook))
    {
      bool found = false;
      Lisp_Object newval = Qnil;
      Lisp_Object val = find_symbol_value (hook);
      FOR_EACH_TAIL (val)
	if (EQ (fun, XCAR (val)))
	  found = true;
	else
	  newval = Fcons (XCAR (val), newval);
      if (found)
	return Fset (hook, Fnreverse (newval));
      /* Not found in the local part of the hook.  Let's look at the global
	 part.  */
      newval = Qnil;
      val = NILP (Fdefault_boundp (hook)) ? Qnil : Fdefault_value (hook);
      FOR_EACH_TAIL (val)
	if (EQ (fun, XCAR (val)))
	  found = true;
	else
	  newval = Fcons (XCAR (val), newval);
      if (found)
	return Fset_default (hook, Fnreverse (newval));
    }
  return Qnil;
}

static Lisp_Object
safe_run_hook_funcall (ptrdiff_t nargs, Lisp_Object *args)
{
  /* We need to swap args[0] and args[1] here or in `safe_run_hooks_1`.
     It's more convenient to do it here.  */
  eassert (nargs >= 2);
  Lisp_Object fun = args[0], hook = args[1];
  /* The `nargs` array cannot be mutated safely here because it is
     reused by our caller `run_hook_with_args`.
     We could arguably change it temporarily if we set it back
     to its original state before returning, but it's too ugly.  */
  USE_SAFE_ALLOCA;
  Lisp_Object *newargs;
  SAFE_ALLOCA_LISP (newargs, nargs);
  newargs[0] = hook, newargs[1] = fun;
  memcpy (newargs + 2, args + 2, (nargs - 2) * word_size);
  internal_condition_case_n (safe_run_hooks_1, nargs, newargs,
                             Qt, safe_run_hooks_error);
  SAFE_FREE ();
  return Qnil;
}

/* If we get an error while running the hook, cause the hook variable
   to be nil.  Also inhibit quits, so that C-g won't cause the hook
   to mysteriously evaporate.  */

void
safe_run_hooks (Lisp_Object hook)
{
  dynwind_begin ();
  specbind_guile (Qinhibit_quit, Qt);
  run_hook_with_args (2, ((Lisp_Object []) {hook, hook}),
                      safe_run_hook_funcall);
  dynwind_end ();
}

static void
safe_run_hooks_maybe_narrowed (Lisp_Object hook, struct window *w)
{
  dynwind_begin ();

  specbind_guile (Qinhibit_quit, Qt);

  if (current_buffer->long_line_optimizations_p
      && long_line_optimizations_region_size > 0)
    {
      ptrdiff_t begv = get_large_narrowing_begv (PT);
      ptrdiff_t zv = get_large_narrowing_zv (PT);
      if (begv != BEG || zv != Z)
	labeled_narrow_to_region (make_fixnum (begv), make_fixnum (zv),
				  Qlong_line_optimizations_in_command_hooks);
    }

  run_hook_with_args (2, ((Lisp_Object []) {hook, hook}), safe_run_hook_funcall);
  dynwind_end ();
}

void
safe_run_hooks_2 (Lisp_Object hook, Lisp_Object arg1, Lisp_Object arg2)
{
  dynwind_begin ();

  specbind_guile (Qinhibit_quit, Qt);
  run_hook_with_args (4, ((Lisp_Object []) {hook, hook, arg1, arg2}),
		      safe_run_hook_funcall);
  dynwind_end ();
}


#ifdef POLL_FOR_INPUT

/* Asynchronous timer for polling.  */

static struct atimer *poll_timer;

/* The poll period that constructed this timer.  */
static Lisp_Object poll_timer_time;

#if defined CYGWIN || defined DOS_NT
/* Poll for input, so that we catch a C-g if it comes in.  */
void
poll_for_input_1 (void)
{
  if (! input_blocked_p ()
      && !waiting_for_input)
    gobble_input ();
}
#endif

/* Timer callback function for poll_timer.  TIMER is equal to
   poll_timer.  */

static void
poll_for_input (struct atimer *timer)
{
}

#endif /* POLL_FOR_INPUT */

/* Begin signals to poll for input, if they are appropriate.
   This function is called unconditionally from various places.  */

void
start_polling (void)
{
#ifdef POLL_FOR_INPUT
  /* XXX This condition was (read_socket_hook && !interrupt_input),
     but read_socket_hook is not global anymore.  Let's pretend that
     it's always set.  */
  if (!interrupt_input)
    {
      /* Turn alarm handling on unconditionally.  It might have
	 been turned off in process.c.  */
      turn_on_atimers (1);

      /* If poll timer doesn't exist, or we need one with
	 a different interval, start a new one.  */
      if (NUMBERP (Vpolling_period)
	  && (poll_timer == NULL
	      || NILP (Fequal (Vpolling_period, poll_timer_time))))
	{
	  struct timespec interval = dtotimespec (XFLOATINT (Vpolling_period));

	  if (poll_timer)
	    cancel_atimer (poll_timer);

	  poll_timer = start_atimer (ATIMER_CONTINUOUS, interval,
				     poll_for_input, NULL);
	  poll_timer_time = Vpolling_period;
	}
    }
#endif
}

#if defined CYGWIN || defined DOS_NT
/* True if we are using polling to handle input asynchronously.  */

bool
input_polling_used (void)
{
# ifdef POLL_FOR_INPUT
  /* XXX This condition was (read_socket_hook && !interrupt_input),
     but read_socket_hook is not global anymore.  Let's pretend that
     it's always set.  */
  return !interrupt_input;
# else
  return false;
# endif
}
#endif

/* Bind polling_period to a value at least N.
   But don't decrease it.  */

void
bind_polling_period (int n)
{
#ifdef POLL_FOR_INPUT
  if (FIXNUMP (Vpolling_period))
    {
      // guilemacs, FIXHOW? see orig efdd2e5c64 max operator
      intmax_t new = XFIXNUM (Vpolling_period);

      if (n > new)
	new = n;

      stop_other_atimers (poll_timer);
      specbind_guile (Qpolling_period, make_int (new));
    }
  else if (FLOATP (Vpolling_period))
    {
      double new = XFLOAT_DATA (Vpolling_period);

      stop_other_atimers (poll_timer);
      specbind_guile (Qpolling_period, (n > new
				  ? make_int (n)
				  : Vpolling_period));
    }

  /* Start a new alarm with the new period.  */
  start_polling ();
#endif
}

/* Apply the control modifier to CHARACTER.  Body lives in
   (emacs event-modifiers) as `make-ctrl-char'; this is the C
   dispatch shim for non-Scheme callers (still used in keyboard.c
   and w32fns.c).  */

int
make_ctrl_char (int c)
{
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs event-modifiers", "make-ctrl-char");
  return scm_to_int (SCM_CALL_1 (proc, scm_from_int (c)));
}

/* Substitute key descriptions and quotes in HELP, unless its first
   character has a non-nil help-echo-inhibit-substitution property.  */

static Lisp_Object
help_echo_substitute_command_keys (Lisp_Object help)
{
  if (STRINGP (help)
      && SCHARS (help) > 0
      && !NILP (Fget_text_property (make_fixnum (0),
                                    Qhelp_echo_inhibit_substitution,
                                    help)))
    return help;

  return call1 (Qsubstitute_command_keys, help);
}

/* Display the help-echo property of the character after the mouse pointer.
   Either show it in the echo area, or call show-help-function to display
   it by other means (maybe in a tooltip).

   If HELP is nil, that means clear the previous help echo.

   If HELP is a string, display that string.  If HELP is a function,
   call it with OBJECT and POS as arguments; the function should
   return a help string or nil for none.  For all other types of HELP,
   evaluate it to obtain a string.

   WINDOW is the window in which the help was generated, if any.
   It is nil if not in a window.

   If OBJECT is a buffer, POS is the position in the buffer where the
   `help-echo' text property was found.

   If OBJECT is an overlay, that overlay has a `help-echo' property,
   and POS is the position in the overlay's buffer under the mouse.

   If OBJECT is a string (an overlay string or a string displayed with
   the `display' property).  POS is the position in that string under
   the mouse.

   Note: this function may only be called with HELP nil or a string
   from X code running asynchronously.  */

void
show_help_echo (Lisp_Object help, Lisp_Object window, Lisp_Object object,
		Lisp_Object pos)
{
  if (!NILP (help) && !STRINGP (help))
    {
      if (FUNCTIONP (help))
	help = safe_calln (help, window, object, pos);
      else
	help = safe_eval (help);

      if (!STRINGP (help))
	return;
    }

  if (!noninteractive && STRINGP (help))
    {
      /* The mouse-fixup-help-message Lisp function can call
	 mouse_position_hook, which resets the mouse_moved flags.
	 This causes trouble if we are trying to read a mouse motion
	 event (i.e., if we are inside a `track-mouse' form), so we
	 restore the mouse_moved flag.  */
      struct frame *f = some_mouse_moved ();

      help = call1 (Qmouse_fixup_help_message, help);
      if (f)
	f->mouse_moved = true;
    }

  if (STRINGP (help) || NILP (help))
    {
      if (!NILP (Vshow_help_function))
	call1 (Vshow_help_function, help_echo_substitute_command_keys (help));
      help_echo_showing_p = STRINGP (help);
    }
}



/* Input of single characters from keyboard.  */

static Lisp_Object kbd_buffer_get_event (KBOARD **kbp, bool *used_mouse_menu,
					 struct timespec *end_time);
static void record_char (Lisp_Object c);

static Lisp_Object help_form_saved_window_configs;
static void
read_char_help_form_unwind (void)
{
  Lisp_Object window_config = XCAR (help_form_saved_window_configs);
  help_form_saved_window_configs = XCDR (help_form_saved_window_configs);
  if (!NILP (window_config))
    Fset_window_configuration (window_config, Qnil, Qnil);
}

static Lisp_Object
read_event_from_main_queue (struct timespec *end_time,
                            Lisp_Object local_tag,
                            bool *used_mouse_menu)
{
  Lisp_Object c = Qnil;
  Lisp_Object save_tag = Qnil;
  sys_jmp_buf *save_jump = xmalloc (sizeof *save_jump);
  KBOARD *kb;

 start:

  /* Read from the main queue, and if that gives us something we can't use yet,
     we put it on the appropriate side queue and try again.  */

  if (end_time && timespec_cmp (*end_time, current_timespec ()) <= 0)
    return c;

  /* Actually read a character, waiting if necessary.  */
  save_tag = getctag;
  getctag = local_tag;
  if (!end_time)
    timer_start_idle ();
  c = kbd_buffer_get_event (&kb, used_mouse_menu, end_time);
  getctag = save_tag;

  if (! NILP (c) && (kb != current_kboard))
    {
      Lisp_Object last = KVAR (kb, kbd_queue);
      if (CONSP (last))
        {
          while (CONSP (XCDR (last)))
	    last = XCDR (last);
          if (!NILP (XCDR (last)))
	    emacs_abort ();
        }
      if (!CONSP (last))
        kset_kbd_queue (kb, list1 (c));
      else
        XSETCDR (last, list1 (c));
      kb->kbd_queue_has_data = true;
      c = Qnil;
      if (single_kboard)
        goto start;
      current_kboard = kb;
      return make_fixnum (-2);
    }

  /* Terminate Emacs in batch mode if at eof.  */
  if (noninteractive && FIXNUMP (c) && XFIXNUM (c) < 0)
    Fkill_emacs (make_fixnum (1), Qnil);

  if (FIXNUMP (c))
    {
      /* Add in any extra modifiers, where appropriate.  */
      if ((extra_keyboard_modifiers & CHAR_CTL)
	  || ((extra_keyboard_modifiers & 0177) < ' '
	      && (extra_keyboard_modifiers & 0177) != 0))
	XSETINT (c, make_ctrl_char (XFIXNUM (c)));

      /* Transfer any other modifier bits directly from
	 extra_keyboard_modifiers to c.  Ignore the actual character code
	 in the low 16 bits of extra_keyboard_modifiers.  */
      XSETINT (c, XFIXNUM (c) | (extra_keyboard_modifiers & ~0xff7f & ~CHAR_CTL));
    }

  return c;
}



/* Like `read_event_from_main_queue' but applies keyboard-coding-system
   to tty input.  */
static Lisp_Object
read_decoded_event_from_main_queue (struct timespec *end_time,
                                    Lisp_Object local_getcjmp,
                                    Lisp_Object prev_event,
                                    bool *used_mouse_menu)
{
#ifndef WINDOWSNT
#define MAX_ENCODED_BYTES 16
  Lisp_Object events[MAX_ENCODED_BYTES];
  int n = 0;
#endif
  while (true)
    {
      Lisp_Object nextevt
        = read_event_from_main_queue (end_time, local_getcjmp,
                                      used_mouse_menu);
#ifdef WINDOWSNT
      /* w32_console already returns decoded events.  It either reads
	 Unicode characters from the Windows keyboard input, or
	 converts characters encoded in the current codepage into
	 Unicode.  See w32inevt.c:key_event, near its end.  */
      return nextevt;
#else
      struct frame *frame = XFRAME (selected_frame);
      struct terminal *terminal = frame->terminal;
      if (!((FRAME_TERMCAP_P (frame) || FRAME_MSDOS_P (frame))
            /* Don't apply decoding if we're just reading a raw event
               (e.g. reading bytes sent by the xterm to specify the position
               of a mouse click).  */
            && (!EQ (prev_event, Qt))
	    && (TERMINAL_KEYBOARD_CODING (terminal)->common_flags
		& CODING_REQUIRE_DECODING_MASK)))
	return nextevt;		/* No decoding needed.  */
      else
	{
	  int meta_key = terminal->display_info.tty->meta_key;
	  eassert (n < MAX_ENCODED_BYTES);
	  events[n++] = nextevt;
	  if (FIXNATP (nextevt)
	      && XFIXNUM (nextevt) < (meta_key == 1 ? 0x80 : 0x100))
	    { /* An encoded byte sequence, let's try to decode it.  */
	      struct coding_system *coding
		= TERMINAL_KEYBOARD_CODING (terminal);

	      if (raw_text_coding_system_p (coding))
		{
		  int i;
		  if (meta_key != 2)
		    {
		      for (i = 0; i < n; i++)
			{
			  int c = XFIXNUM (events[i]);
			  int modifier =
			    (meta_key == 3 && c < 0x100 && (c & 0x80))
			    ? meta_modifier
			    : 0;
			  events[i] = make_fixnum ((c & ~0x80) | modifier);
			}
		    }
		}
	      else
		{
		  unsigned char src[MAX_ENCODED_BYTES];
		  unsigned char dest[MAX_ENCODED_BYTES * MAX_MULTIBYTE_LENGTH];
		  int i;
		  for (i = 0; i < n; i++)
		    src[i] = XFIXNUM (events[i]);
		  if (meta_key < 2) /* input-meta-mode is t or nil */
		    for (i = 0; i < n; i++)
		      src[i] &= ~0x80;
		  coding->destination = dest;
		  coding->dst_bytes = sizeof dest;
		  decode_coding_c_string (coding, src, n, Qnil);
		  eassert (coding->produced_char <= n);
		  if (coding->produced_char == 0)
		    { /* The encoded sequence is incomplete.  */
		      if (n < MAX_ENCODED_BYTES) /* Avoid buffer overflow.  */
			continue;		     /* Read on!  */
		    }
		  else
		    {
		      const unsigned char *p = coding->destination;
		      eassert (coding->carryover_bytes == 0);
		      n = 0;
		      while (n < coding->produced_char)
			{
			  int c = string_char_advance (&p);
			  if (meta_key == 3)
			    {
			      int modifier
				= (c < 0x100 && (c & 0x80)
				   ? meta_modifier
				   : 0);
			      c = (c & ~0x80) | modifier;
			    }
			  events[n++] = make_fixnum (c);
			}
		    }
		}
	    }
	  /* Now `events' should hold decoded events.
	     Normally, n should be equal to 1, but better not rely on it.
	     We can only return one event here, so return the first we
	     had and keep the others (if any) for later.  */
	  while (n > 1)
	    Vunread_command_events
	      = Fcons (events[--n], Vunread_command_events);
	  return events[0];
	}
#endif
    }
}

/* Read a character from the keyboard; call the redisplay if needed.  */
/* commandflag 0 means do not autosave, but do redisplay.
   -1 means do not redisplay, but do autosave.
   -2 means do neither.
   1 means do both.

   The argument MAP is a keymap for menu prompting.

   PREV_EVENT is the previous input event, or nil if we are reading
   the first event of a key sequence (or not reading a key sequence).
   If PREV_EVENT is t, that is a "magic" value that says
   not to run input methods, but in other respects to act as if
   not reading a key sequence.

   If USED_MOUSE_MENU is non-null, then set *USED_MOUSE_MENU to true
   if we used a mouse menu to read the input, or false otherwise.  If
   USED_MOUSE_MENU is null, don't dereference it.

   Value is -2 when we find input on another keyboard.  A second call
   to read_char will read it.

   If END_TIME is non-null, it is a pointer to a struct timespec
   specifying the maximum time to wait until.  If no input arrives by
   that time, stop waiting and return nil.

   Value is t if we showed a menu and the user rejected it.  */

/* Step 2-C/D: the read_char state is the Scheme <rc-state> record
   (defined in mod/emacs/read-char.scm) — single source of truth.
   Slot indices below match the record's constructor order; they're
   read/written via Guile's low-level scm_struct_ref / scm_struct_set_x
   (the srfi-9 accessors themselves are syntax-transformers and
   uncallable from C — see feedback_srfi9_accessors.md).

   Slots 3 and 4 hold the two caller-owned C pointers as Guile
   foreign-pointer SCMs (or Qnil when NULL); they round-trip through
   read_char() entry and the bulk subrs that need them.  */

enum rc_slot {
  RC_SLOT_COMMANDFLAG                 = 0,
  RC_SLOT_MAP                         = 1,
  RC_SLOT_PREV_EVENT                  = 2,
  RC_SLOT_USED_MOUSE_MENU             = 3,  /* foreign-ptr to bool, or Qnil */
  RC_SLOT_END_TIME                    = 4,  /* foreign-ptr to struct timespec, or Qnil */
  RC_SLOT_C                           = 5,
  RC_SLOT_LOCAL_TAG                   = 6,
  RC_SLOT_PREVIOUS_ECHO_AREA_MESSAGE  = 7,
  RC_SLOT_ALSO_RECORD                 = 8,
  RC_SLOT_RECORDED                    = 9,
  RC_SLOT_REREAD                      = 10,
  RC_SLOT_ORIG_KBOARD                 = 11  /* kboard SMOB */
};

/* M6 infrastructure — slot enums for <keyremap> and <rks-state>
   Scheme records, matching the srfi-9 slot order in
   mod/emacs/read-key-sequence.scm.  Used by the M6 state-machine
   migration (Steps A–F); dormant until Step B activates them.  */

/* <keyremap> record slots (srfi-9 order).  */
enum {
  KM_SLOT_PARENT  = 0,
  KM_SLOT_MAP     = 1,
  KM_SLOT_START   = 2,
  KM_SLOT_END     = 3
};

/* <rks-state> record slots (srfi-9 order).  */
enum {
  RKS_SLOT_KEY_COUNT                    = 0,
  RKS_SLOT_MOCK_INPUT                   = 1,
  RKS_SLOT_KEYBUF                       = 2,
  RKS_SLOT_KEYS_START                   = 3,
  RKS_SLOT_ECHO_START                   = 4,
  RKS_SLOT_CURRENT_BINDING              = 5,
  RKS_SLOT_FIRST_UNBOUND                = 6,
  RKS_SLOT_FKEY                         = 7,
  RKS_SLOT_KEYTRAN                      = 8,
  RKS_SLOT_INDEC                        = 9,
  RKS_SLOT_SHIFT_TRANSLATED             = 10,
  RKS_SLOT_DELAYED_SWITCH_FRAME         = 11,
  RKS_SLOT_ORIGINAL_UPPERCASE           = 12,
  RKS_SLOT_ORIGINAL_UPPERCASE_POSITION  = 13,
  RKS_SLOT_FAKE_PREFIXED_KEYS           = 14,
  RKS_SLOT_STARTING_BUFFER              = 15,
  RKS_SLOT_DISABLED_CONVERSION          = 16,
  RKS_SLOT_USED_MOUSE_MENU_HISTORY      = 17,
  RKS_SLOT_ECHO_LOCAL_START             = 18,
  RKS_SLOT_KEYS_LOCAL_START             = 19,
  RKS_SLOT_LAST_REAL_KEY_START          = 20,
  RKS_SLOT_NEW_BINDING                  = 21,
  RKS_SLOT_USED_MOUSE_MENU              = 22,
  RKS_SLOT_FIRST_EVENT                  = 23,
  RKS_SLOT_KEY                          = 24,
  RKS_SLOT_RAW_KEYBUF                   = 25,
  RKS_SLOT_RAW_KEYBUF_COUNT             = 26
};

/* Typed slot accessors.  rc_get / rc_set handle Lisp_Object; these
   add int / bool unboxing so bulk-subr entry caches don't need inline
   casts.  */

static inline int
rks_get_int (SCM rec, int slot)
{
  return XFIXNUM (scm_struct_ref (rec, scm_from_int (slot)));
}

static inline void
rks_set_int (SCM rec, int slot, int val)
{
  scm_struct_set_x (rec, scm_from_int (slot), make_fixnum (val));
}

static inline bool
rks_get_bool (SCM rec, int slot)
{
  return NILP (scm_struct_ref (rec, scm_from_int (slot))) ? false : true;
}

static inline void
rks_set_bool (SCM rec, int slot, bool val)
{
  scm_struct_set_x (rec, scm_from_int (slot), val ? Qt : Qnil);
}

/* M6 state stack.  Currently unused — rks_state_depth stays at 0
   until Step B starts pushing records.  Depth is 8, matching the
   M8 rc_record_stack budget (every read_key_sequence call chains
   through read_char, so M6 nesting ≤ M8 nesting).  */
enum { RKS_STATE_STACK_MAX = 8 };
static SCM rks_state_stack[RKS_STATE_STACK_MAX];
static int rks_state_depth;

/* LOAD_STATE_FROM_SLOTS / SAVE_STATE_TO_SLOTS are defined as no-ops
   initially.  Step B expands them to cache migrated scalars into C
   locals.  See docs/m6-plan.org §"The #define alias cost model".  */
#define LOAD_STATE_FROM_SLOTS(rec)  ((void)0)
#define SAVE_STATE_TO_SLOTS(rec)    ((void)0)

/* Phase 4: raw_keybuf writeback after any mutation.  */
#define RKS_RAW_KEYBUF_WRITEBACK do {                                   \
    if (rks_state_depth > 0) {                                          \
      SCM _rec = rks_state_stack[rks_state_depth - 1];                   \
      scm_struct_set_x (_rec, scm_from_int (RKS_SLOT_RAW_KEYBUF),       \
                        raw_keybuf);                                     \
      rks_set_int (_rec, RKS_SLOT_RAW_KEYBUF_COUNT, raw_keybuf_count);  \
    }                                                                   \
  } while (0)

/* C-9b: load/store helpers defined after the keyremap typedef
   (see line ~10441).  RKS_KEYREMAP_WRITEBACK macro retired with the
   file-static structs.  */

enum { RC_STATE_STACK_MAX = 8 };
static SCM rc_record_stack[RC_STATE_STACK_MAX];
static int rc_state_depth;

static inline Lisp_Object
rc_get (SCM rec, int slot)
{
  return scm_struct_ref (rec, scm_from_int (slot));
}

static inline void
rc_set (SCM rec, int slot, Lisp_Object val)
{
  scm_struct_set_x (rec, scm_from_int (slot), val);
}

/* Wrap a C pointer as a Guile foreign-pointer SCM (or Qnil for NULL).  */
static inline SCM
rc_wrap_ptr (void *p)
{
  return p ? scm_from_pointer (p, NULL) : Qnil;
}

/* Unwrap a foreign-pointer SCM slot back to a C pointer (NULL when nil).  */
static inline void *
rc_unwrap_ptr (SCM rec, int slot)
{
  SCM s = rc_get (rec, slot);
  return NILP (s) ? NULL : scm_to_pointer (s);
}

/* Step 2-B removed the per-field accessor DEFUNs (--rc-c, etc.) —
   tests now go through --rc-record + struct-ref.
   Step 2-C collapsed `struct read_char_state' into the <rc-state>
   record itself; bulk subrs reach state via rc_record_stack +
   rc_get / rc_set.  Step 2-D folded the caller-owned C pointers
   (used_mouse_menu, end_time) into record slots 3 and 4 as
   foreign-pointer SCMs, eliminating the rc_ptr_stack companion.
   See docs/keyboard.org §M8 closeout.  */

DEFUN ("--rc-record", Fc_rc_record, Sc_rc_record, 0, 0, 0,
       doc: /* Internal: return the <rc-state> Scheme record for the
top-of-stack read_char invocation, or nil when no read_char is in
flight.  The record is allocated and pushed by read_char() at entry.
*/)
  (void)
{
  if (rc_state_depth == 0)
    return Qnil;
  return rc_record_stack[rc_state_depth - 1];
}

/* M8final — tiny C shim for the Scheme-owned read_char_1 exit tail.
   The resolved event lives in the <rc-state> record and is returned
   by (emacs read-char) rc-exit!.  C only owns the input_pending /
   input_was_pending globals, so expose the latch as a small primitive.  */
DEFUN ("--rc-latch-input-was-pending",
       Fc_rc_latch_input_was_pending,
       Sc_rc_latch_input_was_pending, 0, 0, 0,
       doc: /* Internal: set input_was_pending = input_pending.
Returns nil.  Used by Scheme rc-exit!.  */)
  (void)
{
  input_was_pending = input_pending;
  return Qnil;
}

/* M8n — tiny C shims for the Scheme-owned help-echo / command-keys
   / help-form epilogue.  Scheme owns the 3-block control flow, the
   last-input-event update, and the block-2 add-command-key / echo
   sequence.  C still owns show_help_echo, the mouse-movement event
   predicate, the ok_to_echo_at_next_pause global write, the
   num_input_events counter, and the Block 3 recursive read_char loop
   with its dynwind / help-form-saved-window-configs machinery.  */

DEFUN ("--rc-show-help-echo",
       Fc_rc_show_help_echo,
       Sc_rc_show_help_echo, 4, 4, 0,
       doc: /* Internal: thin wrapper around C show_help_echo.
HELP is the help string, WINDOW the window, OBJECT the object,
POSITION the position within the help.  Used by Scheme
rc-help-echo-and-help-form! after destructuring the
(help-echo FRAME HELP WINDOW OBJECT POS) event cons.  */)
  (Lisp_Object help, Lisp_Object window,
   Lisp_Object object, Lisp_Object position)
{
  show_help_echo (help, window, object, position);
  return Qnil;
}

DEFUN ("--rc-mouse-movement-event-p",
       Fc_rc_mouse_movement_event_p,
       Sc_rc_mouse_movement_event_p, 1, 1, 0,
       doc: /* Internal: t if C is a mouse-motion event.  Used by
Scheme rc-add-command-keys-and-echo! to keep the C event-kind
predicate narrow while Scheme owns M8n Block 2 sequencing.  */)
  (Lisp_Object c)
{
  return (EVENT_HAS_PARAMETERS (c)
          && EQ (EVENT_HEAD_KIND (EVENT_HEAD (c)), Qmouse_movement))
    ? Qt : Qnil;
}

DEFUN ("--rc-allow-echo-at-next-pause",
       Fc_rc_allow_echo_at_next_pause,
       Sc_rc_allow_echo_at_next_pause, 0, 0, 0,
       doc: /* Internal: set ok_to_echo_at_next_pause = current_kboard.
Used by Scheme rc-add-command-keys-and-echo! when the event is not
mouse motion.  */)
  (void)
{
  ok_to_echo_at_next_pause = current_kboard;

  return Qnil;
}

DEFUN ("--rc-inc-num-input-events",
       Fc_rc_inc_num_input_events,
       Sc_rc_inc_num_input_events, 0, 0, 0,
       doc: /* Internal: ++num_input_events.  Used by Scheme
rc-help-echo-and-help-form! to mirror the M8n tail counter
increment.  */)
  (void)
{
  num_input_events++;
  return Qnil;
}

DEFUN ("--rc-maybe-help-form-recursive-read",
       Fc_rc_maybe_help_form_recursive_read,
       Sc_rc_maybe_help_form_recursive_read, 0, 0, 0,
       doc: /* Internal: Block 3 of M8n.  When Vhelp_form is set and
the top-of-stack rec's c is the help char, push the current
window-configuration onto help_form_saved_window_configs (with an
unwind-protect to read_char_help_form_unwind), show the help form
via Qhelp_form_show, then loop read_char until a non-BUFFERP event
is returned.  If the user typed SPACE, repeat the loop once more
to dismiss.  Writes the final event back to rec.c.  Returns nil.  */)
  (void)
{
  if (rc_state_depth == 0)
    return Qnil;
  SCM rec = rc_record_stack[rc_state_depth - 1];
  Lisp_Object c = rc_get (rec, RC_SLOT_C);

  if (NILP (Vhelp_form) || !help_char_p (c))
    return Qnil;

  dynwind_begin ();

  help_form_saved_window_configs
    = Fcons (Fcurrent_window_configuration (Qnil),
             help_form_saved_window_configs);
  record_unwind_protect_void (read_char_help_form_unwind);
  call0 (Qhelp_form_show);

  cancel_echoing ();
  do
    {
      c = read_char (0, Qnil, Qnil, 0, NULL);
      if (EVENT_HAS_PARAMETERS (c)
          && EQ (EVENT_HEAD_KIND (EVENT_HEAD (c)), Qmouse_click))
        XSETCAR (help_form_saved_window_configs, Qnil);
    }
  while (BUFFERP (c));
  /* Remove the help from the frame.  */
  dynwind_end ();

  redisplay ();
  if (BASE_EQ (c, make_fixnum (040)))
    {
      cancel_echoing ();
      do
        c = read_char (0, Qnil, Qnil, 0, NULL);
      while (BUFFERP (c));
    }
  /* Write back the final c value to the record.  */
  rc_set (rec, RC_SLOT_C, c);
  return Qnil;
}

/* M8m — tiny C shim for the Scheme-owned input-method dispatch.
   Scheme owns the Block 1 gate (FIXNUMP/printable-ASCII + range +
   Vinput_method_function + prev-event-nil) and the trivial Block 2
   record-if-unread tail; the body of Block 1 — the save/restore-
   around-call1 transaction including the dynwind/specbind — stays
   atomic in C.  */

DEFUN ("--rc-input-method-call-and-handle",
       Fc_rc_input_method_call_and_handle,
       Sc_rc_input_method_call_and_handle, 0, 0, 0,
       doc: /* Internal: Block 1 of M8m.  Save echo + this_command_keys
state, dynwind-begin, optionally specbind input-method-use-echo-area
when not reading a key sequence, call1(Vinput_method_function, state->c),
dynwind-end, restore.  On no events, restore the previous-echo-area-
message and return `goto-retry'.  On events, install XCAR(tem) into
state->c, nconc XCDR(tem) onto Vunread_post_input_method_events and
return nil.  Caller has already verified the Block 1 gate.  */)
  (void)
{
  if (rc_state_depth == 0)
    return Qnil;
  SCM rec = rc_record_stack[rc_state_depth - 1];
  Lisp_Object c = rc_get (rec, RC_SLOT_C);

  Lisp_Object keys;
  ptrdiff_t key_count;
  ptrdiff_t command_key_start;

  /* Save the echo status.  */
  bool saved_immediate_echo = current_kboard->immediate_echo;
  struct kboard *saved_ok_to_echo = ok_to_echo_at_next_pause;
  Lisp_Object saved_echo_string = KVAR (current_kboard, echo_string);
  Lisp_Object saved_echo_prompt = KVAR (current_kboard, echo_prompt);

  dynwind_begin ();
  /* Save the this_command_keys status.  */
  key_count = this_command_key_count;
  command_key_start = XFIXNUM (Fc_this_single_command_key_start ());

  if (key_count > 0)
    keys = Fcopy_sequence (this_command_keys);
  else
    keys = Qnil;

  /* Clear out this_command_keys.  */
  this_command_key_count = 0;
  Fc_set_this_single_command_key_start (make_fixnum (0));

  /* Now wipe the echo area.  */
  if (!NILP (echo_area_buffer[0]))
    safe_run_hooks (Qecho_area_clear_hook);
  clear_message (1, 0);
  echo_truncate (0);

  /* If we are not reading a key sequence,
     never use the echo area.  */
  if (!KEYMAPP (rc_get (rec, RC_SLOT_MAP)))
    specbind_guile (Qinput_method_use_echo_area, Qt);

  /* Call the input method.  */
  Lisp_Object tem = call1 (Vinput_method_function, c);

  dynwind_end ();

  /* Restore the saved echoing state
     and this_command_keys state.  */
  this_command_key_count = key_count;
  Fc_set_this_single_command_key_start (make_fixnum (command_key_start));
  if (key_count > 0)
    this_command_keys = keys;

  cancel_echoing ();
  ok_to_echo_at_next_pause = saved_ok_to_echo;
  kset_echo_string (current_kboard, saved_echo_string);
  kset_echo_prompt (current_kboard, saved_echo_prompt);
  if (saved_immediate_echo)
    echo_now ();

  /* The input method can return no events.  */
  if (!CONSP (tem))
    {
      /* Bring back the previous message, if any.  */
      Lisp_Object prev_msg = rc_get (rec, RC_SLOT_PREVIOUS_ECHO_AREA_MESSAGE);
      if (!NILP (prev_msg))
        message_with_string ("%s", prev_msg, 0);
      return intern ("goto-retry");
    }
  /* It returned one event or more.  */
  c = XCAR (tem);
  rc_set (rec, RC_SLOT_C, c);
  Vunread_post_input_method_events
    = nconc2 (XCDR (tem), Vunread_post_input_method_events);
  return Qnil;
}

/* M8l — tiny C shims for the Scheme-owned translate + menu-bar +
   record + echo-wipe block.  Scheme orchestrates the 3 blocks; C
   owns the menu-bar event POSN_SET_POSN rewrite, the C record_char
   path, and the echo-area / mini-window cleanup primitives.
   The keyboard-translate-table lookup is now fully in Scheme
   (rc-translate-kbd-table).  */

DEFUN ("--rc-record-char",
       Fc_rc_record_char,
       Sc_rc_record_char, 1, 1, 0,
       doc: /* Internal: call C record_char(C).  Used by Scheme
rc-event-translate-and-record! and rc-input-method-dispatch!.  */)
  (Lisp_Object c)
{
  record_char (c);
  return Qnil;
}

DEFUN ("--rc-echo-area-wipe",
       Fc_rc_echo_area_wipe,
       Sc_rc_echo_area_wipe, 0, 0, 0,
       doc: /* Internal: Block 3c of M8l.  When the echo area has
content, run Qecho_area_clear_hook + clear_message(1,0) and resize
the mini-window if it was overlapping; otherwise call
clear_message(1,0) when Vclear_message_function is a function.
Used by Scheme rc-event-translate-and-record!.  */)
  (void)
{
  if (!NILP (echo_area_buffer[0]))
    {
      safe_run_hooks (Qecho_area_clear_hook);
      clear_message (1, 0);
      /* If we were showing the echo-area message on top of an
         active minibuffer, resize the mini-window.  */
      if (minibuf_level
          && EQ (minibuf_window, echo_area_window)
          && !NUMBERP (Vminibuffer_message_timeout))
        resize_mini_window (XWINDOW (minibuf_window), false);
    }
  else if (FUNCTIONP (Vclear_message_function))
    clear_message (1, 0);
  return Qnil;
}

/* M8k — tiny C shims for the Scheme-owned BUFFERP + special-event-map
   dispatch.  Scheme owns the control flow and the last-input-event /
   command-execute call; C still owns the exact access_keymap +
   get_keymap composition (and its quit-flag save/restore wrapper)
   plus timer_resume_idle.  */

DEFUN ("--rc-special-event-map-lookup",
       Fc_rc_special_event_map_lookup,
       Sc_rc_special_event_map_lookup, 1, 1, 0,
       doc: /* Internal: look up C in Vspecial_event_map with
Vquit_flag saved-cleared-restored around the lookup.  Returns the
binding (or nil if none).  Used by Scheme rc-bufferp-and-special-event-map!
Block 2.  */)
  (Lisp_Object c)
{
  Lisp_Object save = Vquit_flag;
  Vquit_flag = Qnil;
  Lisp_Object tem = access_keymap (get_keymap (Vspecial_event_map, 0, 1),
                                   c, 0, 0, 1);
  Vquit_flag = save;
  return tem;
}

DEFUN ("--rc-timer-resume-idle",
       Fc_rc_timer_resume_idle,
       Sc_rc_timer_resume_idle, 0, 0, 0,
       doc: /* Internal: call C timer_resume_idle().  Used by Scheme
rc-bufferp-and-special-event-map! to undo the idle-timer stop for
while-no-input-ignore events.  */)
  (void)
{
  timer_resume_idle ();
  return Qnil;
}

/* M8j — tiny C shims for the Scheme-owned blocking-read + non-reread
   loop.  Scheme owns the iteration and the timer-stop / c-is-nil
   gates; C still owns the blocking read_decoded_event_from_main_queue.  */

DEFUN ("--rc-read-decoded-event-from-main-queue",
       Fc_rc_read_decoded_event_from_main_queue,
       Sc_rc_read_decoded_event_from_main_queue, 0, 0, 0,
       doc: /* Internal: call read_decoded_event_from_main_queue
using the top-of-stack rec's end-time / local-tag / prev-event /
used-mouse-menu slots.  Returns the raw event; Scheme owns the
timeout / -2 / Qt / Qno_record postprocessing.  */)
  (void)
{
  if (rc_state_depth == 0)
    return Qnil;
  SCM rec = rc_record_stack[rc_state_depth - 1];
  struct timespec *end_time = rc_unwrap_ptr (rec, RC_SLOT_END_TIME);
  bool *used_mouse_menu = rc_unwrap_ptr (rec, RC_SLOT_USED_MOUSE_MENU);

  return read_decoded_event_from_main_queue (end_time,
                                             rc_get (rec, RC_SLOT_LOCAL_TAG),
                                             rc_get (rec, RC_SLOT_PREV_EVENT),
                                             used_mouse_menu);
}

DEFUN ("--rc-end-time-expired-p",
       Fc_rc_end_time_expired_p,
       Sc_rc_end_time_expired_p, 0, 0, 0,
       doc: /* Internal: t if the top-of-stack rec has a non-null
end-time pointer and that deadline is <= current_timespec ().
Used by Scheme rc-read-and-install-event!.  */)
  (void)
{
  if (rc_state_depth == 0)
    return Qnil;
  SCM rec = rc_record_stack[rc_state_depth - 1];
  struct timespec *end_time = rc_unwrap_ptr (rec, RC_SLOT_END_TIME);

  return (end_time && timespec_cmp (*end_time, current_timespec ()) <= 0)
    ? Qt : Qnil;
}

/* M8i — bulk splice of the four post-M8h blocks: wrong-kboard
   detection, Vunread_command_events drain, current-kboard side
   queue read, and other-kboard scan.  See docs/keyboard.org §M8i.  */
/* M8i — tiny C shims for the Scheme-owned 4-block kboard / queue
   prologue.  Scheme handles Block 1 (wrong-kboard detection via
   the existing kboard-eq / current-kboard primitives) and Block 2
   (Lisp-level Vunread_command_events drain).  C still owns the
   KBOARD struct internals for Block 3 (current kboard's side
   queue) and Block 4 (scan all_kboards).  */

DEFUN ("--rc-pop-current-kboard-queue",
       Fc_rc_pop_current_kboard_queue,
       Sc_rc_pop_current_kboard_queue, 0, 0, 0,
       doc: /* Internal: Block 3 of M8i.  When the current KBOARD has
queued input, dequeue the head event and return it (also updates
input_pending, internal_last_event_frame for switch-frame events,
and clears kbd_queue_has_data when the queue empties).  Returns
nil if no data was available.  Used by Scheme
rc-prologue-kboard-and-queues!.  */)
  (void)
{
  if (!current_kboard->kbd_queue_has_data)
    return Qnil;
  if (!CONSP (KVAR (current_kboard, kbd_queue)))
    emacs_abort ();
  Lisp_Object c0 = XCAR (KVAR (current_kboard, kbd_queue));
  kset_kbd_queue (current_kboard,
                  XCDR (KVAR (current_kboard, kbd_queue)));
  if (NILP (KVAR (current_kboard, kbd_queue)))
    current_kboard->kbd_queue_has_data = false;
  input_pending = readable_events (0);
  if (EVENT_HAS_PARAMETERS (c0)
      && EQ (EVENT_HEAD_KIND (EVENT_HEAD (c0)), Qswitch_frame))
    internal_last_event_frame = XCAR (XCDR (c0));
  Vlast_event_frame = internal_last_event_frame;
  return c0;
}

DEFUN ("--rc-find-other-kboard-with-data",
       Fc_rc_find_other_kboard_with_data,
       Sc_rc_find_other_kboard_with_data, 0, 0, 0,
       doc: /* Internal: Block 4 of M8i.  When not in single_kboard
mode, scan all_kboards for one with queued data; if found, switch
current_kboard to it and return t.  Returns nil otherwise.  Used by
Scheme rc-prologue-kboard-and-queues! to detect when a wrong-kboard
exit is needed.  */)
  (void)
{
  if (single_kboard)
    return Qnil;
  for (KBOARD *kb = all_kboards; kb; kb = kb->next_kboard)
    if (kb->kbd_queue_has_data)
      {
        current_kboard = kb;
        return Qt;
      }
  return Qnil;
}

/* M8h — tiny C shims for the Scheme-owned X-menu / auto-save-by-
   timeout / GC-on-idle prologue.  Scheme owns the per-block gate
   logic and dispatch; C still owns the read_char_x_menu_prompt
   helper, the idle-timer machinery, and the buffer-size-scaled
   auto-save / GC block which is dense C-internal arithmetic.  */

DEFUN ("--rc-read-char-x-menu-prompt",
       Fc_rc_read_char_x_menu_prompt,
       Sc_rc_read_char_x_menu_prompt, 0, 0, 0,
       doc: /* Internal: call C read_char_x_menu_prompt with the
top-of-stack rec's map / prev-event / used-mouse-menu slots.
Returns the resulting event.  Used by Scheme rc-prologue-xmenu-and-idle-gc!
Block 1.  */)
  (void)
{
  if (rc_state_depth == 0)
    return Qnil;
  SCM rec = rc_record_stack[rc_state_depth - 1];
  bool *used_mouse_menu = rc_unwrap_ptr (rec, RC_SLOT_USED_MOUSE_MENU);
  Lisp_Object map = rc_get (rec, RC_SLOT_MAP);
  Lisp_Object prev_event = rc_get (rec, RC_SLOT_PREV_EVENT);
  return read_char_x_menu_prompt (map, prev_event, used_mouse_menu);
}

DEFUN ("--rc-timer-stop-idle",
       Fc_rc_timer_stop_idle,
       Sc_rc_timer_stop_idle, 0, 0, 0,
       doc: /* Internal: call C timer_stop_idle().  Used by Scheme
rc-prologue-xmenu-and-idle-gc! and rc-wrong-kboard-and-non-reread.  */)
  (void)
{
  timer_stop_idle ();
  return Qnil;
}

DEFUN ("--rc-refresh-last-non-minibuf-size",
       Fc_rc_refresh_last_non_minibuf_size,
       Sc_rc_refresh_last_non_minibuf_size, 0, 0, 0,
       doc: /* Internal: update the file-static `last_non_minibuf_size'
from Z - BEG of the current buffer when the selected window is not a
minibuffer, and return the new value as a fixnum.  Used by Scheme
rc-auto-save-delay-level.  */)
  (void)
{
  if (! MINI_WINDOW_P (XWINDOW (selected_window)))
    last_non_minibuf_size = Z - BEG;
  return make_int (last_non_minibuf_size);
}

DEFUN ("--rc-sit-for-timeout",
       Fc_rc_sit_for_timeout, Sc_rc_sit_for_timeout, 1, 1, 0,
       doc: /* Internal: sit_for (TIMEOUT, 1, 1) — pause display
for TIMEOUT seconds, returning t when no input arrived.  Used by
Scheme rc-auto-save-by-timeout-and-gc! for the auto-save delay
wait.  */)
  (Lisp_Object timeout)
{
  return sit_for (timeout, 1, 1);
}

DEFUN ("--rc-gc-collect-a-little",
       Fc_rc_gc_collect_a_little,
       Sc_rc_gc_collect_a_little, 0, 0, 0,
       doc: /* Internal: GC_collect_a_little ().  Used by Scheme
rc-auto-save-by-timeout-and-gc! when no input is pending.  */)
  (void)
{
  GC_collect_a_little ();
  return Qnil;
}

/* M8g — tiny C shims for the Scheme-owned idle/echo/auto-save
   prologue.  Scheme orchestrates the 3 sequential blocks; C owns
   the timer / echo / auto-save primitives.  */

DEFUN ("--rc-timer-start-idle",
       Fc_rc_timer_start_idle,
       Sc_rc_timer_start_idle, 0, 0, 0,
       doc: /* Internal: call C timer_start_idle().  Used by Scheme
rc-prologue-idle-echo-autosave! for Block 1.  */)
  (void)
{
  timer_start_idle ();
  return Qnil;
}

DEFUN ("--rc-echo-area-usable-for-echo-p",
       Fc_rc_echo_area_usable_for_echo_p,
       Sc_rc_echo_area_usable_for_echo_p, 0, 0, 0,
       doc: /* Internal: t when the echo area is in a usable state
for showing keystrokes — either echo_area_buffer[0] is nil, the
buffer is empty (BEG == Z), or ok_to_echo_at_next_pause matches
the appropriate echo_kboard.  Used by Scheme
rc-should-immediate-echo-p.  */)
  (void)
{
  bool ok = (NILP (echo_area_buffer[0])
             || (BUF_BEG (XBUFFER (echo_area_buffer[0]))
                 == BUF_Z (XBUFFER (echo_area_buffer[0])))
             || (echo_kboard
                 && ok_to_echo_at_next_pause == echo_kboard)
             || (!echo_kboard
                 && ok_to_echo_at_next_pause));
  return ok ? Qt : Qnil;
}

DEFUN ("--rc-sit-for-echo-keystrokes",
       Fc_rc_sit_for_echo_keystrokes,
       Sc_rc_sit_for_echo_keystrokes, 0, 0, 0,
       doc: /* Internal: save getctag, sit_for `echo-keystrokes' seconds
with display + input flags, restore getctag.  Returns sit_for's
result (t when no input arrived).  Used by Scheme
rc-prologue-idle-echo-autosave! Block 2's non-mouse path; the
caller decides whether to echo_now based on the result.  The
save/restore stays atomic in C so a non-local exit through sit_for
can't leak the getctag clobber back to the caller.  */)
  (void)
{
  Lisp_Object save_tag = getctag;
  Lisp_Object tem0 = sit_for (Vecho_keystrokes, 1, 1);
  getctag = save_tag;
  return tem0;
}

DEFUN ("--rc-last-auto-save",
       Fc_rc_last_auto_save, Sc_rc_last_auto_save, 0, 0, 0,
       doc: /* Internal: read the file-static last_auto_save counter
(the value of num_nonmacro_input_events at the previous auto-save).
The lisp-side `auto-save-interval' and `num-nonmacro-input-events'
are already DEFVAR_INT and reachable via symbol-value, so this is
the only C-private piece M8g Block 3 needs from Scheme.  */)
  (void)
{
  return make_int (last_auto_save);
}

/* M8f — tiny C shims for the Scheme-owned echo/menu prologue.
   Scheme owns the control flow; C still owns the echo globals and
   the file-static read_char_minibuf_menu_prompt helper.  */

DEFUN ("--rc-echo-area-has-wrong-kboard-p",
       Fc_rc_echo_area_has_wrong_kboard_p,
       Sc_rc_echo_area_has_wrong_kboard_p, 0, 0, 0,
       doc: /* Internal: t when the echo area is showing a message
from a different kboard or when ok_to_echo_at_next_pause is NULL.
Used by Scheme rc-echo-cancel-or-dash.  */)
  (void)
{
  bool wrong = (!NILP (echo_area_buffer[0])
                && (echo_kboard != current_kboard
                    || ok_to_echo_at_next_pause == NULL));
  return wrong ? Qt : Qnil;
}

DEFUN ("--rc-read-char-minibuf-menu-prompt",
       Fc_rc_read_char_minibuf_menu_prompt,
       Sc_rc_read_char_minibuf_menu_prompt, 2, 2, 0,
       doc: /* Internal: call read_char_minibuf_menu_prompt.
COMMANDFLAG must be a fixnum.  MAP is the keymap candidate.
Used by Scheme rc-prologue-echo-and-menu!.  */)
  (Lisp_Object commandflag, Lisp_Object map)
{
  CHECK_FIXNUM (commandflag);
  return read_char_minibuf_menu_prompt (XFIXNUM (commandflag), map);
}

DEFUN ("--rc-detect-input-pending-run-timers",
       Fc_rc_detect_input_pending_run_timers,
       Sc_rc_detect_input_pending_run_timers, 0, 0, 0,
       doc: /* Internal: t if detect_input_pending_run_timers (0).
Used by Scheme rc-prologue-echo-and-menu!.  */)
  (void)
{
  return detect_input_pending_run_timers (0) ? Qt : Qnil;
}

/* M8e — tiny C shims for the Scheme-owned redisplay-loop prologue.
   Scheme owns the commandflag guard and the echo-buffer bookkeeping;
   C still owns the input_pending / input_was_pending / echo_message_buffer
   globals plus the redisplay machinery.  */

DEFUN ("--rc-echo-message-buffer-is-current",
       Fc_rc_echo_message_buffer_is_current,
       Sc_rc_echo_message_buffer_is_current, 0, 0, 0,
       doc: /* Internal: t if echo_message_buffer EQ echo_area_buffer[0].
Used by Scheme rc-prologue-redisplay! to snapshot the echo state
before the redisplay loop.  */)
  (void)
{
  return EQ (echo_message_buffer, echo_area_buffer[0]) ? Qt : Qnil;
}

DEFUN ("--rc-pin-echo-message-buffer-to-current",
       Fc_rc_pin_echo_message_buffer_to_current,
       Sc_rc_pin_echo_message_buffer_to_current, 0, 0, 0,
       doc: /* Internal: set echo_message_buffer = echo_area_buffer[0].
Used by Scheme rc-prologue-redisplay! after the redisplay loop, to
prevent the just-done redisplay from messing up echoing of the
input after the prompt.  */)
  (void)
{
  echo_message_buffer = echo_area_buffer[0];
  return Qnil;
}

DEFUN ("--rc-input-pending",
       Fc_rc_input_pending, Sc_rc_input_pending, 0, 0, 0,
       doc: /* Internal: t if input_pending is set.
Used by Scheme rc-redisplay-and-wait-block!.  */)
  (void)
{
  return input_pending ? Qt : Qnil;
}

DEFUN ("--rc-input-was-pending",
       Fc_rc_input_was_pending, Sc_rc_input_was_pending, 0, 0, 0,
       doc: /* Internal: t if input_was_pending is set.
Used by Scheme rc-redisplay-and-wait-block!.  */)
  (void)
{
  return input_was_pending ? Qt : Qnil;
}

DEFUN ("--rc-swallow-events",
       Fc_rc_swallow_events, Sc_rc_swallow_events, 0, 0, 0,
       doc: /* Internal: call swallow_events (false).
Used by Scheme rc-redisplay-and-wait-block!.  */)
  (void)
{
  swallow_events (false);
  return Qnil;
}

DEFUN ("--rc-help-echo-redisplay-preserve-p",
       Fc_rc_help_echo_redisplay_preserve_p,
       Sc_rc_help_echo_redisplay_preserve_p, 0, 0, 0,
       doc: /* Internal: t when help echo should preserve the echo area
during the read_char redisplay loop.  */)
  (void)
{
  return (help_echo_showing_p && !BASE_EQ (selected_window, minibuf_window))
    ? Qt : Qnil;
}

DEFUN ("--rc-redisplay-preserve-echo-area",
       Fc_rc_redisplay_preserve_echo_area,
       Sc_rc_redisplay_preserve_echo_area, 0, 0, 0,
       doc: /* Internal: call redisplay_preserve_echo_area (5).
Used by Scheme rc-redisplay-and-wait-block!.  */)
  (void)
{
  redisplay_preserve_echo_area (5);
  return Qnil;
}

DEFUN ("--rc-redisplay",
       Fc_rc_redisplay, Sc_rc_redisplay, 0, 0, 0,
       doc: /* Internal: call redisplay ().
Used by Scheme rc-redisplay-and-wait-block!.  */)
  (void)
{
  redisplay ();
  return Qnil;
}

/* M8d — kbd-macro + unread-switch-frame early-exits.  Body lives
   in (emacs read-char) since 2026-05-29; the two tiny shims below
   give Scheme write-access to the C-side state internal_last_event_frame
   and the file-static unread_switch_frame.  See docs/keyboard.org §M8d.  */

DEFUN ("--rc-pin-event-frame-to-macro",
       Fc_rc_pin_event_frame_to_macro,
       Sc_rc_pin_event_frame_to_macro, 0, 0, 0,
       doc: /* Internal: pin both Vlast_event_frame and the C-side
internal_last_event_frame to Qmacro.  Used by the Scheme M8d body
when replaying an in-progress keyboard macro — events read from a
macro must never cause a new frame to be selected.  */)
  (void)
{
  Vlast_event_frame = internal_last_event_frame = Qmacro;
  return Qnil;
}

DEFUN ("--rc-take-unread-switch-frame",
       Fc_rc_take_unread_switch_frame,
       Sc_rc_take_unread_switch_frame, 0, 0, 0,
       doc: /* Internal: read-and-clear the file-static
unread_switch_frame.  Returns its previous value (nil if it was
already nil).  Used by the Scheme M8d body.  */)
  (void)
{
  Lisp_Object v = unread_switch_frame;
  unread_switch_frame = Qnil;
  return v;
}

/* Tiny shims that let the Scheme `read-char-entry' driver manage
   the rc_record_stack from inside its `call-with-prompt' thunk.  */

DEFUN ("--rc-record-stack-push", Fc_rc_record_stack_push,
       Sc_rc_record_stack_push, 1, 1, 0,
       doc: /* Internal: push REC onto rc_record_stack.  */)
  (Lisp_Object rec)
{
  eassert (rc_state_depth < RC_STATE_STACK_MAX);
  rc_record_stack[rc_state_depth++] = rec;
  return Qnil;
}

DEFUN ("--rc-mark-used-mouse-menu-true",
       Fc_rc_mark_used_mouse_menu_true,
       Sc_rc_mark_used_mouse_menu_true, 1, 1, 0,
       doc: /* Internal: write through the caller-owned bool*
in REC's used-mouse-menu slot (foreign-pointer), setting *p = true.
No-op if the slot is nil.  Used by the Scheme M8c body where elisp
record accessors can't deref the foreign pointer directly.  */)
  (Lisp_Object rec)
{
  bool *p = rc_unwrap_ptr (rec, RC_SLOT_USED_MOUSE_MENU);
  if (p)
    *p = true;
  return Qnil;
}

DEFUN ("--rc-record-stack-pop", Fc_rc_record_stack_pop,
       Sc_rc_record_stack_pop, 0, 0, 0,
       doc: /* Internal: pop the top of rc_record_stack.  */)
  (void)
{
  if (rc_state_depth > 0)
    rc_record_stack[--rc_state_depth] = SCM_UNDEFINED;
  return Qnil;
}

/* M6 state-stack push/pop (Step A infrastructure, dormant until
   Step B activates the stack).  Mirrors the rc_record_stack pattern.  */

DEFUN ("--rks-state-stack-push", Fc_rks_state_stack_push,
       Sc_rks_state_stack_push, 1, 1, 0,
       doc: /* Internal: push an <rks-state> Scheme record onto
rks_state_stack.  See docs/m6-plan.org Step A.  */)
  (Lisp_Object rec)
{
  eassert (rks_state_depth < RKS_STATE_STACK_MAX);
  rks_state_stack[rks_state_depth++] = rec;
  return Qnil;
}

DEFUN ("--rks-state-stack-pop", Fc_rks_state_stack_pop,
       Sc_rks_state_stack_pop, 0, 0, 0,
       doc: /* Internal: pop the top of rks_state_stack.  */)
  (void)
{
  if (rks_state_depth > 0)
    rks_state_stack[--rks_state_depth] = SCM_UNDEFINED;
  return Qnil;
}

DEFUN ("--rks-record-set-int", Fc_rks_record_set_int,
       Sc_rks_record_set_int, 3, 3, 0,
       doc: /* Internal: write fixnum VAL to slot SLOT of the
<rks-state> record REC.  */)
  (Lisp_Object rec, Lisp_Object slot, Lisp_Object val)
{
  CHECK_FIXNUM (slot);
  CHECK_FIXNUM (val);
  rks_set_int (rec, XFIXNUM (slot), XFIXNUM (val));
  return Qnil;
}

DEFUN ("--rks-record-set-bool", Fc_rks_record_set_bool,
       Sc_rks_record_set_bool, 3, 3, 0,
       doc: /* Internal: write bool VAL (non-nil = true) to slot SLOT
of the <rks-state> record REC.  */)
  (Lisp_Object rec, Lisp_Object slot, Lisp_Object val)
{
  CHECK_FIXNUM (slot);
  rks_set_bool (rec, XFIXNUM (slot), !NILP (val));
  return Qnil;
}

DEFUN ("--rks-record-get-int", Fc_rks_record_get_int,
       Sc_rks_record_get_int, 2, 2, 0,
       doc: /* Internal: read fixnum from slot SLOT of the
<rks-state> record REC.  */)
  (Lisp_Object rec, Lisp_Object slot)
{
  CHECK_FIXNUM (slot);
  return make_fixnum (rks_get_int (rec, XFIXNUM (slot)));
}

DEFUN ("--rks-record-get", Fc_rks_record_get,
       Sc_rks_record_get, 2, 2, 0,
       doc: /* Internal: read any Lisp_Object from slot SLOT of the
<rks-state> record REC.  */)
  (Lisp_Object rec, Lisp_Object slot)
{
  CHECK_FIXNUM (slot);
  return scm_struct_ref (rec, scm_from_int (XFIXNUM (slot)));
}

DEFUN ("--rks-record-set", Fc_rks_record_set,
       Sc_rks_record_set, 3, 3, 0,
       doc: /* Internal: write any Lisp_Object VAL to slot SLOT of
the <rks-state> record REC.  */)
  (Lisp_Object rec, Lisp_Object slot, Lisp_Object val)
{
  CHECK_FIXNUM (slot);
  scm_struct_set_x (rec, scm_from_int (XFIXNUM (slot)), val);
  return Qnil;
}

DEFUN ("--rks-keyremap-get-int",
       Fc_rks_keyremap_get_int,
       Sc_rks_keyremap_get_int, 2, 2, 0,
       doc: /* Internal: read fixnum from slot SLOT of a <keyremap>
record KM (e.g. start, end).  */)
  (Lisp_Object km, Lisp_Object slot)
{
  CHECK_FIXNUM (slot);
  return make_fixnum (rks_get_int (km, XFIXNUM (slot)));
}

DEFUN ("--rks-keyremap-set-int",
       Fc_rks_keyremap_set_int,
       Sc_rks_keyremap_set_int, 3, 3, 0,
       doc: /* Internal: write fixnum VAL to slot SLOT of the
<keyremap> record KM.  */)
  (Lisp_Object km, Lisp_Object slot, Lisp_Object val)
{
  CHECK_FIXNUM (slot);
  CHECK_FIXNUM (val);
  scm_struct_set_x (km, scm_from_int (XFIXNUM (slot)),
                    make_fixnum (XFIXNUM (val)));
  return Qnil;
}

DEFUN ("--rks-state-current", Fc_rks_state_current,
       Sc_rks_state_current, 0, 0, 0,
       doc: /* Internal: return the top <rks-state> on the stack,
or nil when no read_key_sequence is in flight.  */)
  (void)
{
  if (rks_state_depth == 0)
    return Qnil;
  return rks_state_stack[rks_state_depth - 1];
}

/* C-side preamble of the read_char quit handler: stash quit_char in
   the record's c slot, latch the event frame, clear the quit flag,
   and requeue to a different kboard if focus has moved.  Returns
   nil if the caller should re-enter read-char-main with jump=#t,
   or fixnum -2 if the kboard switched (caller returns that).  */
DEFUN ("--read-char-handle-quit-preamble",
       Fc_read_char_handle_quit_preamble,
       Sc_read_char_handle_quit_preamble, 1, 1, 0,
       doc: /* Internal helper for Scheme `read-char-entry'.  See
docs/keyboard.org §read_char hoist.  */)
  (Lisp_Object rec)
{
  /* Quit clears the prompt-tag context (the original C did this
     via `getctag = state->save_tag' where save_tag was always
     Qnil — the save-step was lost in an earlier adaptation).  */
  getctag = Qnil;
  rc_set (rec, RC_SLOT_C, make_fixnum (quit_char));
  internal_last_event_frame = selected_frame;
  Vlast_event_frame = internal_last_event_frame;
  /* If we report the quit char as an event,
     don't do so more than once.  */
  if (!NILP (Vinhibit_quit))
    Vquit_flag = Qnil;

  KBOARD *kb = FRAME_KBOARD (XFRAME (selected_frame));
  if (kb != current_kboard)
    {
      Lisp_Object last = KVAR (kb, kbd_queue);
      /* We shouldn't get here if we were in single-kboard mode!  */
      if (single_kboard)
        emacs_abort ();
      if (CONSP (last))
        {
          while (CONSP (XCDR (last)))
            last = XCDR (last);
          if (!NILP (XCDR (last)))
            emacs_abort ();
        }
      Lisp_Object qc = rc_get (rec, RC_SLOT_C);
      if (!CONSP (last))
        kset_kbd_queue (kb, list1 (qc));
      else
        XSETCDR (last, list1 (qc));
      kb->kbd_queue_has_data = 1;
      current_kboard = kb;
      /* This is going to exit from read_char
         so we had better get rid of this frame's stuff.  */
      return make_fixnum (-2); /* wrong_kboard_jmpbuf */
    }
  return Qnil;  /* Caller should re-enter read-char-main(jump=t).  */
}

/* {{coccinelle:skip_start}} */
Lisp_Object
read_char (int commandflag, Lisp_Object map,
	   Lisp_Object prev_event,
	   bool *used_mouse_menu, struct timespec *end_time)
{
  /* The full read_char body (record allocation, call_with_prompt
     with body and quit-handler closures) lives in Scheme as
     `read-char-entry' in (emacs read-char).  */
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs read-char", "read-char-entry");
  return scm_call_6 (proc,
                     make_fixnum (commandflag),
                     map, prev_event,
                     rc_wrap_ptr (used_mouse_menu),
                     rc_wrap_ptr (end_time),
                     make_kboard_smob (current_kboard));
}
/* {{coccinelle:skip_end}} */

/* Record a key that came from a mouse menu.
   Record it for echoing, for this-command-keys, and so on.  */

static void
record_menu_key (Lisp_Object c)
{
  /* Wipe the echo area.  */
  clear_message (1, 0);

  record_char (c);

  /* Once we reread a character, echoing can happen
     the next time we pause to read a new one.  */
  ok_to_echo_at_next_pause = NULL;

  /* Record this character as part of the current key.  */
  add_command_key (c);
  echo_update ();

  /* Re-reading in the middle of a command.  */
  last_input_event = c;
  num_input_events++;
}

/* Return true if should recognize C as "the help character".  */

static bool
help_char_p (Lisp_Object c)
{
  if (EQ (c, Vhelp_char))
    return true;
  Lisp_Object tail = Vhelp_event_list;
  FOR_EACH_TAIL_SAFE (tail)
    if (EQ (c, XCAR (tail)))
      return true;
  return false;
}

/* Record the input event C in various ways.  */

static void
record_char (Lisp_Object c)
{
  /* subr.el/read-passwd binds inhibit_record_char to avoid recording
     passwords.  */
  if (!record_all_keys && inhibit_record_char)
    return;

  int recorded = 0;

  if (CONSP (c) && (EQ (XCAR (c), Qhelp_echo) || EQ (XCAR (c), Qmouse_movement)))
    {
      /* To avoid filling recent_keys with help-echo and mouse-movement
	 events, we filter out repeated help-echo events, only store the
	 first and last in a series of mouse-movement events, and don't
	 store repeated help-echo events which are only separated by
	 mouse-movement events.  */

      Lisp_Object ev1, ev2, ev3;
      int ix1, ix2, ix3;

      if ((ix1 = recent_keys_index - 1) < 0)
	ix1 = lossage_limit - 1;
      ev1 = AREF (recent_keys, ix1);

      if ((ix2 = ix1 - 1) < 0)
	ix2 = lossage_limit - 1;
      ev2 = AREF (recent_keys, ix2);

      if ((ix3 = ix2 - 1) < 0)
	ix3 = lossage_limit - 1;
      ev3 = AREF (recent_keys, ix3);

      if (EQ (XCAR (c), Qhelp_echo))
	{
	  /* Don't record `help-echo' in recent_keys unless it shows some help
	     message, and a different help than the previously recorded
	     event.  */
	  Lisp_Object help, last_help;

	  help = Fcar_safe (Fcdr_safe (XCDR (c)));
	  if (!STRINGP (help))
	    recorded = 1;
	  else if (CONSP (ev1) && EQ (XCAR (ev1), Qhelp_echo)
		   && (last_help = Fcar_safe (Fcdr_safe (XCDR (ev1))), EQ (last_help, help)))
	    recorded = 1;
	  else if (CONSP (ev1) && EQ (XCAR (ev1), Qmouse_movement)
		   && CONSP (ev2) && EQ (XCAR (ev2), Qhelp_echo)
		   && (last_help = Fcar_safe (Fcdr_safe (XCDR (ev2))), EQ (last_help, help)))
	    recorded = -1;
	  else if (CONSP (ev1) && EQ (XCAR (ev1), Qmouse_movement)
		   && CONSP (ev2) && EQ (XCAR (ev2), Qmouse_movement)
		   && CONSP (ev3) && EQ (XCAR (ev3), Qhelp_echo)
		   && (last_help = Fcar_safe (Fcdr_safe (XCDR (ev3))), EQ (last_help, help)))
	    recorded = -2;
	}
      else if (EQ (XCAR (c), Qmouse_movement))
	{
	  /* Only record one pair of `mouse-movement' on a window in recent_keys.
	     So additional mouse movement events replace the last element.  */
	  Lisp_Object last_window, window;

	  window = Fcar_safe (Fcar_safe (XCDR (c)));
	  if (CONSP (ev1) && EQ (XCAR (ev1), Qmouse_movement)
	      && (last_window = Fcar_safe (Fcar_safe (XCDR (ev1))), EQ (last_window, window))
	      && CONSP (ev2) && EQ (XCAR (ev2), Qmouse_movement)
	      && (last_window = Fcar_safe (Fcar_safe (XCDR (ev2))), EQ (last_window, window)))
	    {
	      ASET (recent_keys, ix1, c);
	      recorded = 1;
	    }
	}
    }
  else if (NILP (Vexecuting_kbd_macro))
    store_kbd_macro_char (c);

  /* recent_keys should not include events from keyboard macros.  */
  if (NILP (Vexecuting_kbd_macro))
    {
      if (!recorded)
	{
	  total_keys += total_keys < lossage_limit;
	  ASET (recent_keys, recent_keys_index,
                /* Copy the event, in case it gets modified by side-effect
                   by some remapping function (bug#30955).  */
                CONSP (c) ? Fcopy_sequence (c) : c);
	  if (++recent_keys_index >= lossage_limit)
	    recent_keys_index = 0;
	}
      else if (recorded < 0)
	{
	  /* We need to remove one or two events from recent_keys.
	     To do this, we simply put nil at those events and move the
	     recent_keys_index backwards over those events.  Usually,
	     users will never see those nil events, as they will be
	     overwritten by the command keys entered to see recent_keys
	     (e.g. C-h l).  */

	  while (recorded++ < 0 && total_keys > 0)
	    {
	      if (total_keys < lossage_limit)
		total_keys--;
	      if (--recent_keys_index < 0)
		recent_keys_index = lossage_limit - 1;
	      ASET (recent_keys, recent_keys_index, Qnil);
	    }
	}

      num_nonmacro_input_events++;
    }

  /* Write c to the dribble file.  If c is a lispy event, write
     the event's symbol to the dribble file, in <brackets>.  Bleaugh.
     If you, dear reader, have a better idea, you've got the source.  :-) */
  if (dribble && NILP (Vexecuting_kbd_macro))
    {
      block_input ();
      if (FIXNUMP (c))
	{
	  if (XUFIXNUM (c) < 0x100)
	    putc (XUFIXNUM (c), dribble);
	  else
	    fprintf (dribble, " 0x%"pI"x", XUFIXNUM (c));
	}
      else
	{
	  Lisp_Object dribblee;

	  /* If it's a structured event, take the event header.  */
	  dribblee = EVENT_HEAD (c);

	  if (SYMBOLP (dribblee))
	    {
	      putc ('<', dribble);
	      fwrite (SDATA (SYMBOL_NAME (dribblee)), sizeof (char),
		      SBYTES (SYMBOL_NAME (dribblee)), dribble);
	      putc ('>', dribble);
	    }
	}

      fflush (dribble);
      unblock_input ();
    }
}

/* Low level keyboard/mouse input.
   kbd_buffer_store_event places events in kbd_buffer, and
   kbd_buffer_get_event retrieves them.  */

/* Return true if there are any events in the queue that read-char
   would return.  If this returns false, a read-char would block.  */
static bool
readable_events (int flags)
{
  if (flags & READABLE_EVENTS_DO_TIMERS_NOW)
    timer_check ();

  /* READABLE_EVENTS_FILTER_EVENTS is meant to be used only by
     input-pending-p and similar callers, which aren't interested in
     some input events.  If this flag is set, and
     input-pending-p-filter-events is non-nil, ignore events in
     while-no-input-ignore-events.  If the flag is set and
     input-pending-p-filter-events is nil, ignore only
     FOCUS_IN/OUT_EVENT events.  */
  if (kbd_fetch_ptr != kbd_store_ptr)
    {
      /* See https://lists.gnu.org/r/emacs-devel/2005-05/msg00297.html
	 for why we treat toolkit scroll-bar events specially here.  */
      if (flags & (READABLE_EVENTS_FILTER_EVENTS
#ifdef USE_TOOLKIT_SCROLL_BARS
		   | READABLE_EVENTS_IGNORE_SQUEEZABLES
#endif
		   ))
        {
          union buffered_input_event *event = kbd_fetch_ptr;

	  do
	    {
	      if (!(
#ifdef USE_TOOLKIT_SCROLL_BARS
		    (flags & READABLE_EVENTS_FILTER_EVENTS) &&
#endif
		    ((!input_pending_p_filter_events
		      && (event->kind == FOCUS_IN_EVENT
			  || event->kind == FOCUS_OUT_EVENT))
		     || (input_pending_p_filter_events
			 && is_ignored_event (event))))
#ifdef USE_TOOLKIT_SCROLL_BARS
		  && !((flags & READABLE_EVENTS_IGNORE_SQUEEZABLES)
		       && (event->kind == SCROLL_BAR_CLICK_EVENT
			   || event->kind == HORIZONTAL_SCROLL_BAR_CLICK_EVENT)
		       && event->ie.part == scroll_bar_handle
		       && event->ie.modifiers == 0)
#endif
		 )
		return 1;
	      event = next_kbd_event (event);
	    }
	  while (event != kbd_store_ptr);
        }
      else
	return 1;
    }

#ifdef HAVE_X_WINDOWS
  if (x_detect_pending_selection_requests ())
    return 1;
#endif

#ifdef HAVE_TEXT_CONVERSION
  if (detect_conversion_events ())
    return 1;
#endif

  if (!(flags & READABLE_EVENTS_IGNORE_SQUEEZABLES) && some_mouse_moved ())
    return 1;
  if (single_kboard)
    {
      if (current_kboard->kbd_queue_has_data)
	return 1;
    }
  else
    {
      KBOARD *kb;
      for (kb = all_kboards; kb; kb = kb->next_kboard)
	if (kb->kbd_queue_has_data)
	  return 1;
    }
  return 0;
}

/* Set this for debugging, to have a way to get out */
extern int stop_character;
int stop_character EXTERNALLY_VISIBLE;

static KBOARD *
event_to_kboard (struct input_event *event)
{
  /* Not applicable for these special events.  */
  if (event->kind == SELECTION_REQUEST_EVENT
      || event->kind == SELECTION_CLEAR_EVENT)
    return NULL;
  else
    {
      Lisp_Object obj = event->frame_or_window;
      /* There are some events that set this field to nil or string.  */
      if (WINDOWP (obj))
	obj = WINDOW_FRAME (XWINDOW (obj));
      /* Also ignore dead frames here.  */
      return ((FRAMEP (obj) && FRAME_LIVE_P (XFRAME (obj)))
	      ? FRAME_KBOARD (XFRAME (obj)) : NULL);
    }
}

#ifdef subprocesses
/* Return the number of slots occupied in kbd_buffer.  */

static int
kbd_buffer_nr_stored (void)
{
  int n = kbd_store_ptr - kbd_fetch_ptr;
  return n + (n < 0 ? KBD_BUFFER_SIZE : 0);
}
#endif	/* Store an event obtained at interrupt level into kbd_buffer, fifo */

void
kbd_buffer_store_event (register struct input_event *event)
{
  kbd_buffer_store_event_hold (event, 0);
}

/* Store EVENT obtained at interrupt level into kbd_buffer, fifo.

   If HOLD_QUIT is 0, just stuff EVENT into the fifo.
   Else, if HOLD_QUIT.kind != NO_EVENT, discard EVENT.
   Else, if EVENT is a quit event, store the quit event
   in HOLD_QUIT, and return (thus ignoring further events).

   This is used to postpone the processing of the quit event until all
   subsequent input events have been parsed (and discarded).  */

void
kbd_buffer_store_buffered_event (union buffered_input_event *event,
				 struct input_event *hold_quit)
{
  if (event->kind == NO_EVENT)
    emacs_abort ();

  if (hold_quit && hold_quit->kind != NO_EVENT)
    return;

  if (event->kind == ASCII_KEYSTROKE_EVENT)
    {
      int c = event->ie.code & 0377;

      if (event->ie.modifiers & ctrl_modifier)
	c = make_ctrl_char (c);

      c |= (event->ie.modifiers
	    & (meta_modifier | alt_modifier
	       | hyper_modifier | super_modifier));

      if (c == quit_char)
	{
	  KBOARD *kb = FRAME_KBOARD (XFRAME (event->ie.frame_or_window));

	  if (single_kboard && kb != current_kboard)
	    {
	      kset_kbd_queue
		(kb, list2 (make_lispy_switch_frame (event->ie.frame_or_window),
			    make_fixnum (c)));
	      kb->kbd_queue_has_data = true;

	      for (union buffered_input_event *sp = kbd_fetch_ptr;
		   sp != kbd_store_ptr; sp = next_kbd_event (sp))
		{
		  if (event_to_kboard (&sp->ie) == kb)
		    {
		      sp->ie.kind = NO_EVENT;
		      sp->ie.frame_or_window = Qnil;
		      sp->ie.arg = Qnil;
		    }
		}
	      return;
	    }

	  if (hold_quit)
	    {
	      *hold_quit = event->ie;
	      return;
	    }

	  /* If this results in a quit_char being returned to Emacs as
	     input, set Vlast_event_frame properly.  If this doesn't
	     get returned to Emacs as an event, the next event read
	     will set Vlast_event_frame again, so this is safe to do.  */
	  {
	    Lisp_Object focus;

	    focus = FRAME_FOCUS_FRAME (XFRAME (event->ie.frame_or_window));
	    if (NILP (focus))
	      focus = event->ie.frame_or_window;
	    internal_last_event_frame = focus;
	    Vlast_event_frame = focus;
	  }

	  handle_interrupt (0);
	  return;
	}

      if (c && c == stop_character)
	{
	  sys_suspend ();
	  return;
	}
    }

  /* Don't let the very last slot in the buffer become full,
     since that would make the two pointers equal,
     and that is indistinguishable from an empty buffer.
     Discard the event if it would fill the last slot.  */
  union buffered_input_event *next_slot = next_kbd_event (kbd_store_ptr);
  if (kbd_fetch_ptr != next_slot)
    {
      *kbd_store_ptr = *event;
      kbd_store_ptr = next_slot;
#ifdef subprocesses
      if (kbd_buffer_nr_stored () > KBD_BUFFER_SIZE / 2
	  && ! kbd_on_hold_p ())
        {
          /* Don't read keyboard input until we have processed kbd_buffer.
             This happens when pasting text longer than KBD_BUFFER_SIZE/2.  */
          hold_keyboard_input ();
        }
#endif	/* subprocesses */
    }

  /* If we're inside while-no-input, and this event qualifies
     as input, set quit-flag to cause an interrupt.  */
  if (!NILP (Vthrow_on_input)
      && !is_ignored_event (event))
    Vquit_flag = Vthrow_on_input;
}

/* Limit help event positions to this range, to avoid overflow problems.  */
#define INPUT_EVENT_POS_MAX \
  ((ptrdiff_t) min (PTRDIFF_MAX, min (TYPE_MAXIMUM (Time) / 2, \
				      MOST_POSITIVE_FIXNUM)))
#define INPUT_EVENT_POS_MIN (PTRDIFF_MIN < -INPUT_EVENT_POS_MAX \
			     ? -1 - INPUT_EVENT_POS_MAX : PTRDIFF_MIN)

/* Return a Time that encodes position POS.  POS must be in range.  */

static Time
position_to_Time (ptrdiff_t pos)
{
  eassert (INPUT_EVENT_POS_MIN <= pos && pos <= INPUT_EVENT_POS_MAX);
  return pos;
}

/* Return the position that ENCODED_POS encodes.
   Avoid signed integer overflow.  */

static ptrdiff_t
Time_to_position (Time encoded_pos)
{
  if (encoded_pos <= INPUT_EVENT_POS_MAX)
    return encoded_pos;
  Time encoded_pos_min = position_to_Time (INPUT_EVENT_POS_MIN);
  eassert (encoded_pos_min <= encoded_pos);
  ptrdiff_t notpos = -1 - encoded_pos;
  return -1 - notpos;
}

DEFUN ("--time-to-position", Ftime_to_position, Stime_to_position,
       1, 1, 0,
       doc: /* Decode timestamp ENCODED_POS into a buffer position fixnum.

Wraps the C Time_to_position helper used by HELP_EVENT.
Uses scm_to_intmax to handle bignum timestamps (wall-clock ms
can overflow fixnum range on 32-bit unsigned-fixnum builds).  */)
  (Lisp_Object encoded_pos)
{
  return make_fixnum (Time_to_position (scm_to_intmax (encoded_pos)));
}

/* Generate a HELP_EVENT input_event and store it in the keyboard
   buffer.

   HELP is the help form.

   FRAME and WINDOW are the frame and window where the help is
   generated.  OBJECT is the Lisp object where the help was found (a
   buffer, a string, an overlay, or nil if neither from a string nor
   from a buffer).  POS is the position within OBJECT where the help
   was found.  */

void
gen_help_event (Lisp_Object help, Lisp_Object frame, Lisp_Object window,
		Lisp_Object object, ptrdiff_t pos)
{
  struct input_event event;
  EVENT_INIT (event);

  event.kind = HELP_EVENT;
  event.frame_or_window = frame;
  event.arg = object;
  event.x = WINDOWP (window) ? window : frame;
  event.y = help;
  event.timestamp = position_to_Time (pos);
  kbd_buffer_store_event (&event);
}


/* Store HELP_EVENTs for HELP on FRAME in the input queue.  */

void
kbd_buffer_store_help_event (Lisp_Object frame, Lisp_Object help)
{
  struct input_event event;
  EVENT_INIT (event);

  event.kind = HELP_EVENT;
  event.frame_or_window = frame;
  event.arg = Qnil;
  event.x = Qnil;
  event.y = help;
  event.timestamp = 0;
  kbd_buffer_store_event (&event);
}


/* Discard any mouse events in the event buffer by setting them to
   NO_EVENT.  */
void
discard_mouse_events (void)
{
  for (union buffered_input_event *sp = kbd_fetch_ptr;
       sp != kbd_store_ptr; sp = next_kbd_event (sp))
    {
      if (sp->kind == MOUSE_CLICK_EVENT
	  || sp->kind == WHEEL_EVENT
          || sp->kind == HORIZ_WHEEL_EVENT
	  || sp->kind == SCROLL_BAR_CLICK_EVENT
	  || sp->kind == HORIZONTAL_SCROLL_BAR_CLICK_EVENT)
	{
	  sp->kind = NO_EVENT;
	}
    }
}


/* Return true if there are any real events waiting in the event
   buffer, not counting `NO_EVENT's.

   Discard NO_EVENT events at the front of the input queue, possibly
   leaving the input queue empty if there are no real input events.  */

bool
kbd_buffer_events_waiting (void)
{
  for (union buffered_input_event *sp = kbd_fetch_ptr;
       ; sp = next_kbd_event (sp))
    if (sp == kbd_store_ptr || sp->kind != NO_EVENT)
      {
	kbd_fetch_ptr = sp;
	return sp != kbd_store_ptr && sp->kind != NO_EVENT;
      }
}


/* Clear input event EVENT.  */

static void
clear_event (struct input_event *event)
{
  event->kind = NO_EVENT;
}

static Lisp_Object
kbd_buffer_get_event_1 (Lisp_Object arg)
{
  Lisp_Object coding_system = Fget_text_property (make_fixnum (0),
						  Qcoding, arg);

  if (EQ (coding_system, Qt))
    return arg;

  return code_convert_string (arg, (!NILP (coding_system)
				    ? coding_system
				    : Vlocale_coding_system),
			      Qnil, 0, false, 0);
}

static Lisp_Object
kbd_buffer_get_event_2 (Lisp_Object val)
{
  return Qnil;
}

/* Read one event from the event buffer, waiting if necessary.
   The value is a Lisp object representing the event.
   The value is nil for an event that should be ignored,
   or that was handled here.
   We always read and discard one event.  */

static Lisp_Object
kbd_buffer_get_event (KBOARD **kbp,
                      bool *used_mouse_menu,
                      struct timespec *end_time)
{
  Lisp_Object obj, str;
#ifdef HAVE_X_WINDOWS
  bool had_pending_selection_requests;

  had_pending_selection_requests = false;
#endif
#ifdef HAVE_TEXT_CONVERSION
  bool had_pending_conversion_events;

  had_pending_conversion_events = false;
#endif

#ifdef subprocesses
  if (kbd_on_hold_p () && kbd_buffer_nr_stored () < KBD_BUFFER_SIZE / 4)
    {
      /* Start reading input again because we have processed enough to
         be able to accept new events again.  */
      unhold_keyboard_input ();
    }
#endif	/* subprocesses */

#if !defined HAVE_DBUS && !defined USE_FILE_NOTIFY && !defined THREADS_ENABLED
  if (noninteractive
      /* In case we are running as a daemon, only do this before
	 detaching from the terminal.  */
      || (IS_DAEMON && DAEMON_RUNNING))
    {
      int c = getchar ();
      XSETINT (obj, c);
      *kbp = current_kboard;
      return obj;
    }
#endif	/* !defined HAVE_DBUS && !defined USE_FILE_NOTIFY && !defined THREADS_ENABLED  */

  *kbp = current_kboard;

  /* Wait until there is input available.  */
  for (;;)
    {
      /* Break loop if there's an unread command event.  Needed in
	 moused window autoselection which uses a timer to insert such
	 events.  */
      if (CONSP (Vunread_command_events))
	break;

#ifdef HAVE_TEXT_CONVERSION
      /* That text conversion events take priority over keyboard
	 events, since input methods frequently send them immediately
	 after edits, with the assumption that this order of events
	 will be observed.  */

      if (detect_conversion_events ())
	{
	  had_pending_conversion_events = true;
	  break;
	}
#endif /* HAVE_TEXT_CONVERSION */

      if (kbd_fetch_ptr != kbd_store_ptr)
	break;
      if (some_mouse_moved ())
	break;

      /* If the quit flag is set, then read_char will return
	 quit_char, so that counts as "available input."  */
      if (!NILP (Vquit_flag))
	quit_throw_to_read_char (0);

      /* One way or another, wait until input is available; then, if
	 interrupt handlers have not read it, read it now.  */

#if defined (USABLE_SIGIO) || defined (USABLE_SIGPOLL)
      gobble_input ();
#endif

      if (kbd_fetch_ptr != kbd_store_ptr)
	break;
      if (some_mouse_moved ())
	break;
#ifdef HAVE_X_WINDOWS
      if (x_detect_pending_selection_requests ())
	{
	  had_pending_selection_requests = true;
	  break;
	}
#endif
      if (end_time)
	{
	  struct timespec now = current_timespec ();
	  if (timespec_cmp (*end_time, now) <= 0)
	    return Qnil;	/* Finished waiting.  */
	  else
	    {
	      struct timespec duration = timespec_sub (*end_time, now);
	      wait_reading_process_output (min (duration.tv_sec,
						WAIT_READING_MAX),
					   duration.tv_nsec,
					   -1, 1, Qnil, NULL, 0);
	    }
	}
      else
	{
	  bool do_display = true;

	  if (FRAME_TERMCAP_P (SELECTED_FRAME ()))
	    {
	      struct tty_display_info *tty = CURTTY ();

	      /* When this TTY is displaying a menu, we must prevent
		 any redisplay, because we modify the frame's glyph
		 matrix behind the back of the display engine.  */
	      if (tty->showing_menu)
		do_display = false;
	    }

	  wait_reading_process_output (0, 0, -1, do_display, Qnil, NULL, 0);
	}

      if (!interrupt_input && kbd_fetch_ptr == kbd_store_ptr)
	gobble_input ();
    }

#ifdef HAVE_X_WINDOWS
  /* Handle pending selection requests.  This can happen if Emacs
     enters a recursive edit inside a nested event loop (probably
     because the debugger opened) or someone called
     `read-char'.  */

  if (had_pending_selection_requests)
    x_handle_pending_selection_requests ();
#endif

  if (CONSP (Vunread_command_events))
    {
      Lisp_Object first;
      first = XCAR (Vunread_command_events);
      Vunread_command_events = XCDR (Vunread_command_events);
      *kbp = current_kboard;
      return first;
    }

#ifdef HAVE_TEXT_CONVERSION
  /* There are pending text conversion operations.  Text conversion
     events should be generated before processing any other keyboard
     input.  */
  if (had_pending_conversion_events)
    {
      handle_pending_conversion_events ();
      obj = Qtext_conversion;

      /* See the comment in handle_pending_conversion_events_1.
         Note that in addition, text conversion events are not
         generated if no edits were actually made.  */
      if (conversion_disabled_p ()
	  || NILP (Vtext_conversion_edits))
	obj = Qnil;
    }
  else
#endif
  /* At this point, we know that there is a readable event available
     somewhere.  If the event queue is empty, then there must be a
     mouse movement enabled and available.  */
  if (kbd_fetch_ptr != kbd_store_ptr)
    {
      union buffered_input_event *event = kbd_fetch_ptr;

      *kbp = event_to_kboard (&event->ie);
      if (*kbp == 0)
	*kbp = current_kboard;  /* Better than returning null ptr?  */

      obj = Qnil;

      /* These two kinds of events get special handling
	 and don't actually appear to the command loop.
	 We return nil for them.  */
      switch (event->kind)
      {
#ifndef HAVE_HAIKU
      case SELECTION_REQUEST_EVENT:
      case SELECTION_CLEAR_EVENT:
	{
#if defined HAVE_X11 || HAVE_PGTK
	  /* Remove it from the buffer before processing it,
	     since otherwise swallow_events will see it
	     and process it again.  */
	  struct selection_input_event copy = event->sie;
	  kbd_fetch_ptr = next_kbd_event (event);
	  input_pending = readable_events (0);

#ifdef HAVE_X11
	  x_handle_selection_event (&copy);
#else
	  pgtk_handle_selection_event (&copy);
#endif
#else
	  /* We're getting selection request events, but we don't have
             a window system.  */
	  emacs_abort ();
#endif
	}
        break;
#else
      case SELECTION_REQUEST_EVENT:
	emacs_abort ();

      case SELECTION_CLEAR_EVENT:
	{
	  struct input_event copy = event->ie;

	  kbd_fetch_ptr = next_kbd_event (event);
	  input_pending = readable_events (0);
	  haiku_handle_selection_clear (&copy);
	}
	break;
#endif

      case MONITORS_CHANGED_EVENT:
	{
	  kbd_fetch_ptr = next_kbd_event (event);
	  input_pending = readable_events (0);

	  CALLN (Frun_hook_with_args,
		 Qdisplay_monitors_changed_functions,
		 event->ie.arg);

	  break;
	}

#ifdef HAVE_ANDROID
      case NOTIFICATION_EVENT:
        {
	  kbd_fetch_ptr = next_kbd_event (event);
	  input_pending = readable_events (0);
	  CALLN (Fapply, XCAR (event->ie.arg), XCDR (event->ie.arg));
	  break;
	}
#endif /* HAVE_ANDROID */

#ifdef HAVE_EXT_MENU_BAR
      case MENU_BAR_ACTIVATE_EVENT:
	{
          struct frame *f;
	  kbd_fetch_ptr = next_kbd_event (event);
	  input_pending = readable_events (0);
          f = (XFRAME (event->ie.frame_or_window));
	  if (FRAME_LIVE_P (f) && FRAME_TERMINAL (f)->activate_menubar_hook)
	    FRAME_TERMINAL (f)->activate_menubar_hook (f);
	}
        break;
#endif
#if defined (HAVE_NS)
      case NS_TEXT_EVENT:
	if (used_mouse_menu)
	  *used_mouse_menu = true;
	FALLTHROUGH;
#endif
      case PREEDIT_TEXT_EVENT:
#ifdef HAVE_NTGUI
      case END_SESSION_EVENT:
      case LANGUAGE_CHANGE_EVENT:
#endif
#ifdef HAVE_WINDOW_SYSTEM
      case DELETE_WINDOW_EVENT:
      case ICONIFY_EVENT:
      case DEICONIFY_EVENT:
      case MOVE_FRAME_EVENT:
#endif
#ifdef USE_FILE_NOTIFY
      case FILE_NOTIFY_EVENT:
#endif
#ifdef HAVE_DBUS
      case DBUS_EVENT:
#endif
#ifdef THREADS_ENABLED
      case THREAD_EVENT:
#endif
#ifdef HAVE_XWIDGETS
      case XWIDGET_EVENT:
      case XWIDGET_DISPLAY_EVENT:
#endif
      case SAVE_SESSION_EVENT:
      case NO_EVENT:
      case HELP_EVENT:
      case FOCUS_IN_EVENT:
      case CONFIG_CHANGED_EVENT:
      case FOCUS_OUT_EVENT:
      case SELECT_WINDOW_EVENT:
        {
          obj = make_lispy_event (&event->ie);
          kbd_fetch_ptr = next_kbd_event (event);
        }
        break;
      default:
	{
	  /* If this event is on a different frame, return a
	     switch-frame this time, and leave the event in the queue
	     for next time.  */
	  Lisp_Object frame;
	  Lisp_Object focus;

	  frame = event->ie.frame_or_window;
	  if (CONSP (frame))
	    frame = XCAR (frame);
	  else if (WINDOWP (frame))
	    frame = WINDOW_FRAME (XWINDOW (frame));

	  focus = FRAME_FOCUS_FRAME (XFRAME (frame));
	  if (! NILP (focus))
	    frame = focus;

	  if (!EQ (frame, internal_last_event_frame)
	      && !EQ (frame, selected_frame))
	    obj = make_lispy_switch_frame (frame);
	  internal_last_event_frame = frame;

	  if (EQ (event->ie.device, Qt))
	    Vlast_event_device = ((event->ie.kind == ASCII_KEYSTROKE_EVENT
				   || event->ie.kind == MULTIBYTE_CHAR_KEYSTROKE_EVENT
				   || event->ie.kind == NON_ASCII_KEYSTROKE_EVENT)
				  ? virtual_core_keyboard_name
				  : virtual_core_pointer_name);
	  else
	    Vlast_event_device = event->ie.device;

	  /* If we didn't decide to make a switch-frame event, go ahead
	     and build a real event from the queue entry.  */
	  if (NILP (obj))
	    {
	      double pinch_dx, pinch_dy, pinch_angle;

	      /* Pinch events are often sent in rapid succession, so
		 large amounts of such events have the potential to
		 queue up inside the keyboard buffer.  In that case,
		 find the last pinch event in succession on the same
		 frame with the same modifiers, and send that instead.  */

	      if (event->ie.kind == PINCH_EVENT
		  /* Ignore if this is the start of a pinch sequence.
		     These events should always be sent so that we
		     never miss a sequence starting, and they don't
		     have the potential to queue up.  */
		  && ((pinch_dx
		       = XFLOAT_DATA (XCAR (event->ie.arg))) != 0.0
		      || XFLOAT_DATA (XCAR (XCDR (event->ie.arg))) != 0.0
		      || XFLOAT_DATA (Fnth (make_fixnum (3), event->ie.arg)) != 0.0))
		{
		  union buffered_input_event *maybe_event = next_kbd_event (event);

		  pinch_dy = XFLOAT_DATA (XCAR (XCDR (event->ie.arg)));
		  pinch_angle = XFLOAT_DATA (Fnth (make_fixnum (3), event->ie.arg));

		  while (maybe_event != kbd_store_ptr
			 && maybe_event->ie.kind == PINCH_EVENT
			 /* Make sure we never miss an event that has
			    different modifiers.  */
			 && maybe_event->ie.modifiers == event->ie.modifiers
			 /* Make sure that the event is for the same
			    frame.  */
			 && EQ (maybe_event->ie.frame_or_window,
				event->ie.frame_or_window)
			 /* Make sure that the event isn't the start
			    of a new pinch gesture sequence.  */
			 && (XFLOAT_DATA (XCAR (maybe_event->ie.arg)) != 0.0
			     || XFLOAT_DATA (XCAR (XCDR (maybe_event->ie.arg))) != 0.0
			     || XFLOAT_DATA (Fnth (make_fixnum (3),
						   maybe_event->ie.arg)) != 0.0))
		    {
		      event = maybe_event;
		      /* Add up relative deltas inside events we skip.  */
		      pinch_dx += XFLOAT_DATA (XCAR (maybe_event->ie.arg));
		      pinch_dy += XFLOAT_DATA (XCAR (XCDR (maybe_event->ie.arg)));
		      pinch_angle += XFLOAT_DATA (Fnth (make_fixnum (3),
							maybe_event->ie.arg));

		      XSETCAR (maybe_event->ie.arg, make_float (pinch_dx));
		      XSETCAR (XCDR (maybe_event->ie.arg), make_float (pinch_dy));
		      XSETCAR (Fnthcdr (make_fixnum (3),
					maybe_event->ie.arg),
			       make_float (fmod (pinch_angle, 360.0)));

		      if (!EQ (maybe_event->ie.device, Qt))
			Vlast_event_device = maybe_event->ie.device;

		      maybe_event = next_kbd_event (event);
		    }
		}

	      if (event->kind == MULTIBYTE_CHAR_KEYSTROKE_EVENT
		  /* This string has to be decoded.  */
		  && STRINGP (event->ie.arg))
		{
		  str = internal_condition_case_1 (kbd_buffer_get_event_1,
						   event->ie.arg, Qt,
						   kbd_buffer_get_event_2);

		  /* Decoding the string failed, so use the original,
		     where at least ASCII text will work.  */
		  if (NILP (str))
		    str = event->ie.arg;

		  if (!SCHARS (str))
		    {
		      kbd_fetch_ptr = next_kbd_event (event);
		      obj = Qnil;
		      break;
		    }

		  /* car is the index of the next character in the
		     string that will be sent and cdr is the string
		     itself.  */
		  event->ie.arg = Fcons (make_fixnum (0), str);
		}

	      if (event->kind == MULTIBYTE_CHAR_KEYSTROKE_EVENT
		  && CONSP (event->ie.arg))
		{
		  eassert (FIXNUMP (XCAR (event->ie.arg)));
		  eassert (STRINGP (XCDR (event->ie.arg)));
		  eassert (XFIXNUM (XCAR (event->ie.arg))
			   < SCHARS (XCDR (event->ie.arg)));

		  event->ie.code = XFIXNUM (Faref (XCDR (event->ie.arg),
						   XCAR (event->ie.arg)));

		  XSETCAR (event->ie.arg,
			   make_fixnum (XFIXNUM (XCAR (event->ie.arg)) + 1));
		}

	      obj = make_lispy_event (&event->ie);

#ifdef HAVE_EXT_MENU_BAR
	      /* If this was a menu selection, then set the flag to inhibit
		 writing to last_nonmenu_event.  Don't do this if the event
		 we're returning is (menu-bar), though; that indicates the
		 beginning of the menu sequence, and we might as well leave
		 that as the `event with parameters' for this selection.  */
	      if (used_mouse_menu
		  && !EQ (event->ie.frame_or_window, event->ie.arg)
		  && (event->kind == MENU_BAR_EVENT
		      || event->kind == TAB_BAR_EVENT
		      || event->kind == TOOL_BAR_EVENT))
		*used_mouse_menu = true;
#endif
#ifdef HAVE_NS
	      /* Certain system events are non-key events.  */
	      if (used_mouse_menu
                  && event->kind == NS_NONKEY_EVENT)
		*used_mouse_menu = true;
#endif

	      if (event->kind != MULTIBYTE_CHAR_KEYSTROKE_EVENT
		  || !CONSP (event->ie.arg)
		  || (XFIXNUM (XCAR (event->ie.arg))
		      >= SCHARS (XCDR (event->ie.arg))))
		{
		  /* Wipe out this event, to catch bugs.  */
		  clear_event (&event->ie);
		  kbd_fetch_ptr = next_kbd_event (event);
		}
	    }
	}
      }
    }
  /* Try generating a mouse motion event.  */
  else if (some_mouse_moved ())
    {
      struct frame *f, *movement_frame = some_mouse_moved ();
      Lisp_Object bar_window;
      enum scroll_bar_part part;
      Lisp_Object x, y;
      Time t;

      f = movement_frame;
      *kbp = current_kboard;
      /* Note that this uses F to determine which terminal to look at.
	 If there is no valid info, it does not store anything
	 so x remains nil.  */
      x = Qnil;

      /* XXX Can f or mouse_position_hook be NULL here?  */
      if (f && FRAME_TERMINAL (f)->mouse_position_hook)
        (*FRAME_TERMINAL (f)->mouse_position_hook) (&f, 0, &bar_window,
                                                    &part, &x, &y, &t);

      obj = Qnil;

      /* Decide if we should generate a switch-frame event.  Don't
	 generate switch-frame events for motion outside of all Emacs
	 frames.  */
      if (!NILP (x) && f)
	{
	  Lisp_Object frame;

	  frame = FRAME_FOCUS_FRAME (f);
	  if (NILP (frame))
	    XSETFRAME (frame, f);

	  if (!EQ (frame, internal_last_event_frame)
	      && !EQ (frame, selected_frame))
	    obj = make_lispy_switch_frame (frame);
	  internal_last_event_frame = frame;
	}

      /* If we didn't decide to make a switch-frame event, go ahead and
	 return a mouse-motion event.  */
      if (!NILP (x) && NILP (obj))
	obj = make_lispy_movement (f, bar_window, part, x, y, t);

      if (!NILP (obj))
	Vlast_event_device = (STRINGP (movement_frame->last_mouse_device)
			      ? movement_frame->last_mouse_device
			      : virtual_core_pointer_name);
    }
#ifdef HAVE_X_WINDOWS
  else if (had_pending_selection_requests)
    obj = Qnil;
#endif
  else
    /* We were promised by the above while loop that there was
       something for us to read!  */
    emacs_abort ();

  input_pending = readable_events (0);

  Vlast_event_frame = internal_last_event_frame;

  return (obj);
}

/* Process any non-user-visible events (currently X selection events),
   without reading any user-visible events.  */

static void
process_special_events (void)
{
  union buffered_input_event *event;
#if defined HAVE_X11 || defined HAVE_PGTK || defined HAVE_HAIKU
#ifndef HAVE_HAIKU
  struct selection_input_event copy;
#else
  struct input_event copy;
#endif
  int moved_events;
#endif

  for (event = kbd_fetch_ptr;  event != kbd_store_ptr;
       event = next_kbd_event (event))
    {
      /* If we find a stored X selection request, handle it now.  */
      if (event->kind == SELECTION_REQUEST_EVENT
	  || event->kind == SELECTION_CLEAR_EVENT)
	{
#if defined HAVE_X11 || defined HAVE_PGTK

	  /* Remove the event from the fifo buffer before processing;
	     otherwise swallow_events called recursively could see it
	     and process it again.  To do this, we move the events
	     between kbd_fetch_ptr and EVENT one slot to the right,
	     cyclically.  */

	  copy = event->sie;

	  if (event < kbd_fetch_ptr)
	    {
	      memmove (kbd_buffer + 1, kbd_buffer,
		       (event - kbd_buffer) * sizeof *kbd_buffer);
	      kbd_buffer[0] = kbd_buffer[KBD_BUFFER_SIZE - 1];
	      moved_events = kbd_buffer + KBD_BUFFER_SIZE - 1 - kbd_fetch_ptr;
	    }
	  else
	    moved_events = event - kbd_fetch_ptr;

	  memmove (kbd_fetch_ptr + 1, kbd_fetch_ptr,
		   moved_events * sizeof *kbd_fetch_ptr);
	  kbd_fetch_ptr = next_kbd_event (kbd_fetch_ptr);
	  input_pending = readable_events (0);

#ifdef HAVE_X11
	  x_handle_selection_event (&copy);
#else
	  pgtk_handle_selection_event (&copy);
#endif
#elif defined HAVE_HAIKU
	  if (event->ie.kind != SELECTION_CLEAR_EVENT)
	    emacs_abort ();

	  copy = event->ie;

	  if (event < kbd_fetch_ptr)
	    {
	      memmove (kbd_buffer + 1, kbd_buffer,
		       (event - kbd_buffer) * sizeof *kbd_buffer);
	      kbd_buffer[0] = kbd_buffer[KBD_BUFFER_SIZE - 1];
	      moved_events = kbd_buffer + KBD_BUFFER_SIZE - 1 - kbd_fetch_ptr;
	    }
	  else
	    moved_events = event - kbd_fetch_ptr;

	  memmove (kbd_fetch_ptr + 1, kbd_fetch_ptr,
		   moved_events * sizeof *kbd_fetch_ptr);
	  kbd_fetch_ptr = next_kbd_event (kbd_fetch_ptr);
	  input_pending = readable_events (0);
	  haiku_handle_selection_clear (&copy);
#else
	  /* We're getting selection request events, but we don't have
             a window system.  */
	  emacs_abort ();
#endif
	}
    }
}

/* Process any events that are not user-visible, run timer events that
   are ripe, and return, without reading any user-visible events.  */

void
swallow_events (bool do_display)
{
  unsigned old_timers_run;

  process_special_events ();

  old_timers_run = timers_run;
  get_input_pending (READABLE_EVENTS_DO_TIMERS_NOW);

  if (!input_pending && timers_run != old_timers_run && do_display)
    redisplay_preserve_echo_area (7);
}

/* Record the start of when Emacs is idle,
   for the sake of running idle-time timers.  */

static void
timer_start_idle (void)
{
  /* If we are already in the idle state, do nothing.  */
  if (timespec_valid_p (timer_idleness_start_time))
    return;

  timer_idleness_start_time = current_timespec ();
  timer_last_idleness_start_time = timer_idleness_start_time;

  /* Mark all idle-time timers as once again candidates for running.  */
  call0 (Qinternal_timer_start_idle);
}

/* Record that Emacs is no longer idle, so stop running idle-time timers.  */

static void
timer_stop_idle (void)
{
  timer_idleness_start_time = invalid_timespec ();
}

/* Resume idle timer from last idle start time.  */

static void
timer_resume_idle (void)
{
  if (timespec_valid_p (timer_idleness_start_time))
    return;

  timer_idleness_start_time = timer_last_idleness_start_time;
}

/* List of elisp functions to call, delayed because they were generated in
   a context where Elisp could not be safely run (e.g. redisplay, signal,
   ...).  Each element has the form (FUN . ARGS).  */
Lisp_Object pending_funcalls;

/* Return the value of TIMER if it is a valid timer, an invalid struct
   timespec otherwise.  */
static struct timespec
decode_timer (Lisp_Object timer)
{
  if (! ((VECTOR_OR_PSEUDOVECTORP (timer)) && ASIZE (timer) == 10))
    return invalid_timespec ();

  Lisp_Object slot0 = AREF (timer, 0);
  if (! NILP (slot0))
    return invalid_timespec ();

  Lisp_Object slot2 = AREF (timer, 2);
  if (! FIXNUMP (slot2))
    return invalid_timespec ();

  Lisp_Object slot1 = AREF (timer, 1);
  Lisp_Object slot3 = AREF (timer, 3);
  Lisp_Object slot8 = AREF (timer, 8);
  return list4_to_timespec (slot1, slot2, slot3, slot8);
}


/* Check whether a timer has fired.  To prevent larger problems we simply
   disregard elements that are not proper timers.  Do not make a circular
   timer list for the time being.

   Returns the time to wait until the next timer fires.  If a
   timer is triggering now, return zero.
   If no timer is active, return -1.

   If a timer is ripe, we run it, with quitting turned off.
   In that case we return 0 to indicate that a new timer_check_2 call
   should be done.  */

static struct timespec
timer_check_2 (Lisp_Object timers, Lisp_Object idle_timers)
{
  /* First run the code that was delayed.  */
  while (CONSP (pending_funcalls))
    {
      Lisp_Object funcall = XCAR (pending_funcalls);
      pending_funcalls = XCDR (pending_funcalls);
      safe_calln (Qapply, XCAR (funcall), XCDR (funcall));
    }

  if (! (CONSP (timers) || CONSP (idle_timers)))
    return invalid_timespec ();

  struct timespec
    now = current_timespec (),
    idleness_now = (timespec_valid_p (timer_idleness_start_time)
		    ? timespec_sub (now, timer_idleness_start_time)
		    : make_timespec (0, 0));

  do
    {
      Lisp_Object chosen_timer, timer = Qnil, idle_timer = Qnil;
      struct timespec difference;
      struct timespec timer_difference = invalid_timespec ();
      struct timespec idle_timer_difference = invalid_timespec ();
      bool ripe, timer_ripe = 0, idle_timer_ripe = 0;

      /* Set TIMER and TIMER_DIFFERENCE
	 based on the next ordinary timer.
	 TIMER_DIFFERENCE is the distance in time from NOW to when
	 this timer becomes ripe.
         Skip past invalid timers and timers already handled.  */
      if (CONSP (timers))
	{
	  timer = XCAR (timers);
	  struct timespec timer_time = decode_timer (timer);
	  if (! timespec_valid_p (timer_time))
	    {
	      timers = XCDR (timers);
	      continue;
	    }

	  timer_ripe = timespec_cmp (timer_time, now) <= 0;
	  timer_difference = (timer_ripe
			      ? timespec_sub (now, timer_time)
			      : timespec_sub (timer_time, now));
	}

      /* Likewise for IDLE_TIMER and IDLE_TIMER_DIFFERENCE
	 based on the next idle timer.  */
      if (CONSP (idle_timers))
	{
	  idle_timer = XCAR (idle_timers);
	  struct timespec idle_timer_time = decode_timer (idle_timer);
	  if (! timespec_valid_p (idle_timer_time))
	    {
	      idle_timers = XCDR (idle_timers);
	      continue;
	    }

	  idle_timer_ripe = timespec_cmp (idle_timer_time, idleness_now) <= 0;
	  idle_timer_difference
	    = (idle_timer_ripe
	       ? timespec_sub (idleness_now, idle_timer_time)
	       : timespec_sub (idle_timer_time, idleness_now));
	}

      /* Decide which timer is the next timer,
	 and set CHOSEN_TIMER, DIFFERENCE, and RIPE accordingly.
	 Also step down the list where we found that timer.  */

      if (timespec_valid_p (timer_difference)
	  && (! timespec_valid_p (idle_timer_difference)
	      || idle_timer_ripe < timer_ripe
	      || (idle_timer_ripe == timer_ripe
		  && ((timer_ripe
		       ? timespec_cmp (idle_timer_difference,
				       timer_difference)
		       : timespec_cmp (timer_difference,
				       idle_timer_difference))
		      < 0))))
	{
	  chosen_timer = timer;
	  timers = XCDR (timers);
	  difference = timer_difference;
	  ripe = timer_ripe;
	}
      else
	{
	  chosen_timer = idle_timer;
	  idle_timers = XCDR (idle_timers);
	  difference = idle_timer_difference;
	  ripe = idle_timer_ripe;
	}

      /* If timer is ripe, run it if it hasn't been run.  */
      if (ripe)
	{
	  /* If we got here, presumably `decode_timer` has checked
             that this timer has not yet been triggered.  */
	  eassert (NILP (AREF (chosen_timer, 0)));
	  /* In a production build, where assertions compile to
	     nothing, we still want to play it safe here.  */
	  if (NILP (AREF (chosen_timer, 0)))
	    {
	      dynwind_begin ();
	      Lisp_Object old_deactivate_mark = Vdeactivate_mark;

	      /* Mark the timer as triggered to prevent problems if the lisp
		 code fails to reschedule it right.  */
	      ASET (chosen_timer, 0, Qt);

	      specbind_guile (Qinhibit_quit, Qt);

	      call1 (Qtimer_event_handler, chosen_timer);
	      Vdeactivate_mark = old_deactivate_mark;
	      timers_run++;
	      dynwind_end ();

	      /* Since we have handled the event,
		 we don't need to tell the caller to wake up and do it.  */
	      /* But the caller must still wait for the next timer, so
		 return 0 to indicate that.  */
	    }

	  return make_timespec (0, 0);
	}
      else
	/* When we encounter a timer that is still waiting,
	   return the amount of time to wait before it is ripe.  */
	{
	  return difference;
	}
    }
  while (CONSP (timers) || CONSP (idle_timers));

  /* No timers are pending in the future.  */
  return invalid_timespec ();
}


/* Check whether a timer has fired.  To prevent larger problems we simply
   disregard elements that are not proper timers.  Do not make a circular
   timer list for the time being.

   Returns the time to wait until the next timer fires.
   If no timer is active, return an invalid value.

   As long as any timer is ripe, we run it.  */

struct timespec
timer_check (void)
{
  struct timespec nexttime;
  Lisp_Object timers, idle_timers;

  Lisp_Object tem = Vinhibit_quit;
  Vinhibit_quit = Qt;
  block_input ();
  turn_on_atimers (false);

  /* We use copies of the timers' lists to allow a timer to add itself
     again, without locking up Emacs if the newly added timer is
     already ripe when added.  */

  /* Always consider the ordinary timers.  */
  timers = Fcopy_sequence (Vtimer_list);
  /* Consider the idle timers only if Emacs is idle.  */
  if (timespec_valid_p (timer_idleness_start_time))
    idle_timers = Fcopy_sequence (Vtimer_idle_list);
  else
    idle_timers = Qnil;

  turn_on_atimers (true);
  unblock_input ();
  Vinhibit_quit = tem;

  do
    {
      nexttime = timer_check_2 (timers, idle_timers);
    }
  while (nexttime.tv_sec == 0 && nexttime.tv_nsec == 0);

  return nexttime;
}

DEFUN ("current-idle-time", Fcurrent_idle_time, Scurrent_idle_time, 0, 0, 0,
       doc: /* Return the current length of Emacs idleness, or nil.
The value when Emacs is idle is a Lisp timestamp in the style of
`current-time'.

The value when Emacs is not idle is nil.

If the value is a list of four integers (HIGH LOW USEC PSEC), then PSEC
is a multiple of the system clock resolution.  */)
  (void)
{
  if (timespec_valid_p (timer_idleness_start_time))
    return make_lisp_time (timespec_sub (current_timespec (),
					 timer_idleness_start_time));

  return Qnil;
}

/* Caches for modify_event_symbol — backing store for --mes-cache-get/set.  */
static Lisp_Object accent_key_syms;
static Lisp_Object func_key_syms;
static Lisp_Object mouse_syms;
static Lisp_Object wheel_syms;
static Lisp_Object drag_n_drop_syms;
static Lisp_Object pinch_syms;

/* This is a list of keysym codes for special "accent" characters.
   It parallels lispy_accent_keys.  */

static const int lispy_accent_codes[] =
{
#ifdef XK_dead_circumflex
  XK_dead_circumflex,
#else
  0,
#endif
#ifdef XK_dead_grave
  XK_dead_grave,
#else
  0,
#endif
#ifdef XK_dead_tilde
  XK_dead_tilde,
#else
  0,
#endif
#ifdef XK_dead_diaeresis
  XK_dead_diaeresis,
#else
  0,
#endif
#ifdef XK_dead_macron
  XK_dead_macron,
#else
  0,
#endif
#ifdef XK_dead_degree
  XK_dead_degree,
#else
  0,
#endif
#ifdef XK_dead_acute
  XK_dead_acute,
#else
  0,
#endif
#ifdef XK_dead_cedilla
  XK_dead_cedilla,
#else
  0,
#endif
#ifdef XK_dead_breve
  XK_dead_breve,
#else
  0,
#endif
#ifdef XK_dead_ogonek
  XK_dead_ogonek,
#else
  0,
#endif
#ifdef XK_dead_caron
  XK_dead_caron,
#else
  0,
#endif
#ifdef XK_dead_doubleacute
  XK_dead_doubleacute,
#else
  0,
#endif
#ifdef XK_dead_abovedot
  XK_dead_abovedot,
#else
  0,
#endif
#ifdef XK_dead_abovering
  XK_dead_abovering,
#else
  0,
#endif
#ifdef XK_dead_iota
  XK_dead_iota,
#else
  0,
#endif
#ifdef XK_dead_belowdot
  XK_dead_belowdot,
#else
  0,
#endif
#ifdef XK_dead_voiced_sound
  XK_dead_voiced_sound,
#else
  0,
#endif
#ifdef XK_dead_semivoiced_sound
  XK_dead_semivoiced_sound,
#else
  0,
#endif
#ifdef XK_dead_hook
  XK_dead_hook,
#else
  0,
#endif
#ifdef XK_dead_horn
  XK_dead_horn,
#else
  0,
#endif
};

/* This is a list of Lisp names for special "accent" characters.
   It parallels lispy_accent_codes.  */

static const char *const lispy_accent_keys[] =
{
  "dead-circumflex",
  "dead-grave",
  "dead-tilde",
  "dead-diaeresis",
  "dead-macron",
  "dead-degree",
  "dead-acute",
  "dead-cedilla",
  "dead-breve",
  "dead-ogonek",
  "dead-caron",
  "dead-doubleacute",
  "dead-abovedot",
  "dead-abovering",
  "dead-iota",
  "dead-belowdot",
  "dead-voiced-sound",
  "dead-semivoiced-sound",
  "dead-hook",
  "dead-horn",
};

#ifdef HAVE_ANDROID
#define FUNCTION_KEY_OFFSET 0

/* Mind that Android designates 23 KEYCODE_DPAD_CENTER, but it is
   merely abstruse terminology for the ``select'' key frequently
   located in certain physical keyboards.  */

static const char *const lispy_function_keys[] =
  {
    /* All elements in this array default to 0, except for the few
       function keys that Emacs recognizes.  */
    [111] = "escape",
    [112] = "delete",
    [116] = "scroll",
    [120] = "sysrq",
    [121] = "break",
    [122] = "home",
    [123] = "end",
    [124] = "insert",
    [126] = "media-play",
    [127] = "media-pause",
    [130] = "media-record",
    [131] = "f1",
    [132] = "f2",
    [133] = "f3",
    [134] = "f4",
    [135] = "f5",
    [136] = "f6",
    [137] = "f7",
    [138] = "f8",
    [139] = "f9",
    [140] = "f10",
    [141] = "f11",
    [142] = "f12",
    [143] = "kp-numlock",
    [160] = "kp-ret",
    [164] = "volume-mute",
    [165] = "info",
    [19]  = "up",
    [20]  = "down",
    [211] = "zenkaku-hankaku",
    [213] = "muhenkan",
    [214] = "henkan",
    [215] = "hiragana-katakana",
    [218] = "kana",
    [21]  = "left",
    [223] = "sleep",
    [22]  = "right",
    [23]  = "select",
    [24]  = "volume-up",
    [259] = "help",
    [25]  = "volume-down",
    [268] = "kp-up-left",
    [269] = "kp-down-left",
    [26]  = "power",
    [270] = "kp-up-right",
    [271] = "kp-down-right",
    [272] = "media-skip-forward",
    [273] = "media-skip-backward",
    [277] = "cut",
    [278] = "copy",
    [279] = "paste",
    [285] = "browser-refresh",
    [28]  = "clear",
    [300] = "XF86Forward",
    [4]	  = "XF86Back",
    [61]  = "tab",
    [66]  = "return",
    [67]  = "backspace",
    [82]  = "menu",
    [84]  = "find",
    [85]  = "media-play-pause",
    [86]  = "media-stop",
    [87]  = "media-next",
    [88]  = "media-previous",
    [89]  = "media-rewind",
    [92]  = "prior",
    [93]  = "next",
    [95]  = "mode-change",
  };

#elif defined HAVE_NTGUI
#define FUNCTION_KEY_OFFSET 0x0

const char *const lispy_function_keys[] =
  {
    0,                /* 0                      */

    0,                /* VK_LBUTTON        0x01 */
    0,                /* VK_RBUTTON        0x02 */
    "cancel",         /* VK_CANCEL         0x03 */
    0,                /* VK_MBUTTON        0x04 */

    0, 0, 0,          /*    0x05 .. 0x07        */

    "backspace",      /* VK_BACK           0x08 */
    "tab",            /* VK_TAB            0x09 */

    0, 0,             /*    0x0A .. 0x0B        */

    "clear",          /* VK_CLEAR          0x0C */
    "return",         /* VK_RETURN         0x0D */

    0, 0,             /*    0x0E .. 0x0F        */

    0,                /* VK_SHIFT          0x10 */
    0,                /* VK_CONTROL        0x11 */
    0,                /* VK_MENU           0x12 */
    "pause",          /* VK_PAUSE          0x13 */
    "capslock",       /* VK_CAPITAL        0x14 */
    "kana",           /* VK_KANA/VK_HANGUL 0x15 */
    0,                /*    0x16                */
    "junja",          /* VK_JUNJA          0x17 */
    "final",          /* VK_FINAL          0x18 */
    "kanji",          /* VK_KANJI/VK_HANJA 0x19 */
    0,                /*    0x1A                */
    "escape",         /* VK_ESCAPE         0x1B */
    "convert",        /* VK_CONVERT        0x1C */
    "non-convert",    /* VK_NONCONVERT     0x1D */
    "accept",         /* VK_ACCEPT         0x1E */
    "mode-change",    /* VK_MODECHANGE     0x1F */
    0,                /* VK_SPACE          0x20 */
    "prior",          /* VK_PRIOR          0x21 */
    "next",           /* VK_NEXT           0x22 */
    "end",            /* VK_END            0x23 */
    "home",           /* VK_HOME           0x24 */
    "left",           /* VK_LEFT           0x25 */
    "up",             /* VK_UP             0x26 */
    "right",          /* VK_RIGHT          0x27 */
    "down",           /* VK_DOWN           0x28 */
    "select",         /* VK_SELECT         0x29 */
    "print",          /* VK_PRINT          0x2A */
    "execute",        /* VK_EXECUTE        0x2B */
    "snapshot",       /* VK_SNAPSHOT       0x2C */
    "insert",         /* VK_INSERT         0x2D */
    "delete",         /* VK_DELETE         0x2E */
    "help",           /* VK_HELP           0x2F */

    /* VK_0 thru VK_9 are the same as ASCII '0' thru '9' (0x30 - 0x39) */

    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,

    0, 0, 0, 0, 0, 0, 0, /* 0x3A .. 0x40       */

    /* VK_A thru VK_Z are the same as ASCII 'A' thru 'Z' (0x41 - 0x5A) */

    0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,

    "lwindow",       /* VK_LWIN           0x5B */
    "rwindow",       /* VK_RWIN           0x5C */
    "apps",          /* VK_APPS           0x5D */
    0,               /*    0x5E                */
    "sleep",
    "kp-0",          /* VK_NUMPAD0        0x60 */
    "kp-1",          /* VK_NUMPAD1        0x61 */
    "kp-2",          /* VK_NUMPAD2        0x62 */
    "kp-3",          /* VK_NUMPAD3        0x63 */
    "kp-4",          /* VK_NUMPAD4        0x64 */
    "kp-5",          /* VK_NUMPAD5        0x65 */
    "kp-6",          /* VK_NUMPAD6        0x66 */
    "kp-7",          /* VK_NUMPAD7        0x67 */
    "kp-8",          /* VK_NUMPAD8        0x68 */
    "kp-9",          /* VK_NUMPAD9        0x69 */
    "kp-multiply",   /* VK_MULTIPLY       0x6A */
    "kp-add",        /* VK_ADD            0x6B */
    "kp-separator",  /* VK_SEPARATOR      0x6C */
    "kp-subtract",   /* VK_SUBTRACT       0x6D */
    "kp-decimal",    /* VK_DECIMAL        0x6E */
    "kp-divide",     /* VK_DIVIDE         0x6F */
    "f1",            /* VK_F1             0x70 */
    "f2",            /* VK_F2             0x71 */
    "f3",            /* VK_F3             0x72 */
    "f4",            /* VK_F4             0x73 */
    "f5",            /* VK_F5             0x74 */
    "f6",            /* VK_F6             0x75 */
    "f7",            /* VK_F7             0x76 */
    "f8",            /* VK_F8             0x77 */
    "f9",            /* VK_F9             0x78 */
    "f10",           /* VK_F10            0x79 */
    "f11",           /* VK_F11            0x7A */
    "f12",           /* VK_F12            0x7B */
    "f13",           /* VK_F13            0x7C */
    "f14",           /* VK_F14            0x7D */
    "f15",           /* VK_F15            0x7E */
    "f16",           /* VK_F16            0x7F */
    "f17",           /* VK_F17            0x80 */
    "f18",           /* VK_F18            0x81 */
    "f19",           /* VK_F19            0x82 */
    "f20",           /* VK_F20            0x83 */
    "f21",           /* VK_F21            0x84 */
    "f22",           /* VK_F22            0x85 */
    "f23",           /* VK_F23            0x86 */
    "f24",           /* VK_F24            0x87 */

    0, 0, 0, 0,      /*    0x88 .. 0x8B        */
    0, 0, 0, 0,      /*    0x8C .. 0x8F        */

    "kp-numlock",    /* VK_NUMLOCK        0x90 */
    "scroll",        /* VK_SCROLL         0x91 */
    /* Not sure where the following block comes from.
       Windows headers have NEC and Fujitsu specific keys in
       this block, but nothing generic.  */
    "kp-space",	     /* VK_NUMPAD_CLEAR   0x92 */
    "kp-enter",	     /* VK_NUMPAD_ENTER   0x93 */
    "kp-prior",	     /* VK_NUMPAD_PRIOR   0x94 */
    "kp-next",	     /* VK_NUMPAD_NEXT    0x95 */
    "kp-end",	     /* VK_NUMPAD_END     0x96 */
    "kp-home",	     /* VK_NUMPAD_HOME    0x97 */
    "kp-left",	     /* VK_NUMPAD_LEFT    0x98 */
    "kp-up",	     /* VK_NUMPAD_UP      0x99 */
    "kp-right",	     /* VK_NUMPAD_RIGHT   0x9A */
    "kp-down",	     /* VK_NUMPAD_DOWN    0x9B */
    "kp-insert",     /* VK_NUMPAD_INSERT  0x9C */
    "kp-delete",     /* VK_NUMPAD_DELETE  0x9D */

    0, 0,	     /*    0x9E .. 0x9F        */

    /*
     * VK_L* & VK_R* - left and right Alt, Ctrl and Shift virtual keys.
     * Used only as parameters to GetAsyncKeyState and GetKeyState.
     * No other API or message will distinguish left and right keys this way.
     * 0xA0 .. 0xA5
     */
    0, 0, 0, 0, 0, 0,

    /* Multimedia keys. These are handled as WM_APPCOMMAND, which allows us
       to enable them selectively, and gives access to a few more functions.
       See lispy_multimedia_keys below.  */
    0, 0, 0, 0, 0, 0, 0, /* 0xA6 .. 0xAC        Browser */
    0, 0, 0,             /* 0xAD .. 0xAF         Volume */
    0, 0, 0, 0,          /* 0xB0 .. 0xB3          Media */
    0, 0, 0, 0,          /* 0xB4 .. 0xB7           Apps */

    /* 0xB8 .. 0xC0 "OEM" keys - all seem to be punctuation.  */
    0, 0, 0, 0, 0, 0, 0, 0, 0,

    /* 0xC1 - 0xDA unallocated, 0xDB-0xDF more OEM keys */
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,

    0,               /* 0xE0                   */
    "ax",            /* VK_OEM_AX         0xE1 */
    0,               /* VK_OEM_102        0xE2 */
    "ico-help",      /* VK_ICO_HELP       0xE3 */
    "ico-00",        /* VK_ICO_00         0xE4 */
    0,               /* VK_PROCESSKEY     0xE5 - used by IME */
    "ico-clear",     /* VK_ICO_CLEAR      0xE6 */
    0,               /* VK_PACKET         0xE7  - used to pass Unicode chars */
    0,               /*                   0xE8 */
    "reset",         /* VK_OEM_RESET      0xE9 */
    "jump",          /* VK_OEM_JUMP       0xEA */
    "oem-pa1",       /* VK_OEM_PA1        0xEB */
    "oem-pa2",       /* VK_OEM_PA2        0xEC */
    "oem-pa3",       /* VK_OEM_PA3        0xED */
    "wsctrl",        /* VK_OEM_WSCTRL     0xEE */
    "cusel",         /* VK_OEM_CUSEL      0xEF */
    "oem-attn",      /* VK_OEM_ATTN       0xF0 */
    "finish",        /* VK_OEM_FINISH     0xF1 */
    "copy",          /* VK_OEM_COPY       0xF2 */
    "auto",          /* VK_OEM_AUTO       0xF3 */
    "enlw",          /* VK_OEM_ENLW       0xF4 */
    "backtab",       /* VK_OEM_BACKTAB    0xF5 */
    "attn",          /* VK_ATTN           0xF6 */
    "crsel",         /* VK_CRSEL          0xF7 */
    "exsel",         /* VK_EXSEL          0xF8 */
    "ereof",         /* VK_EREOF          0xF9 */
    "play",          /* VK_PLAY           0xFA */
    "zoom",          /* VK_ZOOM           0xFB */
    "noname",        /* VK_NONAME         0xFC */
    "pa1",           /* VK_PA1            0xFD */
    "oem_clear",     /* VK_OEM_CLEAR      0xFE */
    0 /* 0xFF */
  };

/* Some of these duplicate the "Media keys" on newer keyboards,
   but they are delivered to the application in a different way.  */
static const char *const lispy_multimedia_keys[] =
  {
    0,
    "browser-back",
    "browser-forward",
    "browser-refresh",
    "browser-stop",
    "browser-search",
    "browser-favorites",
    "browser-home",
    "volume-mute",
    "volume-down",
    "volume-up",
    "media-next",
    "media-previous",
    "media-stop",
    "media-play-pause",
    "mail",
    "media-select",
    "app-1",
    "app-2",
    "bass-down",
    "bass-boost",
    "bass-up",
    "treble-down",
    "treble-up",
    "mic-volume-mute",
    "mic-volume-down",
    "mic-volume-up",
    "help",
    "find",
    "new",
    "open",
    "close",
    "save",
    "print",
    "undo",
    "redo",
    "copy",
    "cut",
    "paste",
    "mail-reply",
    "mail-forward",
    "mail-send",
    "spell-check",
    "toggle-dictate-command",
    "mic-toggle",
    "correction-list",
    "media-play",
    "media-pause",
    "media-record",
    "media-fast-forward",
    "media-rewind",
    "media-channel-up",
    "media-channel-down"
  };

#else /* not HAVE_NTGUI */

/* This should be dealt with in XTread_socket now, and that doesn't
   depend on the client system having the Kana syms defined.  See also
   the XK_kana_A case below.  */
#if 0
#ifdef XK_kana_A
static const char *const lispy_kana_keys[] =
  {
    /* X Keysym value */
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,	/* 0x400 .. 0x40f */
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,	/* 0x410 .. 0x41f */
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,	/* 0x420 .. 0x42f */
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,	/* 0x430 .. 0x43f */
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,	/* 0x440 .. 0x44f */
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,	/* 0x450 .. 0x45f */
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,	/* 0x460 .. 0x46f */
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,"overline",0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,	/* 0x480 .. 0x48f */
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,	/* 0x490 .. 0x49f */
    0, "kana-fullstop", "kana-openingbracket", "kana-closingbracket",
    "kana-comma", "kana-conjunctive", "kana-WO", "kana-a",
    "kana-i", "kana-u", "kana-e", "kana-o",
    "kana-ya", "kana-yu", "kana-yo", "kana-tsu",
    "prolongedsound", "kana-A", "kana-I", "kana-U",
    "kana-E", "kana-O", "kana-KA", "kana-KI",
    "kana-KU", "kana-KE", "kana-KO", "kana-SA",
    "kana-SHI", "kana-SU", "kana-SE", "kana-SO",
    "kana-TA", "kana-CHI", "kana-TSU", "kana-TE",
    "kana-TO", "kana-NA", "kana-NI", "kana-NU",
    "kana-NE", "kana-NO", "kana-HA", "kana-HI",
    "kana-FU", "kana-HE", "kana-HO", "kana-MA",
    "kana-MI", "kana-MU", "kana-ME", "kana-MO",
    "kana-YA", "kana-YU", "kana-YO", "kana-RA",
    "kana-RI", "kana-RU", "kana-RE", "kana-RO",
    "kana-WA", "kana-N", "voicedsound", "semivoicedsound",
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,	/* 0x4e0 .. 0x4ef */
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,	/* 0x4f0 .. 0x4ff */
  };
#endif /* XK_kana_A */
#endif /* 0 */

#define FUNCTION_KEY_OFFSET 0xff00

/* You'll notice that this table is arranged to be conveniently
   indexed by X Windows keysym values.  */
#if defined HAVE_NS || !defined HAVE_WINDOW_SYSTEM
/* FIXME: Why are we using X11 keysym values for NS?  */
static
#endif
const char *const lispy_function_keys[] =
  {
    /* X Keysym value */

    0, 0, 0, 0, 0, 0, 0, 0,			      /* 0xff00...0f */
    "backspace", "tab", "linefeed", "clear",
    0, "return", 0, 0,
    0, 0, 0, "pause",				      /* 0xff10...1f */
    0, 0, 0, 0, 0, 0, 0, "escape",
    0, 0, 0, 0,
    0, "kanji", "muhenkan", "henkan",		      /* 0xff20...2f */
    "romaji", "hiragana", "katakana", "hiragana-katakana",
    "zenkaku", "hankaku", "zenkaku-hankaku", "touroku",
    "massyo", "kana-lock", "kana-shift", "eisu-shift",
    "eisu-toggle",				      /* 0xff30...3f */
       0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,   /* 0xff40...4f */

    "home", "left", "up", "right", /* 0xff50 */	/* IsCursorKey */
    "down", "prior", "next", "end",
    "begin", 0, 0, 0, 0, 0, 0, 0,
    "select",			/* 0xff60 */	/* IsMiscFunctionKey */
    "print",
    "execute",
    "insert",
    0,		/* 0xff64 */
    "undo",
    "redo",
    "menu",
    "find",
    "cancel",
    "help",
    "break",			/* 0xff6b */

    0, 0, 0, 0,
    0, 0, 0, 0, "backtab", 0, 0, 0,		/* 0xff70...  */
    0, 0, 0, 0, 0, 0, 0, "kp-numlock",		/* 0xff78...  */
    "kp-space",			/* 0xff80 */	/* IsKeypadKey */
    0, 0, 0, 0, 0, 0, 0, 0,
    "kp-tab",			/* 0xff89 */
    0, 0, 0,
    "kp-enter",			/* 0xff8d */
    0, 0, 0,
    "kp-f1",			/* 0xff91 */
    "kp-f2",
    "kp-f3",
    "kp-f4",
    "kp-home",			/* 0xff95 */
    "kp-left",
    "kp-up",
    "kp-right",
    "kp-down",
    "kp-prior",			/* kp-page-up */
    "kp-next",			/* kp-page-down */
    "kp-end",
    "kp-begin",
    "kp-insert",
    "kp-delete",
    0,				/* 0xffa0 */
    0, 0, 0, 0, 0, 0, 0, 0, 0,
    "kp-multiply",		/* 0xffaa */
    "kp-add",
    "kp-separator",
    "kp-subtract",
    "kp-decimal",
    "kp-divide",		/* 0xffaf */
    "kp-0",			/* 0xffb0 */
    "kp-1",	"kp-2",	"kp-3",	"kp-4",	"kp-5",	"kp-6",	"kp-7",	"kp-8",	"kp-9",
    0,		/* 0xffba */
    0, 0,
    "kp-equal",			/* 0xffbd */
    "f1",			/* 0xffbe */	/* IsFunctionKey */
    "f2",
    "f3", "f4", "f5", "f6", "f7", "f8",	"f9", "f10", /* 0xffc0 */
    "f11", "f12", "f13", "f14", "f15", "f16", "f17", "f18",
    "f19", "f20", "f21", "f22", "f23", "f24", "f25", "f26", /* 0xffd0 */
    "f27", "f28", "f29", "f30", "f31", "f32", "f33", "f34",
    "f35", 0, 0, 0, 0, 0, 0, 0,	/* 0xffe0 */
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,     /* 0xfff0 */
    0, 0, 0, 0, 0, 0, 0, "delete"
  };

/* ISO 9995 Function and Modifier Keys; the first byte is 0xFE.  */
#define ISO_FUNCTION_KEY_OFFSET 0xfe00

static const char *const iso_lispy_function_keys[] =
  {
    0, 0, 0, 0, 0, 0, 0, 0,	/* 0xfe00 */
    0, 0, 0, 0, 0, 0, 0, 0,	/* 0xfe08 */
    0, 0, 0, 0, 0, 0, 0, 0,	/* 0xfe10 */
    0, 0, 0, 0, 0, 0, 0, 0,	/* 0xfe18 */
    "iso-lefttab",		/* 0xfe20 */
    "iso-move-line-up", "iso-move-line-down",
    "iso-partial-line-up", "iso-partial-line-down",
    "iso-partial-space-left", "iso-partial-space-right",
    "iso-set-margin-left", "iso-set-margin-right", /* 0xffe27, 28 */
    "iso-release-margin-left", "iso-release-margin-right",
    "iso-release-both-margins",
    "iso-fast-cursor-left", "iso-fast-cursor-right",
    "iso-fast-cursor-up", "iso-fast-cursor-down",
    "iso-continuous-underline", "iso-discontinuous-underline", /* 0xfe30, 31 */
    "iso-emphasize", "iso-center-object", "iso-enter", /* ... 0xfe34 */
  };

#endif /* not HAVE_NTGUI */

static Lisp_Object Vlispy_mouse_stem;

static const char *const lispy_wheel_names[] =
{
  "wheel-up", "wheel-down", "wheel-left", "wheel-right"
};

/* drag-n-drop events are generated when a set of selected files are
   dragged from another application and dropped onto an Emacs window.  */
static const char *const lispy_drag_n_drop_names[] =
{
  "drag-n-drop"
};

/* An array of symbol indexes of scroll bar parts, indexed by an enum
   scroll_bar_part value.  Note that Qnil corresponds to
   scroll_bar_nowhere and should not appear in Lisp events.  */
static short const scroll_bar_parts[] = {
  SYMBOL_INDEX (Qnil), SYMBOL_INDEX (Qabove_handle), SYMBOL_INDEX (Qhandle),
  SYMBOL_INDEX (Qbelow_handle), SYMBOL_INDEX (Qup), SYMBOL_INDEX (Qdown),
  SYMBOL_INDEX (Qtop), SYMBOL_INDEX (Qbottom), SYMBOL_INDEX (Qend_scroll),
  SYMBOL_INDEX (Qratio), SYMBOL_INDEX (Qbefore_handle),
  SYMBOL_INDEX (Qhorizontal_handle), SYMBOL_INDEX (Qafter_handle),
  SYMBOL_INDEX (Qleft), SYMBOL_INDEX (Qright), SYMBOL_INDEX (Qleftmost),
  SYMBOL_INDEX (Qrightmost), SYMBOL_INDEX (Qend_scroll), SYMBOL_INDEX (Qratio)
};

#ifdef HAVE_WINDOW_SYSTEM
/* An array of symbol indexes of internal border parts, indexed by an enum
   internal_border_part value.  Note that Qnil corresponds to
   internal_border_part_none and should not appear in Lisp events.  */
static short const internal_border_parts[] = {
  SYMBOL_INDEX (Qnil), SYMBOL_INDEX (Qleft_edge),
  SYMBOL_INDEX (Qtop_left_corner), SYMBOL_INDEX (Qtop_edge),
  SYMBOL_INDEX (Qtop_right_corner), SYMBOL_INDEX (Qright_edge),
  SYMBOL_INDEX (Qbottom_right_corner), SYMBOL_INDEX (Qbottom_edge),
  SYMBOL_INDEX (Qbottom_left_corner)
};
#endif

/* A vector, indexed by button number, giving the down-going location
   of currently depressed buttons, both scroll bar and non-scroll bar.

   The elements have the form
     (BUTTON-NUMBER MODIFIER-MASK . REST)
   where REST is the cdr of a position as it would be reported in the event.

   The make_lispy_event function stores positions here to tell the
   difference between click and drag events, and to store the starting
   location to be included in drag events.  */

static Lisp_Object button_down_location;

/* A cons recording the original frame-relative x and y coordinates of
   the down mouse event.  */
static Lisp_Object frame_relative_event_pos;

/* The line-number display width, in columns, at the time of most
   recent down mouse event.  */
static int down_mouse_line_number_width;

/* Information about the most recent up-going button event:  Which
   button, what location, and what time.  */

static int last_mouse_button;
static int last_mouse_x;
static int last_mouse_y;
static Time button_down_time;

/* The number of clicks in this multiple-click.  */

static int double_click_count;

/* If OBJECT is an image with a :map property, check whether (DX, DY)
   falls on a hotspot.  Returns the hotspot id on hit, or POSN unchanged.  */
static Lisp_Object
mlp_image_hotspot_check (Lisp_Object object, int dx, int dy, Lisp_Object posn)
{
#ifdef HAVE_WINDOW_SYSTEM
  if (IMAGEP (object))
    {
      Lisp_Object image_map, hotspot;
      if ((image_map = plist_get (XCDR (object), QCmap),
	   !NILP (image_map))
	  && (hotspot = find_hot_spot (image_map, dx, dy),
	      CONSP (hotspot))
	  && (hotspot = XCDR (hotspot), CONSP (hotspot)))
	return XCAR (hotspot);
    }
#endif
  return posn;
}

/* Mode-line, header-line, or tab-line click.  Fills in posn, object,
   string_info, col/row (character positions), dx/dy/width/height, and
   xret/yret from the window's mode/header/tab line at (WX, WY).  */
static void
mlp_mode_header_line (struct window *w, enum window_part part,
		      int wx, int wy,
		      Lisp_Object *posn, Lisp_Object *object,
		      Lisp_Object *string_info,
		      int *col, int *row,
		      int *dx, int *dy, int *width, int *height,
		      int *xret, int *yret)
{
  Lisp_Object string;
  ptrdiff_t charpos;

  *posn = (part == ON_MODE_LINE ? Qmode_line
	   : (part == ON_TAB_LINE ? Qtab_line
	      : Qheader_line));

  /* mode_line_string takes COL, ROW as pixels and converts
     them to characters.  */
  *col = wx;
  *row = wy;
  string = mode_line_string (w, part, col, row, &charpos,
			     object, dx, dy, width, height);
  if (STRINGP (string))
    *string_info = Fcons (string, make_fixnum (charpos));
  *xret = wx;
  *yret = wy;
}

/* Scroll-bar, border, and divider clicks.  Dispatches on PART
   (ON_VERTICAL_BORDER, ON_VERTICAL_SCROLL_BAR, ON_HORIZONTAL_SCROLL_BAR,
   ON_RIGHT_DIVIDER, ON_BOTTOM_DIVIDER).  Fills in posn, width, dx,
   xret, dy, yret.  */
static void
mlp_scroll_border (struct window *w, enum window_part part, int wx, int wy,
		   Lisp_Object *posn, int *width, int *dx,
		   int *xret, int *dy, int *yret)
{
  if (part == ON_VERTICAL_BORDER)
    {
      *posn = Qvertical_line;
      *width = 1;
      *dx = 0;
      *xret = wx;
      *dy = *yret = wy;
    }
  else if (part == ON_VERTICAL_SCROLL_BAR)
    {
      *posn = Qvertical_scroll_bar;
      *width = WINDOW_SCROLL_BAR_AREA_WIDTH (w);
      *dx = *xret = wx;
      *dy = *yret = wy;
    }
  else if (part == ON_HORIZONTAL_SCROLL_BAR)
    {
      *posn = Qhorizontal_scroll_bar;
      *width = WINDOW_SCROLL_BAR_AREA_HEIGHT (w);
      *dx = *xret = wx;
      *dy = *yret = wy;
    }
  else if (part == ON_RIGHT_DIVIDER)
    {
      *posn = Qright_divider;
      *width = WINDOW_RIGHT_DIVIDER_WIDTH (w);
      *dx = *xret = wx;
      *dy = *yret = wy;
    }
  else /* ON_BOTTOM_DIVIDER */
    {
      *posn = Qbottom_divider;
      *width = WINDOW_BOTTOM_DIVIDER_WIDTH (w);
      *dx = *xret = wx;
      *dy = *yret = wy;
    }
}

/* Left or right fringe click.  LEFT_P selects the fringe side.
   Fills in posn, col, dx, dy, xret, yret.  */
static void
mlp_fringes (struct window *w, bool left_p, int wx, int wy,
	     Lisp_Object *posn, int *col, int *dx, int *dy,
	     int *xret, int *yret)
{
  *posn = left_p ? Qleft_fringe : Qright_fringe;
  *col = 0;
  *xret = wx;
  if (left_p)
    *dx = wx - (WINDOW_HAS_FRINGES_OUTSIDE_MARGINS (w)
		? 0 : window_box_width (w, LEFT_MARGIN_AREA));
  else
    *dx = wx
      - window_box_width (w, LEFT_MARGIN_AREA)
      - window_box_width (w, TEXT_AREA)
      - (WINDOW_HAS_FRINGES_OUTSIDE_MARGINS (w)
	 ? window_box_width (w, RIGHT_MARGIN_AREA)
	 : 0);
  *dy = *yret = wy - WINDOW_TAB_LINE_HEIGHT (w) - WINDOW_HEADER_LINE_HEIGHT (w);
}

/* Post-dispatch buffer-position pass.  Called after region handlers
   for clicks in the text area, fringes, margins, or vertical scroll
   bar.  Fills in textpos, posn, object, string_info, col, row, dx,
   dy, width, height from buffer_posn_from_coords.  */
static void
mlp_buffer_posn_pass (struct window *w, enum window_part part,
		      int mx, int wy, int xret,
		      ptrdiff_t *textpos,
		      int *col, int *row,
		      int *dx, int *dy, int *width, int *height,
		      Lisp_Object *posn, Lisp_Object *string_info,
		      Lisp_Object *object)
{
  Lisp_Object string2, object2 = Qnil;
  struct display_pos p;
  int dx2, dy2;
  int width2, height2;
  int x2
    = (part == ON_TEXT) ? xret
    : (part == ON_RIGHT_FRINGE || part == ON_RIGHT_MARGIN
       || (part == ON_VERTICAL_SCROLL_BAR
	   && WINDOW_HAS_VERTICAL_SCROLL_BAR_ON_RIGHT (w)))
    ? (mx - window_box_left (w, TEXT_AREA))
    : 0;
  int y2 = wy;

  string2 = buffer_posn_from_coords (w, &x2, &y2, &p,
				     &object2, &dx2, &dy2,
				     &width2, &height2);
  *textpos = CHARPOS (p.pos);
  if (*col < 0) *col = x2;
  if (*row < 0) *row = y2;
  if (*dx < 0) *dx = dx2;
  if (*dy < 0) *dy = dy2;
  if (*width < 0) *width = width2;
  if (*height < 0) *height = height2;

  if (NILP (*posn))
    {
      *posn = make_fixnum (*textpos);
      if (STRINGP (string2))
	*string_info = Fcons (string2,
			      make_fixnum (CHARPOS (p.string_pos)));
    }
  if (NILP (*object))
    *object = object2;
}

/* Left/right margin click.  Fills in posn, object, string_info,
   col, row, dx, dy, width, height, xret, yret from the window's
   margin area at pixel coordinates (WX, WY) relative to the window
   corner.  */
static void
mlp_margins (struct window *w, enum window_part part,
	     int wx, int wy,
	     Lisp_Object *posn, Lisp_Object *object,
	     Lisp_Object *string_info,
	     int *col, int *row,
	     int *dx, int *dy, int *width, int *height,
	     int *xret, int *yret)
{
  Lisp_Object string;
  ptrdiff_t charpos;

  *posn = (part == ON_LEFT_MARGIN) ? Qleft_margin : Qright_margin;
  *col = wx;
  *row = wy;
  string = marginal_area_string (w, part, col, row, &charpos,
				 object, dx, dy, width, height);
  if (STRINGP (string))
    *string_info = Fcons (string, make_fixnum (charpos));
  *xret = wx;
  *yret = wy - WINDOW_TAB_LINE_HEIGHT (w) - WINDOW_HEADER_LINE_HEIGHT (w);
}

/* If F is a GUI frame with internal borders and POSN hasn't been
   claimed yet, check whether (X, Y) falls on an internal border
   part.  Returns the border-part symbol on hit, or POSN unchanged.  */
static Lisp_Object
mlp_internal_border (struct frame *f, int x, int y, Lisp_Object posn)
{
#ifdef HAVE_WINDOW_SYSTEM
  if (FRAME_WINDOW_P (f)
      && FRAME_LIVE_P (f)
      && NILP (posn)
      && FRAME_INTERNAL_BORDER_WIDTH (f) > 0
      && !NILP (get_frame_param (f, Qdrag_internal_border)))
    {
      enum internal_border_part part
	= frame_internal_border_part (f, x, y);
      return builtin_lisp_symbol (internal_border_parts[part]);
    }
#endif
  return posn;
}

/* Frame preamble: window_from_coordinates + tab/tool/menu-bar detection.
   Determines window_or_frame, part, and initial posn (set to a bar symbol
   if the click is on a tab-bar, tool-bar, or menu-bar).  TRACK_MOUSE is
   the global — passed explicitly so imp-6.3 Scheme ports don't need
   implicit C-global access.  */
static void
mlp_frame_preamble (struct frame *f, int mx, int my,
		    Lisp_Object track_mouse_val,
		    Lisp_Object *window_or_frame,
		    enum window_part *part,
		    Lisp_Object *posn)
{
  *window_or_frame = (f != NULL
		      ? window_from_coordinates (f, mx, my, part,
						 false, true, true)
		      : Qnil);
  *posn = Qnil;

#ifdef HAVE_WINDOW_SYSTEM
  bool tool_bar_p = false;
  bool menu_bar_p = false;

  if (f && ((WINDOWP (f->tab_bar_window)
	     && EQ (*window_or_frame, f->tab_bar_window))
#ifndef HAVE_EXT_TOOL_BAR
	    || (WINDOWP (f->tool_bar_window)
		&& EQ (*window_or_frame, f->tool_bar_window))
#endif
	    ))
    {
      if (NILP (track_mouse_val) || EQ (track_mouse_val, Qt))
	*posn = EQ (*window_or_frame, f->tab_bar_window) ? Qtab_bar : Qtool_bar;
      *window_or_frame = Qnil;
    }

  if (f && FRAME_TERMINAL (f)->toolkit_position_hook)
    {
      FRAME_TERMINAL (f)->toolkit_position_hook (f, mx, my, &menu_bar_p,
						 &tool_bar_p);
      if (NILP (track_mouse_val) || EQ (track_mouse_val, Qt))
	{
	  if (menu_bar_p)
	    *posn = Qmenu_bar;
	  else if (tool_bar_p)
	    *posn = Qtool_bar;
	}
    }
#endif
  if (f
      && !FRAME_WINDOW_P (f)
      && FRAME_TAB_BAR_LINES (f) > 0
      && my >= FRAME_MENU_BAR_LINES (f)
      && my < FRAME_MENU_BAR_LINES (f) + FRAME_TAB_BAR_LINES (f))
    {
      *posn = Qtab_bar;
      *window_or_frame = Qnil;
    }
}

/* X and Y are frame-relative coordinates for a click or wheel event.
   Return a Lisp-style event list.  */

static Lisp_Object
make_lispy_position (struct frame *f, Lisp_Object x, Lisp_Object y,
		     Time t)
{
  /* imp-6.4 — C body replaced by SCM_CALL_4 into the Scheme
     orchestrator in (emacs lispy-position) make-lispy-position.
     The mlp_* helpers remain as C code called by the adapter
     DEFUNs (--mlp-*), which the Scheme orchestrator uses.  */
  static SCM proc = SCM_UNDEFINED;
  Lisp_Object frame_obj;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs lispy-position",
			     "make-lispy-position");
  if (f)
    XSETFRAME (frame_obj, f);
  else
    frame_obj = Qnil;
  return SCM_CALL_4 (proc, frame_obj, x, y, INT_TO_INTEGER (t));
}

/* Return non-zero if F is a GUI frame that uses some toolkit-managed
   menu bar.  This really means that Emacs draws and manages the menu
   bar as part of its normal display, and therefore can compute its
   geometry.  */
static bool
toolkit_menubar_in_use (struct frame *f)
{
#ifdef HAVE_EXT_MENU_BAR
  return !(!FRAME_WINDOW_P (f));
#else
  return false;
#endif
}

/* Build the part of Lisp event which represents scroll bar state from
   EV.  TYPE is one of Qvertical_scroll_bar or Qhorizontal_scroll_bar.  */

static Lisp_Object
make_scroll_bar_position (struct input_event *ev, Lisp_Object type)
{
  return list5 (ev->frame_or_window, type, Fcons (ev->x, ev->y),
		INT_TO_INTEGER (ev->timestamp),
		builtin_lisp_symbol (scroll_bar_parts[ev->part]));
}

#if defined HAVE_WINDOW_SYSTEM && !defined HAVE_EXT_MENU_BAR

/* Return whether or not the coordinates X and Y are inside the
   box of the menu-bar window of frame F.  */

static bool
coords_in_menu_bar_window (struct frame *f, int x, int y)
{
  struct window *window;

  if (!WINDOWP (f->menu_bar_window))
    return false;

  window = XWINDOW (f->menu_bar_window);

  return (y >= WINDOW_TOP_EDGE_Y (window)
	  && x >= WINDOW_LEFT_EDGE_X (window)
	  && y <= WINDOW_BOTTOM_EDGE_Y (window)
	  && x <= WINDOW_RIGHT_EDGE_X (window));
}

#endif

#ifdef HAVE_WINDOW_SYSTEM

/* Return whether or not the coordinates X and Y are inside the
   tab-bar window of the given frame F.  */

static bool
coords_in_tab_bar_window (struct frame *f, int x, int y)
{
  struct window *window;

  if (!WINDOWP (f->tab_bar_window))
    return false;

  window = XWINDOW (f->tab_bar_window);

  return (y >= WINDOW_TOP_EDGE_Y (window)
	  && x >= WINDOW_LEFT_EDGE_X (window)
	  && y <= WINDOW_BOTTOM_EDGE_Y (window)
	  && x <= WINDOW_RIGHT_EDGE_X (window));
}

#endif /* HAVE_WINDOW_SYSTEM */

static void
save_line_number_display_width (struct input_event *event)
{
  struct window *w;
  int pixel_width;

  if (WINDOWP (event->frame_or_window))
    w = XWINDOW (event->frame_or_window);
  else if (FRAMEP (event->frame_or_window))
    w = XWINDOW (XFRAME (event->frame_or_window)->selected_window);
  else
    w = XWINDOW (selected_window);
  line_number_display_width (w, &down_mouse_line_number_width, &pixel_width);
}

/* Return non-zero if the change of position from START_POS to END_POS
   is likely to be the effect of horizontal scrolling due to a change
   in line-number width produced by redisplay between two mouse
   events, like mouse-down followed by mouse-up, at those positions.
   This is used to decide whether to converts mouse-down followed by
   mouse-up event into a mouse-drag event.  */
static bool
line_number_mode_hscroll (Lisp_Object start_pos, Lisp_Object end_pos)
{
  if (!EQ (Fcar (start_pos), Fcar (end_pos)) /* different window */
      || list_length (start_pos) < 7	     /* no COL/ROW info */
      || list_length (end_pos) < 7)
    return false;

  Lisp_Object start_col_row = Fnth (make_fixnum (6), start_pos);
  Lisp_Object end_col_row = Fnth (make_fixnum (6), end_pos);
  Lisp_Object window = Fcar (end_pos);
  int col_width, pixel_width;
  Lisp_Object start_col, end_col;
  struct window *w;
  if (!WINDOW_VALID_P (window))
    {
      if (WINDOW_LIVE_P (window))
	window = XFRAME (window)->selected_window;
      else
	window = selected_window;
    }
  w = XWINDOW (window);
  line_number_display_width (w, &col_width, &pixel_width);
  start_col = Fcar (start_col_row);
  end_col = Fcar (end_col_row);
  return EQ (start_col, end_col)
	 && down_mouse_line_number_width >= 0
	 && col_width != down_mouse_line_number_width;
}

/* Given a struct input_event, build the lisp event which represents
   it.  If EVENT is 0, build a mouse movement event from the mouse
   movement buffer, which should have a movement event in it.

   Note that events must be passed to this function in the order they
   are received; this function stores the location of button presses
   in order to build drag events when the button is released.  */

DEFUN ("--make-lispy-position", Fmake_lispy_position, Smake_lispy_position,
       4, 4, 0,
       doc: /* Build a mouse-click position list for frame-or-window FOW,
pixel coords X and Y, and timestamp T.  T arrives from
--ie-timestamp (INT_TO_INTEGER) and may be a bignum on 32-bit
fixnum builds.  Delegates to (emacs lispy-position).  */)
  (Lisp_Object fow, Lisp_Object x, Lisp_Object y, Lisp_Object t)
{
  struct frame *f = XFRAME (fow);
  return make_lispy_position (f, x, y, scm_to_intmax (t));
}

/* imp-8.1.1 — Cache-slot accessors for modify_event_symbol Scheme port.
 *
 * CACHE-ID is a fixnum selecting one of 7 cache slots:
 *   0 = accent_key_syms    1 = func_key_syms     2 = mouse_syms
 *   3 = wheel_syms          4 = drag_n_drop_syms  5 = pinch_syms
 *   6 = system_key_syms (per-kboard KVAR)
 */

enum mes_cache_id {
  MES_CACHE_ACCENT = 0,
  MES_CACHE_FUNC,
  MES_CACHE_MOUSE,
  MES_CACHE_WHEEL,
  MES_CACHE_DRAG_N_DROP,
  MES_CACHE_PINCH,
  MES_CACHE_SYSTEM
};

DEFUN ("--mes-cache-get", Fmes_cache_get, Smes_cache_get, 1, 1, 0,
       doc: /* Return the Lisp_Object stored in the modify-event-symbol
cache slot identified by CACHE-ID (fixnum 0–6).  */)
  (Lisp_Object cache_id)
{
  switch (XFIXNUM (cache_id))
    {
    case MES_CACHE_ACCENT:      return accent_key_syms;
    case MES_CACHE_FUNC:        return func_key_syms;
    case MES_CACHE_MOUSE:       return mouse_syms;
    case MES_CACHE_WHEEL:       return wheel_syms;
    case MES_CACHE_DRAG_N_DROP: return drag_n_drop_syms;
    case MES_CACHE_PINCH:       return pinch_syms;
    case MES_CACHE_SYSTEM:
      {
	Lisp_Object *sys = &KVAR (current_kboard, system_key_syms);
	if (NILP (*sys))
	  *sys = Fcons (Qnil, Qnil);
	return *sys;
      }
    default:
      return Qnil;
    }
}

DEFUN ("--mes-cache-set", Fmes_cache_set, Smes_cache_set, 2, 2, 0,
       doc: /* Write VALUE into the modify-event-symbol cache slot
identified by CACHE-ID (fixnum 0–6).  Returns nil.  */)
  (Lisp_Object cache_id, Lisp_Object value)
{
  switch (XFIXNUM (cache_id))
    {
    case MES_CACHE_ACCENT:      accent_key_syms = value;      break;
    case MES_CACHE_FUNC:        func_key_syms = value;        break;
    case MES_CACHE_MOUSE:       mouse_syms = value;           break;
    case MES_CACHE_WHEEL:       wheel_syms = value;           break;
    case MES_CACHE_DRAG_N_DROP: drag_n_drop_syms = value;     break;
    case MES_CACHE_PINCH:       pinch_syms = value;           break;
    case MES_CACHE_SYSTEM:
      kset_system_key_syms (current_kboard, value);
      break;
    default:
      break;
    }
  return Qnil;
}

/* imp-8.1.3 — get_keysym_name DEFUN.
 *
 * Wraps the X11 get_keysym_name (src/xterm.c) for the Scheme
 * modify-event-symbol body's NILP(value) fallback clause.
 * Returns a string on X11/W32/NS, Qnil otherwise.  */

DEFUN ("--get-keysym-name", Fget_keysym_name, Sget_keysym_name, 1, 1, 0,
       doc: /* Return the keysym name string for SYMBOL-NUM, or nil.

Wraps get_keysym_name from X11 / W32 / NS.  Returns nil on
non-windowing builds.  */)
  (Lisp_Object symbol_num)
{
#ifdef HAVE_WINDOW_SYSTEM
  char *name = get_keysym_name (XFIXNUM (symbol_num));
  if (name)
    return build_string (name);
#endif
  return Qnil;
}

DEFUN ("--make-scroll-bar-position", Fmake_scroll_bar_position,
       Smake_scroll_bar_position, 6, 6, 0,
       doc: /* Build a scroll-bar position list.

FOW is the frame-or-window.  X, Y are pixel coords.  TIMESTAMP and
PART are Lisp_Objects from the input-event accessors (already
INT_TO_INTEGER'd by --ie-timestamp / --ie-part).  TYPE is the scroll
bar type symbol, e.g. `vertical-scroll-bar'.  */)
  (Lisp_Object fow, Lisp_Object x, Lisp_Object y,
   Lisp_Object timestamp, Lisp_Object part, Lisp_Object type)
{
  return list5 (fow, type, Fcons (x, y),
		timestamp,
		builtin_lisp_symbol (scroll_bar_parts[XFIXNUM (part)]));
}

DEFUN ("--ensure-mouse-syms-size", Fensure_mouse_syms_size,
       Sensure_mouse_syms_size, 1, 1, 0,
       doc: /* Ensure mouse_syms has at least N entries.

Resizes the mouse_syms cache vector if needed.  Called from Scheme
before modify-event-symbol to guarantee the cache slot is sized.  */)
  (Lisp_Object n)
{
  int c = XFIXNUM (n);
  if (c >= ASIZE (mouse_syms))
    mouse_syms = larger_vector (mouse_syms,
				c - ASIZE (mouse_syms) + 1,
				-1);
  return make_fixnum (ASIZE (mouse_syms));
}

/* mlp_* adapter DEFUNs — imp-6.3.
 *
 * Each wraps one decomposed mlp_* C helper, packing out-params into a
 * single Lisp list return so Scheme handlers get clean
 * single-value-call interfaces.  Value-return helpers (internal-border,
 * image-hotspot) pass through directly; multi-out helpers use a list
 * of (posn object string-info col row dx dy width height xret yret).  */

/* imp-9 — consolidated mlp adapter.  Region-id 0–8 dispatches to the
   corresponding mlp_* C helper.  Takes up to 6 payload args after
   region-id; unused slots are #nil and ignored.  */
DEFUN ("--mlp-dispatch", Fmlp_dispatch, Smlp_dispatch, 7, 7, 0,
       doc: /* Dispatch to mlp_* helper for REGION (fixnum 0–8).

REGION: 0=text-area-offset 1=internal-border 2=image-hotspot
        3=frame-preamble  4=fringes  5=scroll-border
        6=mode-header-line 7=margins 8=buffer-posn-pass

A1–A6 are the payload args.  Unused slots are ignored.  */)
  (Lisp_Object region, Lisp_Object a1, Lisp_Object a2,
   Lisp_Object a3, Lisp_Object a4, Lisp_Object a5,
   Lisp_Object a6)
{
  switch (XFIXNUM (region))
    {
    case 0:  /* text-area-offset: w mx my */
      {
	struct window *w = XWINDOW (a1);
	int xret = XFIXNUM (a2) - window_box_left (w, TEXT_AREA);
	int yret = (XFIXNUM (a3) - WINDOW_TOP_EDGE_Y (w)
		    - WINDOW_TAB_LINE_HEIGHT (w) - WINDOW_HEADER_LINE_HEIGHT (w));
	return Fcons (make_fixnum (xret), make_fixnum (yret));
      }
    case 1:  /* internal-border: f x y posn */
      return mlp_internal_border (XFRAME (a1), XFIXNUM (a2), XFIXNUM (a3), a4);
    case 2:  /* image-hotspot: object dx dy posn */
      return mlp_image_hotspot_check (a1, XFIXNUM (a2), XFIXNUM (a3), a4);
    case 3:  /* frame-preamble: f_or_nil x y track_mouse */
      {
	struct frame *f = NILP (a1) ? NULL : XFRAME (a1);
	Lisp_Object window_or_frame, posn;
	enum window_part part;
	mlp_frame_preamble (f, XFIXNUM (a2), XFIXNUM (a3), a4,
			    &window_or_frame, &part, &posn);
	return list3 (window_or_frame, make_fixnum (part), posn);
      }
    case 4:  /* fringes: w left? mx my posn */
      {
	struct window *w = XWINDOW (a1);
	int wx = XFIXNUM (a3) - WINDOW_LEFT_EDGE_X (w);
	int wy = XFIXNUM (a4) - WINDOW_TOP_EDGE_Y (w);
	Lisp_Object posn = a5;
	int col, dx, dy, xret, yret;
	mlp_fringes (w, !NILP (a2), wx, wy, &posn, &col, &dx, &dy, &xret, &yret);
	return listn (6, posn, make_fixnum (col), make_fixnum (dx),
		      make_fixnum (dy), make_fixnum (xret), make_fixnum (yret));
      }
    case 5:  /* scroll-border: w part mx my */
      {
	struct window *w = XWINDOW (a1);
	int wx = XFIXNUM (a3) - WINDOW_LEFT_EDGE_X (w);
	int wy = XFIXNUM (a4) - WINDOW_TOP_EDGE_Y (w);
	Lisp_Object posn;
	int width, dx, xret, dy, yret;
	mlp_scroll_border (w, XFIXNUM (a2), wx, wy,
			   &posn, &width, &dx, &xret, &dy, &yret);
	return listn (6, posn, make_fixnum (width), make_fixnum (dx),
		      make_fixnum (xret), make_fixnum (dy), make_fixnum (yret));
      }
    case 6:  /* mode-header-line: w part mx my */
      {
	struct window *w = XWINDOW (a1);
	int wx = XFIXNUM (a3) - WINDOW_LEFT_EDGE_X (w);
	int wy = XFIXNUM (a4) - WINDOW_TOP_EDGE_Y (w);
	Lisp_Object posn, object = Qnil, string_info = Qnil;
	int col, row, dx, dy, width, height, xret, yret;
	mlp_mode_header_line (w, XFIXNUM (a2), wx, wy,
			      &posn, &object, &string_info,
			      &col, &row, &dx, &dy, &width, &height, &xret, &yret);
	return listn (10, posn, object, string_info,
		      make_fixnum (col), make_fixnum (row),
		      make_fixnum (dx), make_fixnum (dy),
		      make_fixnum (width), make_fixnum (height),
		      make_fixnum (xret), make_fixnum (yret));
      }
    case 7:  /* margins: w part mx my */
      {
	struct window *w = XWINDOW (a1);
	int wx = XFIXNUM (a3) - WINDOW_LEFT_EDGE_X (w);
	int wy = XFIXNUM (a4) - WINDOW_TOP_EDGE_Y (w);
	Lisp_Object posn, object = Qnil, string_info = Qnil;
	int col, row, dx, dy, width, height, xret, yret;
	mlp_margins (w, XFIXNUM (a2), wx, wy,
		     &posn, &object, &string_info,
		     &col, &row, &dx, &dy, &width, &height, &xret, &yret);
	return listn (11, posn, object, string_info,
		      make_fixnum (col), make_fixnum (row),
		      make_fixnum (dx), make_fixnum (dy),
		      make_fixnum (width), make_fixnum (height),
		      make_fixnum (xret), make_fixnum (yret));
      }
    case 8:  /* buffer-posn-pass: w part mx my xret posn */
      {
	struct window *w = XWINDOW (a1);
	int wy = XFIXNUM (a4) - WINDOW_TOP_EDGE_Y (w);
	ptrdiff_t textpos = 0;
	int col = -1, row = -1, dx = -1, dy = -1, width = -1, height = -1;
	Lisp_Object posn = a6, object = Qnil, string_info = Qnil;
	mlp_buffer_posn_pass (w, XFIXNUM (a2), XFIXNUM (a3), wy,
			      XFIXNUM (a5),
			      &textpos, &col, &row, &dx, &dy, &width, &height,
			      &posn, &string_info, &object);
	return listn (10, make_fixnum (textpos), posn, object, string_info,
		      make_fixnum (col), make_fixnum (row),
		      make_fixnum (dx), make_fixnum (dy),
		      make_fixnum (width), make_fixnum (height));
      }
    default:
      return Qnil;
    }
}

DEFUN ("--menu-bar-touch-id", Fmenu_bar_touch_id, Smenu_bar_touch_id,
       0, 0, 0,
       doc: /* Return the current value of menu_bar_touch_id.

This is the file-static Lisp_Object mutated by TOUCHSCREEN_BEGIN
(to store the touch ID that landed on the menu bar) and read by
TOUCHSCREEN_UPDATE (to filter those touches) and TOUCHSCREEN_END
(to activate the menu-bar item on release).  */)
  (void)
{
  return menu_bar_touch_id;
}

DEFUN ("--set-menu-bar-touch-id", Fset_menu_bar_touch_id,
       Sset_menu_bar_touch_id, 1, 1, 0,
       doc: /* Set menu_bar_touch_id to VAL.  See --menu-bar-touch-id.  */)
  (Lisp_Object val)
{
  menu_bar_touch_id = val;
  return Qnil;
}

DEFUN ("--coords-in-menu-bar-window", Fcoords_in_menu_bar_window,
       Scoords_in_menu_bar_window, 3, 3, 0,
       doc: /* Return t if frame-relative (X, Y) lies inside FRAME's
menu-bar window.

FRAME must be a live frame.  X and Y are fixnums (pixel coords).
Returns nil on platforms without a non-toolkit menu bar
(e.g. toolkit builds, no-X builds).  */)
  (Lisp_Object frame, Lisp_Object x, Lisp_Object y)
{
#if defined HAVE_WINDOW_SYSTEM && !defined HAVE_EXT_MENU_BAR
  CHECK_LIVE_FRAME (frame);
  return coords_in_menu_bar_window (XFRAME (frame),
				    XFIXNUM (x), XFIXNUM (y))
    ? Qt : Qnil;
#else
  return Qnil;
#endif
}

DEFUN ("--tab-bar-enrich-position", Ftab_bar_enrich_position,
       Stab_bar_enrich_position, 4, 4, 0,
       doc: /* If frame-relative (X, Y) falls inside FRAME's tab bar,
enrich POSITION with the tab-bar item's propertized string.

FRAME must be a live frame.  X and Y are fixnums (pixel coords).
POSITION is the result of make-lispy-position.  Returns the enriched
position (with propertized-string object appended) if a tab-bar
item exists at (X, Y); returns POSITION unchanged otherwise.

On builds without HAVE_WINDOW_SYSTEM, always returns POSITION
unchanged.  */)
  (Lisp_Object frame, Lisp_Object x, Lisp_Object y,
   Lisp_Object position)
{
#ifdef HAVE_WINDOW_SYSTEM
  struct frame *f = XFRAME (frame);
  int ix = XFIXNUM (x), iy = XFIXNUM (y);
  int tab_bar_item;
  bool close;

  CHECK_LIVE_FRAME (frame);

  if (coords_in_tab_bar_window (f, ix, iy)
      && get_tab_bar_item_kbd (f, ix, iy, &tab_bar_item, &close) >= 0)
    {
      Lisp_Object caption
	= Fcopy_sequence (AREF (f->tab_bar_items,
				tab_bar_item + TAB_BAR_ITEM_CAPTION));
      AUTO_LIST2 (props, Qmenu_item,
		  list3 (AREF (f->tab_bar_items,
			       tab_bar_item + TAB_BAR_ITEM_KEY),
			 AREF (f->tab_bar_items,
			       tab_bar_item + TAB_BAR_ITEM_BINDING),
			 close ? Qt : Qnil));
      Fadd_text_properties (make_fixnum (0),
			    make_fixnum (SCHARS (caption)),
			    props, caption);
      caption = Fcons (caption, make_fixnum (0));
      return nconc2 (position, Fcons (caption, Qnil));
    }
#endif
  return position;
}

DEFUN ("--menu-bar-touch-consume-p", Fmenu_bar_touch_consume_p,
       Smenu_bar_touch_consume_p, 1, 1, 0,
       doc: /* Return t if TOUCH-ID matches menu_bar_touch_id,
clearing the stored ID as a side effect.  Returns nil otherwise.

The caller must short-circuit: if this returns t, the touch
has been consumed (menu_bar_touch_id is now nil) and the
caller should either emit a menu-bar activation event or
return nil — but must NOT fall through to a normal end event.
If this returns nil, the caller proceeds with the normal
touch-end path.

On platforms without a non-toolkit menu bar, always returns nil.  */)
  (Lisp_Object touch_id)
{
#if defined HAVE_WINDOW_SYSTEM && !defined HAVE_EXT_MENU_BAR
  if (EQ (menu_bar_touch_id, touch_id))
    {
      menu_bar_touch_id = Qnil;
      return Qt;
    }
#endif
  return Qnil;
}

DEFUN ("--menu-bar-touch-activate", Fmenu_bar_touch_activate,
       Smenu_bar_touch_activate, 5, 5, 0,
       doc: /* Activate the menu-bar item at frame-relative (X, Y)
on FRAME and return the event (ITEM . POSITION).

Call only after --menu-bar-touch-consume-p returned t.
FRAME is a live frame.  X and Y are fixnum pixel coords.
FOW is the original event->frame_or_window (for position building).
TIMESTAMP is the event timestamp (already INT_TO_INTEGER'd).

Returns nil if no menu-bar item is found at (X, Y)
(e.g. finger slid off, menu-bar hidden between BEGIN and END).
On non-menu-bar platforms, always returns nil.  */)
  (Lisp_Object frame, Lisp_Object x, Lisp_Object y,
   Lisp_Object fow, Lisp_Object timestamp)
{
#if defined HAVE_WINDOW_SYSTEM && !defined HAVE_EXT_MENU_BAR
  struct frame *f = XFRAME (frame);
  int ix = XFIXNUM (x), iy = XFIXNUM (y);
  int column, row, dummy;

  CHECK_LIVE_FRAME (frame);

  if (NILP (f->menu_bar_window))
    return Qnil;

  x_y_to_hpos_vpos (XWINDOW (f->menu_bar_window), ix, iy,
		    &column, &row, NULL, NULL, &dummy);

  if (row >= 0 && row < FRAME_MENU_BAR_LINES (f))
    {
      Lisp_Object items = FRAME_MENU_BAR_ITEMS (f);
      Lisp_Object item = Qnil;
      int i;
      for (i = 0; i < ASIZE (items); i += 4)
	{
	  Lisp_Object str = AREF (items, i + 1);
	  Lisp_Object pos = AREF (items, i + 3);
	  if (NILP (str))
	    break;
	  if (column >= XFIXNUM (pos)
	      && column < XFIXNUM (pos) + SCHARS (str))
	    {
	      item = AREF (items, i);
	      break;
	    }
	}

      if (!NILP (item))
	{
	  Lisp_Object position
	    = list4 (fow, Qmenu_bar,
		     Fcons (x, y),
		     timestamp);
	  return list2 (item, position);
	}
    }
#endif
  return Qnil;
}

/* imp-7.1 — file-static getter/setter DEFUNs for double-click
   and drag state.  8 statics, 16 DEFUNs.  C retains ownership;
   Scheme reads/writes through these wrappers (no Scheme-side
   mirror record).  Used by imp-7.2 wheel double-click detection
   and imp-7.5 MOUSE_CLICK port.  */

DEFUN ("--button-down-location", Fbutton_down_location,
       Sbutton_down_location, 0, 0, 0,
       doc: /* Return the value of button_down_location.

A Lisp_Object vector recording the position of the most recent
mouse-press event.  Used for drag-event position computation.  */)
  (void)
{
  return button_down_location;
}

DEFUN ("--set-button-down-location", Fset_button_down_location,
       Sset_button_down_location, 1, 1, 0,
       doc: /* Set button_down_location to VAL.  */)
  (Lisp_Object val)
{
  button_down_location = val;
  return Qnil;
}

DEFUN ("--frame-relative-event-pos", Fframe_relative_event_pos,
       Sframe_relative_event_pos, 0, 0, 0,
       doc: /* Return the value of frame_relative_event_pos.

A cons (X . Y) recording the original frame-relative coordinates
of the most recent mouse-down event.  */)
  (void)
{
  return frame_relative_event_pos;
}

DEFUN ("--set-frame-relative-event-pos", Fset_frame_relative_event_pos,
       Sset_frame_relative_event_pos, 1, 1, 0,
       doc: /* Set frame_relative_event_pos to VAL.  */)
  (Lisp_Object val)
{
  frame_relative_event_pos = val;
  return Qnil;
}

DEFUN ("--down-mouse-line-number-width", Fdown_mouse_line_number_width,
       Sdown_mouse_line_number_width, 0, 0, 0,
       doc: /* Return down_mouse_line_number_width as a fixnum.  */)
  (void)
{
  return make_fixnum (down_mouse_line_number_width);
}

DEFUN ("--set-down-mouse-line-number-width",
       Fset_down_mouse_line_number_width,
       Sset_down_mouse_line_number_width, 1, 1, 0,
       doc: /* Set down_mouse_line_number_width to VAL (a fixnum).  */)
  (Lisp_Object val)
{
  CHECK_FIXNUM (val);
  down_mouse_line_number_width = XFIXNUM (val);
  return Qnil;
}

DEFUN ("--last-mouse-button", Flast_mouse_button,
       Slast_mouse_button, 0, 0, 0,
       doc: /* Return last_mouse_button as a fixnum.

Distinguishes wheel from mouse button by negative values
(wheel: -(1 + symbol_num)).  */)
  (void)
{
  return make_fixnum (last_mouse_button);
}

DEFUN ("--set-last-mouse-button", Fset_last_mouse_button,
       Sset_last_mouse_button, 1, 1, 0,
       doc: /* Set last_mouse_button to VAL (a fixnum).  */)
  (Lisp_Object val)
{
  CHECK_FIXNUM (val);
  last_mouse_button = XFIXNUM (val);
  return Qnil;
}

DEFUN ("--last-mouse-x", Flast_mouse_x,
       Slast_mouse_x, 0, 0, 0,
       doc: /* Return last_mouse_x as a fixnum.  */)
  (void)
{
  return make_fixnum (last_mouse_x);
}

DEFUN ("--set-last-mouse-x", Fset_last_mouse_x,
       Sset_last_mouse_x, 1, 1, 0,
       doc: /* Set last_mouse_x to VAL (a fixnum).  */)
  (Lisp_Object val)
{
  CHECK_FIXNUM (val);
  last_mouse_x = XFIXNUM (val);
  return Qnil;
}

DEFUN ("--last-mouse-y", Flast_mouse_y,
       Slast_mouse_y, 0, 0, 0,
       doc: /* Return last_mouse_y as a fixnum.  */)
  (void)
{
  return make_fixnum (last_mouse_y);
}

DEFUN ("--set-last-mouse-y", Fset_last_mouse_y,
       Sset_last_mouse_y, 1, 1, 0,
       doc: /* Set last_mouse_y to VAL (a fixnum).  */)
  (Lisp_Object val)
{
  CHECK_FIXNUM (val);
  last_mouse_y = XFIXNUM (val);
  return Qnil;
}

DEFUN ("--button-down-time", Fbutton_down_time,
       Sbutton_down_time, 0, 0, 0,
       doc: /* Return button_down_time as a Lisp integer.

May be a bignum on 32-bit fixnum builds (Time is int64).  */)
  (void)
{
  return INT_TO_INTEGER (button_down_time);
}

DEFUN ("--set-button-down-time", Fset_button_down_time,
       Sset_button_down_time, 1, 1, 0,
       doc: /* Set button_down_time to VAL.

VAL is a Lisp integer (fixnum or bignum).  Converts via
scm_to_intmax to match Time (int64 or unsigned long).  */)
  (Lisp_Object val)
{
  button_down_time = scm_to_intmax (val);
  return Qnil;
}

DEFUN ("--double-click-count", Fdouble_click_count,
       Sdouble_click_count, 0, 0, 0,
       doc: /* Return double_click_count as a fixnum.  */)
  (void)
{
  return make_fixnum (double_click_count);
}

DEFUN ("--set-double-click-count", Fset_double_click_count,
       Sset_double_click_count, 1, 1, 0,
       doc: /* Set double_click_count to VAL (a fixnum).  */)
  (Lisp_Object val)
{
  CHECK_FIXNUM (val);
  double_click_count = XFIXNUM (val);
  return Qnil;
}

DEFUN ("--ensure-button-down-location-size",
       Fensure_button_down_location_size,
       Sensure_button_down_location_size, 1, 1, 0,
       doc: /* Grow button_down_location to hold index N if needed.

If N is >= the current vector size, resizes via larger_vector
(which fills new slots with nil).  Also resizes mouse_syms in
lockstep (same C pattern at keyboard.c:6946-6948).  */)
  (Lisp_Object n)
{
  CHECK_FIXNUM (n);
  int button = XFIXNUM (n);
  if (button >= ASIZE (button_down_location))
    {
      ptrdiff_t incr = button - ASIZE (button_down_location) + 1;
      button_down_location = larger_vector (button_down_location,
					    incr, -1);
      mouse_syms = larger_vector (mouse_syms, incr, -1);
    }
  return Qnil;
}

DEFUN ("--mouse-click-menu-bar-intercept",
       Fmouse_click_menu_bar_intercept,
       Smouse_click_menu_bar_intercept, 6, 6, 0,
       doc: /* If the click at frame-relative (X, Y) on FRAME is on
the menu bar (non-toolkit build), return the menu-bar item
event (ITEM . POSITION).  Returns nil otherwise.

FRAME is a live frame.  X and Y are fixnum pixel coords.
MODIFIERS is the event modifier bitmask (must have down_modifier
for menu-bar activation).  TIMESTAMP is the event timestamp
(already INT_TO_INTEGER'd).  FOW is event->frame_or_window.

Encapsulates toolkit_menubar_in_use, coords_in_menu_bar_window,
pixel_to_glyph_coords / x_y_to_hpos_vpos, and FRAME_MENU_BAR_ITEMS
iteration.  On toolkit builds, always returns nil.  */)
  (Lisp_Object frame, Lisp_Object x, Lisp_Object y,
   Lisp_Object modifiers, Lisp_Object timestamp, Lisp_Object fow)
{
  struct frame *f = XFRAME (frame);
  int ix, iy, row, column;

  CHECK_LIVE_FRAME (frame);
  CHECK_FIXNUM (x);
  CHECK_FIXNUM (y);
  CHECK_FIXNUM (modifiers);
  ix = XFIXNUM (x);
  iy = XFIXNUM (y);

  /* Toolkit builds handle menu bar internally — no intercept.  */
  if (toolkit_menubar_in_use (f))
    return Qnil;

  /* Must have down_modifier for menu-bar activation.  */
  if (!(XFIXNUM (modifiers) & down_modifier))
    return Qnil;

#if defined HAVE_WINDOW_SYSTEM && !defined HAVE_EXT_MENU_BAR
  /* On window-system frames: check coords_in_menu_bar_window,
     convert to window-relative coords, use x_y_to_hpos_vpos.  */
  if (FRAME_WINDOW_P (f))
    {
      if (!coords_in_menu_bar_window (f, ix, iy))
	return Qnil;

      {
	struct window *menu_w = XWINDOW (f->menu_bar_window);
	int wx, wy, dummy;
	wx = FRAME_TO_WINDOW_PIXEL_X (menu_w, ix);
	wy = FRAME_TO_WINDOW_PIXEL_Y (menu_w, iy);
	x_y_to_hpos_vpos (menu_w, wx, wy, &column, &row,
			  NULL, NULL, &dummy);
      }
    }
  else
#endif
    /* Non-window frames: use pixel_to_glyph_coords.  */
    pixel_to_glyph_coords (f, ix, iy, &column, &row, NULL, 1);

  /* Check row is within the menu bar.  */
  if (row < 0 || row >= FRAME_MENU_BAR_LINES (f))
    return Qnil;

  {
    Lisp_Object items = FRAME_MENU_BAR_ITEMS (f);
    Lisp_Object item = Qnil;
    int i;
    for (i = 0; i < ASIZE (items); i += 4)
      {
	Lisp_Object str = AREF (items, i + 1);
	Lisp_Object pos = AREF (items, i + 3);
	if (NILP (str))
	  break;
	if (column >= XFIXNUM (pos)
	    && column < XFIXNUM (pos) + SCHARS (str))
	  {
	    item = AREF (items, i);
	    break;
	  }
      }

    if (!NILP (item))
      {
	Lisp_Object position
	  = list4 (fow, Qmenu_bar,
		   Fcons (x, y),
		   timestamp);
	return list2 (item, position);
      }
  }

  return Qnil;
}

DEFUN ("--ignore-mouse-drag-p", Fignore_mouse_drag_p,
       Signore_mouse_drag_p, 0, 0, 0,
       doc: /* Return the value of ignore_mouse_drag_p (C bool).

When non-zero, implicit mouse-movement events are discarded
during drag tracking (keyboard.c:1761).  */)
  (void)
{
  return ignore_mouse_drag_p ? Qt : Qnil;
}

DEFUN ("--set-ignore-mouse-drag-p", Fset_ignore_mouse_drag_p,
       Sset_ignore_mouse_drag_p, 1, 1, 0,
       doc: /* Set ignore_mouse_drag_p to (VAL != nil).  */)
  (Lisp_Object val)
{
  ignore_mouse_drag_p = !NILP (val);
  return Qnil;
}

DEFUN ("--button-down-location-aref", Fbutton_down_location_aref,
       Sbutton_down_location_aref, 1, 1, 0,
       doc: /* Return button_down_location[INDEX].  */)
  (Lisp_Object index)
{
  CHECK_FIXNUM (index);
  return AREF (button_down_location, XFIXNUM (index));
}

DEFUN ("--button-down-location-aset", Fbutton_down_location_aset,
       Sbutton_down_location_aset, 2, 2, 0,
       doc: /* Set button_down_location[INDEX] = VAL.  */)
  (Lisp_Object index, Lisp_Object val)
{
  CHECK_FIXNUM (index);
  ASET (button_down_location, XFIXNUM (index), val);
  return Qnil;
}

DEFUN ("--save-line-number-display-width",
       Fsave_line_number_display_width,
       Ssave_line_number_display_width, 1, 1, 0,
       doc: /* Save the line-number display width for FOW.

FOW is event->frame_or_window (a frame, window, or nil).
Computes line_number_display_width for the corresponding window
and stores it in down_mouse_line_number_width.  */)
  (Lisp_Object fow)
{
  struct window *w;

  if (WINDOWP (fow))
    w = XWINDOW (fow);
  else if (FRAMEP (fow))
    w = XWINDOW (XFRAME (fow)->selected_window);
  else
    w = XWINDOW (selected_window);

  int pixel_width;
  line_number_display_width (w, &down_mouse_line_number_width, &pixel_width);
  return Qnil;
}

DEFUN ("--line-number-mode-hscroll", Fline_number_mode_hscroll,
       Sline_number_mode_hscroll, 2, 2, 0,
       doc: /* Return t if the position change from START-POS to END-POS
is likely due to line-number-mode hscroll redisplay.

Wraps line_number_mode_hscroll (keyboard.c:6771).  Used by the
mouse-click drag/click resolution to avoid spurious drag events
when line-number display width changes between down and up.  */)
  (Lisp_Object start_pos, Lisp_Object end_pos)
{
  return line_number_mode_hscroll (start_pos, end_pos) ? Qt : Qnil;
}

DEFUN ("--iso-function-key-offset", Fiso_function_key_offset,
       Siso_function_key_offset, 0, 0, 0,
       doc: /* Return ISO_FUNCTION_KEY_OFFSET (0xfe00) as a fixnum.

Used by the Scheme keystroke handler to detect ISO 9995 function
keys (code >= ISO_FUNCTION_KEY_OFFSET && code < FUNCTION_KEY_OFFSET).  */)
  (void)
{
  return make_fixnum (ISO_FUNCTION_KEY_OFFSET);
}

/* Key-name table exporters — imp-5.1.
  *
  * Each DEFUN builds a Scheme vector from a static C key-name
  * table.  NULL slots become #f.  All tables exist at file scope
  * regardless of #ifdef; the Scheme caller-side silent-skip
  * pattern gates per-platform registration.
  */

DEFUN ("--lispy-accent-codes", Flispy_accent_codes, Slispy_accent_codes,
       0, 0, 0,
       doc: /* Return a vector of accent keysym codes from lispy_accent_codes.  */)
  (void)
{
  int n = ARRAYELTS (lispy_accent_codes);
  SCM vec = scm_c_make_vector (n, SCM_BOOL_F);
  int i;
  for (i = 0; i < n; i++)
    scm_c_vector_set_x (vec, i, scm_from_int (lispy_accent_codes[i]));
  return vec;
}

DEFUN ("--lispy-accent-keys", Flispy_accent_keys, Slispy_accent_keys,
       0, 0, 0,
       doc: /* Return a vector of accent key name strings (or #f).  */)
  (void)
{
  int n = ARRAYELTS (lispy_accent_keys);
  SCM vec = scm_c_make_vector (n, SCM_BOOL_F);
  int i;
  for (i = 0; i < n; i++)
    {
      const char *s = lispy_accent_keys[i];
      if (s)
	scm_c_vector_set_x (vec, i, scm_from_utf8_string (s));
    }
  return vec;
}

DEFUN ("--function-key-offset", Ffunction_key_offset, Sfunction_key_offset,
       0, 0, 0,
       doc: /* Return FUNCTION_KEY_OFFSET as a fixnum.

The value is build-specific: 0xff00 on X window systems, 0 on
Android/NS/terminal-only builds.  Used by the Scheme keystroke
handler to compute the index into lispy_function_keys.  */)
  (void)
{
  return make_fixnum (FUNCTION_KEY_OFFSET);
}

DEFUN ("--lispy-function-keys", Flispy_function_keys, Slispy_function_keys,
       0, 0, 0,
       doc: /* Return a vector of function-key name strings (or #f).

Callers should memoize the returned vector — each call reconstructs
it from the C table.  */)
  (void)
{
  int n = ARRAYELTS (lispy_function_keys);
  SCM vec = scm_c_make_vector (n, SCM_BOOL_F);
  int i;
  for (i = 0; i < n; i++)
    {
      const char *s = lispy_function_keys[i];
      if (s)
	scm_c_vector_set_x (vec, i, scm_from_utf8_string (s));
    }
  return vec;
}

DEFUN ("--iso-lispy-function-keys", Fiso_lispy_function_keys,
       Siso_lispy_function_keys, 0, 0, 0,
       doc: /* Return a vector of ISO function-key name strings (or #f).

Callers should memoize the returned vector.  */)
  (void)
{
  int n = ARRAYELTS (iso_lispy_function_keys);
  SCM vec = scm_c_make_vector (n, SCM_BOOL_F);
  int i;
  for (i = 0; i < n; i++)
    {
      const char *s = iso_lispy_function_keys[i];
      if (s)
	scm_c_vector_set_x (vec, i, scm_from_utf8_string (s));
    }
  return vec;
}

DEFUN ("--lispy-multimedia-keys", Flispy_multimedia_keys,
       Slispy_multimedia_keys, 0, 0, 0,
       doc: /* Return a vector of multimedia key name strings (or #f).

Callers should memoize the returned vector.
Returns an empty vector on non-NTGUI builds where
MULTIMEDIA_KEY_EVENT can't fire.  */)
  (void)
{
#ifdef HAVE_NTGUI
  int n = ARRAYELTS (lispy_multimedia_keys);
  SCM vec = scm_c_make_vector (n, SCM_BOOL_F);
  int i;
  for (i = 0; i < n; i++)
    {
      const char *s = lispy_multimedia_keys[i];
      if (s)
	scm_c_vector_set_x (vec, i, scm_from_utf8_string (s));
    }
  return vec;
#else
  return scm_c_make_vector (0, SCM_BOOL_F);
#endif
}

/* thin SCM_CALL_1 wrapper that replaces the old
   make_lispy_event body.  Every kbd_buffer_get_event call that
   previously entered the C switch now goes through the Scheme
   orchestrator in (emacs lispy-event) make-lispy-event.

   Lifetime contract: the ie-smob is invalidated (data → NULL)
   immediately after SCM_CALL_1 returns.  Scheme procedures MUST
   NOT retain the smob beyond the call.  Any post-return access
   aborts via CHECK_IE's NULL guard.  */
static Lisp_Object
make_lispy_event (struct input_event *event)
{
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs lispy-event", "make-lispy-event");
  SCM smob = ie_wrap (event);
  Lisp_Object result = SCM_CALL_1 (proc, smob);
  SCM_SET_SMOB_DATA (smob, NULL);
  return result;
}

static Lisp_Object
make_lispy_movement (struct frame *frame, Lisp_Object bar_window, enum scroll_bar_part part,
		     Lisp_Object x, Lisp_Object y, Time t)
{
  /* Is it a scroll bar movement?  */
  if (frame && ! NILP (bar_window))
    {
      Lisp_Object part_sym;

      part_sym = builtin_lisp_symbol (scroll_bar_parts[part]);
      return list2 (Qscroll_bar_movement,
		    list5 (bar_window,
			   Qvertical_scroll_bar,
			   Fcons (x, y),
			   make_fixnum (t),
			   part_sym));
    }
  /* Or is it an ordinary mouse movement?  */
  else
    {
      Lisp_Object position;
      position = make_lispy_position (frame, x, y, t);
      return list2 (Qmouse_movement, position);
    }
}

/* Construct a switch frame event.  */
static Lisp_Object
make_lispy_switch_frame (Lisp_Object frame)
{
  return list2 (Qswitch_frame, frame);
}

DEFUN ("--make-lispy-focus-in", Fmake_lispy_focus_in, Smake_lispy_focus_in,
       1, 1, 0,
       doc: /* Return (focus-in FRAME).  Scheme-callable wrapper.  */)
  (Lisp_Object frame)
{
  return list2 (Qfocus_in, frame);
}

DEFUN ("--make-lispy-focus-out", Fmake_lispy_focus_out, Smake_lispy_focus_out,
       1, 1, 0,
       doc: /* Return (focus-out FRAME).  Scheme-callable wrapper.  */)
  (Lisp_Object frame)
{
  return list2 (Qfocus_out, frame);
}

/* Manipulating modifiers.

   The modifier-parsing functions below dispatch to
   mod/emacs/event-modifiers.scm.  See docs/keyboard.org §M1.  The
   former C bodies (parse_modifiers_uncached, apply_modifiers_uncached,
   lispy_modifier_list, modifier_names[], modifier_symbols) and their
   syms_of_keyboard init block were removed when M1 landed since
   nothing outside the now-shimmed functions referenced them.  */

#define KEY_TO_CHAR(k) (XFIXNUM (k) & ((1 << CHARACTERBITS) - 1))

/* Parse the modifiers on SYMBOL, returning (UNMODIFIED MASK).
   Caches on SYMBOL's Qevent_symbol_element_mask plist property and
   maintains the Qevent_symbol_elements property.  */

Lisp_Object
parse_modifiers (Lisp_Object symbol)
{
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs event-modifiers", "parse-modifiers");
  return SCM_CALL_1 (proc, symbol);
}


/* Apply the modifiers MODIFIERS to the symbol BASE.
   BASE must be unmodified.

   This is like apply_modifiers_uncached, but uses BASE's
   Qmodifier_cache property, if present.

   apply_modifiers copies the value of BASE's Qevent_kind property to
   the modified symbol.  */
static Lisp_Object
apply_modifiers (int modifiers, Lisp_Object base)
{
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs event-modifiers", "apply-modifiers");
  return SCM_CALL_2 (proc, scm_from_int (modifiers), base);
}


/* Given a symbol whose name begins with modifiers ("C-", "M-", etc),
   return a symbol with the modifiers placed in the canonical order.
   Canonical order is alphabetical, except for down and drag, which
   always come last.  The 'click' modifier is never written out.

   Fdefine_key calls this to make sure that (for example) C-M-foo
   and M-C-foo end up being equivalent in the keymap.  */

Lisp_Object
reorder_modifiers (Lisp_Object symbol)
{
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs event-modifiers", "reorder-modifiers");
  return SCM_CALL_1 (proc, symbol);
}


/* Ported to (emacs modify-event-symbol) modify-event-symbol — imp-8.1.2.
   The 7 call sites now route through SCM_CALL_7 wrappers above.  */

/* Convert a list that represents an event type,
   such as (ctrl meta backspace), into the usual representation of that
   event type as a number or a symbol.  */

DEFUN ("event-convert-list", Fevent_convert_list, Sevent_convert_list, 1, 1, 0,
       doc: /* Convert the event description list EVENT-DESC to an event type.
EVENT-DESC should contain one base event type (a character or symbol)
and zero or more modifier names (control, meta, hyper, super, shift, alt,
drag, down, double or triple).  The base must be last.

The return value is an event type (a character or symbol) which has
essentially the same base event type and all the specified modifiers.
(Some compatibility base types, like symbols that represent a
character, are not returned verbatim.)  */)
  (Lisp_Object event_desc)
{
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs event-modifiers", "event-convert-list");
  return SCM_CALL_1 (proc, event_desc);
}

/* Tiny shims that let the Scheme (emacs read-char) port of
   internal-handle-focus-in read/write the C-side state it relies
   on.  The Scheme implementation reads --get-internal-last-event-frame,
   compares it to FRAME, then writes back via --set-internal-last-event-frame.
   For unread_switch_frame, the existing --set-unread-switch-frame
   handles writes; --get-unread-switch-frame reads it without clearing
   (unlike the read-and-clear --rc-take-unread-switch-frame).  */

DEFUN ("--get-internal-last-event-frame",
       Fc_get_internal_last_event_frame,
       Sc_get_internal_last_event_frame, 0, 0, 0,
       doc: /* Internal: return the C global `internal_last_event_frame'.  */)
  (void)
{
  return internal_last_event_frame;
}

DEFUN ("--set-internal-last-event-frame",
       Fc_set_internal_last_event_frame,
       Sc_set_internal_last_event_frame, 1, 1, 0,
       doc: /* Internal: write the C global `internal_last_event_frame'.
Returns nil.  */)
  (Lisp_Object f)
{
  internal_last_event_frame = f;
  return Qnil;
}

DEFUN ("--get-unread-switch-frame",
       Fc_get_unread_switch_frame,
       Sc_get_unread_switch_frame, 0, 0, 0,
       doc: /* Internal: return the C global `unread_switch_frame'
without clearing it.  See --rc-take-unread-switch-frame for the
read-and-clear variant.  */)
  (void)
{
  return unread_switch_frame;
}

/* Try to recognize SYMBOL as a modifier name.
   Return the modifier flag bit, or 0 if not recognized.  */

int
parse_solitary_modifier (Lisp_Object symbol)
{
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs event-modifiers", "parse-solitary-modifier");
  return scm_to_int (SCM_CALL_1 (proc, symbol));
}

/* Return true if EVENT is a list whose elements are all integers or symbols.
   Such a list is not valid as an event,
   but it can be a Lucid-style event type list.  */

bool
lucid_event_type_list_p (Lisp_Object object)
{
  if (! CONSP (object))
    return false;

  if (EQ (XCAR (object), Qhelp_echo)
      || EQ (XCAR (object), Qvertical_line)
      || EQ (XCAR (object), Qmode_line)
      || EQ (XCAR (object), Qtab_line)
      || EQ (XCAR (object), Qheader_line))
    return false;

  Lisp_Object tail = object;
  FOR_EACH_TAIL_SAFE (object)
    {
      Lisp_Object elt = XCAR (object);
      if (! (FIXNUMP (elt) || SYMBOLP (elt)))
	return false;
      tail = XCDR (object);
    }

  return NILP (tail);
}

/* Return true if terminal input chars are available.
   Also, store the return value into INPUT_PENDING.

   Serves the purpose of ioctl (0, FIONREAD, ...)
   but works even if FIONREAD does not exist.
   (In fact, this may actually read some input.)

   If READABLE_EVENTS_DO_TIMERS_NOW is set in FLAGS, actually run
   timer events that are ripe.
   If READABLE_EVENTS_FILTER_EVENTS is set in FLAGS, ignore internal
   events (FOCUS_IN_EVENT).
   If READABLE_EVENTS_IGNORE_SQUEEZABLES is set in FLAGS, ignore mouse
   movements and toolkit scroll bar thumb drags.

   On X, this also returns if the selection event chain is full, since
   that's also "keyboard input".  */

static bool
get_input_pending (int flags)
{
  /* First of all, have we already counted some input?  */
  input_pending = (!NILP (Vquit_flag) || readable_events (flags));

  /* If input is being read as it arrives, and we have none, there is none.  */
  if (!input_pending && (!interrupt_input || interrupts_deferred))
    {
      /* Try to read some input and see how much we get.  */
      gobble_input ();
      input_pending = (!NILP (Vquit_flag) || readable_events (flags));
    }

  return input_pending;
}

/* Read any terminal input already buffered up by the system
   into the kbd_buffer, but do not wait.

   Return the number of keyboard chars read, or -1 meaning
   this is a bad time to try to read input.  */

int
gobble_input (void)
{
  int nread = 0;
  bool err = false;
  struct terminal *t;

  /* Store pending user signal events, if any.  */
  store_user_signal_events ();

  /* Loop through the available terminals, and call their input hooks.  */
  t = terminal_list;
  while (t)
    {
      struct terminal *next = t->next_terminal;

      if (t->read_socket_hook)
        {
          int nr;
          struct input_event hold_quit;

	  if (input_blocked_p ())
	    {
	      pending_signals = true;
	      break;
	    }

          EVENT_INIT (hold_quit);
          hold_quit.kind = NO_EVENT;

          /* No need for FIONREAD or fcntl; just say don't wait.  */
	  while ((nr = (*t->read_socket_hook) (t, &hold_quit)) > 0)
	    nread += nr;

          if (nr == -1)          /* Not OK to read input now.  */
            {
              err = true;
            }
          else if (nr == -2)          /* Non-transient error.  */
            {
              /* The terminal device terminated; it should be closed.  */

              /* Kill Emacs if this was our last terminal.  */
              if (!terminal_list->next_terminal)
                /* Formerly simply reported no input, but that
                   sometimes led to a failure of Emacs to terminate.
                   SIGHUP seems appropriate if we can't reach the
                   terminal.  */
                /* ??? Is it really right to send the signal just to
                   this process rather than to the whole process
                   group?  Perhaps on systems with FIONREAD Emacs is
                   alone in its group.  */
		terminate_due_to_signal (SIGHUP, 10);

              /* XXX Is calling delete_terminal safe here?  It calls delete_frame.  */
	      {
		Lisp_Object tmp;
		XSETTERMINAL (tmp, t);
		Fdelete_terminal (tmp, Qnoelisp);
	      }
            }

	  /* If there was no error, make sure the pointer
	     is visible for all frames on this terminal.  */
	  if (nr >= 0)
	    {
	      Lisp_Object tail, frame;

	      FOR_EACH_FRAME (tail, frame)
		{
		  struct frame *f = XFRAME (frame);
		  if (FRAME_TERMINAL (f) == t)
		    frame_make_pointer_visible (f);
		}
	    }

          if (hold_quit.kind != NO_EVENT)
            kbd_buffer_store_event (&hold_quit);
        }

      t = next;
    }

  if (err && !nread)
    nread = -1;

  return nread;
}

/* This is the tty way of reading available input.

   Note that each terminal device has its own `struct terminal' object,
   and so this function is called once for each individual termcap
   terminal.  The first parameter indicates which terminal to read from.  */

int
tty_read_avail_input (struct terminal *terminal,
                      struct input_event *hold_quit)
{
  /* Using KBD_BUFFER_SIZE - 1 here avoids reading more than
     the kbd_buffer can really hold.  That may prevent loss
     of characters on some systems when input is stuffed at us.  */
  unsigned char cbuf[KBD_BUFFER_SIZE - 1];
#ifndef WINDOWSNT
  int n_to_read;
#endif
  int i;
  struct tty_display_info *tty = terminal->display_info.tty;
  int nread = 0;
#ifdef subprocesses
  int buffer_free = KBD_BUFFER_SIZE - kbd_buffer_nr_stored () - 1;

  if (kbd_on_hold_p () || buffer_free <= 0)
    return 0;
#endif	/* subprocesses */

  if (!terminal->name)		/* Don't read from a dead terminal.  */
    return 0;

  if (terminal->type != output_termcap
      && terminal->type != output_msdos_raw)
    emacs_abort ();

  /* XXX I think the following code should be moved to separate hook
     functions in system-dependent files.  */
#ifdef WINDOWSNT
  /* FIXME: AFAIK, tty_read_avail_input is not used under w32 since the non-GUI
     code sets read_socket_hook to w32_console_read_socket instead!  */
  return 0;
#else /* not WINDOWSNT */
  if (! tty->term_initted)      /* In case we get called during bootstrap.  */
    return 0;

  if (! tty->input)
    return 0;                   /* The terminal is suspended.  */

#ifdef MSDOS
  n_to_read = dos_keysns ();
  if (n_to_read == 0)
    return 0;

  cbuf[0] = dos_keyread ();
  nread = 1;

#else /* not MSDOS */
#ifdef HAVE_GPM
  if (gpm_tty == tty)
  {
      Gpm_Event event;
      int gpm, fd = gpm_fd;

      /* gpm==1 if event received.
         gpm==0 if the GPM daemon has closed the connection, in which case
                Gpm_GetEvent closes gpm_fd and clears it to -1, which is why
		we save it in `fd' so close_gpm can remove it from the
		select masks.
         gpm==-1 if a protocol error or EWOULDBLOCK; the latter is normal.  */
      while (gpm = Gpm_GetEvent (&event), gpm == 1) {
	  nread += handle_one_term_event (tty, &event);
      }
      if (gpm == 0)
	/* Presumably the GPM daemon has closed the connection.  */
	close_gpm (fd);
      if (nread)
	  return nread;
  }
#endif /* HAVE_GPM */

/* Determine how many characters we should *try* to read.  */
#ifdef USABLE_FIONREAD
  /* Find out how much input is available.  */
  if (ioctl (fileno (tty->input), FIONREAD, &n_to_read) < 0)
    {
      if (! noninteractive)
        return -2;          /* Close this terminal.  */
      else
        n_to_read = 0;
    }
  if (n_to_read == 0)
    return 0;
  if (n_to_read > sizeof cbuf)
    n_to_read = sizeof cbuf;
#elif defined USG || defined CYGWIN
  /* Read some input if available, but don't wait.  */
  n_to_read = sizeof cbuf;
  fcntl (fileno (tty->input), F_SETFL, O_NONBLOCK);
#else
# error "Cannot read without possibly delaying"
#endif

#ifdef subprocesses
  /* Don't read more than we can store.  */
  if (n_to_read > buffer_free)
    n_to_read = buffer_free;
#endif	/* subprocesses */

  /* Now read; for one reason or another, this will not block.
     NREAD is set to the number of chars read.  */
  nread = emacs_read (fileno (tty->input), (char *) cbuf, n_to_read);
  /* POSIX infers that processes which are not in the session leader's
     process group won't get SIGHUPs at logout time.  BSDI adheres to
     this part standard and returns -1 from read (0) with errno==EIO
     when the control tty is taken away.
     Jeffrey Honig <jch@bsdi.com> says this is generally safe.  */
  if (nread == -1 && errno == EIO)
    return -2;          /* Close this terminal.  */
#if defined AIX && defined _BSD
  /* The kernel sometimes fails to deliver SIGHUP for ptys.
     This looks incorrect, but it isn't, because _BSD causes
     O_NDELAY to be defined in fcntl.h as O_NONBLOCK,
     and that causes a value other than 0 when there is no input.  */
  if (nread == 0)
    return -2;          /* Close this terminal.  */
#endif

#ifndef USABLE_FIONREAD
#if defined (USG) || defined (CYGWIN)
  fcntl (fileno (tty->input), F_SETFL, 0);
#endif /* USG or CYGWIN */
#endif /* no FIONREAD */

  if (nread <= 0)
    return nread;

#endif /* not MSDOS */
#endif /* not WINDOWSNT */

  for (i = 0; i < nread; i++)
    {
      struct input_event buf;
      EVENT_INIT (buf);
      buf.kind = ASCII_KEYSTROKE_EVENT;
      buf.modifiers = 0;
      if (tty->meta_key == 1 && (cbuf[i] & 0x80))
        buf.modifiers = meta_modifier;
      if (tty->meta_key < 2)
        cbuf[i] &= ~0x80;

      buf.code = cbuf[i];
      /* Set the frame corresponding to the active tty.  Note that the
         value of selected_frame is not reliable here, redisplay tends
         to temporarily change it.  */
      buf.frame_or_window = tty->top_frame;
      buf.arg = Qnil;

      kbd_buffer_store_event (&buf);
      /* Don't look at input that follows a C-g too closely.
         This reduces lossage due to autorepeat on C-g.  */
      if (buf.kind == ASCII_KEYSTROKE_EVENT
          && buf.code == quit_char)
        break;
    }

  return nread;
}

static void
handle_async_input (void)
{
#if defined HAVE_ANDROID && !defined ANDROID_STUBIFY
  /* Check and respond to an ``urgent'' query from the UI thread.
     A query becomes urgent once the UI thread has been waiting
     for more than two seconds.  */

  android_check_query_urgent ();
#endif /* HAVE_ANDROID && !ANDROID_STUBIFY */

#ifndef DOS_NT
  while (1)
    {
      int nread = gobble_input ();
      /* -1 means it's not ok to read the input now.
	 UNBLOCK_INPUT will read it later; now, avoid infinite loop.
	 0 means there was no keyboard input available.  */
      if (nread <= 0)
	break;
    }
#endif
}

void
process_pending_signals (void)
{
  pending_signals = false;
  handle_async_input ();
  do_pending_atimers ();
}

/* Undo any number of BLOCK_INPUT calls down to level LEVEL,
   and reinvoke any pending signal if the level is now 0 and
   a fatal error is not already in progress.  */

void
unblock_input_to (int level)
{
  interrupt_input_blocked = level;
  if (level == 0)
    {
      if (pending_signals && !fatal_error_in_progress)
	process_pending_signals ();
    }
  else if (level < 0)
    emacs_abort ();
}

/* End critical section.

   If doing signal-driven input, and a signal came in when input was
   blocked, reinvoke the signal handler now to deal with it.

   It will also process queued input, if it was not read before.
   When a longer code sequence does not use block/unblock input
   at all, the whole input gathered up to the next call to
   unblock_input will be processed inside that call. */

void
unblock_input (void)
{
  unblock_input_to (interrupt_input_blocked - 1);
}

/* Undo any number of BLOCK_INPUT calls,
   and also reinvoke any pending signal.  */

void
totally_unblock_input (void)
{
  unblock_input_to (0);
}

#if defined (USABLE_SIGIO) || defined (USABLE_SIGPOLL)

void
handle_input_available_signal (int sig)
{
#if defined HAVE_ANDROID && !defined ANDROID_STUBIFY
  /* Make all writes from the Android UI thread visible.  If
     `android_urgent_query' has been set, preceding writes to query
     related variables should become observable here on as well.  */
#if defined __aarch64__
  asm ("dmb ishst");
#else /* !defined __aarch64__ */
  __atomic_thread_fence (__ATOMIC_SEQ_CST);
#endif /* defined __aarch64__ */
#endif /* HAVE_ANDROID && !ANDROID_STUBIFY */
  pending_signals = true;

  if (input_available_clear_time)
    *input_available_clear_time = make_timespec (0, 0);
}

static void
deliver_input_available_signal (int sig)
{
  deliver_process_signal (sig, handle_input_available_signal);
}
#endif /* defined (USABLE_SIGIO) || defined (USABLE_SIGPOLL)  */


/* User signal events.  */

struct user_signal_info
{
  /* Signal number.  */
  int sig;

  /* Name of the signal.  */
  char *name;

  /* Number of pending signals.  */
  int npending;

  struct user_signal_info *next;
};

/* List of user signals.  */
static struct user_signal_info *user_signals = NULL;

void
add_user_signal (int sig, const char *name)
{
  struct sigaction action;
  struct user_signal_info *p;

  for (p = user_signals; p; p = p->next)
    if (p->sig == sig)
      /* Already added.  */
      return;

  p = xmalloc (sizeof *p);
  p->sig = sig;
  p->name = xstrdup (name);
  p->npending = 0;
  p->next = user_signals;
  user_signals = p;

  emacs_sigaction_init (&action, deliver_user_signal);
  sigaction (sig, &action, 0);
}

static void
handle_user_signal (int sig)
{
  struct user_signal_info *p;
  const char *special_event_name = NULL;

  if (SYMBOLP (Vdebug_on_event))
    special_event_name = SSDATA (SYMBOL_NAME (Vdebug_on_event));

  for (p = user_signals; p; p = p->next)
    if (p->sig == sig)
      {
        if (special_event_name
	    && strcmp (special_event_name, p->name) == 0)
          {
            /* Enter the debugger in many ways.  */
            debug_on_next_call = true;
            debug_on_quit = true;
            Vquit_flag = Qt;
            Vinhibit_quit = Qnil;

            /* Eat the event.  */
            break;
          }

	p->npending++;
#if defined (USABLE_SIGIO) || defined (USABLE_SIGPOLL)
	if (interrupt_input)
	  handle_input_available_signal (sig);
	else
#endif
	  {
	    /* Tell wait_reading_process_output that it needs to wake
	       up and look around.  */
	    if (input_available_clear_time)
	      *input_available_clear_time = make_timespec (0, 0);
	  }
	break;
      }
}

static void
deliver_user_signal (int sig)
{
  deliver_process_signal (sig, handle_user_signal);
}

static char *
find_user_signal_name (int sig)
{
  struct user_signal_info *p;

  for (p = user_signals; p; p = p->next)
    if (p->sig == sig)
      return p->name;

  return NULL;
}

static void
store_user_signal_events (void)
{
  struct user_signal_info *p;
  struct input_event buf;
  bool buf_initialized = false;

  for (p = user_signals; p; p = p->next)
    if (p->npending > 0)
      {
	if (! buf_initialized)
	  {
	    memset (&buf, 0, sizeof buf);
	    buf.kind = USER_SIGNAL_EVENT;
	    buf.frame_or_window = selected_frame;
	    buf_initialized = true;
	  }

	do
	  {
	    buf.code = p->sig;
	    kbd_buffer_store_event (&buf);
	    p->npending--;
	  }
	while (p->npending > 0);
      }
}


static void menu_bar_item (Lisp_Object, Lisp_Object, Lisp_Object, void *);
static Lisp_Object menu_bar_one_keymap_changed_items;

/* These variables hold the vector under construction within
   menu_bar_items and its subroutines, and the current index
   for storing into that vector.  */
static Lisp_Object menu_bar_items_vector;
static int menu_bar_items_index;


static const char *separator_names[] = {
  "space",
  "no-line",
  "single-line",
  "double-line",
  "single-dashed-line",
  "double-dashed-line",
  "shadow-etched-in",
  "shadow-etched-out",
  "shadow-etched-in-dash",
  "shadow-etched-out-dash",
  "shadow-double-etched-in",
  "shadow-double-etched-out",
  "shadow-double-etched-in-dash",
  "shadow-double-etched-out-dash",
  0,
};

/* Return true if LABEL specifies a separator.  */

bool
menu_separator_name_p (const char *label)
{
  if (!label)
    return 0;
  else if (strnlen (label, 4) == 4
	   && memcmp (label, "--", 2) == 0
	   && label[2] != '-')
    {
      int i;
      label += 2;
      for (i = 0; separator_names[i]; ++i)
	if (strcmp (label, separator_names[i]) == 0)
          return 1;
    }
  else
    {
      /* It's a separator if it contains only dashes.  */
      while (*label == '-')
	++label;
      return (*label == 0);
    }

  return 0;
}


/* Return a vector of menu items for a menu bar, appropriate
   to the current buffer.  Each item has three elements in the vector:
   KEY STRING MAPLIST.

   OLD is an old vector we can optionally reuse, or nil.  */

Lisp_Object
menu_bar_items (Lisp_Object old)
{
  /* The number of keymaps we're scanning right now, and the number of
     keymaps we have allocated space for.  */
  ptrdiff_t nmaps;

  /* maps[0..nmaps-1] are the prefix definitions of KEYBUF[0..t-1]
     in the current keymaps, or nil where it is not a prefix.  */
  Lisp_Object *maps;

  Lisp_Object mapsbuf[3];
  Lisp_Object def;

  ptrdiff_t mapno;
  Lisp_Object oquit;

  USE_SAFE_ALLOCA;

  /* In order to build the menus, we need to call the keymap
     accessors.  They all call maybe_quit.  But this function is called
     during redisplay, during which a quit is fatal.  So inhibit
     quitting while building the menus.
     We do this instead of specbind because (1) errors will clear it anyway
     and (2) this avoids risk of specpdl overflow.  */
  oquit = Vinhibit_quit;
  Vinhibit_quit = Qt;

  if (!NILP (old))
    {
      CHECK_TYPE (PLAIN_VECTORP (old), Qvectorp, old);
      menu_bar_items_vector = old;
    }
  else
    menu_bar_items_vector = make_nil_elisp_vector (24);
  menu_bar_items_index = 0;

  /* Build our list of keymaps.
     If we recognize a function key and replace its escape sequence in
     keybuf with its symbol, or if the sequence starts with a mouse
     click and we need to switch buffers, we jump back here to rebuild
     the initial keymaps from the current buffer.  */
  {
    Lisp_Object *tmaps;

    /* Should overriding-terminal-local-map and overriding-local-map apply?  */
    if (!NILP (Voverriding_local_map_menu_flag)
	&& !NILP (Voverriding_local_map))
      {
	/* Yes, use them (if non-nil) as well as the global map.  */
	maps = mapsbuf;
	nmaps = 0;
	if (!NILP (KVAR (current_kboard, Voverriding_terminal_local_map)))
	  maps[nmaps++] = KVAR (current_kboard, Voverriding_terminal_local_map);
	if (!NILP (Voverriding_local_map))
	  maps[nmaps++] = Voverriding_local_map;
      }
    else
      {
	/* No, so use major and minor mode keymaps and keymap property.
	   Note that menu-bar bindings in the local-map and keymap
	   properties may not work reliable, as they are only
	   recognized when the menu-bar (or mode-line) is updated,
	   which does not normally happen after every command.  */
	ptrdiff_t nminor = current_minor_maps (NULL, &tmaps);
	SAFE_NALLOCA (maps, 1, nminor + 4);
	nmaps = 0;
	Lisp_Object tem = KVAR (current_kboard, Voverriding_terminal_local_map);
	if (!NILP (tem) && !NILP (Voverriding_local_map_menu_flag))
	  maps[nmaps++] = tem;
	if (tem = get_local_map (PT, current_buffer, Qkeymap), !NILP (tem))
	  maps[nmaps++] = tem;
	if (nminor != 0)
	  {
	    memcpy (maps + nmaps, tmaps, nminor * sizeof (maps[0]));
	    nmaps += nminor;
	  }
	maps[nmaps++] = get_local_map (PT, current_buffer, Qlocal_map);
      }
    maps[nmaps++] = current_global_map;
  }

  /* Look up in each map the dummy prefix key `menu-bar'.  */

  for (mapno = nmaps - 1; mapno >= 0; mapno--)
    if (!NILP (maps[mapno]))
      {
	def = get_keymap (access_keymap (maps[mapno], Qmenu_bar, 1, 0, 1),
			  0, 1);
	if (CONSP (def))
	  {
	    menu_bar_one_keymap_changed_items = Qnil;
	    map_keymap_canonical (def, menu_bar_item, Qnil, NULL);
	  }
      }

  /* Move to the end those items that should be at the end.  */

  Lisp_Object tail = Vmenu_bar_final_items;
  FOR_EACH_TAIL (tail)
    {
      int end = menu_bar_items_index;

      for (int i = 0; i < end; i += 4)
	if (EQ (XCAR (tail), AREF (menu_bar_items_vector, i)))
	  {
	    Lisp_Object tem0, tem1, tem2, tem3;
	    /* Move the item at index I to the end,
	       shifting all the others forward.  */
	    tem0 = AREF (menu_bar_items_vector, i + 0);
	    tem1 = AREF (menu_bar_items_vector, i + 1);
	    tem2 = AREF (menu_bar_items_vector, i + 2);
	    tem3 = AREF (menu_bar_items_vector, i + 3);
	    /* Forward copy is safe since dest (i) < source (i+4) */
	    if (end > i + 4)
	      for (ptrdiff_t j = i; j < end - 4; j++)
		ASET (menu_bar_items_vector, j,
		      AREF (menu_bar_items_vector, j + 4));
	    ASET (menu_bar_items_vector, end - 4, tem0);
	    ASET (menu_bar_items_vector, end - 3, tem1);
	    ASET (menu_bar_items_vector, end - 2, tem2);
	    ASET (menu_bar_items_vector, end - 1, tem3);
	    break;
	  }
    }

  /* Add nil, nil, nil, nil at the end.  */
  {
    int i = menu_bar_items_index;
    if (i + 4 > ASIZE (menu_bar_items_vector))
      menu_bar_items_vector
	= larger_vector (menu_bar_items_vector, 4, -1);
    /* Add this item.  */
    ASET (menu_bar_items_vector, i, Qnil); i++;
    ASET (menu_bar_items_vector, i, Qnil); i++;
    ASET (menu_bar_items_vector, i, Qnil); i++;
    ASET (menu_bar_items_vector, i, Qnil); i++;
    menu_bar_items_index = i;
  }

  Vinhibit_quit = oquit;
  SAFE_FREE ();
  return menu_bar_items_vector;
}

/* Add one item to menu_bar_items_vector, for KEY, ITEM_STRING and DEF.
   If there's already an item for KEY, add this DEF to it.  */

Lisp_Object item_properties;

static void
ensure_item_properties_vector (void)
{
  if (!NILP (item_properties))
    CHECK_TYPE (PLAIN_VECTORP (item_properties), Qvectorp, item_properties);
}


static void
menu_bar_item (Lisp_Object key, Lisp_Object item, Lisp_Object dummy1, void *dummy2)
{
  ensure_item_properties_vector ();
  int i;
  bool parsed;
  Lisp_Object tem;

  if (EQ (item, Qundefined))
    {
      /* If a map has an explicit `undefined' as definition,
	 discard any previously made menu bar item.  */

      for (i = 0; i < menu_bar_items_index; i += 4)
	if (EQ (key, AREF (menu_bar_items_vector, i)))
	  {
	    /* Forward copy is safe since dest (i) < source (i+4) */
	    if (menu_bar_items_index > i + 4)
	      for (ptrdiff_t j = i; j < menu_bar_items_index - 4; j++)
		ASET (menu_bar_items_vector, j,
		      AREF (menu_bar_items_vector, j + 4));
	    menu_bar_items_index -= 4;
	  }
    }

  /* If this keymap has already contributed to this KEY,
     don't contribute to it a second time.  */
  tem = Fmemq (key, menu_bar_one_keymap_changed_items);
  if (!NILP (tem) || NILP (item))
    return;

  menu_bar_one_keymap_changed_items
    = Fcons (key, menu_bar_one_keymap_changed_items);

  /* We add to menu_bar_one_keymap_changed_items before doing the
     parse_menu_item, so that if it turns out it wasn't a menu item,
     it still correctly hides any further menu item.  */
  parsed = parse_menu_item (item, 1);
  if (!parsed)
    return;

  item = AREF (item_properties, ITEM_PROPERTY_DEF);

  /* Find any existing item for this KEY.  */
  for (i = 0; i < menu_bar_items_index; i += 4)
    if (EQ (key, AREF (menu_bar_items_vector, i)))
      break;

  /* If we did not find this KEY, add it at the end.  */
  if (i == menu_bar_items_index)
    {
      /* If vector is too small, get a bigger one.  */
      if (i + 4 > ASIZE (menu_bar_items_vector))
	menu_bar_items_vector = larger_vector (menu_bar_items_vector, 4, -1);
      /* Add this item.  */
      ASET (menu_bar_items_vector, i, key); i++;
      ASET (menu_bar_items_vector, i,
	    AREF (item_properties, ITEM_PROPERTY_NAME)); i++;
      ASET (menu_bar_items_vector, i, list1 (item)); i++;
      ASET (menu_bar_items_vector, i, make_fixnum (0)); i++;
      menu_bar_items_index = i;
    }
  /* We did find an item for this KEY.  Add ITEM to its list of maps.  */
  else
    {
      Lisp_Object old;
      old = AREF (menu_bar_items_vector, i + 2);
      /* If the new and the old items are not both keymaps,
	 the lookup will only find `item'.  */
      item = Fcons (item, KEYMAPP (item) && KEYMAPP (XCAR (old)) ? old : Qnil);
      ASET (menu_bar_items_vector, i + 2, item);
    }
}

 /* This is used as the handler when calling menu_item_eval_property.  */
static Lisp_Object
menu_item_eval_property_1 (Lisp_Object arg)
{
  /* If we got a quit from within the menu computation,
     quit all the way out of it.  This takes care of C-] in the debugger.  */
  if (signal_quit_p (arg))
    quit ();

  return Qnil;
}

static Lisp_Object
eval_dyn (Lisp_Object form)
{
  return Feval (form, Qnil);
}

/* Evaluate an expression and return the result (or nil if something
   went wrong).  Used to evaluate dynamic parts of menu items.  */
Lisp_Object
menu_item_eval_property (Lisp_Object sexpr)
{
  dynwind_begin ();
  Lisp_Object val;
  specbind_guile (Qinhibit_redisplay, Qt);
  val = internal_condition_case_1 (eval_dyn, sexpr, Qerror,
				   menu_item_eval_property_1);
  dynwind_end ();
  return val;
}

DEFUN ("--menu-item-eval-property", Fmenu_item_eval_property,
       Smenu_item_eval_property, 1, 1, 0,
       doc: /* Signal-safe eval of SEXPR for menu-item property forms.
Returns nil on error.  Delegates to C menu_item_eval_property, which
uses internal_condition_case_1 + specbind_guile inside a dynwind frame
to swallow errors and re-raise quit signals.  */)
  (Lisp_Object sexpr)
{
  return menu_item_eval_property (sexpr);
}

DEFUN ("--item-properties-vector", Fitem_properties_vector,
       Sitem_properties_vector, 0, 0, 0,
       doc: /* Return the staticpro'd item_properties vector, lazy-inited
to a nil-filled vector of ITEM_PROPERTY_MAX+1 slots on first call.  */)
  (void)
{
  ensure_item_properties_vector ();
  if (NILP (item_properties))
    item_properties = make_nil_elisp_vector (ITEM_PROPERTY_MAX + 1);
  return item_properties;
}

DEFUN ("--get-keymap", Fget_keymap, Sget_keymap, 1, 3, 0,
       doc: /* Thin shim over C get_keymap.
Return the keymap (or nil) that OBJECT refers to.
Optional second arg ERROR-IF-NOT-KEYMAP: if non-nil, signal
wrong-type-argument instead of returning nil.
Optional third arg AUTOLOAD: if non-nil, autoload keymaps.  */)
  (Lisp_Object object, Lisp_Object error_if_not_keymap, Lisp_Object autoload)
{
  return get_keymap (object,
                     !NILP (error_if_not_keymap),
                     !NILP (autoload));
}

/* This function parses a menu item and leaves the result in the
   vector item_properties.
   ITEM is a key binding, a possible menu item.
   INMENUBAR is > 0 when this is considered for an entry in a menu bar
   top level.
   INMENUBAR is < 0 when this is considered for an entry in a keyboard menu.
   parse_menu_item returns true if the item is a menu item and false
   otherwise.  */

bool
parse_menu_item (Lisp_Object item, int inmenubar)
{
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs menu-item-parse",
                              "parse-menu-item");
  Lisp_Object result = SCM_CALL_2 (proc, item, make_fixnum (inmenubar));
  return XFIXNUM (result);
}




/***********************************************************************
			       Tab-bars
 ***********************************************************************/

/* A vector holding tab bar items while they are parsed in function
   tab_bar_items. Each item occupies TAB_BAR_ITEM_NSCLOTS elements
   in the vector.  */

static Lisp_Object tab_bar_items_vector;

/* A vector holding the result of parse_tab_bar_item.  Layout is like
   the one for a single item in tab_bar_items_vector.  */

static Lisp_Object tab_bar_item_properties;

/* Next free index in tab_bar_items_vector.  */

static int ntab_bar_items;

/* Infrastructure DEFUNs exposing tab-bar internals to Scheme.
   These let the Scheme side own tab_bar_items() while C still
   manages the static vectors (GC-protected via staticpro).  */

DEFUN ("--tab-bar-items-vector", Ftab_bar_items_vector,
       Stab_bar_items_vector, 0, 0, 0,
       doc: /* Return the tab-bar items vector, lazy-initializing to 64 slots if nil.  */)
  (void)
{
  if (NILP (tab_bar_items_vector))
    tab_bar_items_vector = make_nil_elisp_vector (64);
  return tab_bar_items_vector;
}

DEFUN ("--set-tab-bar-items-vector", Fset_tab_bar_items_vector,
       Sset_tab_bar_items_vector, 1, 1, 0,
       doc: /* Set the tab-bar items vector to VEC.
Used by Scheme to write back a resized vector after larger-vector.  */)
  (Lisp_Object vec)
{
  tab_bar_items_vector = vec;
  return Qnil;
}

DEFUN ("--tab-bar-item-properties-vector", Ftab_bar_item_properties_vector,
       Stab_bar_item_properties_vector, 0, 0, 0,
       doc: /* Return the tab-bar item properties vector, lazy-initializing to NSLOTS if nil.  */)
  (void)
{
  if (NILP (tab_bar_item_properties))
    tab_bar_item_properties = make_nil_elisp_vector (TAB_BAR_ITEM_NSLOTS);
  return tab_bar_item_properties;
}

DEFUN ("--tab-bar-items-count", Ftab_bar_items_count,
       Stab_bar_items_count, 0, 0, 0,
       doc: /* Return the number of entries currently in the tab-bar items vector.  */)
  (void)
{
  return make_fixnum (ntab_bar_items);
}

DEFUN ("--set-tab-bar-items-count", Fset_tab_bar_items_count,
       Sset_tab_bar_items_count, 1, 1, 0,
       doc: /* Set the tab-bar items count to N.  */)
  (Lisp_Object n)
{
  CHECK_FIXNUM (n);
  ntab_bar_items = XFIXNUM (n);
  return Qnil;
}

DEFUN ("--larger-vector", Flarger_vector,
       Slarger_vector, 3, 3, 0,
       doc: /* Return a copy of VEC with room for at least INCR-MIN more elements.
If NITEMS-MAX is not -1, the new vector will not exceed that size.
New slots are filled with nil.  */)
  (Lisp_Object vec, Lisp_Object incr_min, Lisp_Object nitems_max)
{
  CHECK_FIXNUM (incr_min);
  CHECK_FIXNUM (nitems_max);
  return larger_vector (vec, XFIXNUM (incr_min), XFIXNUM (nitems_max));
}


/* Return a vector of tab bar items for keymaps currently in effect.
   Reuse vector REUSE if non-nil.  Return in *NITEMS the number of
   tab bar items found.  */

Lisp_Object
tab_bar_items (Lisp_Object reuse, int *nitems)
{
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs tab-bar-items", "tab-bar-items");
  /* Scheme returns (cons vector nitems).  Unpack. */
  Lisp_Object result = SCM_CALL_1 (proc, reuse);
  *nitems = XFIXNUM (XCDR (result));
  return XCAR (result);
}




/***********************************************************************
			       Tool-bars
 ***********************************************************************/

/* A vector holding tool bar items while they are parsed in function
   tool_bar_items. Each item occupies TOOL_BAR_ITEM_NSCLOTS elements
   in the vector.  */

static Lisp_Object tool_bar_items_vector;

/* A vector holding the result of parse_tool_bar_item.  Layout is like
   the one for a single item in tool_bar_items_vector.  */

static Lisp_Object tool_bar_item_properties;

/* Next free index in tool_bar_items_vector.  */

static int ntool_bar_items;

/* Infrastructure DEFUNs exposing tool-bar internals to Scheme.
   These let the Scheme side own tool_bar_items() while C still
   manages the static vectors (GC-protected via staticpro).  */

DEFUN ("--tool-bar-items-vector", Ftool_bar_items_vector,
       Stool_bar_items_vector, 0, 0, 0,
       doc: /* Return the tool-bar items vector, lazy-initializing to 64 slots if nil.  */)
  (void)
{
  if (NILP (tool_bar_items_vector))
    tool_bar_items_vector = make_nil_elisp_vector (64);
  return tool_bar_items_vector;
}

DEFUN ("--set-tool-bar-items-vector", Fset_tool_bar_items_vector,
       Sset_tool_bar_items_vector, 1, 1, 0,
       doc: /* Set the tool-bar items vector to VEC.
Used by Scheme to write back a resized vector after larger-vector.  */)
  (Lisp_Object vec)
{
  tool_bar_items_vector = vec;
  return Qnil;
}

DEFUN ("--tool-bar-item-properties-vector", Ftool_bar_item_properties_vector,
       Stool_bar_item_properties_vector, 0, 0, 0,
       doc: /* Return the tool-bar item properties vector, lazy-initializing to NSLOTS if nil.  */)
  (void)
{
  if (NILP (tool_bar_item_properties))
    tool_bar_item_properties
      = make_nil_elisp_vector (TOOL_BAR_ITEM_NSLOTS);
  return tool_bar_item_properties;
}

DEFUN ("--tool-bar-items-count", Ftool_bar_items_count,
       Stool_bar_items_count, 0, 0, 0,
       doc: /* Return the number of entries currently in the tool-bar items vector.  */)
  (void)
{
  return make_fixnum (ntool_bar_items);
}

DEFUN ("--set-tool-bar-items-count", Fset_tool_bar_items_count,
       Sset_tool_bar_items_count, 1, 1, 0,
       doc: /* Set the tool-bar items count to N.  */)
  (Lisp_Object n)
{
  CHECK_FIXNUM (n);
  ntool_bar_items = XFIXNUM (n);
  return Qnil;
}

/* Return a vector of tool bar items for keymaps currently in effect.
   Reuse vector REUSE if non-nil.  Return in *NITEMS the number of
   tool bar items found.  */

Lisp_Object
tool_bar_items (Lisp_Object reuse, int *nitems)
{
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs tool-bar-items", "tool-bar-items");
  /* Scheme returns (cons vector nitems).  Unpack. */
  Lisp_Object result = SCM_CALL_1 (proc, reuse);
  *nitems = XFIXNUM (XCDR (result));
  return XCAR (result);
}



/* Read a character using menus based on the keymap MAP.
   Return nil if there are no menus in the maps.
   Return t if we displayed a menu but the user rejected it.

   PREV_EVENT is the previous input event, or nil if we are reading
   the first event of a key sequence.

   If USED_MOUSE_MENU is non-null, set *USED_MOUSE_MENU to true
   if we used a mouse menu to read the input, or false otherwise.  If
   USED_MOUSE_MENU is null, don't dereference it.

   The prompting is done based on the prompt-string of the map
   and the strings associated with various map elements.

   This can be done with X menus or with menus put in the minibuf.
   These are done in different ways, depending on how the input will be read.
   Menus using X are done after auto-saving in read-char, getting the input
   event from Fx_popup_menu; menus using the minibuf use read_char recursively
   and do auto-saving in the inner call of read_char.  */

static Lisp_Object
read_char_x_menu_prompt (Lisp_Object map,
			 Lisp_Object prev_event, bool *used_mouse_menu)
{
  if (used_mouse_menu)
    *used_mouse_menu = false;

  /* Use local over global Menu maps.  */

  if (! menu_prompting)
    return Qnil;

  /* If we got to this point via a mouse click,
     use a real menu for mouse selection.  */
  if (EVENT_HAS_PARAMETERS (prev_event)
      && !EQ (XCAR (prev_event), Qmenu_bar)
      && !EQ (XCAR (prev_event), Qtab_bar)
      && !EQ (XCAR (prev_event), Qtool_bar))
    {
      /* Display the menu and get the selection.  */
      Lisp_Object value;

      value = x_popup_menu_1 (prev_event, get_keymap (map, 0, 1));
      if (CONSP (value))
	{
	  Lisp_Object tem;

	  record_menu_key (XCAR (value));

	  /* If we got multiple events, unread all but
	     the first.
	     There is no way to prevent those unread events
	     from showing up later in last_nonmenu_event.
	     So turn symbol and integer events into lists,
	     to indicate that they came from a mouse menu,
	     so that when present in last_nonmenu_event
	     they won't confuse things.  */
	  for (tem = XCDR (value); CONSP (tem); tem = XCDR (tem))
	    {
	      record_menu_key (XCAR (tem));
	      if (SYMBOLP (XCAR (tem))
		  || FIXNUMP (XCAR (tem)))
		XSETCAR (tem, Fcons (XCAR (tem), Qdisabled));
	    }

	  /* If we got more than one event, put all but the first
	     onto this list to be read later.
	     Return just the first event now.  */
	  Vunread_command_events
	    = nconc2 (XCDR (value), Vunread_command_events);
	  value = XCAR (value);
	}
      else if (NILP (value))
	value = Qt;
      if (used_mouse_menu)
	*used_mouse_menu = true;
      return value;
    }
  return Qnil ;
}

static Lisp_Object
read_char_minibuf_menu_prompt (int commandflag,
			       Lisp_Object map)
{
  Lisp_Object name;
  ptrdiff_t nlength;
  /* FIXME: Use the minibuffer's frame width.  */
  ptrdiff_t width = FRAME_COLS (SELECTED_FRAME ()) - 4;
  ptrdiff_t idx = -1;
  bool nobindings = true;
  Lisp_Object rest, vector;
  Lisp_Object prompt_strings = Qnil;

  vector = Qnil;

  if (! menu_prompting)
    return Qnil;

  map = get_keymap (map, 0, 1);
  name = Fkeymap_prompt (map);

  /* If we don't have any menus, just read a character normally.  */
  if (!STRINGP (name))
    return Qnil;

#define PUSH_C_STR(str, listvar) \
  listvar = Fcons (build_unibyte_string (str), listvar)

  /* Prompt string always starts with map's prompt, and a space.  */
  prompt_strings = Fcons (name, prompt_strings);
  PUSH_C_STR (": ", prompt_strings);
  nlength = SCHARS (name) + 2;

  rest = map;

  /* Present the documented bindings, a line at a time.  */
  while (1)
    {
      bool notfirst = false;
      Lisp_Object menu_strings = prompt_strings;
      ptrdiff_t i = nlength;
      Lisp_Object obj;
      Lisp_Object orig_defn_macro;

      /* Loop over elements of map.  */
      while (i < width)
	{
	  Lisp_Object elt;

	  /* FIXME: Use map_keymap to handle new keymap formats.  */

	  /* At end of map, wrap around if just starting,
	     or end this line if already have something on it.  */
	  if (NILP (rest))
	    {
	      if (notfirst || nobindings)
		break;
	      else
		rest = map;
	    }

	  /* Look at the next element of the map.  */
	  if (idx >= 0)
	    elt = AREF (vector, idx);
	  else
	    elt = Fcar_safe (rest);

	  if (idx < 0 && (VECTOR_OR_PSEUDOVECTORP (elt)))
	    {
	      /* If we found a dense table in the keymap,
		 advanced past it, but start scanning its contents.  */
	      rest = Fcdr_safe (rest);
	      vector = elt;
	      idx = 0;
	    }
	  else
	    {
	      /* An ordinary element.  */
	      Lisp_Object event, tem;

	      if (idx < 0)
		{
		  event = Fcar_safe (elt); /* alist */
		  elt = Fcdr_safe (elt);
		}
	      else
		{
		  XSETINT (event, idx); /* vector */
		}

	      /* Ignore the element if it has no prompt string.  */
	      if (FIXNUMP (event) && parse_menu_item (elt, -1))
		{
		  /* True if the char to type matches the string.  */
		  bool char_matches;
		  Lisp_Object upcased_event, downcased_event;
		  Lisp_Object desc = Qnil;
		  Lisp_Object s
		    = AREF (item_properties, ITEM_PROPERTY_NAME);

		  upcased_event = Fupcase (event);
		  downcased_event = Fdowncase (event);
		  char_matches = (XFIXNUM (upcased_event) == SREF (s, 0)
				  || XFIXNUM (downcased_event) == SREF (s, 0));
		  if (! char_matches)
		    desc = Fsingle_key_description (event, Qnil);

#if 0  /* It is redundant to list the equivalent key bindings because
	  the prefix is what the user has already typed.  */
		  tem
		    = XVECTOR (item_properties)->contents[ITEM_PROPERTY_KEYEQ];
		  if (!NILP (tem))
		    /* Insert equivalent keybinding.  */
		    s = concat2 (s, tem);
#endif
		  tem
		    = AREF (item_properties, ITEM_PROPERTY_TYPE);
		  if (EQ (tem, QCradio) || EQ (tem, QCtoggle))
		    {
		      /* Insert button prefix.  */
		      Lisp_Object selected
			= AREF (item_properties, ITEM_PROPERTY_SELECTED);
		      AUTO_STRING (radio_yes, "(*) ");
		      AUTO_STRING (radio_no , "( ) ");
		      AUTO_STRING (check_yes, "[X] ");
		      AUTO_STRING (check_no , "[ ] ");
		      if (EQ (tem, QCradio))
			tem = NILP (selected) ? radio_yes : radio_no;
		      else
			tem = NILP (selected) ? check_yes : check_no;
		      s = concat2 (tem, s);
		    }


		  /* If we have room for the prompt string, add it to this line.
		     If this is the first on the line, always add it.  */
		  if ((SCHARS (s) + i + 2
		       + (char_matches ? 0 : SCHARS (desc) + 3))
		      < width
		      || !notfirst)
		    {
		      ptrdiff_t thiswidth;

		      /* Punctuate between strings.  */
		      if (notfirst)
			{
			  PUSH_C_STR (", ", menu_strings);
			  i += 2;
			}
		      notfirst = true;
		      nobindings = false;

		      /* If the char to type doesn't match the string's
			 first char, explicitly show what char to type.  */
		      if (! char_matches)
			{
			  /* Add as much of string as fits.  */
			  thiswidth = min (SCHARS (desc), width - i);
			  menu_strings
			    = Fcons (Fsubstring (desc, make_fixnum (0),
						 make_fixnum (thiswidth)),
				     menu_strings);
			  i += thiswidth;
			  PUSH_C_STR (" = ", menu_strings);
			  i += 3;
			}

		      /* Add as much of string as fits.  */
		      thiswidth = min (SCHARS (s), width - i);
		      menu_strings
			= Fcons (Fsubstring (s, make_fixnum (0),
					     make_fixnum (thiswidth)),
				 menu_strings);
		      i += thiswidth;
		    }
		  else
		    {
		      /* If this element does not fit, end the line now,
			 and save the element for the next line.  */
		      PUSH_C_STR ("...", menu_strings);
		      break;
		    }
		}

	      /* Move past this element.  */
	      if (idx >= 0 && idx + 1 >= ASIZE (vector))
		/* Handle reaching end of dense table.  */
		idx = -1;
	      if (idx >= 0)
		idx++;
	      else
		rest = Fcdr_safe (rest);
	    }
	}

      /* Prompt with that and read response.  */
      message3_nolog (apply1 (Qconcat, Fnreverse (menu_strings)));

      /* Make believe it's not a keyboard macro in case the help char
	 is pressed.  Help characters are not recorded because menu prompting
	 is not used on replay.  */
      orig_defn_macro = KVAR (current_kboard, defining_kbd_macro);
      kset_defining_kbd_macro (current_kboard, Qnil);
      do
	obj = read_char (commandflag, Qnil, Qt, 0, NULL);
      while (BUFFERP (obj));
      kset_defining_kbd_macro (current_kboard, orig_defn_macro);

      if (!FIXNUMP (obj) || XFIXNUM (obj) == -2
	  || (! EQ (obj, menu_prompt_more_char)
	      && (!FIXNUMP (menu_prompt_more_char)
		  || ! BASE_EQ (obj, make_fixnum (Ctl (XFIXNUM (menu_prompt_more_char)))))))
	{
	  if (!NILP (KVAR (current_kboard, defining_kbd_macro)))
	    store_kbd_macro_char (obj);
	  return obj;
	}
      /* Help char - go round again.  */
    }
}

/* Reading key sequences.  */

static Lisp_Object
follow_key (Lisp_Object keymap, Lisp_Object key)
{
  return access_keymap (get_keymap (keymap, 0, 1),
			key, 1, 0, 1);
}

static Lisp_Object
active_maps (Lisp_Object first_event, Lisp_Object second_event)
{
  Lisp_Object position
    = EVENT_HAS_PARAMETERS (first_event) ? EVENT_START (first_event) : Qnil;
  /* The position of a click can be in the second event if the first event
     is a fake_prefixed_key like `header-line` or `mode-line`.  */
  if (SYMBOLP (first_event)
      && EVENT_HAS_PARAMETERS (second_event)
      && EQ (first_event, POSN_POSN (EVENT_START (second_event))))
    {
      eassert (NILP (position));
      position = EVENT_START (second_event);
    }
  return Fcons (Qkeymap, Fcurrent_active_maps (Qt, position));
}

/* M6j — file-static shadows of the former read_key_sequence locals
   `echo_start' and `keys_start'.  Scheme `rks-setup-initial-state-c!'
   writes them via `--set-rks-echo-start' / `--set-rks-keys-start';
   the C state machine continues to read them at the two existing
   sites (this_command_key_count restore on replay, echo_truncate
   on replay_key).  Single-threaded use, same lifetime as a
   read_key_sequence call, so file-static is safe.  */
/* M6j: echo_start / keys_start retired — setters write to record.  */

DEFUN ("--set-rks-echo-start", Fc_set_rks_echo_start,
       Sc_set_rks_echo_start, 1, 1, 0,
       doc: /* Internal: write echo_start to the <rks-state> record.  */)
  (Lisp_Object n)
{
  CHECK_FIXNAT (n);
  if (rks_state_depth > 0)
    rks_set_int (rks_state_stack[rks_state_depth - 1],
                 RKS_SLOT_ECHO_START, XFIXNUM (n));
  return Qnil;
}

DEFUN ("--set-rks-keys-start", Fc_set_rks_keys_start,
       Sc_set_rks_keys_start, 1, 1, 0,
       doc: /* Internal: write keys_start to the <rks-state> record.  */)
  (Lisp_Object n)
{
  CHECK_FIXNAT (n);
  if (rks_state_depth > 0)
    rks_set_int (rks_state_stack[rks_state_depth - 1],
                 RKS_SLOT_KEYS_START, XFIXNUM (n));
  return Qnil;
}

/* M6h — primitives exposed to (emacs read-key-sequence) for the
   future setup-phase port (kicked off by M6g infrastructure).  See
   docs/keyboard.org §M6h.  */

DEFUN ("--echo-length", Fc_echo_length, Sc_echo_length, 0, 0, 0,
       doc: /* Internal: current length (in characters) of the echo
buffer on the current kboard.  Captured into the rks-state's
echo-start at the start of read_key_sequence and used by
echo_truncate when replaying a key sequence.  */)
  (void)
{
  return make_fixnum (echo_length ());
}

DEFUN ("--echo-truncate", Fc_echo_truncate, Sc_echo_truncate, 1, 1, 0,
       doc: /* Internal: truncate the echo buffer to NCHARS characters.  */)
  (Lisp_Object nchars)
{
  CHECK_FIXNAT (nchars);
  echo_truncate (XFIXNUM (nchars));
  return Qnil;
}

DEFUN ("--echo-dash", Fc_echo_dash, Sc_echo_dash, 0, 0, 0,
       doc: /* Internal: append a `-' separator to the echo buffer (only
when the buffer is non-empty).  */)
  (void)
{
  echo_dash ();
  return Qnil;
}

DEFUN ("--echo-keystrokes-p", Fc_echo_keystrokes_p, Sc_echo_keystrokes_p,
       0, 0, 0,
       doc: /* Internal: t if `echo-keystrokes' is a positive float or
fixnum (i.e. echo is enabled).  */)
  (void)
{
  return echo_keystrokes_p () ? Qt : Qnil;
}

DEFUN ("--cursor-in-echo-area-p", Fc_cursor_in_echo_area_p,
       Sc_cursor_in_echo_area_p, 0, 0, 0,
       doc: /* Internal: read the C global `cursor_in_echo_area' bit
as a predicate.  */)
  (void)
{
  return cursor_in_echo_area ? Qt : Qnil;
}

DEFUN ("--set-current-kboard-immediate-echo",
       Fc_set_current_kboard_immediate_echo,
       Sc_set_current_kboard_immediate_echo, 1, 1, 0,
       doc: /* Internal: set the current kboard's `immediate_echo'
bit-field to non-zero iff VAL is non-nil.  Counterpart to
`--clear-current-kboard-immediate-echo' (which always clears).  */)
  (Lisp_Object val)
{
  current_kboard->immediate_echo = !NILP (val);
  return Qnil;
}

/* M6f — primitive exposed to (emacs read-key-sequence) for the
   future state-machine port.  See docs/keyboard.org §M6f.  */

DEFUN ("--active-maps", Fc_active_maps, Sc_active_maps, 2, 2, 0,
       doc: /* Internal: build the keymap stack for FIRST-EVENT (and
SECOND-EVENT, which can carry the click position when FIRST-EVENT is a
fake prefix key like `mode-line').  Returns a cons (keymap . MAPS)
where MAPS is the result of `current-active-maps' applied at the
position derived from the events.

This is the same `active_maps' helper that read_key_sequence uses
internally to initialize its `current_binding'.  */)
  (Lisp_Object first_event, Lisp_Object second_event)
{
  return active_maps (first_event, second_event);
}

/* Structure used to keep track of partial application of key remapping
   such as Vfunction_key_map and Vkey_translation_map.  */
typedef struct keyremap
{
  /* This is the map originally specified for this use.  */
  Lisp_Object parent;
  /* This is a submap reached by looking up, in PARENT,
     the events from START to END.  */
  Lisp_Object map;
  /* Positions [START, END) in the key sequence buffer
     are the key that we have scanned so far.
     Those events are the ones that we will replace
     if PARENT maps them into a key sequence.  */
  int start, end;
} keyremap;

/* C-9b: load/store helpers for working with a <keyremap> sub-record
   via a local `keyremap' struct.  Callers do:
     keyremap km;
     rks_keyremap_load (RKS_SLOT_FKEY, &km);
     keyremap_step (..., &km, ...);
     rks_keyremap_store (RKS_SLOT_FKEY, &km);
   Avoids per-iteration record reads inside hot walks.  At idle
   (rks_state_depth == 0) load returns a zero-initialized keyremap;
   store is a no-op.  */
static void
rks_keyremap_load (int slot, keyremap *out)
{
  if (rks_state_depth == 0)
    {
      out->parent = out->map = Qnil;
      out->start = out->end = 0;
      return;
    }
  SCM km = scm_struct_ref (rks_state_stack[rks_state_depth - 1],
                           scm_from_int (slot));
  out->parent = scm_struct_ref (km, scm_from_int (KM_SLOT_PARENT));
  out->map    = scm_struct_ref (km, scm_from_int (KM_SLOT_MAP));
  out->start  = rks_get_int    (km, KM_SLOT_START);
  out->end    = rks_get_int    (km, KM_SLOT_END);
}

static void
rks_keyremap_store (int slot, const keyremap *in)
{
  if (rks_state_depth == 0) return;
  SCM km = scm_struct_ref (rks_state_stack[rks_state_depth - 1],
                           scm_from_int (slot));
  scm_struct_set_x (km, scm_from_int (KM_SLOT_PARENT), in->parent);
  scm_struct_set_x (km, scm_from_int (KM_SLOT_MAP),    in->map);
  rks_set_int      (km, KM_SLOT_START, in->start);
  rks_set_int      (km, KM_SLOT_END,   in->end);
}

/* Field-level convenience helpers for getter/setter DEFUNs.  */
static int
rks_keyremap_field_int (int rks_slot, int km_slot)
{
  if (rks_state_depth == 0) return 0;
  SCM km = scm_struct_ref (rks_state_stack[rks_state_depth - 1],
                           scm_from_int (rks_slot));
  return rks_get_int (km, km_slot);
}

static void
rks_keyremap_set_field_int (int rks_slot, int km_slot, int val)
{
  if (rks_state_depth == 0) return;
  SCM km = scm_struct_ref (rks_state_stack[rks_state_depth - 1],
                           scm_from_int (rks_slot));
  rks_set_int (km, km_slot, val);
}

/* M6l — promote read_key_sequence's `fkey', `keytran', `indec' from
   locals to file-static.  C-9b retired them in favor of <keyremap>
   sub-records in <rks-state>; access is via rks_keyremap_load /
   rks_keyremap_store and field-level helpers.  */

/* M6m — promote five more read_key_sequence locals (the ones written
   by the `replay_sequence:' label).  Same #define alias trick as
   M6l.  See docs/keyboard.org §M6m.  */
static int             rks_t;
static int             rks_mock_input;
static Lisp_Object     rks_current_binding;
/* M6m: rks_first_unbound retired — reads go through the record.  */
/* M6m: rks_starting_buffer retired — getter/setter use record. */

/* M6o — promote `shift_translated' (the done:-block install splice
   reads it).  See docs/keyboard.org §M6o.  */
/* M6o: rks_shift_translated retired — reads go through the record.  */

DEFUN ("--rks-shift-translated-p", Fc_rks_shift_translated_p,
       Sc_rks_shift_translated_p, 0, 0, 0,
       doc: /* Internal: read shift_translated from the <rks-state>
record (slot RKS_SLOT_SHIFT_TRANSLATED).  Returns Qt / Qnil.  */)
  (void)
{
  if (rks_state_depth > 0)
    return rks_get_bool (rks_state_stack[rks_state_depth - 1],
                         RKS_SLOT_SHIFT_TRANSLATED) ? Qt : Qnil;
  return Qnil;
}

/* M6q — keybuf stack.  `keybuf' is a `Lisp_Object[READ_KEY_ELTS]'
   array allocated by each caller of read_key_sequence.  To let
   Scheme code read/write the current keybuf we maintain a small
   stack of pointers, pushed at function entry and popped on dynwind
   unwind (via record_unwind_protect_int).  The stack accommodates
   the recursive call that mouse-menu handling triggers (the outer
   call has its keybuf on the stack at depth 0 while the inner call
   uses depth 1; on inner return, the unwind pops depth back to 0
   and Scheme accesses see the outer call's buffer again).  See
   docs/keyboard.org §M6q.  */
enum { RKS_KEYBUF_STACK_MAX = 8 };
static Lisp_Object *rks_keybuf_stack[RKS_KEYBUF_STACK_MAX];
static int          rks_keybuf_depth;

static void
restore_rks_keybuf_depth (int saved)
{
  rks_keybuf_depth = saved;
}

DEFUN ("--rks-keybuf-depth", Fc_rks_keybuf_depth, Sc_rks_keybuf_depth,
       0, 0, 0,
       doc: /* Internal: current depth of the keybuf stack.  Zero means
no read_key_sequence call is in flight.  */)
  (void)
{
  return make_fixnum (rks_keybuf_depth);
}

DEFUN ("--rks-keybuf-ref", Fc_rks_keybuf_ref, Sc_rks_keybuf_ref, 1, 1, 0,
       doc: /* Internal: read keybuf[I] from the current (top-of-stack)
read_key_sequence call.  Returns nil when no call is in flight.  */)
  (Lisp_Object i)
{
  CHECK_FIXNAT (i);
  EMACS_INT idx = XFIXNUM (i);
  if (rks_keybuf_depth == 0 || idx < 0 || idx >= READ_KEY_ELTS)
    return Qnil;
  return rks_keybuf_stack[rks_keybuf_depth - 1][idx];
}

DEFUN ("--rks-keybuf-set", Fc_rks_keybuf_set, Sc_rks_keybuf_set, 2, 2, 0,
       doc: /* Internal: write keybuf[I] = X in the current
read_key_sequence call's keybuf.  No-op when no call is in flight.  */)
  (Lisp_Object i, Lisp_Object x)
{
  CHECK_FIXNAT (i);
  EMACS_INT idx = XFIXNUM (i);
  if (rks_keybuf_depth > 0 && idx >= 0 && idx < READ_KEY_ELTS)
    rks_keybuf_stack[rks_keybuf_depth - 1][idx] = x;
  return Qnil;
}

/* Phase 4 Step 2: C-only block wrappers.  */

DEFUN ("--rks-vquit-flag-clear", Fc_rks_vquit_flag_clear,
       Sc_rks_vquit_flag_clear, 0, 0, 0,
       doc: /* Internal: Vquit_flag = Qnil.  */)
  (void)
{
  Vquit_flag = Qnil;
  return Qnil;
}

DEFUN ("--rks-replay-sequence-restore", Fc_rks_replay_sequence_restore,
       Sc_rks_replay_sequence_restore, 0, 0, 0,
       doc: /* Internal: echo/keys restore that runs at every
`replay_sequence:' entry.  Restores this_command_key_count from
RKS_SLOT_KEYS_START and (if interactive and rks_t < rks_mock_input)
echo_truncate from RKS_SLOT_ECHO_START.  Called from Scheme
replay-sequence-continue after rks-setup-replay-sequence-c!.

Note: text-conversion gating is intentionally NOT included here.
It depends on read_key_sequence's `disable_text_conversion_p'
parameter and is idempotent, so it stays one-time C-side at entry.  */)
  (void)
{
  if (rks_state_depth > 0)
    {
      SCM rec = rks_state_stack[rks_state_depth - 1];
      this_command_key_count = rks_get_int (rec, RKS_SLOT_KEYS_START);
      if (INTERACTIVE && rks_t < rks_mock_input)
        echo_truncate (rks_get_int (rec, RKS_SLOT_ECHO_START));
    }
  return Qnil;
}

/* Phase 4 Step 3b-proper.1: helpers for the Scheme state machine to
   faithfully port the C while-loop condition and the
   `buffer-switched' / `quit-in-other-frame' side effects.  */

DEFUN ("--rks-loop-continue-p", Fc_rks_loop_continue_p,
       Sc_rks_loop_continue_p, 0, 0, 0,
       doc: /* Internal: t if the read_key_sequence iteration should
continue (mirrors the C while-loop condition).  When current_binding
is non-nil, continue iff it is a keymap (prefix binding); when nil,
continue iff keytran.start < rks_t.  */)
  (void)
{
  if (!NILP (rks_current_binding))
    return KEYMAPP (rks_current_binding) ? Qt : Qnil;
  return rks_keyremap_field_int (RKS_SLOT_KEYTRAN, KM_SLOT_START) < rks_t
    ? Qt : Qnil;
}

DEFUN ("--rks-buffer-switched-handler", Fc_rks_buffer_switched_handler,
       Sc_rks_buffer_switched_handler, 1, 1, 0,
       doc: /* Internal: side effects for the `buffer-switched'
classify branch.  Calls timer_resume_idle, sets rks_mock_input
= rks_t, and if FIX-CURRENT-BUFFER-P is non-nil and the selected
window's buffer differs from current_buffer, calls Fset_buffer
(after a frame-live check).  Called from Scheme before
replay-sequence-continue.  */)
  (Lisp_Object fix_current_buffer_p)
{
  timer_resume_idle ();
  rks_mock_input = rks_t;
  if (rks_state_depth > 0)
    rks_set_int (rks_state_stack[rks_state_depth - 1],
                 RKS_SLOT_MOCK_INPUT, rks_mock_input);
  if (!NILP (fix_current_buffer_p)
      && (XBUFFER (XWINDOW (selected_window)->contents) != current_buffer))
    {
      if (! FRAME_LIVE_P (XFRAME (selected_frame)))
        Fkill_emacs (Qnil, Qnil);
      Fset_buffer (XWINDOW (selected_window)->contents);
    }
  return Qnil;
}

/* Shared helper — set rks_mock_input and mirror to record slot.
   Used by --rks-quit-in-other-frame-handler below and by the
   --rks-mouse-click-prefix-body / --rks-reduce-mouse-event-loop
   helpers further down.  */
static void
rks_mock_input_set_and_mirror (int n)
{
  rks_mock_input = n;
  if (rks_state_depth > 0)
    rks_set_int (rks_state_stack[rks_state_depth - 1],
                 RKS_SLOT_MOCK_INPUT, rks_mock_input);
}

DEFUN ("--rks-quit-in-other-frame-handler",
       Fc_rks_quit_in_other_frame_handler,
       Sc_rks_quit_in_other_frame_handler, 0, 0, 0,
       doc: /* Internal: side effects for the `quit-in-other-frame'
classify branch.  Pushes rks_key onto raw_keybuf (no copy — matches
the original quit-path semantics) and keybuf[rks_t++], sets
mock_input = rks_t, clears Vquit_flag.  Called from Scheme before
replay-sequence-continue.  */)
  (void)
{
  /* Reads rks_key via record slot 24 — file-static declared later.  */
  Lisp_Object key = Qnil;
  if (rks_state_depth > 0)
    key = scm_struct_ref (rks_state_stack[rks_state_depth - 1],
                          scm_from_int (RKS_SLOT_KEY));
  GROW_RAW_KEYBUF;
  ASET (raw_keybuf, raw_keybuf_count, key);
  raw_keybuf_count++;
  RKS_RAW_KEYBUF_WRITEBACK;
  if (rks_keybuf_depth > 0)
    rks_keybuf_stack[rks_keybuf_depth - 1][rks_t++] = key;
  if (rks_state_depth > 0)
    rks_set_int (rks_state_stack[rks_state_depth - 1],
                 RKS_SLOT_KEY_COUNT, rks_t);
  rks_mock_input_set_and_mirror (rks_t);
  Vquit_flag = Qnil;
  return Qnil;
}

DEFUN ("--rks-first-event-init", Fc_rks_first_event_init,
       Sc_rks_first_event_init, 1, 1, 0,
       doc: /* Internal: if first_event slot is nil, set it to rks_key,
optionally fix the current buffer, and recompute current_binding
via active_maps.  FIX-CURRENT-BUFFER-P is Qt/Qnil.  */)
  (Lisp_Object fix_current_buffer_p)
{
  if (rks_state_depth == 0)
    return Qnil;
  SCM rec = rks_state_stack[rks_state_depth - 1];
  SCM fe = scm_struct_ref (rec, scm_from_int (RKS_SLOT_FIRST_EVENT));
  if (!NILP (fe))
    return Qnil;
  Lisp_Object key = scm_struct_ref (rec, scm_from_int (RKS_SLOT_KEY));
  scm_struct_set_x (rec, scm_from_int (RKS_SLOT_FIRST_EVENT), key);
  if (!NILP (fix_current_buffer_p)
      && (XBUFFER (XWINDOW (selected_window)->contents) != current_buffer))
    Fset_buffer (XWINDOW (selected_window)->contents);
  Fc_set_rks_current_binding (active_maps (key, Qnil));
  return Qnil;
}


DEFUN ("--rks-raw-keybuf-push", Fc_rks_raw_keybuf_push,
       Sc_rks_raw_keybuf_push, 1, 1, 0,
       doc: /* Internal: GROW_RAW_KEYBUF + ASET(key) + count++ +
record writeback.  KEY is the event to record.  CONSP keys are
deep-copied (see body comment).  */)
  (Lisp_Object key)
{
  GROW_RAW_KEYBUF;
  ASET (raw_keybuf, raw_keybuf_count,
        /* Copy the event, in case it gets modified by side-effect
           by some remapping function (bug#30955).  */
        CONSP (key) ? Fcopy_sequence (key) : key);
  raw_keybuf_count++;
  RKS_RAW_KEYBUF_WRITEBACK;
  return Qnil;
}

/* M6p — promote `delayed_switch_frame' (8 uses inside read_key_sequence
   + 1 final install into the unread_switch_frame global at done:).
   See docs/keyboard.org §M6p.

   Initialized at staticpro-time (see syms_of_keyboard) so reads
   before read_key_sequence has ever run (e.g. from elisp tests)
   return Qnil rather than the BSS zero, which is not a valid
   Lisp_Object.  */
/* M6p: delayed_switch_frame retired — uses record via getter/setter.  */

/* M6r — promote original_uppercase + position (5 uses).  Used by
   the shift-translation fallback (writes) and the done:-block
   downcase-undo splice (reads).  See docs/keyboard.org §M6r.  */
/* M6r: original_uppercase + position retired — record-backed.  */

/* M6y — promote the three inner-block locals of the while-loop
   iteration: echo_local_start (echo-buffer length captured before
   the per-key read, restored on replay_key), keys_local_start
   (this_command_key_count snapshot, same pattern), and
   last_real_key_start (backtrack target inside the iteration).
   See docs/keyboard.org §M6y.  */
/* M6y: echo_local_start retired — getter/setter use record.  */

/* M6z — promote the per-iteration key + used_mouse_menu locals and
   the used_mouse_menu_history array.  `rks_key' is the current event
   being processed; `rks_used_mouse_menu' tracks whether the event
   came from a menu; `rks_used_mouse_menu_history' is the per-keybuf-
   position snapshot needed for replay through mock_input.  See
   docs/keyboard.org §M6z.  */
static Lisp_Object rks_key;
static bool        rks_used_mouse_menu;
/* M6z: used_mouse_menu_history retired — bitmask in record slot 17.  */

/* M6ab — promote new_binding.  Written by follow_key + the
   unbound-event reduction's inner loop; read by M6aa's install
   step.  See docs/keyboard.org §M6ab.  */

/* M6ac — promote fake_prefixed_keys (list of keys for which we
   generated a fake prefix like `mode-line').  Reset to Qnil at
   read_key_sequence entry.  See docs/keyboard.org §M6ac.  */
/* M6ac: fake_prefixed_keys retired — getter/setter use record.  */

/* M6ae — promote disabled_conversion (HAVE_TEXT_CONVERSION only;
   on TTY/window-system-only builds the symbol is still declared
   but never read).  See docs/keyboard.org §M6ae.  */
#ifdef HAVE_TEXT_CONVERSION
/* M6ae: rks_disabled_conversion retired — getter/setter use record.  */
#endif

#ifdef HAVE_TEXT_CONVERSION
/* Criterion-2: helper for --rks-iter-maybe-disable-text-conversion.
   Scans the first up-to-10 keybuf elements for NUMBERP or
   function-key SYMBOL.  */
static bool
rks_text_conversion_keybuf_has_function_key (Lisp_Object *keybuf)
{
  int n = rks_t < 10 ? rks_t : 10;
  for (int i = 0; i < n; i++)
    if (NUMBERP (keybuf[i])
        || (SYMBOLP (keybuf[i])
            && EQ (Fget (keybuf[i], Qevent_kind), Qfunction_key)))
      return true;
  return false;
}
#endif

DEFUN ("--rks-iter-maybe-disable-text-conversion",
       Fc_rks_iter_maybe_disable_text_conversion,
       Sc_rks_iter_maybe_disable_text_conversion, 0, 0, 0,
       doc: /* Internal: if HAVE_TEXT_CONVERSION is enabled and the
predicate holds (not already disabled, at least one key read, no
mouse menu, not inhibited), scan the first up-to-10 keybuf elements
for a NUMBERP or function-key SYMBOL; if found, disable_text_conversion
+ record_unwind_protect_void + flip rks_disabled_conversion.  Always
returns nil.  */)
  (void)
{
#ifdef HAVE_TEXT_CONVERSION
  if (!NILP (Fc_rks_disabled_conversion_p ()) || rks_t == 0
      || !NILP (Fc_rks_used_mouse_menu_p ())
      || disable_inhibit_text_conversion
      || rks_keybuf_depth == 0)
    return Qnil;
  Lisp_Object *keybuf = rks_keybuf_stack[rks_keybuf_depth - 1];
  if (rks_text_conversion_keybuf_has_function_key (keybuf))
    {
      disable_text_conversion ();
      record_unwind_protect_void (resume_text_conversion);
      Fc_set_rks_disabled_conversion (Qt);
    }
#endif
  return Qnil;
}

/* M6ad — unbound-event reduction loop.  Reduces an unbound mouse
   event to a simpler bound one:
     Drags          → clicks.
     Double-clicks  → clicks.
     Triple-clicks  → double-clicks, then to clicks.
     Up/Down-clicks → eliminated.
     Double-downs   → downs, then eliminated.
     Triple-downs   → double-downs, then to downs, then eliminated.
   Returns one of:
     `replay-key'      — bail out via mock_input = 0 + replay_key.
     `replay-sequence' — bail out via mock_input = last_real_key_start
                         + replay_sequence.
     `fall-through'    — reduction either found a binding (current_binding
                         + key updated) or the loop completed without one;
                         caller continues to M6aa install.
   See docs/keyboard.org §M6ad.  */
/* Criterion-2: factor --rks-reduce-mouse-event-loop's loop body
   (modifier-strip + dispose-unbound + try-new-binding) into helpers.
   Shared rks_mock_input_set_and_mirror is defined earlier.  */

static void
rks_reduce_rewind_one_keyremap (keyremap *km, int last_real)
{
  if (km->end <= last_real) return;
  int new_pos = last_real < km->start ? last_real : km->start;
  km->end = km->start = new_pos;
  km->map = km->parent;
}

static void
rks_reduce_rewind_keyremaps_to_last_real (void)
{
  int last_real = XFIXNUM (Fc_rks_last_real_key_start ());
  keyremap indec, fkey, keytran;
  rks_keyremap_load (RKS_SLOT_INDEC,   &indec);
  rks_keyremap_load (RKS_SLOT_FKEY,    &fkey);
  rks_keyremap_load (RKS_SLOT_KEYTRAN, &keytran);
  /* Nested: rewind indec; if it rewound, fkey; if that, keytran.  */
  if (indec.end > last_real)
    {
      rks_reduce_rewind_one_keyremap (&indec, last_real);
      if (fkey.end > last_real)
        {
          rks_reduce_rewind_one_keyremap (&fkey, last_real);
          if (keytran.end > last_real)
            rks_reduce_rewind_one_keyremap (&keytran, last_real);
        }
    }
  rks_keyremap_store (RKS_SLOT_INDEC,   &indec);
  rks_keyremap_store (RKS_SLOT_FKEY,    &fkey);
  rks_keyremap_store (RKS_SLOT_KEYTRAN, &keytran);
}

static SCM
rks_reduce_dispose_unbound_up_down (void)
{
  /* Unbound up/down event — dispose of it.  Adjust the keyremap
     counters back to last_real_key_start, then jump back to
     replay_key (mock_input = 0) or replay_sequence
     (mock_input = last_real_key_start).  */
  rks_reduce_rewind_keyremaps_to_last_real ();
  int last_real = XFIXNUM (Fc_rks_last_real_key_start ());
  rks_mock_input_set_and_mirror (rks_t == last_real ? 0 : last_real);
  return intern (rks_t == last_real ? "replay-key" : "replay-sequence");
}

/* Try a follow_key for the modifier-reduced event.  Returns true if
   a binding was found (caller breaks the loop).  Mutates rks_key,
   rks_current_binding, and rks_new_binding.  */
static bool
rks_reduce_try_new_binding (int modifiers, Lisp_Object breakdown)
{
  Lisp_Object new_head  = apply_modifiers (modifiers, XCAR (breakdown));
  Lisp_Object new_click = list2 (new_head, EVENT_START (rks_key));
  Lisp_Object new_bind  = follow_key (rks_current_binding, new_click);
  Fc_set_rks_new_binding (new_bind);
  if (NILP (new_bind))
    return false;
  rks_current_binding = new_bind;
  if (rks_state_depth > 0)
    scm_struct_set_x (rks_state_stack[rks_state_depth - 1],
                      scm_from_int (RKS_SLOT_CURRENT_BINDING),
                      rks_current_binding);
  rks_key = new_click;
  return true;
}

static SCM
rks_reduce_strip_loop (Lisp_Object breakdown, int modifiers, int reducer_mask)
{
  while (modifiers & reducer_mask)
    {
      if      (modifiers & triple_modifier) modifiers ^= (double_modifier | triple_modifier);
      else if (modifiers & double_modifier) modifiers &= ~double_modifier;
      else if (modifiers & drag_modifier)   modifiers &= ~drag_modifier;
      else
        return rks_reduce_dispose_unbound_up_down ();
      if (rks_reduce_try_new_binding (modifiers, breakdown))
        return intern ("fall-through");
      /* Otherwise leave rks_key set to the drag event; loop again.  */
    }
  return intern ("fall-through");
}

DEFUN ("--rks-reduce-mouse-event-loop",
       Fc_rks_reduce_mouse_event_loop,
       Sc_rks_reduce_mouse_event_loop, 0, 0, 0,
       doc: /* Internal: drag/click/double/triple reduction cascade
for rks_key.  Returns `fall-through', `replay-key', or
`replay-sequence'.  See M6ad / Step E4.  */)
  (void)
{
  Lisp_Object head = EVENT_HEAD (rks_key);
  if (!SYMBOLP (head))
    return intern ("fall-through");
  Lisp_Object breakdown = parse_modifiers (head);
  int modifiers = XFIXNUM (XCAR (XCDR (breakdown)));
  int reducer_mask = up_modifier | down_modifier | drag_modifier
                     | double_modifier | triple_modifier;
  if (!(modifiers & reducer_mask))
    return intern ("fall-through");
  return rks_reduce_strip_loop (breakdown, modifiers, reducer_mask);
}

/* M6ac — bulk splice of the mouse-click prefix expansion (and
   menu-bar / tab-bar / tool-bar prefix insertion).  Returns one of:
     `replay-sequence' — buffer-switch or menu-bar fake prefix.
                         Caller goto replay_sequence.
     `replay-key' — mode-line / scroll-bar fake prefix.
                    Caller goto replay_key.
     `fall-through' — no decoration applied.  Caller continues to
                      the follow_key dispatch.
   See docs/keyboard.org §M6ac.  */
/* Criterion-2: factor --rks-mouse-click-prefix-body's three event-kind
   branches (mouse-click / touchscreen, menu-bar / tab-bar / tool-bar,
   fall-through) into focused helpers.  Shared helper
   rks_mock_input_set_and_mirror is defined earlier (used by the
   reduce-mouse-event-loop helpers above).  */

static SCM
rks_mouse_click_first_key_buffer_switch (Lisp_Object window,
                                          Lisp_Object *keybuf)
{
  /* Key sequences beginning with mouse clicks are read using the
     keymaps in the buffer clicked on.  Switch buffers if we're at
     the beginning of a key sequence.  */
  if (! (WINDOWP (window)
         && BUFFERP (XWINDOW (window)->contents)
         && XBUFFER (XWINDOW (window)->contents) != current_buffer))
    return intern ("fall-through");
  if (keybuf) keybuf[rks_t] = rks_key;
  rks_mock_input_set_and_mirror (rks_t + 1);
  record_unwind_current_buffer ();
  if (! FRAME_LIVE_P (XFRAME (selected_frame)))
    Fkill_emacs (Qnil, Qnil);
  set_buffer_internal (XBUFFER (XWINDOW (window)->contents));
  return intern ("replay-sequence");
}

static SCM
rks_mouse_click_fake_prefix_expand (Lisp_Object posn, Lisp_Object *keybuf)
{
  /* Expand mode-line / scroll-bar events: use posn as fake prefix key.  */
  if (READ_KEY_ELTS - rks_t <= 1)
    error ("Key sequence too long");
  if (keybuf)
    {
      keybuf[rks_t]     = posn;
      keybuf[rks_t + 1] = rks_key;
    }
  rks_mock_input_set_and_mirror (rks_t + 2);
  /* Record fake-prefix for KEY.  Don't modify the event itself —
     that would prevent proper action when the event is pushed back
     into unread-command-events.  */
  Fc_set_rks_fake_prefixed_keys
    (Fcons (rks_key, Fc_rks_fake_prefixed_keys ()));
  return intern ("replay-key");
}

static SCM
rks_mouse_click_handle (Lisp_Object *keybuf)
{
  Lisp_Object window = POSN_WINDOW (EVENT_START (rks_key));
  Lisp_Object posn   = POSN_POSN (EVENT_START (rks_key));
  if (CONSP (posn)
      || (!NILP (Fc_rks_fake_prefixed_keys ())
          && !NILP (Fmemq (rks_key, Fc_rks_fake_prefixed_keys ()))))
    {
      /* Second look at an event for which a fake prefix was generated.  */
      if (rks_t > 0)
        Fc_rks_set_last_real_key_start (make_fixnum (rks_t - 1));
    }
  if (XFIXNUM (Fc_rks_last_real_key_start ()) == 0)
    {
      SCM result = rks_mouse_click_first_key_buffer_switch (window, keybuf);
      if (!scm_is_eq (result, intern ("fall-through")))
        return result;
    }
  if (SYMBOLP (posn)
      && (NILP (Fc_rks_fake_prefixed_keys ())
          || NILP (Fmemq (rks_key, Fc_rks_fake_prefixed_keys ()))))
    return rks_mouse_click_fake_prefix_expand (posn, keybuf);
  return intern ("fall-through");
}

static SCM
rks_menu_bar_or_similar_handle (Lisp_Object *keybuf)
{
  Lisp_Object posn = POSN_POSN (xevent_start (rks_key));
  /* Insert dummy prefix event `menu-bar' / `tab-bar' / `tool-bar'.
     Only when the event comes directly from the keyboard buffer
     (key translation may produce events with these posn-areas
     without intending the prefix expansion).  */
  if ((EQ (posn, Qmenu_bar) || EQ (posn, Qtab_bar) || EQ (posn, Qtool_bar))
      && (rks_mock_input <= rks_t))
    {
      if (READ_KEY_ELTS - rks_t <= 1)
        error ("Key sequence too long");
      if (keybuf)
        {
          keybuf[rks_t]     = posn;
          keybuf[rks_t + 1] = rks_key;
        }
      /* Zap the position so we know it's expanded; don't re-expand.  */
      POSN_SET_POSN (xevent_start (rks_key), list1 (posn));
      rks_mock_input_set_and_mirror (rks_t + 2);
      return intern ("replay-sequence");
    }
  if (CONSP (posn))
    {
      /* Second event of a previously-expanded sequence.  */
      if (XFIXNUM (Fc_rks_last_real_key_start ()) == rks_t && rks_t > 0)
        Fc_rks_set_last_real_key_start (make_fixnum (rks_t - 1));
    }
  return intern ("fall-through");
}

DEFUN ("--rks-mouse-click-prefix-body",
       Fc_rks_mouse_click_prefix_body,
       Sc_rks_mouse_click_prefix_body, 0, 0, 0,
       doc: /* Internal: mouse-click prefix expansion body.  Caller
(Scheme rks-iter-mouse-click-prefix!) must verify
EVENT_HAS_PARAMETERS(rks_key) before calling.  Returns
`replay-sequence', `replay-key', or `fall-through'.
See M6ac / Step E6.  */)
  (void)
{
  Lisp_Object *keybuf = rks_keybuf_depth > 0
    ? rks_keybuf_stack[rks_keybuf_depth - 1] : NULL;
  Lisp_Object kind = EVENT_HEAD_KIND (EVENT_HEAD (rks_key));
  if (EQ (kind, Qmouse_click) || EQ (kind, Qtouchscreen))
    return rks_mouse_click_handle (keybuf);
  if (CONSP (XCDR (rks_key))
      && CONSP (xevent_start (rks_key))
      && CONSP (XCDR (xevent_start (rks_key))))
    return rks_menu_bar_or_similar_handle (keybuf);
  return intern ("fall-through");
}

DEFUN ("--rks-follow-key",
       Fc_rks_follow_key,
       Sc_rks_follow_key, 2, 2, 0,
       doc: /* Internal: call C follow_key (CURRENT-BINDING, KEY).
Returns the binding or nil.  Scheme owns the first_unbound update
logic in rks-follow-key-and-update-first-unbound!.  */)
  (Lisp_Object current_binding, Lisp_Object key)
{
  return follow_key (current_binding, key);
}

/* M6ab — former --rks-follow-key-and-update-first-unbound bulk subr
   (17 lines), decomposed into --rks-follow-key shim + Scheme logic
   in rks-follow-key-and-update-first-unbound!.  See docs/m6-plan.org
   Step E3.  */

DEFUN ("--rks-new-binding", Fc_rks_new_binding, Sc_rks_new_binding,
       0, 0, 0,
       doc: /* Internal: read new_binding from <rks-state> record.  */)
  (void)
{
  if (rks_state_depth > 0)
    return scm_struct_ref (rks_state_stack[rks_state_depth - 1],
                           scm_from_int (RKS_SLOT_NEW_BINDING));
  return Qnil;
}

DEFUN ("--set-rks-new-binding", Fc_set_rks_new_binding,
       Sc_set_rks_new_binding, 1, 1, 0,
       doc: /* Internal: write new_binding to <rks-state> record.  */)
  (Lisp_Object val)
{
  if (rks_state_depth > 0)
    scm_struct_set_x (rks_state_stack[rks_state_depth - 1],
                      scm_from_int (RKS_SLOT_NEW_BINDING), val);
  return Qnil;
}

DEFUN ("--set-rks-first-unbound", Fc_set_rks_first_unbound,
       Sc_set_rks_first_unbound, 1, 1, 0,
       doc: /* Internal: write first_unbound to <rks-state> record.  */)
  (Lisp_Object val)
{
  CHECK_FIXNUM (val);
  if (rks_state_depth > 0)
    rks_set_int (rks_state_stack[rks_state_depth - 1],
                 RKS_SLOT_FIRST_UNBOUND, XFIXNUM (val));
  return Qnil;
}

DEFUN ("--rks-key", Fc_rks_key, Sc_rks_key, 0, 0, 0,
       doc: /* Internal: read the current key from <rks-state> record
slot 24.  Falls back to file-static rks_key when no call in flight.  */)
  (void)
{
  if (rks_state_depth > 0)
    return scm_struct_ref (rks_state_stack[rks_state_depth - 1],
                           scm_from_int (RKS_SLOT_KEY));
  return rks_key;
}

DEFUN ("--set-rks-key", Fc_set_rks_key, Sc_set_rks_key, 1, 1, 0,
       doc: /* Internal: write rks_key.  */)
  (Lisp_Object val)
{
  rks_key = val;
  if (rks_state_depth > 0)
    scm_struct_set_x (rks_state_stack[rks_state_depth - 1],
                      scm_from_int (RKS_SLOT_KEY), val);
  return Qnil;
}

DEFUN ("--rks-used-mouse-menu-p", Fc_rks_used_mouse_menu_p,
       Sc_rks_used_mouse_menu_p, 0, 0, 0,
       doc: /* Internal: read used_mouse_menu from <rks-state>
record.  Returns nil (false) when no call in flight.  */)
  (void)
{
  if (rks_state_depth > 0)
    return rks_get_bool (rks_state_stack[rks_state_depth - 1],
                         RKS_SLOT_USED_MOUSE_MENU) ? Qt : Qnil;
  return Qnil;
}

DEFUN ("--set-rks-used-mouse-menu", Fc_set_rks_used_mouse_menu,
       Sc_set_rks_used_mouse_menu, 1, 1, 0,
       doc: /* Internal: write used_mouse_menu to <rks-state>
record.  Non-nil VAL → true.  */)
  (Lisp_Object val)
{
  if (rks_state_depth > 0)
    rks_set_bool (rks_state_stack[rks_state_depth - 1],
                  RKS_SLOT_USED_MOUSE_MENU, !NILP (val));
  return Qnil;
}

/* Phase 4 Step 2 #4: read_char + bitmask + wrong_kboard, factored
   so the DEFUN body stays under criterion-2's 30-line budget.
   Helpers handle the wrong_kboard cascade and the read_char mirror.  */

static void
rks_call_setup_replay_entire_sequence (void)
{
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs read-key-sequence",
                             "rks-setup-replay-entire-sequence-c!");
  SCM_CALL_0 (proc);
}

static Lisp_Object
rks_read_char_and_mirror (Lisp_Object prevent_redisplay, Lisp_Object prompt,
                          Lisp_Object cur_binding, Lisp_Object lne,
                          bool *used_mouse_menu_out)
{
  /* COMMANDFLAG = -2 avoids redisplay in read_char + subroutines.  */
  Lisp_Object key
    = read_char (!NILP (prevent_redisplay) ? -2 : NILP (prompt),
                 cur_binding, lne, used_mouse_menu_out, NULL);
  rks_key = key;
  rks_used_mouse_menu = *used_mouse_menu_out;
  if (rks_state_depth > 0)
    {
      SCM rec = rks_state_stack[rks_state_depth - 1];
      int bitmask = rks_get_int (rec, RKS_SLOT_USED_MOUSE_MENU_HISTORY);
      if (*used_mouse_menu_out) bitmask |=  (1 << rks_t);
      else                      bitmask &= ~(1 << rks_t);
      rks_set_int  (rec, RKS_SLOT_USED_MOUSE_MENU_HISTORY, bitmask);
      rks_set_bool (rec, RKS_SLOT_USED_MOUSE_MENU, *used_mouse_menu_out);
      scm_struct_set_x (rec, scm_from_int (RKS_SLOT_KEY), key);
    }
  return key;
}

static void
rks_wrong_kboard_prepend_delayed_switch_frame (KBOARD *kb)
{
  if (!NILP (Fc_rks_delayed_switch_frame ()))
    {
      kset_kbd_queue (kb, Fcons (Fc_rks_delayed_switch_frame (),
                                 KVAR (kb, kbd_queue)));
      Fc_set_rks_delayed_switch_frame (Qnil);
    }
}

static void
rks_wrong_kboard_drain_keybuf (KBOARD *kb)
{
  Lisp_Object *keybuf = rks_keybuf_stack[rks_keybuf_depth - 1];
  while (rks_t > 0)
    kset_kbd_queue (kb, Fcons (keybuf[--rks_t], KVAR (kb, kbd_queue)));
}

static void
rks_wrong_kboard_setup_mock_from_queue_head (KBOARD *interrupted_kboard,
                                             struct frame *interrupted_frame)
{
  Lisp_Object head = XCAR (KVAR (interrupted_kboard, kbd_queue));
  /* Mirror head as the next key (matches the original
     `key = XCAR(...)' via Fc_set_rks_key).  */
  Fc_set_rks_key (head);
  Lisp_Object *keybuf = rks_keybuf_stack[rks_keybuf_depth - 1];
  if (!(EVENT_HAS_PARAMETERS (head)
        && EQ (EVENT_HEAD_KIND (EVENT_HEAD (head)), Qswitch_frame)))
    {
      Lisp_Object frame;
      XSETFRAME (frame, interrupted_frame);
      kset_kbd_queue (interrupted_kboard,
                      Fcons (make_lispy_switch_frame (frame),
                             KVAR (interrupted_kboard, kbd_queue)));
      rks_mock_input = 0;
    }
  else if (FIXNUMP (head) && XFIXNUM (head) != -2)
    {
      /* Interrupted while initializing terminal — replay the
         interrupting key.  See Bug#5095 and Bug#37782.  */
      rks_mock_input = 1;
      keybuf[0] = head;
    }
  else
    rks_mock_input = 0;
}

static void
rks_wrong_kboard_setup_mock_from_read_key (Lisp_Object key)
{
  /* Side queue is empty: fall back to the read_char return value.  */
  Lisp_Object *keybuf = rks_keybuf_stack[rks_keybuf_depth - 1];
  if (FIXNUMP (key) && XFIXNUM (key) != -2)
    {
      rks_mock_input = 1;
      keybuf[0] = key;
    }
  else
    rks_mock_input = 0;
}

static SCM
rks_handle_wrong_kboard (KBOARD *interrupted_kboard,
                         struct frame *interrupted_frame,
                         Lisp_Object key)
{
  bool found = false;
  for (KBOARD *k = all_kboards; k; k = k->next_kboard)
    if (k == interrupted_kboard) { found = true; break; }

  if (!found)
    {
      /* Don't touch interrupted_kboard when it's been deleted.  */
      Fc_set_rks_delayed_switch_frame (Qnil);
      rks_call_setup_replay_entire_sequence ();
      return intern ("replay-sequence");
    }
  rks_wrong_kboard_prepend_delayed_switch_frame (interrupted_kboard);
  rks_wrong_kboard_drain_keybuf (interrupted_kboard);
  if (CONSP (KVAR (interrupted_kboard, kbd_queue)))
    rks_wrong_kboard_setup_mock_from_queue_head (interrupted_kboard,
                                                  interrupted_frame);
  else
    rks_wrong_kboard_setup_mock_from_read_key (key);
  rks_call_setup_replay_entire_sequence ();
  return intern ("replay-sequence");
}

DEFUN ("--rks-read-char-and-kboard",
       Fc_rks_read_char_and_kboard,
       Sc_rks_read_char_and_kboard, 4, 4, 0,
       doc: /* Internal: read_char + used_mouse_menu bitmask +
wrong_kboard handling.  Args: PREVENT-REDISPLAY (Qt/Qnil), PROMPT,
CUR-BINDING (current_binding for read_char), LNE (last_nonmenu_event).
Returns `continue' (proceed to classifier) or `replay-sequence'
(wrong_kboard fired — caller does replay setup and iterates).  */)
  (Lisp_Object prevent_redisplay, Lisp_Object prompt,
   Lisp_Object cur_binding, Lisp_Object lne)
{
  KBOARD *interrupted_kboard = current_kboard;
  struct frame *interrupted_frame = SELECTED_FRAME ();
  bool used_mouse_menu = false;
  Lisp_Object key
    = rks_read_char_and_mirror (prevent_redisplay, prompt, cur_binding, lne,
                                &used_mouse_menu);

  /* wrong_kboard check.  Also covers Bug#5095 (read_char returns a
     buffer when terminal-init-xterm eats the wrong_kboard_jmpbuf
     return).  */
  if ((FIXNUMP (key) && XFIXNUM (key) == -2)
      || (interrupted_kboard != current_kboard))
    return rks_handle_wrong_kboard (interrupted_kboard, interrupted_frame, key);
  return intern ("continue");
}

/* M6aa — bulk splice of the final binding-install + per-key
   bookkeeping (post-dispatch).  NEW-BINDING is the resolved
   binding from the keymap dispatch above.  See
   docs/keyboard.org §M6aa.  */
DEFUN ("--rks-iter-install-binding",
       Fc_rks_iter_install_binding, Sc_rks_iter_install_binding, 1, 1, 0,
       doc: /* Internal: install NEW-BINDING as the resolved
rks_current_binding for this iteration.  Writes rks_key into
keybuf[rks_t] and advances rks_t.  Updates last_nonmenu_event
unless the key came from a mouse menu.  Recomputes
this_single_command_key_start (clamped to >= 0; see Bug#20223).
Mirrors src/keyboard.c lines 12058-12081 pre-M6aa.  */)
  (Lisp_Object new_binding)
{
  rks_current_binding = new_binding;
  /* M6i wave A: write current_binding back to record.  */
  if (rks_state_depth > 0)
    scm_struct_set_x (rks_state_stack[rks_state_depth - 1],
                      scm_from_int (RKS_SLOT_CURRENT_BINDING),
                      rks_current_binding);
  if (rks_keybuf_depth > 0)
    rks_keybuf_stack[rks_keybuf_depth - 1][rks_t] = rks_key;
  rks_t++;
  /* M6i-1: keep the record slot current after increment.  */
  if (rks_state_depth > 0)
    rks_set_int (rks_state_stack[rks_state_depth - 1],
                 RKS_SLOT_KEY_COUNT, rks_t);
  if (NILP (Fc_rks_used_mouse_menu_p ()))
    last_nonmenu_event = rks_key;
  ptrdiff_t single = this_command_key_count - rks_t;
  Fc_set_this_single_command_key_start (make_fixnum (single < 0 ? 0 : single));
  return Qnil;
}

/* M6z — atomic splice of the mock-input / end-of-macro cascade.
   Returns one of:
     `mock' — branch 1 fired (rks_t < rks_mock_input).  rks_key,
              rks_used_mouse_menu have been set from the buffer.
              Caller continues with the per-key dispatch.
     `done' — branch 2 fired (executing kbd-macro at end with no
              requeued events).  rks_t has been set to 0.  Caller
              goes to `done:'.
     `read-char' — neither branch applied; caller must do the
                   inline read_char (deferred to M8).
   See docs/keyboard.org §M6z.  */
/* Criterion-2: extract --rks-iter-pre-read-cascade's mock branch.  */
static SCM
rks_pre_read_cascade_mock_branch (void)
{
  Lisp_Object *kb = rks_keybuf_stack[rks_keybuf_depth - 1];
  rks_key = kb[rks_t];
  if (rks_state_depth > 0)
    scm_struct_set_x (rks_state_stack[rks_state_depth - 1],
                      scm_from_int (RKS_SLOT_KEY), rks_key);
  add_command_key (rks_key);
  if (current_kboard->immediate_echo)
    {
      current_kboard->immediate_echo = false;
      echo_now ();
    }
  if (rks_state_depth > 0)
    {
      rks_used_mouse_menu
        = (rks_get_int (rks_state_stack[rks_state_depth - 1],
                        RKS_SLOT_USED_MOUSE_MENU_HISTORY) >> rks_t) & 1;
      rks_set_bool (rks_state_stack[rks_state_depth - 1],
                    RKS_SLOT_USED_MOUSE_MENU, rks_used_mouse_menu);
    }
  return intern ("mock");
}

DEFUN ("--rks-iter-pre-read-cascade",
       Fc_rks_iter_pre_read_cascade, Sc_rks_iter_pre_read_cascade,
       0, 0, 0,
       doc: /* Internal: dispatches the per-iteration key-source
cascade.  See M6z.  Returns `mock', `done', or `read-char'.  */)
  (void)
{
  if (rks_t < rks_mock_input)
    return rks_pre_read_cascade_mock_branch ();
  if (!NILP (Vexecuting_kbd_macro)
      && at_end_of_macro_p ()
      && !requeued_events_pending_p ())
    {
      rks_t = 0;
      return intern ("done");
    }
  return intern ("read-char");
}

DEFUN ("--rks-set-echo-local-start", Fc_rks_set_echo_local_start,
       Sc_rks_set_echo_local_start, 1, 1, 0,
       doc: /* Internal: write echo_local_start to <rks-state>
record slot.  */)
  (Lisp_Object n)
{
  CHECK_FIXNAT (n);
  if (rks_state_depth > 0)
    rks_set_int (rks_state_stack[rks_state_depth - 1],
                 RKS_SLOT_ECHO_LOCAL_START, XFIXNUM (n));
  return Qnil;
}

DEFUN ("--rks-echo-local-start", Fc_rks_echo_local_start,
       Sc_rks_echo_local_start, 0, 0, 0,
       doc: /* Internal: read echo_local_start from <rks-state>
record slot.  Returns 0 when no call in flight.  */)
  (void)
{
  if (rks_state_depth > 0)
    return make_fixnum (rks_get_int (rks_state_stack[rks_state_depth - 1],
                                     RKS_SLOT_ECHO_LOCAL_START));
  return make_fixnum (0);
}

DEFUN ("--rks-set-keys-local-start", Fc_rks_set_keys_local_start,
       Sc_rks_set_keys_local_start, 1, 1, 0,
       doc: /* Internal: write keys_local_start to <rks-state> record.  */)
  (Lisp_Object n)
{
  CHECK_FIXNAT (n);
  if (rks_state_depth > 0)
    rks_set_int (rks_state_stack[rks_state_depth - 1],
                 RKS_SLOT_KEYS_LOCAL_START, XFIXNUM (n));
  return Qnil;
}

DEFUN ("--rks-keys-local-start", Fc_rks_keys_local_start,
       Sc_rks_keys_local_start, 0, 0, 0,
       doc: /* Internal: read keys_local_start from <rks-state>
record.  Returns 0 when no call in flight.  */)
  (void)
{
  if (rks_state_depth > 0)
    return make_fixnum (rks_get_int (rks_state_stack[rks_state_depth - 1],
                                     RKS_SLOT_KEYS_LOCAL_START));
  return make_fixnum (0);
}

DEFUN ("--rks-last-real-key-start", Fc_rks_last_real_key_start,
       Sc_rks_last_real_key_start, 0, 0, 0,
       doc: /* Internal: read last_real_key_start from <rks-state>
record.  Returns 0 when no call in flight.  */)
  (void)
{
  if (rks_state_depth > 0)
    return make_fixnum (rks_get_int (rks_state_stack[rks_state_depth - 1],
                                     RKS_SLOT_LAST_REAL_KEY_START));
  return make_fixnum (0);
}

DEFUN ("--rks-set-last-real-key-start", Fc_rks_set_last_real_key_start,
       Sc_rks_set_last_real_key_start, 1, 1, 0,
       doc: /* Internal: write last_real_key_start to <rks-state>
record.  */)
  (Lisp_Object n)
{
  CHECK_FIXNUM (n);
  if (rks_state_depth > 0)
    rks_set_int (rks_state_stack[rks_state_depth - 1],
                 RKS_SLOT_LAST_REAL_KEY_START, XFIXNUM (n));
  return Qnil;
}

/* M6y — atomic iteration-setup splice: the `t >= READ_KEY_ELTS'
   error check + echo / keys-start capture.  See docs/keyboard.org §M6y.  */
DEFUN ("--rks-iter-setup-capture",
       Fc_rks_iter_setup_capture, Sc_rks_iter_setup_capture, 0, 0, 0,
       doc: /* Internal: error if rks_t exceeds READ_KEY_ELTS, then
capture echo_length into rks_echo_local_start (only when
interactive) and this_command_key_count into
rks_keys_local_start.  Mirrors src/keyboard.c lines 11354-11359
pre-M6y.  */)
  (void)
{
  if (rks_t >= READ_KEY_ELTS)
    error ("Key sequence too long");
  if (!noninteractive)
    Fc_rks_set_echo_local_start (make_fixnum (echo_length ()));
  Fc_rks_set_keys_local_start (make_fixnum (this_command_key_count));
  return Qnil;
}

/* M6y — atomic replay_key-restore splice: echo + keys restore +
   last_real_key_start = rks_t.  See docs/keyboard.org §M6y.  */
DEFUN ("--rks-iter-replay-restore",
       Fc_rks_iter_replay_restore, Sc_rks_iter_replay_restore, 0, 0, 0,
       doc: /* Internal: if interactive and rks_t < rks_mock_input, call
echo_truncate (echo_local_start).  Then write
this_command_key_count = keys_local_start and
last_real_key_start = rks_t.  Mirrors src/keyboard.c lines
11403-11408 pre-M6y.  */)
  (void)
{
  if (!noninteractive && rks_t < rks_mock_input)
    echo_truncate (XFIXNUM (Fc_rks_echo_local_start ()));
  this_command_key_count  = XFIXNUM (Fc_rks_keys_local_start ());
  Fc_rks_set_last_real_key_start (make_fixnum (rks_t));
  return Qnil;
}

DEFUN ("--rks-original-uppercase", Fc_rks_original_uppercase,
       Sc_rks_original_uppercase, 0, 0, 0,
       doc: /* Internal: read original_uppercase from <rks-state>
record slot.  Returns nil when no call is in flight.  */)
  (void)
{
  if (rks_state_depth > 0)
    return scm_struct_ref (rks_state_stack[rks_state_depth - 1],
                           scm_from_int (RKS_SLOT_ORIGINAL_UPPERCASE));
  return Qnil;
}

DEFUN ("--rks-original-uppercase-position",
       Fc_rks_original_uppercase_position,
       Sc_rks_original_uppercase_position, 0, 0, 0,
       doc: /* Internal: read original_uppercase_position from
<rks-state> record slot.  Returns -1 when no call in flight.  */)
  (void)
{
  if (rks_state_depth > 0)
    return make_fixnum (rks_get_int (rks_state_stack[rks_state_depth - 1],
                                     RKS_SLOT_ORIGINAL_UPPERCASE_POSITION));
  return make_fixnum (-1);
}

DEFUN ("--set-rks-original-uppercase",
       Fc_set_rks_original_uppercase,
       Sc_set_rks_original_uppercase, 1, 1, 0,
       doc: /* Internal: write original_uppercase to <rks-state>
record slot.  */)
  (Lisp_Object val)
{
  if (rks_state_depth > 0)
    scm_struct_set_x (rks_state_stack[rks_state_depth - 1],
                      scm_from_int (RKS_SLOT_ORIGINAL_UPPERCASE), val);
  return Qnil;
}

DEFUN ("--set-rks-original-uppercase-position",
       Fc_set_rks_original_uppercase_position,
       Sc_set_rks_original_uppercase_position, 1, 1, 0,
       doc: /* Internal: write original_uppercase_position to
<rks-state> record slot.  */)
  (Lisp_Object val)
{
  CHECK_FIXNUM (val);
  if (rks_state_depth > 0)
    rks_set_int (rks_state_stack[rks_state_depth - 1],
                 RKS_SLOT_ORIGINAL_UPPERCASE_POSITION, XFIXNUM (val));
  return Qnil;
}

DEFUN ("--rks-t", Fc_rks_t, Sc_rks_t, 0, 0, 0,
       doc: /* Internal: read the file-static rks_t (the C `t' local
of read_key_sequence — current key-sequence length).  */)
  (void)
{
  return make_fixnum (rks_t);
}

DEFUN ("--rks-current-binding", Fc_rks_current_binding,
       Sc_rks_current_binding, 0, 0, 0,
       doc: /* Internal: read the file-static rks_current_binding
shadow.  */)
  (void)
{
  return rks_current_binding;
}

DEFUN ("--set-rks-current-binding", Fc_set_rks_current_binding,
       Sc_set_rks_current_binding, 1, 1, 0,
       doc: /* Internal: write rks_current_binding.  */)
  (Lisp_Object val)
{
  rks_current_binding = val;
  if (rks_state_depth > 0)
    scm_struct_set_x (rks_state_stack[rks_state_depth - 1],
                      scm_from_int (RKS_SLOT_CURRENT_BINDING),
                      rks_current_binding);
  return Qnil;
}

DEFUN ("--set-rks-shift-translated", Fc_set_rks_shift_translated,
       Sc_set_rks_shift_translated, 1, 1, 0,
       doc: /* Internal: write shift_translated to the <rks-state>
record slot.  Non-nil VAL → true.  */)
  (Lisp_Object val)
{
  if (rks_state_depth > 0)
    rks_set_bool (rks_state_stack[rks_state_depth - 1],
                  RKS_SLOT_SHIFT_TRANSLATED, !NILP (val));
  return Qnil;
}

DEFUN ("--rks-mock-input", Fc_rks_mock_input, Sc_rks_mock_input,
       0, 0, 0,
       doc: /* Internal: read the file-static rks_mock_input shadow.  */)
  (void)
{
  return make_fixnum (rks_mock_input);
}

DEFUN ("--set-rks-t", Fc_set_rks_t, Sc_set_rks_t, 1, 1, 0,
       doc: /* Internal: write the file-static rks_t (the C `t' of
read_key_sequence).  */)
  (Lisp_Object n)
{
  CHECK_FIXNUM (n);
  rks_t = XFIXNUM (n);
  return Qnil;
}

DEFUN ("--echo-update", Fc_echo_update, Sc_echo_update, 0, 0, 0,
       doc: /* Internal: invoke the C echo_update helper that refreshes
the echo-area buffer from the current kboard state.  */)
  (void)
{
  echo_update ();
  return Qnil;
}

/* M6t — primitives exposed to (emacs read-key-sequence) for the
   first_unbound short-circuit branch.  See docs/keyboard.org §M6t.  */

DEFUN ("--rks-fkey-start", Fc_rks_fkey_start, Sc_rks_fkey_start, 0, 0, 0,
       doc: /* Internal: read fkey.start from <rks-state>.  */)
  (void)
{
  return make_fixnum (rks_keyremap_field_int (RKS_SLOT_FKEY, KM_SLOT_START));
}

DEFUN ("--rks-fkey-end", Fc_rks_fkey_end, Sc_rks_fkey_end, 0, 0, 0,
       doc: /* Internal: read fkey.end from <rks-state>.  */)
  (void)
{
  return make_fixnum (rks_keyremap_field_int (RKS_SLOT_FKEY, KM_SLOT_END));
}

DEFUN ("--rks-keytran-start", Fc_rks_keytran_start, Sc_rks_keytran_start,
       0, 0, 0,
       doc: /* Internal: read keytran.start from <rks-state>.  */)
  (void)
{
  return make_fixnum (rks_keyremap_field_int (RKS_SLOT_KEYTRAN, KM_SLOT_START));
}

DEFUN ("--rks-indec-start", Fc_rks_indec_start, Sc_rks_indec_start,
       0, 0, 0,
       doc: /* Internal: read indec.start from <rks-state>.  */)
  (void)
{
  return make_fixnum (rks_keyremap_field_int (RKS_SLOT_INDEC, KM_SLOT_START));
}

DEFUN ("--rks-keytran-end", Fc_rks_keytran_end, Sc_rks_keytran_end,
       0, 0, 0,
       doc: /* Internal: read keytran.end from <rks-state>.  */)
  (void)
{
  return make_fixnum (rks_keyremap_field_int (RKS_SLOT_KEYTRAN, KM_SLOT_END));
}

DEFUN ("--rks-indec-end", Fc_rks_indec_end, Sc_rks_indec_end,
       0, 0, 0,
       doc: /* Internal: read indec.end from <rks-state>.  */)
  (void)
{
  return make_fixnum (rks_keyremap_field_int (RKS_SLOT_INDEC, KM_SLOT_END));
}

/* Keyremap field setters — added for M6h-1 Scheme-side sync.  */

DEFUN ("--set-rks-fkey-start", Fc_set_rks_fkey_start,
       Sc_set_rks_fkey_start, 1, 1, 0,
       doc: /* Internal: write fkey.start in <rks-state>.  */)
  (Lisp_Object n)
{
  CHECK_FIXNUM (n);
  rks_keyremap_set_field_int (RKS_SLOT_FKEY, KM_SLOT_START, XFIXNUM (n));
  return Qnil;
}

DEFUN ("--set-rks-fkey-end", Fc_set_rks_fkey_end,
       Sc_set_rks_fkey_end, 1, 1, 0,
       doc: /* Internal: write fkey.end in <rks-state>.  */)
  (Lisp_Object n)
{
  CHECK_FIXNUM (n);
  rks_keyremap_set_field_int (RKS_SLOT_FKEY, KM_SLOT_END, XFIXNUM (n));
  return Qnil;
}

DEFUN ("--set-rks-keytran-start", Fc_set_rks_keytran_start,
       Sc_set_rks_keytran_start, 1, 1, 0,
       doc: /* Internal: write keytran.start in <rks-state>.  */)
  (Lisp_Object n)
{
  CHECK_FIXNUM (n);
  rks_keyremap_set_field_int (RKS_SLOT_KEYTRAN, KM_SLOT_START, XFIXNUM (n));
  return Qnil;
}

DEFUN ("--set-rks-keytran-end", Fc_set_rks_keytran_end,
       Sc_set_rks_keytran_end, 1, 1, 0,
       doc: /* Internal: write keytran.end in <rks-state>.  */)
  (Lisp_Object n)
{
  CHECK_FIXNUM (n);
  rks_keyremap_set_field_int (RKS_SLOT_KEYTRAN, KM_SLOT_END, XFIXNUM (n));
  return Qnil;
}

DEFUN ("--set-rks-indec-start", Fc_set_rks_indec_start,
       Sc_set_rks_indec_start, 1, 1, 0,
       doc: /* Internal: write indec.start in <rks-state>.  */)
  (Lisp_Object n)
{
  CHECK_FIXNUM (n);
  rks_keyremap_set_field_int (RKS_SLOT_INDEC, KM_SLOT_START, XFIXNUM (n));
  return Qnil;
}

DEFUN ("--set-rks-indec-end", Fc_set_rks_indec_end,
       Sc_set_rks_indec_end, 1, 1, 0,
       doc: /* Internal: write indec.end in <rks-state>.  */)
  (Lisp_Object n)
{
  CHECK_FIXNUM (n);
  rks_keyremap_set_field_int (RKS_SLOT_INDEC, KM_SLOT_END, XFIXNUM (n));
  return Qnil;
}

DEFUN ("--set-rks-mock-input", Fc_set_rks_mock_input,
       Sc_set_rks_mock_input, 1, 1, 0,
       doc: /* Internal: write rks_mock_input.  */)
  (Lisp_Object n)
{
  CHECK_FIXNUM (n);
  rks_mock_input = XFIXNUM (n);
  if (rks_state_depth > 0)
    rks_set_int (rks_state_stack[rks_state_depth - 1],
                 RKS_SLOT_MOCK_INPUT, rks_mock_input);
  return Qnil;
}

DEFUN ("--rks-starting-buffer", Fc_rks_starting_buffer,
       Sc_rks_starting_buffer, 0, 0, 0,
       doc: /* Internal: read starting_buffer from <rks-state>
record slot (a Lisp buffer object).  Returns nil when no call
in flight.  */)
  (void)
{
  if (rks_state_depth > 0)
    return scm_struct_ref (rks_state_stack[rks_state_depth - 1],
                           scm_from_int (RKS_SLOT_STARTING_BUFFER));
  return Qnil;
}

DEFUN ("--set-rks-starting-buffer", Fc_set_rks_starting_buffer,
       Sc_set_rks_starting_buffer, 1, 1, 0,
       doc: /* Internal: write starting_buffer to <rks-state>
record slot.  VAL should be a Lisp buffer object.  */)
  (Lisp_Object val)
{
  if (rks_state_depth > 0)
    scm_struct_set_x (rks_state_stack[rks_state_depth - 1],
                      scm_from_int (RKS_SLOT_STARTING_BUFFER), val);
  return Qnil;
}

DEFUN ("--rks-disabled-conversion-p", Fc_rks_disabled_conversion_p,
       Sc_rks_disabled_conversion_p, 0, 0, 0,
       doc: /* Internal: read disabled_conversion from <rks-state>
record slot.  Returns nil (false) when no call in flight.  */)
  (void)
{
  if (rks_state_depth > 0)
    return rks_get_bool (rks_state_stack[rks_state_depth - 1],
                         RKS_SLOT_DISABLED_CONVERSION) ? Qt : Qnil;
  return Qnil;
}

DEFUN ("--set-rks-disabled-conversion",
       Fc_set_rks_disabled_conversion,
       Sc_set_rks_disabled_conversion, 1, 1, 0,
       doc: /* Internal: write disabled_conversion to <rks-state>
record slot.  Non-nil VAL → true.  */)
  (Lisp_Object val)
{
  if (rks_state_depth > 0)
    rks_set_bool (rks_state_stack[rks_state_depth - 1],
                  RKS_SLOT_DISABLED_CONVERSION, !NILP (val));
  return Qnil;
}

DEFUN ("--rks-keybuf-shift-down", Fc_rks_keybuf_shift_down,
       Sc_rks_keybuf_shift_down, 1, 1, 0,
       doc: /* Internal: shift keybuf[N..rks_t-1] down to keybuf[0..rks_t-N-1].
N must be a non-negative fixnum.  No-op when no read_key_sequence
call is in flight.  */)
  (Lisp_Object n)
{
  CHECK_FIXNAT (n);
  if (rks_keybuf_depth == 0)
    return Qnil;
  Lisp_Object *kb = rks_keybuf_stack[rks_keybuf_depth - 1];
  EMACS_INT shift = XFIXNUM (n);
  for (int i = shift; i < rks_t; i++)
    kb[i - shift] = kb[i];
  return Qnil;
}

DEFUN ("--rks-keyremaps-shrink-by",
       Fc_rks_keyremaps_shrink_by, Sc_rks_keyremaps_shrink_by, 1, 1, 0,
       doc: /* Internal: for each of indec, fkey, keytran, subtract N
from start, set end = start, and set map = parent.  Mirrors the inner
adjustment of the first_unbound short-circuit branch.  */)
  (Lisp_Object n)
{
  CHECK_FIXNUM (n);
  EMACS_INT amount = XFIXNUM (n);
  keyremap indec, fkey, keytran;
  rks_keyremap_load (RKS_SLOT_INDEC,   &indec);
  rks_keyremap_load (RKS_SLOT_FKEY,    &fkey);
  rks_keyremap_load (RKS_SLOT_KEYTRAN, &keytran);
  indec.start   -= amount; indec.end   = indec.start;   indec.map   = indec.parent;
  fkey.start    -= amount; fkey.end    = fkey.start;    fkey.map    = fkey.parent;
  keytran.start -= amount; keytran.end = keytran.start; keytran.map = keytran.parent;
  rks_keyremap_store (RKS_SLOT_INDEC,   &indec);
  rks_keyremap_store (RKS_SLOT_FKEY,    &fkey);
  rks_keyremap_store (RKS_SLOT_KEYTRAN, &keytran);
  return Qnil;
}

DEFUN ("--rks-first-unbound", Fc_rks_first_unbound,
       Sc_rks_first_unbound, 0, 0, 0,
       doc: /* Internal: read first_unbound from <rks-state> record.
Returns 0 when no call is in flight.  */)
  (void)
{
  if (rks_state_depth > 0)
    return make_fixnum (rks_get_int (rks_state_stack[rks_state_depth - 1],
                                     RKS_SLOT_FIRST_UNBOUND));
  return make_fixnum (0);
}

/* M6x — three translation-map walks (input-decode-map, function-
   key-map, key-translation-map) plus the in-between fkey-shortcut.
   See docs/keyboard.org §M6x.

   Forward declarations needed: keyremap_step and test_undefined are
   defined further down in this file.  */
static bool keyremap_step (Lisp_Object *, volatile keyremap *, int,
                           bool, int *, Lisp_Object);
static bool test_undefined (Lisp_Object);

DEFUN ("--rks-walk-indec",
       Fc_rks_walk_indec,
       Sc_rks_walk_indec, 1, 1, 0,
       doc: /* Internal: walk the input-decode-map (indec) over
the current keybuf.  Returns t when a step completes (mock_input
updated), nil when exhausted.  */)
  (Lisp_Object prompt)
{
  if (rks_keybuf_depth == 0)
    return Qnil;
  Lisp_Object *keybuf = rks_keybuf_stack[rks_keybuf_depth - 1];
  /* C-9b: load keyremap from record into local; mutate; store back.  */
  keyremap indec;
  rks_keyremap_load (RKS_SLOT_INDEC, &indec);
  while (indec.end < rks_t)
    {
      int diff;
      bool done = keyremap_step (keybuf, &indec,
                                 max (rks_t, rks_mock_input),
                                 true, &diff, prompt);
      if (!done) continue;
      rks_mock_input = diff + max (rks_t, rks_mock_input);
      if (rks_state_depth > 0)
        rks_set_int (rks_state_stack[rks_state_depth - 1],
                     RKS_SLOT_MOCK_INPUT, rks_mock_input);
      rks_keyremap_store (RKS_SLOT_INDEC, &indec);
      return Qt;
    }
  rks_keyremap_store (RKS_SLOT_INDEC, &indec);
  return Qnil;
}

/* C-9b: --rks-fkey-shortcut-or-walk decomposed.  Both branches go
   through record-backed load/store now.  */

static Lisp_Object
rks_fkey_shortcut_advance (void)
{
  /* Bound non-keymap + no indec scan pending — advance fkey past
     rks_t so keytran can still scan.  */
  keyremap fkey;
  rks_keyremap_load (RKS_SLOT_FKEY, &fkey);
  if (fkey.start < rks_t)
    {
      fkey.start = fkey.end = rks_t;
      fkey.map = fkey.parent;
      rks_keyremap_store (RKS_SLOT_FKEY, &fkey);
    }
  return Qnil;
}

static Lisp_Object
rks_fkey_walk (Lisp_Object *keybuf, Lisp_Object prompt)
{
  keyremap fkey, indec;
  rks_keyremap_load (RKS_SLOT_FKEY,  &fkey);
  rks_keyremap_load (RKS_SLOT_INDEC, &indec);
  while (fkey.end < indec.start)
    {
      int diff;
      bool done = keyremap_step (keybuf, &fkey,
                                 max (rks_t, rks_mock_input),
                                 (fkey.end + 1 == rks_t
                                  && test_undefined (rks_current_binding)),
                                 &diff, prompt);
      if (!done) continue;
      rks_mock_input = diff + max (rks_t, rks_mock_input);
      indec.end   += diff;
      indec.start += diff;
      if (rks_state_depth > 0)
        rks_set_int (rks_state_stack[rks_state_depth - 1],
                     RKS_SLOT_MOCK_INPUT, rks_mock_input);
      rks_keyremap_store (RKS_SLOT_FKEY,  &fkey);
      rks_keyremap_store (RKS_SLOT_INDEC, &indec);
      return Qt;
    }
  rks_keyremap_store (RKS_SLOT_FKEY, &fkey);
  return Qnil;
}

DEFUN ("--rks-fkey-shortcut-or-walk",
       Fc_rks_fkey_shortcut_or_walk,
       Sc_rks_fkey_shortcut_or_walk, 1, 1, 0,
       doc: /* Internal: fkey (function-key-map) shortcut or walk.
When current_binding is a bound non-keymap and no indec scan is
pending, advance fkey past rks_t so keytran can still scan.
Otherwise walk fkey from fkey.end < indec.start.  Returns t when
a hit is found (mock_input + indec counters updated), nil when
exhausted.  */)
  (Lisp_Object prompt)
{
  if (rks_keybuf_depth == 0)
    return Qnil;
  Lisp_Object *keybuf = rks_keybuf_stack[rks_keybuf_depth - 1];
  if (!KEYMAPP (rks_current_binding)
      && !test_undefined (rks_current_binding)
      && rks_keyremap_field_int (RKS_SLOT_INDEC, KM_SLOT_START) >= rks_t)
    return rks_fkey_shortcut_advance ();
  return rks_fkey_walk (keybuf, prompt);
}

DEFUN ("--rks-walk-keytran",
       Fc_rks_walk_keytran,
       Sc_rks_walk_keytran, 1, 1, 0,
       doc: /* Internal: walk the key-translation-map (keytran) over
the current keybuf.  Returns t on a hit (mock_input + indec + fkey
updated), nil when exhausted.  */)
  (Lisp_Object prompt)
{
  if (rks_keybuf_depth == 0)
    return Qnil;
  Lisp_Object *keybuf = rks_keybuf_stack[rks_keybuf_depth - 1];
  /* C-9b: load keytran, fkey, indec from record.  */
  keyremap keytran, fkey, indec;
  rks_keyremap_load (RKS_SLOT_KEYTRAN, &keytran);
  rks_keyremap_load (RKS_SLOT_FKEY,    &fkey);
  rks_keyremap_load (RKS_SLOT_INDEC,   &indec);
  while (keytran.end < fkey.start)
    {
      int diff;
      bool done = keyremap_step (keybuf, &keytran,
                                 max (rks_t, rks_mock_input),
                                 true, &diff, prompt);
      if (!done) continue;
      rks_mock_input = diff + max (rks_t, rks_mock_input);
      indec.end   += diff;
      indec.start += diff;
      fkey.end    += diff;
      fkey.start  += diff;
      if (rks_state_depth > 0)
        rks_set_int (rks_state_stack[rks_state_depth - 1],
                     RKS_SLOT_MOCK_INPUT, rks_mock_input);
      rks_keyremap_store (RKS_SLOT_KEYTRAN, &keytran);
      rks_keyremap_store (RKS_SLOT_FKEY,    &fkey);
      rks_keyremap_store (RKS_SLOT_INDEC,   &indec);
      return Qt;
    }
  rks_keyremap_store (RKS_SLOT_KEYTRAN, &keytran);
  return Qnil;
}

/* M6x — former --rks-walk-translation-maps bulk subr (99 lines),
   decomposed into three per-map walk shims + Scheme orchestration
   in rks-walk-translation-maps!.  See docs/m6-plan.org Step E5.  */

/* M6w — shifted-function-key shift-translation (block C at the
   while-loop iteration tail).  See docs/keyboard.org §M6w.  */
/* Criterion-2: helpers for --rks-fn-key-shift-translate.  */

static Lisp_Object
rks_strip_shift_modifier (Lisp_Object key, int m)
{
  /* Strip shift from parsed modifiers, re-apply the rest.  */
  Lisp_Object breakdown = parse_modifiers (key);
  if (!CONSP (breakdown))
    return Qnil;
  return apply_modifiers (m & ~shift_modifier, XCAR (breakdown));
}

static Lisp_Object
rks_downcase_uppercase_char (Lisp_Object key, int m)
{
  if (!FIXNUMP (key))
    return Qnil;
  int ch = KEY_TO_CHAR (key);
  if (ch >= XCHAR_TABLE (BVAR (current_buffer,
                               downcase_table))->header.size)
    return Qnil;
  if (!uppercasep (ch))
    return Qnil;
  return make_fixnum (downcase (ch) | m);
}

DEFUN ("--rks-fn-key-shift-translate",
       Fc_rks_fn_key_shift_translate,
       Sc_rks_fn_key_shift_translate, 3, 3, 0,
       doc: /* Internal: attempt the fn-key shift-translation.
KEY is the raw event; MODS is the modifier int from parse_modifiers;
TRANSLATE-ENABLED is translate-upper-case-key-bindings (t or nil).
Returns the translated key or nil.  */)
  (Lisp_Object key, Lisp_Object mods, Lisp_Object translate_enabled)
{
  CHECK_FIXNUM (mods);
  int m = XFIXNUM (mods);
  if (NILP (translate_enabled))
    return Qnil;
  return (m & shift_modifier)
    ? rks_strip_shift_modifier (key, m)
    : rks_downcase_uppercase_char (key, m);
}

DEFUN ("--rks-reset-fkey-and-keytran-scans",
       Fc_rks_reset_fkey_and_keytran_scans,
       Sc_rks_reset_fkey_and_keytran_scans, 0, 0, 0,
       doc: /* Internal: reset fkey and keytran start/end to 0 so
function-key-map re-applies on the replacement key after
shift-translation.  */)
  (void)
{
  rks_keyremap_set_field_int (RKS_SLOT_FKEY,    KM_SLOT_START, 0);
  rks_keyremap_set_field_int (RKS_SLOT_FKEY,    KM_SLOT_END,   0);
  rks_keyremap_set_field_int (RKS_SLOT_KEYTRAN, KM_SLOT_START, 0);
  rks_keyremap_set_field_int (RKS_SLOT_KEYTRAN, KM_SLOT_END,   0);
  return Qnil;
}

/* M6w — former --rks-try-shift-translation-fn-key bulk subr (40
   lines), decomposed into the two shims above + Scheme logic in
   rks-try-shift-translation-fn-key!.  See docs/m6-plan.org E2.  */

/* M6v — help-char prefix check at while-loop iteration tail.
   See docs/keyboard.org §M6v.  */
DEFUN ("--rks-try-help-char", Fc_rks_try_help_char,
       Sc_rks_try_help_char, 1, 1, 0,
       doc: /* Internal: if rks_current_binding is nil, KEY's event-head
is the user's help character, and at least one prior key has
been read (rks_t > 1), install `prefix-help-command' as the
final read_key_sequence_cmd and return t (caller should goto
done).  Returns nil otherwise.  Mirrors src/keyboard.c lines
11812-11819 pre-M6v.  */)
  (Lisp_Object key)
{
  if (NILP (rks_current_binding)
      && help_char_p (EVENT_HEAD (key)) && rks_t > 1)
    {
      read_key_sequence_cmd = Vprefix_help_command;
      return Qt;
    }
  return Qnil;
}

/* M6u — shift-translation fallback (simple upper→lower case).
   See docs/keyboard.org §M6u.  */
DEFUN ("--rks-shift-translate-key",
       Fc_rks_shift_translate_key,
       Sc_rks_shift_translate_key, 1, 1, 0,
       doc: /* Internal: attempt simple shift-translation for KEY (a
fixnum).  Returns the down-translated fixnum, or nil when no
translation applies.  Scheme owns the gate-check and side-effect
logic (rks-try-shift-translation-simple!).  */)
  (Lisp_Object key)
{
  CHECK_FIXNUM (key);
  EMACS_INT k = XFIXNUM (key);
  Lisp_Object new_key;

  if (k & shift_modifier)
    XSETINT (new_key, k & ~shift_modifier);
  else if (CHARACTERP (make_fixnum (k & ~CHAR_MODIFIER_MASK)))
    {
      int dc = downcase (k & ~CHAR_MODIFIER_MASK);
      if (dc == (k & ~CHAR_MODIFIER_MASK))
        return Qnil;
      XSETINT (new_key, dc | (k & CHAR_MODIFIER_MASK));
    }
  else
    return Qnil;

  return new_key;
}

DEFUN ("--rks-delayed-switch-frame", Fc_rks_delayed_switch_frame,
       Sc_rks_delayed_switch_frame, 0, 0, 0,
       doc: /* Internal: read delayed_switch_frame from <rks-state>
record slot.  */)
  (void)
{
  if (rks_state_depth > 0)
    return scm_struct_ref (rks_state_stack[rks_state_depth - 1],
                           scm_from_int (RKS_SLOT_DELAYED_SWITCH_FRAME));
  return Qnil;
}

DEFUN ("--rks-switch-frame-event-p", Fc_rks_switch_frame_event_p,
       Sc_rks_switch_frame_event_p, 1, 1, 0,
       doc: /* Internal: t if KEY is a switch-frame event.  */)
  (Lisp_Object key)
{
  return (EVENT_HAS_PARAMETERS (key)
          && EQ (EVENT_HEAD_KIND (EVENT_HEAD (key)), Qswitch_frame))
    ? Qt : Qnil;
}

DEFUN ("--set-rks-delayed-switch-frame",
       Fc_set_rks_delayed_switch_frame,
       Sc_set_rks_delayed_switch_frame, 1, 1, 0,
       doc: /* Internal: write delayed_switch_frame to <rks-state>
record slot.  */)
  (Lisp_Object val)
{
  if (rks_state_depth > 0)
    scm_struct_set_x (rks_state_stack[rks_state_depth - 1],
                      scm_from_int (RKS_SLOT_DELAYED_SWITCH_FRAME), val);
  return Qnil;
}

DEFUN ("--rks-fake-prefixed-keys", Fc_rks_fake_prefixed_keys,
       Sc_rks_fake_prefixed_keys, 0, 0, 0,
       doc: /* Internal: read fake_prefixed_keys from <rks-state>
record slot.  Returns nil when no call in flight.  */)
  (void)
{
  if (rks_state_depth > 0)
    return scm_struct_ref (rks_state_stack[rks_state_depth - 1],
                           scm_from_int (RKS_SLOT_FAKE_PREFIXED_KEYS));
  return Qnil;
}

DEFUN ("--set-rks-fake-prefixed-keys", Fc_set_rks_fake_prefixed_keys,
       Sc_set_rks_fake_prefixed_keys, 1, 1, 0,
       doc: /* Internal: write fake_prefixed_keys to <rks-state>
record slot.  */)
  (Lisp_Object val)
{
  if (rks_state_depth > 0)
    scm_struct_set_x (rks_state_stack[rks_state_depth - 1],
                      scm_from_int (RKS_SLOT_FAKE_PREFIXED_KEYS), val);
  return Qnil;
}

DEFUN ("--set-unread-switch-frame", Fc_set_unread_switch_frame,
       Sc_set_unread_switch_frame, 1, 1, 0,
       doc: /* Internal: write the C global `unread_switch_frame'.
Called by the Scheme done:-block port to install
rks_delayed_switch_frame into the post-read-key-sequence pending
queue.  */)
  (Lisp_Object x)
{
  unread_switch_frame = x;
  return Qnil;
}

DEFUN ("--rks-replay-sequence-init-rest",
       Fc_rks_replay_sequence_init_rest,
       Sc_rks_replay_sequence_init_rest, 1, 1, 0,
       doc: /* Internal: complete the `replay_sequence:' init given a
pre-computed CURRENT-BINDING (from `--active-maps').  Sets the
file-static rks_starting_buffer = current_buffer, rks_first_unbound
= READ_KEY_ELTS + 1, rks_current_binding = CURRENT-BINDING,
rks_t = 0, and clears last_nonmenu_event.  Mirrors src/keyboard.c
lines 10678-10688 (the body of the replay_sequence: label minus
the active_maps call, which the Scheme caller performs).  */)
  (Lisp_Object current_binding)
{
  Fc_set_rks_starting_buffer (Fcurrent_buffer ());
  rks_current_binding = current_binding;
  rks_t               = 0;
  last_nonmenu_event  = Qnil;
  if (rks_state_depth > 0)
    {
      SCM rec = rks_state_stack[rks_state_depth - 1];
      rks_set_int (rec, RKS_SLOT_FIRST_UNBOUND, READ_KEY_ELTS + 1);
      scm_struct_set_x (rec, scm_from_int (RKS_SLOT_CURRENT_BINDING),
                        rks_current_binding);
      rks_set_int (rec, RKS_SLOT_KEY_COUNT, rks_t);
    }
  return Qnil;
}

DEFUN ("--rks-init-keyremaps", Fc_rks_init_keyremaps, Sc_rks_init_keyremaps,
       3, 3, 0,
       doc: /* Internal: initialize the three keyremap sub-records
in <rks-state> with the given INDEC-MAP, FKEY-MAP, KEYTRAN-MAP.
Each keyremap is set so parent == map == MAP and start == end == 0.
Mirrors the C `replay_entire_sequence:' inline block.  */)
  (Lisp_Object indec_map, Lisp_Object fkey_map, Lisp_Object keytran_map)
{
  keyremap indec   = { .parent = indec_map,   .map = indec_map,   .start = 0, .end = 0 };
  keyremap fkey    = { .parent = fkey_map,    .map = fkey_map,    .start = 0, .end = 0 };
  keyremap keytran = { .parent = keytran_map, .map = keytran_map, .start = 0, .end = 0 };
  rks_keyremap_store (RKS_SLOT_INDEC,   &indec);
  rks_keyremap_store (RKS_SLOT_FKEY,    &fkey);
  rks_keyremap_store (RKS_SLOT_KEYTRAN, &keytran);
  return Qnil;
}

/* Lookup KEY in MAP.
   MAP is a keymap mapping keys to key vectors or functions.
   If the mapping is a function and DO_FUNCALL is true,
   the function is called with PROMPT as parameter and its return
   value is used as the return value of this function (after checking
   that it is indeed a vector).

   START and END are the indices of the first and last key of the
   sequence being remapped within the keyboard buffer KEYBUF.  */

static Lisp_Object
access_keymap_keyremap (Lisp_Object map, Lisp_Object key, Lisp_Object prompt,
			bool do_funcall, unsigned int start, unsigned int end,
			Lisp_Object *keybuf)
{
  Lisp_Object next;

  next = access_keymap (map, key, 1, 0, 1);

  /* Handle a symbol whose function definition is a keymap
     or an array.  */
  if (SYMBOLP (next) && !NILP (Ffboundp (next))
      && (ARRAYP (SYMBOL_FUNCTION (next))
	  || KEYMAPP (SYMBOL_FUNCTION (next))))
    next = Fautoload_do_load (SYMBOL_FUNCTION (next),
                                              next, Qnil);

  /* If the keymap gives a function, not an
     array, then call the function with one arg and use
     its value instead.  */
  if (do_funcall && FUNCTIONP (next))
    {
      Lisp_Object tem, remap;
      tem = next;

      /* Build Vcurrent_key_remap_sequence.  */
      remap = Fvector (end - start + 1, keybuf + start);

      /* Bind `current-key-remap-sequence' to the key sequence being
	 remapped.  */
      dynwind_begin ();
      specbind_guile (Qcurrent_key_remap_sequence, remap);
      next = call1 (next, prompt);
      dynwind_end ();

      /* If the function returned something invalid,
	 barf--don't ignore it.  */
      if (! (NILP (next) || VECTOR_OR_PSEUDOVECTORP (next) || STRINGP (next)))
	signal_error ("Function returns invalid key sequence", tem);
    }
  return next;
}

/* Do one step of the key remapping used for function-key-map and
   key-translation-map:
   KEYBUF is the READ_KEY_ELTS-size buffer holding the input events.
   FKEY is a pointer to the keyremap structure to use.
   INPUT is the index of the last element in KEYBUF.
   DOIT if true says that the remapping can actually take place.
   DIFF is used to return the number of keys added/removed by the remapping.
   PARENT is the root of the keymap.
   PROMPT is the prompt to use if the remapping happens through a function.
   Return true if the remapping actually took place.  */

static bool
keyremap_step (Lisp_Object *keybuf, volatile keyremap *fkey,
	       int input, bool doit, int *diff, Lisp_Object prompt)
{
  Lisp_Object next, key;
  ptrdiff_t buf_start, buf_end;

  /* Save the key sequence being translated.  */
  buf_start = fkey->start;
  buf_end = fkey->end;

  key = keybuf[fkey->end++];

  if (KEYMAPP (fkey->parent))
    next = access_keymap_keyremap (fkey->map, key, prompt, doit,
				   buf_start, buf_end, keybuf);
  else
    next = Qnil;

  /* If keybuf[fkey->start..fkey->end] is bound in the
     map and we're in a position to do the key remapping, replace it with
     the binding and restart with fkey->start at the end.  */
  if ((VECTOR_OR_PSEUDOVECTORP (next) || STRINGP (next)) && doit)
    {
      int len = XFIXNAT (Flength (next));
      int i;

      *diff = len - (fkey->end - fkey->start);

      if (READ_KEY_ELTS - input <= *diff)
	error ("Key sequence too long");

      /* Shift the keys that follow fkey->end.  */
      if (*diff < 0)
	for (i = fkey->end; i < input; i++)
	  keybuf[i + *diff] = keybuf[i];
      else if (*diff > 0)
	for (i = input - 1; i >= fkey->end; i--)
	  keybuf[i + *diff] = keybuf[i];
      /* Overwrite the old keys with the new ones.  */
      for (i = 0; i < len; i++)
	keybuf[fkey->start + i]
	  = Faref (next, make_fixnum (i));

      fkey->start = fkey->end += *diff;
      fkey->map = fkey->parent;

      return 1;
    }

  fkey->map = get_keymap (next, 0, 1);

  /* If we no longer have a bound suffix, try a new position for
     fkey->start.  */
  if (!CONSP (fkey->map))
    {
      fkey->end = ++fkey->start;
      fkey->map = fkey->parent;
    }
  return 0;
}

static bool
test_undefined (Lisp_Object binding)
{
  return (NILP (binding)
	  || EQ (binding, Qundefined)
	  || (SYMBOLP (binding)
	      && EQ (Fcommand_remapping (binding, Qnil, Qnil), Qundefined)));
}

void init_raw_keybuf_count (void)
{
  raw_keybuf_count = 0;
}



#ifdef HAVE_TEXT_CONVERSION

static void
restore_reading_key_sequence (int old_reading_key_sequence)
{
  reading_key_sequence = old_reading_key_sequence;

  /* If a key sequence is no longer being read, reset input methods
     whose state changes were postponed.  */

  if (!old_reading_key_sequence)
    check_postponed_buffers ();
}

#endif /* HAVE_TEXT_CONVERSION */

/* Read a sequence of keys that ends with a non prefix character,
   storing it in KEYBUF, a buffer of size READ_KEY_ELTS.
   Prompt with PROMPT.
   Return the length of the key sequence stored.
   Return -1 if the user rejected a command menu.

   Echo starting immediately unless `prompt' is 0.

   If PREVENT_REDISPLAY is non-zero, avoid redisplay by calling
   read_char with a suitable COMMANDFLAG argument.

   Where a key sequence ends depends on the currently active keymaps.
   These include any minor mode keymaps active in the current buffer,
   the current buffer's local map, and the global map.

   If a key sequence has no other bindings, we check Vfunction_key_map
   to see if some trailing subsequence might be the beginning of a
   function key's sequence.  If so, we try to read the whole function
   key, and substitute its symbolic name into the key sequence.

   We ignore unbound `down-' mouse clicks.  We turn unbound `drag-' and
   `double-' events into similar click events, if that would make them
   bound.  We try to turn `triple-' events first into `double-' events,
   then into clicks.

   If we get a mouse click in a mode line, vertical divider, or other
   non-text area, we treat the click as if it were prefixed by the
   symbol denoting that area - `mode-line', `vertical-line', or
   whatever.

   If the sequence starts with a mouse click, we read the key sequence
   with respect to the buffer clicked on, not the current buffer.

   If the user switches frames in the midst of a key sequence, we put
   off the switch-frame event until later; the next call to
   read_char will return it.

   If FIX_CURRENT_BUFFER, we restore current_buffer
   from the selected window's buffer.

   If DISABLE_TEXT_CONVERSION_P, disable text conversion so the input
   method will always send key events.  */

static int
read_key_sequence (Lisp_Object *keybuf, Lisp_Object prompt,
		   bool dont_downcase_last, bool can_return_switch_frame,
		   bool fix_current_buffer, bool prevent_redisplay,
		   bool disable_text_conversion_p)
{
  /* M6 Step B: push a fresh <rks-state> record so the Scheme side
     can inspect state during the call (via --rks-state-current) and
     the exit sync captures final field values.  See docs/m6-plan.org
     Step B.  */
  {
    static SCM rks_make_state_proc = SCM_UNDEFINED;
    if (SCM_UNBNDP (rks_make_state_proc))
      rks_make_state_proc
        = scm_c_public_ref ("emacs read-key-sequence", "make-rks-state");
    SCM rec = SCM_CALL_0 (rks_make_state_proc);
    eassert (rks_state_depth < RKS_STATE_STACK_MAX);
    rks_state_stack[rks_state_depth++] = rec;
    /* M6i: load all 7 migrated scalars from the record at entry.
       For the outermost call the record defaults (0/nil/false)
       match the static zero-init.  For nested calls (recursive
       edit), this restores the saved state.  */
    rks_t = rks_get_int (rec, RKS_SLOT_KEY_COUNT);
    rks_mock_input = rks_get_int (rec, RKS_SLOT_MOCK_INPUT);
    rks_current_binding = scm_struct_ref (rec,
                             scm_from_int (RKS_SLOT_CURRENT_BINDING));
  }

  /* How many keys there are in the current key sequence.
     M6m: promoted to file-static rks_t, aliased here.  */
#define t rks_t

  /* The length of the echo buffer when we started reading, and
     the length of this_command_keys when we started reading.  */
  /* M6j: echo_start and keys_start were locals here; promoted to
     the file-static rks_echo_start / rks_keys_start (declared below)
     so the Scheme rks-setup-initial-state-c! can write them and the
     C state machine continues to read them.  See docs/keyboard.org §M6j.  */

  /* M6m: current_binding promoted to file-static rks_current_binding.  */
#define current_binding rks_current_binding

  /* Index of the first key that has no binding.
     It is useless to try fkey.start larger than that.
     M6m/Wave C: retired — reads from record slot.  */

  /* If t < mock_input, then KEYBUF[t] should be read as the next
     input key.

     We use this to recover after recognizing a function key.  Once we
     realize that a suffix of the current key sequence is actually a
     function key's escape sequence, we replace the suffix with the
     function key's binding from Vfunction_key_map.  Now keybuf
     contains a new and different key sequence, so the echo area,
     this_command_keys, and the submaps and defs arrays are wrong.  In
     this situation, we set mock_input to t, set t to 0, and jump to
     restart_sequence; the loop will read keys from keybuf up until
     mock_input, thus rebuilding the state; and then it will resume
     reading characters from the keyboard.
     M6m: promoted to file-static rks_mock_input.  */
#define mock_input rks_mock_input

  /* Whether each event in the mocked input came from a mouse menu.
     M6z: promoted to file-static rks_used_mouse_menu_history.  Reset
     to all-false at function entry (the original local-array
     `= {0}' initializer).  */
  if (rks_state_depth > 0)
    rks_set_int (rks_state_stack[rks_state_depth - 1],
		 RKS_SLOT_USED_MOUSE_MENU_HISTORY, 0);

  /* If the sequence is unbound in submaps[], then
     keybuf[fkey.start..fkey.end-1] is a prefix in Vfunction_key_map,
     and fkey.map is its binding.

     These might be > t, indicating that all function key scanning
     should hold off until t reaches them.  We do this when we've just
     recognized a function key, to avoid searching for the function
     key's again in Vfunction_key_map.

     M6l: these three locals are file-static shadows
     (rks_fkey / rks_keytran / rks_indec) written by Scheme via
     --rks-init-keyremaps.  Phase 4 Step 3b-proper.2 deleted the
     in-function access sites; the post-done sync block below uses
     the rks_* names directly.  */

  /* (shift_translated retired — reads go through the record via
     --rks-shift-translated-p / --set-rks-shift-translated.)  */

  /* If we receive a `switch-frame' or `select-window' event in the middle of
     a key sequence, we put it off for later.
     While we're reading, we keep the event here.
     M6p/Wave C: retired — setter writes to record.  */

  /* M6r: original_uppercase + position promoted to file-static
     rks_original_uppercase / rks_original_uppercase_position.  */
/* (Retired — getter/setter use record.)  */

#ifdef HAVE_TEXT_CONVERSION
  /* M6ae: disabled_conversion promoted to file-static rks_disabled_conversion.
     Initialized to false at function entry (the original local-init).  */
  Fc_set_rks_disabled_conversion (Qnil);
#endif /* HAVE_TEXT_CONVERSION */

  /* M6m: starting_buffer promoted to file-static rks_starting_buffer.  */
  /* List of events for which a fake prefix key has been generated.  */
  /* M6ac/Wave C: fake_prefixed_keys retired — getter/setter use record.  */
  Fc_set_rks_fake_prefixed_keys (Qnil);

  /* raw_keybuf_count is now initialized in (most of) the callers of
     read_key_sequence.  This is so that in a recursive call (for
     mouse menus) a spurious initialization doesn't erase the contents
     of raw_keybuf created by the outer call.  */
  /* raw_keybuf_count = 0; */

  Fc_set_rks_delayed_switch_frame (Qnil);

  /* M6m: explicit init for the promoted file-statics that were
     previously initialized at their (now-removed) local declaration.
     The other promoted vars (t, first_unbound, starting_buffer) are
     written at the replay_sequence: label before being read.  */
  current_binding = Qnil;
  mock_input      = 0;

  dynwind_begin ();

  /* M6q: push our keybuf onto the rks_keybuf_stack so the elisp
     accessor subrs (`--rks-keybuf-ref' / `--rks-keybuf-set') see
     it.  Pop on dynwind unwind so recursive (mouse-menu) calls
     restore the caller's keybuf cleanly.  See docs/keyboard.org §M6q.  */
  eassert (rks_keybuf_depth < RKS_KEYBUF_STACK_MAX);
  record_unwind_protect_int (restore_rks_keybuf_depth, rks_keybuf_depth);
  rks_keybuf_stack[rks_keybuf_depth++] = keybuf;

  /* M6i: prompt + echo setup ported to (emacs read-key-sequence)
     rks-setup-prompt! — see docs/keyboard.org §M6i.  */
  {
    static SCM rks_setup_prompt_proc = SCM_UNDEFINED;
    if (SCM_UNBNDP (rks_setup_prompt_proc))
      rks_setup_prompt_proc = scm_c_public_ref ("emacs read-key-sequence",
                                                "rks-setup-prompt!");
    SCM_CALL_1 (rks_setup_prompt_proc, prompt);
  }

  /* Wave B: pre-loop initial-state capture folded into Scheme.  */
  {
    static SCM rks_setup_pre_loop_proc = SCM_UNDEFINED;
    if (SCM_UNBNDP (rks_setup_pre_loop_proc))
      rks_setup_pre_loop_proc =
        scm_c_public_ref ("emacs read-key-sequence",
                          "rks-setup-pre-loop!");
    SCM_CALL_0 (rks_setup_pre_loop_proc);
  }

  /* Initialize fkey/indec/keytran from current-kboard's translation
     maps + key-translation-map.  Vanilla emacs did this at the
     `replay_entire_sequence:' label which ran once on entry.  Without
     this, the three maps stay Qnil and `local-function-key-map'
     translations (like <return> -> RET) never fire.  */
  rks_call_setup_replay_entire_sequence ();

#ifdef HAVE_TEXT_CONVERSION
  record_unwind_protect_int (restore_reading_key_sequence,
			     reading_key_sequence);
  reading_key_sequence = true;
#endif

  /* Phase 4 Step 3b-proper.2: the replay_sequence: label + the C
     while-loop + the done: label are subsumed by the Scheme
     rks-state-machine call below.  The state machine's entry
     invokes replay-sequence-continue itself; each internal
     replay-sequence dispatch re-invokes it.  */

  /* If text conversion is supposed to be disabled immediately, do
     it now.  Idempotent (the slot stays Qt and disable_text_conversion
     is no-op once set), so one-time entry is sufficient.  */
#ifdef HAVE_TEXT_CONVERSION
  if (disable_text_conversion_p)
    {
      disable_text_conversion ();
      record_unwind_protect_void (resume_text_conversion);
      Fc_set_rks_disabled_conversion (Qt);
    }
#endif /* HAVE_TEXT_CONVERSION */

  /* Hand off to the Scheme state machine.  Returns -1 (menu-reject)
     or the symbol `done'.  read_key_sequence_cmd is set only on the
     break-equivalent path (rks_t > 0); the goto-done-equivalent
     path (rks-iteration-prepare! 'done with rks_t = 0) skipped the
     assignment in the C original.  */
  {
    static SCM rks_sm_proc = SCM_UNDEFINED;
    if (SCM_UNBNDP (rks_sm_proc))
      rks_sm_proc = scm_c_public_ref ("emacs read-key-sequence",
                                      "rks-state-machine");
    SCM sm_result = scm_call_4 (rks_sm_proc,
                                prompt,
                                can_return_switch_frame ? Qt : Qnil,
                                prevent_redisplay ? Qt : Qnil,
                                fix_current_buffer ? Qt : Qnil);
    if (FIXNUMP (sm_result) && XFIXNUM (sm_result) == -1)
      {
        dynwind_end ();
        return -1;
      }
    if (rks_t > 0)
      read_key_sequence_cmd = current_binding;
  }

  /* (C while-loop + replay_sequence: + have_key: + done: labels
     deleted in Step 3b-proper.2 — all subsumed by the Scheme state
     machine call above.)  */
  /* M6n: remapping computation ported to (emacs read-key-sequence)
     rks-done-compute-remapped!  Does this here (before dynwind_end) so
     `command-remapping' sees the right keymap stack.  See
     docs/keyboard.org §M6n.  */
  {
    static SCM rks_done_remapped_proc = SCM_UNDEFINED;
    if (SCM_UNBNDP (rks_done_remapped_proc))
      rks_done_remapped_proc =
        scm_c_public_ref ("emacs read-key-sequence",
                          "rks-done-compute-remapped!");
    SCM_CALL_0 (rks_done_remapped_proc);
  }

  /* M6p: unread_switch_frame install ported to (emacs read-key-sequence)
     rks-done-install-unread-switch-frame!.  Runs before dynwind_end
     so it sees the same dynwind context as the original.  See
     docs/keyboard.org §M6p.  */
  {
    static SCM rks_done_unread_sf_proc = SCM_UNDEFINED;
    if (SCM_UNBNDP (rks_done_unread_sf_proc))
      rks_done_unread_sf_proc =
        scm_c_public_ref ("emacs read-key-sequence",
                          "rks-done-install-unread-switch-frame!");
    SCM_CALL_0 (rks_done_unread_sf_proc);
  }
  dynwind_end ();

  /* Wave B: post-dynwind done: body (downcase-undo, shift-translated,
     fabricated-events) folded into one Scheme call.  */
  {
    static SCM rks_done_post_proc = SCM_UNDEFINED;
    if (SCM_UNBNDP (rks_done_post_proc))
      rks_done_post_proc =
        scm_c_public_ref ("emacs read-key-sequence",
                          "rks-done-post-dynwind!");
    SCM_CALL_1 (rks_done_post_proc,
                dont_downcase_last ? Qt : Qnil);
  }

  /* M6 Step B: sync iteration-local file-statics → record so the
     record captures final state.  C-9b deleted the keyremap sync
     here — keyremap state is record-authoritative.  */
  {
    SCM rec = rks_state_stack[rks_state_depth - 1];
    rks_set_int (rec, RKS_SLOT_KEY_COUNT, rks_t);
    rks_set_int (rec, RKS_SLOT_MOCK_INPUT, rks_mock_input);
    rc_set (rec, RKS_SLOT_CURRENT_BINDING, rks_current_binding);
    rks_state_stack[--rks_state_depth] = SCM_UNDEFINED;
  }

  return t;
}

#undef t
#undef mock_input
#undef current_binding

/* M6a — primitives exposed to (emacs read-key-sequence) for the
   outer wrapper port.  The state machine (read_key_sequence above)
   stays C; M6b–M6f will incrementally move parts of it to Scheme.
   See docs/keyboard.org §M6a.  */

DEFUN ("--read-key-sequence-and-vector",
       Fc_read_key_sequence_and_vector,
       Sc_read_key_sequence_and_vector, 4, 4, 0,
       doc: /* Internal: invoke the C read_key_sequence state machine with
PROMPT, DONT-DOWNCASE-LAST, CAN-RETURN-SWITCH-FRAME, DISABLE-TEXT-CONVERSION.
Returns the read keys as a Lisp vector of length i, or the fixnum -1
on quit (i == -1).  The caller is responsible for the specbind
housekeeping (input-method-exit-on-first-char,
input-method-use-echo-area) and any quit handling.  */)
  (Lisp_Object prompt, Lisp_Object dont_downcase_last,
   Lisp_Object can_return_switch_frame,
   Lisp_Object disable_text_conversion)
{
  if (!NILP (prompt))
    CHECK_STRING (prompt);
  Lisp_Object keybuf[READ_KEY_ELTS];
  int i = read_key_sequence (keybuf, prompt,
                             !NILP (dont_downcase_last),
                             !NILP (can_return_switch_frame),
                             false, false,
                             !NILP (disable_text_conversion));
  if (i == -1)
    return make_fixnum (-1);
  Lisp_Object result = scm_c_make_vector (i, Qnil);
  for (ptrdiff_t j = 0; j < i; j++)
    GASET (result, j, keybuf[j]);
  return result;
}

DEFUN ("read-key-sequence", Fread_key_sequence, Sread_key_sequence, 1, 6, 0,
       doc: /* Read a sequence of keystrokes and return as a string or vector.
The sequence is sufficient to specify a non-prefix command in the
current local and global maps.

First arg PROMPT is a prompt string.  If nil, do not prompt specially.
Second (optional) arg CONTINUE-ECHO, if non-nil, means this key echos
as a continuation of the previous key.

The third (optional) arg DONT-DOWNCASE-LAST, if non-nil, means do not
convert the last event to lower case.  (Normally any upper case event
is converted to lower case if the original event is undefined and the lower
case equivalent is defined.)  A non-nil value is appropriate for reading
a key sequence to be defined.

A C-g typed while in this function is treated like any other character,
and `quit-flag' is not set.

If the key sequence starts with a mouse click, then the sequence is read
using the keymaps of the buffer of the window clicked in, not the buffer
of the selected window as normal.

`read-key-sequence' drops unbound button-down events, since you normally
only care about the click or drag events which follow them.  If a drag
or multi-click event is unbound, but the corresponding click event would
be bound, `read-key-sequence' turns the event into a click event at the
drag's starting position.  This means that you don't have to distinguish
between click and drag, double, or triple events unless you want to.

`read-key-sequence' prefixes mouse events on mode lines, the vertical
lines separating windows, and scroll bars with imaginary keys
`mode-line', `vertical-line', and `vertical-scroll-bar'.

Optional fourth argument CAN-RETURN-SWITCH-FRAME non-nil means that this
function will process a switch-frame event if the user switches frames
before typing anything.  If the user switches frames in the middle of a
key sequence, or at the start of the sequence but CAN-RETURN-SWITCH-FRAME
is nil, then the event will be put off until after the current key sequence.

`read-key-sequence' checks `function-key-map' for function key
sequences, where they wouldn't conflict with ordinary bindings.  See
`function-key-map' for more details.

The optional fifth argument CMD-LOOP, if non-nil, means
that this key sequence is being read by something that will
read commands one after another.  It should be nil if the caller
will read just one key sequence.

The optional sixth argument DISABLE-TEXT-CONVERSION, if non-nil, means
disable input method text conversion for the duration of reading this
key sequence, and that keyboard input will always result in key events
being sent.  */)
  (Lisp_Object prompt, Lisp_Object continue_echo, Lisp_Object dont_downcase_last,
   Lisp_Object can_return_switch_frame, Lisp_Object cmd_loop,
   Lisp_Object disable_text_conversion)
{
  /* M6a: dispatch to (emacs read-key-sequence) — see docs/keyboard.org §M6a.  */
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs read-key-sequence", "read-key-sequence-vs-string");
  SCM args[6] = { prompt, continue_echo, dont_downcase_last,
                  can_return_switch_frame, cmd_loop,
                  disable_text_conversion };
  return SCM_CALL_N (proc, args, 6);
}

DEFUN ("read-key-sequence-vector", Fread_key_sequence_vector,
       Sread_key_sequence_vector, 1, 6, 0,
       doc: /* Like `read-key-sequence' but always return a vector.  */)
  (Lisp_Object prompt, Lisp_Object continue_echo, Lisp_Object dont_downcase_last,
   Lisp_Object can_return_switch_frame, Lisp_Object cmd_loop,
   Lisp_Object disable_text_conversion)
{
  /* M6a: dispatch to (emacs read-key-sequence) — see docs/keyboard.org §M6a.  */
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs read-key-sequence", "read-key-sequence-vs-vector");
  SCM args[6] = { prompt, continue_echo, dont_downcase_last,
                  can_return_switch_frame, cmd_loop,
                  disable_text_conversion };
  return SCM_CALL_N (proc, args, 6);
}

/* Return true if input events are pending.  */

bool
detect_input_pending (void)
{
  return input_pending || get_input_pending (0);
}

/* Return true if input events other than mouse movements are
   pending.  */

bool
detect_input_pending_ignore_squeezables (void)
{
  return input_pending || get_input_pending (READABLE_EVENTS_IGNORE_SQUEEZABLES);
}

/* Return true if input events are pending, and run any pending timers.  */

bool
detect_input_pending_run_timers (bool do_display)
{
  unsigned old_timers_run = timers_run;

  if (!input_pending)
    get_input_pending (READABLE_EVENTS_DO_TIMERS_NOW);

  if (old_timers_run != timers_run && do_display)
    redisplay_preserve_echo_area (8);

  return input_pending;
}

/* This is called in some cases before a possible quit.
   It cases the next call to detect_input_pending to recompute input_pending.
   So calling this function unnecessarily can't do any harm.  */

void
clear_input_pending (void)
{
  input_pending = false;
}

/* Return true if there are pending requeued command events.  */

bool
requeued_command_events_pending_p (void)
{
  return (CONSP (Vunread_command_events));
}

/* Return true if there are any pending requeued events (command events
   or events to be processed by other levels of the input processing
   stages).  */

bool
requeued_events_pending_p (void)
{
  return (requeued_command_events_pending_p ()
	  || !NILP (Vunread_post_input_method_events)
	  || !NILP (Vunread_input_method_events));
}

/* M6e — primitives exposed to (emacs read-key-sequence) for the
   input-pending-p port.  See docs/keyboard.org §M6e.  */

DEFUN ("--requeued-events-pending-p", Fc_requeued_events_pending_p,
       Sc_requeued_events_pending_p, 0, 0, 0,
       doc: /* Internal: t if any events have been requeued (waiting
in `unread-command-events' and friends).  */)
  (void)
{
  return requeued_events_pending_p () ? Qt : Qnil;
}

DEFUN ("--process-special-events", Fc_process_special_events,
       Sc_process_special_events, 0, 0, 0,
       doc: /* Internal: process non-user-visible events queued in the
input buffer (Bug#10195).  */)
  (void)
{
  process_special_events ();
  return Qnil;
}

DEFUN ("--get-input-pending", Fc_get_input_pending,
       Sc_get_input_pending, 1, 1, 0,
       doc: /* Internal: t if get_input_pending (FLAGS) reports a pending
event.  FLAGS is a fixnum bitmask (1 = DO_TIMERS_NOW, 2 = FILTER_EVENTS,
4 = IGNORE_SQUEEZABLES).  */)
  (Lisp_Object flags)
{
  CHECK_FIXNUM (flags);
  return get_input_pending (XFIXNUM (flags)) ? Qt : Qnil;
}

DEFUN ("input-pending-p", Finput_pending_p, Sinput_pending_p, 0, 1, 0,
       doc: /* Return t if command input is currently available with no wait.
Actually, the value is nil only if we can be sure that no input is available;
if there is a doubt, the value is t.

If CHECK-TIMERS is non-nil, timers that are ready to run will do so.  */)
  (Lisp_Object check_timers)
{
  /* M6e: dispatch to (emacs read-key-sequence) — see docs/keyboard.org §M6e.  */
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs read-key-sequence", "input-pending-p");
  return SCM_CALL_1 (proc, check_timers);
}

/* Reallocate recent_keys copying the recorded keystrokes
   in the right order.  */
static void
update_recent_keys (int new_size, int kept_keys)
{
  int osize = ASIZE (recent_keys);
  eassert (recent_keys_index < osize);
  eassert (kept_keys <= min (osize, new_size));
  Lisp_Object v = make_nil_elisp_vector (new_size);
  int i, idx;
  for (i = 0; i < kept_keys; ++i)
    {
      idx = recent_keys_index - kept_keys + i;
      while (idx < 0)
        idx += osize;
      ASET (v, i, AREF (recent_keys, idx));
    }
  recent_keys = v;
  total_keys = kept_keys;
  recent_keys_index = total_keys % new_size;
  lossage_limit = new_size;

}

/* M3 — primitives exposed to (emacs recent-keys).  The recent_keys
   ring stays C-owned; the Scheme module reads its state through these
   subrs.  See docs/keyboard.org §M3.  */

DEFUN ("--recent-keys-ring", Frecent_keys_ring, Srecent_keys_ring, 0, 0, 0,
       doc: /* Internal: return the raw recent-keys ring vector.  */)
  (void)
{
  return recent_keys;
}

DEFUN ("--recent-keys-index", Frecent_keys_index, Srecent_keys_index, 0, 0, 0,
       doc: /* Internal: return the next-write index into the recent-keys ring.  */)
  (void)
{
  return make_fixnum (recent_keys_index);
}

DEFUN ("--total-keys", Ftotal_keys, Stotal_keys, 0, 0, 0,
       doc: /* Internal: return the count of keys recorded since startup
(capped at the ring size).  */)
  (void)
{
  return make_fixnum (total_keys);
}

DEFUN ("--lossage-limit", Flossage_limit, Slossage_limit, 0, 0, 0,
       doc: /* Internal: return the current recent-keys ring size.  */)
  (void)
{
  return make_fixnum (lossage_limit);
}

DEFUN ("--min-num-recent-keys", Fmin_num_recent_keys, Smin_num_recent_keys, 0, 0, 0,
       doc: /* Internal: lower bound on the recent-keys ring size.  */)
  (void)
{
  return make_fixnum (MIN_NUM_RECENT_KEYS);
}

DEFUN ("--max-num-recent-keys", Fmax_num_recent_keys, Smax_num_recent_keys, 0, 0, 0,
       doc: /* Internal: upper bound on the recent-keys ring size.  */)
  (void)
{
  return make_fixnum (MAX_NUM_RECENT_KEYS);
}

DEFUN ("--update-recent-keys", Fupdate_recent_keys, Supdate_recent_keys,
       2, 2, 0,
       doc: /* Internal: resize the recent-keys ring to NEW-SIZE keeping
KEPT-KEYS entries; mirrors C update_recent_keys.  */)
  (Lisp_Object new_size, Lisp_Object kept_keys)
{
  CHECK_FIXNAT (new_size);
  CHECK_FIXNAT (kept_keys);
  update_recent_keys (XFIXNAT (new_size), XFIXNAT (kept_keys));
  return Qnil;
}

DEFUN ("--make-event-array-from-vector", Fmake_event_array_from_vector,
       Smake_event_array_from_vector, 3, 3, 0,
       doc: /* Internal: extract COUNT elements starting at START from VEC
and return as a string (if all events are simple characters) or a vector.
Mirrors C make_event_array_from_vector.  */)
  (Lisp_Object vec, Lisp_Object start, Lisp_Object count)
{
  CHECK_VECTOR (vec);
  CHECK_FIXNAT (start);
  CHECK_FIXNAT (count);
  return make_event_array_from_vector (vec, XFIXNAT (start), XFIXNAT (count));
}

DEFUN ("lossage-size", Flossage_size, Slossage_size, 0, 1,
       "(list (read-number \"Set maximum keystrokes to: \" (lossage-size)))",
       doc: /* Return or set the maximum number of keystrokes to save.
If called with a non-nil ARG, set the limit to ARG and return it.
Otherwise, return the current limit.

The saved keystrokes are shown by `view-lossage'.  */)
  (Lisp_Object arg)
{
  /* M3: dispatch to (emacs recent-keys) — see docs/keyboard.org §M3. */
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs recent-keys", "lossage-size");
  return SCM_CALL_1 (proc, arg);
}

DEFUN ("recent-keys", Frecent_keys, Srecent_keys, 0, 1, 0,
       doc: /* Return vector of last few events, not counting those from keyboard macros.
If INCLUDE-CMDS is non-nil, include the commands that were run,
represented as pseudo-events of the form (nil . COMMAND).  */)
  (Lisp_Object include_cmds)
{
  /* M3: dispatch to (emacs recent-keys) — see docs/keyboard.org §M3. */
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs recent-keys", "recent-keys");
  return SCM_CALL_1 (proc, include_cmds);
}

/* M5 — primitives exposed to (emacs this-command-keys).  The
   this-command-keys vector and raw_keybuf stay C-owned; the Scheme
   module reads their state through these `--' subrs.  See
   docs/keyboard.org §M5.  */

DEFUN ("--this-command-keys", Fc_this_command_keys, Sc_this_command_keys, 0, 0, 0,
       doc: /* Internal: return the raw this_command_keys vector.  */)
  (void)
{
  return this_command_keys;
}

DEFUN ("--this-command-key-count", Fc_this_command_key_count, Sc_this_command_key_count, 0, 0, 0,
       doc: /* Internal: return this_command_key_count.  */)
  (void)
{
  return make_fixnum (this_command_key_count);
}

DEFUN ("--raw-keybuf", Fc_raw_keybuf, Sc_raw_keybuf, 0, 0, 0,
       doc: /* Internal: return the raw_keybuf vector.  */)
  (void)
{
  return raw_keybuf;
}

DEFUN ("--raw-keybuf-count", Fc_raw_keybuf_count, Sc_raw_keybuf_count, 0, 0, 0,
       doc: /* Internal: return raw_keybuf_count.  */)
  (void)
{
  return make_fixnum (raw_keybuf_count);
}

DEFUN ("--this-single-command-key-start", Fc_this_single_command_key_start,
       Sc_this_single_command_key_start, 0, 0, 0,
       doc: /* Internal: return this_single_command_key_start.  Storage
lives in Scheme; this dispatches into (emacs this-command-keys)
this-single-command-key-start-get.  */)
  (void)
{
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs this-command-keys",
                             "this-single-command-key-start-get");
  return SCM_CALL_0 (proc);
}

DEFUN ("this-command-keys-vector", Fthis_command_keys_vector, Sthis_command_keys_vector, 0, 0, 0,
       doc: /* Return the key sequence that invoked this command, as a vector.
However, if the command has called `read-key-sequence', it returns
the last key sequence that has been read.

See also `this-command-keys'.  */)
  (void)
{
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs this-command-keys", "this-command-keys-vector");
  return SCM_CALL_0 (proc);
}

DEFUN ("--reset-this-command-keys", Fc_reset_this_command_keys,
       Sc_reset_this_command_keys, 0, 0, 0,
       doc: /* Internal: reset this_command_keys to a fresh 40-slot
vector and zero this_command_key_count.  Used by (emacs
this-command-keys) when it detects the post-GC string-corruption case
in this-command-keys-vector.  */)
  (void)
{
  this_command_keys = make_nil_elisp_vector (40);
  this_command_key_count = 0;
  return Qnil;
}

DEFUN ("--set-this-command-key-count", Fc_set_this_command_key_count,
       Sc_set_this_command_key_count, 1, 1, 0,
       doc: /* Internal: set this_command_key_count to N.  */)
  (Lisp_Object n)
{
  CHECK_FIXNAT (n);
  this_command_key_count = XFIXNAT (n);
  return Qnil;
}

DEFUN ("--clear-recent-keys-ring", Fc_clear_recent_keys_ring,
       Sc_clear_recent_keys_ring, 0, 0, 0,
       doc: /* Internal: zero out the recent_keys ring and reset
total_keys / recent_keys_index.  Used by
(emacs this-command-keys) clear-this-command-keys when KEEP-RECORD is
nil.  Mirrors the inner loop of the original C Fclear_this_command_keys.  */)
  (void)
{
  for (ptrdiff_t i = 0; i < ASIZE (recent_keys); ++i)
    ASET (recent_keys, i, Qnil);
  total_keys = 0;
  recent_keys_index = 0;
  return Qnil;
}

/* Consolidation: helpers used by set--this-command-keys in
   (emacs this-command-keys) when porting the M-x kludge from C.  */

DEFUN ("--add-command-key", Fc_add_command_key, Sc_add_command_key, 1, 1, 0,
       doc: /* Internal: append KEY to this_command_keys via the C
add_command_key helper.  Same defensive corruption check as the C
hot-path callers (read_char_1, read_key_sequence, set--this-command-keys).  */)
  (Lisp_Object key)
{
  add_command_key (key);
  return Qnil;
}

DEFUN ("--set-this-single-command-key-start", Fc_set_this_single_command_key_start,
       Sc_set_this_single_command_key_start, 1, 1, 0,
       doc: /* Internal: set this_single_command_key_start to N.
Storage lives in Scheme; this dispatches into (emacs this-command-keys)
this-single-command-key-start-set!.  */)
  (Lisp_Object n)
{
  CHECK_FIXNAT (n);
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs this-command-keys",
                             "this-single-command-key-start-set!");
  return SCM_CALL_1 (proc, n);
}








DEFUN ("open-dribble-file", Fopen_dribble_file, Sopen_dribble_file, 1, 1,
       "FOpen dribble file: ",
       doc: /* Start writing input events to a dribble file called FILE.
Any previously open dribble file will be closed first.  If FILE is
nil, just close the dribble file, if any.

If the file is still open when Emacs exits, it will be closed then.

The events written to the file include keyboard and mouse input
events, but not events from executing keyboard macros.  The events are
written to the dribble file immediately without line buffering.

Be aware that this records ALL characters you type!
This may include sensitive information such as passwords.  */)
  (Lisp_Object file)
{
  if (dribble)
    {
      block_input ();
      emacs_fclose (dribble);
      unblock_input ();
      dribble = 0;
    }
  if (!NILP (file))
    {
      int fd;
      Lisp_Object encfile;

      file = Fexpand_file_name (file, Qnil);
      encfile = ENCODE_FILE (file);
      fd = emacs_open (SSDATA (encfile), O_WRONLY | O_CREAT | O_EXCL, 0600);
      if (fd < 0 && errno == EEXIST
	  && (emacs_unlink (SSDATA (encfile)) == 0 || errno == ENOENT))
	fd = emacs_open (SSDATA (encfile), O_WRONLY | O_CREAT | O_EXCL, 0600);
      dribble = fd < 0 ? 0 : emacs_fdopen (fd, "w");
      if (dribble == 0)
	report_file_error ("Opening dribble", file);
    }
  return Qnil;
}

/* M6b — primitives exposed to (emacs read-key-sequence) for the
   discard-input port.  See docs/keyboard.org §M6b.  */

DEFUN ("--end-kbd-macro", Fc_end_kbd_macro, Sc_end_kbd_macro, 0, 0, 0,
       doc: /* Internal: invoke the C end_kbd_macro helper that finalizes
the current kbd-macro recording.  */)
  (void)
{
  end_kbd_macro ();
  return Qnil;
}

DEFUN ("--discard-tty-input", Fc_discard_tty_input, Sc_discard_tty_input,
       0, 0, 0,
       doc: /* Internal: drain any unread bytes from the TTY input buffer.  */)
  (void)
{
  discard_tty_input ();
  return Qnil;
}

DEFUN ("--reset-kbd-ring-and-pending", Fc_reset_kbd_ring_and_pending,
       Sc_reset_kbd_ring_and_pending, 0, 0, 0,
       doc: /* Internal: set kbd_fetch_ptr = kbd_store_ptr (empty the
queued-event ring) and clear input_pending.  */)
  (void)
{
  kbd_fetch_ptr = kbd_store_ptr;
  input_pending = false;
  return Qnil;
}

DEFUN ("discard-input", Fdiscard_input, Sdiscard_input, 0, 0, 0,
       doc: /* Discard the contents of the terminal input buffer.
Also end any kbd macro being defined.  */)
  (void)
{
  /* M6b: dispatch to (emacs read-key-sequence) — see docs/keyboard.org §M6b.  */
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs read-key-sequence", "discard-input");
  return SCM_CALL_0 (proc);
}

DEFUN ("suspend-emacs", Fsuspend_emacs, Ssuspend_emacs, 0, 1, "",
       doc: /* Stop Emacs and return to superior process.  You can resume later.
If `cannot-suspend' is non-nil, or if the system doesn't support job
control, run a subshell instead.

If optional arg STUFFSTRING is non-nil, its characters are stuffed
to be read as terminal input by Emacs's parent, after suspension.

Before suspending, run the normal hook `suspend-hook'.
After resumption run the normal hook `suspend-resume-hook'.

Some operating systems cannot stop the Emacs process and resume it later.
On such systems, Emacs starts a subshell instead of suspending.

On some operating systems, stuffing characters into terminal input
buffer requires special privileges or is not supported at all.
On such systems, calling this function with non-nil STUFFSTRING might
either signal an error or silently fail to stuff the characters.  */)
  (Lisp_Object stuffstring)
{
  dynwind_begin ();
  int old_height, old_width;
  int width, height;

  if (tty_list && tty_list->next)
    error ("There are other tty frames open; close them before suspending Emacs");

  if (!NILP (stuffstring))
    CHECK_STRING (stuffstring);

  run_hook (Qsuspend_hook);

  get_tty_size (fileno (CURTTY ()->input), &old_width, &old_height);
  reset_all_sys_modes ();
  /* sys_suspend can get an error if it tries to fork a subshell
     and the system resources aren't available for that.  */
  record_unwind_protect_void (init_all_sys_modes);
  stuff_buffered_input (stuffstring);
  if (cannot_suspend)
    sys_subshell ();
  else
    sys_suspend ();
  dynwind_end ();

  /* Check if terminal/window size has changed.
     Note that this is not useful when we are running directly
     with a window system; but suspend should be disabled in that case.  */
  get_tty_size (fileno (CURTTY ()->input), &width, &height);
  if (width != old_width || height != old_height)
    change_frame_size (SELECTED_FRAME (), width, height, false, false, false);

  run_hook (Qsuspend_resume_hook);

  return Qnil;
}

/* If STUFFSTRING is a string, stuff its contents as pending terminal input.
   Then in any case stuff anything Emacs has read ahead and not used.  */

void
stuff_buffered_input (Lisp_Object stuffstring)
{
#ifdef SIGTSTP  /* stuff_char is defined if SIGTSTP.  */
  register unsigned char *p;

  if (STRINGP (stuffstring))
    {
      register ptrdiff_t count;

      p = SDATA (stuffstring);
      count = SBYTES (stuffstring);
      while (count-- > 0)
	stuff_char (*p++);
      stuff_char ('\n');
    }

  /* Anything we have read ahead, put back for the shell to read.  */
  /* ?? What should this do when we have multiple keyboards??
     Should we ignore anything that was typed in at the "wrong" kboard?

     rms: we should stuff everything back into the kboard
     it came from.  */
  for (; kbd_fetch_ptr != kbd_store_ptr;
       kbd_fetch_ptr = next_kbd_event (kbd_fetch_ptr))
    {

      if (kbd_fetch_ptr->kind == ASCII_KEYSTROKE_EVENT)
	stuff_char (kbd_fetch_ptr->ie.code);

      clear_event (&kbd_fetch_ptr->ie);
    }

  input_pending = false;
#endif /* SIGTSTP */
}

void
set_waiting_for_input (struct timespec *time_to_clear)
{
  input_available_clear_time = time_to_clear;

  /* Tell handle_interrupt to throw back to read_char,  */
  waiting_for_input = true;

  /* If handle_interrupt was called before and buffered a C-g,
     make it run again now, to avoid timing error.  */
  if (!NILP (Vquit_flag))
    quit_throw_to_read_char (0);
}

void
clear_waiting_for_input (void)
{
  /* Tell handle_interrupt not to throw back to read_char,  */
  waiting_for_input = false;
  input_available_clear_time = 0;
}

/* The SIGINT handler.

   If we have a frame on the controlling tty, we assume that the
   SIGINT was generated by C-g, so we call handle_interrupt.
   Otherwise, tell maybe_quit to kill Emacs.  */

static void
handle_interrupt_signal (int sig)
{
  /* See if we have an active terminal on our controlling tty.  */
  struct terminal *terminal = get_named_terminal (dev_tty);
  if (!terminal)
    {
      /* If there are no frames there, let's pretend that we are a
         well-behaving UN*X program and quit.  We must not call Lisp
         in a signal handler, so tell maybe_quit to exit when it is
         safe.  */
      Vquit_flag = Qkill_emacs;
    }
  else
    {
      /* Otherwise, the SIGINT was probably generated by C-g.  */

      /* Set internal_last_event_frame to the top frame of the
         controlling tty, if we have a frame there.  We disable the
         interrupt key on secondary ttys, so the SIGINT must have come
         from the controlling tty.  */
      internal_last_event_frame = terminal->display_info.tty->top_frame;

      handle_interrupt (1);
    }
}

static void
deliver_interrupt_signal (int sig)
{
  deliver_process_signal (sig, handle_interrupt_signal);
}

/* Output MSG directly to standard output, without buffering.  Ignore
   failures.  This is safe in a signal handler.  */
static void
write_stdout (char const *msg)
{
  ignore_value (write (STDOUT_FILENO, msg, strlen (msg)));
}

/* Read a byte from stdin, without buffering.  Safe in signal handlers.  */
static int
read_stdin (void)
{
  char c;
  return read (STDIN_FILENO, &c, 1) == 1 ? c : EOF;
}

/* If Emacs is stuck because `inhibit-quit' is true, then keep track
   of the number of times C-g has been requested.  If C-g is pressed
   enough times, then quit anyway.  See bug#6585.  */
static int volatile force_quit_count;

/* This routine is called at interrupt level in response to C-g.

   It is called from the SIGINT handler or kbd_buffer_store_event.

   If `waiting_for_input' is non zero, then unless `echoing' is
   nonzero, immediately throw back to read_char.

   Otherwise it sets the Lisp variable quit-flag not-nil.  This causes
   eval to throw, when it gets a chance.  If quit-flag is already
   non-nil, it stops the job right away.  */

static void
handle_interrupt (bool in_signal_handler)
{
  char c;

  cancel_echoing ();

  /* XXX This code needs to be revised for multi-tty support.  */
  if (!NILP (Vquit_flag) && get_named_terminal (dev_tty))
    {
      if (! in_signal_handler)
	{
	  /* If SIGINT isn't blocked, don't let us be interrupted by
	     a SIGINT.  It might be harmful due to non-reentrancy
	     in I/O functions.  */
	  sigset_t blocked;
	  sigemptyset (&blocked);
	  sigaddset (&blocked, SIGINT);
	  pthread_sigmask (SIG_BLOCK, &blocked, 0);
	  fflush (stdout);
	}

      reset_all_sys_modes ();

#ifdef SIGTSTP
/*
 * On systems which can suspend the current process and return to the original
 * shell, this command causes the user to end up back at the shell.
 * The "Auto-save" and "Abort" questions are not asked until
 * the user elects to return to emacs, at which point he can save the current
 * job and either dump core or continue.
 */
      sys_suspend ();
#else
      /* Perhaps should really fork an inferior shell?
	 But that would not provide any way to get back
	 to the original shell, ever.  */
      write_stdout ("No support for stopping a process"
		    " on this operating system;\n"
		    "you can continue or abort.\n");
#endif /* not SIGTSTP */
#ifdef MSDOS
      /* We must remain inside the screen area when the internal terminal
	 is used.  Note that [Enter] is not echoed by dos.  */
      cursor_to (SELECTED_FRAME (), 0, 0);
#endif

      write_stdout ("Emacs is resuming after an emergency escape.\n");

	  write_stdout ("Auto-save? (y or n) ");
	  c = read_stdin ();
	  if (c == 'y' || c == 'Y')
	    {
	      Fdo_auto_save (Qt, Qnil);
#ifdef MSDOS
	      write_stdout ("\r\nAuto-save done");
#else
	      write_stdout ("Auto-save done\n");
#endif
	    }
	  while (c != '\n')
	    c = read_stdin ();

#ifdef MSDOS
      write_stdout ("\r\nAbort?  (y or n) ");
#else
      write_stdout ("Abort (and dump core)? (y or n) ");
#endif
      c = read_stdin ();
      if (c == 'y' || c == 'Y')
	emacs_abort ();
      while (c != '\n')
	c = read_stdin ();
#ifdef MSDOS
      write_stdout ("\r\nContinuing...\r\n");
#else /* not MSDOS */
      write_stdout ("Continuing...\n");
#endif /* not MSDOS */
      init_all_sys_modes ();
    }
  else
    {
      /* Request quit when it's safe.  */
      int count = NILP (Vquit_flag) ? 1 : force_quit_count + 1;
      force_quit_count = count;
      if (count == 3)
	Vinhibit_quit = Qnil;
      Vquit_flag = Qt;
    }

  pthread_sigmask (SIG_SETMASK, &empty_mask, 0);

/* TODO: The longjmp in this call throws the NS event loop integration off,
         and it seems to do fine without this.  Probably some attention
	 needs to be paid to the setting of waiting_for_input in
         wait_reading_process_output() under HAVE_NS because of the call
         to ns_select there (needed because otherwise events aren't picked up
         outside of polling since we don't get SIGIO like X and we don't have a
         separate event loop thread like W32.  */
#ifndef HAVE_NS
#ifdef THREADS_ENABLED
  /* If we were called from a signal handler, we must be in the main
     thread, see deliver_process_signal.  So we must make sure the
     main thread holds the global lock.  */
  if (in_signal_handler)
    maybe_reacquire_global_lock ();
#endif
  if (waiting_for_input && !echoing)
    quit_throw_to_read_char (in_signal_handler);
#endif
}

/* Handle a C-g by making read_char return C-g.  */

static void
quit_throw_to_read_char (bool from_signal)
{
  /* When not called from a signal handler it is safe to call
     Lisp.  */
  if (!from_signal && EQ (Vquit_flag, Qkill_emacs))
    Fkill_emacs (Qnil, Qnil);

  /* Prevent another signal from doing this before we finish.  */
  clear_waiting_for_input ();
  input_pending = false;

  Vunread_command_events = Qnil;

  if (FRAMEP (internal_last_event_frame)
      && !EQ (internal_last_event_frame, selected_frame))
    do_switch_frame (make_lispy_switch_frame (internal_last_event_frame),
		     0, 0, Qnil);

  abort_to_prompt (getctag, SCM_EOL);
}

DEFUN ("set-input-interrupt-mode", Fset_input_interrupt_mode,
       Sset_input_interrupt_mode, 1, 1, 0,
       doc: /* Set interrupt mode of reading keyboard input.
If INTERRUPT is non-nil, Emacs will use input interrupts;
otherwise Emacs uses CBREAK mode.

See also `current-input-mode'.  */)
  (Lisp_Object interrupt)
{
  bool new_interrupt_input;
#if defined (USABLE_SIGIO) || defined (USABLE_SIGPOLL)
#ifdef HAVE_X_WINDOWS
  if (x_display_list != NULL)
    {
      /* When using X, don't give the user a real choice,
	 because we haven't implemented the mechanisms to support it.  */
      new_interrupt_input = true;
    }
  else
#endif /* HAVE_X_WINDOWS */
    new_interrupt_input = !NILP (interrupt);
#else /* not USABLE_SIGIO || USABLE_SIGPOLL */
  new_interrupt_input = false;
#endif /* not USABLE_SIGIO || USABLE_SIGPOLL */

  if (new_interrupt_input != interrupt_input)
    {
#ifndef DOS_NT
      /* this causes startup screen to be restored and messes with the mouse */
      reset_all_sys_modes ();
      interrupt_input = new_interrupt_input;
      init_all_sys_modes ();
#else
      interrupt_input = new_interrupt_input;
#endif

#ifdef POLL_FOR_INPUT
      start_polling ();
#endif
    }
  return Qnil;
}

DEFUN ("set-output-flow-control", Fset_output_flow_control, Sset_output_flow_control, 1, 2, 0,
       doc: /* Enable or disable ^S/^Q flow control for output to TERMINAL.
If FLOW is non-nil, flow control is enabled and you cannot use C-s or
C-q in key sequences.

This setting only has an effect on tty terminals and only when
Emacs reads input in CBREAK mode; see `set-input-interrupt-mode'.

See also `current-input-mode'.  */)
  (Lisp_Object flow, Lisp_Object terminal)
{
  struct terminal *t = decode_tty_terminal (terminal);
  struct tty_display_info *tty;

  if (!t)
    return Qnil;
  tty = t->display_info.tty;

  if (tty->flow_control != !NILP (flow))
    {
#ifndef DOS_NT
      /* This causes startup screen to be restored and messes with the mouse.  */
      reset_sys_modes (tty);
#endif

      tty->flow_control = !NILP (flow);

#ifndef DOS_NT
      init_sys_modes (tty);
#endif
    }
  return Qnil;
}

DEFUN ("set-input-meta-mode", Fset_input_meta_mode, Sset_input_meta_mode, 1, 2, 0,
       doc: /* Enable or disable 8-bit input on TERMINAL.
If META is t, Emacs will accept 8-bit input, and interpret the 8th
bit as the Meta modifier before it decodes the characters.

If META is `encoded', Emacs will interpret the 8th bit of single-byte
characters after decoding the characters.

If META is nil, Emacs will ignore the top bit, on the assumption it is
parity.

Otherwise, Emacs will accept and pass through 8-bit input without
specially interpreting the top bit.

This setting only has an effect on tty terminal devices.

Optional parameter TERMINAL specifies the tty terminal device to use.
It may be a terminal object, a frame, or nil for the terminal used by
the currently selected frame.

See also `current-input-mode'.  */)
  (Lisp_Object meta, Lisp_Object terminal)
{
  struct terminal *t = decode_tty_terminal (terminal);
  struct tty_display_info *tty;
  int new_meta;

  if (!t)
    return Qnil;
  tty = t->display_info.tty;

  if (NILP (meta))
    new_meta = 0;
  else if (EQ (meta, Qt))
    new_meta = 1;
  else if (EQ (meta, Qencoded))
    new_meta = 3;
  else
    new_meta = 2;

  if (tty->meta_key != new_meta)
    {
#ifndef DOS_NT
      /* this causes startup screen to be restored and messes with the mouse */
      reset_sys_modes (tty);
#endif

      tty->meta_key = new_meta;

#ifndef DOS_NT
      init_sys_modes (tty);
#endif
    }
  return Qnil;
}

DEFUN ("set-quit-char", Fset_quit_char, Sset_quit_char, 1, 1, 0,
       doc: /* Specify character used for quitting.
QUIT must be an ASCII character.

This function only has an effect on the controlling tty of the Emacs
process.

See also `current-input-mode'.  */)
  (Lisp_Object quit)
{
  struct terminal *t = get_named_terminal (dev_tty);
  struct tty_display_info *tty;

  if (!t)
    return Qnil;
  tty = t->display_info.tty;

  if (NILP (quit) || !FIXNUMP (quit) || XFIXNUM (quit) < 0 || XFIXNUM (quit) > 0400)
    error ("QUIT must be an ASCII character");

#ifndef DOS_NT
  /* this causes startup screen to be restored and messes with the mouse */
  reset_sys_modes (tty);
#endif

  /* Don't let this value be out of range.  */
  quit_char = XFIXNUM (quit) & (tty->meta_key == 0 ? 0177 : 0377);

#ifndef DOS_NT
  init_sys_modes (tty);
#endif

  return Qnil;
}

DEFUN ("set-input-mode", Fset_input_mode, Sset_input_mode, 3, 4, 0,
       doc: /* Set mode of reading keyboard input.
First arg INTERRUPT non-nil means use input interrupts;
 nil means use CBREAK mode.
Second arg FLOW non-nil means use ^S/^Q flow control for output to terminal
 (no effect except in CBREAK mode).
Third arg META t means accept 8-bit input (for a Meta key).
 META nil means ignore the top bit, on the assumption it is parity.
 META `encoded' means accept 8-bit input and interpret Meta after
   decoding the input characters.
 Otherwise, accept 8-bit input and don't use the top bit for Meta.
Optional fourth arg QUIT if non-nil specifies character to use for quitting.
See also `current-input-mode'.  */)
  (Lisp_Object interrupt, Lisp_Object flow, Lisp_Object meta, Lisp_Object quit)
{
  /* M6c: dispatch to (emacs read-key-sequence) — see docs/keyboard.org §M6c.  */
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs read-key-sequence", "set-input-mode");
  return SCM_CALL_4 (proc, interrupt, flow, meta, quit);
}

/* M6c — primitives exposed to (emacs read-key-sequence) for the
   current-input-mode port.  See docs/keyboard.org §M6c.  */

DEFUN ("--interrupt-input-p", Fc_interrupt_input_p, Sc_interrupt_input_p,
       0, 0, 0,
       doc: /* Internal: t if the C global `interrupt_input' is non-zero
(Emacs is using interrupt-driven input rather than CBREAK mode).  */)
  (void)
{
  return interrupt_input ? Qt : Qnil;
}

DEFUN ("--selected-frame-tty-p", Fc_selected_frame_tty_p,
       Sc_selected_frame_tty_p, 0, 0, 0,
       doc: /* Internal: t if the selected frame is a TTY frame (termcap
or msdos output-method).  */)
  (void)
{
  struct frame *sf = XFRAME (selected_frame);
  return (FRAME_TERMCAP_P (sf) || FRAME_MSDOS_P (sf)) ? Qt : Qnil;
}

DEFUN ("--selected-frame-tty-flow-control-p",
       Fc_selected_frame_tty_flow_control_p,
       Sc_selected_frame_tty_flow_control_p, 0, 0, 0,
       doc: /* Internal: t if FRAME_TTY (selected_frame)->flow_control is
non-zero.  Caller must verify --selected-frame-tty-p first; this
subr dereferences FRAME_TTY unconditionally.  */)
  (void)
{
  return FRAME_TTY (XFRAME (selected_frame))->flow_control ? Qt : Qnil;
}

DEFUN ("--selected-frame-tty-meta-key",
       Fc_selected_frame_tty_meta_key,
       Sc_selected_frame_tty_meta_key, 0, 0, 0,
       doc: /* Internal: return FRAME_TTY (selected_frame)->meta_key as
a small integer (0..3).  Caller must verify --selected-frame-tty-p
first; this subr dereferences FRAME_TTY unconditionally.  */)
  (void)
{
  return make_fixnum (FRAME_TTY (XFRAME (selected_frame))->meta_key);
}

DEFUN ("current-input-mode", Fcurrent_input_mode, Scurrent_input_mode, 0, 0, 0,
       doc: /* Return information about the way Emacs currently reads keyboard input.
The value is a list of the form (INTERRUPT FLOW META QUIT), where
  INTERRUPT is non-nil if Emacs is using interrupt-driven input; if
    nil, Emacs is using CBREAK mode.
  FLOW is non-nil if Emacs uses ^S/^Q flow control for output to the
    terminal; this does not apply if Emacs uses interrupt-driven input.
  META is t if accepting 8-bit unencoded input with 8th bit as Meta flag.
  META is `encoded' if accepting 8-bit encoded input with 8th bit as
    Meta flag which has to be interpreted after decoding the input.
  META is nil if ignoring the top bit of input, on the assumption that
    it is a parity bit.
  META is neither t nor nil if accepting 8-bit input and using
    all 8 bits as the character code.
  QUIT is the character Emacs currently uses to quit.
The elements of this list correspond to the arguments of
`set-input-mode'.  */)
  (void)
{
  /* M6c: dispatch to (emacs read-key-sequence) — see docs/keyboard.org §M6c.  */
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs read-key-sequence", "current-input-mode");
  return SCM_CALL_0 (proc);
}

DEFUN ("posn-at-x-y", Fposn_at_x_y, Sposn_at_x_y, 2, 4, 0,
       doc: /* Return position information for pixel coordinates X and Y.
By default, X and Y are relative to text area of the selected window.
Note that the text area includes the header-line and the tab-line of
the window, if any of them are present.
Optional third arg FRAME-OR-WINDOW non-nil specifies frame or window.
If optional fourth arg WHOLE is non-nil, X is relative to the left
edge of the window.

The return value is similar to a mouse click position:
   (WINDOW AREA-OR-POS (X . Y) TIMESTAMP OBJECT POS (COL . ROW)
    IMAGE (DX . DY) (WIDTH . HEIGHT))
The `posn-' functions access elements of such lists.  */)
  (Lisp_Object x, Lisp_Object y, Lisp_Object frame_or_window, Lisp_Object whole)
{
  CHECK_FIXNUM (x);
  /* We allow X of -1, for the newline in a R2L line that overflowed
     into the left fringe.  */
  if (XFIXNUM (x) != -1)
    CHECK_FIXNAT (x);
  CHECK_FIXNAT (y);

  if (NILP (frame_or_window))
    frame_or_window = selected_window;

  if (WINDOWP (frame_or_window))
    {
      struct window *w = decode_live_window (frame_or_window);

      XSETINT (x, (XFIXNUM (x)
		   + WINDOW_LEFT_EDGE_X (w)
		   + (NILP (whole)
		      ? window_box_left_offset (w, TEXT_AREA)
		      : 0)));
      XSETINT (y, WINDOW_TO_FRAME_PIXEL_Y (w, XFIXNUM (y)));
      frame_or_window = w->frame;
    }

  CHECK_LIVE_FRAME (frame_or_window);

  return make_lispy_position (XFRAME (frame_or_window), x, y, 0);
}

DEFUN ("posn-at-point", Fposn_at_point, Sposn_at_point, 0, 2, 0,
       doc: /* Return position information for buffer position POS in WINDOW.
POS defaults to point in WINDOW; WINDOW defaults to the selected window.

If POS is in invisible text or is hidden by `display' properties,
this function may report on buffer positions before or after POS.

Return nil if POS is not visible in WINDOW.  Otherwise,
the return value is similar to that returned by `event-start' for
a mouse click at the upper left corner of the glyph corresponding
to POS:
   (WINDOW AREA-OR-POS (X . Y) TIMESTAMP OBJECT POS (COL . ROW)
    IMAGE (DX . DY) (WIDTH . HEIGHT))
The `posn-' functions access elements of such lists.  */)
  (Lisp_Object pos, Lisp_Object window)
{
  /* M6d: dispatch to (emacs read-key-sequence) — see docs/keyboard.org §M6d.  */
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs read-key-sequence", "posn-at-point");
  return SCM_CALL_2 (proc, pos, window);
}

/* Set up a new kboard object with reasonable initial values.
   TYPE is a window system for which this keyboard is used.  */

static void
init_kboard (KBOARD *kb, Lisp_Object type)
{
  kset_overriding_terminal_local_map (kb, Qnil);
  kset_last_command (kb, Qnil);
  kset_real_last_command (kb, Qnil);
  kset_keyboard_translate_table (kb, Qnil);
  kset_last_repeatable_command (kb, Qnil);
  kset_prefix_arg (kb, Qnil);
  kset_last_prefix_arg (kb, Qnil);
  kset_kbd_queue (kb, Qnil);
  kb->kbd_queue_has_data = false;
  kb->immediate_echo = false;
  kset_echo_string (kb, Qnil);
  kset_echo_prompt (kb, Qnil);
  kb->kbd_macro_buffer = 0;
  kb->kbd_macro_bufsize = 0;
  kset_defining_kbd_macro (kb, Qnil);
  kset_last_kbd_macro (kb, Qnil);
  kb->reference_count = 0;
  kset_system_key_alist (kb, Qnil);
  kset_system_key_syms (kb, Qnil);
  kset_window_system (kb, type);
  kset_input_decode_map (kb, Fmake_sparse_keymap (Qnil));
  kset_local_function_key_map (kb, Fmake_sparse_keymap (Qnil));
  Fset_keymap_parent (KVAR (kb, Vlocal_function_key_map), Vfunction_key_map);
  kset_default_minibuffer_frame (kb, Qnil);
}

/* Allocate and basically initialize keyboard
   object to use with window system TYPE.  */

KBOARD *
allocate_kboard (Lisp_Object type)
{
  KBOARD *kb = xmalloc (sizeof *kb);

  init_kboard (kb, type);
  kb->next_kboard = all_kboards;
  all_kboards = kb;
  return kb;
}

/*
 * Destroy the contents of a kboard object, but not the object itself.
 * We use this just before deleting it, or if we're going to initialize
 * it a second time.
 */
static void
wipe_kboard (KBOARD *kb)
{
  xfree (kb->kbd_macro_buffer);
}

/* Free KB and memory referenced from it.  */

void
delete_kboard (KBOARD *kb)
{
  KBOARD **kbp;
  struct thread_state *thread;

  for (kbp = &all_kboards; *kbp != kb; kbp = &(*kbp)->next_kboard)
    if (*kbp == NULL)
      emacs_abort ();
  *kbp = kb->next_kboard;

  /* Prevent a dangling reference to KB.  */
  if (kb == current_kboard
      && FRAMEP (selected_frame)
      && FRAME_LIVE_P (XFRAME (selected_frame)))
    {
      current_kboard = FRAME_KBOARD (XFRAME (selected_frame));
      single_kboard = false;
      if (current_kboard == kb)
	emacs_abort ();
    }

  wipe_kboard (kb);
  xfree (kb);
}

void
init_keyboard (void)
{
  /* This is correct before outermost invocation of the editor loop.  */
  command_loop_level = -1;
  quit_char = Ctl ('g');
  Vunread_command_events = Qnil;
  last_command_event = Qnil;
  last_nonmenu_event = Qnil;
  last_input_event = Qnil;
  timer_idleness_start_time = invalid_timespec ();
  total_keys = 0;
  recent_keys_index = 0;
  kbd_fetch_ptr = kbd_buffer;
  kbd_store_ptr = kbd_buffer;
  track_mouse = Qnil;
  input_pending = false;
  interrupt_input_blocked = 0;
  pending_signals = false;

  virtual_core_pointer_name = build_string ("Virtual core pointer");
  virtual_core_keyboard_name = build_string ("Virtual core keyboard");
  Vlast_event_device = Qnil;

  /* This means that command_loop_1 won't try to select anything the first
     time through.  */
  internal_last_event_frame = Qnil;
  Vlast_event_frame = internal_last_event_frame;

  current_kboard = initial_kboard;
  /* Re-initialize the keyboard again.  */
  wipe_kboard (current_kboard);
  /* A value of nil for Vwindow_system normally means a tty, but we also use
     it for the initial terminal since there is no window system there.  */
  init_kboard (current_kboard, Qnil);

  if (!noninteractive)
    {
      /* Before multi-tty support, these handlers used to be installed
         only if the current session was a tty session.  Now an Emacs
         session may have multiple display types, so we always handle
         SIGINT.  There is special code in handle_interrupt_signal to exit
         Emacs on SIGINT when there are no termcap frames on the
         controlling terminal.  */
      struct sigaction action;
      emacs_sigaction_init (&action, deliver_interrupt_signal);
      sigaction (SIGINT, &action, 0);
#ifndef DOS_NT
      /* For systems with SysV TERMIO, C-g is set up for both SIGINT and
	 SIGQUIT and we can't tell which one it will give us.  */
      sigaction (SIGQUIT, &action, 0);
#endif /* not DOS_NT */
    }
#if defined (USABLE_SIGIO) || defined (USABLE_SIGPOLL)
  if (!noninteractive)
    {
      struct sigaction action;
      emacs_sigaction_init (&action, deliver_input_available_signal);
#ifdef USABLE_SIGIO
      sigaction (SIGIO, &action, 0);
#else
      sigaction (SIGPOLL, &action, 0);
#endif
    }
#endif

/* Use interrupt input by default, if it works and noninterrupt input
   has deficiencies.  */

#ifdef INTERRUPT_INPUT
  interrupt_input = 1;
#else
  interrupt_input = 0;
#endif

  pthread_sigmask (SIG_SETMASK, &empty_mask, 0);
  dribble = 0;

  if (keyboard_init_hook)
    (*keyboard_init_hook) ();

#ifdef POLL_FOR_INPUT
  poll_timer = NULL;
  start_polling ();
#endif
}

/* This type's only use is in syms_of_keyboard, to put properties on the
   event header symbols.  */
struct event_head
{
  short var;
  short kind;
};

static const struct event_head head_table[] = {
  {SYMBOL_INDEX (Qmouse_movement),      SYMBOL_INDEX (Qmouse_movement)},
  {SYMBOL_INDEX (Qscroll_bar_movement), SYMBOL_INDEX (Qmouse_movement)},

  /* Some of the event heads.  */
  {SYMBOL_INDEX (Qswitch_frame),        SYMBOL_INDEX (Qswitch_frame)},

  {SYMBOL_INDEX (Qfocus_in),            SYMBOL_INDEX (Qfocus_in)},
  {SYMBOL_INDEX (Qfocus_out),           SYMBOL_INDEX (Qfocus_out)},
  {SYMBOL_INDEX (Qmove_frame),          SYMBOL_INDEX (Qmove_frame)},
  {SYMBOL_INDEX (Qdelete_frame),        SYMBOL_INDEX (Qdelete_frame)},
  {SYMBOL_INDEX (Qiconify_frame),       SYMBOL_INDEX (Qiconify_frame)},
  {SYMBOL_INDEX (Qmake_frame_visible),  SYMBOL_INDEX (Qmake_frame_visible)},
  /* `select-window' should be handled just like `switch-frame'
     in read_key_sequence.  */
  {SYMBOL_INDEX (Qselect_window),       SYMBOL_INDEX (Qswitch_frame)},
  /* Touchscreen events should be prefixed by the posn.  */
  {SYMBOL_INDEX (Qtouchscreen_begin),	SYMBOL_INDEX (Qtouchscreen)},
  {SYMBOL_INDEX (Qtouchscreen_end),	SYMBOL_INDEX (Qtouchscreen)},
};

static Lisp_Object
init_while_no_input_ignore_events (void)
{
  Lisp_Object events = listn (9, Qselect_window, Qhelp_echo, Qmove_frame,
			      Qiconify_frame, Qmake_frame_visible,
			      Qfocus_in, Qfocus_out, Qconfig_changed_event,
			      Qselection_request);

#ifdef HAVE_DBUS
  events = Fcons (Qdbus_event, events);
#endif
#ifdef USE_FILE_NOTIFY
  events = Fcons (Qfile_notify, events);
#endif
#ifdef THREADS_ENABLED
  events = Fcons (Qthread_event, events);
#endif

  return events;
}

static bool
is_ignored_event (union buffered_input_event *event)
{
  Lisp_Object ignore_event;

  switch (event->kind)
    {
    case FOCUS_IN_EVENT: ignore_event = Qfocus_in; break;
    case FOCUS_OUT_EVENT: ignore_event = Qfocus_out; break;
    case HELP_EVENT: ignore_event = Qhelp_echo; break;
    case ICONIFY_EVENT: ignore_event = Qiconify_frame; break;
    case DEICONIFY_EVENT: ignore_event = Qmake_frame_visible; break;
    case SELECTION_REQUEST_EVENT: ignore_event = Qselection_request; break;
#ifdef USE_FILE_NOTIFY
    case FILE_NOTIFY_EVENT: ignore_event = Qfile_notify; break;
#endif
#ifdef HAVE_DBUS
    case DBUS_EVENT: ignore_event = Qdbus_event; break;
#endif
    default: ignore_event = Qnil; break;
    }

  return !NILP (Fmemq (ignore_event, Vwhile_no_input_ignore_events));
}

void
syms_of_keyboard (void)
{
#include "keyboard.x"

  pending_funcalls = Qnil;
  staticpro (&pending_funcalls);

  /* M6 — initialize and protect the read_key_sequence file-static
     Lisp_Object shadows.  These are Qnil at startup so the elisp
     getter subrs return a valid value even before read_key_sequence
     has ever been entered.  See docs/keyboard.org §M6.  */
  rks_current_binding      = Qnil;
  staticpro (&rks_current_binding);
  rks_key                  = Qnil;
  staticpro (&rks_key);
  /* C-9b: rks_fkey/keytran/indec staticpro retired with the structs.  */

  Vlispy_mouse_stem = build_pure_c_string ("mouse");
  staticpro (&Vlispy_mouse_stem);

  DEFVAR_LISP ("internal--top-level-message", Vinternal__top_level_message,
	       doc: /* Message displayed by `normal-top-level'.  */);
  Vinternal__top_level_message = build_pure_c_string ("Back to top level");

  /* M2 — predicate symbol for the kboard smob type.  */
  DEFSYM (Qkboardp, "kboardp");

  /* M9 — register ie-smob hooks and predicate symbol.  */
  scm_set_smob_mark (ie_tag, ie_mark);
  scm_set_smob_free (ie_tag, ie_free);
  scm_set_smob_print (ie_tag, ie_print);
  DEFSYM (Qiep, "iep");

  /* Tool-bars.  */
  DEFSYM (QCimage, ":image");
  DEFSYM (Qhelp_echo, "help-echo");
  DEFSYM (Qhelp_echo_inhibit_substitution, "help-echo-inhibit-substitution");
  DEFSYM (QCrtl, ":rtl");
  DEFSYM (QCwrap, ":wrap");

  staticpro (&item_properties);
  item_properties = Qnil;

  staticpro (&tab_bar_item_properties);
  tab_bar_item_properties = Qnil;
  staticpro (&tab_bar_items_vector);
  tab_bar_items_vector = Qnil;

  staticpro (&tool_bar_item_properties);
  tool_bar_item_properties = Qnil;
  staticpro (&tool_bar_items_vector);
  tool_bar_items_vector = Qnil;

  DEFSYM (Qtimer_event_handler, "timer-event-handler");

  /* Non-nil disable property on a command means do not execute it;
     call disabled-command-function's value instead.  */
  DEFSYM (Qdisabled, "disabled");

  DEFSYM (Qundefined, "undefined");

  /* Hooks to run before and after each command.  */
  DEFSYM (Qpre_command_hook, "pre-command-hook");
  DEFSYM (Qpost_command_hook, "post-command-hook");
  DEFSYM (Qlong_line_optimizations_in_command_hooks,
	  "long-line-optimizations-in-command-hooks");

  /* Hook run after the region is selected.  */
  DEFSYM (Qpost_select_region_hook, "post-select-region-hook");

  DEFSYM (Qundo_auto__add_boundary, "undo-auto--add-boundary");
  DEFSYM (Qundo_auto__undoably_changed_buffers,
          "undo-auto--undoably-changed-buffers");

  DEFSYM (Qdelayed_warnings_hook, "delayed-warnings-hook");
  DEFSYM (Qfunction_key, "function-key");

  /* The values of Qevent_kind properties.  */
  DEFSYM (Qmouse_click, "mouse-click");
  DEFSYM (Qwheel_event, "wheel-event");
  DEFSYM (Qhorizontal_wheel_event, "horizontal-wheel-event");

  DEFSYM (Qdrag_n_drop, "drag-n-drop");
#ifdef USE_TOOLKIT_SCROLL_BARS
  DEFSYM (Qscroll_bar_click_toolkit, "scroll-bar-click-toolkit");
  DEFSYM (Qhorizontal_scroll_bar_click_toolkit,
          "horizontal-scroll-bar-click-toolkit");
#endif

  /* Mouse + scroll-bar event-kind keys (imp-7.5).  */
  DEFSYM (Qmouse_click_event, "mouse-click-event");
#ifndef USE_TOOLKIT_SCROLL_BARS
  DEFSYM (Qscroll_bar_click_event, "scroll-bar-click-event");
  DEFSYM (Qhorizontal_scroll_bar_click_event,
          "horizontal-scroll-bar-click-event");
#endif

  /* Keystroke event-kind keys (imp-5).  */
  DEFSYM (Qascii_keystroke, "ascii-keystroke");
  DEFSYM (Qmultibyte_char_keystroke, "multibyte-char-keystroke");
  DEFSYM (Qnon_ascii_keystroke, "non-ascii-keystroke");
#ifdef HAVE_NS
  DEFSYM (Qns_nonkey, "ns-nonkey");
  DEFSYM (Qns_text_event, "ns-text-event");
#endif
#ifdef HAVE_NTGUI
  DEFSYM (Qmultimedia_key, "multimedia-key");
#endif
  DEFSYM (Qsave_session, "save-session");
  DEFSYM (Qconfig_changed_event, "config-changed-event");
  DEFSYM (Quser_signal_event, "user-signal-event");

  /* Menu and tool bar item parts.  */
  DEFSYM (Qmenu_enable, "menu-enable");

#ifdef HAVE_NTGUI
  DEFSYM (Qlanguage_change, "language-change");
  DEFSYM (Qend_session, "end-session");
#endif

#ifdef HAVE_DBUS
  DEFSYM (Qdbus_event, "dbus-event");
#endif

#ifdef THREADS_ENABLED
  DEFSYM (Qthread_event, "thread-event");
#endif

#ifdef HAVE_XWIDGETS
  DEFSYM (Qxwidget_event, "xwidget-event");
  DEFSYM (Qxwidget_display_event, "xwidget-display-event");
#endif

#ifdef USE_FILE_NOTIFY
  DEFSYM (Qfile_notify, "file-notify");
#endif /* USE_FILE_NOTIFY */

  DEFSYM (Qtouch_end, "touch-end");

  /* Menu and tool bar item parts.  */
  DEFSYM (QCenable, ":enable");
  DEFSYM (QCvisible, ":visible");
  DEFSYM (QChelp, ":help");
  DEFSYM (QCfilter, ":filter");
  DEFSYM (QCbutton, ":button");
  DEFSYM (QCkeys, ":keys");
  DEFSYM (QCkey_sequence, ":key-sequence");

  /* Non-nil disable property on a command means
     do not execute it; call disabled-command-function's value instead.  */
  DEFSYM (QCtoggle, ":toggle");
  DEFSYM (QCradio, ":radio");
  DEFSYM (QClabel, ":label");
  DEFSYM (QCvert_only, ":vert-only");

  /* Symbols to use for parts of windows.  */
  DEFSYM (Qvertical_line, "vertical-line");
  DEFSYM (Qright_divider, "right-divider");
  DEFSYM (Qbottom_divider, "bottom-divider");

  DEFSYM (Qmouse_fixup_help_message, "mouse-fixup-help-message");

  DEFSYM (Qabove_handle, "above-handle");
  DEFSYM (Qhandle, "handle");
  DEFSYM (Qbelow_handle, "below-handle");
  DEFSYM (Qup, "up");
  DEFSYM (Qdown, "down");
  DEFSYM (Qtop, "top");
  DEFSYM (Qbottom, "bottom");
  DEFSYM (Qend_scroll, "end-scroll");
  DEFSYM (Qratio, "ratio");
  DEFSYM (Qbefore_handle, "before-handle");
  DEFSYM (Qhorizontal_handle, "horizontal-handle");
  DEFSYM (Qafter_handle, "after-handle");
  DEFSYM (Qleftmost, "leftmost");
  DEFSYM (Qrightmost, "rightmost");

  /* Properties of event headers.  */
  DEFSYM (Qevent_kind, "event-kind");
  DEFSYM (Qevent_symbol_elements, "event-symbol-elements");

  /* An event header symbol HEAD may have a property named
     Qevent_symbol_element_mask, which is of the form (BASE MODIFIERS);
     BASE is the base, unmodified version of HEAD, and MODIFIERS is the
     mask of modifiers applied to it.  If present, this is used to help
     speed up parse_modifiers.  */
  DEFSYM (Qevent_symbol_element_mask, "event-symbol-element-mask");

  /* An unmodified event header BASE may have a property named
     Qmodifier_cache, which is an alist mapping modifier masks onto
     modified versions of BASE.  If present, this helps speed up
     apply_modifiers.  */
  DEFSYM (Qmodifier_cache, "modifier-cache");

  DEFSYM (Qactivate_menubar_hook, "activate-menubar-hook");

  DEFSYM (Qpolling_period, "polling-period");

  DEFSYM (Qgui_set_selection, "gui-set-selection");
  DEFSYM (Qxterm__set_selection, "xterm--set-selection");
  DEFSYM (Qtty_select_active_regions, "tty-select-active-regions");

  /* The primary selection.  */
  DEFSYM (QPRIMARY, "PRIMARY");

  DEFSYM (Qhandle_switch_frame, "handle-switch-frame");
  DEFSYM (Qhandle_select_window, "handle-select-window");

  DEFSYM (Qinput_method_exit_on_first_char, "input-method-exit-on-first-char");
  DEFSYM (Qinput_method_use_echo_area, "input-method-use-echo-area");

  DEFSYM (Qhelp_form_show, "help-form-show");

  DEFSYM (Qhelp_key_binding, "help-key-binding");

  DEFSYM (Qhelp__append_keystrokes_help, "help--append-keystrokes-help");

  DEFSYM (Qecho_keystrokes, "echo-keystrokes");

  Fset (Qinput_method_exit_on_first_char, Qnil);
  Fset (Qinput_method_use_echo_area, Qnil);

  /* Symbols for dragging internal borders.  */
  DEFSYM (Qdrag_internal_border, "drag-internal-border");
  DEFSYM (Qleft_edge, "left-edge");
  DEFSYM (Qtop_left_corner, "top-left-corner");
  DEFSYM (Qtop_edge, "top-edge");
  DEFSYM (Qtop_right_corner, "top-right-corner");
  DEFSYM (Qright_edge, "right-edge");
  DEFSYM (Qbottom_right_corner, "bottom-right-corner");
  DEFSYM (Qbottom_edge, "bottom-edge");
  DEFSYM (Qbottom_left_corner, "bottom-left-corner");

  /* Symbols to head events.  */
  DEFSYM (Qmouse_movement, "mouse-movement");
  DEFSYM (Qscroll_bar_movement, "scroll-bar-movement");
  DEFSYM (Qswitch_frame, "switch-frame");
  DEFSYM (Qfocus_in, "focus-in");
  DEFSYM (Qfocus_out, "focus-out");
  DEFSYM (Qmove_frame, "move-frame");
  DEFSYM (Qdelete_frame, "delete-frame");
  DEFSYM (Qiconify_frame, "iconify-frame");
  DEFSYM (Qmake_frame_visible, "make-frame-visible");
  DEFSYM (Qno_event, "no-event");
  DEFSYM (Qselect_window, "select-window");
  DEFSYM (Qselection_request, "selection-request");
  DEFSYM (Qwindow_edges, "window-edges");
  {
    int i;

    for (i = 0; i < ARRAYELTS (head_table); i++)
      {
	const struct event_head *p = &head_table[i];
	Lisp_Object var = builtin_lisp_symbol (p->var);
	Lisp_Object kind = builtin_lisp_symbol (p->kind);
	Fput (var, Qevent_kind, kind);
	Fput (var, Qevent_symbol_elements, list1 (var));
      }
  }
  DEFSYM (Qno_record, "no-record");
  DEFSYM (Qencoded, "encoded");

  DEFSYM (Qpreedit_text, "preedit-text");

  button_down_location = make_nil_elisp_vector (5);
  staticpro (&button_down_location);
  staticpro (&frame_relative_event_pos);
  mouse_syms = make_nil_elisp_vector (5);
  staticpro (&mouse_syms);
  wheel_syms = make_nil_elisp_vector (ARRAYELTS (lispy_wheel_names));
  staticpro (&wheel_syms);

  /* modifier_symbols / modifier_names[] were removed at M1 — the
     modifier-name list now lives in mod/emacs/event-modifiers.scm.  */

  recent_keys = make_nil_elisp_vector (lossage_limit);
  staticpro (&recent_keys);

  this_command_keys = make_nil_elisp_vector (40);
  staticpro (&this_command_keys);

  raw_keybuf = make_nil_elisp_vector (30);
  staticpro (&raw_keybuf);

  DEFSYM (Qcommand_execute, "command-execute");
  DEFSYM (Qinternal_echo_keystrokes_prefix, "internal-echo-keystrokes-prefix");

  accent_key_syms = Qnil;
  staticpro (&accent_key_syms);

  func_key_syms = Qnil;
  staticpro (&func_key_syms);

  drag_n_drop_syms = Qnil;
  staticpro (&drag_n_drop_syms);

  pinch_syms = Qnil;
  staticpro (&pinch_syms);

  unread_switch_frame = Qnil;
  staticpro (&unread_switch_frame);

  internal_last_event_frame = Qnil;
  staticpro (&internal_last_event_frame);

  read_key_sequence_cmd = Qnil;
  staticpro (&read_key_sequence_cmd);
  read_key_sequence_remapped = Qnil;
  staticpro (&read_key_sequence_remapped);

  menu_bar_one_keymap_changed_items = Qnil;
  staticpro (&menu_bar_one_keymap_changed_items);

  menu_bar_items_vector = Qnil;
  staticpro (&menu_bar_items_vector);

  help_form_saved_window_configs = Qnil;
  staticpro (&help_form_saved_window_configs);

#ifdef POLL_FOR_INPUT
  poll_timer_time = Qnil;
  staticpro (&poll_timer_time);
#endif

  virtual_core_pointer_name = Qnil;
  staticpro (&virtual_core_pointer_name);

  virtual_core_keyboard_name = Qnil;
  staticpro (&virtual_core_keyboard_name);

  menu_bar_touch_id = Qnil;
  staticpro (&menu_bar_touch_id);

  DEFVAR_LISP ("last-command-event", last_command_event,
		     doc: /* Last input event of a key sequence that called a command.
See Info node `(elisp)Command Loop Info'.*/);

  DEFVAR_LISP ("last-nonmenu-event", last_nonmenu_event,
	       doc: /* Last input event in a command, except for mouse menu events.
Mouse menus give back keys that don't look like mouse events;
this variable holds the actual mouse event that led to the menu,
so that you can determine whether the command was run by mouse or not.  */);

  DEFVAR_LISP ("last-input-event", last_input_event,
	       doc: /* Last input event.  */);

  DEFVAR_LISP ("unread-command-events", Vunread_command_events,
	       doc: /* List of events to be read as the command input.
These events are processed first, before actual keyboard input.
Events read from this list are not normally added to `this-command-keys',
as they will already have been added once as they were read for the first time.
An element of the form (t . EVENT) forces EVENT to be added to that list.
An element of the form (no-record . EVENT) means process EVENT, but do not
record it in the keyboard macros, recent-keys, and the dribble file.  */);
  Vunread_command_events = Qnil;

  DEFVAR_LISP ("unread-post-input-method-events", Vunread_post_input_method_events,
	       doc: /* List of events to be processed as input by input methods.
These events are processed before `unread-command-events'
and actual keyboard input, but are not given to `input-method-function'.  */);
  Vunread_post_input_method_events = Qnil;

  DEFVAR_LISP ("unread-input-method-events", Vunread_input_method_events,
	       doc: /* List of events to be processed as input by input methods.
These events are processed after `unread-command-events', but
before actual keyboard input.
If there's an active input method, the events are given to
`input-method-function'.  */);
  Vunread_input_method_events = Qnil;

  DEFVAR_LISP ("meta-prefix-char", meta_prefix_char,
	       doc: /* Meta-prefix character code.
Meta-foo as command input turns into this character followed by foo.  */);
  XSETINT (meta_prefix_char, 033);

  DEFVAR_KBOARD ("last-command", Vlast_command,
		 doc: /* The last command executed.
Normally a symbol with a function definition, but can be whatever was found
in the keymap, or whatever the variable `this-command' was set to by that
command.

The value `mode-exit' is special; it means that the previous command
read an event that told it to exit, and it did so and unread that event.
In other words, the present command is the event that made the previous
command exit.

The value `kill-region' is special; it means that the previous command
was a kill command.

`last-command' has a separate binding for each terminal device.
See Info node `(elisp)Multiple Terminals'.  */);

  DEFVAR_KBOARD ("real-last-command", Vreal_last_command,
		 doc: /* Same as `last-command', but never altered by Lisp code.
Taken from the previous value of `real-this-command'.  */);

  DEFVAR_KBOARD ("last-repeatable-command", Vlast_repeatable_command,
		 doc: /* Last command that may be repeated.
The last command executed that was not bound to an input event.
This is the command `repeat' will try to repeat.
Taken from a previous value of `real-this-command'.  */);

  DEFVAR_LISP ("this-command", Vthis_command,
	       doc: /* The command now being executed.
The command can set this variable; whatever is put here
will be in `last-command' during the following command.  */);
  Vthis_command = Qnil;

  DEFVAR_LISP ("real-this-command", Vreal_this_command,
	       doc: /* This is like `this-command', except that commands should never modify it.  */);
  Vreal_this_command = Qnil;

  DEFSYM (Qcurrent_minibuffer_command, "current-minibuffer-command");
  DEFVAR_LISP ("current-minibuffer-command", Vcurrent_minibuffer_command,
	       doc: /* This is like `this-command', but bound recursively.
Code running from (for instance) a minibuffer hook can check this variable
to see what command invoked the current minibuffer.  */);
  Vcurrent_minibuffer_command = Qnil;

  DEFVAR_LISP ("this-command-keys-shift-translated",
	       Vthis_command_keys_shift_translated,
	       doc: /* Non-nil if the key sequence activating this command was shift-translated.
Shift-translation occurs when there is no binding for the key sequence
as entered, but a binding was found by changing an upper-case letter
to lower-case, or a shifted function key to an unshifted one.  */);
  Vthis_command_keys_shift_translated = Qnil;

  DEFVAR_LISP ("this-original-command", Vthis_original_command,
	       doc: /* The command bound to the current key sequence before remapping.
It equals `this-command' if the original command was not remapped through
any of the active keymaps.  Otherwise, the value of `this-command' is the
result of looking up the original command in the active keymaps.  */);
  Vthis_original_command = Qnil;

  DEFVAR_INT ("auto-save-interval", auto_save_interval,
	      doc: /* Number of input events between auto-saves.
Zero means disable autosaving due to number of characters typed.  */);
  auto_save_interval = 300;

  DEFVAR_BOOL ("auto-save-no-message", auto_save_no_message,
	       doc: /* Non-nil means do not print any message when auto-saving. */);
  auto_save_no_message = false;

  DEFVAR_LISP ("auto-save-timeout", Vauto_save_timeout,
	       doc: /* Number of seconds idle time before auto-save.
Zero or nil means disable auto-saving due to idleness.
After auto-saving due to this many seconds of idle time,
Emacs also does a garbage collection if that seems to be warranted.  */);
  XSETFASTINT (Vauto_save_timeout, 30);

  DEFVAR_LISP ("echo-keystrokes", Vecho_keystrokes,
    doc: /* Nonzero means echo unfinished commands after this many seconds of pause.
The value may be integer or floating point.
If the value is zero, don't echo at all.  */);
  Vecho_keystrokes = make_fixnum (1);

  DEFVAR_BOOL ("echo-keystrokes-help", echo_keystrokes_help,
    doc: /* Whether to append help text to echoed commands.
When non-nil, a reference to `C-h' is printed after echoed
keystrokes.  */);
  echo_keystrokes_help = true;

  DEFVAR_LISP ("polling-period", Vpolling_period,
	      doc: /* Interval between polling for input during Lisp execution.
The reason for polling is to make C-g work to stop a running program.
Polling is needed only when using X windows and SIGIO does not work.
Polling is automatically disabled in all other cases.  */);
  Vpolling_period = make_float (2.0);

  DEFVAR_LISP ("double-click-time", Vdouble_click_time,
	       doc: /* Maximum time between mouse clicks to make a double-click.
Measured in milliseconds.  The value nil means disable double-click
recognition; t means double-clicks have no time limit and are detected
by position only.

In Lisp, you might want to use `mouse-double-click-time' instead of
reading the value of this variable directly.  */);
  Vdouble_click_time = make_fixnum (500);

  DEFVAR_INT ("double-click-fuzz", double_click_fuzz,
	      doc: /* Maximum mouse movement between clicks to make a double-click.
On window-system frames, value is the number of pixels the mouse may have
moved horizontally or vertically between two clicks to make a double-click.
On non window-system frames, value is interpreted in units of 1/8 characters
instead of pixels.

This variable is also the threshold for motion of the mouse
to count as a drag.  */);
  double_click_fuzz = 3;

  DEFVAR_INT ("num-input-keys", num_input_keys,
	      doc: /* Number of complete key sequences read as input so far.
This includes key sequences read from keyboard macros.
The number is effectively the number of interactive command invocations.  */);
  num_input_keys = 0;

  DEFVAR_INT ("num-nonmacro-input-events", num_nonmacro_input_events,
	      doc: /* Number of input events read from the keyboard so far.
This does not include events generated by keyboard macros.  */);
  num_nonmacro_input_events = 0;

  DEFVAR_LISP ("last-event-frame", Vlast_event_frame,
	       doc: /* The frame in which the most recently read event occurred.
If the last event came from a keyboard macro, this is set to `macro'.  */);
  Vlast_event_frame = Qnil;

  DEFVAR_LISP ("last-event-device", Vlast_event_device,
	       doc: /* The name of the input device of the most recently read event.
When the input extension is being used on X, this is the name of the X
Input Extension device from which the last event was generated as a
string.  Otherwise, this is "Virtual core keyboard" for keyboard input
events, and "Virtual core pointer" for other events.

It is nil if the last event did not come from an input device (i.e. it
came from `unread-command-events' instead).  */);
  Vlast_event_device = Qnil;

  /* This variable is set up in sysdep.c.  */
  DEFVAR_LISP ("tty-erase-char", Vtty_erase_char,
	       doc: /* The ERASE character as set by the user with stty.  */);

  DEFVAR_LISP ("help-char", Vhelp_char,
	       doc: /* Character to recognize as meaning Help.
When it is read, do `(eval help-form)', and display result if it's a string.
If the value of `help-form' is nil, this char can be read normally.  */);
  XSETINT (Vhelp_char, Ctl ('H'));

  DEFVAR_LISP ("help-event-list", Vhelp_event_list,
	       doc: /* List of input events to recognize as meaning Help.
These work just like the value of `help-char' (see that).  */);
  Vhelp_event_list = Qnil;

  DEFVAR_LISP ("help-form", Vhelp_form,
	       doc: /* Form to execute when character `help-char' is read.
If the form returns a string, that string is displayed.
If `help-form' is nil, the help char is not recognized.  */);
  Vhelp_form = Qnil;

  DEFVAR_LISP ("prefix-help-command", Vprefix_help_command,
	       doc: /* Command to run when `help-char' character follows a prefix key.
This command is used only when there is no actual binding
for that character after that prefix key.  */);
  Vprefix_help_command = Qnil;

  DEFVAR_LISP ("top-level", Vtop_level,
	       doc: /* Form to evaluate when Emacs starts up.
Useful to set before you dump a modified Emacs.  */);
  Vtop_level = Qnil;

  DEFVAR_KBOARD ("keyboard-translate-table", Vkeyboard_translate_table,
                 doc: /* Translate table for local keyboard input, or nil.
If non-nil, the value should be a char-table.  Each character read
from the keyboard is looked up in this char-table.  If the value found
there is non-nil, then it is used instead of the actual input character.

The value can also be a string or vector, but this is considered obsolete.
If it is a string or vector of length N, character codes N and up are left
untranslated.  In a vector, an element which is nil means "no translation".

This is applied to the characters supplied to input methods, not their
output.  See also `translation-table-for-input'.

This variable has a separate binding for each terminal.
See Info node `(elisp)Multiple Terminals'.  */);

  DEFVAR_BOOL ("cannot-suspend", cannot_suspend,
	       doc: /* Non-nil means to always spawn a subshell instead of suspending.
\(Even if the operating system has support for stopping a process.)  */);
  cannot_suspend = false;

  DEFVAR_BOOL ("menu-prompting", menu_prompting,
	       doc: /* Non-nil means prompt with menus when appropriate.
This is done when reading from a keymap that has a prompt string,
for elements that have prompt strings.
The menu is displayed on the screen
if X menus were enabled at configuration
time and the previous event was a mouse click prefix key.
Otherwise, menu prompting uses the echo area.  */);
  menu_prompting = true;

  DEFVAR_LISP ("menu-prompt-more-char", menu_prompt_more_char,
	       doc: /* Character to see next line of menu prompt.
Type this character while in a menu prompt to rotate around the lines of it.  */);
  XSETINT (menu_prompt_more_char, ' ');

  DEFVAR_INT ("extra-keyboard-modifiers", extra_keyboard_modifiers,
	      doc: /* A mask of additional modifier keys to use with every keyboard character.
Emacs applies the modifiers of the character stored here to each keyboard
character it reads.  For example, after evaluating the expression
    (setq extra-keyboard-modifiers ?\\C-x)
all input characters will have the control modifier applied to them.

Note that the character ?\\C-@, equivalent to the integer zero, does
not count as a control character; rather, it counts as a character
with no modifiers; thus, setting `extra-keyboard-modifiers' to zero
cancels any modification.  */);
  extra_keyboard_modifiers = 0;

  DEFSYM (Qdeactivate_mark, "deactivate-mark");
  DEFVAR_LISP ("deactivate-mark", Vdeactivate_mark,
    doc: /* Whether to deactivate the mark after an editing command.
The command loop sets this to nil before each command,
and tests the value when the command returns.
If an editing command sets this non-nil, deactivate the mark after
the command returns.

Buffer modifications store t in this variable.

By default, deactivating the mark will save the contents of the region
according to `select-active-regions', unless this is set to the symbol
`dont-save'.  */);
  Vdeactivate_mark = Qnil;
  Fmake_variable_buffer_local (Qdeactivate_mark);

  DEFVAR_LISP ("pre-command-hook", Vpre_command_hook,
	       doc: /* Normal hook run before each command is executed.

If an unhandled error happens in running this hook, the function in
which the error occurred is unconditionally removed, since otherwise
the error might happen repeatedly and make Emacs nonfunctional.

Note that, when `long-line-optimizations-p' is non-nil in the buffer,
these functions are called as if they were in a `with-restriction' form,
with a `long-line-optimizations-in-command-hooks' label and with the
buffer narrowed to a portion around point whose size is specified by
`long-line-optimizations-region-size'.

See also `post-command-hook'.  */);
  Vpre_command_hook = Qnil;

  DEFVAR_LISP ("post-command-hook", Vpost_command_hook,
	       doc: /* Normal hook run after each command is executed.

If an unhandled error happens in running this hook, the function in
which the error occurred is unconditionally removed, since otherwise
the error might happen repeatedly and make Emacs nonfunctional.

It is a bad idea to use this hook for expensive processing.  If
unavoidable, wrap your code in `(while-no-input (redisplay) CODE)' to
avoid making Emacs unresponsive while the user types.

Note that, when `long-line-optimizations-p' is non-nil in the buffer,
these functions are called as if they were in a `with-restriction' form,
with a `long-line-optimizations-in-command-hooks' label and with the
buffer narrowed to a portion around point whose size is specified by
`long-line-optimizations-region-size'.

See also `pre-command-hook'.  */);
  Vpost_command_hook = Qnil;

#if 0
  DEFVAR_LISP ("echo-area-clear-hook", ...,
	       doc: /* Normal hook run when clearing the echo area.  */);
#endif
  DEFSYM (Qecho_area_clear_hook, "echo-area-clear-hook");
  DEFSYM (Qtouchscreen_begin, "touchscreen-begin");
  DEFSYM (Qtouchscreen_end, "touchscreen-end");
  DEFSYM (Qtouchscreen_update, "touchscreen-update");
  DEFSYM (Qpinch, "pinch");
  DEFSYM (Qdisplay_monitors_changed_functions,
	  "display-monitors-changed-functions");

  DEFSYM (Qcoding, "coding");
  DEFSYM (Qtouchscreen, "touchscreen");
#ifdef HAVE_TEXT_CONVERSION
  DEFSYM (Qtext_conversion, "text-conversion");
#endif

  Fset (Qecho_area_clear_hook, Qnil);

#ifdef USE_LUCID
  DEFVAR_BOOL ("lucid--menu-grab-keyboard",
               lucid__menu_grab_keyboard,
               doc: /* If non-nil, grab keyboard during menu operations.
This is only relevant when using the Lucid X toolkit.  It can be
convenient to disable this for debugging purposes.  */);
  lucid__menu_grab_keyboard = true;
#endif

  DEFVAR_LISP ("menu-bar-final-items", Vmenu_bar_final_items,
	       doc: /* List of menu bar items to move to the end of the menu bar.
The elements of the list are event types that may have menu bar
bindings.  The order of this list controls the order of the items.  */);
  Vmenu_bar_final_items = Qnil;

  DEFVAR_LISP ("tab-bar-separator-image-expression", Vtab_bar_separator_image_expression,
    doc: /* Expression evaluating to the image spec for a tab-bar separator.
This is used internally by graphical displays that do not render
tab-bar separators natively.  Otherwise it is unused (e.g. on GTK).  */);
  Vtab_bar_separator_image_expression = Qnil;

  DEFVAR_LISP ("tool-bar-separator-image-expression", Vtool_bar_separator_image_expression,
    doc: /* Expression evaluating to the image spec for a tool-bar separator.
This is used internally by graphical displays that do not render
tool-bar separators natively.  Otherwise it is unused (e.g. on GTK).  */);
  Vtool_bar_separator_image_expression = Qnil;

  DEFVAR_KBOARD ("overriding-terminal-local-map",
		 Voverriding_terminal_local_map,
		 doc: /* Per-terminal keymap that takes precedence over all other keymaps.
This variable is intended to let commands such as `universal-argument'
set up a different keymap for reading the next command.

`overriding-terminal-local-map' has a separate binding for each
terminal device.  See Info node `(elisp)Multiple Terminals'.  */);

  DEFVAR_LISP ("overriding-local-map", Voverriding_local_map,
	       doc: /* Keymap that replaces (overrides) local keymaps.
If this variable is non-nil, Emacs looks up key bindings in this
keymap INSTEAD OF `keymap' text properties, `local-map' and `keymap'
overlay properties, minor mode maps, and the buffer's local map.

Hence, the only active keymaps would be `overriding-terminal-local-map',
this keymap, and `global-keymap', in order of precedence.  */);
  Voverriding_local_map = Qnil;

  DEFVAR_LISP ("overriding-local-map-menu-flag", Voverriding_local_map_menu_flag,
	       doc: /* Non-nil means `overriding-local-map' applies to the menu bar.
Otherwise, the menu bar continues to reflect the buffer's local map
and the minor mode maps regardless of `overriding-local-map'.  */);
  Voverriding_local_map_menu_flag = Qnil;

  DEFVAR_LISP ("special-event-map", Vspecial_event_map,
	       doc: /* Keymap defining bindings for special events to execute at low level.  */);
  Vspecial_event_map = list1 (Qkeymap);

  DEFVAR_LISP ("track-mouse", track_mouse,
	       doc: /* Non-nil means generate motion events for mouse motion.
The special values `dragging' and `dropping' assert that the mouse
cursor retains its appearance during mouse motion.  Any non-nil value
but `dropping' or `drag-source' asserts that motion events always
relate to the frame where the mouse movement started.  The value
`dropping' asserts that motion events relate to the frame where the
mouse cursor is seen when generating the event.  If there's no such
frame, such motion events relate to the frame where the mouse movement
started.  The value `drag-source' is like `dropping', but the
`posn-window' will be nil in mouse position lists inside mouse
movement events if there is no frame directly visible underneath the
mouse pointer.  */);
  DEFVAR_KBOARD ("system-key-alist", Vsystem_key_alist,
		 doc: /* Alist of system-specific X windows key symbols.
Each element should have the form (N . SYMBOL) where N is the
numeric keysym code (sans the \"system-specific\" bit 1<<28)
and SYMBOL is its name.

`system-key-alist' has a separate binding for each terminal device.
See Info node `(elisp)Multiple Terminals'.  */);

  DEFVAR_KBOARD ("local-function-key-map", Vlocal_function_key_map,
                 doc: /* Keymap that translates key sequences to key sequences during input.
This is used mainly for mapping key sequences into some preferred
key events (symbols).

The `read-key-sequence' function replaces any subsequence bound by
`local-function-key-map' with its binding.  More precisely, when the
active keymaps have no binding for the current key sequence but
`local-function-key-map' binds a suffix of the sequence to a vector or
string, `read-key-sequence' replaces the matching suffix with its
binding, and continues with the new sequence.

If the binding is a function, it is called with one argument (the prompt)
and its return value (a key sequence) is used.

The events that come from bindings in `local-function-key-map' are not
themselves looked up in `local-function-key-map'.

For example, suppose `local-function-key-map' binds `ESC O P' to [f1].
Typing `ESC O P' to `read-key-sequence' would return [f1].  Typing
`C-x ESC O P' would return [?\\C-x f1].  If [f1] were a prefix key,
typing `ESC O P x' would return [f1 x].

`local-function-key-map' has a separate binding for each terminal
device.  See Info node `(elisp)Multiple Terminals'.  If you need to
define a binding on all terminals, change `function-key-map'
instead.  Initially, `local-function-key-map' is an empty keymap that
has `function-key-map' as its parent on all terminal devices.  */);

  DEFVAR_KBOARD ("input-decode-map", Vinput_decode_map,
		 doc: /* Keymap that decodes input escape sequences.
This is used mainly for mapping ASCII function key sequences into
real Emacs function key events (symbols).

The `read-key-sequence' function replaces any subsequence bound by
`input-decode-map' with its binding.  Contrary to `function-key-map',
this map applies its rebinding regardless of the presence of an ordinary
binding.  So it is more like `key-translation-map' except that it applies
before `function-key-map' rather than after.

If the binding is a function, it is called with one argument (the prompt)
and its return value (a key sequence) is used.

The events that come from bindings in `input-decode-map' are not
themselves looked up in `input-decode-map'.  */);

  DEFVAR_LISP ("function-key-map", Vfunction_key_map,
               doc: /* The parent keymap of all `local-function-key-map' instances.
Function key definitions that apply to all terminal devices should go
here.  If a mapping is defined in both the current
`local-function-key-map' binding and this variable, then the local
definition will take precedence.  */);
  Vfunction_key_map = Fmake_sparse_keymap (Qnil);

  DEFVAR_LISP ("key-translation-map", Vkey_translation_map,
               doc: /* Keymap of key translations that can override keymaps.
This keymap works like `input-decode-map', but comes after `function-key-map'.
Another difference is that it is global rather than terminal-local.  */);
  Vkey_translation_map = Fmake_sparse_keymap (Qnil);

  DEFVAR_LISP ("delayed-warnings-list", Vdelayed_warnings_list,
               doc: /* List of warnings to be displayed after this command.
Each element must be a list (TYPE MESSAGE [LEVEL [BUFFER-NAME]]),
as per the args of `display-warning' (which see).
If this variable is non-nil, `delayed-warnings-hook' will be run
immediately after running `post-command-hook'.  */);
  Vdelayed_warnings_list = Qnil;

  DEFVAR_LISP ("timer-list", Vtimer_list,
	       doc: /* List of active absolute time timers in order of increasing time.  */);
  Vtimer_list = Qnil;

  DEFVAR_LISP ("timer-idle-list", Vtimer_idle_list,
	       doc: /* List of active idle-time timers in order of increasing time.  */);
  Vtimer_idle_list = Qnil;

  DEFVAR_LISP ("input-method-function", Vinput_method_function,
	       doc: /* If non-nil, the function that implements the current input method.
It's called with one argument, which must be a single-byte
character that was just read.  Any single-byte character is
acceptable, except the DEL character, codepoint 127 decimal, 177 octal.
Typically this function uses `read-event' to read additional events.
When it does so, it should first bind `input-method-function' to nil
so it will not be called recursively.

The function should return a list of zero or more events
to be used as input.  If it wants to put back some events
to be reconsidered, separately, by the input method,
it can add them to the beginning of `unread-command-events'.

The input method function can find in `input-method-previous-message'
the previous echo area message.

The input method function should refer to the variables
`input-method-use-echo-area' and `input-method-exit-on-first-char'
for guidance on what to do.  */);
  Vinput_method_function = Qlist;

  DEFVAR_LISP ("input-method-previous-message",
	       Vinput_method_previous_message,
	       doc: /* When `input-method-function' is called, hold the previous echo area message.
This variable exists because `read-event' clears the echo area
before running the input method.  It is nil if there was no message.  */);
  Vinput_method_previous_message = Qnil;

  DEFVAR_LISP ("show-help-function", Vshow_help_function,
	       doc: /* If non-nil, the function that implements the display of help.
It's called with one argument, the help string to display.  */);
  Vshow_help_function = Qnil;

  DEFVAR_LISP ("disable-point-adjustment", Vdisable_point_adjustment,
	       doc: /* If non-nil, suppress point adjustment after executing a command.

After a command is executed, if point moved into a region that has
special properties (e.g. composition, display), Emacs adjusts point to
the boundary of the region.  But when a command leaves this variable at
a non-nil value (e.g., with a setq), this point adjustment is suppressed.

This variable is set to nil before reading a command, and is checked
just after executing the command.  */);
  Vdisable_point_adjustment = Qnil;

  DEFVAR_LISP ("global-disable-point-adjustment",
	       Vglobal_disable_point_adjustment,
	       doc: /* If non-nil, always suppress point adjustments.

The default value is nil, in which case point adjustments are
suppressed only after special commands that leave
`disable-point-adjustment' (which see) at a non-nil value.  */);
  Vglobal_disable_point_adjustment = Qnil;

  DEFVAR_LISP ("minibuffer-message-timeout", Vminibuffer_message_timeout,
	       doc: /* How long to display an echo-area message when the minibuffer is active.
If the value is a number, it should be specified in seconds.
If the value is not a number, such messages never time out.  */);
  Vminibuffer_message_timeout = make_fixnum (2);

  DEFVAR_LISP ("throw-on-input", Vthrow_on_input,
	       doc: /* If non-nil, any keyboard input throws to this symbol.
The value of that variable is passed to `quit-flag' and later causes a
peculiar kind of quitting.  */);
  Vthrow_on_input = Qnil;

  DEFVAR_LISP ("command-error-function", Vcommand_error_function,
	       doc: /* Function to output error messages.
Called with three arguments:
- the error data, a list of the form (SIGNALED-CONDITION . SIGNAL-DATA)
  such as what `condition-case' would bind its variable to,
- the context (a string which normally goes at the start of the message),
- the Lisp function within which the error was signaled.

For instance, to make error messages stand out more in the echo area,
you could say something like:

    (setq command-error-function
          (lambda (data _ _)
            (message "%s" (propertize (error-message-string data)
                                      \\='face \\='error))))

Also see `set-message-function' (which controls how non-error messages
are displayed).  */);
  Vcommand_error_function = Qcommand_error_default_function;

  DEFVAR_LISP ("enable-disabled-menus-and-buttons",
	       Venable_disabled_menus_and_buttons,
	       doc: /* If non-nil, don't ignore events produced by disabled menu items and tool-bar.

Help functions bind this to allow help on disabled menu items
and tool-bar buttons.  */);
  Venable_disabled_menus_and_buttons = Qnil;

  DEFVAR_LISP ("select-active-regions",
	       Vselect_active_regions,
	       doc: /* If non-nil, any active region automatically sets the primary selection.
This variable only has an effect when Transient Mark mode is enabled.

If the value is `only', only temporarily active regions (usually made
by mouse-dragging or shift-selection) set the window system's primary
selection.

If this variable causes the region to be set as the primary selection,
`post-select-region-hook' is then run afterwards.  */);
  Vselect_active_regions = Qt;

  DEFVAR_LISP ("saved-region-selection",
	       Vsaved_region_selection,
	       doc: /* Contents of active region prior to buffer modification.
If `select-active-regions' is non-nil, Emacs sets this to the
text in the region before modifying the buffer.  The next call to
the function `deactivate-mark' uses this to set the window selection.  */);
  Vsaved_region_selection = Qnil;

  DEFVAR_LISP ("selection-inhibit-update-commands",
	       Vselection_inhibit_update_commands,
	       doc: /* List of commands which should not update the selection.
Normally, if `select-active-regions' is non-nil and the mark remains
active after a command (i.e. the mark was not deactivated), the Emacs
command loop sets the selection to the text in the region.  However,
if the command is in this list, the selection is not updated.  */);
  Vselection_inhibit_update_commands
    = list2 (Qhandle_switch_frame, Qhandle_select_window);

  DEFVAR_LISP ("debug-on-event",
               Vdebug_on_event,
               doc: /* Enter debugger on this event.
When Emacs receives the special event specified by this variable,
it will try to break into the debugger as soon as possible instead
of processing the event normally through `special-event-map'.

Currently, the only supported values for this
variable are `sigusr1' and `sigusr2'.  */);
  Vdebug_on_event = Qsigusr2;

  DEFVAR_BOOL ("attempt-stack-overflow-recovery",
               attempt_stack_overflow_recovery,
               doc: /* If non-nil, attempt to recover from C stack overflows.
This recovery is potentially unsafe and may lead to deadlocks or data
corruption, but it usually works and may preserve modified buffers
that would otherwise be lost.  If nil, treat stack overflow like any
other kind of crash or fatal error.  */);
  attempt_stack_overflow_recovery = true;

  DEFVAR_BOOL ("attempt-orderly-shutdown-on-fatal-signal",
               attempt_orderly_shutdown_on_fatal_signal,
               doc: /* If non-nil, attempt orderly shutdown on fatal signals.
By default this variable is non-nil, and Emacs attempts to perform
an orderly shutdown when it catches a fatal signal (e.g., a crash).
The orderly shutdown includes an attempt to auto-save your unsaved edits
and other useful cleanups.  These cleanups are potentially unsafe and may
lead to deadlocks or data corruption, but it usually works and may
preserve data in modified buffers that would otherwise be lost.
If nil, Emacs crashes immediately in response to fatal signals.  */);
  attempt_orderly_shutdown_on_fatal_signal = true;

  DEFVAR_LISP ("while-no-input-ignore-events",
               Vwhile_no_input_ignore_events,
               doc: /* Ignored events from `while-no-input'.
Events in this list do not count as pending input while running
`while-no-input' and do not cause any idle timers to get reset when they
occur.  */);
  Vwhile_no_input_ignore_events = init_while_no_input_ignore_events ();

  DEFVAR_BOOL ("translate-upper-case-key-bindings",
               translate_upper_case_key_bindings,
               doc: /* If non-nil, interpret upper case keys as lower case (when applicable).
Emacs allows binding both upper and lower case key sequences to
commands.  However, if there is a lower case key sequence bound to a
command, and the user enters an upper case key sequence that is not
bound to a command, Emacs will use the lower case binding.  Setting
this variable to nil inhibits this behavior.  */);
  translate_upper_case_key_bindings = true;

  DEFVAR_BOOL ("input-pending-p-filter-events",
               input_pending_p_filter_events,
               doc: /* If non-nil, `input-pending-p' ignores some input events.
If this variable is non-nil (the default), `input-pending-p' and
other similar functions ignore input events in `while-no-input-ignore-events'.
This flag may eventually be removed once this behavior is deemed safe.  */);
  input_pending_p_filter_events = true;

  DEFVAR_BOOL ("mwheel-coalesce-scroll-events", mwheel_coalesce_scroll_events,
	       doc: /* Non-nil means send a wheel event only for scrolling at least one screen line.
Otherwise, a wheel event will be sent every time the mouse wheel is
moved.  */);
  mwheel_coalesce_scroll_events = true;

  DEFVAR_LISP ("display-monitors-changed-functions", Vdisplay_monitors_changed_functions,
    doc: /* Abnormal hook run when the monitor configuration changes.
This can happen if a monitor is rotated, moved, plugged in or removed
from a multi-monitor setup, if the primary monitor changes, or if the
resolution of a monitor changes.  The hook should accept a single
argument, which is the terminal on which the monitor configuration
changed.  */);
  Vdisplay_monitors_changed_functions = Qnil;

  DEFVAR_BOOL ("inhibit--record-char",
	       inhibit_record_char,
	       doc: /* If non-nil, don't record input events.
This inhibits recording input events for the purposes of keyboard
macros, dribble file, and `recent-keys'.
Internal use only.  */);
  inhibit_record_char = false;

  DEFVAR_BOOL ("record-all-keys", record_all_keys,
	       doc: /* Non-nil means record all keys you type.
When nil, the default, characters typed as part of passwords are
not recorded.  The non-nil value countermands `inhibit--record-char',
which see.  */);
  record_all_keys = false;

  DEFVAR_LISP ("post-select-region-hook", Vpost_select_region_hook,
    doc: /* Abnormal hook run after the region is selected.
This usually happens as a result of `select-active-regions'.  The hook
is called with one argument, the string that was selected.  */);
  Vpost_select_region_hook = Qnil;

  DEFVAR_BOOL ("disable-inhibit-text-conversion",
	       disable_inhibit_text_conversion,
    doc: /* Don't disable text conversion inside `read-key-sequence'.
If non-nil, text conversion will continue to happen after a prefix
key has been read inside `read-key-sequence'.  */);
  disable_inhibit_text_conversion = false;

  DEFVAR_LISP ("current-key-remap-sequence",
	       Vcurrent_key_remap_sequence,
    doc: /* The key sequence currently being remap, or nil.
Bound to a vector containing the sub-sequence matching a binding
within `input-decode-map' or `local-function-key-map' when its bound
function is called to remap that sequence.  */);
  Vcurrent_key_remap_sequence = Qnil;
  DEFSYM (Qcurrent_key_remap_sequence, "current-key-remap-sequence");

  /* Create the initial keyboard.  Qt means 'unset'.  */
  eassert (initial_kboard == NULL);
  initial_kboard = allocate_kboard (Qt);

  DEFSYM (Qactivate_mark_hook, "activate-mark-hook");
  DEFSYM (Qns_unput_working_text, "ns-unput-working-text");
  DEFSYM (Qinternal_timer_start_idle, "internal-timer-start-idle");
  DEFSYM (Qconcat, "concat");
  DEFSYM (Qsuspend_hook, "suspend-hook");
  DEFSYM (Qsuspend_resume_hook, "suspend-resume-hook");
  DEFSYM (Qcommand_error_default_function, "command-error-default-function");
  DEFSYM (Qsigusr2, "sigusr2");
}

void
keys_of_keyboard (void)
{
  initial_define_lispy_key (Vspecial_event_map, "delete-frame",
			    "handle-delete-frame");
#ifdef HAVE_NTGUI
  initial_define_lispy_key (Vspecial_event_map, "end-session",
			    "kill-emacs");
#endif
  initial_define_lispy_key (Vspecial_event_map, "ns-put-working-text",
			    "ns-put-working-text");
  initial_define_lispy_key (Vspecial_event_map, "ns-unput-working-text",
			    "ns-unput-working-text");
  /* Here we used to use `ignore-event' which would simple set prefix-arg to
     current-prefix-arg, as is done in `handle-switch-frame'.
     But `handle-switch-frame is not run from the special-map.
     Commands from that map are run in a special way that automatically
     preserves the prefix-arg.  Restoring the prefix arg here is not just
     redundant but harmful:
     - C-u C-x v =
     - current-prefix-arg is set to non-nil, prefix-arg is set to nil.
     - after the first prompt, the exit-minibuffer-hook is run which may
       iconify a frame and thus push a `iconify-frame' event.
     - after running exit-minibuffer-hook, current-prefix-arg is
       restored to the non-nil value it had before the prompt.
     - we enter the second prompt.
       current-prefix-arg is non-nil, prefix-arg is nil.
     - before running the first real event, we run the special iconify-frame
       event, but we pass the `special' arg to command-execute so
       current-prefix-arg and prefix-arg are left untouched.
     - here we foolishly copy the non-nil current-prefix-arg to prefix-arg.
     - the next key event will have a spuriously non-nil current-prefix-arg.  */
  initial_define_lispy_key (Vspecial_event_map, "iconify-frame",
			    "ignore");
  initial_define_lispy_key (Vspecial_event_map, "make-frame-visible",
			    "ignore");
  /* Handling it at such a low-level causes read_key_sequence to get
   * confused because it doesn't realize that the current_buffer was
   * changed by read_char.
   *
   * initial_define_lispy_key (Vspecial_event_map, "select-window",
   * 			    "handle-select-window"); */
  initial_define_lispy_key (Vspecial_event_map, "save-session",
			    "handle-save-session");

#ifdef HAVE_DBUS
  /* Define a special event which is raised for dbus callback
     functions.  */
  initial_define_lispy_key (Vspecial_event_map, "dbus-event",
			    "dbus-handle-event");
#endif

#ifdef THREADS_ENABLED
  /* Define a special event which is raised for thread signals.  */
  initial_define_lispy_key (Vspecial_event_map, "thread-event",
			    "thread-handle-event");
#endif

#ifdef USE_FILE_NOTIFY
  /* Define a special event which is raised for notification callback
     functions.  */
  initial_define_lispy_key (Vspecial_event_map, "file-notify",
                            "file-notify-handle-event");
#endif /* USE_FILE_NOTIFY */

  initial_define_lispy_key (Vspecial_event_map, "config-changed-event",
			    "ignore");
#if defined (WINDOWSNT)
  initial_define_lispy_key (Vspecial_event_map, "language-change",
			    "ignore");
#endif
  initial_define_lispy_key (Vspecial_event_map, "focus-in",
			    "handle-focus-in");
  initial_define_lispy_key (Vspecial_event_map, "focus-out",
			    "handle-focus-out");
  initial_define_lispy_key (Vspecial_event_map, "move-frame",
			    "handle-move-frame");
}
