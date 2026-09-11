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

#include "guile.h"
#include <errno.h>

#ifdef HAVE_PTHREAD
#include <pthread.h>
#endif
#include <sys/ioctl.h>

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

char const DEV_TTY[] = "/dev/tty";
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

/* FIX-20260814-guilemacs: the Scheme imp-3 dispatch port
   (mod/emacs/kbd-buffer.scm dispatch-event!) mutates event->ie.arg in
   place (elisp setcar) during pinch coalescing while the event is in
   the queue.  Safe: kbd_buffer is a C global, so the conservative GC
   (Fgarbage_collect → GC_gcollect, alloc.c) treats the whole array as
   a root and the Lisp_Objects inside it stay reachable — the same
   guarantee mark_kboards used to provide before the emacs mark-and-
   sweep GC was retired.  */
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

static void echo_now (void);
static ptrdiff_t echo_length (void);

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
static Lisp_Object make_lispy_event (struct input_event *);
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
  /* M18 imp-3 — C body replaced by a SCM_CALL_* into (emacs echo). */
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs echo", "echo-keystrokes-p");
  return scm_is_true (SCM_CALL_0 (proc));
}

/* Add C to the echo string, without echoing it immediately.  C can be
   a character, which is pretty-printed, or a symbol, whose name is
   printed.  */

static void
echo_add_key (Lisp_Object c)
{
  /* M18 imp-3 — C body replaced by a SCM_CALL_* into (emacs echo). */
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs echo", "echo-add-key");
  SCM_CALL_1 (proc, c);
}

/* Temporarily add a dash to the end of the echo string if it's not
   empty, so that it serves as a mini-prompt for the very next
   character.  */

static void
echo_dash (void)
{
  /* M18 imp-3 — C body replaced by a SCM_CALL_* into (emacs echo). */
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs echo", "echo-dash");
  SCM_CALL_0 (proc);
}

static void
echo_update (void)
{
  /* M18 imp-3 — C body replaced by a SCM_CALL_* into (emacs echo). */
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs echo", "echo-update");
  SCM_CALL_0 (proc);
}

/* Display the current echo string, and begin echoing if not already
   doing so.  */

static void
echo_now (void)
{
  /* M18 imp-3 — C body replaced by a SCM_CALL_* into (emacs echo). */
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs echo", "echo-now");
  SCM_CALL_0 (proc);
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
  /* M18 imp-3 — C body replaced by a SCM_CALL_* into (emacs echo). */
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs echo", "echo-length");
  return XFIXNUM (SCM_CALL_0 (proc));
}

/* Truncate the current echo message to its first LEN chars.
   This and echo_char get used by read_key_sequence when the user
   switches frames while entering a key sequence.  */

static void
echo_truncate (ptrdiff_t nchars)
{
  /* M18 imp-3 — C body replaced by a SCM_CALL_* into (emacs echo). */
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs echo", "echo-truncate");
  SCM_CALL_1 (proc, INT_TO_INTEGER (nchars));
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
/* M22 imp-2: thin dispatcher.  The recursive_edit_1 body (prologue +
   command-loop-main + throw-value tail) lives in Scheme as
   (emacs recursive-edit)/recursive-edit-1.  Called directly by
   read_minibuf (minibuf.c), which runs the edit loop without the
   Frecursive_edit command_loop_level increment / kboard switch.  */
Lisp_Object
recursive_edit_1 (void)
{
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs recursive-edit", "recursive-edit-1");
  SCM_CALL_0 (proc);
  return Qnil;
}


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
  /* M22 imp-2: thin dispatcher.  The whole body lives in Scheme as
     (emacs recursive-edit)/recursive-edit.  The dynwind bracket is kept
     (unlike Ftop_level, which never registers an unwind action) so that
     temporarily_switch_to_single_kboard's internal record_unwind_protect_int
     still fires at dynwind_end below — after the whole Scheme call and its
     dynamic-wind after-thunk have returned.  */
  dynwind_begin ();
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs recursive-edit", "recursive-edit");
  SCM_CALL_0 (proc);
  dynwind_end ();
  return Qnil;
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

DEFUN ("--set-ie-arg", Fset_ie_arg, Sset_ie_arg, 2, 2, 0,
       doc: /* Set the arg field of input-event handle IE to VAL.

Plain write; the caller is responsible for the value's lifetime (the
multibyte-decode path wraps the decoded string in a fresh cons).  Used
by the imp-3 dispatch port to install `(0 . DECODED)' into the queue
entry.  Returns VAL.  */)
  (Lisp_Object ie, Lisp_Object val)
{
  CHECK_IE (ie);
  XIE (ie)->arg = val;
  return val;
}

DEFUN ("--set-ie-code", Fset_ie_code, Sset_ie_code, 2, 2, 0,
       doc: /* Set the code field of input-event handle IE to VAL.

Used by the multibyte-incremental path of the imp-3 dispatch port to
install the next character code.  Unsigned int ← fixnum.  Returns
VAL.  */)
  (Lisp_Object ie, Lisp_Object val)
{
  CHECK_IE (ie);
  CHECK_FIXNAT (val);
  XIE (ie)->code = XFIXNUM (val);
  return val;
}

DEFUN ("--set-ie-frame-or-window", Fset_ie_frame_or_window,
       Sset_ie_frame_or_window, 2, 2, 0,
       doc: /* Set the frame_or_window field of input-event handle IE to VAL.

Plain write; used by the imp-3 dispatch unit tests to fabricate a
switch-frame source or a non-live pinch frame, since the test-only
--kbd-buffer-store-fake-event always stores the selected frame.  Returns
VAL.  */)
  (Lisp_Object ie, Lisp_Object val)
{
  CHECK_IE (ie);
  XIE (ie)->frame_or_window = val;
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

DEFUN ("--ie-copy", Fie_copy, Sie_copy, 2, 2, 0,
       doc: /* Copy input-event handle SRC onto DST, field by field.

Full struct assignment: copies every struct input_event field,
including x, y, part, timestamp, and device — none of which have
individual Scheme setters today.  Returns DST.  */)
  (Lisp_Object dst, Lisp_Object src)
{
  CHECK_IE (dst);
  CHECK_IE (src);
  *ie_unwrap (dst) = *ie_unwrap (src);
  return dst;
}

DEFUN ("--ie-kind-alist", Fie_kind_alist, Sie_kind_alist, 0, 0, 0,
       doc: /* Return an alist mapping each event symbol to its event_kind integer.

Each entry is (SYMBOL . INTEGER), in reverse declaration order.  The
integer is the value of the C enum `event_kind' member for this exact
build.
Because the enum has #ifdef-guarded members, these numbers depend on
the build configuration; they are not portable across builds.

Scheme must treat this as opaque build data: it consumes the list for
lookup but must never hard-code any returned integer.  Used by
(emacs lispy-position) to build its ie-kind-from-name dispatch
table.  */)
  (void)
{
  Lisp_Object result = Qnil;
#ifdef HAVE_DBUS
  result = Fcons (Fcons (Qdbus_event, make_fixnum (DBUS_EVENT)), result);
#endif
#ifdef THREADS_ENABLED
  result = Fcons (Fcons (Qthread_event, make_fixnum (THREAD_EVENT)), result);
#endif
#ifdef HAVE_XWIDGETS
  result = Fcons (Fcons (Qxwidget_event, make_fixnum (XWIDGET_EVENT)), result);
  result = Fcons (Fcons (Qxwidget_display_event, make_fixnum (XWIDGET_DISPLAY_EVENT)), result);
#endif
#ifdef USE_FILE_NOTIFY
  result = Fcons (Fcons (Qfile_notify, make_fixnum (FILE_NOTIFY_EVENT)), result);
#endif

  /* Trivial-frame group  */
  result = Fcons (Fcons (Qno_event, make_fixnum (NO_EVENT)), result);
#ifdef HAVE_WINDOW_SYSTEM
  result = Fcons (Fcons (Qdelete_frame, make_fixnum (DELETE_WINDOW_EVENT)), result);
  result = Fcons (Fcons (Qiconify_frame, make_fixnum (ICONIFY_EVENT)), result);
  result = Fcons (Fcons (Qmake_frame_visible, make_fixnum (DEICONIFY_EVENT)), result);
  result = Fcons (Fcons (Qmove_frame, make_fixnum (MOVE_FRAME_EVENT)), result);
#endif

  /* Simple-list group (imp-3.3).  */
  result = Fcons (Fcons (Qselect_window, make_fixnum (SELECT_WINDOW_EVENT)), result);
  result = Fcons (Fcons (Qsave_session, make_fixnum (SAVE_SESSION_EVENT)), result);
  result = Fcons (Fcons (Qconfig_changed_event, make_fixnum (CONFIG_CHANGED_EVENT)), result);
  result = Fcons (Fcons (Qpreedit_text, make_fixnum (PREEDIT_TEXT_EVENT)), result);
  result = Fcons (Fcons (Quser_signal_event, make_fixnum (USER_SIGNAL_EVENT)), result);

  /* Simple-helper group (imp-4).  */
  result = Fcons (Fcons (Qhelp_echo, make_fixnum (HELP_EVENT)), result);
  result = Fcons (Fcons (Qfocus_in, make_fixnum (FOCUS_IN_EVENT)), result);
  result = Fcons (Fcons (Qfocus_out, make_fixnum (FOCUS_OUT_EVENT)), result);
  result = Fcons (Fcons (Qtab_bar, make_fixnum (TAB_BAR_EVENT)), result);
  result = Fcons (Fcons (Qtool_bar, make_fixnum (TOOL_BAR_EVENT)), result);
  result = Fcons (Fcons (Qdrag_n_drop, make_fixnum (DRAG_N_DROP_EVENT)), result);
#ifdef HAVE_EXT_MENU_BAR
  result = Fcons (Fcons (Qmenu_bar, make_fixnum (MENU_BAR_EVENT)), result);
#endif
#ifdef USE_TOOLKIT_SCROLL_BARS
  result = Fcons (Fcons (Qscroll_bar_click_toolkit, make_fixnum (SCROLL_BAR_CLICK_EVENT)), result);
  result = Fcons (Fcons (Qhorizontal_scroll_bar_click_toolkit, make_fixnum (HORIZONTAL_SCROLL_BAR_CLICK_EVENT)), result);
#endif

  /* Keystroke group (imp-5).  */
  result = Fcons (Fcons (Qascii_keystroke, make_fixnum (ASCII_KEYSTROKE_EVENT)), result);
  result = Fcons (Fcons (Qmultibyte_char_keystroke, make_fixnum (MULTIBYTE_CHAR_KEYSTROKE_EVENT)), result);
  result = Fcons (Fcons (Qnon_ascii_keystroke, make_fixnum (NON_ASCII_KEYSTROKE_EVENT)), result);

  /* imp-7.2 — wheel events (always compiled in).  */
  result = Fcons (Fcons (Qwheel_event, make_fixnum (WHEEL_EVENT)), result);
  result = Fcons (Fcons (Qhorizontal_wheel_event, make_fixnum (HORIZ_WHEEL_EVENT)), result);

  /* imp-7.3 — touch/pinch (always compiled in).  */
  result = Fcons (Fcons (Qtouch_end, make_fixnum (TOUCH_END_EVENT)), result);
  result = Fcons (Fcons (Qpinch, make_fixnum (PINCH_EVENT)), result);

  /* imp-7.4 — touchscreen group (always compiled in).  */
  result = Fcons (Fcons (Qtouchscreen_begin, make_fixnum (TOUCHSCREEN_BEGIN_EVENT)), result);
  result = Fcons (Fcons (Qtouchscreen_end, make_fixnum (TOUCHSCREEN_END_EVENT)), result);
  result = Fcons (Fcons (Qtouchscreen_update, make_fixnum (TOUCHSCREEN_UPDATE_EVENT)), result);

  /* imp-7.5 — mouse click + non-toolkit scroll-bar click.  */
  result = Fcons (Fcons (Qmouse_click_event, make_fixnum (MOUSE_CLICK_EVENT)), result);
#ifndef USE_TOOLKIT_SCROLL_BARS
  result = Fcons (Fcons (Qscroll_bar_click_event, make_fixnum (SCROLL_BAR_CLICK_EVENT)), result);
  result = Fcons (Fcons (Qhorizontal_scroll_bar_click_event, make_fixnum (HORIZONTAL_SCROLL_BAR_CLICK_EVENT)), result);
#endif

  /* Swallowed kinds — imp-3 dispatch switch (never produce a Lisp
     event: handled and looped back to wait).  */
  result = Fcons (Fcons (Qselection_request_event, make_fixnum (SELECTION_REQUEST_EVENT)), result);
  result = Fcons (Fcons (Qselection_clear_event, make_fixnum (SELECTION_CLEAR_EVENT)), result);
  result = Fcons (Fcons (Qmonitors_changed, make_fixnum (MONITORS_CHANGED_EVENT)), result);
  result = Fcons (Fcons (Qmenu_bar_activate_event, make_fixnum (MENU_BAR_ACTIVATE_EVENT)), result);

  /* More entries added as additional kind groups are ported.  */
  return result;
}

/* M11 imp-1.1 — kbd_buffer queue accessors for Scheme ring-buffer walking.
   See docs/m11-plan.org §imp-1.1.  */

DEFUN ("--kbd-fetch-ptr-index", Fkbd_fetch_ptr_index, Skbd_fetch_ptr_index, 0, 0, 0,
       doc: /* Return the current kbd_fetch_ptr index (0..KBD_BUFFER_SIZE-1).

This is the integer offset into kbd_buffer where the next dequeue
will read.  Together with --kbd-store-ptr-index, Scheme can detect
whether the queue is empty (indices equal) without walking pointers.  */)
  (void)
{
  return make_fixnum (kbd_fetch_ptr - kbd_buffer);
}

DEFUN ("--kbd-store-ptr-index", Fkbd_store_ptr_index, Skbd_store_ptr_index, 0, 0, 0,
       doc: /* Return the current kbd_store_ptr index (0..KBD_BUFFER_SIZE-1).

The position where the next event will be enqueued (producer cursor).  */)
  (void)
{
  return make_fixnum (kbd_store_ptr - kbd_buffer);
}

DEFUN ("--kbd-buffer-nr-stored", Fkbd_buffer_nr_stored, Skbd_buffer_nr_stored, 0, 0, 0,
       doc: /* Return the number of events currently in kbd_buffer.

Wraps kbd_buffer_nr_stored().  Returns 0 when fetch == store.
Handles wrap-around (kbd_store_ptr may have wrapped past KBD_BUFFER_SIZE).  */)
  (void)
{
  ptrdiff_t n = kbd_store_ptr - kbd_fetch_ptr;
  return make_fixnum (n + (n < 0 ? KBD_BUFFER_SIZE : 0));
}

/* M28 imp-3 — batched ring-cursor EMPTY test.  Replaces two separate
   Scheme→C crossings (fetch-index + store-index) on the queue-empty
   path with one atomic C comparison.  Pure C read (no advance, no
   side effect).

   An early imp-3 attempt also added --kbd-peek-event (fetch index +
   kind copy + ie-smob in one call) to batch the dispatch prologue.
   It was REMOVED after measurement (cr.org F3): it allocated a
   scm_values list + call-with-values + re-list on top of the single
   (unavoidable) ie_wrap smob and regressed the bench median 5.0 ->
   6.0 us.  The dispatch prologue stays three scalar crossings.  */

DEFUN ("--kbd-empty-p", Fkbd_empty_p, Skbd_empty_p, 0, 0, 0,
       doc: /* Return t when the kbd_buffer queue is empty, else nil.

One atomic C read of both ring cursors — more correct than comparing
two separate --kbd-fetch-ptr-index / --kbd-store-ptr-index reads.  */)
  (void)
{
  return (kbd_fetch_ptr == kbd_store_ptr) ? Qt : Qnil;
}

DEFUN ("--frame-set-mouse-moved!", Fframe_set_mouse_moved,
       Sframe_set_mouse_moved, 1, 1, 0,
       doc: /* Internal: set FRAME's mouse_moved flag to true.

Restore side of show_help_echo's save/restore around the
mouse-fixup-help-message call: the Lisp call can reset mouse_moved as
a side effect, so the flag saved by some-mouse-moved is restored
here afterward.  Always sets true — there is no false-setting call
site.  */)
  (Lisp_Object frame)
{
  CHECK_FRAME (frame);
  XFRAME (frame)->mouse_moved = true;
  return Qnil;
}

/* M22 imp-3 — track-mouse trio.  Primitives for the (emacs
   read-key-sequence) port of some_mouse_moved / tracking_off /
   Finternal_track_mouse.  See docs/m22-plan.org §imp-3.  */

DEFUN ("--track-mouse", Fc_track_mouse, Sc_track_mouse, 0, 0, 0,
       doc: /* FIX-20260901-guilemacs: Internal: return the C track_mouse cell.
Distinct from the elisp dynamic variable `track-mouse' read via
symbol-value; this is the C Lisp_Object cell some_mouse_moved tests.  */)
  (void)
{
  return track_mouse;
}

DEFUN ("--track-mouse-set!", Fc_track_mouse_set, Sc_track_mouse_set, 1, 1, 0,
       doc: /* FIX-20260901-guilemacs: Internal: set the C track_mouse cell.  */)
  (Lisp_Object v)
{
  track_mouse = v;
  return Qnil;
}

DEFUN ("--frame-mouse-moved-p", Fc_frame_mouse_moved_p, Sc_frame_mouse_moved_p, 1, 1, 0,
       doc: /* FIX-20260901-guilemacs: Internal: t if FRAME's mouse_moved
bitfield is set.  Read-only — never clears the flag; the C redisplay
code is what resets mouse_moved elsewhere.  */)
  (Lisp_Object frame)
{
  CHECK_FRAME (frame);
  return XFRAME (frame)->mouse_moved ? Qt : Qnil;
}

DEFUN ("--frame-list-raw", Fc_frame_list_raw, Sc_frame_list_raw, 0, 0, 0,
       doc: /* FIX-20260901-guilemacs: Internal: return a copy of the raw
Vframe_list in scan order.

The elisp primitive `frame-list' — when compiled with a window system —
filters out tooltip frames and reverses the order (Fframe_list,
src/frame.c).  some_mouse_moved walks Vframe_list directly via
FOR_EACH_FRAME — no filter, forward order — so Scheme needs this raw
copy to behave identically.  Returns a fresh list; the caller may not
mutate Vframe_list.  */)
  (void)
{
  return Fcopy_sequence (Vframe_list);
}

DEFUN ("--kbd-event-kind", Fkbd_event_kind, Skbd_event_kind, 1, 1, 0,
       doc: /* Return the event_kind at kbd_buffer index N (0-based fixnum).

Reads kbd_buffer[N].kind directly without minting an ie-smob.
Scheme uses this for peek-ahead during pinch coalescing and
for the outer dispatch switch before committing to --kbd-event-ie.

No bounds check — caller must ensure 0 <= N < KBD_BUFFER_SIZE.  */)
  (Lisp_Object n)
{
  EMACS_INT idx = XFIXNUM (n);
  eassert (idx >= 0 && idx < KBD_BUFFER_SIZE);
  return make_fixnum (kbd_buffer[idx].kind);
}

DEFUN ("--kbd-event-ie", Fkbd_event_ie, Skbd_event_ie, 1, 1, 0,
       doc: /* Return a fresh ie-smob wrapping &kbd_buffer[N].ie.

Lifetime contract (M9): the smob is invalidated when the enclosing
DEFUN call returns.  Scheme MUST extract all needed fields (via
--ie-kind, --ie-arg, etc.) BEFORE any operation that might advance
kbd_fetch_ptr.  The smob wraps a live pointer into the ring buffer —
advancing fetch_ptr may overwrite that slot.

No bounds check — caller must ensure 0 <= N < KBD_BUFFER_SIZE.  */)
  (Lisp_Object n)
{
  EMACS_INT idx = XFIXNUM (n);
  eassert (idx >= 0 && idx < KBD_BUFFER_SIZE);
  return ie_wrap (&kbd_buffer[idx].ie);
}

DEFUN ("--kbd-advance-fetch-ptr", Fkbd_advance_fetch_ptr, Skbd_advance_fetch_ptr, 0, 0, 0,
       doc: /* Advance kbd_fetch_ptr past the current event.

Equivalent to `kbd_fetch_ptr = next_kbd_event(kbd_fetch_ptr)'.
Does NOT update input_pending — the C code sets it at the end of
kbd_buffer_get_event via readable_events() (keyboard.c:5542), which is
a heavier check than pointer comparison.  Scheme queries input_pending
via --get-input-pending when needed.  Returns nil.

Caller MUST ensure all ie-smobs from the old fetch position have been
extracted and dropped — this may overwrite the slot with new input.  */)
  (void)
{
  kbd_fetch_ptr = next_kbd_event (kbd_fetch_ptr);
  return Qnil;
}

DEFUN ("--update-input-pending", Fupdate_input_pending,
       Supdate_input_pending, 0, 0, 0,
       doc: /* Recompute the C global `input_pending' via readable_events (0).

Mirrors the `input_pending = readable_events (0)' statement the C
switch executes after advancing past a swallowed event kind
(keyboard.c:5207/5230/5239/5252/5263).  --kbd-advance-fetch-ptr does
NOT do this (see its docstring), so the imp-3 dispatch port calls this
after advancing for the swallowed kinds whose C handlers update
input_pending.  Returns nil.  */)
  (void)
{
  input_pending = readable_events (0);
  return Qnil;
}

DEFUN ("--kbd-set-fetch-ptr-index", Fkbd_set_fetch_ptr_index, Skbd_set_fetch_ptr_index, 1, 1, 0,
       doc: /* Set kbd_fetch_ptr to kbd_buffer[N].

Used by pinch coalescing to skip past coalesced events.
Caller must ensure 0 <= N < KBD_BUFFER_SIZE.  Returns nil.  */)
  (Lisp_Object n)
{
  EMACS_INT idx = XFIXNUM (n);
  eassert (idx >= 0 && idx < KBD_BUFFER_SIZE);
  kbd_fetch_ptr = &kbd_buffer[idx];
  return Qnil;
}

DEFUN ("--kbd-set-store-ptr-index", Fkbd_set_store_ptr_index, Skbd_set_store_ptr_index, 1, 1, 0,
       doc: /* Set kbd_store_ptr to kbd_buffer[N].

Used by the M13 store-side port to position the producer cursor
before storing an event.  Caller must ensure 0 <= N < KBD_BUFFER_SIZE.
Returns nil.  */)
  (Lisp_Object n)
{
  EMACS_INT idx = XFIXNUM (n);
  eassert (idx >= 0 && idx < KBD_BUFFER_SIZE);
  kbd_store_ptr = &kbd_buffer[idx];
  return Qnil;
}

DEFUN ("--kbd-handle-selection-event", Fkbd_handle_selection_event,
       Skbd_handle_selection_event, 0, 0, 0,
       doc: /* Handle a selection event at the current kbd_fetch_ptr
position.

If the event at kbd_fetch_ptr is SELECTION_REQUEST_EVENT or
SELECTION_CLEAR_EVENT, handle it via the platform-specific handler,
advance kbd_fetch_ptr, update input_pending, and return t.

If the event at the fetch position is NOT a selection event, return
nil and leave the queue state unchanged.

Selection events do not produce a Lisp event — they are swallowed by
the C-side handler.  The Scheme wait loop calls this before other
event dispatch; on t, it loops back to wait for the next event.

Platform routing is internal:
  X11:   x_handle_selection_event   (struct selection_input_event *)
  PGTK:  pgtk_handle_selection_event (same)
  Otherwise: emacs_abort ().  */)
  (void)
{
  if (kbd_fetch_ptr == kbd_store_ptr)
    return Qnil;

  switch (kbd_fetch_ptr->kind)
    {
    case SELECTION_REQUEST_EVENT:
    case SELECTION_CLEAR_EVENT:
      {
# if defined HAVE_X11 || defined HAVE_PGTK
        /* Remove it from the buffer before processing it, since
           otherwise swallow_events will see it and process it
           again.  */
        struct selection_input_event copy = kbd_fetch_ptr->sie;
        kbd_fetch_ptr = next_kbd_event (kbd_fetch_ptr);
        input_pending = readable_events (0);
#  ifdef HAVE_X11
        x_handle_selection_event (&copy);
#  else
        pgtk_handle_selection_event (&copy);
#  endif
        return Qt;
# else
        emacs_abort ();
# endif
      }
    default:
      return Qnil;
    }
}

DEFUN ("--kbd-excise-selection-event-at!",
       Fc_kbd_excise_selection_event_at,
       Sc_kbd_excise_selection_event_at, 1, 1, 0,
       doc: /* Internal: if kbd_buffer[N]'s kind is
SELECTION_REQUEST_EVENT or SELECTION_CLEAR_EVENT, excise it from the
ring's middle (two-arm cyclic memmove, copy taken first as a
re-entrancy guard), dispatch the platform handler on the copy,
update input_pending, and return t.  Otherwise return nil and leave
the ring untouched.

Caller must ensure 0 <= N < KBD_BUFFER_SIZE.  The Scheme walk in
kbd-buffer-process-special-events! finds N by scanning kind fields
between the fetch and store cursors, then re-reads both cursors
after each excise (this shim moves them).  Aborts on builds without
HAVE_X11 or HAVE_PGTK, matching process_special_events' no-window
arm.  */)
  (Lisp_Object n)
{
  EMACS_INT idx = XFIXNUM (n);
  eassert (idx >= 0 && idx < KBD_BUFFER_SIZE);
  union buffered_input_event *event = &kbd_buffer[idx];

  if (event->kind != SELECTION_REQUEST_EVENT
      && event->kind != SELECTION_CLEAR_EVENT)
    return Qnil;

#if defined HAVE_X11 || defined HAVE_PGTK
  struct selection_input_event copy = event->sie;
  int moved_events;

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
  return Qt;
#else
  emacs_abort ();
#endif
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
  /* M27 imp-1 — C body replaced by a SCM_CALL_1 into (emacs
     single-kboard).  The single_kboard flag clear lives in Scheme
     (not-single-kboard-state) over the M2 kboard smob.  */
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs single-kboard", "not-single-kboard-state");
  SCM_CALL_1 (proc, make_kboard_smob (kboard));
}

/* Maintain a stack of kboards, so other parts of Emacs
   can switch temporarily to the kboard of a given frame
   and then revert to the previous status.  The C struct
   kboard_stack node is now a Scheme list owned by the
   (emacs single-kboard) module.  */

void
push_kboard (struct kboard *k)
{
  /* M27 imp-1 — C body replaced by a SCM_CALL_1 into (emacs
     single-kboard).  push-kboard! saves current_kboard then sets it
     to the pushed kboard, exactly like the deleted C node push.  */
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs single-kboard", "push-kboard!");
  SCM_CALL_1 (proc, make_kboard_smob (k));
}

void
pop_kboard (void)
{
  /* M27 imp-1 — C body replaced by a SCM_CALL_0 into (emacs
     single-kboard).  pop-kboard! restores the saved kboard if it is
     still live (any terminal still carries it), else falls back to the
     selected frame's kboard and clears single_kboard.  */
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs single-kboard", "pop-kboard!");
  SCM_CALL_0 (proc);
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
    }
  /* M27 imp-1 — the current-kboard / single_kboard switch policy
     dispatches to (emacs single-kboard)
     temporarily-switch-to-single-kboard!.  The locked-terminal error
     above stays in the C entry (noreturn); so does the
     record_unwind_protect_int unwind below, so a Scheme dispatch that
     moves current_kboard cannot disturb the unwind frame (see
     restore_kboard_configuration).  */
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs single-kboard",
                             "temporarily-switch-to-single-kboard!");
  SCM_CALL_2 (proc,
              was_locked ? Qt : Qnil,
              f ? make_kboard_smob (FRAME_KBOARD (f)) : Qnil);
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
  /* M22 imp-2: thin dispatcher.  The body lives in Scheme as
     (emacs command-loop)/cmd-error-internal!.  Keep this C signature so
     the two process.c call sites need no change.  */
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs command-loop", "cmd-error-internal!");
  SCM_CALL_2 (proc, data,
              context ? build_string (context) : empty_unibyte_string);
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
   recursive-edit).  Since M22 imp-2 the recursive-edit body and its
   unwind (buffer/level restore) live entirely in Scheme, so the
   level is read and stepped via these accessors.  See
   docs/keyboard.org §M4.  */

DEFUN ("--command-loop-level", Fcommand_loop_level, Scommand_loop_level, 0, 0, 0,
       doc: /* Internal: current depth in recursive edits.
-1 means not yet inside any command loop.  Stepped by
recursive-edit in Scheme (emacs recursive-edit).  */)
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

/* M22 imp-2 — one-purpose accessors for C-only recursive-edit state.
   Permanent accessors (not workarounds): the wrapped state is either a
   plain C global/function with no Lisp-visible name, or a one-way
   step.  Follows the --recent-keys-ring-set! precedent from M22 imp-1.  */

DEFUN ("--input-blocked-p", Fc_input_blocked_p, Sc_input_blocked_p, 0, 0, 0,
       doc: /* Internal: t if input is currently blocked
(input_blocked_p ()).  recursive-edit returns early when true.  */)
  (void)
{
  return input_blocked_p () ? Qt : Qnil;
}

DEFUN ("--command-loop-level-increment!", Fc_command_loop_level_increment,
       Sc_command_loop_level_increment, 0, 0, 0,
       doc: /* Internal: increment command_loop_level and return the new
value as a fixnum.  */)
  (void)
{
  return make_fixnum (++command_loop_level);
}

DEFUN ("--command-loop-level-decrement!", Fc_command_loop_level_decrement,
       Sc_command_loop_level_decrement, 0, 0, 0,
       doc: /* Internal: decrement command_loop_level and return the new
value as a fixnum.  */)
  (void)
{
  return make_fixnum (--command_loop_level);
}

DEFUN ("--update-mode-lines-set!", Fc_update_mode_lines_set,
       Sc_update_mode_lines_set, 1, 1, 0,
       doc: /* Internal: set the C global update_mode_lines to N (a
fixnum).  recursive-edit sets it to 17 on entry and 18 on exit.  */)
  (Lisp_Object n)
{
  CHECK_FIXNUM (n);
  update_mode_lines = XFIXNUM (n);
  return Qnil;
}

DEFUN ("--redisplaying-p-clear!", Fc_redisplaying_p_clear,
       Sc_redisplaying_p_clear, 0, 0, 0,
       doc: /* Internal: set the C bool global redisplaying_p to false.
Lets redisplay run inside a recursive edit entered from within
redisplay (e.g. Edebugging a fontification-functions call).  */)
  (void)
{
  redisplaying_p = false;
  return Qnil;
}

DEFUN ("--temporarily-switch-to-single-kboard!",
       Fc_temporarily_switch_to_single_kboard,
       Sc_temporarily_switch_to_single_kboard, 0, 0, 0,
       doc: /* Internal: call temporarily_switch_to_single_kboard on the
selected frame (M27-owned, kept C).  */)
  (void)
{
  temporarily_switch_to_single_kboard (SELECTED_FRAME ());
  return Qnil;
}

DEFUN ("--recursive-edit-quit!", Fc_recursive_edit_quit,
       Sc_recursive_edit_quit, 0, 0, 0,
       doc: /* Internal: call the real C quit (void).  Not the same as
elisp (signal 'quit nil): quit calls signal_or_quit with
continuable = true.  recursive-edit tail calls this when the
command loop returns t.  */)
  (void)
{
  quit ();
  return Qnil;
}

DEFUN ("--signal-quit-p", Fc_signal_quit_p, Sc_signal_quit_p, 1, 1, 0,
       doc: /* Internal: t if DATA is a quit-condition (signal_quit_p).  */)
  (Lisp_Object data)
{
  return signal_quit_p (data) ? Qt : Qnil;
}

DEFUN ("--signaling-function", Fc_signaling_function,
       Sc_signaling_function, 0, 0, 0,
       doc: /* Internal: return the C global Vsignaling_function.  */)
  (void)
{
  return Vsignaling_function;
}

DEFUN ("--signaling-function-set!", Fc_signaling_function_set,
       Sc_signaling_function_set, 1, 1, 0,
       doc: /* Internal: set the C global Vsignaling_function to N.  */)
  (Lisp_Object n)
{
  Vsignaling_function = n;
  return Qnil;
}

/* `exit-recursive-edit' and `abort-recursive-edit' are provided
   entirely by Scheme — see (emacs recursive-edit).  They are
   registered against their elisp symbols by
   init-recursive-edit-registrations at prelude/load.scm startup
   time.  */

/* Restore mouse tracking enablement.  See Finternal_track_mouse for
   the only use of this function.  */
/* M22 imp-3: tracking_off and some_mouse_moved moved to Scheme (emacs
   read-key-sequence); their C bodies were deleted with the cutover.  */

DEFUN ("internal--track-mouse", Finternal_track_mouse, Sinternal_track_mouse,
       1, 1, 0,
       doc: /* Call BODYFUN with mouse movement events enabled.  */)
  (Lisp_Object bodyfun)
{
  /* M22 imp-3: dispatch to (emacs read-key-sequence)
     internal-track-mouse, which ports the old dynwind/record_unwind
     dance with Guile dynamic-wind.  */
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs read-key-sequence", "internal-track-mouse");
  return SCM_CALL_1 (proc, bodyfun);
}

/* If mouse has moved on some frame and we are tracking the mouse,
   return one of those frames.  Return NULL otherwise.

   If ignore_mouse_drag_p is non-zero, ignore (implicit) mouse movement
   after resizing the tool-bar window.  */
/* M22 imp-3: some_mouse_moved moved to (emacs read-key-sequence);
   its C body was deleted with the cutover.  */

bool ignore_mouse_drag_p;


/* This is the actual command reading loop,
   sans error-handling encapsulation.  */

enum { READ_KEY_ELTS = 30 };
static int read_key_sequence (Lisp_Object *, Lisp_Object,
                              bool, bool, bool, bool, bool);

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

DEFUN ("--get-large-narrowing-begv", Fc_get_large_narrowing_begv,
       Sc_get_large_narrowing_begv, 1, 1, 0,
       doc: /* Internal: return the large-narrowing begv for POS.
Wraps xdisp.c get_large_narrowing_begv, which has no Lisp-visible
primitive.  FIX-20260901-guilemacs.  */)
  (Lisp_Object pos)
{
  CHECK_FIXNUM (pos);
  return make_fixnum (get_large_narrowing_begv (XFIXNUM (pos)));
}

DEFUN ("--get-large-narrowing-zv", Fc_get_large_narrowing_zv,
       Sc_get_large_narrowing_zv, 1, 1, 0,
       doc: /* Internal: return the large-narrowing zv for POS.
Wraps xdisp.c get_large_narrowing_zv, which has no Lisp-visible
primitive.  FIX-20260901-guilemacs.  */)
  (Lisp_Object pos)
{
  CHECK_FIXNUM (pos);
  return make_fixnum (get_large_narrowing_zv (XFIXNUM (pos)));
}

DEFUN ("--buffer-beg", Fc_buffer_beg, Sc_buffer_beg, 0, 0, 0,
       doc: /* Internal: return the absolute start position (BEG) of the
current buffer.  Unlike `point-min', this does not move when the buffer
is narrowed (BEG is always 1).  FIX-20260901-guilemacs.  */)
  (void)
{
  return make_fixnum (BEG);
}

DEFUN ("--buffer-end", Fc_buffer_end, Sc_buffer_end, 0, 0, 0,
       doc: /* Internal: return the absolute end position (Z) of the
current buffer.  Unlike `point-max', this does not move when the buffer
is narrowed.  FIX-20260901-guilemacs.  */)
  (void)
{
  return make_fixnum (Z);
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

DEFUN ("--waiting-for-input-p", Fc_waiting_for_input_p,
       Sc_waiting_for_input_p, 0, 0, 0,
       doc: /* Internal: t if the C waiting_for_input flag is set.  */)
  (void)
{
  return waiting_for_input ? Qt : Qnil;
}

DEFUN ("--message3-nolog", Fc_message3_nolog, Sc_message3_nolog, 1, 1, 0,
       doc: /* Internal: display MSG in the echo area, no log entry.
Wraps xdisp.c message3_nolog.  */)
  (Lisp_Object msg)
{
  message3_nolog (msg);
  return Qnil;
}

DEFUN ("--truncate-echo-area", Fc_truncate_echo_area,
       Sc_truncate_echo_area, 1, 1, 0,
       doc: /* Internal: truncate the echo area to N columns.
Wraps xdisp.c truncate_echo_area.  */)
  (Lisp_Object n)
{
  CHECK_FIXNUM (n);
  truncate_echo_area (XFIXNUM (n));
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
plumb it.  M22 imp-3: dispatches to (emacs command-loop).  */)
  (void)
{
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs command-loop", "adjust-point-for-property");
  SCM_CALL_2 (proc, make_fixnum (last_point_position),
	      MODIFF != cl1_prev_modiff ? Qt : Qnil);
  return Qnil;
}

DEFUN ("--composition-adjust-point", Fc_composition_adjust_point,
       Sc_composition_adjust_point, 2, 2, 0,
       doc: /* FIX-20260901-guilemacs: Internal: return
composition_adjust_point (LAST-PT, PT) as a fixnum — the actual new
position, unlike the *-changes-p variants which only report whether
the position moved.  */)
  (Lisp_Object last_pt, Lisp_Object pt)
{
  CHECK_FIXNUM (last_pt);
  CHECK_FIXNUM (pt);
  return make_fixnum (composition_adjust_point (XFIXNUM (last_pt),
						XFIXNUM (pt)));
}

DEFUN ("--display-prop-intangible-p", Fc_display_prop_intangible_p,
       Sc_display_prop_intangible_p, 4, 4, 0,
       doc: /* FIX-20260901-guilemacs: Internal: t if the display property
VAL (on OVERLAY, at POS / POS-BYTE) is an intangible display
property.  Wraps display_prop_intangible_p.  */)
  (Lisp_Object val, Lisp_Object overlay, Lisp_Object pos, Lisp_Object pos_byte)
{
  CHECK_FIXNUM (pos);
  CHECK_FIXNUM (pos_byte);
  return (display_prop_intangible_p (val, overlay, XFIXNUM (pos),
				     XFIXNUM (pos_byte))
	  ? Qt : Qnil);
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

DEFUN ("--store-kbd-macro-char", Fc_store_kbd_macro_char,
       Sc_store_kbd_macro_char, 1, 1, 0,
       doc: /* FIX-20260829-guilemacs: internal: thin shim over C
store_kbd_macro_char.  Appends C to the kbd macro being defined, if
one is being defined.  Used by the Scheme
read-char-minibuf-menu-prompt port (M20).  */)
  (Lisp_Object c)
{
  store_kbd_macro_char (c);
  return Qnil;
}

Lisp_Object
read_menu_command (void)
{
  /* M20 imp-4 — C body (dynwind/specbind/read_key_sequence/FRAME_LIVE_P
     logic) replaced by a SCM_CALL into (emacs menu-prompt)
     read-menu-command, which reproduces the echo-keystrokes save/restore
     and FRAME_LIVE_P / kill-emacs check internally.  Keep signature and
     non-static linkage: src/term.c:3265 calls this directly.  */
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs menu-prompt", "read-menu-command");
  return SCM_CALL_0 (proc);
}

/* M22 imp-4: safe_run_hooks family moved to (emacs command-loop);
   safe_run_hooks and safe_run_hooks_2 remain thin dispatchers for
   cross-file callers; the other four bodies were deleted with the
   cutover.  */

void
safe_run_hooks (Lisp_Object hook)
{
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs command-loop", "safe-run-hooks!");
  SCM_CALL_1 (proc, hook);
}

void
safe_run_hooks_2 (Lisp_Object hook, Lisp_Object arg1, Lisp_Object arg2)
{
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs command-loop", "safe-run-hooks-2!");
  SCM_CALL_3 (proc, hook, arg1, arg2);
}


#ifdef POLL_FOR_INPUT

/* Asynchronous timer for polling.  */

static struct atimer *poll_timer;

/* Timer callback function for poll_timer.  TIMER is equal to
   poll_timer.  */

static void
poll_for_input (struct atimer *timer)
{
}

/* M24 shim — (re)start the poll atimer at the current polling period.
   Mirrors the inner "start a new one" block of the old start_polling
   body: turn alarm handling on, cancel any existing poll_timer, then
   register a fresh continuous timer.  The compare-against-cached-period
   decision (when to call this) moved to (emacs input-poll) as
   start-polling!; that is the only piece of state that left C.  Returns
   Qnil always.  */

DEFUN ("--atimer-poll-restart!", F_atimer_poll_restart,
       S_atimer_poll_restart, 0, 0, 0,
       doc: /* Internal: (re)start the poll atimer at the current
polling-period.  Mirrors the inner "start a new one" block of the old
C start_polling; the when-to-restart decision lives in (emacs input-poll)
as `start-polling!'.  */)
  (void)
{
  turn_on_atimers (1);
  struct timespec interval = dtotimespec (XFLOATINT (Vpolling_period));

  if (poll_timer)
    cancel_atimer (poll_timer);

  poll_timer = start_atimer (ATIMER_CONTINUOUS, interval,
			     poll_for_input, NULL);
  return Qnil;
}

#endif /* POLL_FOR_INPUT */

/* Begin signals to poll for input, if they are appropriate.
   This function is called unconditionally from various places.  The
   body lives in (emacs input-poll) as `start-polling!'; this C entry
   point is a thin dispatcher for non-Scheme callers (init_keyboard,
   bind_polling_period, the --start-polling DEFUN).  */

void
start_polling (void)
{
#ifdef POLL_FOR_INPUT
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs input-poll", "start-polling!");
  SCM_CALL_0 (proc);
#endif
}

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
  /* M16 imp-3 — C body replaced by a SCM_CALL_4 into the Scheme
     procedure in (emacs help-echo) show-help-echo.  */
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs help-echo", "show-help-echo");
  SCM_CALL_4 (proc, help, window, object, pos);
}



/* Input of single characters from keyboard.  */

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





/* Maximum number of bytes in an encoded keyboard input sequence that
   read_decoded_event_from_main_queue buffers before decoding.  File
   scope (not function-local) so the M12 imp-1 tty decode shim below
   uses the same bound without depending on a scoped #define leaking
   out of the decode loop.  */
#define MAX_ENCODED_BYTES 16

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

   The plain Scheme used-mouse-menu flag (M12 imp-1, formerly slot 4)
   is at slot 3; the end-time slot holds the one caller-owned C pointer
   as a Guile foreign-pointer SCM (or Qnil when NULL), which
   round-trips through read_char() entry and the bulk subrs that need
   it.  M12 imp-3 deleted the used-mouse-menu pointer slot.  */

enum rc_slot {
  RC_SLOT_COMMANDFLAG                 = 0,
  RC_SLOT_MAP                         = 1,
  RC_SLOT_PREV_EVENT                  = 2,
  RC_SLOT_USED_MOUSE_MENU_FLAG        = 3,  /* plain Scheme boolean (imp-1) */
  RC_SLOT_END_TIME                    = 4,  /* foreign-ptr to struct timespec, or Qnil */
  RC_SLOT_C                           = 5,
  RC_SLOT_LOCAL_TAG                   = 6,
  RC_SLOT_PREVIOUS_ECHO_AREA_MESSAGE  = 7,
  RC_SLOT_ALSO_RECORD                 = 8,
  RC_SLOT_RECORDED                    = 9,
  RC_SLOT_REREAD                      = 10,
  RC_SLOT_ORIG_KBOARD                 = 11, /* kboard SMOB */
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

/* C-9b: retired — the <keyremap> file-static struct and the
   load/store helpers that mirrored it are gone.  C reads the keyremap
   fields of the live <rks-state> record directly (see the field-level
   helper below).  */

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
   last-input-event update, the block-2 add-command-key / echo
   sequence, and the help-echo dispatch (reached directly through the
   (emacs help-echo) port since M28 imp-5 group 2).  C still owns the
   mouse-movement event predicate, the ok_to_echo_at_next_pause global
   write, the num_input_events counter, and the Block 3 recursive
   read_char loop with its dynwind / help-form-saved-window-configs
   machinery.  */

DEFUN ("--safe-calln-or-eval", Fsafe_calln_or_eval, Ssafe_calln_or_eval,
       4, 4, 0,
       doc: /* Internal: resolve untrusted HELP for show-help-echo.

If HELP is a function, call it with WINDOW OBJECT POS via safe_calln
(errors are caught, logged, and muted — never signaled to the
caller).  Otherwise evaluate HELP as a form via safe_eval, same error
containment.  Returns whatever the safe call/eval produces — the
Scheme caller is responsible for checking it is a string before use,
matching C's own STRINGP re-check after this call.  */)
  (Lisp_Object help, Lisp_Object window, Lisp_Object object, Lisp_Object pos)
{
  if (FUNCTIONP (help))
    return safe_calln (help, window, object, pos);
  else
    return safe_eval (help);
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

DEFUN ("--rc-clear-echo-at-next-pause",
       Fc_rc_clear_echo_at_next_pause,
       Sc_rc_clear_echo_at_next_pause, 0, 0, 0,
       doc: /* FIX-20260829-guilemacs: internal: set
ok_to_echo_at_next_pause = NULL.  Used by the Scheme
record-menu-key port (M20).  */)
  (void)
{
  ok_to_echo_at_next_pause = NULL;

  return Qnil;
}

DEFUN ("--rc-ok-to-echo-at-next-pause-p",
       Fc_rc_ok_to_echo_at_next_pause_p,
       Sc_rc_ok_to_echo_at_next_pause_p, 0, 0, 0,
       doc: /* FIX-20260829-guilemacs: internal: t when
ok_to_echo_at_next_pause is non-NULL.  Raw reader for the
--rc-allow/--rc-clear-echo-at-next-pause pair, so Scheme tests can
assert the field state.  */)
  (void)
{
  return ok_to_echo_at_next_pause ? Qt : Qnil;
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
   owns the menu-bar event POSN_SET_POSN rewrite and the echo-area /
   mini-window cleanup primitives.  C record_char is reached directly
   through the (emacs recent-keys) port since M28 imp-5 group 2.
   The keyboard-translate-table lookup is now fully in Scheme
   (rc-translate-kbd-table).  */

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
   logic and dispatch; the X-menu step calls into (emacs menu-prompt)
   read-char-x-menu-prompt; C still owns the idle-timer machinery,
   and the buffer-size-scaled auto-save / GC block which is dense
   C-internal arithmetic.  */

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
   Scheme owns the control flow; C still owns the echo globals.  */

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

DEFUN ("--rc-pin-echo-kboard-to-current",
       Fc_rc_pin_echo_kboard_to_current,
       Sc_rc_pin_echo_kboard_to_current, 0, 0, 0,
       doc: /* Internal: set echo_kboard = current_kboard.
Used by Scheme rc-prologue-redisplay! after the redisplay loop, so
that a current echo-area message is attributed to the current
kboard (see echo_kboard's declaration).  */)
  (void)
{
  echo_kboard = current_kboard;
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

DEFUN ("--rc-help-echo-showing-set!",
       Frc_help_echo_showing_set,
       Src_help_echo_showing_set, 1, 1, 0,
       doc: /* Internal: set the shared help_echo_showing_p flag.

Single write path for the cell xdisp.c reads (xdisp.c:13450, :38606)
and --rc-help-echo-redisplay-preserve-p reads.  Do not shadow this
with a Scheme-local copy — xdisp would desync.  */)
  (Lisp_Object flag)
{
  help_echo_showing_p = !NILP (flag);
  return Qnil;
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

DEFUN ("--redisplay-preserve-echo-area", Fc_redisplay_preserve_echo_area,
       Sc_redisplay_preserve_echo_area, 1, 1, 0,
       doc: /* Internal: call redisplay_preserve_echo_area (N).

Generalizes --rc-redisplay-preserve-echo-area's hardcoded 5 so
kbd-buffer-swallow-events! can pass swallow_events' 7.  Returns
nil.  */)
  (Lisp_Object n)
{
  CHECK_FIXNUM (n);
  redisplay_preserve_echo_area (XFIXNUM (n));
  return Qnil;
}

DEFUN ("--timers-run", Fc_timers_run, Sc_timers_run, 0, 0, 0,
       doc: /* Internal: return the C timers_run counter as a
fixnum.  Used by kbd-buffer-swallow-events! to snapshot and compare
timers_run around get_input_pending; shared with M15.  */)
  (void)
{
  return make_fixnum (timers_run);
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
  SCM result = scm_call_5 (proc,
                           make_fixnum (commandflag),
                           map, prev_event,
                           rc_wrap_ptr (end_time),
                           make_kboard_smob (current_kboard));
  /* M12 imp-3: read-char-entry returns two values — the resolved
     event and the used-mouse-menu flag (plain Scheme boolean), the
     only remaining path for that flag (the pointer slot is deleted).
     Read both back with scm_c_value_ref (a non-values result is a
     single value, itself) and write the flag through the caller's
     pointer — callers of read_char still read through it.  */
  Lisp_Object event = scm_c_value_ref (result, 0);
  bool flag = scm_is_true (scm_c_value_ref (result, 1));
  if (used_mouse_menu)
    *used_mouse_menu = flag;
  return event;
}
/* {{coccinelle:skip_end}} */

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
  /* M17 imp-3 — C body replaced by a SCM_CALL_1 into the Scheme
     procedure in (emacs recent-keys) record-char.  */
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs recent-keys", "record-char");
  SCM_CALL_1 (proc, c);
}

/* Low level keyboard/mouse input.
   kbd_buffer_store_event places events in kbd_buffer, and
   kbd_buffer_get_event retrieves them.  */

/* Return true if there are any events in the queue that read-char
   would return.  If this returns false, a read-char would block.  */
static bool
readable_events (int flags)
{
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs kbd-buffer", "kbd-buffer-readable-events");
  return scm_is_true (SCM_CALL_1 (proc, scm_from_int (flags)));
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

DEFUN ("--ie-kboard", Fie_kboard, Sie_kboard, 1, 1, 0,
       doc: /* Return the KBOARD that owns input-event handle IE, as a
   kboard smob, or nil when the event resolves to no live frame's
   kboard (event_to_kboard returns NULL for the two selection kinds,
   dead frames, and non-frame frame_or_window values).

   Exposes the deleted C queue-event prologue
   `*kbp = event_to_kboard (&event->ie); if (*kbp == 0) *kbp =
   current_kboard;` so the Scheme dispatch port can reproduce the
   event-kboard write-back.  The nil→current_kboard fallback lives in
   Scheme (mod/emacs/kbd-buffer.scm dispatch-event!).  */)
  (Lisp_Object ie)
{
  CHECK_IE (ie);
  KBOARD *kb = event_to_kboard (XIE (ie));
  return kb ? make_kboard_smob (kb) : Qnil;
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

   The phase-by-phase logic now lives in Scheme in
   (emacs kbd-buffer) `kbd-buffer-store-event!' (mod/emacs/kbd-buffer.scm);
   this C entry keeps the extern signature so other C files can call
   it by name, keeps the single NO_EVENT guard, then dispatches (M13
   imp-3).  */

void
kbd_buffer_store_buffered_event (union buffered_input_event *event,
				 struct input_event *hold_quit)
{
  if (event->kind == NO_EVENT)
    emacs_abort ();

  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs kbd-buffer", "kbd-buffer-store-event!");

  SCM ie_smob = ie_wrap (&event->ie);
  SCM hold_quit_smob = hold_quit ? ie_wrap (hold_quit) : SCM_BOOL_F;
  SCM_CALL_2 (proc, ie_smob, hold_quit_smob);

  /* M9 ie-smob lifetime contract: invalidate right after the call.  */
  SCM_SET_SMOB_DATA (ie_smob, NULL);
  if (hold_quit)
    SCM_SET_SMOB_DATA (hold_quit_smob, NULL);
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

DEFUN ("--position-to-time", Fposition_to_time, Sposition_to_time,
       1, 1, 0,
       doc: /* Encode buffer position POS as a Time fixnum.

Wraps the C position_to_Time helper used by HELP_EVENT.  Range-checks
POS into INPUT_EVENT_POS_MIN/MAX first, since callers cross the FFI
boundary where eassert may be compiled out.  */)
  (Lisp_Object pos)
{
  CHECK_FIXNUM (pos);
  ptrdiff_t p = XFIXNUM (pos);
  if (p < INPUT_EVENT_POS_MIN || p > INPUT_EVENT_POS_MAX)
    args_out_of_range (pos, pos);
  return make_fixnum (position_to_Time (p));
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
  /* M16 imp-3 — C body replaced by a SCM_CALL_5 into the Scheme
     procedure in (emacs help-echo) gen-help-event.  */
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs help-echo", "gen-help-event");
  SCM_CALL_5 (proc, help, frame, window, object, INT_TO_INTEGER (pos));
}


/* Store HELP_EVENTs for HELP on FRAME in the input queue.  */

void
kbd_buffer_store_help_event (Lisp_Object frame, Lisp_Object help)
{
  /* M16 imp-3 — C body replaced by a SCM_CALL_2 into the Scheme
     procedure in (emacs help-echo) store-help-event.  */
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs help-echo", "store-help-event");
  SCM_CALL_2 (proc, frame, help);
}


/* Discard any mouse events in the event buffer by setting them to
   NO_EVENT.  */
void
discard_mouse_events (void)
{
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs kbd-buffer", "kbd-buffer-discard-mouse-events!");
  SCM_CALL_0 (proc);
}


/* Return true if there are any real events waiting in the event
   buffer, not counting `NO_EVENT's.

   Discard NO_EVENT events at the front of the input queue, possibly
   leaving the input queue empty if there are no real input events.  */

bool
kbd_buffer_events_waiting (void)
{
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs kbd-buffer", "kbd-buffer-events-waiting");
  return scm_is_true (SCM_CALL_0 (proc));
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
   We always read and discard one event.

   M11 imp-5 replaced the C body (wait loop, event-kind dispatch, and
   mouse-motion fallback) with a shim delegating to (emacs kbd-buffer);
   M12 imp-2 made the Scheme entry return (values event kboard
   used-mouse-menu) and served this shim through the temporary
   kbd-buffer-get-event-write-back adapter.  M12 imp-4 deleted the
   shim together with the adapter: (emacs main-queue) now calls
   kbd-buffer-get-event directly.  */

/* M12 imp-1 — C shim DEFUNs for the main-queue port.

   Expose the C-internal operations the (emacs main-queue) Scheme
   procedures need: the getctag prompt-tag globals, the single-kboard
   flag, the kboard side-queue tail-append, the end-time deadline
   check, and the tty keyboard-coding decode core.  Each is thin; the
   tty decode shim is the only non-trivial one.  Scheme gates every
   tty call behind --selected-frame-tty-p at runtime; the tty shims
   are #ifdef-gated internally to match the C
   decode loop.  See docs/m12-plan.org §imp-1.  */

/* imp-1.1 — single-kboard reflection.  The getctag save/set pair
   (--get-ctag, --set-ctag) moved to the cell table at M30 imp-5; see
   cell_table and mod/emacs/cell-accessors.scm.  */

DEFUN ("--kbd-single-kboard-p", Fc_kbd_single_kboard_p,
       Sc_kbd_single_kboard_p, 0, 0, 0,
       doc: /* Internal: t when the C static single_kboard flag is set.  */)
  (void)
{
  return single_kboard ? Qt : Qnil;
}

DEFUN ("--kbd-single-kboard-set!", Fc_kbd_single_kboard_set,
       Sc_kbd_single_kboard_set, 1, 1, 0,
       doc: /* FIX-20260907-guilemacs: Internal: hard-set the C static
`single_kboard' flag to (not V nil) and return nil.  Scheme needs a
setter for the flag (only the getter --kbd-single-kboard-p exists) to
drive not_single_kboard_state and temporarily-switch-to-single-kboard!
policy from (emacs single-kboard).  Mirrors --input-pending-set!.  */)
  (Lisp_Object v)
{
  single_kboard = !NILP (v);
  return Qnil;
}

DEFUN ("--kboard-live-p", Fc_kboard_live_p, Sc_kboard_live_p, 1, 1, 0,
       doc: /* FIX-20260907-guilemacs: Internal: return t when KB wraps
a KBOARD still present on some terminal in `terminal_list', nil
otherwise.  Keeps pop-kboard!'s raw `terminal_list' walk in C.  */)
  (Lisp_Object kb)
{
  struct terminal *t;
  CHECK_KBOARD (kb);
  for (t = terminal_list; t; t = t->next_terminal)
    if (t->kboard == XKBOARD (kb))
      return Qt;
  return Qnil;
}

DEFUN ("--selected-frame-kboard", Fc_selected_frame_kboard,
       Sc_selected_frame_kboard, 0, 0, 0,
       doc: /* FIX-20260907-guilemacs: Internal: return the KBOARD of
the selected frame as a kboard smob.  pop-kboard!'s fallback when the
remembered kboard's terminal has been deleted.  */)
  (void)
{
  return make_kboard_smob (FRAME_KBOARD (SELECTED_FRAME ()));
}

DEFUN ("--kbd-queue-has-data", Fc_kbd_queue_has_data,
       Sc_kbd_queue_has_data, 1, 1, 0,
       doc: /* Internal: t when KB's kbd_queue_has_data flag is set,
nil otherwise.  Getter companion to
--set-kboard-kbd-queue-has-data; no generic accessor covers this
plain C bitfield.  */)
  (Lisp_Object kb)
{
  CHECK_KBOARD (kb);
  return XKBOARD (kb)->kbd_queue_has_data ? Qt : Qnil;
}

DEFUN ("--any-kbd-queue-has-data", Fc_any_kbd_queue_has_data,
       Sc_any_kbd_queue_has_data, 0, 0, 0,
       doc: /* Internal: t when any KBOARD in all_kboards has its
kbd_queue_has_data flag set, nil otherwise.  readable_events' phase-6
non-single-kboard branch.  */)
  (void)
{
  for (KBOARD *kb = all_kboards; kb; kb = kb->next_kboard)
    if (kb->kbd_queue_has_data)
      return Qt;
  return Qnil;
}

/* imp-1.2 — kboard side-queue append.  Compound on purpose: the
   tail-walk + append + abort-check + flag must be atomic in C, so
   Scheme never set-cdr!s C-owned cons cells across the FFI.  */

DEFUN ("--kbd-enqueue-side-queue", Fc_kbd_enqueue_side_queue,
       Sc_kbd_enqueue_side_queue, 2, 2, 0,
       doc: /* Internal: append (list EVENT) to KB's kbd_queue side
queue and set KB's kbd_queue_has_data flag, exactly like the deleted
C main-queue routing block.  Aborts if the tail
invariant is broken.  Returns nil.  */)
  (Lisp_Object kb, Lisp_Object event)
{
  CHECK_KBOARD (kb);
  KBOARD *k = XKBOARD (kb);
  Lisp_Object last = KVAR (k, kbd_queue);
  if (CONSP (last))
    {
      while (CONSP (XCDR (last)))
	last = XCDR (last);
      if (!NILP (XCDR (last)))
	emacs_abort ();
    }
  if (!CONSP (last))
    kset_kbd_queue (k, list1 (event));
  else
    XSETCDR (last, list1 (event));
  k->kbd_queue_has_data = true;
  return Qnil;
}

/* imp-1 (M13) — store-side port shims.  One block keeps every M13
   imp-1 addition in one place for review.  */

DEFUN ("--set-kboard-kbd-queue-has-data",
       Fc_set_kboard_kbd_queue_has_data,
       Sc_set_kboard_kbd_queue_has_data, 2, 2, 0,
       doc: /* Internal: set KB's kbd_queue_has_data flag to (not VAL
   nil) and return VAL.  The flag is a plain C bitfield, not a
   Lisp_Object, so KBOARD_LISP_FIELD cannot cover it — this setter is
   the only way Scheme can drive it.  No getter DEFUN exists; tests
   read the flag back via --rc-pop-current-kboard-queue.  */)
  (Lisp_Object kb, Lisp_Object val)
{
  CHECK_KBOARD (kb);
  XKBOARD (kb)->kbd_queue_has_data = !NILP (val);
  return val;
}

DEFUN ("--stop-character", Fc_stop_character_, Sc_stop_character_, 0, 0, 0,
       doc: /* Internal: return the current C stop_character as a fixnum.

Reads the C global stop_character back at call time — do not assume a
specific value in callers.  */)
  (void)
{
  return make_fixnum (stop_character);
}

DEFUN ("--sys-suspend", Fc_sys_suspend_, Sc_sys_suspend_, 0, 0, 0,
       doc: /* Internal: suspend the whole process via sys_suspend ().

Real SIGTSTP-class suspend — only smoke-tested, never exercised in the
test suite (it would stop the runner).  */)
  (void)
{
  sys_suspend ();
  return Qnil;
}

DEFUN ("--handle-interrupt-normal", Fc_handle_interrupt_normal,
       Sc_handle_interrupt_normal, 0, 0, 0,
       doc: /* Internal: run a C-g interrupt from a normal (non-signal)
context, handle_interrupt (false).  The live dispatch from
kbd-buffer.scm's quit-char branch (see brief.org M26).  Arm 1 (the
emergency-escape prompt) stays in C on both the signal and this normal
path; the arm-2 + tail force-quit body of this normal path is forwarded
to (emacs interrupt) handle-interrupt.  Returns nil.  */)
  (void)
{
  handle_interrupt (false);
  return Qnil;
}

/* M15 imp-1 — timer firing core shims.  Each shim wraps one piece of
   the C timer firing core for Scheme, leaving every C function body
   unchanged.  decode_timer is static and defined later in this file,
   so declare it up front; its slot 0/1/2/3/8 checks run verbatim
   inside the shims.  The three-way {invalid | {0,0} | wait} return
   contract survives the FFI as {nil | t | (SEC . NSEC)} — the same
   encoding every M15 shim and the imp-2 Scheme body share (see
   docs/m15-plan.org risk 3).  */

static struct timespec decode_timer (Lisp_Object);

DEFUN ("--timer-get-pending-funcalls-drain!",
       Fc_timer_get_pending_funcalls_drain,
       Sc_timer_get_pending_funcalls_drain, 0, 0, 0,
       doc: /* Internal: pop and run every entry in C's
pending_funcalls, one at a time, via safe_calln (Qapply, ...) — the
same delayed-funcall drain the timer firing core runs at its
top.  Returns nil.  */)
  (void)
{
  while (CONSP (pending_funcalls))
    {
      Lisp_Object funcall = XCAR (pending_funcalls);
      pending_funcalls = XCDR (pending_funcalls);
      safe_calln (Qapply, XCAR (funcall), XCDR (funcall));
    }
  return Qnil;
}

/* M15 imp-1 — test-support accessors for pending_funcalls.  These two
   are NOT part of the 5-shim set (brief.org) and carry no production
   logic: the C writers in frame.c/terminal.c are the only live writers
   during a real run.  The brief's drain test spec ("write one entry to
   pending_funcalls, call the drain shim, confirm it runs once and the
   queue is empty") cannot be met from Scheme otherwise — no existing
   shim touches the cell.  get/set let the corpus seed and then read
   back the queue.  */

DEFUN ("--timer-pending-funcalls",
       Fc_timer_pending_funcalls,
       Sc_timer_pending_funcalls, 0, 0, 0,
       doc: /* Internal (test support): return C's pending_funcalls as
a list of (FUN . ARGS) entries.  */)
  (void)
{
  return pending_funcalls;
}

DEFUN ("--timer-pending-funcalls-set!",
       Fc_timer_pending_funcalls_set,
       Sc_timer_pending_funcalls_set, 1, 1, 0,
       doc: /* Internal (test support): replace C's pending_funcalls
with LIST of (FUN . ARGS) entries.  Lets the drain test seed the queue
that --timer-get-pending-funcalls-drain! consumes.
Returns nil.  */)
  (Lisp_Object list)
{
  pending_funcalls = list;
  return Qnil;
}

DEFUN ("--timer-fire-ripe", Fc_timer_fire_ripe, Sc_timer_fire_ripe, 1, 1, 0,
       doc: /* Internal: run the ripe-timer fire sequence for TIMER as
one compound, in the exact C fire order: mark slot 0 = t
first, bind inhibit-quit to t, call the timer handler once, restore
Vdeactivate-mark, then bump timers_run.  Returns nil.  */)
  (Lisp_Object timer)
{
  dynwind_begin ();
  Lisp_Object old_deactivate_mark = Vdeactivate_mark;
  ASET (timer, 0, Qt);
  specbind_guile (Qinhibit_quit, Qt);
  call1 (Qtimer_event_handler, timer);
  Vdeactivate_mark = old_deactivate_mark;
  timers_run++;
  dynwind_end ();
  return Qnil;
}

DEFUN ("--timer-copy-window", Fc_timer_copy_window, Sc_timer_copy_window,
       0, 0, 0,
       doc: /* Internal: snapshot both timer lists in one atomic window
against atimer callbacks, exactly as timer_check does: save and set
inhibit-quit to t, block input, turn atimers off, copy Vtimer-list and
Vtimer-idle-list, turn atimers back on, unblock input, then restore
inhibit-quit.  Returns the two copies as a pair (TIMERS . IDLE-TIMERS);
the idle copy is nil when Emacs is not idle.  */)
  (void)
{
  Lisp_Object tem = Vinhibit_quit;
  Vinhibit_quit = Qt;
  block_input ();
  turn_on_atimers (false);
  Lisp_Object timers = Fcopy_sequence (Vtimer_list);
  Lisp_Object idle_timers
    = (timespec_valid_p (timer_idleness_start_time)
       ? Fcopy_sequence (Vtimer_idle_list)
       : Qnil);
  turn_on_atimers (true);
  unblock_input ();
  Vinhibit_quit = tem;
  return Fcons (timers, idle_timers);
}

DEFUN ("--timespec-diff-to-now", Fc_timespec_diff_to_now,
       Sc_timespec_diff_to_now, 1, 1, 0,
       doc: /* Internal: return timespec_sub (current_timespec (),
decode_timer (TIMER)) as (SEC . NSEC).  Negative when TIMER's fire time
is still in the future; positive when it is overdue.  decode_timer's
slot 0/1/2/3/8 checks run verbatim.  */)
  (Lisp_Object timer)
{
  struct timespec diff = timespec_sub (current_timespec (),
				       decode_timer (timer));
  return Fcons (make_fixnum (diff.tv_sec), make_fixnum (diff.tv_nsec));
}

/* M15 imp-2 — addendum to the imp-1 shim set (brief.org Gap 1).  The
   idle branch of the Scheme timer-check-2 and the current-idle-time DEFUN both
   need the *elapsed idle* duration (current_timespec() minus
   timer_idleness_start_time), which no imp-1 shim exposed.  One small
   getter gives both call sites a single clock read and a single
   implementation.  */

DEFUN ("--timer-idleness-now", Fc_timer_idleness_now,
       Sc_timer_idleness_now, 0, 0, 0,
       doc: /* Internal: return the current elapsed idle duration, or
nil if Emacs is not idle.

"Elapsed idle" is timespec_sub (current_timespec (),
timer_idleness_start_time) — the same "idleness now" value the timer
firing core derives for its idle-timer branch and current-idle-time
returns.  Returns (SEC . NSEC); nil when timer_idleness_start_time is
invalid (not idle).  M15 imp-2 addendum to the imp-1 shim set.  */)
  (void)
{
  if (timespec_valid_p (timer_idleness_start_time))
    {
      struct timespec idle
        = timespec_sub (current_timespec (), timer_idleness_start_time);
      return Fcons (make_fixnum (idle.tv_sec), make_fixnum (idle.tv_nsec));
    }
  return Qnil;
}

/* imp-1.3 — rec-free end-time deadline check.  */

DEFUN ("--timespec-expired-p", Fc_timespec_expired_p,
       Sc_timespec_expired_p, 1, 1, 0,
       doc: /* Internal: t when PTR is a non-nil foreign pointer to a
timespec whose deadline is <= current_timespec (); nil otherwise
(including a nil PTR).  Rec-free companion to --rc-end-time-expired-p:
the Scheme main-queue procedures pass the end-time pointer explicitly
so they stay testable without an rc-record on the stack.  */)
  (Lisp_Object ptr)
{
  if (NILP (ptr))
    return Qnil;
  struct timespec *end_time = scm_to_pointer (ptr);
  return (timespec_cmp (*end_time, current_timespec ()) <= 0) ? Qt : Qnil;
}

/* imp-1.4 — tty keyboard-coding decode shims.  Scheme gates every call
   behind --selected-frame-tty-p at runtime (see Risk 4: these shims
   deref FRAME_TTY unguarded).  MAX_ENCODED_BYTES (16) is a file-scope
   #define above the decode loop.  */

DEFUN ("--tty-keyboard-coding-requires-decoding-p",
       Fc_tty_keyboard_coding_requires_decoding_p,
       Sc_tty_keyboard_coding_requires_decoding_p, 0, 0, 0,
       doc: /* Internal: t when the selected frame's terminal keyboard
coding has CODING_REQUIRE_DECODING_MASK set.  Caller must verify
--selected-frame-tty-p first.  */)
  (void)
{
  struct frame *frame = XFRAME (selected_frame);
  struct terminal *terminal = frame->terminal;
  return (TERMINAL_KEYBOARD_CODING (terminal)->common_flags
	  & CODING_REQUIRE_DECODING_MASK) ? Qt : Qnil;
}

DEFUN ("--tty-keyboard-coding-raw-text-p",
       Fc_tty_keyboard_coding_raw_text_p,
       Sc_tty_keyboard_coding_raw_text_p, 0, 0, 0,
       doc: /* Internal: t when the selected frame's terminal keyboard
coding is a raw-text coding system.  Caller must verify
--selected-frame-tty-p first.  */)
  (void)
{
  struct frame *frame = XFRAME (selected_frame);
  struct terminal *terminal = frame->terminal;
  return raw_text_coding_system_p (TERMINAL_KEYBOARD_CODING (terminal))
    ? Qt : Qnil;
}

DEFUN ("--tty-decode-keyboard-bytes", Fc_tty_decode_keyboard_bytes,
       Sc_tty_decode_keyboard_bytes, 1, 1, 0,
       doc: /* Internal: decode BYTE-VECTOR through the selected
frame's terminal keyboard coding and return the decoded characters as
a list of fixnums, or nil when the sequence is incomplete
(produced_char == 0).  The raw-text high-bit strip stays in Scheme;
Scheme tracks n and treats nil as continue (n < MAX_ENCODED_BYTES) or
flush (n == MAX_ENCODED_BYTES).  Caller must verify
--selected-frame-tty-p first.  */)
  (Lisp_Object bytevector)
{
  if (!scm_is_bytevector (bytevector))
    return Qnil;
  ptrdiff_t n = scm_c_bytevector_length (bytevector);
  const unsigned char *bytes
    = (const unsigned char *) SCM_BYTEVECTOR_CONTENTS (bytevector);
  if (n <= 0 || n > MAX_ENCODED_BYTES)
    return Qnil;

  struct frame *frame = XFRAME (selected_frame);
  struct terminal *terminal = frame->terminal;
  struct coding_system *coding = TERMINAL_KEYBOARD_CODING (terminal);
  int meta_key = FRAME_TTY (frame)->meta_key;

  unsigned char src[MAX_ENCODED_BYTES];
  unsigned char dest[MAX_ENCODED_BYTES * MAX_MULTIBYTE_LENGTH];
  int i;
  for (i = 0; i < n; i++)
    src[i] = bytes[i];
  if (meta_key < 2)		/* input-meta-mode is t or nil */
    for (i = 0; i < n; i++)
      src[i] &= ~0x80;
  coding->destination = dest;
  coding->dst_bytes = sizeof dest;
  decode_coding_c_string (coding, src, n, Qnil);
  eassert (coding->produced_char <= n);
  if (coding->produced_char == 0)
    return Qnil;		/* incomplete sequence */

  const unsigned char *p = coding->destination;
  eassert (coding->carryover_bytes == 0);
  Lisp_Object result = Qnil;
  int produced = coding->produced_char;
  for (i = 0; i < produced; i++)
    {
      int c = string_char_advance (&p);
      if (meta_key == 3)
	{
	  int modifier = (c < 0x100 && (c & 0x80) ? meta_modifier : 0);
	  c = (c & ~0x80) | modifier;
	}
      result = Fcons (make_fixnum (c), result);
    }
  return Fnreverse (result);
}

/* Process any non-user-visible events (currently X selection events),
   without reading any user-visible events.  */

/* M11 imp-1.3 — C-escape shims for the kbd_buffer_get_event port.
   Thin wrappers over non-portable / non-Scheme-callable C functions;
   no behaviour change.  Platform gating lives inside each DEFUN body
   (#ifdef discipline); Scheme calls these blind, without featurep
   guards.  See docs/m11-plan.org §imp-1.3.  */

DEFUN ("--quit-throw-to-read-char",
       Fc_quit_throw_to_read_char,
       Sc_quit_throw_to_read_char, 0, 0, 0,
       doc: /* Internal: throw to the read-char wait point, exactly as
   the C wait loop does when Vquit_flag is set
   (quit_throw_to_read_char (0)).  Never returns — longjmps to the
   waiting read-char; the caller must treat this as a non-local exit.  */)
  (void)
{
  quit_throw_to_read_char (0);
  return Qnil;   /* Not reached.  */
}

DEFUN ("--kbd-abort", Fkbd_abort, Skbd_abort, 0, 0, 0,
       doc: /* Internal: abort exactly as the C kbd_buffer_get_event
   shared `else' does when the event queue is empty yet no frame has
   pending mouse movement (emacs_abort ()).  This "impossible"
   invariant dumps core in C; imp-4 calls it from Scheme for the same
   fatal semantics.  Never returns.  */)
  (void)
{
  emacs_abort ();
  return Qnil;   /* Not reached.  */
}

DEFUN ("--wait-reading-process-output",
       Fc_wait_reading_process_output,
       Sc_wait_reading_process_output, 4, 4, 0,
       doc: /* Internal: call C wait_reading_process_output (SEC, NSEC,
   READ_KBD, DO_DISPLAY, nil, NULL, 0).  SEC is clamped to
   WAIT_READING_MAX (20 s) inside, mirroring the kbd_buffer_get_event
   wait-loop call sites exactly.  Returns nil; the caller re-checks
   the event queues after the sleep.  */)
  (Lisp_Object sec, Lisp_Object nsec, Lisp_Object read_kbd,
   Lisp_Object do_display)
{
  CHECK_FIXNUM (sec);
  CHECK_FIXNUM (nsec);
  CHECK_FIXNUM (read_kbd);
  wait_reading_process_output (min (XFIXNUM (sec), WAIT_READING_MAX),
			       XFIXNUM (nsec),
			       XFIXNUM (read_kbd),
			       !NILP (do_display),
			       Qnil, NULL, 0);
  return Qnil;
}

DEFUN ("--frame-focus-frame", Fc_frame_focus_frame, Sc_frame_focus_frame, 1, 1, 0,
       doc: /* Internal: return the focus-frame of FRAME, or nil.

Wraps FRAME_FOCUS_FRAME (f->focus_frame).  Returns nil when FRAME is
not a frame, so the imp-3 switch-frame synthesis can pass event
frame_or_window values through without XFRAME aborts.  */)
  (Lisp_Object frame)
{
  if (!FRAMEP (frame))
    return Qnil;
  return FRAME_FOCUS_FRAME (XFRAME (frame));
}

DEFUN ("--frame-last-mouse-device", Fc_frame_last_mouse_device,
       Sc_frame_last_mouse_device, 1, 1, 0,
       doc: /* Internal: return FRAME's last_mouse_device — the string
   name of the last input device to move over FRAME, or nil/other when
   it is the virtual core pointer.  Returns nil when FRAME is not a
   frame.  Used by imp-4 device tracking (compare against Scheme
   (emacs kbd-buffer) VIRTUAL-CORE-POINTER-NAME).  */)
  (Lisp_Object frame)
{
  if (!FRAMEP (frame))
    return Qnil;
  return XFRAME (frame)->last_mouse_device;
}

DEFUN ("--activate-menubar-hook",
       Fc_activate_menubar_hook,
       Sc_activate_menubar_hook, 1, 1, 0,
       doc: /* Internal: call the FRAME terminal's activate_menubar_hook
   with FRAME.  Returns nil; also nil (no-op) when FRAME is not a frame
   or when the terminal has no such hook (e.g. termcap builds).  Scheme
   checks FRAME_LIVE_P before calling.  */)
  (Lisp_Object frame)
{
  if (!FRAMEP (frame))
    return Qnil;
#ifdef HAVE_EXT_MENU_BAR
  struct frame *f = XFRAME (frame);
  if (FRAME_TERMINAL (f)->activate_menubar_hook)
    FRAME_TERMINAL (f)->activate_menubar_hook (f);
#endif
  return Qnil;
}

DEFUN ("--kbd-decode-multibyte-string",
       Fc_kbd_decode_multibyte_string,
       Sc_kbd_decode_multibyte_string, 1, 1, 0,
       doc: /* Internal: run STR through the C multibyte-decode path
   (internal_condition_case_1 (kbd_buffer_get_event_1, STR, Qt,
   kbd_buffer_get_event_2)).  Returns the raw result — nil (use the
   original string), an empty string (drop the event), or the decoded
   string.  Signals `wrong-type-argument' on a non-string STR.  */)
  (Lisp_Object str)
{
  CHECK_STRING (str);
  return internal_condition_case_1 (kbd_buffer_get_event_1, str, Qt,
				    kbd_buffer_get_event_2);
}

DEFUN ("--kbd-noninteractive-getchar",
       Fc_kbd_noninteractive_getchar,
       Sc_kbd_noninteractive_getchar, 0, 0, 0,
       doc: /* Internal: batch fast path — read one raw char from stdin
   (getchar ()) and return it as a fixnum; EOF returns -1, exactly like
   the C kbd_buffer_get_event noninteractive branch.  Returns nil on
   builds compiled with DBus / file-notify / threads (no fast path);
   Scheme gates the call on noninteractive / daemon predicates.  */)
  (void)
{
#if !defined (HAVE_DBUS) && !defined (USE_FILE_NOTIFY) && !defined (THREADS_ENABLED)
  return make_fixnum (getchar ());
#else
  return Qnil;
#endif
}

DEFUN ("--mouse-position-hook",
       Fc_mouse_position_hook,
       Sc_mouse_position_hook, 1, 1, 0,
       doc: /* Internal: call the FRAME terminal's mouse_position_hook
   and return (F BAR-WINDOW PART X Y TIME) — PART and TIME as fixnums,
   F the (possibly updated) frame under the pointer (the hook takes
   &f and may rewrite it — XTmouse_position sets *fp to the frame
   actually under the pointer, or NULL when the pointer is outside all
   frames during a drag).  Returns nil when FRAME is not a frame or
   the terminal has no such hook (termcap builds).  Used by imp-4
   mouse-motion synthesis.  */)
  (Lisp_Object frame)
{
  if (!FRAMEP (frame))
    return Qnil;
  struct frame *f = XFRAME (frame);
  Lisp_Object bar_window;
  enum scroll_bar_part part;
  Lisp_Object x, y;
  Time t;
  if (!FRAME_TERMINAL (f)->mouse_position_hook)
    return Qnil;
  (*FRAME_TERMINAL (f)->mouse_position_hook) (&f, 0, &bar_window, &part,
					      &x, &y, &t);
  return listn (6,
		f ? make_lisp_ptr (f, Lisp_Vectorlike) : Qnil,
		bar_window, make_fixnum (part), x, y, make_fixnum (t));
}

DEFUN ("--toolkit-scroll-bars-p", Fc_toolkit_scroll_bars_p,
       Sc_toolkit_scroll_bars_p, 0, 0, 0,
       doc: /* Internal: t when built with USE_TOOLKIT_SCROLL_BARS,
nil otherwise.  Feature predicate for readable_events' squeezable
filter (mirrors --detect-conversion-events' nil-when-absent
convention).  */)
  (void)
{
#ifdef USE_TOOLKIT_SCROLL_BARS
  return Qt;
#else
  return Qnil;
#endif
}

DEFUN ("--detect-conversion-events",
       Fc_detect_conversion_events,
       Sc_detect_conversion_events, 0, 0, 0,
       doc: /* Internal: t when text-conversion events are pending
   (detect_conversion_events ()), nil otherwise; nil on builds without
   HAVE_TEXT_CONVERSION.  */)
  (void)
{
#ifdef HAVE_TEXT_CONVERSION
  return detect_conversion_events () ? Qt : Qnil;
#else
  return Qnil;
#endif
}

DEFUN ("--handle-pending-conversion-events",
       Fc_handle_pending_conversion_events,
       Sc_handle_pending_conversion_events, 0, 0, 0,
       doc: /* Internal: process pending text-conversion events
   (handle_pending_conversion_events ()).  Returns nil; no-op on
   builds without HAVE_TEXT_CONVERSION.  */)
  (void)
{
#ifdef HAVE_TEXT_CONVERSION
  handle_pending_conversion_events ();
#endif
  return Qnil;
}

DEFUN ("--conversion-disabled-p",
       Fc_conversion_disabled_p,
       Sc_conversion_disabled_p, 0, 0, 0,
       doc: /* Internal: t when text conversion is disabled
   (conversion_disabled_p ()), nil otherwise; nil on builds without
   HAVE_TEXT_CONVERSION.  */)
  (void)
{
#ifdef HAVE_TEXT_CONVERSION
  return conversion_disabled_p () ? Qt : Qnil;
#else
  return Qnil;
#endif
}

DEFUN ("--unhold-keyboard-input",
       Fc_unhold_keyboard_input,
       Sc_unhold_keyboard_input, 0, 0, 0,
       doc: /* Internal: resume accepting keyboard input after it was
   held (unhold_keyboard_input ()).  Returns nil; no-op on builds
   without subprocesses.  */)
  (void)
{
#ifdef subprocesses
  unhold_keyboard_input ();
#endif
  return Qnil;
}

DEFUN ("--kbd-on-hold-p",
       Fc_kbd_on_hold_p,
       Sc_kbd_on_hold_p, 0, 0, 0,
       doc: /* Internal: t when keyboard input is currently held
   (kbd_on_hold_p ()), nil otherwise; nil on builds without
   subprocesses.  imp-2a unholds when the queue drains below a quarter
   of KBD_BUFFER_SIZE.  */)
  (void)
{
#ifdef subprocesses
  return kbd_on_hold_p () ? Qt : Qnil;
#else
  return Qnil;
#endif
}

DEFUN ("--kbd-maybe-hold-keyboard-input",
       Fc_kbd_maybe_hold_keyboard_input,
       Sc_kbd_maybe_hold_keyboard_input, 0, 0, 0,
       doc: /* Internal: hold keyboard input when the ring is more
   than half full and not already held (hold_keyboard_input ()).
   Returns nil; no-op on builds without subprocesses.  Called by the
   M13 store-side port when the queue backs up.  */)
  (void)
{
#ifdef subprocesses
  if (kbd_buffer_nr_stored () > KBD_BUFFER_SIZE / 2 && !kbd_on_hold_p ())
    hold_keyboard_input ();
#endif
  return Qnil;
}

DEFUN ("--x-detect-pending-selection-requests",
       Fc_x_detect_pending_selection_requests,
       Sc_x_detect_pending_selection_requests, 0, 0, 0,
       doc: /* Internal: t when X selection requests are pending
   (x_detect_pending_selection_requests ()), nil otherwise; nil on
   builds without HAVE_X_WINDOWS.  Called by the Scheme wait loop.  */)
  (void)
{
#ifdef HAVE_X_WINDOWS
  return x_detect_pending_selection_requests () ? Qt : Qnil;
#else
  return Qnil;
#endif
}

DEFUN ("--x-handle-pending-selection-requests",
       Fc_x_handle_pending_selection_requests,
       Sc_x_handle_pending_selection_requests, 0, 0, 0,
       doc: /* Internal: process pending X selection requests
   (x_handle_pending_selection_requests ()).  Returns nil; no-op on
   builds without HAVE_X_WINDOWS.  Called by the Scheme wait loop
   post-wait when --x-detect-pending-selection-requests was true.  */)
  (void)
{
#ifdef HAVE_X_WINDOWS
  x_handle_pending_selection_requests ();
#endif
  return Qnil;
}

DEFUN ("--gobble-input",
       Fc_gobble_input,
       Sc_gobble_input, 0, 0, 0,
       doc: /* Internal: call gobble_input () and return the number of
   events read as a fixnum (-1 when input is blocked).  Scheme calls it
   for side effect only — the wait loop ignores the value.  */)
  (void)
{
  return make_fixnum (gobble_input ());
}

/* M11 imp-2 — additions beyond the imp-1.3 inventory (recorded in
   docs/m11-plan.org §imp-2): the timed-branch deadline helper, the
   untimed-branch tty-menu display gate, the imp-1.4 queue-stuffing
   helper pulled forward, and the test-only end-time storage pointers.  */

DEFUN ("--rc-end-time-remaining",
       Fc_rc_end_time_remaining,
       Sc_rc_end_time_remaining, 0, 0, 0,
       doc: /* Internal: return (SEC . NSEC), the fixnum seconds and
   nanoseconds remaining until the top-of-stack rec's end-time deadline
   (timespec_sub (*END_TIME, current_timespec ())).  Returns nil when
   no rec is current, its end-time slot is nil, or the deadline has
   already passed.  The caller checks --rc-end-time-expired-p first, so
   SEC > 0 here; the WAIT_READING_MAX clamp lives inside
   --wait-reading-process-output (Scheme passes raw seconds).  */)
  (void)
{
  if (rc_state_depth == 0)
    return Qnil;
  SCM rec = rc_record_stack[rc_state_depth - 1];
  struct timespec *end_time = rc_unwrap_ptr (rec, RC_SLOT_END_TIME);
  if (!end_time)
    return Qnil;
  struct timespec now = current_timespec ();
  if (timespec_cmp (*end_time, now) <= 0)
    return Qnil;
  struct timespec duration = timespec_sub (*end_time, now);
  return Fcons (make_fixnum (duration.tv_sec), make_fixnum (duration.tv_nsec));
}

DEFUN ("--kbd-wait-do-display-p",
       Fc_kbd_wait_do_display_p,
       Sc_kbd_wait_do_display_p, 0, 0, 0,
       doc: /* Internal: t when the wait loop may redisplay while
   waiting for input (the DO_DISPLAY argument of
   --wait-reading-process-output in kbd_buffer_get_event's untimed
   branch).  Returns nil only when the selected frame is a termcap
   frame whose TTY is showing a menu — the exact C condition
   !(FRAME_TERMCAP_P (SELECTED_FRAME ()) && CURTTY ()->showing_menu).
   Non-termcap builds always return t.  */)
  (void)
{
  return (FRAME_TERMCAP_P (SELECTED_FRAME ()) && CURTTY ()->showing_menu)
    ? Qnil : Qt;
}

DEFUN ("--kbd-buffer-store-fake-event",
       Fc_kbd_buffer_store_fake_event,
       Sc_kbd_buffer_store_fake_event, 1, 2, 0,
       doc: /* Internal test helper: store a synthetic event of KIND at
   kbd_store_ptr, bypassing kbd_buffer_store_event's signal path (no
   SIGIO handlers, no hold/quit special-casing).  KIND is a fixnum
   event_kind (see enum event_kind in src/termhooks.h); optional ARG is
   stored in the event's arg field (default nil).  code/modifiers/
   part/x/y/timestamp are zeroed; frame_or_window defaults to the
   selected frame; device to Qt.  Returns nil, or nil with no store
   when the buffer is full (the last slot is never filled).  Only for
   imp-2/imp-6 queue-exit and round-trip tests — not production API.  */)
  (Lisp_Object kind, Lisp_Object arg)
{
  CHECK_FIXNUM (kind);
  union buffered_input_event *next_slot = next_kbd_event (kbd_store_ptr);
  if (kbd_fetch_ptr == next_slot)
    return Qnil;              /* buffer full — discard, like C.  */
  union buffered_input_event ev;
  memset (&ev, 0, sizeof ev);
  ev.ie.kind = (enum event_kind) XFIXNUM (kind);
  ev.ie.frame_or_window = selected_frame;
  ev.ie.arg = NILP (arg) ? Qnil : arg;
  ev.ie.device = Qt;
  *kbd_store_ptr = ev;
  kbd_store_ptr = next_slot;
  return Qnil;
}

/* M11 imp-2 — test-only end-time storage pointers for the timed
   branch.  Mirrors the deleted M11 imp-1.3 --rc-test-kbp-storage-ptr
   pattern (see the M12 imp-4 diff): a static timespec whose address is
   handed to Scheme as a foreign pointer to store in an rc-record's
   RC_SLOT_END_TIME slot.  The expired one is initialised to the epoch
   (always <= now), so the wait loop's "expired → return nil, no
   sleep" arm is testable without blocking; the far-future one (year
   ~2038) exercises the (SEC . NSEC) shape without tripping the
   expired arm.  */

static struct timespec rc_test_expired_end_time = { 0, 0 };
static struct timespec rc_test_far_future_end_time = { (time_t) 0x7fffffff, 0 };

DEFUN ("--rc-test-expired-end-time-ptr",
       Fc_rc_test_expired_end_time_ptr,
       Sc_rc_test_expired_end_time_ptr, 0, 0, 0,
       doc: /* Internal test helper: return a foreign pointer to a
   static timespec initialised to {0, 0} (the epoch — always already
   expired), for storing in an rc-record's end-time slot to exercise
   the timed wait-loop branch's expired arm without sleeping.  */)
  (void)
{
  return rc_wrap_ptr (&rc_test_expired_end_time);
}

DEFUN ("--rc-test-far-future-end-time-ptr",
       Fc_rc_test_far_future_end_time_ptr,
       Sc_rc_test_far_future_end_time_ptr, 0, 0, 0,
       doc: /* Internal test helper: return a foreign pointer to a
   static timespec in the far future (tv_sec = INT32_MAX), for
   storing in an rc-record's end-time slot to check the
   --rc-end-time-remaining (SEC . NSEC) shape.  Do NOT call
   kbd-buffer-get-event with this pointer — the untimed-wait would
   sleep until year 2038.  */)
  (void)
{
  return rc_wrap_ptr (&rc_test_far_future_end_time);
}

/* M13 imp-1 — test-only synthetic event constructors.  Fill style
   mirrors --kbd-buffer-store-fake-event: memset the whole struct to
   zero first, set the named fields explicitly, leave x/y zeroed.  */

static struct input_event ie_test_event_storage;
static struct input_event ie_test_hold_quit_storage;

DEFUN ("--ie-test-event", Fie_test_event, Sie_test_event, 4, 4, 0,
       doc: /* Internal test helper: fill a static struct input_event
   and return an ie-smob wrapping it.  KIND, CODE, MODIFIERS, and
   FRAME-OR-WINDOW are stored as given; arg is set to nil, device to
   Qt, and x/y are left zeroed (like --kbd-buffer-store-fake-event).
   Only for M13 imp-2/imp-4 tests — not production API.  */)
  (Lisp_Object kind, Lisp_Object code, Lisp_Object modifiers,
   Lisp_Object frame_or_window)
{
  CHECK_FIXNUM (kind);
  CHECK_FIXNUM (code);
  CHECK_FIXNUM (modifiers);
  memset (&ie_test_event_storage, 0, sizeof ie_test_event_storage);
  ie_test_event_storage.kind = (enum event_kind) XFIXNUM (kind);
  ie_test_event_storage.code = XFIXNUM (code);
  ie_test_event_storage.modifiers = XFIXNUM (modifiers);
  ie_test_event_storage.frame_or_window = frame_or_window;
  ie_test_event_storage.arg = Qnil;
  ie_test_event_storage.device = Qt;
  return ie_wrap (&ie_test_event_storage);
}

static struct input_event ie_help_event_storage;

DEFUN ("--ie-help-event", Fie_help_event, Sie_help_event, 5, 5, 0,
       doc: /* Internal: build a HELP_EVENT input_event and return an
ie-smob wrapping it.  FRAME-OR-WINDOW, ARG, X, Y, TIMESTAMP fill the
matching fields; kind is always HELP_EVENT.  X is passed as already
resolved by the caller (Scheme decides window-vs-frame, see
gen-help-event) — this shim does no branching, only field fill.
Caller must pass the returned smob to kbd-buffer-store-event! in the
same call, per the M9 ie-smob lifetime rule.  */)
  (Lisp_Object frame_or_window, Lisp_Object arg, Lisp_Object x,
   Lisp_Object y, Lisp_Object timestamp)
{
  memset (&ie_help_event_storage, 0, sizeof ie_help_event_storage);
  ie_help_event_storage.kind = HELP_EVENT;
  ie_help_event_storage.frame_or_window = frame_or_window;
  ie_help_event_storage.arg = arg;
  ie_help_event_storage.x = x;
  ie_help_event_storage.y = y;
  ie_help_event_storage.timestamp = scm_to_intmax (timestamp);
  ie_help_event_storage.device = Qt;
  return ie_wrap (&ie_help_event_storage);
}

DEFUN ("--ie-test-hold-quit", Fie_test_hold_quit, Sie_test_hold_quit, 0, 0, 0,
       doc: /* Internal test helper: reset the static hold_quit
   struct and return an ie-smob wrapping it.  Every call resets kind
   to NO_EVENT first, then frame_or_window and arg to nil and device
   to Qt — imp-2's already-holding guard and imp-4's tests both depend
   on a fresh hold_quit starting at NO_EVENT.  Only for M13 imp-2/imp-4
   tests — not production API.  */)
  (void)
{
  memset (&ie_test_hold_quit_storage, 0, sizeof ie_test_hold_quit_storage);
  ie_test_hold_quit_storage.kind = NO_EVENT;
  ie_test_hold_quit_storage.frame_or_window = Qnil;
  ie_test_hold_quit_storage.arg = Qnil;
  ie_test_hold_quit_storage.device = Qt;
  return ie_wrap (&ie_test_hold_quit_storage);
}

DEFUN ("--kbd-store-buffered-event", Fkbd_store_buffered_event,
       Skbd_store_buffered_event, 2, 2, 0,
       doc: /* Internal test helper: call the real C
   kbd_buffer_store_buffered_event with IE (an ie-smob) and HOLD-QUIT
   (an ie-smob, or nil for NULL).  M13 imp-3 round-trip: exercises the
   dispatcher wiring (C guard + ie_wrap + SCM_CALL_2) through the real
   entry point, not just kbd-buffer-store-event! directly.  Only for
   M13 imp-3 tests — not production API.  */)
  (Lisp_Object ie, Lisp_Object hold_quit)
{
  struct input_event *ev = ie_unwrap (ie);
  struct input_event *hq = NILP (hold_quit) ? NULL : ie_unwrap (hold_quit);
  kbd_buffer_store_buffered_event ((union buffered_input_event *) ev, hq);
  return Qnil;
}

static void
process_special_events (void)
{
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs kbd-buffer", "kbd-buffer-process-special-events!");
  SCM_CALL_0 (proc);
}

/* Process any events that are not user-visible, run timer events that
   are ripe, and return, without reading any user-visible events.  */

void
swallow_events (bool do_display)
{
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs kbd-buffer", "kbd-buffer-swallow-events!");
  SCM_CALL_1 (proc, do_display ? Qt : Qnil);
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

   Returns the time to wait until the next timer fires.
   If no timer is active, return an invalid value.

   As long as any timer is ripe, we run it.  */

struct timespec
timer_check (void)
{
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs timers", "timer-check");
  SCM result = SCM_CALL_0 (proc);
  if (NILP (result))
    return invalid_timespec ();
  return make_timespec (XFIXNUM (XCAR (result)), XFIXNUM (XCDR (result)));
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
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs timers", "current-idle-time");
  return SCM_CALL_0 (proc);
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

#define FUNCTION_KEY_OFFSET 0xff00

/* You'll notice that this table is arranged to be conveniently
   indexed by X Windows keysym values.  */
#if !defined HAVE_WINDOW_SYSTEM
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

/* M30 imp-1: table-driven cell accessors.  The C cell stays C, so the
   signal-context reads and writes stay safe.  Scheme reaches a cell
   through --cell-ref and --cell-set!; the kind picks the convert step.
   imp-1 proves the table and keeps every per-cell DEFUN.  imp-2 to
   imp-4 delete the wrappers.

   M30 imp-2 converts the plain bool cells.  `waiting_for_input' is a
   per-thread field (`current_thread->m_waiting_for_input', see
   src/thread.h), so its address is not a constant expression and it
   cannot appear in the static initializer below.  It stays C for now
   (`--clear-waiting-for-input', `--waiting-for-input-p'); the table is
   not the only writer of the cell.  Recorded in docs/m30-plan.org.  */

/* M30 imp-3: the menu-bar / tab-bar / tool-bar index cells are the real
   definitions, placed here so the cell table initializer below can take
   their addresses.  Their infrastructure code uses them further down
   this file.  */
static int menu_bar_items_index;
static int ntab_bar_items;
static int ntool_bar_items;

/* M30 imp-4: the menu-bar / tab-bar / tool-bar object cells follow the
   same rule as the index cells above.  Their real `static Lisp_Object'
   definitions are placed here, above the table, so the cell table
   initializer can take their addresses.  The menu-bar / tab-bar /
   tool-bar infrastructure code further down this file uses them.  Each
   cell is a GC root: syms_of_keyboard sets it and staticpros it.  */
static Lisp_Object menu_bar_one_keymap_changed_items;
static Lisp_Object menu_bar_items_vector;
static Lisp_Object tab_bar_items_vector;
static Lisp_Object tool_bar_items_vector;

enum cell_kind
{
  CELL_BOOL,
  CELL_FIXNUM,
  CELL_FIXNAT,
  CELL_LISP_OBJECT
};

struct cell_entry
{
  const char *name;
  void *cell;
  enum cell_kind kind;
};

static const struct cell_entry cell_table[] =
  {
    /* plain bool cells (M30 imp-2) */
    { "--set-echoing!", &echoing, CELL_BOOL },
    { "--set-ignore-mouse-drag-p", &ignore_mouse_drag_p, CELL_BOOL },
    { "--clear-display-working-on-window-p", &display_working_on_window_p,
      CELL_BOOL },
    /* plain fixnum cells (M30 imp-3).  Each cell is a `static int'
       (or the extern int windows_or_buffers_changed).  The setter name
       is the canonical table key; the bare C getters stay C.  */
    { "--set-down-mouse-line-number-width", &down_mouse_line_number_width,
      CELL_FIXNUM },
    { "--set-last-mouse-button", &last_mouse_button, CELL_FIXNUM },
    { "--set-last-mouse-x", &last_mouse_x, CELL_FIXNUM },
    { "--set-last-mouse-y", &last_mouse_y, CELL_FIXNUM },
    { "--set-double-click-count", &double_click_count, CELL_FIXNUM },
    { "--set-menu-bar-items-index", &menu_bar_items_index, CELL_FIXNUM },
    { "--set-tab-bar-items-count", &ntab_bar_items, CELL_FIXNUM },
    { "--set-tool-bar-items-count", &ntool_bar_items, CELL_FIXNUM },
    { "--set-windows-or-buffers-changed", &windows_or_buffers_changed,
      CELL_FIXNUM },
    /* fixnum count cell (M30 imp-3).  raw_keybuf_count indexes
       raw_keybuf, so a negative value corrupts the key buffer.  The
       deleted per-cell setter ran CHECK_FIXNAT; CELL_FIXNAT keeps that
       duty as the table becomes the only writer.  */
    { "--set-raw-keybuf-count", &raw_keybuf_count, CELL_FIXNAT },
    /* Lisp_Object cell (M30 imp-1) */
    { "--set-frame-relative-event-pos", &frame_relative_event_pos,
      CELL_LISP_OBJECT },
    /* Lisp_Object cells (M30 imp-4).  Each cell is a GC root: a
       staticpro in syms_of_keyboard roots it, and the cell is set to
       Qnil (or a fresh vector) before that staticpro.  A write uses
       the canonical --set- name; a get/set pair shares one row, so a
       read uses the same key.  */
    { "--set-menu-bar-items-vector", &menu_bar_items_vector,
      CELL_LISP_OBJECT },
    { "--set-tab-bar-items-vector", &tab_bar_items_vector,
      CELL_LISP_OBJECT },
    { "--set-tool-bar-items-vector", &tool_bar_items_vector,
      CELL_LISP_OBJECT },
    { "--set-menu-bar-one-keymap-changed-items",
      &menu_bar_one_keymap_changed_items, CELL_LISP_OBJECT },
    { "--set-menu-bar-touch-id", &menu_bar_touch_id, CELL_LISP_OBJECT },
    { "--set-internal-last-event-frame", &internal_last_event_frame,
      CELL_LISP_OBJECT },
    { "--set-unread-switch-frame", &unread_switch_frame,
      CELL_LISP_OBJECT },
    { "--set-read-key-sequence-remapped", &read_key_sequence_remapped,
      CELL_LISP_OBJECT },
    /* Lisp_Object cell (M30 imp-5).  getctag is the prompt tag that
       quit_throw_to_read_char unwinds to via abort_to_prompt.  imp-5
       roots it in syms_of_keyboard (getctag = Qnil then staticpro), so
       the object-cell rule holds.  A write uses the canonical
       --set- name; --set-ctag must return TAG, so the Scheme wrapper
       returns it.  */
    { "--set-ctag", &getctag, CELL_LISP_OBJECT },
  };

/* Return the table entry for the accessor name NAME, or NULL.  A linear
   scan is enough for the 23 entries.  */

/* A one-entry memo for the linear scan.  The hot callers use one name
   repeatedly: for example `kbd-buffer-get-event' reads
   --get-internal-last-event-frame once per event.  An EQ test reuses
   the last result and keeps the lookup from adding a visible cost.
   M30 imp-4.

   The memo caches NAME on the strcmp hit path, for any symbol, not just
   an interned one (cr.org F2).  An EQ false hit needs the same address,
   so the cached symbol must stay alive.  last_cell_name is a GC root:
   syms_of_keyboard staticpros it.  Without that root an uninterned
   symbol could be collected, a later object could reuse its address,
   and EQ would return the wrong cell entry.  */
static Lisp_Object last_cell_name;
static const struct cell_entry *last_cell_entry;

static const struct cell_entry *
lookup_cell (Lisp_Object name)
{
  CHECK_SYMBOL (name);

  if (EQ (name, last_cell_name))
    return last_cell_entry;

  const char *s = SSDATA (SYMBOL_NAME (name));

  for (int i = 0; i < ARRAYELTS (cell_table); i++)
    if (strcmp (s, cell_table[i].name) == 0)
      {
	last_cell_name = name;
	last_cell_entry = &cell_table[i];
	return &cell_table[i];
      }

  return NULL;
}

DEFUN ("--cell-ref", Fcell_ref, Scell_ref, 1, 1, 0,
       doc: /* Internal: return the value of the C cell named NAME.

The NAME is the accessor name of the cell, for example
`--set-echoing!`.  A missing name signals an error.  */)
  (Lisp_Object name)
{
  const struct cell_entry *e = lookup_cell (name);

  if (e == NULL)
    xsignal2 (Qerror, build_string ("unknown cell"), name);

  switch (e->kind)
    {
    case CELL_BOOL:
      return *(bool *) e->cell ? Qt : Qnil;

    case CELL_FIXNUM:
    case CELL_FIXNAT:
      return make_fixnum (*(int *) e->cell);

    case CELL_LISP_OBJECT:
      return *(Lisp_Object *) e->cell;
    }

  emacs_abort ();
}

DEFUN ("--cell-set!", Fcell_set, Scell_set, 2, 2, 0,
       doc: /* Internal: set the C cell named NAME to VAL.

The NAME is the accessor name of the cell, for example
`--set-echoing!`.  The kind of the cell selects the convert step.  A
missing name signals an error.  Return nil.  */)
  (Lisp_Object name, Lisp_Object val)
{
  const struct cell_entry *e = lookup_cell (name);

  if (e == NULL)
    xsignal2 (Qerror, build_string ("unknown cell"), name);

  switch (e->kind)
    {
    case CELL_BOOL:
      *(bool *) e->cell = !NILP (val);
      break;

    case CELL_FIXNUM:
      /* A plain `static int' cell.  The deleted per-cell setter ran
	 CHECK_FIXNUM, which accepts a negative value; the table keeps
	 the same range.  (cr.org F7: no confirmed writer stores a
	 negative value; the range is kept to match the old setter.)  */
      CHECK_FIXNUM (val);
      *(int *) e->cell = XFIXNUM (val);
      break;

    case CELL_FIXNAT:
      /* A fixnum count cell (raw_keybuf_count, M30 imp-3).  The cell
	 indexes raw_keybuf, so the value must not be negative.  The
	 deleted per-cell setter ran CHECK_FIXNAT; keep that duty.  */
      CHECK_FIXNAT (val);
      *(int *) e->cell = XFIXNAT (val);
      break;

    case CELL_LISP_OBJECT:
      *(Lisp_Object *) e->cell = val;
      break;

    default:
      /* Symmetry with --cell-ref: a kind outside the enum must not write
	 nothing and report success.  */
      emacs_abort ();
    }

  return Qnil;
}


/* X and Y are frame-relative coordinates for a click or wheel event.
   Return a Lisp-style event list.  */

static Lisp_Object
make_lispy_position (struct frame *f, Lisp_Object x, Lisp_Object y,
		     Time t)
{
  /* imp-6.4 — C body replaced by SCM_CALL_4 into the Scheme
     orchestrator in (emacs lispy-position) make-lispy-position.  */
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
fixnum builds.  Delegates to (emacs lispy-position).  FOW may be
nil (the pointer can be outside every frame during a drag), which
make_lispy_position handles by passing a nil frame.  */)
  (Lisp_Object fow, Lisp_Object x, Lisp_Object y, Lisp_Object t)
{
  struct frame *f = NILP (fow) ? NULL : XFRAME (fow);
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

/* FIX-20260828-guilemacs: M19 imp-1 — thin C shims that wrap the
   heavyweight C geometry/matrix functions the Scheme port in
   (emacs lispy-position) calls.  Each stays small and single-purpose.  */

DEFUN ("--find-hot-spot", Ffind_hot_spot_shim, Sfind_hot_spot_shim,
       3, 3, 0,
       doc: /* FIX-20260828-guilemacs: internal: return hotspot id of
OBJECT's :map under pixel (DX, DY), or nil.

Wraps xdisp.c find_hot_spot.  On a build without a window system the
whole guarded body is absent and nil is returned, so Scheme can treat
nil uniformly as "no hit".  */)
  (Lisp_Object object, Lisp_Object dx, Lisp_Object dy)
{
#ifdef HAVE_WINDOW_SYSTEM
  Lisp_Object image_map, hotspot;
  if (IMAGEP (object)
      && (image_map = plist_get (XCDR (object), QCmap), !NILP (image_map))
      && (hotspot = find_hot_spot (image_map, XFIXNUM (dx), XFIXNUM (dy)),
	  CONSP (hotspot))
      && (hotspot = XCDR (hotspot), CONSP (hotspot)))
    return XCAR (hotspot);
#endif
  return Qnil;
}

DEFUN ("--frame-internal-border-part", Fframe_internal_border_part_shim,
       Sframe_internal_border_part_shim, 4, 4, 0,
       doc: /* FIX-20260828-guilemacs: internal: return the symbol for
the internal-border part of live frame F at pixel (X, Y), or nil.

Wraps frame.c frame_internal_border_part and folds in the
internal_border_parts symbol lookup so Scheme never sees the raw enum.
The whole original guarded body (FRAME_WINDOW_P / FRAME_LIVE_P / nilp
POSN / border width / drag-internal-border param) lives here because
Scheme cannot see the #ifdef HAVE_WINDOW_SYSTEM; on a build without a
window system the guarded body is absent and nil is returned, so
Scheme treats nil as "no hit".  */)
  (Lisp_Object f, Lisp_Object x, Lisp_Object y, Lisp_Object posn)
{
#ifdef HAVE_WINDOW_SYSTEM
  struct frame *fr = XFRAME (f);
  if (FRAME_WINDOW_P (fr)
      && FRAME_LIVE_P (fr)
      && NILP (posn)
      && FRAME_INTERNAL_BORDER_WIDTH (fr) > 0
      && !NILP (get_frame_param (fr, Qdrag_internal_border)))
    {
      enum internal_border_part part
	= frame_internal_border_part (fr, XFIXNUM (x), XFIXNUM (y));
      if (part != INTERNAL_BORDER_NONE)
	return builtin_lisp_symbol (internal_border_parts[part]);
    }
#endif
  return Qnil;
}

DEFUN ("--window-box-left", Fwindow_box_left_shim, Swindow_box_left_shim,
       2, 2, 0,
       doc: /* FIX-20260828-guilemacs: internal: return the X pixel
coordinate of the left edge of WINDOW's AREA glyph row area.  */)
  (Lisp_Object w, Lisp_Object area)
{
  return make_fixnum (window_box_left (XWINDOW (w),
				       (enum glyph_row_area) XFIXNUM (area)));
}

DEFUN ("--window-box-width", Fwindow_box_width_shim, Swindow_box_width_shim,
       2, 2, 0,
       doc: /* FIX-20260828-guilemacs: internal: return the width in
pixels of WINDOW's AREA glyph row area.  */)
  (Lisp_Object w, Lisp_Object area)
{
  return make_fixnum (window_box_width (XWINDOW (w),
					(enum glyph_row_area) XFIXNUM (area)));
}

DEFUN ("--window-frame-origin", Fwindow_frame_origin_shim,
       Swindow_frame_origin_shim, 1, 1, 0,
       doc: /* FIX-20260828-guilemacs: internal: return (X . Y), the
frame-relative pixel coordinates of WINDOW's top-left corner
(WINDOW_LEFT_EDGE_X / WINDOW_TOP_EDGE_Y).  */)
  (Lisp_Object w)
{
  struct window *win = XWINDOW (w);
  return Fcons (make_fixnum (WINDOW_LEFT_EDGE_X (win)),
		make_fixnum (WINDOW_TOP_EDGE_Y (win)));
}

DEFUN ("--mode-line-string", Fmode_line_string_shim, Smode_line_string_shim,
       4, 4, 0,
       doc: /* FIX-20260828-guilemacs: internal: return the string at
(WX, WY) in WINDOW's mode/header/tab line for PART, packed as
(STRING CHARPOS OBJECT COL ROW DX DY WIDTH HEIGHT).

COL/ROW are pixel positions in, character positions out.  Wraps
dispnew.c mode_line_string.  */)
  (Lisp_Object w, Lisp_Object part, Lisp_Object wx, Lisp_Object wy)
{
  struct window *win = XWINDOW (w);
  int col = XFIXNUM (wx), row = XFIXNUM (wy);
  ptrdiff_t charpos = 0;
  Lisp_Object object = Qnil;
  int dx, dy, width, height;
  Lisp_Object string = mode_line_string (win, (enum window_part) XFIXNUM (part),
					 &col, &row, &charpos, &object,
					 &dx, &dy, &width, &height);
  return listn (9, string, make_fixnum (charpos), object,
		make_fixnum (col), make_fixnum (row),
		make_fixnum (dx), make_fixnum (dy),
		make_fixnum (width), make_fixnum (height));
}

DEFUN ("--marginal-area-string", Fmarginal_area_string_shim,
       Smarginal_area_string_shim, 4, 4, 0,
       doc: /* FIX-20260828-guilemacs: internal: return the string at
(WX, WY) in WINDOW's margin area for PART, packed as
(STRING CHARPOS OBJECT COL ROW DX DY WIDTH HEIGHT).

COL/ROW are pixel positions in, character positions out.  Wraps
dispnew.c marginal_area_string.  */)
  (Lisp_Object w, Lisp_Object part, Lisp_Object wx, Lisp_Object wy)
{
  struct window *win = XWINDOW (w);
  int col = XFIXNUM (wx), row = XFIXNUM (wy);
  ptrdiff_t charpos = 0;
  Lisp_Object object = Qnil;
  int dx, dy, width, height;
  Lisp_Object string = marginal_area_string (win, (enum window_part) XFIXNUM (part),
					     &col, &row, &charpos, &object,
					     &dx, &dy, &width, &height);
  return listn (9, string, make_fixnum (charpos), object,
		make_fixnum (col), make_fixnum (row),
		make_fixnum (dx), make_fixnum (dy),
		make_fixnum (width), make_fixnum (height));
}

DEFUN ("--buffer-posn-from-coords", Fbuffer_posn_from_coords_shim,
       Sbuffer_posn_from_coords_shim, 3, 3, 0,
       doc: /* FIX-20260828-guilemacs: internal: matrix walk for the
window-relative pixel coords (X2, Y2) in WINDOW, packed as
(STRING TEXT-POS STRING-POS OBJECT COL ROW DX DY WIDTH HEIGHT).

COL/ROW are the character positions (x2/y2 out).  Wraps dispnew.c
buffer_posn_from_coords.  */)
  (Lisp_Object w, Lisp_Object x2, Lisp_Object y2)
{
  struct window *win = XWINDOW (w);
  int col = XFIXNUM (x2), row = XFIXNUM (y2);
  struct display_pos p;
  Lisp_Object object = Qnil;
  int dx, dy, width, height;
  Lisp_Object string = buffer_posn_from_coords (win, &col, &row, &p, &object,
						&dx, &dy, &width, &height);
  return listn (10, string, make_fixnum (CHARPOS (p.pos)),
		make_fixnum (STRINGP (string) ? CHARPOS (p.string_pos) : 0),
		object,
		make_fixnum (col), make_fixnum (row),
		make_fixnum (dx), make_fixnum (dy),
		make_fixnum (width), make_fixnum (height));
}

DEFUN ("--window-from-coordinates", Fwindow_from_coordinates_shim,
       Swindow_from_coordinates_shim, 3, 3, 0,
       doc: /* FIX-20260828-guilemacs: internal: return
(WINDOW PART BAR-KIND) for pixel (MX, MY) in FRAME.

Wraps window.c window_from_coordinates.  BAR-KIND is 'tab-bar,
'tool-bar, or nil, encoding whether WINDOW is FRAME's tab-bar or
tool-bar window (the guarded body that needs f->tab_bar_window /
f->tool_bar_window, which Scheme cannot reach).  On a build without a
window system BAR-KIND is always nil.  */)
  (Lisp_Object f, Lisp_Object mx, Lisp_Object my)
{
  struct frame *fr = XFRAME (f);
  enum window_part part;
  Lisp_Object window = window_from_coordinates (fr,
						XFIXNUM (mx), XFIXNUM (my),
						&part, false, true, true);
  Lisp_Object bar_kind = Qnil;
#ifdef HAVE_WINDOW_SYSTEM
  if (WINDOWP (fr->tab_bar_window) && EQ (window, fr->tab_bar_window))
    bar_kind = Qtab_bar;
#ifndef HAVE_EXT_TOOL_BAR
  else if (WINDOWP (fr->tool_bar_window) && EQ (window, fr->tool_bar_window))
    bar_kind = Qtool_bar;
#endif
#endif
  return list3 (window, make_fixnum (part), bar_kind);
}

DEFUN ("--toolkit-position", Ftoolkit_position_shim, Stoolkit_position_shim,
       3, 3, 0,
       doc: /* FIX-20260828-guilemacs: internal: return (MENU-BAR-P
TOOL-BAR-P) for pixel (MX, MY) in FRAME from the terminal's toolkit
position hook, or nil if the hook is absent.

On a build without a window system the guarded body is absent and nil
is returned.  */)
  (Lisp_Object f, Lisp_Object mx, Lisp_Object my)
{
#ifdef HAVE_WINDOW_SYSTEM
  struct frame *fr = XFRAME (f);
  bool menu_bar_p = false, tool_bar_p = false;
  if (fr && FRAME_TERMINAL (fr)->toolkit_position_hook)
    {
      FRAME_TERMINAL (fr)->toolkit_position_hook (fr, XFIXNUM (mx),
						  XFIXNUM (my),
						  &menu_bar_p, &tool_bar_p);
      return Fcons (menu_bar_p ? Qt : Qnil,
		    tool_bar_p ? Qt : Qnil);
    }
#endif
  return Qnil;
}

/* FIX-20260828-guilemacs: M19 imp-2 — thin C shims for the menu-bar /
   tab-bar / line-number-hscroll helpers ported to (emacs lispy-position).
   Each wraps a build-time macro, a frame-internal field, or a heavyweight
   C geometry function that Scheme cannot see directly.  */

DEFUN ("--have-ext-menu-bar-p", Fhave_ext_menu_bar_p, Shave_ext_menu_bar_p,
       0, 0, 0,
       doc: /* FIX-20260828-guilemacs: internal: return t if this build
uses an external (toolkit-provided) menu bar, else nil.  Exposes the
build-time HAVE_EXT_MENU_BAR macro to Scheme.  */)
  (void)
{
#ifdef HAVE_EXT_MENU_BAR
  return Qt;
#else
  return Qnil;
#endif
}

DEFUN ("--frame-menu-bar-window", Fframe_menu_bar_window_shim,
       Sframe_menu_bar_window_shim, 1, 1, 0,
       doc: /* FIX-20260828-guilemacs: internal: return FRAME's menu-bar
window (a dummy window on non-toolkit X builds), or nil if it is not a
window or this build has no non-toolkit menu-bar window.  */)
  (Lisp_Object frame)
{
#if defined HAVE_WINDOW_SYSTEM && !defined HAVE_EXT_MENU_BAR
  struct frame *f = XFRAME (frame);
  return WINDOWP (f->menu_bar_window) ? f->menu_bar_window : Qnil;
#else
  return Qnil;
#endif
}

DEFUN ("--frame-tab-bar-window", Fframe_tab_bar_window_shim,
       Sframe_tab_bar_window_shim, 1, 1, 0,
       doc: /* FIX-20260828-guilemacs: internal: return FRAME's tab-bar
window, or nil if it is not a window or this build has no tab-bar
window.  */)
  (Lisp_Object frame)
{
#ifdef HAVE_WINDOW_SYSTEM
  struct frame *f = XFRAME (frame);
  return WINDOWP (f->tab_bar_window) ? f->tab_bar_window : Qnil;
#else
  return Qnil;
#endif
}

DEFUN ("--line-number-display-width-for-window",
       Fline_number_display_width_for_window,
       Sline_number_display_width_for_window, 1, 1, 0,
       doc: /* FIX-20260828-guilemacs: internal: return the column width
of the line-number display for WINDOW as a fixnum.  Unlike the existing
line-number-display-width, this takes an arbitrary window.  */)
  (Lisp_Object window)
{
  int width, pixel_width;
  line_number_display_width (XWINDOW (window), &width, &pixel_width);
  return make_fixnum (width);
}

DEFUN ("--frame-menu-bar-items", Fframe_menu_bar_items_shim,
       Sframe_menu_bar_items_shim, 1, 1, 0,
       doc: /* FIX-20260828-guilemacs: internal: return the raw
menu-bar-items vector for FRAME (FRAME_MENU_BAR_ITEMS).  */)
  (Lisp_Object frame)
{
  return FRAME_MENU_BAR_ITEMS (XFRAME (frame));
}

DEFUN ("--frame-tab-bar-items", Fframe_tab_bar_items_shim,
       Sframe_tab_bar_items_shim, 1, 1, 0,
       doc: /* FIX-20260828-guilemacs: internal: return the raw
tab-bar-items vector for FRAME (f->tab_bar_items).  */)
  (Lisp_Object frame)
{
  return XFRAME (frame)->tab_bar_items;
}

DEFUN ("--get-tab-bar-item-kbd", Fget_tab_bar_item_kbd_shim,
       Sget_tab_bar_item_kbd_shim, 3, 3, 0,
       doc: /* FIX-20260828-guilemacs: internal: return (PROP-IDX .
CLOSE-P) for the tab-bar item of FRAME at frame-relative pixel (X, Y),
or nil if no item is there.  Wraps get_tab_bar_item_kbd.  */)
  (Lisp_Object frame, Lisp_Object x, Lisp_Object y)
{
#ifdef HAVE_WINDOW_SYSTEM
  int prop_idx;
  bool close_p;
  if (get_tab_bar_item_kbd (XFRAME (frame), XFIXNUM (x), XFIXNUM (y),
			    &prop_idx, &close_p) >= 0)
    return Fcons (make_fixnum (prop_idx), close_p ? Qt : Qnil);
#endif
  return Qnil;
}

DEFUN ("--menu-bar-hpos-vpos", Fmenu_bar_hpos_vpos_shim,
       Smenu_bar_hpos_vpos_shim, 3, 3, 0,
       doc: /* FIX-20260828-guilemacs: internal: return (COLUMN . ROW)
for the menu-bar WINDOW at frame-relative pixel (IX, IY).  Wraps
x_y_to_hpos_vpos after FRAME_TO_WINDOW_PIXEL conversion.  */)
  (Lisp_Object window, Lisp_Object ix, Lisp_Object iy)
{
#ifdef HAVE_WINDOW_SYSTEM
  struct window *w = XWINDOW (window);
  int wx = FRAME_TO_WINDOW_PIXEL_X (w, XFIXNUM (ix));
  int wy = FRAME_TO_WINDOW_PIXEL_Y (w, XFIXNUM (iy));
  int column, row, dummy;
  x_y_to_hpos_vpos (w, wx, wy, &column, &row, NULL, NULL, &dummy);
  return Fcons (make_fixnum (column), make_fixnum (row));
#else
  return Qnil;
#endif
}

DEFUN ("--menu-bar-hpos-vpos-raw", Fmenu_bar_hpos_vpos_raw_shim,
       Smenu_bar_hpos_vpos_raw_shim, 3, 3, 0,
       doc: /* FIX-20260829-guilemacs: internal: return (COLUMN . ROW)
for the menu-bar WINDOW at frame-relative pixel (IX, IY), with NO
FRAME_TO_WINDOW_PIXEL conversion.  Matches the raw call in the Scheme
menu-bar-touch-activate port (emacs lispy-position): same compile guard and same
NILP (menu_bar_window) short-circuit.  Used by the Scheme
menu-bar-touch-activate port (M20, imp-4).  */)
  (Lisp_Object window, Lisp_Object ix, Lisp_Object iy)
{
#if defined HAVE_WINDOW_SYSTEM && !defined HAVE_EXT_MENU_BAR
  if (NILP (window))
    return Qnil;
  struct window *w = XWINDOW (window);
  int column, row, dummy;
  x_y_to_hpos_vpos (w, XFIXNUM (ix), XFIXNUM (iy), &column, &row,
		    NULL, NULL, &dummy);
  return Fcons (make_fixnum (column), make_fixnum (row));
#else
  return Qnil;
#endif
}

DEFUN ("--menu-pixel-to-glyph-coords", Fmenu_pixel_to_glyph_coords_shim,
       Smenu_pixel_to_glyph_coords_shim, 3, 3, 0,
       doc: /* FIX-20260828-guilemacs: internal: return (COLUMN . ROW)
for FRAME at frame-relative pixel (IX, IY) via pixel_to_glyph_coords.  */)
  (Lisp_Object frame, Lisp_Object ix, Lisp_Object iy)
{
  int column, row;
  pixel_to_glyph_coords (XFRAME (frame), XFIXNUM (ix), XFIXNUM (iy),
			 &column, &row, NULL, 1);
  return Fcons (make_fixnum (column), make_fixnum (row));
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

/* imp-7.1 — file-static getter/setter DEFUNs for double-click
   and drag state.  8 statics, 16 DEFUNs.  C retains ownership;
   Scheme reads/writes through these wrappers (no Scheme-side
   mirror record).  Used by imp-7.2 wheel double-click detection
   and imp-7.5 MOUSE_CLICK port.  */

DEFUN ("--frame-relative-event-pos", Fframe_relative_event_pos,
       Sframe_relative_event_pos, 0, 0, 0,
       doc: /* Return the value of frame_relative_event_pos.

A cons (X . Y) recording the original frame-relative coordinates
of the most recent mouse-down event.  */)
  (void)
{
  return frame_relative_event_pos;
}

DEFUN ("--down-mouse-line-number-width", Fdown_mouse_line_number_width,
       Sdown_mouse_line_number_width, 0, 0, 0,
       doc: /* Return down_mouse_line_number_width as a fixnum.  */)
  (void)
{
  return make_fixnum (down_mouse_line_number_width);
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

DEFUN ("--last-mouse-x", Flast_mouse_x,
       Slast_mouse_x, 0, 0, 0,
       doc: /* Return last_mouse_x as a fixnum.  */)
  (void)
{
  return make_fixnum (last_mouse_x);
}

DEFUN ("--last-mouse-y", Flast_mouse_y,
       Slast_mouse_y, 0, 0, 0,
       doc: /* Return last_mouse_y as a fixnum.  */)
  (void)
{
  return make_fixnum (last_mouse_y);
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

DEFUN ("--ignore-mouse-drag-p", Fignore_mouse_drag_p,
       Signore_mouse_drag_p, 0, 0, 0,
       doc: /* Return the value of ignore_mouse_drag_p (C bool).

When non-zero, implicit mouse-movement events are discarded
during drag tracking (keyboard.c:1761).  */)
  (void)
{
  return ignore_mouse_drag_p ? Qt : Qnil;
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
Always returns an empty vector: MULTIMEDIA_KEY_EVENT came from a
dropped platform and can't fire here.  */)
  (void)
{
  return scm_c_make_vector (0, SCM_BOOL_F);
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

/* M30 imp-4: the four tiny shims that let the Scheme (emacs read-char)
   and (emacs kbd-buffer) ports of internal-handle-focus-in read and
   write internal_last_event_frame and unread_switch_frame moved to
   (emacs cell-accessors), through the cell table.  The read-and-clear
   variant --rc-take-unread-switch-frame stays C.  */

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
  /* M22 imp-1: the decision logic moved to Scheme
     (emacs read-key-sequence) get-input-pending!.  The C global
     `input_pending' stays C-owned; only the decision moves.  */
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs read-key-sequence", "get-input-pending!");
  input_pending = scm_is_true (SCM_CALL_1 (proc, scm_from_int (flags)));
  return input_pending;
}

/* M25 imp-3: the terminal_list walk that gobble_input used to do moved
   into (emacs gobble) `gobble-input!'.  gobble_input is now a thin
   dispatcher (below).  It returns the number of keyboard chars read,
   or -1 meaning this is a bad time to try to read input.  Four
   single-purpose shims stay C because each owns something Scheme
   cannot reach safely:

   - --terminal-read-socket-hook-p       predicate; read_socket_hook is
     a raw C function pointer that a Scheme body only probes for here.
   - --terminal-read-socket-hook!        drains read_socket_hook (a raw
     C pointer, so the call itself must stay C) and owns the nr == -2
     terminal-death arm (Fdelete_terminal, or terminate_due_to_signal
     when the dying terminal was the last).  terminate_due_to_signal
     never returns, so it must not unwind through a live Scheme call
     frame; keeping it inside this shim's C body is the guard.
   - --pending-signals-set!              pending_signals is also written
     by deliver_input_available_signal from a signal handler.
   - --frame-make-pointer-visible!       frame_make_pointer_visible is a
     plain C subroutine; Scheme drives which frames via frame-list and
     frame-terminal.  */

/* Return t if TERMINAL has a read_socket_hook, else nil.  */
DEFUN ("--terminal-read-socket-hook-p", Fterminal_read_socket_hook_p,
       Sterminal_read_socket_hook_p, 1, 1, 0,
       doc: /* Internal: return t if TERMINAL has a read_socket_hook.
No side effects.  */)
  (Lisp_Object terminal)
{
  struct terminal *t = decode_live_terminal (terminal);
  return (t->read_socket_hook ? Qt : Qnil);
}

/* Static storage for the hold_quit input_event shared across calls to
   --terminal-read-socket-hook!.  Reset once per call (M9 ie-smob
   lifetime rule: the caller reads the returned smob's kind before the
   next call reuses this storage).  */
static struct input_event gobble_hold_quit_storage;

DEFUN ("--terminal-read-socket-hook!", Fterminal_read_socket_hook,
       Sterminal_read_socket_hook, 1, 1, 0,
       doc: /* Internal: drain TERMINAL's read_socket_hook.  Reset a
shared hold_quit input event to NO_EVENT, then call the hook repeatedly,
adding each positive result to the count, until it returns 0 or less.
If the last call returned -2 (the terminal died), delete the terminal —
or terminate Emacs (SIGHUP) if it was the last one; that arm must stay
in this C body because terminate_due_to_signal never returns.  Returns
\(nread nr ie), where nr is the last hook return (0 clean end, -1 not
ok to read now, -2 handled here) and ie wraps the shared hold_quit.
Read ie's kind in the same step that receives it — the storage is
reused on the next call.  */)
  (Lisp_Object terminal)
{
  struct terminal *t = decode_live_terminal (terminal);
  int nread = 0, nr;
  Lisp_Object tmp;

  memset (&gobble_hold_quit_storage, 0, sizeof gobble_hold_quit_storage);
  gobble_hold_quit_storage.kind = NO_EVENT;
  gobble_hold_quit_storage.frame_or_window = Qnil;
  gobble_hold_quit_storage.arg = Qnil;
  gobble_hold_quit_storage.device = Qt;

  /* No need for FIONREAD or fcntl; just say don't wait.  */
  while ((nr = (*t->read_socket_hook) (t, &gobble_hold_quit_storage)) > 0)
    nread += nr;

  if (nr == -2)
    {
      /* The terminal device terminated; it should be closed.  */
      if (!terminal_list->next_terminal)
	/* This was our last terminal.  SIGHUP seems appropriate if we
	   can't reach the terminal.  Never returns.  */
	terminate_due_to_signal (SIGHUP, 10);

      /* XXX Is calling delete_terminal safe here?  It calls
         delete_frame.  */
      XSETTERMINAL (tmp, t);
      Fdelete_terminal (tmp, Qnoelisp);
    }

  return list3 (make_fixnum (nread), make_fixnum (nr),
		ie_wrap (&gobble_hold_quit_storage));
}

DEFUN ("--pending-signals-set!", Fpending_signals_set,
       Spending_signals_set, 0, 0, 0,
       doc: /* Internal: set the pending-signals flag.  pending_signals
stays a C cell because deliver_input_available_signal also writes it
from a signal handler.  Returns nil.  */)
  (void)
{
  pending_signals = true;
  return Qnil;
}

DEFUN ("--frame-make-pointer-visible!", Fframe_make_pointer_visible,
       Sframe_make_pointer_visible, 1, 1, 0,
       doc: /* Internal: make the mouse pointer visible on FRAME.
frame_make_pointer_visible is a plain C subroutine.  Returns nil.  */)
  (Lisp_Object frame)
{
  frame_make_pointer_visible (decode_live_frame (frame));
  return Qnil;
}

/* Dispatch into (emacs gobble) `gobble-input!'.  */
int
gobble_input (void)
{
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs gobble", "gobble-input!");
  return scm_to_int (SCM_CALL_0 (proc));
}

/* This is the tty way of reading available input.

   Note that each terminal device has its own `struct terminal' object,
   and so this function is called once for each individual termcap
   terminal.  The first parameter indicates which terminal to read from.

   M25 imp-4: this is now a thin dispatcher into (emacs gobble)
   `tty-read-avail-input!'.  Only the pieces that must stay C remain
   here:
   - the raw dead-terminal / terminal-type / term_initted /
     suspended-terminal guards, read off the raw struct terminal *
     before XSETTERMINAL.  A dead terminal must silently return 0, not
     signal — routing through decode_live_terminal would change that;
   - the GPM drain (an external C-library callout with no Scheme
     representation).
   Everything after the guards — buffer-free/hold sizing, FIONREAD
   sizing, the nonblocking emacs_read, the per-byte meta decode and the
   kbd_buffer_store_event calls — lives in the Scheme body.  */

/* GPM: drain the GPM mouse event queue.  Returns the number of events
   handled (each stored via handle_one_term_event), or 0 to fall
   through to the byte read path.  Only reached once the raw guards
   have passed (a live, tty-typed, initted, non-suspended terminal).
   #ifdef'd out of this build: HAVE_GPM is undefined in src/config.h.  */
#ifdef HAVE_GPM
static int
tty_gpm_read (struct tty_display_info *tty)
{
  int nread = 0;

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
      while (gpm = Gpm_GetEvent (&event), gpm == 1)
	nread += handle_one_term_event (tty, &event);
      if (gpm == 0)
	/* Presumably the GPM daemon has closed the connection.  */
	close_gpm (fd);
    }
  return nread;
}
#endif /* HAVE_GPM */

int
tty_read_avail_input (struct terminal *terminal,
                      struct input_event *hold_quit)
{
  struct tty_display_info *tty = terminal->display_info.tty;
  Lisp_Object term;
  static SCM proc = SCM_UNDEFINED;

  if (!terminal->name)		/* Don't read from a dead terminal.  */
    return 0;

  if (terminal->type != output_termcap
      && terminal->type != output_msdos_raw)
    emacs_abort ();

  if (! tty->term_initted)      /* In case we get called during bootstrap.  */
    return 0;

  if (! tty->input)
    return 0;                   /* The terminal is suspended.  */

#ifdef HAVE_GPM
  {
    int gpm_read = tty_gpm_read (tty);
    if (gpm_read)
      return gpm_read;
  }
#endif /* HAVE_GPM */

  /* Dispatch the rest (buffer-free/hold sizing, FIONREAD sizing, the
     nonblocking read, the per-byte meta decode and the store) into
     (emacs gobble) `tty-read-avail-input!'.  The unused hold_quit
     parameter is not forwarded: the pre-port C body never used it (it
     called kbd_buffer_store_event, which takes no hold_quit), and
     kbd-buffer-store-event! mirrors that with a #f hold-quit.  */
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs gobble", "tty-read-avail-input!");
  XSETTERMINAL (term, terminal);
  return scm_to_int (SCM_CALL_1 (proc, term));
}


/* M25 imp-2: handle_async_input / process_pending_signals became thin
   dispatchers into (emacs gobble).  Two C cells need Scheme-side
   triggers and stay C: pending_signals (also written by
   deliver_input_available_signal, a signal handler) and the atimer
   callback machinery do_pending_atimers (the same kind of thing that
   stayed C in M24, e.g. poll_timer).  keyboard.x auto-registers these
   DEFUNs; neither is reached from an early-init path (see
   early-init-c-body-before-defun-registration, docs/kb.org).  */

DEFUN ("--pending-signals-clear!", Fpending_signals_clear,
       Spending_signals_clear, 0, 0, 0,
       doc: /* Internal: clear the pending-signals flag.  pending_signals
stays a C cell because deliver_input_available_signal also writes it
from a signal handler.  Returns nil.  */)
  (void)
{
  pending_signals = false;
  return Qnil;
}

DEFUN ("--do-pending-atimers!", Fdo_pending_atimers,
       Sdo_pending_atimers, 0, 0, 0,
       doc: /* Internal: call do_pending_atimers ().  Returns nil.  */)
  (void)
{
  do_pending_atimers ();
  return Qnil;
}

/* Dispatch into (emacs gobble) `handle-async-input!'.  */
static void
handle_async_input (void)
{
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs gobble", "handle-async-input!");
  SCM_CALL_0 (proc);
}

/* Dispatch into (emacs gobble) `process-pending-signals!'.  */
void
process_pending_signals (void)
{
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs gobble", "process-pending-signals!");
  SCM_CALL_0 (proc);
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

/* Register a user signal.  Kept as a C body (not a dispatcher into
   (emacs gobble)) because init_signals calls this entry point before
   syms_of_keyboard registers the --user-signal-* DEFUNs, so a Scheme
   dispatch could not run before those primitives exist (emacs.c:
   init_signals 1622 < syms_of_keyboard 1688; milestone M25 imp-1
   close-out).  Registration needs no Scheme decision, so this stays a
   plain C body; the drain *loop* policy lives in Scheme as
   store-user-signal-events!.  */
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

/* --- M25 imp-1: user-signal primitives -------------------------------
   Scheme owns the drain decision ((emacs gobble)); C owns the raw
   user_signals list because handle_user_signal reads it from a signal
   handler and store-user-signal-events! needs node mutation.  (The
   abandoned registration dispatcher add-user-signal! and its two
   primitives were deleted per cr.org Finding 1; add_user_signal stays
   a plain C body.  The imp-1 thin dispatcher store_user_signal_events
   was deleted by imp-3 — gobble-input! now calls the Scheme
   store-user-signal-events! directly, so no C dispatcher is left.)
   These DEFUNs expose query/mutation/event-fill only.
   The list walk shape is repeated here rather than in
   find_user_signal_name: that function stays C and normal-context-only,
   serving --user-signal-name.  (Do not repoint find_user_signal_name
   at Scheme.)  */

/* Return an elisp list of the registered signal numbers.  The order is
   not semantically significant: store-user-signal-events! drains each
   signal independently.  (Nodes are prepended, so this reflects the
   linked-list traversal order, not registration order.)  */
DEFUN ("--user-signal-list", Fuser_signal_list, Suser_signal_list, 0, 0, 0,
       doc: /* Internal: return the list of registered user-signal
numbers.  Order is not significant.  */)
  (void)
{
  Lisp_Object result = Qnil;
  struct user_signal_info *p;

  for (p = user_signals; p; p = p->next)
    result = Fcons (make_fixnum (p->sig), result);
  return result;
}

/* Return SIG's current pending count (0 when not found — cannot happen
   for a sig taken from --user-signal-list).  */
DEFUN ("--user-signal-pending", Fuser_signal_pending, Suser_signal_pending,
       1, 1, 0,
       doc: /* Internal: return the number of pending signals for
user-signal SIG.  */)
  (Lisp_Object sig)
{
  struct user_signal_info *p;
  int s = XFIXNUM (sig);

  for (p = user_signals; p; p = p->next)
    if (p->sig == s)
      return make_fixnum (p->npending);
  return make_fixnum (0);
}

/* Decrement SIG's pending count by one and return the new count.
   Undefined (0) when SIG is not found.  */
DEFUN ("--user-signal-pending-decrement!",
       Fuser_signal_pending_decrement, Suser_signal_pending_decrement,
       1, 1, 0,
       doc: /* Internal: decrement user-signal SIG's pending count and
return the new count.  */)
  (Lisp_Object sig)
{
  struct user_signal_info *p;
  int s = XFIXNUM (sig);

  for (p = user_signals; p; p = p->next)
    if (p->sig == s)
      return make_fixnum (--p->npending);
  return make_fixnum (0);
}

static struct input_event ie_user_signal_event_storage;

/* Fill a USER_SIGNAL_EVENT input_event and return an ie-smob wrapping
   it.  CODE is the user-signal number.  The ie-smob aliases the static
   storage, which is reused on the next call — safe because
   kbd-buffer-store-event! copies the event out of the smob synchronously
   (via %--ie-copy) before the drain loop's next --ie-user-signal-event
   call.  Caller must pass the returned smob to kbd-buffer-store-event!
   in the same call, per the M9 ie-smob lifetime rule.  */
DEFUN ("--ie-user-signal-event", Fie_user_signal_event,
       Sie_user_signal_event, 1, 1, 0,
       doc: /* Internal: build a USER_SIGNAL_EVENT input_event for
user-signal CODE and return an ie-smob wrapping it.  */)
  (Lisp_Object code)
{
  memset (&ie_user_signal_event_storage, 0, sizeof ie_user_signal_event_storage);
  ie_user_signal_event_storage.kind = USER_SIGNAL_EVENT;
  ie_user_signal_event_storage.frame_or_window = selected_frame;
  ie_user_signal_event_storage.code = XFIXNUM (code);
  ie_user_signal_event_storage.device = Qt;
  ie_user_signal_event_storage.arg = Qnil;
  return ie_wrap (&ie_user_signal_event_storage);
}

/* M25 imp-4 — production event constructor for the TTY ASCII-keystroke
   decode loop.  The meta-key decode and quit-char batch-break decisions
   are made in Scheme (gobble.scm tty-read-avail-input!); this shim only
   fills a fresh struct input_event with the already-resolved CODE,
   MODIFIERS and FRAME-OR-WINDOW, kind fixed to ASCII_KEYSTROKE_EVENT,
   arg nil and device t.  Do NOT reuse --ie-test-event for this — that
   is a test-only helper.  The returned smob aliases the static storage,
   which is reused on the next call — safe because the caller passes it
   to kbd-buffer-store-event! synchronously (per the M9 ie-smob lifetime
   rule) before building the next event.  */
static struct input_event ie_ascii_keystroke_event_storage;

DEFUN ("--ie-ascii-keystroke-event", Fie_ascii_keystroke_event,
       Sie_ascii_keystroke_event, 3, 3, 0,
       doc: /* Internal: build an ASCII_KEYSTROKE_EVENT input_event and
return an ie-smob wrapping it.  CODE, MODIFIERS and FRAME-OR-WINDOW are
stored as given; kind is always ASCII_KEYSTROKE_EVENT, arg nil, device
Qt.  Caller must pass the returned smob to kbd-buffer-store-event! in
the same step, per the M9 ie-smob lifetime rule.  */)
  (Lisp_Object code, Lisp_Object modifiers, Lisp_Object frame_or_window)
{
  CHECK_FIXNUM (code);
  CHECK_FIXNUM (modifiers);
  memset (&ie_ascii_keystroke_event_storage, 0, sizeof ie_ascii_keystroke_event_storage);
  ie_ascii_keystroke_event_storage.kind = ASCII_KEYSTROKE_EVENT;
  ie_ascii_keystroke_event_storage.code = XFIXNUM (code);
  ie_ascii_keystroke_event_storage.modifiers = XFIXNUM (modifiers);
  ie_ascii_keystroke_event_storage.frame_or_window = frame_or_window;
  ie_ascii_keystroke_event_storage.arg = Qnil;
  ie_ascii_keystroke_event_storage.device = Qt;
  return ie_wrap (&ie_ascii_keystroke_event_storage);
}


/* M30 imp-4: menu_bar_one_keymap_changed_items and
   menu_bar_items_vector are defined above, near the cell table, so the
   table initializer can take their addresses. */

/* Infrastructure DEFUNs exposing menu-bar internals to Scheme.
   These let the Scheme side own menu_bar_items() while C still
   manages the static vectors (GC-protected via staticpro).  */

DEFUN ("--menu-bar-items-vector", Fmenu_bar_items_vector,
       Smenu_bar_items_vector, 0, 0, 0,
       doc: /* Return the menu-bar items vector, lazy-initializing to 24 slots if nil.  */)
  (void)
{
  if (NILP (menu_bar_items_vector))
    menu_bar_items_vector = make_nil_elisp_vector (24);
  return menu_bar_items_vector;
}

DEFUN ("--menu-bar-items-index", Fmenu_bar_items_index,
       Smenu_bar_items_index, 0, 0, 0,
       doc: /* Return the current fill index in the menu-bar items vector.
This is the slot count, not item count (÷4 for item count).  */)
  (void)
{
  return make_fixnum (menu_bar_items_index);
}

DEFUN ("--menu-bar-one-keymap-changed-items",
       Fmenu_bar_one_keymap_changed_items,
       Smenu_bar_one_keymap_changed_items, 0, 0, 0,
       doc: /* Return the per-keymap dedup list for menu-bar item construction.
Scheme consults this via `memq' before processing a binding to avoid
duplicate contributions from the same keymap.  */)
  (void)
{
  return menu_bar_one_keymap_changed_items;
}

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


Lisp_Object
menu_bar_items (Lisp_Object old)
{
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs menu-bar-items", "menu-bar-items");
  /* Scheme returns the vector directly (unlike tab/tool-bar which
     return a cons — menu-bar has no nitems out-param, downstream
     scans for the nil sentinel).  */
  return SCM_CALL_1 (proc, old);
}

Lisp_Object item_properties;

static void
ensure_item_properties_vector (void)
{
  if (!NILP (item_properties))
    CHECK_TYPE (PLAIN_VECTORP (item_properties), Qvectorp, item_properties);
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

DEFUN ("--x-popup-menu-1", Fx_popup_menu_1_shim,
       Sx_popup_menu_1_shim, 2, 2, 0,
       doc: /* FIX-20260829-guilemacs: internal: thin shim over C
x_popup_menu_1.  Unlike `x-popup-menu', does NOT call
init_raw_keybuf_count.  Used by the Scheme read-char-x-menu-prompt
port (M20).  */)
  (Lisp_Object position, Lisp_Object menu)
{
  return x_popup_menu_1 (position, menu);
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
   in the vector.  M30 imp-4: defined above, near the cell table, so
   the table initializer can take its address.  */

/* A vector holding the result of parse_tab_bar_item.  Layout is like
   the one for a single item in tab_bar_items_vector.  */

static Lisp_Object tab_bar_item_properties;

/* ntab_bar_items (the next free index in tab_bar_items_vector) is
   defined above, near the M30 cell table, so the table initializer can
   take its address.  */

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
   in the vector.  M30 imp-4: defined above, near the cell table, so
   the table initializer can take its address.  */

/* A vector holding the result of parse_tool_bar_item.  Layout is like
   the one for a single item in tool_bar_items_vector.  */

static Lisp_Object tool_bar_item_properties;

/* ntool_bar_items (the next free index in tool_bar_items_vector) is
   defined above, near the M30 cell table, so the table initializer can
   take its address.  */

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



/* Reading key sequences.  */

DEFUN ("--access-keymap", Faccess_keymap, Saccess_keymap, 2, 2, 0,
       doc: /* FIX-20260830-guilemacs: internal: thin shim over C
access_keymap.  Look up KEY in MAP with the fixed flags t_ok=1,
noinherit=0, autoload=1 -- the flags used by the Scheme callers
`rks-follow-key' and `rks-keyremap-step!'.  Not a general-purpose
keymap lookup: `lookup-key' has different prefix/t_ok semantics.  */)
  (Lisp_Object map, Lisp_Object key)
{
  return access_keymap (map, key, 1, 0, 1);
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

/* Field-level helper for reading an <rks-state> <keyremap> sub-record
   slot (used by --rks-loop-continue-p at depth 0; returns 0).  */
static int
rks_keyremap_field_int (int rks_slot, int km_slot)
{
  if (rks_state_depth == 0) return 0;
  SCM km = scm_struct_ref (rks_state_stack[rks_state_depth - 1],
                           scm_from_int (rks_slot));
  return rks_get_int (km, km_slot);
}

/* M6l — promote read_key_sequence's `fkey', `keytran', `indec' from
   locals to file-static.  C-9b retired them in favor of <keyremap>
   sub-records in <rks-state>; the Scheme side reads and rebases them
   through the srfi-9 accessors.  */

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

/* M6ab — promote new_binding.  Written by rks-follow-key + the
   rks-reduce-try-new-binding! inner loop; read by M6aa's install
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
/* imp-3: the reduction cascade (rks_reduce_rewind_one_keyremap /
   rks_reduce_rewind_keyremaps_to_last_real /
   rks_reduce_dispose_unbound_up_down / rks_reduce_try_new_binding /
   rks_reduce_strip_loop / --rks-reduce-mouse-event-loop) was ported to
   Scheme as rks-reduce-mouse-event-loop! in (emacs read-key-sequence);
   the C bodies are deleted.  See docs/keyboard.org §M6ad.  */

/* M6ac — bulk splice of the mouse-click prefix expansion (and
   menu-bar / tab-bar / tool-bar prefix insertion).  Returns one of:
     `replay-sequence' — buffer-switch or menu-bar fake prefix.
                         Caller goto replay_sequence.
     `replay-key' — mode-line / scroll-bar fake prefix.
                    Caller goto replay_key.
     `fall-through' — no decoration applied.  Caller continues to
                      the rks-follow-key dispatch.
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

/* M6ab — former --rks-follow-key-and-update-first-unbound bulk subr
   (17 lines), decomposed into --rks-follow-key shim + Scheme logic
   in rks-follow-key-and-update-first-unbound!.  imp-3 deleted the
   --rks-follow-key shim; rks-follow-key is now pure Scheme.
   See docs/m6-plan.org Step E3.  */

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

/* M6x — the three translation-map walks (input-decode-map,
   function-key-map, key-translation-map) plus the in-between
   fkey-shortcut were ported to Scheme in imp-3: rks-walk-translation-maps!
   (and its rks-walk-indec-scheme! / rks-fkey-shortcut-or-walk-scheme! /
   rks-walk-keytran-scheme! helpers) in (emacs read-key-sequence) drive
   rks-keyremap-step! over the state's keyremap records.  The C DEFUNs
   --rks-walk-indec / --rks-fkey-shortcut-or-walk / --rks-walk-keytran,
   their helpers rks_fkey_shortcut_advance / rks_fkey_walk, and the
   keyremap_step / test_undefined forward declarations are deleted.
   See docs/keyboard.org §M6x.  */

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

DEFUN ("--rks-replay-sequence-init-rest",
       Fc_rks_replay_sequence_init_rest,
       Sc_rks_replay_sequence_init_rest, 1, 1, 0,
       doc: /* Internal: complete the `replay_sequence:' init given a
pre-computed CURRENT-BINDING (from `--active-maps').  Sets the
file-statics rks_starting_buffer = current_buffer,
rks_current_binding = CURRENT-BINDING and rks_t = 0, clears
last_nonmenu_event, and -- when a <rks-state> is pushed -- writes the
record slots first_unbound = READ_KEY_ELTS + 1, current_binding =
CURRENT-BINDING and key_count = 0.  The rks_first_unbound file-static
is retired (M6m); the DEFUN writes that slot on the record via
rks_set_int.  Mirrors src/keyboard.c lines 10678-10688 (the body of
the replay_sequence: label minus the active_maps call, which the
Scheme caller performs).  */)
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

/* imp-3: keyremap_step and access_keymap_keyremap were ported to
   Scheme as rks-keyremap-step! / rks-access-keymap-keyremap in
   (emacs read-key-sequence) and their C bodies deleted (their only
   remaining caller was the walk DEFUNs, also deleted in imp-3).
   test_undefined was ported as rks-test-undefined?.  See
   docs/keyboard.org §M6h/§M6x.  */

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
     Step B.  This must precede the HAVE_TEXT_CONVERSION block below,
     which writes the record's disabled-conversion slot and therefore
     needs the record live (M21 imp-4 keeps the push in C for this
     reason; the entry-time resets and 3-scalar load moved into the
     rks-read-key-sequence-start! Scheme call, which resolves the
     record through --rks-state-current).  */
  {
    static SCM rks_make_state_proc = SCM_UNDEFINED;
    if (SCM_UNBNDP (rks_make_state_proc))
      rks_make_state_proc
        = scm_c_public_ref ("emacs read-key-sequence", "make-rks-state");
    SCM rec = SCM_CALL_0 (rks_make_state_proc);
    eassert (rks_state_depth < RKS_STATE_STACK_MAX);
    rks_state_stack[rks_state_depth++] = rec;
  }

  dynwind_begin ();

  /* M6q: push our keybuf onto the rks_keybuf_stack so the elisp
     accessor subrs (`--rks-keybuf-ref' / `--rks-keybuf-set') see
     it.  Pop on dynwind unwind so recursive (mouse-menu) calls
     restore the caller's keybuf cleanly.  See docs/keyboard.org §M6q.  */
  eassert (rks_keybuf_depth < RKS_KEYBUF_STACK_MAX);
  record_unwind_protect_int (restore_rks_keybuf_depth, rks_keybuf_depth);
  rks_keybuf_stack[rks_keybuf_depth++] = keybuf;

  /* Hand off the setup half to Scheme: 3-scalar load, prompt / pre-loop
     / replay-entire-sequence setup.  The record push above must precede
     this (the load resolves the record through --rks-state-current).  */
  {
    static SCM rks_start_proc = SCM_UNDEFINED;
    if (SCM_UNBNDP (rks_start_proc))
      rks_start_proc
        = scm_c_public_ref ("emacs read-key-sequence",
                            "rks-read-key-sequence-start!");
    scm_call_1 (rks_start_proc, prompt);
  }

#ifdef HAVE_TEXT_CONVERSION
  record_unwind_protect_int (restore_reading_key_sequence,
			     reading_key_sequence);
  reading_key_sequence = true;

  /* If text conversion is supposed to be disabled immediately, do
     it now.  Idempotent (the slot stays Qt and disable_text_conversion
     is no-op once set), so one-time entry is sufficient.  */
  if (disable_text_conversion_p)
    {
      disable_text_conversion ();
      record_unwind_protect_void (resume_text_conversion);
      Fc_set_rks_disabled_conversion (Qt);
    }
#endif /* HAVE_TEXT_CONVERSION */

  /* Hand off the state-machine / done orchestration to the Scheme
     state-machine half.  This runs *after* the text-conversion block
     above, restoring the pre-hoist ordering (prompt/pre-loop/replay
     setup, then reading_key_sequence/disable, then the state machine —
     see cr.org Finding 1).  Returns -1 (menu-reject) or the symbol
     `done'.  read_key_sequence_cmd is set only on the non-reject
     path (rks_t > 0), matching the pre-hoist ordering.  */
  {
    static SCM rks_run_proc = SCM_UNDEFINED;
    if (SCM_UNBNDP (rks_run_proc))
      rks_run_proc
        = scm_c_public_ref ("emacs read-key-sequence",
                            "rks-read-key-sequence-run!");
    SCM sm_result = scm_call_4 (rks_run_proc,
                                prompt,
                                can_return_switch_frame ? Qt : Qnil,
                                prevent_redisplay ? Qt : Qnil,
                                fix_current_buffer ? Qt : Qnil);
    if (FIXNUMP (sm_result) && XFIXNUM (sm_result) == -1)
      {
	/* Menu-reject: pop the state record too.  Pre-existing leak
	   fixed at M21 imp-4 (Finding D) — the old body returned
	   without popping on this path.  The pop happens here, before
	   dynwind_end — unlike the finish! path, which pops after
	   dynwind_end.  This asymmetry is safe: none of the unwind
	   handlers registered between dynwind_begin and dynwind_end
	   (restore_rks_keybuf_depth / restore_reading_key_sequence /
	   resume_text_conversion) read or write the state record.  */
	Fc_rks_state_stack_pop ();
	dynwind_end ();
	return -1;
      }
    if (rks_t > 0)
      read_key_sequence_cmd = rks_current_binding;
  }
  dynwind_end ();

  /* Scheme finish-half (only reached on the non-reject path):
     post-dynwind done body, 3-scalar store-back, record pop.  It
     returns the final key count, which we return directly.  */
  {
    static SCM rks_finish_proc = SCM_UNDEFINED;
    if (SCM_UNBNDP (rks_finish_proc))
      rks_finish_proc
        = scm_c_public_ref ("emacs read-key-sequence",
                            "rks-read-key-sequence-finish!");
    SCM result = scm_call_1 (rks_finish_proc,
                             dont_downcase_last ? Qt : Qnil);
    return XFIXNUM (result);
  }
}


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

/* FIX-20260829-guilemacs: internal shim for the M20 Scheme
   read-menu-command port.  The existing --read-key-sequence-and-vector
   hardcodes fix_current_buffer/prevent_redisplay = false, but C
   read_menu_command (keyboard.c:2627) needs true for both; reusing it
   would silently change TTY menu-navigation buffer/redisplay behavior.  */
DEFUN ("--rc-read-key-sequence-menu", Fc_rc_read_key_sequence_menu,
       Sc_rc_read_key_sequence_menu, 0, 0, 0,
       doc: /* FIX-20260829-guilemacs: internal: invoke the C
read_key_sequence state machine with the exact fixed flags
read_menu_command uses (prompt nil, dont-downcase-last nil,
can-return-switch-frame t, fix-current-buffer t, prevent-redisplay t,
disable-text-conversion nil).  Returns the read keys as a Lisp vector
of length i, or the fixnum -1 on quit (i == -1).  Used by the Scheme
read-menu-command port (M20).  */)
  (void)
{
  Lisp_Object keybuf[READ_KEY_ELTS];
  int i = read_key_sequence (keybuf, Qnil, false, true, true, true,
                             false);
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

DEFUN ("--recent-keys-index-set!", Frecent_keys_index_set, Srecent_keys_index_set,
       1, 1, 0,
       doc: /* Internal: set the next-write index into the recent-keys ring.
Raw setter for the int global recent_keys_index, for the Scheme record-char
port (M17).  Caller owns the wrap-around arithmetic.  Returns nil.  */)
  (Lisp_Object index)
{
  CHECK_FIXNAT (index);
  recent_keys_index = XFIXNAT (index);
  return Qnil;
}

DEFUN ("--total-keys-set!", Ftotal_keys_set, Stotal_keys_set, 1, 1, 0,
       doc: /* Internal: set the recorded-key count (capped at the ring size).
Raw setter for the int global total_keys, for the Scheme record-char port
(M17).  Caller owns the increment/decrement arithmetic.  Returns nil.  */)
  (Lisp_Object n)
{
  CHECK_FIXNAT (n);
  total_keys = XFIXNAT (n);
  return Qnil;
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

DEFUN ("--recent-keys-ring-set!", Frecent_keys_ring_set, Srecent_keys_ring_set,
       1, 1, 0,
       doc: /* Internal: replace the raw recent-keys ring vector.
FIX-20260831-guilemacs: raw setter for the Scheme lossage-size ring
resize (M22 imp-1).  Caller owns building the replacement vector.
Returns nil.  */)
  (Lisp_Object vec)
{
  CHECK_VECTOR (vec);
  recent_keys = vec;
  return Qnil;
}

DEFUN ("--lossage-limit-set!", Flossage_limit_set, Slossage_limit_set,
       1, 1, 0,
       doc: /* Internal: set the recent-keys ring size.
FIX-20260831-guilemacs: raw setter for the Scheme lossage-size ring
resize (M22 imp-1).  Returns nil.  */)
  (Lisp_Object size)
{
  CHECK_FIXNAT (size);
  lossage_limit = XFIXNAT (size);
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

DEFUN ("--dribble-open-p", Fdribble_open_p, Sdribble_open_p, 0, 0, 0,
       doc: /* Internal: return non-nil when a dribble file is currently open.
Reads the static FILE *dribble (src/keyboard.c:252) for the Scheme
record-char / open-dribble-file port (M17).  */)
  (void)
{
  return dribble ? Qt : Qnil;
}

DEFUN ("--dribble-write-event", Fdribble_write_event, Sdribble_write_event,
       1, 1, 0,
       doc: /* Internal: write the input event C to the open dribble file,
mirroring the tail of C record_char (src/keyboard.c, the `if (dribble ...)'
block).  If no dribble file is open, or a kbd macro is executing, this is a
no-op.  The FILE* itself stays C-owned.  Returns nil.  */)
  (Lisp_Object c)
{
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
  return Qnil;
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
  /* M26 imp-1: dispatch to (emacs interrupt) -- see brief.org M26 imp-1.  */
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs interrupt", "suspend-emacs");
  return SCM_CALL_1 (proc, stuffstring);
}

/* If STUFFSTRING is a string, stuff its contents as pending terminal input.
   Then in any case stuff anything Emacs has read ahead and not used.  */

/* M22 imp-3 — the body moved to (emacs kbd-buffer) stuff-buffered-input.
   This copy stays as the C fallback for the fatal-signal path only:
   terminate_due_to_signal (src/emacs.c:421) sets fatal_error_in_progress
   before calling shut_down_emacs, which calls stuff_buffered_input.  From
   a signal handler the Guile VM may be interrupted mid-eval, so calling
   into Scheme there is unsafe.  See docs/m22-plan.org §imp-3 (Finding D).  */
static void
stuff_buffered_input_c (Lisp_Object stuffstring)
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
stuff_buffered_input (Lisp_Object stuffstring)
{
  /* Fatal-signal path: fall back to the C body (see above).  */
  if (fatal_error_in_progress)
    {
      stuff_buffered_input_c (stuffstring);
      return;
    }
#ifdef SIGTSTP
  /* M22 imp-3: dispatch to (emacs kbd-buffer).  Keeps external linkage
     and signature — src/emacs.c:2825 and Fsuspend_emacs call this.  The
     #ifdef SIGTSTP guard absorbs the C body's own guard: on a build
     without SIGTSTP the whole function is a no-op, exactly like the old
     body (its entire contents sat inside #ifdef SIGTSTP).  */
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs kbd-buffer", "stuff-buffered-input");
  SCM_CALL_1 (proc, stuffstring);
#endif /* SIGTSTP */
}

DEFUN ("--stuff-char", Fc_stuff_char, Sc_stuff_char, 1, 1, 0,
       doc: /* FIX-20260901-guilemacs: Internal: stuff one char N into the
tty input queue (wraps stuff_char).  No-op when SIGTSTP is not
defined, so the Scheme body never needs to know about the guard.  */)
  (Lisp_Object n)
{
#ifdef SIGTSTP
  CHECK_FIXNAT (n);
  stuff_char (XFIXNAT (n));
#endif
  return Qnil;
}

DEFUN ("--stuff-string", Fc_stuff_string, Sc_stuff_string, 1, 1, 0,
       doc: /* FIX-20260901-guilemacs: Internal: stuff S's bytes plus a
trailing newline into the tty input queue.  No-op when SIGTSTP is not
defined.  Mirrors the string block of the C stuff_buffered_input
(SDATA/SBYTES loop) that Scheme cannot express over an elisp string.  */)
  (Lisp_Object s)
{
#ifdef SIGTSTP
  if (STRINGP (s))
    {
      unsigned char *p = SDATA (s);
      ptrdiff_t count = SBYTES (s);
      while (count-- > 0)
	stuff_char (*p++);
      stuff_char ('\n');
    }
#endif
  return Qnil;
}

DEFUN ("--input-pending-set!", Fc_input_pending_set, Sc_input_pending_set,
       1, 1, 0,
       doc: /* FIX-20260901-guilemacs: Internal: hard-set the C global
`input_pending' to t/nil from V.  Unlike --update-input-pending (which
recomputes via readable_events), this is a direct assignment — the
stuff_buffered_input drain must force it false regardless of what else
is pending.  */)
  (Lisp_Object v)
{
  input_pending = !NILP (v);
  return Qnil;
}

/* M27 imp-3 — three absolute reset shims for init_keyboard.  Each
   existing reset accessor is only a getter or a delta step; the
   init_keyboard port needs an absolute write, so these three cells get
   dedicated shims (brief.org M27 imp-3).  */

DEFUN ("--command-loop-level-set!", Fc_command_loop_level_set,
       Sc_command_loop_level_set, 1, 1, 0,
       doc: /* FIX-20260908-guilemacs: Internal: hard-set the C global
`command_loop_level' to N (a fixnum).  init_keyboard needs the absolute
-1; the existing increment!/decrement! pair only step the counter.
Returns nil.  */)
  (Lisp_Object n)
{
  CHECK_FIXNUM (n);
  command_loop_level = XFIXNUM (n);
  return Qnil;
}

DEFUN ("--timer-idleness-reset!", Fc_timer_idleness_reset,
       Sc_timer_idleness_reset, 0, 0, 0,
       doc: /* FIX-20260908-guilemacs: Internal: reset
timer_idleness_start_time to invalid_timespec ().  The only existing
shim --timer-idleness-now is a getter (elapsed idle) and cannot reset;
init_keyboard is where the absolute invalid write happens.  Returns
nil.  */)
  (void)
{
  timer_idleness_start_time = invalid_timespec ();
  return Qnil;
}

DEFUN ("--interrupt-input-blocked-set!", Fc_interrupt_input_blocked_set,
       Sc_interrupt_input_blocked_set, 1, 1, 0,
       doc: /* FIX-20260908-guilemacs: Internal: hard-set the volatile
int `interrupt_input_blocked' to N (a fixnum).  blockinput.h only
increments/decrements it; init_keyboard is the one place that needs an
absolute 0.  Returns nil.  */)
  (Lisp_Object n)
{
  CHECK_FIXNUM (n);
  interrupt_input_blocked = XFIXNUM (n);
  return Qnil;
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

DEFUN ("--force-quit-count", Fc_force_quit_count, Sc_force_quit_count, 0, 0, 0,
       doc: /* FIX-20260907-guilemacs: Internal: return the C force_quit_count
global as a fixnum.  M26 imp-3 (emacs interrupt) handle-interrupt needs it to
reproduce handle_interrupt's arm-2 force-quit bump on the normal path.  */)
  (void)
{
  return make_fixnum (force_quit_count);
}

DEFUN ("--set-force-quit-count!", Fc_set_force_quit_count, Sc_set_force_quit_count, 1, 1, 0,
       doc: /* FIX-20260907-guilemacs: Internal: set the C force_quit_count
global to COUNT (a fixnum).  M26 imp-3 (emacs interrupt) handle-interrupt needs it
to reproduce handle_interrupt's arm-2 force-quit bump on the normal path.  */)
  (Lisp_Object count)
{
  CHECK_FIXNUM (count);
  force_quit_count = XFIXNUM (count);
  return count;
}

DEFUN ("--restore-signal-mask", Fc_restore_signal_mask, Sc_restore_signal_mask, 0, 0, 0,
       doc: /* FIX-20260907-guilemacs: Internal: reset the signal mask to the
empty set, pthread_sigmask (SIG_SETMASK, &empty_mask, 0).  Reproduces the tail of
C handle_interrupt (src/keyboard.c) for M26 imp-3 (emacs interrupt)
handle-interrupt on the normal path.  */)
  (void)
{
  pthread_sigmask (SIG_SETMASK, &empty_mask, 0);
  return Qnil;
}

/* M26 imp-3 — arm 1 of handle_interrupt: the emergency-escape prompt.  The body
   below was extracted verbatim from C handle_interrupt (was lines 11241-11309),
   preserving the #ifdef SIGTSTP arm byte for byte; the dropped-platform arms
   are gone.  It stays C on BOTH the signal and the normal path.  See brief.org
   M26 imp-3.  */
static void
handle_interrupt_emergency_escape (bool in_signal_handler)
{
  char c;

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

  write_stdout ("Emacs is resuming after an emergency escape.\n");

  write_stdout ("Auto-save? (y or n) ");
  c = read_stdin ();
  if (c == 'y' || c == 'Y')
    {
      Fdo_auto_save (Qt, Qnil);
      write_stdout ("Auto-save done\n");
    }
  while (c != '\n')
    c = read_stdin ();

  write_stdout ("Abort (and dump core)? (y or n) ");
  c = read_stdin ();
  if (c == 'y' || c == 'Y')
	emacs_abort ();
  while (c != '\n')
	c = read_stdin ();
  write_stdout ("Continuing...\n");
  init_all_sys_modes ();
}

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
  cancel_echoing ();

  /* XXX This code needs to be revised for multi-tty support.  */
  if (!NILP (Vquit_flag) && get_named_terminal (dev_tty))
    handle_interrupt_emergency_escape (in_signal_handler);  /* arm 1, C */
  else if (in_signal_handler)
    {
      /* arm 2 + tail, SIGINT path.  Straight-line C copy.
	 (signal-handler-no-guile-vm-call: never call into Guile from a
	 signal handler.)  */
      int count = NILP (Vquit_flag) ? 1 : force_quit_count + 1;
      force_quit_count = count;
      if (count == 3)
	Vinhibit_quit = Qnil;
      Vquit_flag = Qt;
    }
  else
    {
      /* arm 2 + tail, normal path -> (emacs interrupt) handle-interrupt.  */
      static SCM proc = SCM_UNDEFINED;
      if (SCM_UNBNDP (proc))
	proc = scm_c_public_ref ("emacs interrupt", "handle-interrupt");
      SCM_CALL_0 (proc);
      return;   /* Scheme body runs arm 2 + tail.  */
    }

  /* tail — arm 1 (both paths) and arm 2 signal path.  */
  pthread_sigmask (SIG_SETMASK, &empty_mask, 0);

#ifdef THREADS_ENABLED
  /* If we were called from a signal handler, we must be in the main
     thread, see deliver_process_signal.  So we must make sure the
     main thread holds the global lock.  */
  if (in_signal_handler)
    maybe_reacquire_global_lock ();
#endif
  if (waiting_for_input && !echoing)
    quit_throw_to_read_char (in_signal_handler);
}

/* M26 imp-2 — quit_throw_to_read_char (from_signal == false) cutover
   shims.  Thin wrappers over C-only helpers the Scheme body
   (mod/emacs/interrupt.scm quit-throw-to-read-char) needs but that
   have no Scheme port.  See brief.org M26 imp-2.  */
DEFUN ("--clear-input-available-clear-time!",
       Fc_clear_input_available_clear_time,
       Sc_clear_input_available_clear_time, 0, 0, 0,
       doc: /* FIX-20260907-guilemacs: Internal: clear the C global
input_available_clear_time.  This is the other half of the real
clear_waiting_for_input (src/keyboard.c:11153); the existing
--clear-waiting-for-input (src/keyboard.c:2103) only clears
waiting_for_input, not input_available_clear_time.  The Scheme
quit-throw-to-read-char calls this together with --clear-waiting-for-input
to reproduce clear_waiting_for_input's full effect without touching
either existing function.  */)
  (void)
{
  input_available_clear_time = 0;
  return Qnil;
}

DEFUN ("--switch-to-frame!", Fc_switch_to_frame, Sc_switch_to_frame, 1, 1, 0,
       doc: /* FIX-20260907-guilemacs: Internal: switch the selected
frame to FRAME by calling do_switch_frame (make_lispy_switch_frame
(frame), 0, 0, Qnil) — NO-QUIT/PREVIOUS/STEAL all false.  Wraps both
C-only helpers in one call; no Scheme port exists for do_switch_frame
or make_lispy_switch_frame (frame.c / keyboard.c internals).  The
Scheme quit-throw-to-read-char does its own FRAMEP + EQ guard and calls
this shim only when a switch is needed.  */)
  (Lisp_Object frame)
{
  do_switch_frame (make_lispy_switch_frame (frame), 0, 0, Qnil);
  return Qnil;
}

/* Handle a C-g by making read_char return C-g.  */

static void
quit_throw_to_read_char (bool from_signal)
{
  if (from_signal)
    {
      /* M26 imp-2: real-signal path stays C.  Never call into Guile
         from the SIGINT handler (signal-handler-no-guile-vm-call,
         docs/kb.org).  Straight-line copy of the pre-imp-2 body —
         do not rewrite it, only relocate it under this guard.  */
      clear_waiting_for_input ();
      input_pending = false;

      Vunread_command_events = Qnil;

      if (FRAMEP (internal_last_event_frame)
          && !EQ (internal_last_event_frame, selected_frame))
        do_switch_frame (make_lispy_switch_frame (internal_last_event_frame),
                         0, 0, Qnil);

      abort_to_prompt (getctag, SCM_EOL);
    }

  /* M26 imp-2: normal-context path -> (emacs interrupt)
     quit-throw-to-read-char.  See brief.org M26 imp-2.  */
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs interrupt", "quit-throw-to-read-char");
  SCM_CALL_0 (proc);
  emacs_abort ();  /* Not reached: the Scheme body ends in abort-to-prompt.  */
}

DEFUN ("set-input-interrupt-mode", Fset_input_interrupt_mode,
       Sset_input_interrupt_mode, 1, 1, 0,
       doc: /* Set interrupt mode of reading keyboard input.
If INTERRUPT is non-nil, Emacs will use input interrupts;
otherwise Emacs uses CBREAK mode.

See also `current-input-mode'.  */)
  (Lisp_Object interrupt)
{
  /* M22 imp-3: dispatch to (emacs read-key-sequence).  The X-override
     and USABLE_SIGIO/SIGPOLL branches are reproduced by the Scheme
     body through the M22 imp-3 shims.  */
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs read-key-sequence", "set-input-interrupt-mode");
  return SCM_CALL_1 (proc, interrupt);
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
  /* M22 imp-3: dispatch to (emacs read-key-sequence).  The terminal-arg
     decode and reset/init dance are in the Scheme body.  */
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs read-key-sequence", "set-output-flow-control");
  return SCM_CALL_2 (proc, flow, terminal);
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
  /* M22 imp-3: dispatch to (emacs read-key-sequence).  The META value
     mapping (nil/t/encoded/else -> 0/1/3/2), terminal-arg decode and
     reset/init dance are in the Scheme body.  */
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs read-key-sequence", "set-input-meta-mode");
  return SCM_CALL_2 (proc, meta, terminal);
}

DEFUN ("set-quit-char", Fset_quit_char, Sset_quit_char, 1, 1, 0,
       doc: /* Specify character used for quitting.
QUIT must be an ASCII character.

This function only has an effect on the controlling tty of the Emacs
process.

See also `current-input-mode'.  */)
  (Lisp_Object quit)
{
  /* M22 imp-3: dispatch to (emacs read-key-sequence).  The controlling-tty
     resolution, ASCII-char error, mask and reset/init dance are in the
     Scheme body.  */
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs read-key-sequence", "set-quit-char");
  return SCM_CALL_1 (proc, quit);
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

DEFUN ("--interrupts-deferred-p", Fc_interrupts_deferred_p,
       Sc_interrupts_deferred_p, 0, 0, 0,
       doc: /* Internal: t if the C global `interrupts_deferred' is
non-zero.  */)
  (void)
{
  return interrupts_deferred ? Qt : Qnil;
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

/* M22 imp-3 — the input-mode quartet (set-input-interrupt-mode,
   set-output-flow-control, set-input-meta-mode, set-quit-char) moved to
   (emacs read-key-sequence).  These shims give the Scheme bodies the
   per-terminal and controlling-tty state they need.  See
   docs/m22-plan.org §imp-3 (Findings A/B).  */

/* Decode TERMINAL (a terminal object, a frame, or nil = selected frame)
   to its tty_display_info, or NULL if it is not a tty terminal.  */
static struct tty_display_info *
m22_tty_of_terminal (Lisp_Object terminal)
{
  struct terminal *t = decode_tty_terminal (terminal);
  return t ? t->display_info.tty : NULL;
}

/* The controlling tty's tty_display_info (get_named_terminal of the
   dev_tty global), or NULL if there is no controlling tty.  */
static struct tty_display_info *
m22_controlling_tty (void)
{
  struct terminal *t = get_named_terminal (dev_tty);
  return t ? t->display_info.tty : NULL;
}

DEFUN ("--decode-tty-terminal-p", Fc_decode_tty_terminal_p,
       Sc_decode_tty_terminal_p, 1, 1, 0,
       doc: /* FIX-20260901-guilemacs: Internal: t if TERMINAL (a terminal
object, a frame, or nil = selected frame) decodes to a tty terminal.  */)
  (Lisp_Object terminal)
{
  return m22_tty_of_terminal (terminal) ? Qt : Qnil;
}

DEFUN ("--tty-flow-control", Fc_tty_flow_control, Sc_tty_flow_control, 1, 1, 0,
       doc: /* FIX-20260901-guilemacs: Internal: return TERMINAL's
flow_control flag (t/nil).  Caller must have confirmed
--decode-tty-terminal-p first; nil is returned if TERMINAL does not
decode to a tty.  */)
  (Lisp_Object terminal)
{
  struct tty_display_info *tty = m22_tty_of_terminal (terminal);
  return tty ? (tty->flow_control ? Qt : Qnil) : Qnil;
}

DEFUN ("--tty-flow-control-set!", Fc_tty_flow_control_set,
       Sc_tty_flow_control_set, 2, 2, 0,
       doc: /* FIX-20260901-guilemacs: Internal: set TERMINAL's
flow_control flag to t/nil from FLOW.  Caller must have confirmed
--decode-tty-terminal-p first; no-op if TERMINAL does not decode to a
tty.  */)
  (Lisp_Object terminal, Lisp_Object flow)
{
  struct tty_display_info *tty = m22_tty_of_terminal (terminal);
  if (tty)
    tty->flow_control = !NILP (flow);
  return Qnil;
}

DEFUN ("--tty-meta-key", Fc_tty_meta_key, Sc_tty_meta_key, 1, 1, 0,
       doc: /* FIX-20260901-guilemacs: Internal: return TERMINAL's meta_key
as a small integer (0..3).  Caller must have confirmed
--decode-tty-terminal-p first; 0 is returned if TERMINAL does not
decode to a tty.  */)
  (Lisp_Object terminal)
{
  struct tty_display_info *tty = m22_tty_of_terminal (terminal);
  return make_fixnum (tty ? tty->meta_key : 0);
}

DEFUN ("--tty-meta-key-set!", Fc_tty_meta_key_set, Sc_tty_meta_key_set, 2, 2, 0,
       doc: /* FIX-20260901-guilemacs: Internal: set TERMINAL's meta_key to
META (0..3).  Caller must have confirmed --decode-tty-terminal-p first;
no-op if TERMINAL does not decode to a tty.  */)
  (Lisp_Object terminal, Lisp_Object meta)
{
  struct tty_display_info *tty = m22_tty_of_terminal (terminal);
  if (tty)
    tty->meta_key = XFIXNUM (meta);
  return Qnil;
}

/* M25 imp-4 — TTY read-path shims for (emacs gobble) tty-read-avail-input!.
   The dispatcher tty_read_avail_input already ran the raw guards (live,
   tty-typed, initted, non-suspended terminal) before calling Scheme, so
   these assume a live terminal; m22_tty_of_terminal returns NULL only for
   a non-tty decode and the shims defensively return a neutral value then.  */

DEFUN ("--tty-bytes-readable", Fc_tty_bytes_readable,
       Sc_tty_bytes_readable, 1, 1, 0,
       doc: /* FIX-20260901-guilemacs: Internal: how many bytes are
available on TERMINAL's tty, via the USABLE_FIONREAD ioctl only.  Caller
must have confirmed --decode-tty-terminal-p first (the raw guards already
ran in C).  Returns 0 for nothing available, the ioctl byte count for
some available, or -2 when the ioctl fails and !noninteractive (matching
the original C return -2 / close-terminal arm); when noninteractive and
the ioctl fails, returns 0.  Returns 0 if TERMINAL does not decode to a
tty.  */)
  (Lisp_Object terminal)
{
  struct tty_display_info *tty = m22_tty_of_terminal (terminal);
  int n_to_read = 0;

  if (!tty)
    return make_fixnum (0);

  if (ioctl (fileno (tty->input), FIONREAD, &n_to_read) < 0)
    {
      if (!noninteractive)
        return make_fixnum (-2); /* Close this terminal.  */
      else
        n_to_read = 0;
    }
  return make_fixnum (n_to_read);
}

DEFUN ("--tty-read-nonblocking", Fc_tty_read_nonblocking,
       Sc_tty_read_nonblocking, 2, 2, 0,
       doc: /* FIX-20260901-guilemacs: Internal: emacs_read up to N bytes
from TERMINAL's tty into a fresh N-byte bytevector without blocking.
Returns (nread . bytevector), where nread may be less than N.  Returns
the bare fixnum -2 when the read failed with errno==EIO (matching the
original C close-terminal arm).  Otherwise the raw emacs_read result is
the pair's car (0, a short count, or a bare -1 — never swallowed here);
the caller decides what to do with a negative count.  Returns (0 . empty)
if TERMINAL does not decode to a tty.  */)
  (Lisp_Object terminal, Lisp_Object n)
{
  struct tty_display_info *tty = m22_tty_of_terminal (terminal);
  int nbytes = XFIXNUM (n);
  Lisp_Object bv = scm_c_make_bytevector (nbytes);
  int nread;

  if (!tty)
    return scm_cons (make_fixnum (0), bv);

  nread = emacs_read (fileno (tty->input), SCM_BYTEVECTOR_CONTENTS (bv),
                      nbytes);
  /* POSIX infers that processes which are not in the session leader's
     process group won't get SIGHUPs at logout time.  BSDI adheres to
     this part standard and returns -1 from read (0) with errno==EIO
     when the control tty is taken away.
     Jeffrey Honig <jch@bsdi.com> says this is generally safe.  */
  if (nread == -1 && errno == EIO)
    return make_fixnum (-2);  /* Close this terminal.  */
  return scm_cons (make_fixnum (nread), bv);
}

DEFUN ("--tty-top-frame", Fc_tty_top_frame, Sc_tty_top_frame, 1, 1, 0,
       doc: /* FIX-20260901-guilemacs: Internal: return the top_frame of
TERMINAL's tty — the frame_or_window used for each keystroke event from
that terminal.  Caller must have confirmed --decode-tty-terminal-p first;
nil if TERMINAL does not decode to a tty.  */)
  (Lisp_Object terminal)
{
  struct tty_display_info *tty = m22_tty_of_terminal (terminal);
  return tty ? tty->top_frame : Qnil;
}

DEFUN ("--reset-sys-modes", Fc_reset_sys_modes, Sc_reset_sys_modes, 1, 1, 0,
       doc: /* FIX-20260901-guilemacs: Internal: reset the terminal modes of
TERMINAL's tty (wraps reset_sys_modes (tty)).  No-op when TERMINAL does
not decode to a tty.  */)
  (Lisp_Object terminal)
{
  struct tty_display_info *tty = m22_tty_of_terminal (terminal);
  if (tty)
    reset_sys_modes (tty);
  return Qnil;
}

DEFUN ("--init-sys-modes", Fc_init_sys_modes, Sc_init_sys_modes, 1, 1, 0,
       doc: /* FIX-20260901-guilemacs: Internal: initialize the terminal
modes of TERMINAL's tty (wraps init_sys_modes (tty)).  No-op when
TERMINAL does not decode to a tty.  */)
  (Lisp_Object terminal)
{
  struct tty_display_info *tty = m22_tty_of_terminal (terminal);
  if (tty)
    init_sys_modes (tty);
  return Qnil;
}

DEFUN ("--reset-all-sys-modes", Fc_reset_all_sys_modes, Sc_reset_all_sys_modes,
       0, 0, 0,
       doc: /* FIX-20260901-guilemacs: Internal: reset all terminal modes
(wraps reset_all_sys_modes).  */)
  (void)
{
  reset_all_sys_modes ();
  return Qnil;
}

DEFUN ("--init-all-sys-modes", Fc_init_all_sys_modes, Sc_init_all_sys_modes,
       0, 0, 0,
       doc: /* FIX-20260901-guilemacs: Internal: initialize all terminal
modes (wraps init_all_sys_modes).  */)
  (void)
{
  init_all_sys_modes ();
  return Qnil;
}

DEFUN ("--multiple-tty-frames?", Fc_multiple_tty_frames_p,
       Sc_multiple_tty_frames_p, 0, 0, 0,
       doc: /* FIX-20260907-guilemacs: Internal: return t if more than one
tty is open (tty_list has a next element), else nil.  Ports the
`if (tty_list && tty_list->next) error (...)' guard in the old
Fsuspend_emacs body; tty_list is a raw C global (src/term.c) not
Lisp-visible any other way.  */)
  (void)
{
  return (tty_list && tty_list->next) ? Qt : Qnil;
}

DEFUN ("--tty-size", Fc_tty_size, Sc_tty_size, 0, 0, 0,
       doc: /* FIX-20260907-guilemacs: Internal: return the controlling
tty's current size as (WIDTH . HEIGHT) fixnums.  Wraps the
get_tty_size (fileno (CURTTY ()->input), &width, &height) call the old
Fsuspend_emacs made (both before and after the suspend).  */)
  (void)
{
  int width, height;
  get_tty_size (fileno (CURTTY ()->input), &width, &height);
  return Fcons (make_fixnum (width), make_fixnum (height));
}

DEFUN ("--sys-subshell", Fc_sys_subshell, Sc_sys_subshell, 0, 0, 0,
       doc: /* FIX-20260907-guilemacs: Internal: run a subshell via
sys_subshell (), return nil.  Mirrors the --sys-suspend shim for the
cannot_suspend branch of the ported suspend-emacs.  Only smoke-tested,
never exercised in the test suite (it would stop or fork the runner).  */)
  (void)
{
  sys_subshell ();
  return Qnil;
}

DEFUN ("--change-frame-size", Fc_change_frame_size, Sc_change_frame_size,
       2, 2, 0,
       doc: /* FIX-20260907-guilemacs: Internal: resize SELECTED_FRAME to
WIDTH x HEIGHT.  Hardcodes PRETEND/DELAY/SAFE = false, which is always
the case at the single (old Fsuspend_emacs) call site.  */)
  (Lisp_Object width, Lisp_Object height)
{
  change_frame_size (SELECTED_FRAME (), XFIXNUM (width), XFIXNUM (height),
                     false, false, false);
  return Qnil;
}

DEFUN ("--controlling-tty-meta-key", Fc_controlling_tty_meta_key,
       Sc_controlling_tty_meta_key, 0, 0, 0,
       doc: /* FIX-20260901-guilemacs: Internal: return the controlling
tty's meta_key (0..3), or nil when there is no controlling tty.
Sources from get_named_terminal (dev_tty), NOT from a Lisp TERMINAL
argument.  */)
  (void)
{
  struct tty_display_info *tty = m22_controlling_tty ();
  return tty ? make_fixnum (tty->meta_key) : Qnil;
}

DEFUN ("--reset-controlling-tty-sys-modes", Fc_reset_controlling_tty_sys_modes,
       Sc_reset_controlling_tty_sys_modes, 0, 0, 0,
       doc: /* FIX-20260901-guilemacs: Internal: reset the controlling
tty's terminal modes (wraps reset_sys_modes).  No-op when there is no
controlling tty.  */)
  (void)
{
  struct tty_display_info *tty = m22_controlling_tty ();
  if (tty)
    reset_sys_modes (tty);
  return Qnil;
}

DEFUN ("--init-controlling-tty-sys-modes", Fc_init_controlling_tty_sys_modes,
       Sc_init_controlling_tty_sys_modes, 0, 0, 0,
       doc: /* FIX-20260901-guilemacs: Internal: initialize the controlling
tty's terminal modes (wraps init_sys_modes).  No-op when there is no
controlling tty.  */)
  (void)
{
  struct tty_display_info *tty = m22_controlling_tty ();
  if (tty)
    init_sys_modes (tty);
  return Qnil;
}

DEFUN ("--quit-char-set!", Fc_quit_char_set, Sc_quit_char_set, 1, 1, 0,
       doc: /* FIX-20260901-guilemacs: Internal: set the C global quit_char
to N.  */)
  (Lisp_Object n)
{
  CHECK_FIXNAT (n);
  quit_char = XFIXNAT (n);
  return Qnil;
}

DEFUN ("--sigio-or-poll-usable-p", Fc_sigio_or_poll_usable_p,
       Sc_sigio_or_poll_usable_p, 0, 0, 0,
       doc: /* FIX-20260901-guilemacs: Internal: t when either USABLE_SIGIO
or USABLE_SIGPOLL is defined (i.e. set-input-interrupt-mode's first
branch is live).  */)
  (void)
{
#if defined (USABLE_SIGIO) || defined (USABLE_SIGPOLL)
  return Qt;
#else
  return Qnil;
#endif
}

DEFUN ("--x-display-forces-interrupt-p", Fc_x_display_forces_interrupt_p,
       Sc_x_display_forces_interrupt_p, 0, 0, 0,
       doc: /* FIX-20260901-guilemacs: Internal: t when the "when using X,
don't give the user a real choice" override applies: HAVE_X_WINDOWS
with a live X display forces new_interrupt_input = true regardless of
the INTERRUPT argument.  */)
  (void)
{
#if defined (USABLE_SIGIO) || defined (USABLE_SIGPOLL)
#ifdef HAVE_X_WINDOWS
  return (x_display_list != NULL) ? Qt : Qnil;
#else
  return Qnil;
#endif
#else
  return Qnil;
#endif
}

DEFUN ("--interrupt-input-set!", Fc_interrupt_input_set,
       Sc_interrupt_input_set, 1, 1, 0,
       doc: /* FIX-20260901-guilemacs: Internal: set the C global
`interrupt_input' to t/nil from V.  */)
  (Lisp_Object v)
{
  interrupt_input = !NILP (v);
  return Qnil;
}

DEFUN ("--start-polling", Fc_start_polling, Sc_start_polling, 0, 0, 0,
       doc: /* FIX-20260901-guilemacs: Internal: call start_polling ().
No-op when POLL_FOR_INPUT is not defined.  */)
  (void)
{
#ifdef POLL_FOR_INPUT
  start_polling ();
#endif
  return Qnil;
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
  static SCM proc = SCM_UNDEFINED;
  Lisp_Object frame_obj, window_or_nil;
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
      window_or_nil = frame_or_window;
      frame_obj = w->frame;
    }
  else
    {
      CHECK_LIVE_FRAME (frame_or_window);
      frame_obj = frame_or_window;
      window_or_nil = Qnil;
    }

  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs lispy-position", "posn-at-x-y");
  return SCM_CALL_5 (proc, frame_obj, window_or_nil, x, y, whole);
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
  /* M27 imp-2 — raw C-only fields stay here; the Lisp_Object field
     defaults and keymap wiring dispatch to (emacs kboard-lifecycle)
     init-kboard!.  */
  kb->immediate_echo = false;      /* no per-kb setter exists */
  kb->kbd_macro_buffer = 0;        /* raw pointer; macros.c writes it */
  kb->kbd_macro_bufsize = 0;       /* raw size; macros.c writes it */
  kb->reference_count = 0;         /* raw int; terminal.c / term files manage it */
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs kboard-lifecycle", "init-kboard!");
  SCM_CALL_2 (proc, make_kboard_smob (kb), type);
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
  /* Dispatch the 19 file-static resets to Scheme (brief.org M27 imp-3).
     init_keyboard runs from src/emacs.c after load_guile_prelude and
     syms_of_keyboard, so (emacs keyboard-init) is loaded and its C
     DEFUNs are registered when this dispatcher fires (no
     early-init-c-body-before-defun-registration hazard).  Each reset
     cell is written by init-keyboard! in C order.  The C body keeps
     only the current-kboard re-init, the sigaction installs, and the
     signal / poll arms below.  */
  static SCM proc = SCM_UNDEFINED;
  if (SCM_UNBNDP (proc))
    proc = scm_c_public_ref ("emacs keyboard-init", "init-keyboard!");
  SCM_CALL_0 (proc);

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
      /* For systems with SysV TERMIO, C-g is set up for both SIGINT and
	 SIGQUIT and we can't tell which one it will give us.  */
      sigaction (SIGQUIT, &action, 0);
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

void
syms_of_keyboard (void)
{
#include "keyboard.x"

  /* M23 imp-4 — the cross-file DEFSYM sites for 31 symbols used by
     other .c/.h files now live in syms_of_keyboard_globals
     (keyboard-globals.c), which make-docfile still scans.  The
     local-only DEFSYM sites for 39 symbols with no other C reader were
     deleted; those symbols are now interned from Scheme boot code (see
     prelude/load.scm).  Only symbols with a remaining C consumer stay
     here.  */

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

  /* M2 — predicate symbol for the kboard smob type.  */
  DEFSYM (Qkboardp, "kboardp");

  /* M9 — register ie-smob hooks and predicate symbol.
     M23 imp-5 review: stays in C.  scm_set_smob_mark/free/print register
     Guile smob-type hooks that dispatch to ie_mark/ie_free/ie_print
     (defined in C in this file); this is SMOB machinery, not a Lisp
     declaration, so it is out of scope for the "Scheme declarations"
     migration.  Qiep is Group D (still has a C consumer) and also stays
     (brief.org B).  */
  scm_set_smob_mark (ie_tag, ie_mark);
  scm_set_smob_free (ie_tag, ie_free);
  scm_set_smob_print (ie_tag, ie_print);
  DEFSYM (Qiep, "iep");

  /* Tool-bars.  */

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

  DEFSYM (Qfunction_key, "function-key");

  /* The values of Qevent_kind properties.  */
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
  DEFSYM (Qsave_session, "save-session");
  DEFSYM (Qconfig_changed_event, "config-changed-event");
  DEFSYM (Quser_signal_event, "user-signal-event");

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

  DEFSYM (Qabove_handle, "above-handle");
  DEFSYM (Qhandle, "handle");
  DEFSYM (Qbelow_handle, "below-handle");
  DEFSYM (Qend_scroll, "end-scroll");
  DEFSYM (Qratio, "ratio");
  DEFSYM (Qbefore_handle, "before-handle");
  DEFSYM (Qhorizontal_handle, "horizontal-handle");
  DEFSYM (Qafter_handle, "after-handle");
  DEFSYM (Qleftmost, "leftmost");
  DEFSYM (Qrightmost, "rightmost");

  /* An unmodified event header BASE may have a property named
     Qmodifier_cache, which is an alist mapping modifier masks onto
     modified versions of BASE.  If present, this helps speed up
     apply_modifiers.  */
  DEFSYM (Qmodifier_cache, "modifier-cache");


  DEFSYM (Qpolling_period, "polling-period");


  DEFSYM (Qinput_method_exit_on_first_char, "input-method-exit-on-first-char");
  DEFSYM (Qinput_method_use_echo_area, "input-method-use-echo-area");

  DEFSYM (Qhelp_form_show, "help-form-show");




  /* M23 imp-5 review: these two Fset calls stay in C with their DEFSYM.
     Each symbol is Group D (still read from C keyboard logic elsewhere
     in this file, e.g. specbind Qinput_method_use_echo_area), so the
     DEFSYM cannot move yet; each Fset that zeroes its value must keep
     its pair together (brief.org B).  */
  Fset (Qinput_method_exit_on_first_char, Qnil);
  Fset (Qinput_method_use_echo_area, Qnil);

  /* Symbols for dragging internal borders.  */
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
  DEFSYM (Qfocus_out, "focus-out");
  DEFSYM (Qmove_frame, "move-frame");
  DEFSYM (Qmake_frame_visible, "make-frame-visible");
  DEFSYM (Qno_event, "no-event");
  DEFSYM (Qselect_window, "select-window");
  /* M23 imp-5 review: the head_table[] Fput loop below stays a C-side
     Fput loop.  head_table (this file, static const) is read only here,
     in syms_of_keyboard (checked live: no other C reader in the tree),
     so its data is not cross-file.  The loop runs during syms, before
     any post-syms Scheme hook exists; it calls Fput (a C DEFUN) to tag
     each event-head symbol with Qevent_kind / Qevent_symbol_elements,
     properties consumed from C (apply_modifiers, etc.).  Porting it to
     Scheme would need a post-syms trigger that does not yet exist, so
     it stays verbatim (brief.org B).  */
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

  DEFSYM (Qpreedit_text, "preedit-text");

  button_down_location = make_nil_elisp_vector (5);
  staticpro (&button_down_location);
  /* M30 imp-1: frame_relative_event_pos is read through --cell-ref; a
     staticpro of a zeroed Lisp_Object roots NULL.  Initialize to Qnil.  */
  frame_relative_event_pos = Qnil;
  staticpro (&frame_relative_event_pos);
  mouse_syms = make_nil_elisp_vector (5);
  staticpro (&mouse_syms);
  /* 4 wheel event names; matches (emacs lispy-event)'s wheel-names vector. */
  wheel_syms = make_nil_elisp_vector (4);
  staticpro (&wheel_syms);

  /* modifier_symbols / modifier_names[] were removed at M1 — the
     modifier-name list now lives in mod/emacs/event-modifiers.scm.  */

  recent_keys = make_nil_elisp_vector (lossage_limit);
  staticpro (&recent_keys);

  this_command_keys = make_nil_elisp_vector (40);
  staticpro (&this_command_keys);

  raw_keybuf = make_nil_elisp_vector (30);
  staticpro (&raw_keybuf);


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

  /* M30 imp-5: root the getctag prompt tag so the cell table can hold
     it.  An object cell must be a GC root; the table holds a raw
     void *.  A zeroed Lisp_Object is not Qnil (DEFINE_NON_NIL_Q_SYMBOL_MACROS
     is false), so set it before the staticpro.  */
  getctag = Qnil;
  staticpro (&getctag);

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
  /* M24: poll_timer_time moved to (emacs input-poll) as the Scheme
     module cache *poll-timer-period*; nothing to staticpro here.  */
#endif

  menu_bar_touch_id = Qnil;
  staticpro (&menu_bar_touch_id);

  /* M30 imp-4: root the lookup_cell one-entry memo name (cr.org F2).
     See the comment at the definition of last_cell_name.  */
  last_cell_name = Qnil;
  staticpro (&last_cell_name);


  DEFSYM (Qecho_area_clear_hook, "echo-area-clear-hook");
  DEFSYM (Qtouchscreen_update, "touchscreen-update");
  DEFSYM (Qpinch, "pinch");

  /* Event-kind keys for the imp-3 dispatch switch.  */
  DEFSYM (Qselection_request_event, "selection-request-event");
  DEFSYM (Qselection_clear_event, "selection-clear-event");
  DEFSYM (Qmonitors_changed, "monitors-changed");
  DEFSYM (Qmenu_bar_activate_event, "menu-bar-activate-event");

  DEFSYM (Qtouchscreen, "touchscreen");

  /* M23 imp-5 review: this Fset stays in C with its DEFSYM
     (Qecho_area_clear_hook, above).  The symbol is Group D — still
     consumed from C (safe_run_hooks Qecho_area_clear_hook), so its
     DEFSYM cannot move yet; the Fset zeroing its value keeps its pair
     together (brief.org B).  */
  Fset (Qecho_area_clear_hook, Qnil);




  /* Create the initial keyboard.  Qt means 'unset'.  */

  /* M23 imp-5: Vfunction_key_map's DEFVAR stays here (not relocated to
     keyboard-globals.c) because allocate_kboard() -> init_kboard()
     below reads Vfunction_key_map before syms_of_keyboard_globals
     runs.  Moving it there would leave it uninitialized at this
     point.  See brief.org Section C/D ordering note.  */
  DEFVAR_LISP ("function-key-map", Vfunction_key_map,
               doc: /* The parent keymap of all `local-function-key-map' instances.
Function key definitions that apply to all terminal devices should go
here.  If a mapping is defined in both the current
`local-function-key-map' binding and this variable, then the local
definition will take precedence.  */);
  Vfunction_key_map = Fmake_sparse_keymap (Qnil);

  eassert (initial_kboard == NULL);
  initial_kboard = allocate_kboard (Qt);

  DEFSYM (Qinternal_timer_start_idle, "internal-timer-start-idle");
  DEFSYM (Qsuspend_hook, "suspend-hook");
  DEFSYM (Qsuspend_resume_hook, "suspend-resume-hook");
  DEFSYM (Qsigusr2, "sigusr2");
}

void
keys_of_keyboard (void)
{
  /* M23 imp-5: dispatch to (emacs command-loop) init-m23-imp5-
     registrations, which runs here (not at prelude boot) because
     special-event-map does not exist until syms_of_keyboard_globals
     runs, earlier in this same src/emacs.c init sequence.  */
  SCM_CALL_0 (scm_c_public_ref ("emacs command-loop",
                                 "init-m23-imp5-registrations"));
}
