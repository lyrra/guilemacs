/* Cross-file keyboard global variables and DEFSYM sites
   (M23 imp-2, imp-3, imp-4, imp-5).

Copyright (C) 1985-1989, 1993-1997, 1999-2026 Free Software Foundation,
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

/* This file holds the cross-file DEFVAR_LISP/DEFVAR_INT/DEFVAR_BOOL
   call sites moved out of syms_of_keyboard in M23 imp-2, the 8
   DEFVAR_KBOARD call sites relocated there in imp-3, and the imp-4
   cross-file DEFSYM sites appended at the end of
   syms_of_keyboard_globals.  Each imp-2/imp-4 name here is read from
   at least one other .c/.h file, so its DEFVAR_* / DEFSYM call site
   must stay in a file scanned by make-docfile (base_obj), even though
   it no longer lives in keyboard.c.

   M23 imp-5 relocates 23 of the 24 imp-1-deferred DEFVAR_* call sites
   (18 with a keyboard-local C reader, group C; 5 cross-file names
   imp-1's audit missed, group D).  Same pure-relocation rule as
   imp-2/imp-3: each name keeps a live C reader, so its call site
   stays in a make-docfile file; the reader and the globals.h storage
   are untouched.  Exception: Vfunction_key_map (group C) stays in
   syms_of_keyboard because allocate_kboard()->init_kboard() reads it
   during syms_of_keyboard, before syms_of_keyboard_globals runs.

   The imp-3 DEFVAR_KBOARD sites are a pure relocation: DEFVAR_KBOARD
   registers a Lisp_Kboard_Objfwd forwarding record (offsetof into
   struct kboard) that dispatches through current_kboard, so its call
   site is not tied to any translation unit.  It needs the full struct
   kboard definition, hence the keyboard.h include.  See brief.org.  */

#include <config.h>

#include "lisp.h"
#include "keyboard.h"

void
syms_of_keyboard_globals (void)
{
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

  DEFVAR_LISP ("meta-prefix-char", meta_prefix_char,
	       doc: /* Meta-prefix character code.
Meta-foo as command input turns into this character followed by foo.  */);
  XSETINT (meta_prefix_char, 033);

  DEFVAR_LISP ("this-command", Vthis_command,
	       doc: /* The command now being executed.
The command can set this variable; whatever is put here
will be in `last-command' during the following command.  */);
  Vthis_command = Qnil;

  DEFVAR_LISP ("real-this-command", Vreal_this_command,
	       doc: /* This is like `this-command', except that commands should never modify it.  */);
  Vreal_this_command = Qnil;

  DEFVAR_LISP ("this-original-command", Vthis_original_command,
	       doc: /* The command bound to the current key sequence before remapping.
It equals `this-command' if the original command was not remapped through
any of the active keymaps.  Otherwise, the value of `this-command' is the
result of looking up the original command in the active keymaps.  */);
  Vthis_original_command = Qnil;

  DEFVAR_LISP ("double-click-time", Vdouble_click_time,
	       doc: /* Maximum time between mouse clicks to make a double-click.
Measured in milliseconds.  The value nil means disable double-click
recognition; t means double-clicks have no time limit and are detected
by position only.

In Lisp, you might want to use `mouse-double-click-time' instead of
reading the value of this variable directly.  */);
  Vdouble_click_time = make_fixnum (500);

  DEFVAR_INT ("num-nonmacro-input-events", num_nonmacro_input_events,
	      doc: /* Number of input events read from the keyboard so far.
This does not include events generated by keyboard macros.  */);
  num_nonmacro_input_events = 0;

  /* This variable is set up in sysdep.c.  */
  DEFVAR_LISP ("tty-erase-char", Vtty_erase_char,
	       doc: /* The ERASE character as set by the user with stty.  */);

  DEFVAR_LISP ("help-form", Vhelp_form,
	       doc: /* Form to execute when character `help-char' is read.
If the form returns a string, that string is displayed.
If `help-form' is nil, the help char is not recognized.  */);
  Vhelp_form = Qnil;

  DEFVAR_LISP ("top-level", Vtop_level,
	       doc: /* Form to evaluate when Emacs starts up.
Useful to set before you dump a modified Emacs.  */);
  Vtop_level = Qnil;

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
  /* Moved with the DEFVAR so the buffer-local wrap still follows the
     symbol forward.  In the original syms_of_keyboard this call sat
     right after this DEFVAR; relocating the DEFVAR alone (leaving the
     Fmake in keyboard.c) would run Fmake *before* the DEFVAR, and
     defvar_lisp_nopro would then overwrite the buffer-local redirect,
     silently de-buffer-localizing deactivate-mark.  */
  Fmake_variable_buffer_local (Qdeactivate_mark);

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

  DEFVAR_LISP ("throw-on-input", Vthrow_on_input,
	       doc: /* If non-nil, any keyboard input throws to this symbol.
The value of that variable is passed to `quit-flag' and later causes a
peculiar kind of quitting.  */);
  Vthrow_on_input = Qnil;

  DEFVAR_BOOL ("mwheel-coalesce-scroll-events", mwheel_coalesce_scroll_events,
	       doc: /* Non-nil means send a wheel event only for scrolling at least one screen line.
Otherwise, a wheel event will be sent every time the mouse wheel is
moved.  */);
  mwheel_coalesce_scroll_events = true;


  /* M23 imp-3: relocated DEFVAR_KBOARD call sites.  Each registers a
     Lisp_Kboard_Objfwd forwarding into struct kboard; storage and
     forwarding are unchanged.  See brief.org.  */

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

  DEFVAR_KBOARD ("overriding-terminal-local-map",
		 Voverriding_terminal_local_map,
		 doc: /* Per-terminal keymap that takes precedence over all other keymaps.
This variable is intended to let commands such as `universal-argument'
set up a different keymap for reading the next command.

`overriding-terminal-local-map' has a separate binding for each
terminal device.  See Info node `(elisp)Multiple Terminals'.  */);

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

  /* M23 imp-5 — relocated DEFVAR_LISP/INT/BOOL call sites whose
     local-looking declarations were deferred from imp-1 because they
     still have live C readers (group C) or were missed by imp-1's
     audit because the reader lives in another .c file (group D).
     Pure relocation, byte-for-byte text move; the reader and the
     globals.h storage are unaffected (see docs/m23-plan.org Finding
     6).  Each initializer line moves with its declaration so the
     value is set only after defvar_* registers the forward.  */

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

  DEFVAR_INT ("auto-save-interval", auto_save_interval,
              doc: /* Number of input events between auto-saves.
Zero means disable autosaving due to number of characters typed.  */);
  auto_save_interval = 300;

  DEFVAR_LISP ("echo-keystrokes", Vecho_keystrokes,
    doc: /* Nonzero means echo unfinished commands after this many seconds of pause.
The value may be integer or floating point.
If the value is zero, don't echo at all.  */);
  Vecho_keystrokes = make_fixnum (1);

  DEFVAR_LISP ("polling-period", Vpolling_period,
              doc: /* Interval between polling for input during Lisp execution.
The reason for polling is to make C-g work to stop a running program.
Polling is needed only when using X windows and SIGIO does not work.
Polling is automatically disabled in all other cases.  */);
  Vpolling_period = make_float (2.0);

  DEFVAR_INT ("num-input-keys", num_input_keys,
              doc: /* Number of complete key sequences read as input so far.
This includes key sequences read from keyboard macros.
The number is effectively the number of interactive command invocations.  */);
  num_input_keys = 0;

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

  DEFVAR_LISP ("help-char", Vhelp_char,
               doc: /* Character to recognize as meaning Help.
When it is read, do `(eval help-form)', and display result if it's a string.
If the value of `help-form' is nil, this char can be read normally.  */);
  XSETINT (Vhelp_char, 8);

  DEFVAR_LISP ("help-event-list", Vhelp_event_list,
               doc: /* List of input events to recognize as meaning Help.
These work just like the value of `help-char' (see that).  */);
  Vhelp_event_list = Qnil;

  DEFVAR_LISP ("prefix-help-command", Vprefix_help_command,
               doc: /* Command to run when `help-char' character follows a prefix key.
This command is used only when there is no actual binding
for that character after that prefix key.  */);
  Vprefix_help_command = Qnil;

  DEFVAR_BOOL ("cannot-suspend", cannot_suspend,
               doc: /* Non-nil means to always spawn a subshell instead of suspending.
\(Even if the operating system has support for stopping a process.)  */);
  cannot_suspend = false;

  DEFVAR_LISP ("special-event-map", Vspecial_event_map,
               doc: /* Keymap defining bindings for special events to execute at low level.  */);
  Vspecial_event_map = list1 (Qkeymap);

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

  DEFVAR_LISP ("minibuffer-message-timeout", Vminibuffer_message_timeout,
               doc: /* How long to display an echo-area message when the minibuffer is active.
If the value is a number, it should be specified in seconds.
If the value is not a number, such messages never time out.  */);
  Vminibuffer_message_timeout = make_fixnum (2);

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

  DEFVAR_BOOL ("disable-inhibit-text-conversion",
               disable_inhibit_text_conversion,
    doc: /* Don't disable text conversion inside `read-key-sequence'.
If non-nil, text conversion will continue to happen after a prefix
key has been read inside `read-key-sequence'.  */);
  disable_inhibit_text_conversion = false;


  /* M23 imp-4 — cross-file DEFSYM call sites relocated out of
     syms_of_keyboard.  Each symbol below is read by name from at least
     one other .c/.h file, so its DEFSYM must stay in a file scanned by
     make-docfile (base_obj) to keep the generated Qsym #define and
     defsym_name[] entry.  Pure relocation, unchanged text.  */

  DEFSYM (QCfilter, ":filter");
  DEFSYM (QCradio, ":radio");
  DEFSYM (QCtoggle, ":toggle");
  DEFSYM (QPRIMARY, "PRIMARY");
  DEFSYM (Qactivate_menubar_hook, "activate-menubar-hook");
  DEFSYM (Qbottom, "bottom");
  DEFSYM (Qbottom_divider, "bottom-divider");
  DEFSYM (Qcoding, "coding");
  DEFSYM (Qconcat, "concat");
  DEFSYM (Qcurrent_minibuffer_command, "current-minibuffer-command");
  DEFSYM (Qdeactivate_mark, "deactivate-mark");
  DEFSYM (Qdelete_frame, "delete-frame");
  DEFSYM (Qdisabled, "disabled");
  DEFSYM (Qdown, "down");
  DEFSYM (Qdrag_internal_border, "drag-internal-border");
  DEFSYM (Qevent_kind, "event-kind");
  DEFSYM (Qevent_symbol_element_mask, "event-symbol-element-mask");
  DEFSYM (Qevent_symbol_elements, "event-symbol-elements");
  DEFSYM (Qfocus_in, "focus-in");
  DEFSYM (Qhelp_echo, "help-echo");
  DEFSYM (Qhelp_key_binding, "help-key-binding");
  DEFSYM (Qiconify_frame, "iconify-frame");
  DEFSYM (Qmouse_click, "mouse-click");
  DEFSYM (Qright_divider, "right-divider");
  DEFSYM (Qswitch_frame, "switch-frame");
#ifdef HAVE_TEXT_CONVERSION
  DEFSYM (Qtext_conversion, "text-conversion");
#endif
  DEFSYM (Qtop, "top");
  DEFSYM (Qtouchscreen_begin, "touchscreen-begin");
  DEFSYM (Qtouchscreen_end, "touchscreen-end");
  DEFSYM (Qup, "up");
  DEFSYM (Qvertical_line, "vertical-line");
}
