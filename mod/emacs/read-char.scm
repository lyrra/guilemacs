(define-module (emacs read-char)
  #:use-module (emacs-elisp runtime)
  #:use-module (srfi srfi-9)            ; define-record-type
  #:declarative? #t
  #:export (;; M8a — data substrate
            make-rc-state rc-state?
            rc-state-fresh!
            ;; M8c — read_char_1 splices
            rc-prologue-drain-unread!
            rc-prologue-macro-or-switch-frame!
            rc-prologue-redisplay!
            rc-prologue-echo-and-menu!
            rc-prologue-idle-echo-autosave!
            rc-prologue-xmenu-and-idle-gc!
            init-read-char-registrations))

;;; M8 — read_char / read_char_1 port.
;;;
;;; read_char (src/keyboard.c:2978) is the entry wrapper that
;;; heap-allocates a `struct read_char_state' and dispatches via
;;; Guile's `call_with_prompt' to `read_char_1' (the ~820-line
;;; state machine).
;;;
;;; Architecture inherited from C:
;;;   - State lives in a heap-allocated struct (read_char_state).
;;;   - read_char_1 uses `#define commandflag state->commandflag'
;;;     etc. to make struct-field access look like locals.
;;;     This is exactly the M6 #define-alias pattern, applied to
;;;     a struct rather than file-static globals.
;;;   - Guile delimited continuations handle the longjmp-style
;;;     quit path (no setjmp/longjmp needed).
;;;
;;; M8 plan (after M6 close):
;;;   M8a — this module skeleton + <rc-state> record + state-pointer
;;;         stack + first 3-4 trivial accessor subrs.  No splices.
;;;   M8b-M8d — field-accessor subrs for the remaining struct fields.
;;;   M8e — splice the prologue (unread-events / quit-flag /
;;;         help_char_p).
;;;   M8f+ — successive translation-map / dispatch / blocking-wait
;;;          splices, following the M6 atomic-bulk-subr pattern.
;;;
;;; See docs/keyboard.org §M8 for the full revised plan.

(define (%c name) (symbol-function name))

(define (%nilp x)
  (or (null? x) (not x)))

;;;;
;;;; M8a — <rc-state> Scheme record type.
;;;;
;;;; Mirrors `struct read_char_state' (src/keyboard.c:2835-2852)
;;;; one field per slot.  Used by future M8 slices for testable
;;;; in-Scheme state representation.  Not yet wired into the
;;;; runtime — read_char_1 still keeps its state as a C struct.
;;;;
;;;; Field semantics (mirror the C struct):
;;;;   commandflag      — -1 = inhibit redisplay,
;;;;                      0  = called via read-event,
;;;;                      1  = called from command loop,
;;;;                      -2 = read_char called with prevent_redisplay.
;;;;   map              — keymap stack (the FOLLOW arg from read_char).
;;;;   prev-event       — last-command-event the caller saw.
;;;;   used-mouse-menu  — set true if the read produced a menu choice.
;;;;   end-time         — deadline for timed reads (#nil = no timeout).
;;;;   c                — the resulting event (output slot).
;;;;   tag, local-tag, save-tag
;;;;                    — Guile-prompt tags used for quit handling.
;;;;   previous-echo-area-message
;;;;                    — saved echo-area state for restoration.
;;;;   also-record      — secondary event to add_command_key when set.
;;;;   recorded         — true once add_command_key has been called
;;;;                      for this iteration.
;;;;   reread           — true when re-reading from unread-events.
;;;;   polling-stopped-here
;;;;                    — true when poll_for_input was stopped by us.
;;;;   orig-kboard      — current_kboard snapshot at entry (for
;;;;                      detecting kboard switches mid-read).

(define-record-type <rc-state>
  (%make-rc-state commandflag map prev-event used-mouse-menu end-time
                  c tag local-tag save-tag
                  previous-echo-area-message also-record
                  recorded reread polling-stopped-here
                  orig-kboard)
  rc-state?
  (commandflag       rc-state-commandflag       set-rc-state-commandflag!)
  (map               rc-state-map               set-rc-state-map!)
  (prev-event        rc-state-prev-event        set-rc-state-prev-event!)
  (used-mouse-menu   rc-state-used-mouse-menu   set-rc-state-used-mouse-menu!)
  (end-time          rc-state-end-time          set-rc-state-end-time!)
  (c                 rc-state-c                 set-rc-state-c!)
  (tag               rc-state-tag               set-rc-state-tag!)
  (local-tag         rc-state-local-tag         set-rc-state-local-tag!)
  (save-tag          rc-state-save-tag          set-rc-state-save-tag!)
  (previous-echo-area-message
                     rc-state-previous-echo-area-message
                     set-rc-state-previous-echo-area-message!)
  (also-record       rc-state-also-record       set-rc-state-also-record!)
  (recorded          rc-state-recorded          set-rc-state-recorded!)
  (reread            rc-state-reread            set-rc-state-reread!)
  (polling-stopped-here
                     rc-state-polling-stopped-here
                     set-rc-state-polling-stopped-here!)
  (orig-kboard       rc-state-orig-kboard       set-rc-state-orig-kboard!))

(define (make-rc-state)
  "Create a fresh rc-state with C-struct defaults (everything nil
or false, commandflag = 0).  Mirrors the read_char entry's
explicit zeroing (src/keyboard.c:2915-2927)."
  (%make-rc-state
   0      ; commandflag
   #nil   ; map
   #nil   ; prev-event
   #nil   ; used-mouse-menu (bool)
   #nil   ; end-time
   #nil   ; c
   #nil   ; tag
   #nil   ; local-tag
   #nil   ; save-tag
   #nil   ; previous-echo-area-message
   #nil   ; also-record
   #nil   ; recorded (bool)
   #nil   ; reread (bool)
   #nil   ; polling-stopped-here (bool)
   #nil)) ; orig-kboard

(define (rc-state-fresh! state)
  "Reset STATE in-place to the C-struct defaults.  Useful for
test setup when the same rc-state is reused across calls."
  (set-rc-state-commandflag!                state 0)
  (set-rc-state-map!                        state #nil)
  (set-rc-state-prev-event!                 state #nil)
  (set-rc-state-used-mouse-menu!            state #nil)
  (set-rc-state-end-time!                   state #nil)
  (set-rc-state-c!                          state #nil)
  (set-rc-state-tag!                        state #nil)
  (set-rc-state-local-tag!                  state #nil)
  (set-rc-state-save-tag!                   state #nil)
  (set-rc-state-previous-echo-area-message! state #nil)
  (set-rc-state-also-record!                state #nil)
  (set-rc-state-recorded!                   state #nil)
  (set-rc-state-reread!                     state #nil)
  (set-rc-state-polling-stopped-here!       state #nil)
  (set-rc-state-orig-kboard!                state #nil))

;;;;
;;;; M8c — read_char_1 prologue splices.
;;;;

(define %rc-prologue-xmenu-and-idle-gc
  (delay (%c '--rc-prologue-xmenu-and-idle-gc)))

(define (rc-prologue-xmenu-and-idle-gc!)
  "X-menu read + auto-save-by-idle-timeout + GC blocks after M8g.
Block 1: when KEYMAPP(map) && INTERACTIVE && prev-event has
parameters && head not menu/tab/tool-bar && no unread events,
install state->c from read_char_x_menu_prompt, stop the idle
timer if not timed, return `goto-exit'.  Block 2: pure fall-
through — buffer-size-scaled sit_for + Fdo_auto_save + redisplay
when the auto-save threshold is crossed, then GC_collect_a_little
if no input pending.  Returns `goto-exit' or `fall-through'.  See
docs/keyboard.org §M8h."
  ((force %rc-prologue-xmenu-and-idle-gc)))

(define %rc-prologue-idle-echo-autosave
  (delay (%c '--rc-prologue-idle-echo-autosave)))

(define (rc-prologue-idle-echo-autosave!)
  "Three pure-side-effect blocks before the blocking input wait:
idle-timer start, immediate-echo start (with sit_for delay for
non-mouse events), and auto-save by keystroke count.  Always
returns nil — caller falls through.  See docs/keyboard.org §M8g."
  ((force %rc-prologue-idle-echo-autosave)))

(define %rc-prologue-echo-and-menu
  (delay (%c '--rc-prologue-echo-and-menu)))

(define (rc-prologue-echo-and-menu!)
  "Echo-cancel-or-dash + minibuf-menu-prompt blocks before the
blocking read.  Returns one of `return-wrong-kboard' (caller
returns -2 from read_char_1 — the wrong_kboard_jmpbuf code),
`goto-exit' (caller goto exit; state->c installed), or
`fall-through' (caller continues to the next block).  See
docs/keyboard.org §M8f."
  ((force %rc-prologue-echo-and-menu)))

(define %rc-prologue-redisplay
  (delay (%c '--rc-prologue-redisplay)))

(define (rc-prologue-redisplay!)
  "Redisplay loop in the read_char_1 prologue.  When the current
read_char's commandflag is >= 0, swallow non-user-visible events
and redisplay until convergence, then pin echo_message_buffer
when commandflag == 0.  Always returns nil — caller falls
through.  See docs/keyboard.org §M8e."
  ((force %rc-prologue-redisplay)))

(define %rc-prologue-macro-or-switch-frame
  (delay (%c '--rc-prologue-macro-or-switch-frame)))

(define (rc-prologue-macro-or-switch-frame!)
  "Two early-exit blocks after the unread-events drain:
in-progress kbd-macro replay, and pending switch-frame event.
Returns `from-macro', `reread-first', or `fall-through' for
3-way C control flow.  See docs/keyboard.org §M8d."
  ((force %rc-prologue-macro-or-switch-frame)))

(define %rc-prologue-drain-unread
  (delay (%c '--rc-prologue-drain-unread)))

(define (rc-prologue-drain-unread!)
  "Drain the three unread-events queues at the top of read_char_1.
The current (top-of-stack) read_char invocation's state is mutated
in place (c / reread / recorded / *used_mouse_menu).  Returns one
of `reread-first', `reread-for-input-method', or `fall-through' to
control the C caller's goto.

See docs/keyboard.org §M8c."
  ((force %rc-prologue-drain-unread)))

;;;;
;;;; Registration
;;;;
;;;; srfi-9 accessors are syntax-transformers in this Guile build
;;;; (see feedback_scheme_module_elisp_calls.md note from M6g),
;;;; so we expose only constructors / predicates and the
;;;; regular-define helpers as elisp-callable shims.

(define (init-read-char-registrations)
  "Wire the elisp-visible (emacs read-char) handles."
  (for-each (lambda (sym-fun)
              (set-symbol-function! (car sym-fun) (cadr sym-fun)))
            `((--make-rc-state         ,make-rc-state)
              (--rc-state-fresh!       ,rc-state-fresh!)
              ;; M8c — prologue dispatch
              (--rc-prologue-drain-unread!
                                       ,rc-prologue-drain-unread!)
              ;; M8d — kbd-macro / switch-frame early-exit
              (--rc-prologue-macro-or-switch-frame!
                                       ,rc-prologue-macro-or-switch-frame!)
              ;; M8e — redisplay loop
              (--rc-prologue-redisplay!
                                       ,rc-prologue-redisplay!)
              ;; M8f — echo-cancel + minibuf-menu-prompt
              (--rc-prologue-echo-and-menu!
                                       ,rc-prologue-echo-and-menu!)
              ;; M8g — idle-timer + immediate-echo + auto-save
              (--rc-prologue-idle-echo-autosave!
                                       ,rc-prologue-idle-echo-autosave!)
              ;; M8h — X-menu + auto-save-by-idle-timeout + GC
              (--rc-prologue-xmenu-and-idle-gc!
                                       ,rc-prologue-xmenu-and-idle-gc!))))
