(define-module (emacs read-char)
  #:use-module (emacs elisp-ref)
  #:use-module (emacs-elisp runtime)
  #:use-module (srfi srfi-9)            ; define-record-type
  #:declarative? #t
  #:export (;; M8a — data substrate
            make-rc-state rc-state?
            rc-state-fresh!
            ;; end-time slot accessors — imported by (emacs
            ;; kbd-buffer) for the imp-2 entry-sync (M11 imp-2).
            rc-state-end-time set-rc-state-end-time!
            read-char-init-state
            read-char-entry
            ;; M8c — read_char_1 splices
            rc-prologue-drain-unread!
            rc-prologue-macro-or-switch-frame!
            rc-prologue-redisplay!
            rc-prologue-echo-and-menu!
            rc-prologue-idle-echo-autosave!
            rc-prologue-xmenu-and-idle-gc!
            rc-prologue-kboard-and-queues!
            rc-wrong-kboard-and-non-reread!
            rc-bufferp-and-special-event-map!
            rc-event-translate-and-record!
            rc-input-method-dispatch!
            rc-help-echo-and-help-form!
            rc-exit!
            read-char-main
            internal-handle-focus-in
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


(define (%nilp x)
  (or (null? x) (not x)))

(define (%elisp-t? x)
  (or (eq? x #t) (eq? x 't)))

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
;;;;   used-mouse-menu  — foreign-ptr to the caller-owned C bool (or
;;;;                      #nil); C consumers set *p true when the read
;;;;                      produced a menu choice.  brief.org sub-task B
;;;;                      part 1: the pointer field stays for imp-3 to
;;;;                      remove; the used-mouse-menu-flag field below
;;;;                      is the value-return path.  Both paths run
;;;;                      side by side and must agree.
;;;;   used-mouse-menu-flag
;;;;                      — plain Scheme boolean, false value is #f.
;;;;                      DELIBERATELY NOT #nil: C read_char reads it
;;;;                      back with scm_is_true, and scm_is_true(#nil)
;;;;                      is true — a #nil false value would trip the
;;;;                      imp-2 eassert on every ordinary read.  See
;;;;                      docs/arch.org "used-mouse-menu-flag false
;;;;                      value".  Set to #t exactly when the
;;;;                      used-mouse-menu pointer write fires (menu
;;;;                      choice / disabled re-read).
;;;;                      Sub-task B part 2 done: rc-exit!, all three
;;;;                      wrong-kboard -2 exits, and the quit-handler
;;;;                      branch return the flag as the second value,
;;;;                      and C read_char writes it through
;;;;                      used_mouse_menu under an eassert divergence
;;;;                      check (M12 imp-2).
;;;;   end-time         — deadline for timed reads (#nil = no timeout).
;;;;   c                — the resulting event (output slot).
;;;;   local-tag        — Guile-prompt tag passed as local_getcjmp to
;;;;                      read-decoded-event-from-main-queue (M8j / M12
;;;;                      imp-5 rewire).
;;;;   previous-echo-area-message
;;;;                    — saved echo-area state for restoration.
;;;;   also-record      — secondary event to add_command_key when set.
;;;;   recorded         — true once add_command_key has been called
;;;;                      for this iteration.
;;;;   reread           — true when re-reading from unread-events.
;;;;   orig-kboard      — current_kboard snapshot at entry (for
;;;;                      detecting kboard switches mid-read).

(define-record-type <rc-state>
  (%make-rc-state commandflag map prev-event used-mouse-menu
                  used-mouse-menu-flag end-time
                  c local-tag
                  previous-echo-area-message also-record
                  recorded reread
                  orig-kboard)
  rc-state?
  (commandflag       rc-state-commandflag       set-rc-state-commandflag!)
  (map               rc-state-map               set-rc-state-map!)
  (prev-event        rc-state-prev-event        set-rc-state-prev-event!)
  (used-mouse-menu   rc-state-used-mouse-menu   set-rc-state-used-mouse-menu!)
  (used-mouse-menu-flag
                     rc-state-used-mouse-menu-flag
                     set-rc-state-used-mouse-menu-flag!)
  (end-time          rc-state-end-time          set-rc-state-end-time!)
  (c                 rc-state-c                 set-rc-state-c!)
  (local-tag         rc-state-local-tag         set-rc-state-local-tag!)
  (previous-echo-area-message
                     rc-state-previous-echo-area-message
                     set-rc-state-previous-echo-area-message!)
  (also-record       rc-state-also-record       set-rc-state-also-record!)
  (recorded          rc-state-recorded          set-rc-state-recorded!)
  (reread            rc-state-reread            set-rc-state-reread!)
  (orig-kboard       rc-state-orig-kboard       set-rc-state-orig-kboard!))

(define (make-rc-state)
  "Create a fresh rc-state with C-struct defaults (everything nil
or false, commandflag = 0).  Mirrors the read_char entry's
explicit zeroing in src/keyboard.c."
  (%make-rc-state
   0      ; commandflag
   #nil   ; map
   #nil   ; prev-event
   #nil   ; used-mouse-menu (foreign-ptr or #nil)
   #f     ; used-mouse-menu-flag (plain Scheme boolean)
   #nil   ; end-time        (foreign-ptr or #nil)
   #nil   ; c
   #nil   ; local-tag
   #nil   ; previous-echo-area-message
   #nil   ; also-record
   #nil   ; recorded (bool)
   #nil   ; reread (bool)
   #nil)) ; orig-kboard

(define (read-char-init-state commandflag map prev-event
                              used-mouse-menu end-time orig-kboard)
  "Allocate the <rc-state> Scheme record for a read_char entry,
populate it from the caller's args, mint a fresh prompt-tag for
local-tag, and return (REC . TAG).  Called from `read-char-entry'.
Caller-owned pointer args USED-MOUSE-MENU and END-TIME arrive
already wrapped as Guile foreign-pointer SCMs (or nil)."
  (let* ((tag (make-prompt-tag))
         (rec (%make-rc-state commandflag map prev-event
                              used-mouse-menu
                              #f            ; used-mouse-menu-flag
                              end-time
                              #nil          ; c
                              tag           ; local-tag
                              #nil          ; previous-echo-area-message
                              #nil          ; also-record
                              #nil          ; recorded
                              #nil          ; reread
                              orig-kboard)))
    (cons rec tag)))

(define %rc-record-stack-push (delay (%c '--rc-record-stack-push)))
(define %rc-record-stack-pop  (delay (%c '--rc-record-stack-pop)))
(define %read-char-handle-quit-preamble
  (delay (%c '--read-char-handle-quit-preamble)))

(define (read-char-entry commandflag map prev-event
                         used-mouse-menu end-time orig-kboard)
  "Body of C `read_char': build the <rc-state> record, set up the
Guile prompt, dispatch into `read-char-main' under both the normal
(thunk) and quit-handler closures.  Called from C read_char().
Returns two values: the resolved event (via --rc-exit inside
read-char-main) or fixnum -2 (wrong_kboard_jmpbuf), and the
used-mouse-menu flag (plain Scheme boolean, #t when the read
produced a menu choice)."
  (let* ((rec-and-tag (read-char-init-state commandflag map prev-event
                                            used-mouse-menu end-time
                                            orig-kboard))
         (rec (car rec-and-tag))
         (tag (cdr rec-and-tag)))
    (call-with-prompt
     tag
     (lambda ()
       ((force %rc-record-stack-push) rec)
       (dynamic-wind
         (lambda () #f)
         (lambda () (read-char-main #nil))
         (lambda () ((force %rc-record-stack-pop)))))
     (lambda (k . _)
       ;; Quit handler: stash quit_char and maybe requeue to another
       ;; kboard.  Returns two values like every other exit: nil (rec
       ;; read again with jump=t) or fixnum -2, each paired with the
       ;; used-mouse-menu flag.
       (let ((preamble-result ((force %read-char-handle-quit-preamble) rec)))
         (if (%nilp preamble-result)
             (read-char-main #t)
             (values preamble-result (rc-state-used-mouse-menu-flag rec))))))))

(define (rc-state-fresh! state)
  "Reset STATE in-place to the C-struct defaults.  Useful for
test setup when the same rc-state is reused across calls."
  (set-rc-state-commandflag!                state 0)
  (set-rc-state-map!                        state #nil)
  (set-rc-state-prev-event!                 state #nil)
  (set-rc-state-used-mouse-menu!            state #nil)
  (set-rc-state-used-mouse-menu-flag!       state #f)  ; #f, not #nil — see field comment above
  (set-rc-state-end-time!                   state #nil)
  (set-rc-state-c!                          state #nil)
  (set-rc-state-local-tag!                  state #nil)
  (set-rc-state-previous-echo-area-message! state #nil)
  (set-rc-state-also-record!                state #nil)
  (set-rc-state-recorded!                   state #nil)
  (set-rc-state-reread!                     state #nil)
  (set-rc-state-orig-kboard!                state #nil))

;; Internal test harness: srfi-9 accessors are not elisp-callable in
;; this build, so branch tests go through these narrow field helpers.
(define (%rc-test-state-ref rec field)
  (case field
    ((commandflag)                (rc-state-commandflag rec))
    ((map)                        (rc-state-map rec))
    ((prev-event)                 (rc-state-prev-event rec))
    ((used-mouse-menu)            (rc-state-used-mouse-menu rec))
    ((used-mouse-menu-flag)       (rc-state-used-mouse-menu-flag rec))
    ((end-time)                   (rc-state-end-time rec))
    ((c)                          (rc-state-c rec))
    ((local-tag)                  (rc-state-local-tag rec))
    ((previous-echo-area-message) (rc-state-previous-echo-area-message rec))
    ((also-record)                (rc-state-also-record rec))
    ((recorded)                   (rc-state-recorded rec))
    ((reread)                     (rc-state-reread rec))
    ((orig-kboard)                (rc-state-orig-kboard rec))
    (else ((%c 'error) "Unknown rc-state test field: %S" field))))

(define (%rc-test-state-set! rec field value)
  (case field
    ((commandflag)                (set-rc-state-commandflag! rec value))
    ((map)                        (set-rc-state-map! rec value))
    ((prev-event)                 (set-rc-state-prev-event! rec value))
    ((used-mouse-menu)            (set-rc-state-used-mouse-menu! rec value))
    ((used-mouse-menu-flag)       (set-rc-state-used-mouse-menu-flag! rec value))
    ((end-time)                   (set-rc-state-end-time! rec value))
    ((c)                          (set-rc-state-c! rec value))
    ((local-tag)                  (set-rc-state-local-tag! rec value))
    ((previous-echo-area-message) (set-rc-state-previous-echo-area-message! rec value))
    ((also-record)                (set-rc-state-also-record! rec value))
    ((recorded)                   (set-rc-state-recorded! rec value))
    ((reread)                     (set-rc-state-reread! rec value))
    ((orig-kboard)                (set-rc-state-orig-kboard! rec value))
    (else ((%c 'error) "Unknown rc-state test field: %S" field)))
  #nil)

(define (%rc-test-with-state rec thunk)
  ((force %rc-record-stack-push) rec)
  (dynamic-wind
    (lambda () #f)
    (lambda () ((%c 'funcall) thunk))
    (lambda () ((force %rc-record-stack-pop)))))

;;;;
;;;; M8c — read_char_1 prologue splices.
;;;;

(define %rc-latch-input-was-pending
  (delay (%c '--rc-latch-input-was-pending)))

(define (rc-exit!)
  "Final tail of read_char_1: latch input_was_pending = input_pending
and return two values: state->c (the resolved event) and the
used-mouse-menu flag (M12 imp-2).  A nil rec (no state pushed)
yields (#nil #f).  See docs/keyboard.org §M8final."
  (let ((rec ((force %rc-record-current))))
    (cond
     ((%nilp rec) (values #nil #f))
     (else
      ((force %rc-latch-input-was-pending))
      (values (rc-state-c rec) (rc-state-used-mouse-menu-flag rec))))))

(define %rc-show-help-echo
  (delay (%c '--rc-show-help-echo)))
(define %rc-mouse-movement-event-p
  (delay (%c '--rc-mouse-movement-event-p)))
(define %rc-allow-echo-at-next-pause
  (delay (%c '--rc-allow-echo-at-next-pause)))
(define %add-command-key
  (delay (%c '--add-command-key)))
(define %echo-update
  (delay (%c '--echo-update)))
(define %rc-inc-num-input-events
  (delay (%c '--rc-inc-num-input-events)))
(define %rc-maybe-help-form-recursive-read
  (delay (%c '--rc-maybe-help-form-recursive-read)))
(define %this-command-key-count
  (delay (%c '--this-command-key-count)))

(define (rc-add-command-keys-and-echo! c also-record)
  "Add C and ALSO-RECORD to this-command-keys, then refresh echo state."
  (when (%nilp ((force %rc-mouse-movement-event-p) c))
    ;; Once we reread a character, echoing can happen the next time
    ;; we pause to read a new one.
    ((force %rc-allow-echo-at-next-pause)))
  ((force %add-command-key) c)
  (when (not (%nilp also-record))
    ((force %add-command-key) also-record))
  ((force %echo-update))
  #nil)

(define (rc-help-echo-and-help-form!)
  "Final read_char_1 tail.  Block 1: if state->c is a (help-echo
FRAME HELP WINDOW OBJECT POS), call show_help_echo and return
`goto-retry'.  Block 2: add state->c to this_command_keys (and
state->also_record) under the !reread / first-key / !timed gate,
update last_input_event + num_input_events.  Block 3: when
Vhelp_form and help_char_p match, recursively read_char until
non-BUFFERP under a dynwind that saves window configuration,
then repeat the read if state->c == fixnum 040 (space).  Returns
`goto-retry' or `fall-through'.  See docs/keyboard.org §M8n."
  (let ((rec ((force %rc-record-current))))
    (cond
     ((%nilp rec) 'fall-through)
     (else
      (let ((c (rc-state-c rec)))
        (cond
         ;; Block 1: help-echo display.
         ((and (pair? c) (eq? (car c) 'help-echo))
          ;; c is (help-echo FRAME HELP WINDOW OBJECT POS).
          (let* ((htem (cddr c))
                 (help (car htem))
                 (htem (cdr htem))
                 (window (car htem))
                 (htem (cdr htem))
                 (object (car htem))
                 (htem (cdr htem))
                 (position (car htem)))
            ((force %rc-show-help-echo) help window object position))
          ;; We stopped being idle for this event; undo that.
          (when (%nilp (rc-state-end-time rec))
            ((force %rc-timer-resume-idle)))
          'goto-retry)
         (else
          ;; Block 2: add to this_command_keys + echo + last-input-event.
          (when (and (or (%nilp (rc-state-reread rec))
                         (= ((force %this-command-key-count)) 0))
                     (%nilp (rc-state-end-time rec)))
            (rc-add-command-keys-and-echo!
             c (rc-state-also-record rec)))
          (set-symbol-value! 'last-input-event c)
          ((force %rc-inc-num-input-events))
          ;; Block 3: help_form recursive read.
          ((force %rc-maybe-help-form-recursive-read))
          'fall-through)))))))

(define %rc-input-method-call-and-handle
  (delay (%c '--rc-input-method-call-and-handle)))

(define (rc-input-method-dispatch!)
  "Input-method dispatch + record-if-unread.  Block 1: when
state->c is a printable ASCII fixnum, Vinput_method_function is
set, and we're at the first event of a key sequence, run the IM
inside a dynwind with this_command_keys / echo state save and
restore.  Returns `goto-retry' when IM consumed input without
producing events; otherwise installs new c and concats remaining
events onto Vunread_post_input_method_events.  Block 2: if
!state->recorded, record_char + state->recorded = true.  Returns
`goto-retry' or `fall-through'.  See docs/keyboard.org §M8m."
  (let ((rec ((force %rc-record-current))))
    (cond
     ((%nilp rec) 'fall-through)
     (else
      (let* ((c (rc-state-c rec))
             ;; Block 1 gate.
             (b1 (cond
                  ((and (%printable-ascii? c)
                        (not (%nilp (symbol-value 'input-method-function)))
                        (%nilp (rc-state-prev-event rec)))
                   ((force %rc-input-method-call-and-handle)))
                  (else #nil))))
        (cond
         ((eq? b1 'goto-retry) 'goto-retry)
         (else
          ;; Block 2: record if the event bypassed the M8l record path.
          (when (%nilp (rc-state-recorded rec))
            ((force %rc-record-char) (rc-state-c rec))
            (set-rc-state-recorded! rec #t))
          'fall-through)))))))

(define %stringp       (delay (%c 'stringp)))
(define %char-table-p  (delay (%c 'char-table-p)))
(define %characterp    (delay (%c 'characterp)))
(define %aref          (delay (%c 'aref)))
(define %length        (delay (%c 'length)))

(define (rc-translate-kbd-table c)
  "M8l Block 1 in Scheme: apply current_kboard's
keyboard-translate-table (a DEFVAR_KBOARD, accessible via
symbol-value) to fixnum C when in range for the table's type
(string, vector/pseudovector, or char-table).  Returns the
translated value, or C unchanged when no translation applies.
nil entries in the table mean no translation (the aref result
is returned only when non-nil)."
  (let ((table (symbol-value 'keyboard-translate-table)))
    (cond
     ((%nilp table) c)
     (((force %stringp) table)
      (if (< c ((force %length) table))
          (or ((force %aref) table c) c)
          c))
     (((force %char-table-p) table)
      (if ((force %characterp) c)
          (or ((force %aref) table c) c)
          c))
     (else
      ;; VECTOR_OR_PSEUDOVECTORP: anything with a length that isn't
      ;; nil, a string, or a char-table.
      (if (< c ((force %length) table))
          (or ((force %aref) table c) c)
          c)))))
(define %rc-record-char
  (delay (%c '--rc-record-char)))
(define %rc-echo-area-wipe
  (delay (%c '--rc-echo-area-wipe)))
(define %setcar (delay (%c 'setcar)))
(define %current-message (delay (%c 'current-message)))

(define (rc-maybe-synthesize-menu-bar-event!)
  "M8l Block 2 in Scheme.  When state->c is a mouse-position event
whose posn is menu-bar / tab-bar / tool-bar, rewrites the event's
posn to (list posn), pushes the original onto unread-command-events
(wrapped in (t . c) when end-time is set, plain otherwise with
also-record set), installs the bare posn symbol into rec.c, and
returns the bare posn.  Returns nil when no synthesis happened.

The C macros xevent_start / POSN_POSN / POSN_SET_POSN are pure
Lisp data ops — cadr, cadr-of-cadr, and setcar-on-cdr — so the
body needs no C primitive beyond elisp setcar."
  (let ((rec ((force %rc-record-current))))
    (cond
     ((%nilp rec) #nil)
     (else
      (let ((c (rc-state-c rec)))
        (cond
         ;; EVENT_HAS_PARAMETERS + nested-CONSP gate on xevent_start.
         ((not (and (pair? c)
                    (pair? (cdr c))
                    (pair? (cadr c))
                    (pair? (cdr (cadr c)))))
          #nil)
         (else
          (let ((posn (cadr (cadr c))))
            (cond
             ((not (or (eq? posn 'menu-bar)
                       (eq? posn 'tab-bar)
                       (eq? posn 'tool-bar)))
              #nil)
             (else
              ;; Change menu-bar to (menu-bar) as the event "position".
              ((force %setcar) (cdr (cadr c)) (list posn))
              (cond
               ((not (%nilp (rc-state-end-time rec)))
                (set-symbol-value!
                 'unread-command-events
                 (cons (cons 't c)
                       (symbol-value 'unread-command-events))))
               (else
                (set-rc-state-also-record! rec c)
                (set-symbol-value!
                 'unread-command-events
                 (cons c (symbol-value 'unread-command-events)))))
              (set-rc-state-c! rec posn)
              posn))))))))))

(define (%printable-ascii? c)
  "True when C is a fixnum in the printable ASCII range used by
the input-method echo-area save (space..255, not 127)."
  (and (integer? c)
       (<= 32 c)
       (< c 256)
       (not (= c 127))))

(define (rc-event-translate-and-record!)
  "Post-special-event translate + record + wipe.  Block 1: FIXNUMP
EOF check (returns `goto-exit' for c == -1) then keyboard-translate-
table lookup; Block 2: menu-bar/tab-bar/tool-bar synthesis (push
original onto Vunread_command_events, set state->c to the bare posn
symbol); Block 3: record_char + also_record, save echo-area for
input-method when appropriate, wipe echo area unless state->c is a
help-echo / switch-frame / select-window event.  Returns `goto-exit'
or `fall-through'.  See docs/keyboard.org §M8l."
  (let ((rec ((force %rc-record-current))))
    (cond
     ((%nilp rec) 'fall-through)
     (else
      (let ((c (rc-state-c rec)))
        ;; Block 1: FIXNUMP + keyboard-translate-table.
        (cond
         ((and (integer? c) (= c -1)) 'goto-exit)
         (else
          (let ((c (cond
                    ((integer? c)
                     (let ((d (rc-translate-kbd-table c)))
                       (when (not (eq? c d))
                         (set-rc-state-c! rec d))
                       d))
                    (else c))))
            ;; Block 2: menu-bar synthesis.
            (let* ((maybe-posn (rc-maybe-synthesize-menu-bar-event!))
                   (c (if (%nilp maybe-posn) c maybe-posn)))
              ;; Block 3a: record_char + also_record.
              ((force %rc-record-char) c)
              (set-rc-state-recorded! rec #t)
              (let ((also-record (rc-state-also-record rec)))
                (when (not (%nilp also-record))
                  ((force %rc-record-char) also-record)))
              ;; Block 3b: pre-input-method echo-area save.
              (when (and (%printable-ascii? c)
                         (not (%nilp (symbol-value 'input-method-function))))
                (let ((cur ((force %current-message))))
                  (set-rc-state-previous-echo-area-message! rec cur)
                  (set-symbol-value! 'input-method-previous-message cur)))
              ;; Block 3c: echo-area wipe.
              (when (or (not (pair? c))
                        (and (not (eq? (car c) 'help-echo))
                             (not (eq? (car c) 'switch-frame))
                             (not (eq? (car c) 'select-window))))
                ((force %rc-echo-area-wipe)))
              'fall-through)))))))))

(define %rc-special-event-map-lookup
  (delay (%c '--rc-special-event-map-lookup)))
(define %rc-timer-resume-idle
  (delay (%c '--rc-timer-resume-idle)))
(define %bufferp (delay (%c 'bufferp)))
(define %current-buffer (delay (%c 'current-buffer)))
(define %command-execute (delay (%c 'command-execute)))
(define %memq (delay (%c 'memq)))

(define (rc-bufferp-and-special-event-map!)
  "BUFFERP early-exit + special-event-map dispatch.  If state->c
is a buffer, return `goto-exit'.  Otherwise look up state->c in
Vspecial_event_map; on hit, execute the bound command via
call4 Qcommand_execute and return `goto-exit' (when
current_buffer changed; state->c is reset to -2 first) or
`goto-retry' (otherwise).  Returns `fall-through' when no
special command matched.  See docs/keyboard.org §M8k."
  (let ((rec ((force %rc-record-current))))
    (cond
     ((%nilp rec) 'fall-through)
     (else
      (let ((c (rc-state-c rec)))
        (cond
         ;; Block 1: BUFFERP early-exit.
         ((not (%nilp ((force %bufferp) c))) 'goto-exit)
         (else
          ;; Block 2: special-event-map dispatch.
          (let ((tem ((force %rc-special-event-map-lookup) c)))
            (cond
             ((%nilp tem) 'fall-through)
             (else
              (let ((prev-buffer ((force %current-buffer))))
                (set-symbol-value! 'last-input-event c)
                ((force %command-execute) tem #nil (vector c) #t)
                (when (and (pair? c)
                           (not (%nilp ((force %memq) (car c)
                                        (symbol-value 'while-no-input-ignore-events))))
                           (%nilp (rc-state-end-time rec)))
                  ;; We stopped being idle for this event; undo that.
                  ((force %rc-timer-resume-idle)))
                ;; HAVE_NS: latch input_was_pending for ns-unput-working-text.
                (when (and (pair? c) (eq? (car c) 'ns-unput-working-text))
                  ((force %rc-latch-input-was-pending)))
                (cond
                 ((not (eq? prev-buffer ((force %current-buffer))))
                  ;; The command may have changed the keymaps.  Pretend
                  ;; there is input in another keyboard and return.
                  (set-rc-state-c! rec -2)
                  'goto-exit)
                 (else 'goto-retry)))))))))))))

(define %rc-end-time-expired-p
  (delay (%c '--rc-end-time-expired-p)))

;;; Lazy reference to the Scheme (emacs main-queue) port (M12 imp-3).
;;; Deliberately NOT a #:use-module: read-char is loaded by the prelude
;;; (prelude/load.scm) BEFORE syms_of_keyboard registers the C DEFUNs,
;;; and (emacs main-queue) pulls in (emacs kbd-buffer) → (emacs
;;; lispy-event), whose top-level forms force C DEFUNs at load time.
;;; The delay defers the module load to the first read — at runtime,
;;; after syms_of_keyboard — matching how kbd-buffer itself is loaded
;;; via scm_c_public_ref (the m12-plan's "same as kbd-buffer today"
;;; claim assumed lazy loading; an eager use-module here breaks the
;;; prelude, see FIX-20260821-guilemacs).
(define %read-decoded-event-from-main-queue
  (delay (module-ref (resolve-module '(emacs main-queue) #:ensure #t)
                     'read-decoded-event-from-main-queue)))

(define (rc-maybe-redisplay-when-no-input! commandflag)
  "Redisplay when COMMANDFLAG allows it and no input is pending.
Hoisted from the M8j C helper; C now exposes only the raw input
flags, timer-aware input probe, and redisplay action."
  (when (and (>= commandflag 0)
             (%nilp ((force %rc-input-pending)))
             (%nilp ((force %rc-detect-input-pending-run-timers))))
    ((force %rc-redisplay)))
  #nil)

(define (rc-install-read-event! rec c)
  "Install raw M8j read event C into REC and return the loop control symbol."
  (cond
   ((and (%nilp c)
         (not (%nilp (rc-state-end-time rec)))
         (not (%nilp ((force %rc-end-time-expired-p)))))
    (set-rc-state-c! rec c)
    'goto-exit)
   ((and (integer? c) (= c -2))
    (set-rc-state-c! rec c)
    'return-wrong-kboard)
   (else
    (let ((c (cond
              ((and (pair? c) (%elisp-t? (car c)))
               (cdr c))
              ((and (pair? c) (eq? (car c) 'no-record))
               (set-rc-state-recorded! rec #t)
               (cdr c))
              (else c))))
      (set-rc-state-c! rec c)
      'continue))))

(define (rc-read-and-install-event!)
  "Read one raw M8j event, peel wrappers, and install it into the current state.
M12 imp-5: calls the Scheme (emacs main-queue) port directly — the
C seam it replaces was deleted by imp-4."
  (let ((rec ((force %rc-record-current))))
    (cond
     ((%nilp rec) 'continue)
     (else
      (call-with-values
        (lambda ()
          ((force %read-decoded-event-from-main-queue)
           (rc-state-end-time rec)
           (rc-state-local-tag rec)
           (rc-state-prev-event rec)))
        (lambda (event used-mouse-menu)
          ;; Consume the returned used-mouse-menu through the caller's
          ;; bool pointer (RC_SLOT_USED_MOUSE_MENU) exactly as the
          ;; deleted C seam did (imp-4).  --rc-mark-used-mouse-menu-true
          ;; is kept (deferrable imp-5 half).
          (when (not (%nilp used-mouse-menu))
            ((force %rc-mark-used-mouse-menu-true) rec)
            (set-rc-state-used-mouse-menu-flag! rec #t))
          (rc-install-read-event! rec event)))))))

(define (%rc-test-install-read-event c)
  "Test-only entry for Scheme M8j postprocessing without blocking for input."
  (let ((rec ((force %rc-record-current))))
    (cond
     ((%nilp rec) 'continue)
     (else (rc-install-read-event! rec c)))))

(define (rc-wrong-kboard-and-non-reread!)
  "Blocking-read + non-reread fixup loop.  Calls
rc-read-and-install-event! (which drives state->c through the Scheme
(emacs main-queue) port, M12 imp-5), peels Qt / Qno_record wrappers,
and loops back to retry the blocking read when c is still nil after a
redisplay.  Returns `goto-exit' (end_time expired),
`return-wrong-kboard' (caller returns -2), or `fall-through' (state->c
is non-nil).  See docs/keyboard.org §M8j."
  (let ((rec ((force %rc-record-current))))
    (cond
     ((%nilp rec) 'fall-through)
     (else
      (let loop ()
        ;; Block A — wrong_kboard label position.
        (let ((r (if (%nilp (rc-state-c rec))
                     (rc-read-and-install-event!)
                     'continue)))
          (cond
           ((eq? r 'goto-exit) 'goto-exit)
           ((eq? r 'return-wrong-kboard) 'return-wrong-kboard)
           (else
            ;; Block B — non_reread label position.
            (when (%nilp (rc-state-end-time rec))
              ((force %rc-timer-stop-idle)))
            (cond
             ((%nilp (rc-state-c rec))
              (rc-maybe-redisplay-when-no-input!
               (rc-state-commandflag rec))
              (loop))
             (else 'fall-through))))))))))

(define %rc-pop-current-kboard-queue
  (delay (%c '--rc-pop-current-kboard-queue)))
(define %rc-find-other-kboard-with-data
  (delay (%c '--rc-find-other-kboard-with-data)))
(define %current-kboard
  (delay (%c 'current-kboard)))
(define %kboard-eq
  (delay (%c 'kboard-eq)))

(define (%drain-unread-command-events! rec)
  "Block 2 of M8i: pop one event from Vunread_command_events,
peeling the (Qt . event) and (Qno_record . event) wrappers and
setting rec's recorded/reread bits accordingly.  Returns the new
c value (which may be nil if the queue was empty)."
  (let ((q (symbol-value 'unread-command-events)))
    (cond
     ((not (pair? q))
      (rc-state-c rec))
     (else
      (set-symbol-value! 'unread-command-events (cdr q))
      (let ((c0 (car q)))
        (let ((c1 (cond
                   ((and (pair? c0) (%elisp-t? (car c0)))
                    (cdr c0))
                   (else
                    (let ((c2 (if (and (pair? c0)
                                       (eq? (car c0) 'no-record))
                                  (begin
                                    (set-rc-state-recorded! rec #t)
                                    (cdr c0))
                                  c0)))
                      (set-rc-state-reread! rec #t)
                      c2)))))
          (set-rc-state-c! rec c1)
          c1))))))

(define (%maybe-pop-current-kboard-queue! rec c)
  "Block 3 of M8i: when c is nil, try to dequeue from the current
KBOARD's side queue; if data was popped, install it into rec.c and
return it.  Returns the (possibly unchanged) c value."
  (cond
   ((not (%nilp c)) c)
   (else
    (let ((c0 ((force %rc-pop-current-kboard-queue))))
      (cond
       ((%nilp c0) c)
       (else
        (set-rc-state-c! rec c0)
        c0))))))

(define (rc-prologue-kboard-and-queues!)
  "Four blocks after M8h: wrong-kboard detection, Vunread_command_events
drain, current-kboard side-queue read, and other-kboard scan.  Mutates
state->c / state->recorded / state->reread / current_kboard /
Vunread_command_events / input_pending / Vlast_event_frame in place.
Returns `return-wrong-kboard' (caller returns -2) or `fall-through'.
See docs/keyboard.org §M8i."
  (let ((rec ((force %rc-record-current))))
    (cond
     ((%nilp rec) 'fall-through)
     (else
      (let* ((c0 (rc-state-c rec))
             (orig (rc-state-orig-kboard rec))
             ;; Block 1: wrong-kboard detection.
             (wrong-kboard? (and (%nilp c0)
                                 (or (%nilp orig)
                                     (%nilp ((force %kboard-eq)
                                             ((force %current-kboard))
                                             orig))))))
        (cond
         (wrong-kboard? 'return-wrong-kboard)
         (else
          ;; Block 2: drain Vunread_command_events.
          (let* ((c1 (%drain-unread-command-events! rec))
                 ;; Block 3: read from current KBOARD's side queue.
                 (c2 (%maybe-pop-current-kboard-queue! rec c1)))
            ;; Block 4: scan other kboards.
            (cond
             ((and (%nilp c2)
                   (not (%nilp ((force %rc-find-other-kboard-with-data)))))
              'return-wrong-kboard)
             (else 'fall-through))))))))))

(define %rc-read-char-x-menu-prompt
  (delay (%c '--rc-read-char-x-menu-prompt)))
(define %rc-timer-stop-idle
  (delay (%c '--rc-timer-stop-idle)))
(define %rc-refresh-last-non-minibuf-size
  (delay (%c '--rc-refresh-last-non-minibuf-size)))

(define (rc-auto-save-delay-level)
  "M8h helper in Scheme: refresh `last_non_minibuf_size' via the C
shim --rc-refresh-last-non-minibuf-size (MINI_WINDOW_P guard +
Z - BEG assignment), then compute the buffer-size-scaled auto-save
delay level.  The level is 4 for files under ~50k, 7 at 100k, 9 at
200k, 11 at 300k, 12 at 500k, and 15 at 1 meg."
  (let* ((buf-size ((force %rc-refresh-last-non-minibuf-size)))
         (buffer-size (+ (ash buf-size -8) 1))
         (dl (let loop ((dl 0) (bs buffer-size))
               (if (<= bs 64)
                   dl
                   (loop (+ dl 1) (- bs (ash bs -2)))))))
    (max dl 4)))
(define %rc-sit-for-timeout
  (delay (%c '--rc-sit-for-timeout)))
(define %rc-gc-collect-a-little
  (delay (%c '--rc-gc-collect-a-little)))

(define (%interactive?)
  "Scheme port of the commands.h INTERACTIVE macro."
  (and (%nilp (symbol-value 'executing-kbd-macro))
       (%nilp (symbol-value 'noninteractive))))

(define (rc-auto-save-by-timeout-and-gc! commandflag)
  "M8h Block 2 in Scheme: when enough idle time elapses, fire
do-auto-save + redisplay; either way, GC_collect_a_little when no
input is pending.  Caller has already checked INTERACTIVE and
c-is-nil.  C exposes only the buffer-size-scaled delay-level, the
sit_for primitive, and the GC trigger; everything else
(`auto-save-timeout', `most-positive-fixnum', `do-auto-save',
`auto-save-no-message', `num-nonmacro-input-events', and the
detect-input/redisplay primitives) is reachable from Scheme."
  (let ((cf commandflag)
        (delay-level (rc-auto-save-delay-level))
        (ast (symbol-value 'auto-save-timeout)))
    ;; Auto save if enough time goes by without input.
    (when (and (not (= cf 0))
               (not (= cf -2))
               (> (symbol-value 'num-nonmacro-input-events)
                  ((force %rc-last-auto-save)))
               (integer? ast)
               (> ast 0))
      ;; Mirror the C: cap timeout to (MOST_POSITIVE_FIXNUM / delay_level) * 4,
      ;; then scale by delay_level / 4.
      (let* ((mpf (symbol-value 'most-positive-fixnum))
             (capped (min ast (* (quotient mpf delay-level) 4)))
             (timeout (quotient (* delay-level capped) 4))
             (tem0 ((force %rc-sit-for-timeout) timeout)))
        (when (and (%elisp-t? tem0)
                   (not (pair? (symbol-value 'unread-command-events))))
          ((force %do-auto-save)
           (if (%nilp (symbol-value 'auto-save-no-message)) #nil #t)
           #nil)
          ;; Hooks may modify buffers during auto-save.
          ((force %rc-redisplay)))))
    ;; If there is still no input available, ask for GC.
    (when (%nilp ((force %rc-detect-input-pending-run-timers)))
      ((force %rc-gc-collect-a-little))))
  #nil)

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
  (let ((rec ((force %rc-record-current))))
    (cond
     ((%nilp rec) 'fall-through)
     (else
      (let ((map (rc-state-map rec))
            (prev-event (rc-state-prev-event rec)))
        (cond
         ;; Block 1: X-menu read.
         ((and (not (%nilp ((force %keymapp) map)))
               (%interactive?)
               (not (%nilp prev-event))
               (pair? prev-event)
               (not (eq? (car prev-event) 'menu-bar))
               (not (eq? (car prev-event) 'tab-bar))
               (not (eq? (car prev-event) 'tool-bar))
               (not (pair? (symbol-value 'unread-command-events))))
          (call-with-values
            (lambda () ((force %rc-read-char-x-menu-prompt)))
            (lambda (event used-mouse-menu-p)
              (set-rc-state-c! rec event)
              (when used-mouse-menu-p
                (set-rc-state-used-mouse-menu-flag! rec #t))))
          ;; Now that we have read an event, Emacs is not idle.
          (when (%nilp (rc-state-end-time rec))
            ((force %rc-timer-stop-idle)))
          'goto-exit)
         (else
          ;; Block 2: maybe autosave and/or GC due to idleness.
          (when (and (%interactive?) (%nilp (rc-state-c rec)))
            (rc-auto-save-by-timeout-and-gc!
             (rc-state-commandflag rec)))
          'fall-through)))))))

(define %rc-timer-start-idle
  (delay (%c '--rc-timer-start-idle)))
(define %rc-minibuf-level
  (delay (%c '--minibuf-level)))
(define %rc-current-kboard-immediate-echo-p
  (delay (%c '--current-kboard-immediate-echo-p)))
(define %rc-echo-keystrokes-p
  (delay (%c '--echo-keystrokes-p)))
(define %rc-echo-area-usable-for-echo-p
  (delay (%c '--rc-echo-area-usable-for-echo-p)))

(define (rc-should-immediate-echo-p rec)
  "M8g Block 2 gate in Scheme.  Returns #t when all of:
 minibuf_level 0, end_time nil, immediate_echo off, key-count
 >0 or keystrokes prefix non-empty, !noninteractive,
 echo_keystrokes_p, and echo area usable.  The echo-area
 liveness sub-predicate delegates to the C primitive
 --rc-echo-area-usable-for-echo-p."
  (and (= ((force %rc-minibuf-level)) 0)
       (%nilp (rc-state-end-time rec))
       (%nilp ((force %rc-current-kboard-immediate-echo-p)))
       (or (> ((force %this-command-key-count)) 0)
           (not (%nilp ((%c 'internal-echo-keystrokes-prefix)))))
       (%nilp (symbol-value 'noninteractive))
       (not (%nilp ((force %rc-echo-keystrokes-p))))
       (not (%nilp ((force %rc-echo-area-usable-for-echo-p))))))
(define %rc-sit-for-echo-keystrokes
  (delay (%c '--rc-sit-for-echo-keystrokes)))

(define (rc-sit-for-and-maybe-echo!)
  "M8g Block 2 non-mouse path in Scheme: sit_for `echo-keystrokes'
seconds (with getctag saved/restored atomically by the C primitive),
then echo_now when no input arrived and the unread-command-events
queue is empty.  The save/restore stays in C so a non-local exit
through sit_for can't leak getctag back to the caller; the result-
predicate and conditional echo move out to Scheme."
  (let ((tem0 ((force %rc-sit-for-echo-keystrokes))))
    (when (and (%elisp-t? tem0)
               (not (pair? (symbol-value 'unread-command-events))))
      ((force %echo-now))))
  #nil)
(define %rc-last-auto-save
  (delay (%c '--rc-last-auto-save)))
(define %do-auto-save
  (delay (%c 'do-auto-save)))
(define %echo-now
  (delay (%c '--echo-now)))

(define (rc-maybe-auto-save-by-keystroke!)
  "M8g Block 3 in Scheme: when the keystroke counter has crossed
the auto-save threshold and no input is pending, fire do-auto-save
+ redisplay.  Caller has already checked that commandflag is
neither 0 nor -2.  C now exposes only the file-static last-auto-save
counter; `auto-save-interval' / `num-nonmacro-input-events' /
`auto-save-no-message' are DEFVAR_INT or DEFVAR_BOOL and reachable
via symbol-value."
  (let ((interval (symbol-value 'auto-save-interval)))
    (when (and (> interval 0)
               (> (- (symbol-value 'num-nonmacro-input-events)
                     ((force %rc-last-auto-save)))
                  (max interval 20))
               (%nilp ((force %rc-detect-input-pending-run-timers))))
      ((force %do-auto-save)
       (if (%nilp (symbol-value 'auto-save-no-message)) #nil #t)
       #nil)
      ;; Hooks may modify buffers during auto-save.
      ((force %rc-redisplay))))
  #nil)

(define (rc-prologue-idle-echo-autosave!)
  "Three pure-side-effect blocks before the blocking input wait:
idle-timer start, immediate-echo start (with sit_for delay for
non-mouse events), and auto-save by keystroke count.  Always
returns nil — caller falls through.  See docs/keyboard.org §M8g."
  (let ((rec ((force %rc-record-current))))
    (cond
     ((%nilp rec) #nil)
     (else
      (let ((end-time-nil? (%nilp (rc-state-end-time rec))))
        ;; Block 1: idle-timer start.
        (when end-time-nil?
          ((force %rc-timer-start-idle)))
        ;; Block 2: immediate echo.
        (when (rc-should-immediate-echo-p rec)
          (if (pair? (rc-state-prev-event rec))
              ;; After a mouse event, start echoing right away.
              ((force %echo-now))
              (rc-sit-for-and-maybe-echo!)))
        ;; Block 3: auto-save by keystroke count.
        (let ((cf (rc-state-commandflag rec)))
          (when (and (not (= cf 0)) (not (= cf -2)))
            (rc-maybe-auto-save-by-keystroke!)))
        #nil)))))

(define %rc-echo-area-has-wrong-kboard-p
  (delay (%c '--rc-echo-area-has-wrong-kboard-p)))
(define %rc-cancel-echoing
  (delay (%c '--cancel-echoing)))
(define %rc-echo-dash
  (delay (%c '--echo-dash)))

(define (rc-echo-cancel-or-dash)
  "M8f helper in Scheme: cancel echoing when the echo area belongs
to a different kboard, otherwise append a dash separator."
  (if (not (%nilp ((force %rc-echo-area-has-wrong-kboard-p))))
      ((force %rc-cancel-echoing))
      ((force %rc-echo-dash))))
(define %rc-read-char-minibuf-menu-prompt
  (delay (%c '--rc-read-char-minibuf-menu-prompt)))
(define %rc-detect-input-pending-run-timers
  (delay (%c '--rc-detect-input-pending-run-timers)))
(define %keymapp
  (delay (%c 'keymapp)))

(define (rc-prologue-echo-and-menu!)
  "Echo-cancel-or-dash + minibuf-menu-prompt blocks before the
blocking read.  Returns one of `return-wrong-kboard' (caller
returns -2 from read_char_1 — the wrong_kboard_jmpbuf code),
`goto-exit' (caller goto exit; state->c installed), or
`fall-through' (caller continues to the next block).  See
docs/keyboard.org §M8f."
  (let ((rec ((force %rc-record-current))))
    (cond
     ((%nilp rec) 'fall-through)
     (else
      (rc-echo-cancel-or-dash)
      (set-rc-state-c! rec #nil)
      (let ((map (rc-state-map rec))
            (prev-event (rc-state-prev-event rec)))
        (if (and (not (%nilp ((force %keymapp) map)))
                 (%nilp (symbol-value 'noninteractive))
                 (not (%nilp prev-event))
                 (not (pair? prev-event))
                 (not (pair? (symbol-value 'unread-command-events)))
                 (%nilp ((force %rc-detect-input-pending-run-timers))))
            (let ((c ((force %rc-read-char-minibuf-menu-prompt)
                      (rc-state-commandflag rec)
                      map)))
              (cond
               ((and (integer? c) (= c -2)) 'return-wrong-kboard)
               ((%nilp c) 'fall-through)
               (else
                (set-rc-state-c! rec c)
                'goto-exit)))
            'fall-through))))))

(define %rc-echo-message-buffer-is-current
  (delay (%c '--rc-echo-message-buffer-is-current)))
(define %rc-pin-echo-message-buffer-to-current
  (delay (%c '--rc-pin-echo-message-buffer-to-current)))
(define %rc-input-pending
  (delay (%c '--rc-input-pending)))
(define %rc-input-was-pending
  (delay (%c '--rc-input-was-pending)))
(define %rc-swallow-events
  (delay (%c '--rc-swallow-events)))
(define %rc-help-echo-redisplay-preserve-p
  (delay (%c '--rc-help-echo-redisplay-preserve-p)))
(define %rc-redisplay-preserve-echo-area
  (delay (%c '--rc-redisplay-preserve-echo-area)))
(define %rc-redisplay
  (delay (%c '--rc-redisplay)))

(define (rc-redisplay-and-wait-block!)
  "Swallow non-user-visible events, then redisplay until input state
converges.  Hoisted from the M8e C helper; C still exposes only the
raw input flags and redisplay actions."
  ;; If there is pending input, process any events which are not
  ;; user-visible, such as X selection_request events.
  (when (or (not (%nilp ((force %rc-input-pending))))
            (not (%nilp ((force %rc-detect-input-pending-run-timers)))))
    ((force %rc-swallow-events)))
  ;; Redisplay if no pending input, mirroring the original C loop:
  ;; while (!(input_pending && input_was_pending)) { ... }.
  (let loop ()
    (when (not (and (not (%nilp ((force %rc-input-pending))))
                    (not (%nilp ((force %rc-input-was-pending))))))
      ((force %rc-latch-input-was-pending))
      (if (not (%nilp ((force %rc-help-echo-redisplay-preserve-p))))
          ((force %rc-redisplay-preserve-echo-area))
          ((force %rc-redisplay)))
      (when (not (%nilp ((force %rc-input-pending))))
        ((force %rc-swallow-events))
        (loop))))
  #nil)

(define (rc-prologue-redisplay!)
  "Redisplay loop in the read_char_1 prologue.  When the current
read_char's commandflag is >= 0, swallow non-user-visible events
and redisplay until convergence, then pin echo_message_buffer
when commandflag == 0.  Always returns nil — caller falls
through.  See docs/keyboard.org §M8e."
  (let ((rec ((force %rc-record-current))))
    (cond
     ((%nilp rec) #nil)
     (else
      (let ((cf (rc-state-commandflag rec)))
        (cond
         ((< cf 0) #nil)
         (else
          (let ((echo-current ((force %rc-echo-message-buffer-is-current))))
            (rc-redisplay-and-wait-block!)
            (when (and (= cf 0) (not (%nilp echo-current)))
              ((force %rc-pin-echo-message-buffer-to-current)))
            #nil))))))))

(define %rc-pin-event-frame-to-macro
  (delay (%c '--rc-pin-event-frame-to-macro)))
(define %rc-take-unread-switch-frame
  (delay (%c '--rc-take-unread-switch-frame)))
(define %get-internal-last-event-frame
  (delay (%c '--get-internal-last-event-frame)))
(define %set-internal-last-event-frame!
  (delay (%c '--set-internal-last-event-frame)))
(define %get-unread-switch-frame
  (delay (%c '--get-unread-switch-frame)))
(define %set-unread-switch-frame!
  (delay (%c '--set-unread-switch-frame)))
(define %selected-frame
  (delay (%c 'selected-frame)))

(define %rc-record-current   (delay (%c '--rc-record)))
(define %rc-mark-used-mouse-menu-true
  (delay (%c '--rc-mark-used-mouse-menu-true)))

(define (%peel-popup-menu-cons c)
  "Undo Fx_popup_menu's nested-cons unread of (sym/fixnum . nil) —
return its car, otherwise C unchanged."
  (if (and (pair? c)
           (or (symbol? (car c)) (integer? (car c)))
           (%nilp (cdr c)))
      (car c)
      c))

(define (%drain-block-3 rec)
  "Try Vunread_input_method_events.  Returns the dispatch symbol."
  (let ((q (symbol-value 'unread-input-method-events)))
    (if (pair? q)
        (begin
          (set-symbol-value! 'unread-input-method-events (cdr q))
          (set-rc-state-c! rec (%peel-popup-menu-cons (car q)))
          (set-rc-state-reread! rec #t)
          'reread-for-input-method)
        'fall-through)))

(define (%drain-block-2 rec)
  "Try Vunread_command_events.  Returns the dispatch symbol; falls
through to block 3 if the queue is empty."
  (let ((q (symbol-value 'unread-command-events)))
    (if (not (pair? q))
        (%drain-block-3 rec)
        (begin
          (set-symbol-value! 'unread-command-events (cdr q))
          (let* ((c0 (car q))
                 ;; sit-for's (t . event) marker peels here;
                 ;; otherwise no-record / reread bookkeeping.
                 (c1 (cond
                      ((and (pair? c0) (%elisp-t? (car c0)))
                       (cdr c0))
                      (else
                       (let ((c (if (and (pair? c0)
                                         (eq? (car c0) 'no-record))
                                    (begin
                                      (set-rc-state-recorded! rec #t)
                                      (cdr c0))
                                    c0)))
                         (set-rc-state-reread! rec #t)
                         c))))
                 ;; Fx_popup_menu wraps disabled menu items as
                 ;; (SYM . disabled); peel and remember.
                 (was-disabled (and (pair? c1)
                                    (eq? (cdr c1) 'disabled)
                                    (or (symbol? (car c1))
                                        (integer? (car c1)))))
                 (c2 (if was-disabled (car c1) c1)))
            (when (or was-disabled
                      (eq? c2 'tool-bar)
                      (eq? c2 'tab-bar)
                      (eq? c2 'menu-bar))
              ((force %rc-mark-used-mouse-menu-true) rec)
              (set-rc-state-used-mouse-menu-flag! rec #t))
            (set-rc-state-c! rec c2)
            'reread-for-input-method)))))

(define (internal-handle-focus-in event)
  "Internally handle focus-in events.  May generate an artificial
switch-frame event.  EVENT is `(focus-in FRAME)'.  Ported from C
DEFUN internal-handle-focus-in 2026-05-29."
  (let* ((tail (and (pair? event)
                    (eq? (car event) 'focus-in)
                    (cdr event)))
         (frame (and (pair? tail) (car tail))))
    (unless (and frame ((%c 'framep) frame))
      ((%c 'error) "Invalid focus-in event"))
    ;; Conceptually, the concept of window-manager focus on a
    ;; particular frame and the Emacs selected frame shouldn't be
    ;; related, but for a long time, we automatically switched the
    ;; selected frame in response to focus events, so keep doing that.
    (let* ((old ((force %get-internal-last-event-frame)))
           (sel ((force %selected-frame)))
           (switching (and (not (eq? frame old))
                           (not (eq? frame sel)))))
      ((force %set-internal-last-event-frame!) frame)
      (when (or switching
                (not (%nilp ((force %get-unread-switch-frame)))))
        ((force %set-unread-switch-frame!) (list 'switch-frame frame)))
      #nil)))

(define (%at-end-of-macro?)
  "Scheme port of at_end_of_macro_p (src/macros.c).  Caller must
ensure executing-kbd-macro is non-nil."
  (let ((m (symbol-value 'executing-kbd-macro)))
    (or (eq? m #t)
        (>= (symbol-value 'executing-kbd-macro-index)
            ((%c 'length) m)))))

(define %char-meta-bit #x8000000)        ; CHAR_META, src/lisp.h:2900

(define (%try-kbd-macro-block rec)
  "Block 1 of M8d: pull the next char/event from the executing
macro buffer, decoding the meta high-bit for STRINGP macros."
  ((force %rc-pin-event-frame-to-macro))
  (let* ((macro (symbol-value 'executing-kbd-macro))
         (idx   (symbol-value 'executing-kbd-macro-index))
         (c     ((%c 'aref) macro idx))
         (c2    (if (and ((%c 'stringp) macro)
                         (integer? c)
                         (not (zero? (logand c #x80)))
                         (<= c #xff))
                    (logior %char-meta-bit (logand c #x7f))
                    c)))
    (set-symbol-value! 'executing-kbd-macro-index (+ idx 1))
    (set-rc-state-c! rec c2)
    'from-macro))

(define (%try-switch-frame-block rec)
  "Block 2 of M8d: take the C-side unread_switch_frame; if set,
install it into state->c and return reread-first."
  (let ((sf ((force %rc-take-unread-switch-frame))))
    (cond
     ((%nilp sf) 'fall-through)
     (else
      (set-rc-state-c! rec sf)
      ;; This event should make it into this_command_keys and get
      ;; echoed again, so we do NOT set `reread'.
      'reread-first))))

(define (rc-prologue-macro-or-switch-frame!)
  "Two early-exit blocks after the unread-events drain:
in-progress kbd-macro replay, and pending switch-frame event.
Returns `from-macro', `reread-first', or `fall-through' for
3-way C control flow.  See docs/keyboard.org §M8d.

Migrated from C 2026-05-29: body lives here; the two C shims
--rc-pin-event-frame-to-macro and --rc-take-unread-switch-frame
give Scheme write/take access to the C-side state."
  (let ((rec ((force %rc-record-current))))
    (cond
     ((%nilp rec) 'fall-through)
     (else
      (let ((macro (symbol-value 'executing-kbd-macro)))
        (cond
         ((and (not (%nilp macro)) (not (%at-end-of-macro?)))
          (%try-kbd-macro-block rec))
         (else
          (%try-switch-frame-block rec))))))))

(define (rc-prologue-drain-unread!)
  "Drain the three unread-events queues at the top of read_char_1.
The current (top-of-stack) read_char invocation's state is mutated
in place (c / reread / recorded / *used_mouse_menu).  Returns one
of `reread-first', `reread-for-input-method', or `fall-through' to
control the read-char-main caller's goto.  See docs/keyboard.org §M8c.

Migrated from C 2026-05-29: body lives here; rc-set on the record
uses srfi-9 setters; the foreign-pointer write for used_mouse_menu
goes through the small --rc-mark-used-mouse-menu-true C helper."
  (let ((rec ((force %rc-record-current))))
    (cond
     ((%nilp rec) 'fall-through)
     (else
      (set-rc-state-recorded! rec #nil)
      ;; Block 1: unread-post-input-method-events.
      (let ((q (symbol-value 'unread-post-input-method-events)))
        (cond
         ((pair? q)
          (set-symbol-value! 'unread-post-input-method-events (cdr q))
          (set-rc-state-c! rec (%peel-popup-menu-cons (car q)))
          (set-rc-state-reread! rec #t)
          'reread-first)
         (else
          (set-rc-state-reread! rec #nil)
          (set-symbol-value! 'last-event-device #nil)
          (%drain-block-2 rec))))))))

;;;;
;;;; M8final — hoisted body of read_char_1.
;;;;
;;;; Drives the M8c..M8n bulk subrs in sequence.  Each named
;;;; sub-section either tail-calls the next section, jumps via
;;;; tail-call to one of the labelled sections (retry-section,
;;;; non-reread-section, reread-for-input-method-section,
;;;; reread-first-section, exit-section), or returns -2 for the
;;;; `wrong_kboard_jmpbuf' path.  Guile's TCO means `goto retry'
;;;; cycles do not grow the C stack.

(define (read-char-main jump?)
  "Hoisted body of read_char_1.  JUMP? is t when called after a
quit-handler longjmp re-entry (mirrors the C `if (jump) goto
non_reread').  Drives the M8c..M8n bulk subrs in sequence;
returns two values: the event (via --rc-exit) or -2 (for
wrong-kboard exits), and the used-mouse-menu flag.
See docs/keyboard.org §M8final."
  (define (retry-section)
    ;; M8c — drain unread events.
    (let ((r (rc-prologue-drain-unread!)))
      (cond
       ((eq? r 'reread-first)            (reread-first-section))
       ((eq? r 'reread-for-input-method) (reread-for-input-method-section))
       (else                             (after-drain)))))

  (define (after-drain)
    ;; M8d — kbd-macro + unread-switch-frame early exits.
    (let ((r (rc-prologue-macro-or-switch-frame!)))
      (cond
       ((eq? r 'from-macro)    (reread-for-input-method-section))
       ((eq? r 'reread-first)  (reread-first-section))
       (else                   (after-macro-sf)))))

  (define (after-macro-sf)
    ;; M8e — redisplay loop (always fall-through).
    (rc-prologue-redisplay!)
    ;; M8f — echo cancel/dash + minibuf-menu prompt.
    (let ((r (rc-prologue-echo-and-menu!)))
      (cond
       ((eq? r 'return-wrong-kboard)
        (let ((rec ((force %rc-record-current))))
          (values -2 (rc-state-used-mouse-menu-flag rec))))
       ((eq? r 'goto-exit)           (exit-section))
       (else                         (after-echo-menu)))))

  (define (after-echo-menu)
    ;; M8g — idle / immediate-echo / auto-save by keystroke (fall-through).
    (rc-prologue-idle-echo-autosave!)
    ;; M8h — X-menu + auto-save-by-timeout + GC.
    (let ((r (rc-prologue-xmenu-and-idle-gc!)))
      (cond
       ((eq? r 'goto-exit)  (exit-section))
       (else                (after-xmenu)))))

  (define (after-xmenu)
    ;; M8i — wrong-kboard + unread-events + kbd-queue + other-kboard.
    (let ((r (rc-prologue-kboard-and-queues!)))
      (cond
       ((eq? r 'return-wrong-kboard)
        (let ((rec ((force %rc-record-current))))
          (values -2 (rc-state-used-mouse-menu-flag rec))))
       (else                         (non-reread-section)))))

  (define (non-reread-section)
    ;; M8j — wrong_kboard + non_reread loop (the blocking-read entry).
    (let ((r (rc-wrong-kboard-and-non-reread!)))
      (cond
       ((eq? r 'goto-exit)           (exit-section))
       ((eq? r 'return-wrong-kboard)
        (let ((rec ((force %rc-record-current))))
          (values -2 (rc-state-used-mouse-menu-flag rec))))
       (else                         (after-non-reread)))))

  (define (after-non-reread)
    ;; M8k — BUFFERP early-exit + special-event-map dispatch.
    (let ((r (rc-bufferp-and-special-event-map!)))
      (cond
       ((eq? r 'goto-exit)  (exit-section))
       ((eq? r 'goto-retry) (retry-section))
       (else                (after-bufp-special)))))

  (define (after-bufp-special)
    ;; M8l — FIXNUMP/translate + menu-bar synthesis + record + echo-wipe.
    (let ((r (rc-event-translate-and-record!)))
      (cond
       ((eq? r 'goto-exit) (exit-section))
       (else               (reread-for-input-method-section)))))

  (define (reread-for-input-method-section)
    ;; M8m — input-method dispatch + record-if-unread.
    (let ((r (rc-input-method-dispatch!)))
      (cond
       ((eq? r 'goto-retry) (retry-section))
       (else                (reread-first-section)))))

  (define (reread-first-section)
    ;; M8n — help-echo + this-command-keys + last_input_event + help-form.
    (let ((r (rc-help-echo-and-help-form!)))
      (cond
       ((eq? r 'goto-retry) (retry-section))
       (else                (exit-section)))))

  (define (exit-section)
    ;; --rc-exit: input_was_pending = input_pending; return state->c.
    (rc-exit!))

  (if (%nilp jump?)
      (retry-section)
      (non-reread-section)))

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
              (--rc-test-state-ref     ,%rc-test-state-ref)
              (--rc-test-state-set!    ,%rc-test-state-set!)
              (--rc-test-with-state    ,%rc-test-with-state)
              ;; M8c — prologue dispatch
              (--rc-prologue-drain-unread!
                                       ,rc-prologue-drain-unread!)
              (--rc-prologue-drain-unread
                                       ,rc-prologue-drain-unread!)
              ;; M8d — kbd-macro / switch-frame early-exit
              (--rc-prologue-macro-or-switch-frame!
                                       ,rc-prologue-macro-or-switch-frame!)
              (--rc-prologue-macro-or-switch-frame
                                       ,rc-prologue-macro-or-switch-frame!)
              ;; M8e — redisplay loop
              (--rc-redisplay-and-wait-block!
                                       ,rc-redisplay-and-wait-block!)
              (--rc-redisplay-and-wait-block
                                       ,rc-redisplay-and-wait-block!)
              (--rc-prologue-redisplay!
                                       ,rc-prologue-redisplay!)
              (--rc-prologue-redisplay
                                       ,rc-prologue-redisplay!)
              ;; M8f — echo-cancel + minibuf-menu-prompt
              (--rc-prologue-echo-and-menu!
                                       ,rc-prologue-echo-and-menu!)
              (--rc-prologue-echo-and-menu
                                       ,rc-prologue-echo-and-menu!)
              ;; M8g — idle-timer + immediate-echo + auto-save
              (--rc-prologue-idle-echo-autosave!
                                       ,rc-prologue-idle-echo-autosave!)
              (--rc-prologue-idle-echo-autosave
                                       ,rc-prologue-idle-echo-autosave!)
              (--rc-maybe-auto-save-by-keystroke!
                                       ,rc-maybe-auto-save-by-keystroke!)
              (--rc-maybe-auto-save-by-keystroke
                                       ,rc-maybe-auto-save-by-keystroke!)
              (--rc-sit-for-and-maybe-echo!
                                       ,rc-sit-for-and-maybe-echo!)
              (--rc-sit-for-and-maybe-echo
                                       ,rc-sit-for-and-maybe-echo!)
              (--rc-should-immediate-echo-p
                                       ,rc-should-immediate-echo-p)
              ;; M8h — X-menu + auto-save-by-idle-timeout + GC
              (--rc-prologue-xmenu-and-idle-gc!
                                       ,rc-prologue-xmenu-and-idle-gc!)
              (--rc-prologue-xmenu-and-idle-gc
                                       ,rc-prologue-xmenu-and-idle-gc!)
              (--rc-auto-save-by-timeout-and-gc!
                                       ,rc-auto-save-by-timeout-and-gc!)
              (--rc-auto-save-by-timeout-and-gc
                                       ,rc-auto-save-by-timeout-and-gc!)
              ;; M8i — wrong-kboard + unread-events + kbd-queue + other-kboard
              (--rc-prologue-kboard-and-queues!
                                       ,rc-prologue-kboard-and-queues!)
              (--rc-prologue-kboard-and-queues
                                       ,rc-prologue-kboard-and-queues!)
              ;; M8j — wrong_kboard + non_reread loop
              (--rc-maybe-redisplay-when-no-input!
                                       ,rc-maybe-redisplay-when-no-input!)
              (--rc-maybe-redisplay-when-no-input
                                       ,rc-maybe-redisplay-when-no-input!)
              (--rc-read-and-install-event!
                                       ,rc-read-and-install-event!)
              (--rc-read-and-install-event
                                       ,rc-read-and-install-event!)
              (--rc-test-install-read-event
                                       ,%rc-test-install-read-event)
              (--rc-wrong-kboard-and-non-reread!
                                       ,rc-wrong-kboard-and-non-reread!)
              (--rc-wrong-kboard-and-non-reread
                                       ,rc-wrong-kboard-and-non-reread!)
              ;; M8k — BUFFERP + special-event-map dispatch
              (--rc-bufferp-and-special-event-map!
                                       ,rc-bufferp-and-special-event-map!)
              (--rc-bufferp-and-special-event-map
                                       ,rc-bufferp-and-special-event-map!)
              ;; M8l — translate + menu-bar + record + echo-wipe
              (--rc-event-translate-and-record!
                                       ,rc-event-translate-and-record!)
              (--rc-event-translate-and-record
                                       ,rc-event-translate-and-record!)
              (--rc-maybe-synthesize-menu-bar-event!
                                       ,rc-maybe-synthesize-menu-bar-event!)
              (--rc-maybe-synthesize-menu-bar-event
                                       ,rc-maybe-synthesize-menu-bar-event!)
              ;; M8m — input-method dispatch + record-if-unread
              (--rc-input-method-dispatch!
                                       ,rc-input-method-dispatch!)
              (--rc-input-method-dispatch
                                       ,rc-input-method-dispatch!)
              ;; M8n — help-echo + this-command-keys + help-form
              (--rc-add-command-keys-and-echo!
                                       ,rc-add-command-keys-and-echo!)
              (--rc-add-command-keys-and-echo
                                       ,rc-add-command-keys-and-echo!)
              (--rc-help-echo-and-help-form!
                                       ,rc-help-echo-and-help-form!)
              (--rc-help-echo-and-help-form
                                       ,rc-help-echo-and-help-form!)
              ;; M8final — exit tail + hoisted dispatcher
              (--rc-exit!              ,rc-exit!)
              (--rc-exit               ,rc-exit!)
              (--read-char-main        ,read-char-main)
              ;; Hoisted from C DEFUN: artificial switch-frame on focus-in.
              (internal-handle-focus-in
                                       ,internal-handle-focus-in))))
