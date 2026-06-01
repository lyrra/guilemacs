(define-module (emacs read-key-sequence)
  #:use-module (emacs-elisp runtime)
  #:use-module (srfi srfi-9)            ; define-record-type
  #:declarative? #t
  #:export (read-key-sequence-vs
            read-key-sequence-vs-string
            read-key-sequence-vs-vector
            discard-input
            set-input-mode
            current-input-mode
            posn-at-point
            input-pending-p
            ;; M6g — state-machine record types and helpers.
            ;; Note: srfi-9 auto-generates the field accessors / setters
            ;; as syntax-transformers in this Guile build, so they are
            ;; not first-class callable from elisp.  Scheme code in this
            ;; module uses them fine.  Future state-machine slices
            ;; should add explicit wrapper procedures (or expose via
            ;; `--rks-state-...' DEFUNs) for any field that needs to be
            ;; reachable from elisp tests.
            make-keyremap keyremap?
            keyremap-empty-p
            keyremap-reset!
            keyremap-rebase!
            make-rks-state rks-state?
            rks-setup-prompt!
            rks-setup-initial-keys-state!
            rks-setup-initial-state-c!
            rks-setup-replay-entire-sequence!
            rks-setup-replay-entire-sequence-c!
            rks-setup-replay-sequence!
            rks-setup-replay-sequence-c!
            rks-done-compute-remapped!
            rks-done-install-shift-translated!
            rks-done-install-unread-switch-frame!
            rks-done-downcase-undo!
            rks-done-fabricated-events!
            rks-first-unbound-short-circuit!
            rks-try-shift-translation-simple!
            rks-try-help-char!
            rks-try-shift-translation-fn-key!
            rks-walk-translation-maps!
            rks-iter-setup-capture!
            rks-iter-replay-restore!
            rks-iter-pre-read-cascade!
            rks-iter-install-binding!
            rks-follow-key-and-update-first-unbound!
            rks-iter-mouse-click-prefix!
            rks-iter-unbound-event-reduction!
            rks-iter-maybe-disable-text-conversion!
            init-read-key-sequence-registrations))

;;; M6a — read_key_sequence outer wrapper, ported from C
;;; read_key_sequence_vs (src/keyboard.c).
;;;
;;; This is the housekeeping shell around the read_key_sequence
;;; state machine: arg validation, specbind of two input-method vars,
;;; per-key-sequence counter reset, hourglass cancel, raw-keybuf-count
;;; reset, then the C state-machine call (via --read-key-sequence-and-vector),
;;; then quit handling and return-value packaging.
;;;
;;; The state-machine itself (~1000 lines in C) stays C-side for now.
;;; M6b–M6f will move portions of it (function-key-map, input-decode-map,
;;; key-translation-map, shift-translation, delayed switch-frame) to
;;; Scheme as separate slices.
;;;
;;; See docs/keyboard.org §M6a.

(define (%c name) (symbol-function name))

(define (%nilp x)
  ;; Recognize all three nil-equivalents that show up in Guile-elisp.
  (or (null? x) (not x)))

;;;;
;;;; M6g — state-machine data infrastructure.
;;;;
;;;; Two record types that mirror the C-side state of read_key_sequence:
;;;;
;;;;   `keyremap'   ←→  C struct keyremap   (src/keyboard.c:10202)
;;;;   `rks-state'  ←→  read_key_sequence locals (src/keyboard.c:10424–10500)
;;;;
;;;; These are the *substrate* for future M6h–M6j slices that will
;;;; move pieces of the state machine into Scheme.  They are NOT yet
;;;; wired into production code — the C state machine continues to
;;;; run during read-key-sequence-vs.  See docs/keyboard.org §M6g.

;;; The keyremap record models the partial application of one
;;; translation map (function-key-map, key-translation-map, or
;;; input-decode-map).  Semantics:
;;;
;;;   parent   — the original map specified for this slot.
;;;   map      — a submap reached by looking up, in PARENT, the
;;;              events from START to END.  Reset to PARENT after a
;;;              successful translation.
;;;   start    — position in keybuf where this map began scanning.
;;;   end      — exclusive end of the scan.  start == end means no
;;;              active scan.  Both indices CAN be > t (the
;;;              sequence length) when scanning is held off after a
;;;              just-resolved translation, to avoid re-scanning.

(define-record-type <keyremap>
  (%make-keyremap parent map start end)
  keyremap?
  (parent keyremap-parent set-keyremap-parent!)
  (map    keyremap-map    set-keyremap-map!)
  (start  keyremap-start  set-keyremap-start!)
  (end    keyremap-end    set-keyremap-end!))

(define (make-keyremap parent-map)
  "Create a fresh keyremap with PARENT-MAP as both parent and map and
both indices set to zero."
  (%make-keyremap parent-map parent-map 0 0))

(define (keyremap-empty-p kr)
  "True iff the keyremap has no scan in progress (start == end).
The corresponding C check is `kr.start == kr.end'."
  (= (keyremap-start kr) (keyremap-end kr)))

(define (keyremap-reset! kr)
  "Reset KR to its initial state: map ← parent, start = end = 0.
Used after a translation map fires and the recognized prefix has
been consumed."
  (set-keyremap-map!   kr (keyremap-parent kr))
  (set-keyremap-start! kr 0)
  (set-keyremap-end!   kr 0))

(define (keyremap-rebase! kr new-parent)
  "Repoint KR to a new PARENT map (also setting map) and zero the
scan indices.  Used at the top of `replay_entire_sequence' to
reinitialize from current-kboard / Vkey_translation_map."
  (set-keyremap-parent! kr new-parent)
  (set-keyremap-map!    kr new-parent)
  (set-keyremap-start!  kr 0)
  (set-keyremap-end!    kr 0))

;;; The rks-state record bundles every local variable of
;;; read_key_sequence that flows through the state machine.  Slots
;;; mirror the C declarations (src/keyboard.c:10424-10500) one-to-one.
;;;
;;; `keybuf' is a Scheme vector of length READ-KEY-ELTS (= 30 in C);
;;; treat it as the analogue of the Lisp_Object keybuf[READ_KEY_ELTS]
;;; array.  Per-position mutation via `vector-set!'.

(define READ-KEY-ELTS 30)               ; matches C enum at keyboard.c:1503

(define-record-type <rks-state>
  (%make-rks-state key-count mock-input keybuf
                   keys-start echo-start
                   current-binding first-unbound
                   fkey keytran indec
                   shift-translated
                   delayed-switch-frame
                   original-uppercase original-uppercase-position
                   fake-prefixed-keys)
  rks-state?
  ;; `key-count' = the C local `t' (terse name avoided in Scheme).
  (key-count            rks-state-key-count            set-rks-state-key-count!)
  (mock-input           rks-state-mock-input           set-rks-state-mock-input!)
  (keybuf               rks-state-keybuf)              ; vector — mutate in place
  (keys-start           rks-state-keys-start           set-rks-state-keys-start!)
  (echo-start           rks-state-echo-start           set-rks-state-echo-start!)
  (current-binding      rks-state-current-binding      set-rks-state-current-binding!)
  (first-unbound        rks-state-first-unbound        set-rks-state-first-unbound!)
  (fkey                 rks-state-fkey)                ; <keyremap>
  (keytran              rks-state-keytran)             ; <keyremap>
  (indec                rks-state-indec)               ; <keyremap>
  (shift-translated     rks-state-shift-translated
                        set-rks-state-shift-translated!)
  (delayed-switch-frame rks-state-delayed-switch-frame
                        set-rks-state-delayed-switch-frame!)
  (original-uppercase   rks-state-original-uppercase
                        set-rks-state-original-uppercase!)
  (original-uppercase-position
                        rks-state-original-uppercase-position
                        set-rks-state-original-uppercase-position!)
  (fake-prefixed-keys   rks-state-fake-prefixed-keys
                        set-rks-state-fake-prefixed-keys!))

(define (make-rks-state)
  "Create a fresh rks-state with the same defaults as read_key_sequence
on entry.  The three keyremap slots start with their respective
parent maps set to nil; callers should `keyremap-rebase!' them once
current-kboard has been queried (this matches the C
`replay_entire_sequence:' setup, not the local-decl defaults)."
  (%make-rks-state
   0                                    ; t
   0                                    ; mock-input
   (make-vector READ-KEY-ELTS #nil)     ; keybuf
   0                                    ; keys-start
   0                                    ; echo-start
   #nil                                 ; current-binding
   (+ READ-KEY-ELTS 1)                  ; first-unbound  (matches C init)
   (make-keyremap #nil)                 ; fkey
   (make-keyremap #nil)                 ; keytran
   (make-keyremap #nil)                 ; indec
   #nil                                 ; shift-translated
   #nil                                 ; delayed-switch-frame
   #nil                                 ; original-uppercase
   -1                                   ; original-uppercase-position
   #nil))                               ; fake-prefixed-keys

;; `--read-key-sequence-and-vector' is looked up per call (see body) so
;; tests can stub it.  The other helpers are stable across calls.
(define %make-event-array-from-vector
  (delay (%c '--make-event-array-from-vector)))
(define %maybe-quit                (delay (%c '--maybe-quit)))
(define %set-this-command-key-count
  (delay (%c '--set-this-command-key-count)))
(define %set-this-single-command-key-start
  (delay (%c '--set-this-single-command-key-start)))
(define %display-hourglass-p       (delay (%c '--display-hourglass-p)))
(define %cancel-hourglass          (delay (%c '--cancel-hourglass)))
(define %set-raw-keybuf-count      (delay (%c '--set-raw-keybuf-count)))

(define (read-key-sequence-vs prompt continue-echo dont-downcase-last
                              can-return-switch-frame cmd-loop
                              allow-string disable-text-conversion)
  "Housekeeping wrapper for the C read_key_sequence state machine.
Ports src/keyboard.c read_key_sequence_vs.  Sequence of side-effects:

  1. CHECK_STRING on PROMPT (--read-key-sequence-and-vector does this).
  2. maybe-quit (so a pending quit-flag fires before we block on input).
  3. Specbind input-method-exit-on-first-char and
     input-method-use-echo-area to t when CMD-LOOP is nil, else nil.
  4. If CONTINUE-ECHO is nil, reset this-command-key-count and
     this-single-command-key-start to 0.
  5. Cancel any in-flight hourglass (window-system only).
  6. Reset raw-keybuf-count to 0.
  7. Call --read-key-sequence-and-vector with the remaining args; on
     a -1 return (user quit during read), set quit-flag and call
     maybe-quit (throws).
  8. Package the resulting vector as either a string (event-array
     form, when ALLOW-STRING is true) or the vector itself.

Mirrors src/keyboard.c read_key_sequence_vs (lines 11402-11454)."
  ((force %maybe-quit))
  (let* ((cmd-loop-nil? (%nilp cmd-loop))
         (specbind-value (if cmd-loop-nil? #t #nil))
         (saved-exit (symbol-value 'input-method-exit-on-first-char))
         (saved-echo (symbol-value 'input-method-use-echo-area)))
    (dynamic-wind
      (lambda ()
        (set-symbol-value! 'input-method-exit-on-first-char specbind-value)
        (set-symbol-value! 'input-method-use-echo-area      specbind-value))
      (lambda ()
        (when (%nilp continue-echo)
          ((force %set-this-command-key-count)        0)
          ((force %set-this-single-command-key-start) 0))
        (when (not (%nilp ((force %display-hourglass-p))))
          ((force %cancel-hourglass)))
        ((force %set-raw-keybuf-count) 0)
        (let ((result
               ;; Direct elisp-symbol-function lookup (no `delay' cache)
               ;; so tests can stub --read-key-sequence-and-vector via
               ;; `fset' or advice without us pinning the original.
               ((%c '--read-key-sequence-and-vector)
                prompt dont-downcase-last
                can-return-switch-frame
                disable-text-conversion)))
          (cond
           ((and (number? result) (= result -1))
            ;; Quit during read — set the flag and re-enter maybe-quit
            ;; so it throws normally.  No value returned from this path.
            (set-symbol-value! 'quit-flag #t)
            ((force %maybe-quit))
            ;; Unreachable; maybe-quit throws.
            result)
           (else
            ;; result is a vector of the read keys.
            (if allow-string
                ;; The shared subr takes (vec start count).
                ((force %make-event-array-from-vector)
                 result 0 (vector-length result))
                result)))))
      (lambda ()
        (set-symbol-value! 'input-method-exit-on-first-char saved-exit)
        (set-symbol-value! 'input-method-use-echo-area      saved-echo)))))

;; Specialized wrappers matching the two C DEFUN signatures.

(define (read-key-sequence-vs-string prompt continue-echo dont-downcase-last
                                     can-return-switch-frame cmd-loop
                                     disable-text-conversion)
  (read-key-sequence-vs prompt continue-echo dont-downcase-last
                        can-return-switch-frame cmd-loop
                        #t disable-text-conversion))

(define (read-key-sequence-vs-vector prompt continue-echo dont-downcase-last
                                     can-return-switch-frame cmd-loop
                                     disable-text-conversion)
  (read-key-sequence-vs prompt continue-echo dont-downcase-last
                        can-return-switch-frame cmd-loop
                        #nil disable-text-conversion))

;;;;
;;;; M6b — discard-input (ported from C Fdiscard_input).
;;;;

(define %end-kbd-macro            (delay (%c '--end-kbd-macro)))
(define %discard-tty-input        (delay (%c '--discard-tty-input)))
(define %reset-kbd-ring-and-pending
  (delay (%c '--reset-kbd-ring-and-pending)))
(define %kboard-defining-kbd-macro (delay (%c 'kboard-defining-kbd-macro)))
(define %current-kboard           (delay (%c 'current-kboard)))

(define (discard-input)
  "Discard the contents of the terminal input buffer.  Also end any
kbd macro being defined.  Mirrors src/keyboard.c Fdiscard_input."
  (let ((kb ((force %current-kboard))))
    (when (not (%nilp ((force %kboard-defining-kbd-macro) kb)))
      ;; Discard the last command from the macro, then end it.
      ((%c 'cancel-kbd-macro-events))
      ((force %end-kbd-macro))))

  (set-symbol-value! 'unread-command-events #nil)
  ((force %discard-tty-input))
  ((force %reset-kbd-ring-and-pending))
  #nil)

;;;;
;;;; M6c — set-input-mode / current-input-mode.
;;;;

(define %interrupt-input-p           (delay (%c '--interrupt-input-p)))
(define %selected-frame-tty-p        (delay (%c '--selected-frame-tty-p)))
(define %selected-frame-tty-flow-control-p
  (delay (%c '--selected-frame-tty-flow-control-p)))
(define %selected-frame-tty-meta-key
  (delay (%c '--selected-frame-tty-meta-key)))
(define %quit-char                   (delay (%c '--quit-char)))

(define (set-input-mode interrupt flow meta quit)
  "Set the keyboard-input mode.  Wraps the four underlying elisp
DEFUNs (set-input-interrupt-mode, set-output-flow-control,
set-input-meta-mode, set-quit-char).  Mirrors src/keyboard.c
Fset_input_mode."
  ((%c 'set-input-interrupt-mode) interrupt)
  ((%c 'set-output-flow-control) flow #nil)
  ((%c 'set-input-meta-mode) meta #nil)
  (when (not (%nilp quit))
    ((%c 'set-quit-char) quit))
  #nil)

(define (current-input-mode)
  "Return (INTERRUPT FLOW META QUIT) describing the current keyboard
input mode.  Mirrors src/keyboard.c Fcurrent_input_mode."
  (let* ((interrupt (if (not (%nilp ((force %interrupt-input-p)))) #t #nil))
         (tty?      (not (%nilp ((force %selected-frame-tty-p)))))
         (flow      (if tty?
                        (if (not (%nilp ((force %selected-frame-tty-flow-control-p))))
                            #t #nil)
                        #nil))
         (meta      (if tty?
                        (let ((mk ((force %selected-frame-tty-meta-key))))
                          (cond
                           ((= mk 2) 0)
                           ((= mk 1) #t)
                           ((= mk 3) 'encoded)
                           (else     #nil)))
                        #t))
         (quit      ((force %quit-char))))
    (list interrupt flow meta quit)))

;;;;
;;;; M6d — posn-at-point.
;;;;

(define (posn-at-point pos window)
  "Return position information for buffer position POS in WINDOW.
POS defaults to point in WINDOW; WINDOW defaults to the selected
window.  Returns nil when POS is not visible in WINDOW.  Mirrors
src/keyboard.c Fposn_at_point."
  (let* ((win (if (%nilp window)
                  ((%c 'selected-window))
                  window))
         (tem ((%c 'pos-visible-in-window-p) pos win #t)))
    (cond
     ((%nilp tem) #nil)
     (else
      (let* ((x ((%c 'car) tem))
             (y ((%c 'car) ((%c 'cdr) tem)))
             (aux-info ((%c 'cdr) ((%c 'cdr) tem)))
             (y-coord y))
        (cond
         ;; Point invisible due to hscrolling? X = -1 means newline
         ;; in a R2L line overflowed into the left fringe — still
         ;; considered visible.  X < -1 means actually invisible.
         ((< x -1) #nil)
         (else
          (let ((y* (if (and (not (%nilp aux-info)) (< y-coord 0))
                        (+ y-coord ((%c 'car) aux-info))
                        y)))
            ((%c 'posn-at-x-y) x y* win #nil)))))))))

;;;;
;;;; M6e — input-pending-p.
;;;;
;;;; READABLE_EVENTS flags (see src/keyboard.c lines 381-383):
;;;;   1 = DO_TIMERS_NOW
;;;;   2 = FILTER_EVENTS
;;;;   4 = IGNORE_SQUEEZABLES

(define %requeued-events-pending-p
  (delay (%c '--requeued-events-pending-p)))
(define %process-special-events
  (delay (%c '--process-special-events)))
(define %get-input-pending
  (delay (%c '--get-input-pending)))

(define (input-pending-p check-timers)
  "Return t if command input is currently available with no wait.
If CHECK-TIMERS is non-nil, ready timers fire first.  Mirrors
src/keyboard.c Finput_pending_p."
  (cond
   ((not (%nilp ((force %requeued-events-pending-p)))) #t)
   (else
    ;; Process non-user-visible events (Bug#10195) before checking.
    ((force %process-special-events))
    (let ((flags (+ (if (%nilp check-timers) 0 1) 2)))
      (if (not (%nilp ((force %get-input-pending) flags))) #t #nil)))))

;;;;
;;;; M6h — setup-phase procedures (called BEFORE the C state-machine
;;;; while-loop).  Not yet wired into runtime — the C function still
;;;; performs all of this work inline.  These procedures are tested
;;;; in isolation; future slices (M6i+) will wire them in.
;;;;

(define %echo-length           (delay (%c '--echo-length)))
(define %echo-truncate         (delay (%c '--echo-truncate)))
(define %echo-dash             (delay (%c '--echo-dash)))
(define %echo-keystrokes-p     (delay (%c '--echo-keystrokes-p)))
(define %cursor-in-echo-area-p (delay (%c '--cursor-in-echo-area-p)))
(define %set-current-kboard-immediate-echo
  (delay (%c '--set-current-kboard-immediate-echo)))
(define %echo-now-2            (delay (%c '--echo-now)))
(define %this-command-key-count
  (delay (%c '--this-command-key-count)))
(define %set-this-single-command-key-start-2
  (delay (%c '--set-this-single-command-key-start)))
(define %set-kboard-echo-prompt
  (delay (%c 'set-kboard-echo-prompt)))

(define (rks-setup-prompt! prompt)
  "Initial prompt + echo setup for read_key_sequence.  Runs only when
interactive (i.e. `noninteractive' is nil).  Mirrors the C body of
read_key_sequence lines 10504-10526:

  if PROMPT is non-nil → install it on the current kboard's
    echo-prompt, force-redisplay via echo_now (with immediate-echo
    juggling), then re-clear immediate-echo when keystroke echo is
    disabled.
  else if cursor is in echo area AND keystrokes are echoed →
    append a dash to the echo buffer so the user sees a hanging
    prefix prompt."
  (when (%nilp (symbol-value 'noninteractive))
    (cond
     ((not (%nilp prompt))
      (let ((kb ((force %current-kboard))))
        ((force %set-kboard-echo-prompt) kb prompt)
        ((force %set-current-kboard-immediate-echo) #nil)
        ((force %echo-now-2))
        (when (%nilp ((force %echo-keystrokes-p)))
          ((force %set-current-kboard-immediate-echo) #nil))))
     ((and (not (%nilp ((force %cursor-in-echo-area-p))))
           (not (%nilp ((force %echo-keystrokes-p)))))
      ((force %echo-dash))))))

(define %set-rks-echo-start (delay (%c '--set-rks-echo-start)))
(define %set-rks-keys-start (delay (%c '--set-rks-keys-start)))

(define (rks-setup-initial-state-c!)
  "Runtime initial-state capture for read_key_sequence.  Writes the
file-static C globals rks_echo_start and rks_keys_start (the
promoted shadows of the former `echo_start' / `keys_start' locals)
and updates this-single-command-key-start.  Mirrors the C inline
block at lines 10578-10581 (pre-M6j).

Used at runtime via the cached-SCM dispatch in read_key_sequence.
For the rks-state record-writing variant used by tests, see
`rks-setup-initial-keys-state!'."
  (let ((kc ((force %this-command-key-count))))
    (when (%nilp (symbol-value 'noninteractive))
      ((force %set-rks-echo-start) ((force %echo-length))))
    ((force %set-rks-keys-start) kc)
    ((force %set-this-single-command-key-start-2) kc)))

(define (rks-setup-initial-keys-state! state)
  "Capture the initial echo length + this-command-key-count into the
rks-state record.  Mirrors src/keyboard.c lines 10528-10535:

  echo_start             = echo_length () [interactive only]
  keys_start             = this_command_key_count
  this_single_command_key_start = keys_start"
  (when (%nilp (symbol-value 'noninteractive))
    (set-rks-state-echo-start! state ((force %echo-length))))
  (let ((kc ((force %this-command-key-count))))
    (set-rks-state-keys-start! state kc)
    ((force %set-this-single-command-key-start-2) kc)))

;;;;
;;;; M6k — replay-phase setup procedures.
;;;;
;;;; Parallel Scheme implementations of the two label-bodies inside
;;;; read_key_sequence: `replay_entire_sequence' (resets the three
;;;; keyremap maps from current-kboard) and `replay_sequence' (caches
;;;; starting buffer, first_unbound, builds current-binding from
;;;; active_maps).  These operate on an rks-state record.  NOT yet
;;;; wired into the C state machine; the wire-in waits until the
;;;; keyremap locals are promoted to file-static (a bigger refactor).

(define %kboard-input-decode-map
  (delay (%c 'kboard-input-decode-map)))
(define %kboard-local-function-key-map
  (delay (%c 'kboard-local-function-key-map)))
(define %active-maps           (delay (%c '--active-maps)))

(define %rks-init-keyremaps    (delay (%c '--rks-init-keyremaps)))

(define (rks-setup-replay-entire-sequence! state)
  "Reset the three keyremaps in STATE from current-kboard's translation
maps and the global `key-translation-map'.  Mirrors the C block at
the `replay_entire_sequence:' label (src/keyboard.c lines
10635-10640)."
  (let ((kb ((force %current-kboard))))
    (keyremap-rebase! (rks-state-indec state)
                      ((force %kboard-input-decode-map) kb))
    (keyremap-rebase! (rks-state-fkey state)
                      ((force %kboard-local-function-key-map) kb))
    (keyremap-rebase! (rks-state-keytran state)
                      (symbol-value 'key-translation-map))))

(define (rks-setup-replay-entire-sequence-c!)
  "Runtime variant of `rks-setup-replay-entire-sequence!': writes the
file-static C-side keyremap shadows (rks_indec, rks_fkey,
rks_keytran) via `--rks-init-keyremaps'.  Called from
read_key_sequence's `replay_entire_sequence:' label via the
cached-SCM dispatch."
  (let ((kb ((force %current-kboard))))
    ((force %rks-init-keyremaps)
     ((force %kboard-input-decode-map) kb)
     ((force %kboard-local-function-key-map) kb)
     (symbol-value 'key-translation-map))))

(define READ-KEY-ELTS-PLUS-1 (+ READ-KEY-ELTS 1))

(define %rks-replay-sequence-init-rest
  (delay (%c '--rks-replay-sequence-init-rest)))

(define (rks-setup-replay-sequence-c! keybuf0 keybuf1)
  "Runtime variant for the `replay_sequence:' label.  Called by C
read_key_sequence with KEYBUF0 = (mock_input > 0 ? keybuf[0] : nil)
and KEYBUF1 = (mock_input > 1 ? keybuf[1] : nil).  Computes
current_binding via `--active-maps' and writes the five promoted
file-statics (rks_starting_buffer, rks_first_unbound,
rks_current_binding, rks_t, last_nonmenu_event) via
`--rks-replay-sequence-init-rest'."
  ((force %rks-replay-sequence-init-rest)
   ((force %active-maps) keybuf0 keybuf1)))

(define (rks-setup-replay-sequence! state)
  "Capture per-replay state: zeroes key-count, sets first-unbound to
its sentinel value, computes the initial current-binding from
keybuf[0]/keybuf[1] (where mock-input permits) via the C
`--active-maps' helper.  Mirrors src/keyboard.c lines 10649-10661
(the `replay_sequence:' label body)."
  (let* ((mock-input (rks-state-mock-input state))
         (keybuf    (rks-state-keybuf state))
         (first-event  (if (> mock-input 0) (vector-ref keybuf 0) #nil))
         (second-event (if (> mock-input 1) (vector-ref keybuf 1) #nil)))
    (set-rks-state-first-unbound! state READ-KEY-ELTS-PLUS-1)
    (set-rks-state-current-binding! state
                                    ((force %active-maps) first-event second-event))
    (set-rks-state-key-count! state 0)))

;;;;
;;;; M6n — done:-block remapped computation.
;;;;

(define %read-key-sequence-cmd
  (delay (%c '--read-key-sequence-cmd)))
(define %set-read-key-sequence-remapped
  (delay (%c '--set-read-key-sequence-remapped)))

(define %rks-shift-translated-p
  (delay (%c '--rks-shift-translated-p)))
(define %rks-delayed-switch-frame
  (delay (%c '--rks-delayed-switch-frame)))
(define %set-unread-switch-frame
  (delay (%c '--set-unread-switch-frame)))

(define %rks-t                       (delay (%c '--rks-t)))
(define %rks-current-binding         (delay (%c '--rks-current-binding)))
(define %rks-original-uppercase      (delay (%c '--rks-original-uppercase)))
(define %rks-original-uppercase-position
  (delay (%c '--rks-original-uppercase-position)))
(define %set-rks-shift-translated
  (delay (%c '--set-rks-shift-translated)))
(define %rks-keybuf-set              (delay (%c '--rks-keybuf-set)))

(define %rks-mock-input  (delay (%c '--rks-mock-input)))
(define %set-rks-t       (delay (%c '--set-rks-t)))
(define %echo-update     (delay (%c '--echo-update)))
(define %add-command-key (delay (%c '--add-command-key)))
(define %rks-keybuf-ref  (delay (%c '--rks-keybuf-ref)))

(define %rks-first-unbound       (delay (%c '--rks-first-unbound)))
(define %rks-keytran-start       (delay (%c '--rks-keytran-start)))
(define %set-rks-mock-input      (delay (%c '--set-rks-mock-input)))
(define %rks-keybuf-shift-down   (delay (%c '--rks-keybuf-shift-down)))
(define %rks-keyremaps-shrink-by (delay (%c '--rks-keyremaps-shrink-by)))

(define %rks-iter-setup-capture
  (delay (%c '--rks-iter-setup-capture)))
(define %rks-iter-replay-restore
  (delay (%c '--rks-iter-replay-restore)))

(define (rks-iter-setup-capture!)
  "Per-iteration setup at the top of the while-loop body, after the
M6t first_unbound short-circuit.  Errors if rks_t exceeds
READ_KEY_ELTS; otherwise captures echo-length and
this-command-key-count into the file-static rks_echo_local_start
/ rks_keys_local_start so the replay_key restore below can revert
to them.  See docs/keyboard.org §M6y."
  ((force %rks-iter-setup-capture)))

(define %rks-iter-maybe-disable-text-conversion
  (delay (%c '--rks-iter-maybe-disable-text-conversion)))

(define (rks-iter-maybe-disable-text-conversion!)
  "On HAVE_TEXT_CONVERSION builds: after the first key is read and
no mouse menu was used, scan the first up-to-10 keybuf elements
for a NUMBERP or function-key SYMBOL.  If found, disable text
conversion + install a resume-on-unwind, then mark the per-call
flag so this only happens once.  On non-HAVE_TEXT_CONVERSION
builds, no-op.  See docs/keyboard.org §M6ae."
  ((force %rks-iter-maybe-disable-text-conversion)))

(define %rks-reduce-mouse-event-loop
  (delay (%c '--rks-reduce-mouse-event-loop)))

(define (rks-iter-unbound-event-reduction!)
  "M6 Step E4: unbound-event modifier-reduction cascade, partially
decomposed.  The first_unbound = min(t, first_unbound) update moved
to Scheme; the modifier-reduction while-loop + keyremap-reset logic
stays in C (--rks-reduce-mouse-event-loop).  Returns `replay-key',
`replay-sequence', or `fall-through'."
  (let ((t ((force %rks-t)))
        (fu ((force %rks-first-unbound))))
    (when (< t fu)
      ((force %set-rks-first-unbound) t)))
  ((force %rks-reduce-mouse-event-loop)))

(define %rks-mouse-click-prefix-body
  (delay (%c '--rks-mouse-click-prefix-body)))

(define (rks-iter-mouse-click-prefix!)
  "M6 Step E6: mouse-click prefix expansion, partially decomposed.
The EVENT_HAS_PARAMETERS gate check moved to Scheme; the body
(buffer-switch, mode-line/scroll-bar/tool-bar prefix insertion,
keybuf writes) stays in C (--rks-mouse-click-prefix-body).
Returns `replay-sequence', `replay-key', or `fall-through'."
  (let ((key ((force %rks-key))))
    (if (and (pair? key) (symbol? (car key)))
        ((force %rks-mouse-click-prefix-body))
        'fall-through)))

(define %rks-follow-key  (delay (%c '--rks-follow-key)))
(define %rks-key          (delay (%c '--rks-key)))
(define %rks-first-unbound
  (delay (%c '--rks-first-unbound)))
(define %set-rks-new-binding
  (delay (%c '--set-rks-new-binding)))
(define %set-rks-first-unbound
  (delay (%c '--set-rks-first-unbound)))

(define (rks-follow-key-and-update-first-unbound!)
  "M6 Step E3: follow_key + first_unbound update, decomposed from C.
Only follow_key stays in C (--rks-follow-key); the nil check and
first_unbound update are Scheme logic.  Returns t if key was bound
(caller skips unbound-event reduction), nil otherwise."
  (let* ((cb  ((force %rks-current-binding)))
         (key ((force %rks-key)))
         (new-binding ((force %rks-follow-key) cb key)))
    (if (%nilp new-binding)
        #nil
        (begin
          ((force %set-rks-new-binding) new-binding)
          (let ((candidate (1+ ((force %rks-t)))))
            (when (> candidate ((force %rks-first-unbound)))
              ((force %set-rks-first-unbound) candidate)))
          #t))))

(define %rks-iter-install-binding
  (delay (%c '--rks-iter-install-binding)))

(define (rks-iter-install-binding! new-binding)
  "Install NEW-BINDING as the resolved rks_current_binding for this
iteration.  Advances rks_t with the new keybuf element, updates
last_nonmenu_event unless the key came from a mouse menu, and
clamps this_single_command_key_start to >= 0 (Bug#20223).  See
docs/keyboard.org §M6aa."
  ((force %rks-iter-install-binding) new-binding))

(define %rks-iter-pre-read-cascade
  (delay (%c '--rks-iter-pre-read-cascade)))

(define (rks-iter-pre-read-cascade!)
  "Dispatch the per-iteration key-source cascade.  Returns one of:

  `mock'      — branch 1 fired (rks_t < rks_mock_input).  rks_key
                + rks_used_mouse_menu set from keybuf;
                rks-add-command-key + echo refresh have run.
                Caller continues to the per-key dispatch.
  `done'      — branch 2 fired (executing kbd-macro at end with
                no requeued events).  rks_t has been set to 0.
                Caller goto done.
  `read-char' — neither branch applied.  Caller must do the
                inline read_char (M8 territory).

See docs/keyboard.org §M6z."
  ((force %rks-iter-pre-read-cascade)))

(define (rks-iter-replay-restore!)
  "replay_key:-target restore.  On every iteration (and after the
text-conversion-disable jump), restore the echo buffer and
this-command-key-count to the values captured by
`rks-iter-setup-capture!', then snapshot rks_t as
rks_last_real_key_start so the per-key dispatch can backtrack
into the buffer if a mouse-click expands into multiple keybuf
elements.  See docs/keyboard.org §M6y."
  ((force %rks-iter-replay-restore)))

(define %rks-walk-indec          (delay (%c '--rks-walk-indec)))
(define %rks-fkey-shortcut-or-walk
  (delay (%c '--rks-fkey-shortcut-or-walk)))
(define %rks-walk-keytran        (delay (%c '--rks-walk-keytran)))

(define %rks-state-current
  (delay (%c '--rks-state-current)))
(define %rks-record-get-int
  (delay (%c '--rks-record-get-int)))
(define %rks-record-set-int
  (delay (%c '--rks-record-set-int)))

;; M6h-1 keyremap getter/setter delays
(define %rks-fkey-start     (delay (%c '--rks-fkey-start)))
(define %rks-fkey-end       (delay (%c '--rks-fkey-end)))
(define %rks-keytran-start  (delay (%c '--rks-keytran-start)))
(define %rks-keytran-end    (delay (%c '--rks-keytran-end)))
(define %rks-indec-start    (delay (%c '--rks-indec-start)))
(define %rks-indec-end      (delay (%c '--rks-indec-end)))
(define %set-rks-fkey-start    (delay (%c '--set-rks-fkey-start)))
(define %set-rks-fkey-end      (delay (%c '--set-rks-fkey-end)))
(define %set-rks-keytran-start (delay (%c '--set-rks-keytran-start)))
(define %set-rks-keytran-end   (delay (%c '--set-rks-keytran-end)))
(define %set-rks-indec-start   (delay (%c '--set-rks-indec-start)))
(define %set-rks-indec-end     (delay (%c '--set-rks-indec-end)))
(define %set-rks-t          (delay (%c '--set-rks-t)))

;; RKS_SLOT_* values (must match C enum in src/keyboard.c)
(define RKS-SLOT-KEY-COUNT         0)
(define RKS-SLOT-MOCK-INPUT        1)
(define RKS-SLOT-KEYBUF            2)
(define RKS-SLOT-KEYS-START        3)
(define RKS-SLOT-ECHO-START        4)
(define RKS-SLOT-CURRENT-BINDING   5)
(define RKS-SLOT-FIRST-UNBOUND     6)
(define RKS-SLOT-FKEY              7)
(define RKS-SLOT-KEYTRAN           8)
(define RKS-SLOT-INDEC             9)
(define RKS-SLOT-SHIFT-TRANSLATED 10)

(define (rks-sync-record->file-statics keyremap-slot start end)
  "M6h-1: sync 4 scalar fields FROM record TO C file-statics before
a walk call.  KEYREMAP-SLOT is RKS-SLOT-FKEY/KEYTRAN/INDEC;
START and END are the km slot indices (KM_SLOT_START=2, KM_SLOT_END=3)."
  (let ((rec ((force %rks-state-current))))
    (when (not (%nilp rec))
      ((force %set-rks-t)
       ((force %rks-record-get-int) rec RKS-SLOT-KEY-COUNT))
      ((force %set-rks-mock-input)
       ((force %rks-record-get-int) rec RKS-SLOT-MOCK-INPUT))
      ;; Keyremap sync deferred to M6h-2.
      #nil)))

(define (rks-sync-file-statics->record)
  "M6h-1: sync mock_input FROM C file-statics TO record.  Always returns #nil."
  (let ((rec ((force %rks-state-current))))
    (when (not (%nilp rec))
      ((force %rks-record-set-int)
       rec RKS-SLOT-MOCK-INPUT ((force %rks-mock-input))))
    #nil))

(define (rks-walk-translation-maps! prompt)
  "M6 Step E5 + M6h-2: three-map translation walk.  The indec walk
loads/saves state from the <rks-state> record internally (M6h-2);
fkey and keytran walks still use M6h-1 Scheme-side sync until
M6h-4/M6h-6.  See docs/m6-plan.org §M6h."
  (let ((r1 ((force %rks-walk-indec) prompt)))  ;; M6h-2: C-side sync
    (or (not (%nilp r1))
        (let ((r2 (begin   ;; fkey walk (M6h-1 sync)
                    (rks-sync-record->file-statics RKS-SLOT-FKEY 2 3)
                    ((force %rks-fkey-shortcut-or-walk) prompt)
                    (rks-sync-file-statics->record))))
          (or (not (%nilp r2))
              ((force %rks-walk-keytran) prompt)
              #nil)))))

(define %rks-fn-key-shift-translate
  (delay (%c '--rks-fn-key-shift-translate)))
(define %rks-reset-fkey-and-keytran-scans
  (delay (%c '--rks-reset-fkey-and-keytran-scans)))

(define (rks-try-shift-translation-fn-key! key)
  "M6 Step E2: shifted-function-key shift-translation, decomposed
from C to Scheme.  Only the modifier arithmetic (strip-shift /
downcase-via-downcase-table) stays in C (--rks-fn-key-shift-translate);
the gate check, parse_modifiers call, and side effects are Scheme
logic.  Returns t (caller goto replay_sequence) or nil."
  (if (or (not (%nilp ((force %rks-current-binding))))
          (< ((force %rks-keytran-start)) ((force %rks-t))))
      #nil
      (let* ((breakdown ((%c 'parse-modifiers) key))
             (mods (if (pair? breakdown)
                       (cadr (cadr breakdown))
                       0))
             (translate? (symbol-value
                          'translate-upper-case-key-bindings))
             (new-key ((force %rks-fn-key-shift-translate)
                       key mods translate?)))
        (if (%nilp new-key)
            #nil
            (begin
              ((force %set-rks-original-uppercase) key)
              ((force %set-rks-original-uppercase-position)
               (- ((force %rks-t)) 1))
              ((force %rks-keybuf-set)
               (- ((force %rks-t)) 1)
               new-key)
              (when (> ((force %rks-t)) ((force %rks-mock-input)))
                ((force %set-rks-mock-input) ((force %rks-t))))
              ((force %rks-reset-fkey-and-keytran-scans))
              ((force %set-rks-shift-translated) #t)
              #t)))))

(define %rks-try-help-char (delay (%c '--rks-try-help-char)))

(define (rks-try-help-char! key)
  "If the iteration ended with current_binding nil and KEY is the
help-character (and at least one prior key has been read), install
`prefix-help-command' as the resolved command and return t (caller
should goto done).  Otherwise nil.  See docs/keyboard.org §M6v."
  ((force %rks-try-help-char) key))

(define %rks-shift-translate-key
  (delay (%c '--rks-shift-translate-key)))

(define %rks-current-binding     (delay (%c '--rks-current-binding)))
(define %rks-keytran-start       (delay (%c '--rks-keytran-start)))
(define %rks-t                   (delay (%c '--rks-t)))
(define %rks-mock-input          (delay (%c '--rks-mock-input)))
(define %rks-shift-translated-p  (delay (%c '--rks-shift-translated-p)))
(define %set-rks-shift-translated
  (delay (%c '--set-rks-shift-translated)))
(define %set-rks-mock-input      (delay (%c '--set-rks-mock-input)))
(define %set-rks-original-uppercase
  (delay (%c '--set-rks-original-uppercase)))
(define %set-rks-original-uppercase-position
  (delay (%c '--set-rks-original-uppercase-position)))
(define %rks-keybuf-set          (delay (%c '--rks-keybuf-set)))

(define (rks-try-shift-translation-simple! key)
  "M6 Step E1: shift-translation for KEY, decomposed from C to
Scheme.  Only the shift/downcase arithmetic stays in C
(--rks-shift-translate-key); everything else (gate check, keybuf
write, mock-input bump, shift-translated flag, original-uppercase
save) is Scheme logic calling thin C primitives.

Returns t (caller goto replay_sequence) or nil (fall through)."
  (if (or (not (%nilp ((force %rks-current-binding))))
          (< ((force %rks-keytran-start)) ((force %rks-t)))
          (not (integer? key))
          (not (symbol-value 'translate-upper-case-key-bindings)))
      #nil
      (let ((new-key ((force %rks-shift-translate-key) key)))
        (if (%nilp new-key)
            #nil
            (begin
              ((force %set-rks-original-uppercase) key)
              ((force %set-rks-original-uppercase-position)
               (- ((force %rks-t)) 1))
              ((force %rks-keybuf-set)
               (- ((force %rks-t)) 1)
               new-key)
              (when (> ((force %rks-t)) ((force %rks-mock-input)))
                ((force %set-rks-mock-input) ((force %rks-t))))
              ((force %set-rks-shift-translated) #t)
              #t)))))

(define (rks-first-unbound-short-circuit!)
  "If the prefix up to rks_first_unbound has no binding and no
translation left to do, shift it off keybuf and rebase the
keyremap scans.  Returns t iff the short-circuit fired (caller
should goto replay_sequence), nil otherwise.

Mirrors the C 17-line block at the top of the read_key_sequence
while-loop body (src/keyboard.c lines 11102-11119 pre-M6t)."
  (let* ((fu  ((force %rks-first-unbound)))
         (kts ((force %rks-keytran-start))))
    (cond
     ((< fu kts)
      (let ((shift (+ fu 1)))
        ;; Shift keybuf[shift..t-1] down to keybuf[0..t-shift-1].
        ((force %rks-keybuf-shift-down) shift)
        ;; mock_input = t - shift.
        ((force %set-rks-mock-input) (- ((force %rks-t)) shift))
        ;; For each keyremap: start -= shift, end = start, map = parent.
        ((force %rks-keyremaps-shrink-by) shift))
      #t)
     (else #nil))))

(define (rks-done-fabricated-events!)
  "Push any fabricated events in keybuf[t..mock_input-1] onto the
this-command-keys ring, then refresh the echo area.  After the
loop, update rks_t to the final value (= max of starting t and
mock_input) so the C `return t' yields the right key-sequence
length.  Mirrors the C body at lines 11824-11826 pre-M6s."
  (let* ((start ((force %rks-t)))
         (mi    ((force %rks-mock-input))))
    (let loop ((cur start))
      (cond
       ((< cur mi)
        ((force %add-command-key) ((force %rks-keybuf-ref) cur))
        (loop (+ cur 1)))
       (else
        ;; Sync rks_t to the post-loop value (only changed when start < mi).
        (when (> cur start)
          ((force %set-rks-t) cur))))))
  ((force %echo-update)))

(define (rks-done-downcase-undo! dont-downcase-last)
  "Restore the upper-case key in keybuf when the caller asked for
no downcasing OR the resolved binding is nil (undefined).  Mirrors
the C 5-line block:

  if ((dont_downcase_last || NILP (current_binding))
      && t > 0
      && t - 1 == original_uppercase_position)
    {
      keybuf[t - 1] = original_uppercase;
      shift_translated = false;
    }

See docs/keyboard.org §M6r."
  (let ((t-val   ((force %rks-t)))
        (cb      ((force %rks-current-binding)))
        (oup-pos ((force %rks-original-uppercase-position))))
    (when (and (or (not (%nilp dont-downcase-last)) (%nilp cb))
               (> t-val 0)
               (= (- t-val 1) oup-pos))
      ((force %rks-keybuf-set) (- t-val 1) ((force %rks-original-uppercase)))
      ((force %set-rks-shift-translated) #nil))))

(define (rks-done-install-unread-switch-frame!)
  "Copy the C-side rks_delayed_switch_frame into the global
unread_switch_frame.  Mirrors the C line at the done: block
(src/keyboard.c lines 11596 pre-M6p).  Runs before dynwind_end
to match the original behavior.  See docs/keyboard.org §M6p."
  ((force %set-unread-switch-frame)
   ((force %rks-delayed-switch-frame))))

(define (rks-done-install-shift-translated!)
  "If the C-side `rks_shift_translated' is non-zero, set the elisp
defvar `this-command-keys-shift-translated' to t.  Mirrors the
2-line C block near the end of read_key_sequence (just after the
downcase-undo, before the fabricated-events finalize loop).  See
docs/keyboard.org §M6o."
  (when (not (%nilp ((force %rks-shift-translated-p))))
    (set-symbol-value! 'this-command-keys-shift-translated #t)))

(define (rks-done-compute-remapped!)
  "Read read_key_sequence_cmd and, if it is a symbol, write the
result of `command-remapping' (looked up in the current active
keymaps) into read_key_sequence_remapped.  Else write nil.

Mirrors the C 3-line block at the top of the `done:' label
(src/keyboard.c lines 11554-11561 pre-M6n).  Runs before
dynwind_end so `command-remapping' resolves against the right
keymap stack."
  (let ((cmd ((force %read-key-sequence-cmd))))
    ((force %set-read-key-sequence-remapped)
     (if (and (not (%nilp cmd)) (symbol? cmd))
         ((%c 'command-remapping) cmd #nil #nil)
         #nil))))

(define (init-read-key-sequence-registrations)
  "Expose the M6a wrapper as an elisp symbol so tests can call it
directly bypassing the C DEFUNs.  The production callers go through
the C `read-key-sequence' / `read-key-sequence-vector' DEFUNs which
cached-dispatch into here."
  (for-each (lambda (sym-fun)
              (set-symbol-function! (car sym-fun) (cadr sym-fun)))
            `((--read-key-sequence-vs ,read-key-sequence-vs)
              (--discard-input         ,discard-input)
              (--set-input-mode        ,set-input-mode)
              (--current-input-mode    ,current-input-mode)
              (--posn-at-point         ,posn-at-point)
              (--input-pending-p       ,input-pending-p)
              ;; M6g — state-machine record types (elisp-visible
              ;; constructors / regular-define helpers only; srfi-9
              ;; accessors/setters are Scheme-internal).
              (--make-keyremap         ,make-keyremap)
              (--keyremap-empty-p      ,keyremap-empty-p)
              (--keyremap-reset!       ,keyremap-reset!)
              (--keyremap-rebase!      ,keyremap-rebase!)
              (--make-rks-state        ,make-rks-state)
              ;; M6h — setup-phase procedures (not yet wired into runtime)
              (--rks-setup-prompt!     ,rks-setup-prompt!)
              (--rks-setup-initial-keys-state! ,rks-setup-initial-keys-state!)
              (--rks-setup-initial-state-c!    ,rks-setup-initial-state-c!)
              ;; M6k — replay-phase procedures (parallel, not yet wired)
              (--rks-setup-replay-entire-sequence!
               ,rks-setup-replay-entire-sequence!)
              (--rks-setup-replay-sequence!
               ,rks-setup-replay-sequence!)
              ;; M6l — runtime variant (writes C-side shadows)
              (--rks-setup-replay-entire-sequence-c!
               ,rks-setup-replay-entire-sequence-c!)
              ;; M6m — runtime variant for replay_sequence
              (--rks-setup-replay-sequence-c!
               ,rks-setup-replay-sequence-c!)
              ;; M6n — done:-block remapped computation
              (--rks-done-compute-remapped!
               ,rks-done-compute-remapped!)
              ;; M6o — done:-block shift-translated install
              (--rks-done-install-shift-translated!
               ,rks-done-install-shift-translated!)
              ;; M6p — done:-block unread-switch-frame install
              (--rks-done-install-unread-switch-frame!
               ,rks-done-install-unread-switch-frame!)
              ;; M6r — done:-block downcase-undo
              (--rks-done-downcase-undo!
               ,rks-done-downcase-undo!)
              ;; M6s — done:-block fabricated-events finalize loop
              (--rks-done-fabricated-events!
               ,rks-done-fabricated-events!)
              ;; M6t — first_unbound short-circuit branch
              (--rks-first-unbound-short-circuit!
               ,rks-first-unbound-short-circuit!)
              ;; M6u — simple shift-translation (upper→lower case)
              (--rks-try-shift-translation-simple!
               ,rks-try-shift-translation-simple!)
              ;; M6v — help-char prefix check
              (--rks-try-help-char!
               ,rks-try-help-char!)
              ;; M6w — shifted-function-key shift-translation
              (--rks-try-shift-translation-fn-key!
               ,rks-try-shift-translation-fn-key!)
              ;; M6x — three translation-map walks
              (--rks-walk-translation-maps!
               ,rks-walk-translation-maps!)
              (--rks-walk-translation-maps
               ,rks-walk-translation-maps!)
              ;; M6y — per-iteration setup + replay_key restore
              (--rks-iter-setup-capture!
               ,rks-iter-setup-capture!)
              (--rks-iter-replay-restore!
               ,rks-iter-replay-restore!)
              ;; M6z — mock-input + end-of-macro cascade
              (--rks-iter-pre-read-cascade!
               ,rks-iter-pre-read-cascade!)
              ;; M6aa — final binding install + per-key bookkeeping
              (--rks-iter-install-binding!
               ,rks-iter-install-binding!)
              ;; M6ab — follow_key + first_unbound update
              (--rks-follow-key-and-update-first-unbound!
               ,rks-follow-key-and-update-first-unbound!)
              (--rks-follow-key-and-update-first-unbound
               ,rks-follow-key-and-update-first-unbound!)
              ;; M6ac — mouse-click prefix expansion
              (--rks-iter-mouse-click-prefix!
               ,rks-iter-mouse-click-prefix!)
              ;; M6ad — unbound-event reduction cascade
              (--rks-iter-unbound-event-reduction!
               ,rks-iter-unbound-event-reduction!)
              ;; M6ae — text-conversion-disable check
              (--rks-iter-maybe-disable-text-conversion!
               ,rks-iter-maybe-disable-text-conversion!))))
