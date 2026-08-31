(define-module (emacs read-key-sequence)
  #:use-module (emacs elisp-ref)
  #:use-module (emacs-elisp runtime)
  #:use-module (srfi srfi-9)            ; define-record-type
  #:use-module ((emacs event-modifiers)
                #:select (parse-modifiers
                          apply-modifiers
                          up-modifier down-modifier drag-modifier
                          double-modifier triple-modifier))
  #:declarative? #t
  #:export (read-key-sequence-vs
            read-key-sequence-vs-string
            read-key-sequence-vs-vector
            discard-input
            set-input-mode
            current-input-mode
            posn-at-point
            input-pending-p
            get-input-pending!
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
            rks-setup-pre-loop!
            rks-setup-replay-entire-sequence!
            rks-setup-replay-entire-sequence-c!
            rks-setup-replay-sequence!
            rks-setup-replay-sequence-c!
            rks-done-post-dynwind!
            rks-done-compute-remapped!
            rks-done-install-shift-translated!
            rks-done-install-unread-switch-frame!
            rks-done-downcase-undo!
            rks-done-fabricated-events!
            rks-first-unbound-short-circuit!
            rks-try-shift-translation-simple!
            replay-sequence-continue
            replay-key-continue
            rks-classify-event-simple!
            rks-state-machine
            rks-read-key-sequence-start!
            rks-read-key-sequence-run!
            rks-read-key-sequence-finish!
            with-rks-sync
            rks-have-key-orchestrator!
            rks-try-help-char!
            rks-try-shift-translation-fn-key!
            rks-walk-translation-maps!
            rks-keyremap-step!
            rks-iteration-prepare!
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

;;;;
;;;; M6h — rks-keyremap-step!: port of C keyremap_step +
;;;; access_keymap_keyremap (src/keyboard.c:10601-10715).
;;;;
;;;; imp-3 wired rks-keyremap-step! into the live walk: it is now
;;;; driven by rks-walk-translation-maps! over the state's keyremap
;;;; records (see the M6h-r7 section below).  The C keyremap_step /
;;;; access_keymap_keyremap bodies were deleted.

(define %rks-access-keymap (delay (%c '--access-keymap)))
(define %rks-get-keymap    (delay (%c '--get-keymap)))
(define %rks-funcall       (delay (%c 'funcall)))
(define %rks-aref          (delay (%c 'aref)))
(define %rks-length        (delay (%c 'length)))
(define %rks-error         (delay (%c 'error)))
(define %rks-signal        (delay (%c 'signal)))
(define %rks-vectorp       (delay (%c 'vectorp)))
(define %rks-stringp       (delay (%c 'stringp)))
(define %rks-keymapp       (delay (%c 'keymapp)))
(define %rks-functionp     (delay (%c 'functionp)))
(define %rks-symbolp       (delay (%c 'symbolp)))
(define %rks-fboundp       (delay (%c 'fboundp)))
(define %rks-autoload-do-load (delay (%c 'autoload-do-load)))

;;; Port of access_keymap_keyremap (src/keyboard.c:10601-10642).
;;; Looks up KEY in MAP; handles the autoload-shaped branch (symbol
;;; whose function cell is a keymap or an array) and the funcall branch
;;; (keymap entry is a function, called with PROMPT).  START/END are
;;; the keybuf indices of the sequence being remapped; KEYBUF holds the
;;; events.  Returns the remap value (vector/string/function result, or
;;; nil when MAP has no usable binding for KEY).
(define (rks-access-keymap-keyremap map key prompt do-funcall start end keybuf)
  (let ((next ((force %rks-access-keymap) map key)))
    ;; Symbol whose function definition is a keymap or an array.  C:
    ;; SYMBOLP && !NILP(Ffboundp) && (ARRAYP(SYMBOL_FUNCTION) ||
    ;; KEYMAPP(SYMBOL_FUNCTION)) -- here ARRAYP is the practical
    ;; vectorp|stringp subset (see brief.org Open decision 1).  A plain
    ;; defalias to a keymap-valued symbol takes the same path as a real
    ;; autoload, because the branch only checks fboundp plus the cell's
    ;; type.
    (when (and ((force %rks-symbolp) next)
               (not (%nilp ((force %rks-fboundp) next))))
      (let ((fn (symbol-function next)))
        (when (or ((force %rks-keymapp) fn)
                  ((force %rks-vectorp) fn)
                  ((force %rks-stringp) fn))
          (set! next ((force %rks-autoload-do-load) fn next #nil)))))
    ;; If the keymap gives a function, call it with PROMPT and use its
    ;; return value instead of the function object.
    (when (and do-funcall
               (not (%nilp ((force %rks-functionp) next))))
      ;; Build Vcurrent_key_remap_sequence from keybuf[start..end]
      ;; (inclusive) and specbind it around the call (dynamic-wind, the
      ;; same idiom read-key-sequence-vs uses for its specbinds).
      (let* ((remap (list->vector
                     (let loop ((i end) (acc '()))
                       (if (< i start)
                           acc
                           (loop (- i 1) (cons (vector-ref keybuf i) acc))))))
             (tem  next)
             (saved (symbol-value 'current-key-remap-sequence)))
        (dynamic-wind
          (lambda () (set-symbol-value! 'current-key-remap-sequence remap))
          (lambda ()
            (set! next ((force %rks-funcall) tem prompt)))
          (lambda () (set-symbol-value! 'current-key-remap-sequence saved)))
        ;; Barf on an invalid return value, exactly like C's
        ;; signal_error ("Function returns invalid key sequence", tem).
        (unless (or (%nilp next)
                    ((force %rks-vectorp) next)
                    ((force %rks-stringp) next))
          ((force %rks-signal) 'error
           (list "Function returns invalid key sequence" tem)))))
    next))

;;; Port of keyremap_step (src/keyboard.c:10655-10715).
;;; FKEY is a <keyremap> record, mutated in place.  KEYBUF is the
;;; state's keybuf vector (rks-state-keybuf).  INPUT is the index of
;;; the last element in KEYBUF.  DOIT? says whether a translation may
;;; actually take place.  Returns the diff (an integer, possibly 0)
;;; when a translation happened, or #f when it did not.  The Scheme
;;; return convention packs C's (bool done, int* diff) into one value:
;;; 0 is truthy in Scheme, so a zero-length diff is not confused with
;;; "no translation".
(define (rks-keyremap-step! fkey keybuf input doit? prompt)
  (let* ((buf-start (keyremap-start fkey))
         (buf-end   (keyremap-end fkey))
         (key       (vector-ref keybuf (keyremap-end fkey))))
    (set-keyremap-end! fkey (+ (keyremap-end fkey) 1))
    (let ((next (if (not (%nilp ((force %rks-keymapp) (keyremap-parent fkey))))
                    (rks-access-keymap-keyremap
                     (keyremap-map fkey) key prompt doit?
                     buf-start buf-end keybuf)
                    #nil)))
      (if (and doit?
               (or ((force %rks-vectorp) next)
                   ((force %rks-stringp) next)))
          ;; keybuf[start..end] is bound in the map: replace it.
          (let* ((len  ((force %rks-length) next))
                 (diff (- len (- (keyremap-end fkey) (keyremap-start fkey)))))
            (when (<= (- READ-KEY-ELTS input) diff)
              ((force %rks-error) "Key sequence too long"))
            ;; Shift keybuf entries between fkey->end and input by DIFF
            ;; slots.  Negative diff shifts down from the low end;
            ;; positive shifts up from the high end (so as not to
            ;; overwrite not-yet-moved data).
            (if (< diff 0)
                (let loop ((i (keyremap-end fkey)))
                  (when (< i input)
                    (vector-set! keybuf (+ i diff) (vector-ref keybuf i))
                    (loop (+ i 1))))
                (when (> diff 0)
                  (let loop ((i (- input 1)))
                    (when (>= i (keyremap-end fkey))
                      (vector-set! keybuf (+ i diff) (vector-ref keybuf i))
                      (loop (- i 1))))))
            ;; Overwrite the old keys with the new ones.  Faref, not
            ;; vector-ref, because NEXT may be a string or a vector.
            (let loop ((i 0))
              (when (< i len)
                (vector-set! keybuf (+ (keyremap-start fkey) i)
                             ((force %rks-aref) next i))
                (loop (+ i 1))))
            ;; fkey->start = fkey->end += diff  (order matters: end is
            ;; incremented first, then start is set to the new end).
            (set-keyremap-end! fkey (+ (keyremap-end fkey) diff))
            (set-keyremap-start! fkey (keyremap-end fkey))
            (set-keyremap-map! fkey (keyremap-parent fkey))
            diff)
          ;; No usable binding (or doit? is false): follow into the
          ;; submap, resetting the scan if there is no bound suffix.
          (begin
            (set-keyremap-map! fkey
                               ((force %rks-get-keymap) next #nil #t))
            (when (not (pair? (keyremap-map fkey)))
              ;; C: fkey->end = ++fkey->start; both become start+1.
              (let ((s (keyremap-start fkey)))
                (set-keyremap-start! fkey (+ s 1))
                (set-keyremap-end! fkey (keyremap-start fkey)))
              (set-keyremap-map! fkey (keyremap-parent fkey)))
            #f)))))

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
                   fake-prefixed-keys
                   starting-buffer
                   disabled-conversion
                   used-mouse-menu-history
                   echo-local-start
                   keys-local-start
                   last-real-key-start
                   new-binding
                   used-mouse-menu
                   first-event
                   key
                   raw-keybuf
                   raw-keybuf-count)
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
                        set-rks-state-fake-prefixed-keys!)
  (starting-buffer      rks-state-starting-buffer
                        set-rks-state-starting-buffer!)
  (disabled-conversion  rks-state-disabled-conversion
                        set-rks-state-disabled-conversion!)
  (used-mouse-menu-history rks-state-used-mouse-menu-history
                           set-rks-state-used-mouse-menu-history!)
  (echo-local-start      rks-state-echo-local-start
                          set-rks-state-echo-local-start!)
  (keys-local-start      rks-state-keys-local-start
                          set-rks-state-keys-local-start!)
  (last-real-key-start   rks-state-last-real-key-start
                          set-rks-state-last-real-key-start!)
  (new-binding           rks-state-new-binding
                          set-rks-state-new-binding!)
  (used-mouse-menu       rks-state-used-mouse-menu
                          set-rks-state-used-mouse-menu!)
  (first-event           rks-state-first-event
                          set-rks-state-first-event!)
  (key                   rks-state-key
                          set-rks-state-key!)
  (raw-keybuf            rks-state-raw-keybuf
                          set-rks-state-raw-keybuf!)
  (raw-keybuf-count      rks-state-raw-keybuf-count
                          set-rks-state-raw-keybuf-count!))

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
   #nil                                ; fake-prefixed-keys
   #nil                                ; starting-buffer
   #nil                                ; disabled-conversion
   0                                    ; used-mouse-menu-history (bitmask)
   0                                    ; echo-local-start
   0                                    ; keys-local-start
   0                                    ; last-real-key-start
   #nil                                 ; new-binding
   #nil                                 ; used-mouse-menu
   #nil                                 ; first-event
   #nil                                 ; key
   #nil                                 ; raw-keybuf (populated on first writeback)
   0))                                   ; raw-keybuf-count

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
(define %current-buffer              (delay (%c 'current-buffer)))
(define %rks-starting-buffer         (delay (%c '--rks-starting-buffer)))

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

(define (truthy? x)
  "Elisp truthiness: everything except #nil is true."
  (not (eq? x #nil)))

(define %interrupts-deferred-p (delay (%c '--interrupts-deferred-p)))
(define %gobble-input          (delay (%c '--gobble-input)))

;; kbd-buffer-readable-events lives in (emacs kbd-buffer).  We resolve it
;; lazily at call time instead of importing the module: an eager
;; #:use-module makes read-key-sequence.scm depend on the whole kbd-buffer
;; import chain (lispy-event -> lispy-position) at compile time, which fails
;; in the isolated test harness when lispy-position is not yet loaded
;; (see cr.org Finding 1 + the m22 test note).  The C readable_events uses
;; the same public ref.
(define %kbd-buffer-readable-events
  (delay (module-ref (resolve-module '(emacs kbd-buffer))
                     'kbd-buffer-readable-events)))

(define (get-input-pending! flags)
  "Port of C get_input_pending (src/keyboard.c:7614-7629).  The caller
stores the return value into the C global `input_pending' itself."
  (define (quit-or-readable?)
    (or (truthy? (symbol-value 'quit-flag))
        (truthy? ((force %kbd-buffer-readable-events) flags))))
  (cond
   ((quit-or-readable?) #t)
   ((or (not (truthy? ((force %interrupt-input-p))))
        (truthy? ((force %interrupts-deferred-p))))
    ((force %gobble-input))
    (if (quit-or-readable?) #t #nil))
   (else #nil)))

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

;;; M6ad — unbound-event reduction cascade, ported from C
;;; (src/keyboard.c:9168-9270, deleted in imp-3).  Reduces an unbound
;;; mouse up/down/drag/double/triple event: strips modifiers trying to
;;; find a real binding, else disposes the event (rewinding the
;;; keyremap counters) and returns `replay-key' / `replay-sequence'.

(define (rks-event-head event)
  "EVENT_HEAD macro (src/keyboard.h:407): for a composite (CONSP)
event the car, else the event itself."
  (if (pair? event) (car event) event))

(define (rks-event-start event)
  "EVENT_START macro (src/keyboard.h:414): the position of a
composite event; touchscreen events take a different slot."
  (let ((head (rks-event-head event)))
    (if (or (eq? head 'touchscreen-begin)
            (eq? head 'touchscreen-end))
        ((%c 'cdr-safe) ((%c 'car-safe) ((%c 'cdr-safe) event)))
        ((%c 'car-safe) ((%c 'cdr-safe) event)))))

(define (rks-reduce-rewind-one-keyremap! km last-real)
  "Port of rks_reduce_rewind_one_keyremap (src/keyboard.c:9168-9175)."
  (when (> (keyremap-end km) last-real)
    (let ((new-pos (if (< last-real (keyremap-start km))
                       last-real
                       (keyremap-start km))))
      (set-keyremap-end! km new-pos)
      (set-keyremap-start! km new-pos)
      (set-keyremap-map! km (keyremap-parent km)))))

(define (rks-reduce-rewind-keyremaps-to-last-real! indec fkey keytran)
  "Port of rks_reduce_rewind_keyremaps_to_last_real
(src/keyboard.c:9177-9199): nested rewind of indec, then fkey, then
keytran."
  (let ((last-real ((force %rks-last-real-key-start))))
    (when (> (keyremap-end indec) last-real)
      (rks-reduce-rewind-one-keyremap! indec last-real)
      (when (> (keyremap-end fkey) last-real)
        (rks-reduce-rewind-one-keyremap! fkey last-real)
        (when (> (keyremap-end keytran) last-real)
          (rks-reduce-rewind-one-keyremap! keytran last-real))))))

(define (rks-reduce-dispose-unbound-up-down! indec fkey keytran)
  "Port of rks_reduce_dispose_unbound_up_down (src/keyboard.c:9201-9212).
Rewinds the keyremap counters to last-real-key-start, sets mock-input
to 0 (replay-key) or last-real-key-start (replay-sequence), and returns
the matching symbol."
  (rks-reduce-rewind-keyremaps-to-last-real! indec fkey keytran)
  (let ((t ((force %rks-t)))
        (last-real ((force %rks-last-real-key-start))))
    ((force %set-rks-mock-input) (if (= t last-real) 0 last-real))
    (if (= t last-real) 'replay-key 'replay-sequence)))

(define (rks-reduce-try-new-binding! modifiers breakdown)
  "Port of rks_reduce_try_new_binding (src/keyboard.c:9217-9233).
Looks up the modifier-reduced click; on a hit, updates
current-binding, new-binding and rks-key and returns #t."
  (let* ((new-head  (apply-modifiers modifiers (car breakdown)))
         (new-click (list new-head (rks-event-start ((force %rks-key)))))
         (new-bind  (rks-follow-key ((force %rks-current-binding))
                                    new-click)))
    ((force %set-rks-new-binding) new-bind)
    (if (%nilp new-bind)
        #f
        (begin
          ((force %set-rks-current-binding) new-bind)
          ((force %set-rks-key) new-click)
          #t))))

(define (rks-reduce-strip-loop! breakdown modifiers reducer-mask
                               indec fkey keytran)
  "Port of rks_reduce_strip_loop (src/keyboard.c:9235-9250).  Strips
one modifier level at a time (triple → double → drag), trying
rks-reduce-try-new-binding! after each; falls to
rks-reduce-dispose-unbound-up-down! when only up/down remain."
  (let loop ((modifiers modifiers))
    (if (zero? (logand modifiers reducer-mask))
        'fall-through
        (cond
         ((not (zero? (logand modifiers triple-modifier)))
          (let ((nm (logxor modifiers
                           (logior double-modifier triple-modifier))))
            (if (rks-reduce-try-new-binding! nm breakdown)
                'fall-through
                (loop nm))))
         ((not (zero? (logand modifiers double-modifier)))
          (let ((nm (logand modifiers (lognot double-modifier))))
            (if (rks-reduce-try-new-binding! nm breakdown)
                'fall-through
                (loop nm))))
         ((not (zero? (logand modifiers drag-modifier)))
          (let ((nm (logand modifiers (lognot drag-modifier))))
            (if (rks-reduce-try-new-binding! nm breakdown)
                'fall-through
                (loop nm))))
         (else
          (rks-reduce-dispose-unbound-up-down! indec fkey keytran))))))

(define (rks-reduce-mouse-event-loop! indec fkey keytran)
  "Port of the --rks-reduce-mouse-event-loop DEFUN (src/keyboard.c:9252-9270).
Returns `fall-through', `replay-key', or `replay-sequence'."
  (let ((head (rks-event-head ((force %rks-key)))))
    (if (not (symbol? head))
        'fall-through
        (let ((breakdown (parse-modifiers head)))
          (if (not (pair? breakdown))
              'fall-through
              (let ((modifiers (cadr breakdown))
                    (reducer-mask (logior up-modifier down-modifier
                                          drag-modifier double-modifier
                                          triple-modifier)))
                (if (zero? (logand modifiers reducer-mask))
                    'fall-through
                    (rks-reduce-strip-loop!
                     breakdown modifiers reducer-mask
                     indec fkey keytran))))))))

(define (rks-iter-unbound-event-reduction!)
  "M6h-r6: unbound-event reduction with inline record sync."
  (let ((rec ((force %rks-state-current))))
    (when (not (%nilp rec))
      (rks-sync-read rec 'key-count)
      (rks-sync-read rec 'first-unbound))
    (let ((t ((force %rks-t)))
          (fu ((force %rks-first-unbound))))
      (when (< t fu)
        ((force %set-rks-first-unbound) t)))
    (let ((result
           (if (%nilp rec)
               'fall-through
               (rks-reduce-mouse-event-loop!
                (rks-state-indec rec)
                (rks-state-fkey rec)
                (rks-state-keytran rec)))))
      (when (not (%nilp rec))
        (rks-sync-write rec 'first-unbound))
      result)))

(define %rks-mouse-click-prefix-body
  (delay (%c '--rks-mouse-click-prefix-body)))

(define (rks-iter-mouse-click-prefix!)
  "M6h-r5: mouse-click prefix expansion with inline record sync.
Syncs record-resident fields (key-count, mock-input) only;
iteration-locals (key, last_real_key_start, fake_prefixed_keys)
remain bare file-static reads."
  (let ((rec ((force %rks-state-current))))
    (when (not (%nilp rec))
      (rks-sync-read rec 'key-count)
      (rks-sync-read rec 'mock-input))
    (let ((key ((force %rks-key))))
      (if (and (pair? key) (symbol? (car key)))
          (let ((result ((force %rks-mouse-click-prefix-body))))
            (when (not (%nilp rec))
              (rks-sync-write rec 'mock-input))
            result)
          'fall-through))))

(define %rks-key          (delay (%c '--rks-key)))
(define %set-rks-key      (delay (%c '--set-rks-key)))
(define %rks-last-real-key-start
  (delay (%c '--rks-last-real-key-start)))
(define %rks-keybuf-depth (delay (%c '--rks-keybuf-depth)))
(define %rks-first-unbound
  (delay (%c '--rks-first-unbound)))
(define %rks-new-binding
  (delay (%c '--rks-new-binding)))
(define %set-rks-new-binding
  (delay (%c '--set-rks-new-binding)))
(define %set-rks-first-unbound
  (delay (%c '--set-rks-first-unbound)))

;;; Port of follow_key (src/keyboard.c:8603-8608).
;;; KEYMAP is a keymap (or keymap-designating object); KEY is the event
;;; to look up.  Returns the binding, or nil when unbound.  The two
;;; --get-keymap booleans are (error-if-not-keymap, autoload) per the
;;; --get-keymap doc (src/keyboard.c:8350); C follow_key calls
;;; get_keymap (keymap, 0, 1) i.e. error=#nil, autoload=#t.  The inner
;;; access_keymap is access_keymap (map, key, 1, 0, 1) — t_ok=1,
;;; noinherit=0, autoload=1, exactly what --access-keymap hardcodes.
(define (rks-follow-key keymap key)
  ((force %rks-access-keymap)
   ((force %rks-get-keymap) keymap #nil #t)
   key))

;;; Port of test_undefined (src/keyboard.c:10717-10724).
;;; A binding counts as "undefined" when it is nil, is the symbol
;;; `undefined', or (for a symbol) command-remapping resolves to
;;; `undefined'.
(define (rks-test-undefined? binding)
  (or (%nilp binding)
      (eq? binding 'undefined)
      (and (symbol? binding)
           (eq? ((%c 'command-remapping) binding #nil #nil)
                'undefined))))

(define (rks-follow-key-and-update-first-unbound!)
  "M6h-r1: follow_key + first_unbound update with inline record sync."
  (let ((rec ((force %rks-state-current))))
    (when (not (%nilp rec))
      (rks-sync-read rec 'key-count)
      (rks-sync-read rec 'current-binding)
      (rks-sync-read rec 'first-unbound))
    (let* ((cb  ((force %rks-current-binding)))
           (key ((force %rks-key)))
           (new-binding (rks-follow-key cb key)))
      (if (%nilp new-binding)
          #nil
          (begin
            ((force %set-rks-new-binding) new-binding)
            (let ((candidate (1+ ((force %rks-t)))))
              (when (> candidate ((force %rks-first-unbound)))
                ((force %set-rks-first-unbound) candidate)))
            (when (not (%nilp rec))
              (rks-sync-write rec 'first-unbound))
            #t)))))

(define %rks-iter-install-binding
  (delay (%c '--rks-iter-install-binding)))

(define (rks-iter-install-binding! new-binding)
  "M6h-r4: install binding with inline record sync."
  (let ((rec ((force %rks-state-current))))
    (when (not (%nilp rec))
      (rks-sync-read rec 'key-count)
      (rks-sync-read rec 'current-binding))
    ((force %rks-iter-install-binding) new-binding)
    (when (not (%nilp rec))
      (rks-sync-write rec 'key-count)
      (rks-sync-write rec 'current-binding))))

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

(define %rks-state-current
  (delay (%c '--rks-state-current)))
(define %rks-state-stack-push
  (delay (%c '--rks-state-stack-push)))
(define %rks-state-stack-pop
  (delay (%c '--rks-state-stack-pop)))
(define %rks-record-get-int
  (delay (%c '--rks-record-get-int)))
(define %rks-record-set-int
  (delay (%c '--rks-record-set-int)))
(define %rks-record-set-bool
  (delay (%c '--rks-record-set-bool)))
(define %rks-record-get
  (delay (%c '--rks-record-get)))
(define %rks-record-set
  (delay (%c '--rks-record-set)))
(define %set-rks-current-binding
  (delay (%c '--set-rks-current-binding)))

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
(define RKS-SLOT-SHIFT-TRANSLATED     10)
(define RKS-SLOT-DELAYED-SWITCH-FRAME  11)
(define RKS-SLOT-ORIGINAL-UPPERCASE    12)
(define RKS-SLOT-ORIGINAL-UPPERCASE-POSITION 13)
(define RKS-SLOT-FAKE-PREFIXED-KEYS    14)
(define RKS-SLOT-STARTING-BUFFER       15)
(define RKS-SLOT-DISABLED-CONVERSION   16)
(define RKS-SLOT-USED-MOUSE-MENU-HISTORY 17)
(define RKS-SLOT-ECHO-LOCAL-START       18)
(define RKS-SLOT-KEYS-LOCAL-START       19)
(define RKS-SLOT-LAST-REAL-KEY-START    20)
(define RKS-SLOT-NEW-BINDING            21)
(define RKS-SLOT-USED-MOUSE-MENU        22)
(define RKS-SLOT-FIRST-EVENT            23)
(define RKS-SLOT-KEY                    24)
(define RKS-SLOT-RAW-KEYBUF             25)
(define RKS-SLOT-RAW-KEYBUF-COUNT       26)

;; M6h — Scheme-side record↔file-static sync infrastructure.
;; `with-rks-sync' macro + `rks-sync-read'/`rks-sync-write' dispatch
;; helpers.  See docs/m6-plan-revised.org.
;;
;; Currently supported fields: `t', `mock-input'.  Keyremap fields
;; (indec/fkey/keytran .start/.end/.map/.parent) are intentionally
;; NOT synced through the record — the walks read and mutate them
;; via C file-statics directly, same as the pre-M6 C bulk subr.
;; The required record-side accessors (--rks-record-get-slot,
;; --rks-keyremap-get-int) don't exist yet; they'll be added when
;; M6i actually retires the keyremap file-statics.

(define (rks-sync-read rec field)
  "Sync one field FROM record TO C file-static.  Returns #nil."
  (case field
    ((key-count)       ((force %set-rks-t)
                        ((force %rks-record-get-int)
                         rec RKS-SLOT-KEY-COUNT)))
    ((mock-input)      ((force %set-rks-mock-input)
                        ((force %rks-record-get-int)
                         rec RKS-SLOT-MOCK-INPUT)))
    ((current-binding) ((force %set-rks-current-binding)
                        ((force %rks-record-get)
                         rec RKS-SLOT-CURRENT-BINDING)))
    ((first-unbound)   ((force %set-rks-first-unbound)
                        ((force %rks-record-get-int)
                         rec RKS-SLOT-FIRST-UNBOUND)))
    ((keytran-start)   ((force %set-rks-keytran-start)
                        ((force %rks-record-get-int)
                         (force %rks-keytran-start))))  ;; FIXME: read from record
    (else (error "rks-sync-read: unknown field" field)))
  #nil)

(define (rks-sync-write rec field)
  "Sync one field FROM C file-static TO record.  Returns #nil."
  (case field
    ((mock-input)      ((force %rks-record-set-int)
                        rec RKS-SLOT-MOCK-INPUT
                        ((force %rks-mock-input))))
    ((key-count)       ((force %rks-record-set-int)
                        rec RKS-SLOT-KEY-COUNT
                        ((force %rks-t))))
    ((current-binding) ((force %rks-record-set)
                        rec RKS-SLOT-CURRENT-BINDING
                        ((force %rks-current-binding))))
    ((first-unbound)    ((force %rks-record-set-int)
                         rec RKS-SLOT-FIRST-UNBOUND
                         ((force %rks-first-unbound))))
    ((shift-translated) ((force %rks-record-set-bool)
                         rec RKS-SLOT-SHIFT-TRANSLATED
                         (if ((force %rks-shift-translated-p)) #t #nil)))
    (else (error "rks-sync-write: unknown field" field)))
  #nil)

;; M6h — Scheme-side record↔file-static sync macro.
;;
;; Wraps a C shim call with:
;;   1. Pre-sync: read each read-field from record into C file-static.
;;   2. Body: the C shim call.
;;   3. Post-sync via dynamic-wind: write each write-field from C
;;      file-static back to record.  Runs on normal return AND on
;;      non-local exit (exception / prompt-abort), so the record
;;      can never lag the file-statics across a fault.
;;
;; When no record is active (rks_state_depth == 0), the syncs are
;; no-ops and the body runs unchanged.

(define (rks--sync-read-fields rec fields)
  "Run rks-sync-read for each field in FIELDS list."
  (for-each (lambda (f) (rks-sync-read rec f)) fields))

(define (rks--sync-write-fields rec fields)
  "Run rks-sync-write for each field in FIELDS list."
  (for-each (lambda (f) (rks-sync-write rec f)) fields))

(define-syntax with-rks-sync
  (syntax-rules ()
    "Wrap BODY with record↔file-static sync.  READ-FIELDS synced from
record to C before BODY; WRITE-FIELDS from C to record after,
including on non-local exit.

Note: dynamic-wind is used for the post-sync to guarantee it runs
on exception / prompt-abort.  In Guilemacs, read_char uses
call_with_prompt for quit handling — if the prompt traverses this
sync boundary, the after-thunk will fire on each crossing.  The
post-sync is idempotent (read file-static, write record), so
multiple firings are safe.

Implementation note: the field lists are built as quoted lists
(=(list 'read-fields ...)=) and dispatched via a helper procedure
rather than as macro-template repetitions of =(quote read-fields)
...=.  The latter shape produced an \"Unbound variable: key-count\"
error in the Guilemacs syntax-rules expander; the helper-procedure
shape compiles cleanly."
    ((_ (read read-fields ...) (write write-fields ...) body ...)
     (let ((rec ((force %rks-state-current))))
       (when (not (%nilp rec))
         (rks--sync-read-fields rec (list 'read-fields ...)))
       (dynamic-wind
         (lambda () #f)
         (lambda () (begin body ...))
         (lambda ()
           (when (not (%nilp rec))
             (rks--sync-write-fields rec (list 'write-fields ...)))))))))

;;; M6h-r7 — three translation-map walks, ported from the C DEFUNs
;;; --rks-walk-indec / --rks-fkey-shortcut-or-walk / --rks-walk-keytran
;;; (src/keyboard.c:10215-10354, deleted in imp-3).  Each drives
;;; rks-keyremap-step! over the state's own fkey/keytran/indec
;;; <keyremap> records (mutated in place) and mirrors the live C
;;; keybuf into the state's keybuf vector so the walk sees (and writes
;;; back) the caller-owned keybuf array.  When no keybuf is on the C
;;; stack (the pure-record / test path) the record's own keybuf vector
;;; is authoritative.

(define (rks-keybuf-c-to-record! keybuf n)
  "Copy the live C keybuf into the record's KEYBUF vector so the walk
sees the caller-owned buffer, and zero (nil) the slots the walk may
touch beyond the live sequence.

Only the first N slots of the C keybuf are read: N = max (rks_t,
mock_input) is the walk's input bound, and those slots are the only
ones guaranteed to hold initialized Lisp objects.  Reading the
uninitialized C slots beyond them into this GC-scanned Scheme vector
would crash the collector, so they are set to nil instead (writing
nil back to them is harmless — the C code never reads past mock).
When no keybuf is on the C stack (the pure-record / test path) the
caller's own KEYBUF slots [0, N) are preserved and only the tail is
nilled."
  (let ((n (min n READ-KEY-ELTS)))
    (if (> ((force %rks-keybuf-depth)) 0)
        (let loop ((i 0))
          (if (< i n)
              (begin
                (vector-set! keybuf i ((force %rks-keybuf-ref) i))
                (loop (+ i 1)))
              (begin
                (when (< i READ-KEY-ELTS)
                  (vector-set! keybuf i #nil)
                  (loop (+ i 1))))))
        (let loop ((i n))
          (when (< i READ-KEY-ELTS)
            (vector-set! keybuf i #nil)
            (loop (+ i 1)))))))

(define (rks-keybuf-record-to-c! keybuf)
  "Write the record's KEYBUF vector back into the live C keybuf.
No-op when no keybuf is on the C stack."
  (when (> ((force %rks-keybuf-depth)) 0)
    (let loop ((i 0))
      (when (< i READ-KEY-ELTS)
        ((force %rks-keybuf-set) i (vector-ref keybuf i))
        (loop (+ i 1))))))

;; Port of the C --rks-walk-indec loop (src/keyboard.c:10229-10244):
;; while (indec.end < rks_t) with doit = true, input = max(rks_t, mock).
;; Returns the new mock on a translation, #f when exhausted.
(define (rks-walk-indec-scheme! indec keybuf prompt t mock)
  (let loop ((mock mock))
    (if (>= (keyremap-end indec) t)
        #f
        (let ((diff (rks-keyremap-step! indec keybuf
                                        (max t mock) #t prompt)))
          (if diff
              (+ diff (max t mock))
              (loop mock))))))

;; Port of rks_fkey_shortcut_advance (src/keyboard.c:10250-10264):
;; advance fkey past rks_t so keytran can still scan.  Returns #f
;; (never reports a hit).
(define (rks-fkey-shortcut-advance-scheme! fkey t)
  (when (< (keyremap-start fkey) t)
    (set-keyremap-start! fkey t)
    (set-keyremap-end! fkey t)
    (set-keyremap-map! fkey (keyremap-parent fkey)))
  #f)

;; Port of rks_fkey_walk (src/keyboard.c:10267-10293):
;; while (fkey.end < indec.start); doit? for this walk is
;; (and (= (+ (keyremap-end fkey) 1) t) (rks-test-undefined? cb)).
;; On a hit, also adds diff to indec.start and indec.end.
(define (rks-fkey-walk-scheme! fkey indec keybuf prompt t mock
                               current-binding)
  (let loop ((mock mock))
    (if (>= (keyremap-end fkey) (keyremap-start indec))
        #f
        (let ((diff (rks-keyremap-step!
                     fkey keybuf (max t mock)
                     (and (= (+ (keyremap-end fkey) 1) t)
                          (rks-test-undefined? current-binding))
                     prompt)))
          (if diff
              (let ((new-mock (+ diff (max t mock))))
                (set-keyremap-end! indec (+ (keyremap-end indec) diff))
                (set-keyremap-start! indec (+ (keyremap-start indec) diff))
                new-mock)
              (loop mock))))))

;; Port of --rks-fkey-shortcut-or-walk (src/keyboard.c:10295-10314):
;; the shortcut branch when current-binding is a bound non-keymap that
;; is not `undefined' and indec.start >= rks_t; otherwise the fkey walk.
(define (rks-fkey-shortcut-or-walk-scheme! fkey indec keybuf prompt
                                          t mock current-binding)
  (if (and (%nilp ((force %rks-keymapp) current-binding))
           (not (rks-test-undefined? current-binding))
           (>= (keyremap-start indec) t))
      (rks-fkey-shortcut-advance-scheme! fkey t)
      (rks-fkey-walk-scheme! fkey indec keybuf prompt t mock
                             current-binding)))

;; Port of the C --rks-walk-keytran loop (src/keyboard.c:10332-10353):
;; while (keytran.end < fkey.start) with doit = true.  On a hit, adds
;; diff to indec.start/end AND fkey.start/end.
(define (rks-walk-keytran-scheme! keytran fkey indec keybuf prompt t mock)
  (let loop ((mock mock))
    (if (>= (keyremap-end keytran) (keyremap-start fkey))
        #f
        (let ((diff (rks-keyremap-step! keytran keybuf (max t mock)
                                        #t prompt)))
          (if diff
              (let ((new-mock (+ diff (max t mock))))
                (set-keyremap-end! indec (+ (keyremap-end indec) diff))
                (set-keyremap-start! indec (+ (keyremap-start indec) diff))
                (set-keyremap-end! fkey (+ (keyremap-end fkey) diff))
                (set-keyremap-start! fkey (+ (keyremap-start fkey) diff))
                new-mock)
              (loop mock))))))

(define (rks-walk-translation-maps! prompt)
  "M6h-r7: three-map translation walk with inline record sync.
Drives rks-keyremap-step! over the state's own fkey/keytran/indec
records.  Returns t when any of the three walks completes a
translation (mock-input updated), nil when exhausted.  Replaces the
deleted C --rks-walk-indec / --rks-fkey-shortcut-or-walk /
--rks-walk-keytran DEFUNs."
  (let ((rec ((force %rks-state-current))))
    (when (not (%nilp rec))
      (rks-sync-read rec 'key-count)
      (rks-sync-read rec 'mock-input))
    (if (%nilp rec)
        #nil
        (let* ((tval ((force %rks-t)))
               (mock ((force %rks-mock-input)))
               (keybuf  (rks-state-keybuf rec))
               (fkey    (rks-state-fkey rec))
               (keytran (rks-state-keytran rec))
               (indec   (rks-state-indec rec))
               (cb      ((force %rks-current-binding))))
          (rks-keybuf-c-to-record! keybuf (max tval mock))
          (let ((result
                 (or (rks-walk-indec-scheme! indec keybuf prompt tval mock)
                     (rks-fkey-shortcut-or-walk-scheme!
                      fkey indec keybuf prompt tval mock cb)
                     (rks-walk-keytran-scheme!
                      keytran fkey indec keybuf prompt tval mock))))
            (rks-keybuf-record-to-c! keybuf)
            ((force %set-rks-mock-input) (if result result mock))
            (rks-sync-write rec 'mock-input)
            (if result #t #nil))))))

(define %rks-fn-key-shift-translate
  (delay (%c '--rks-fn-key-shift-translate)))
(define %rks-reset-fkey-and-keytran-scans
  (delay (%c '--rks-reset-fkey-and-keytran-scans)))

(define (rks-try-shift-translation-fn-key! key)
  "M6h-r3: fn-key shift-translation with inline record sync."
  (let ((rec ((force %rks-state-current))))
    (when (not (%nilp rec))
      (rks-sync-read rec 'key-count)
      (rks-sync-read rec 'mock-input)
      (rks-sync-read rec 'current-binding))
    (if (or (not (%nilp ((force %rks-current-binding))))
            (< ((force %rks-keytran-start)) ((force %rks-t))))
        #nil
        (let* ((breakdown (parse-modifiers key))
               (mods (if (pair? breakdown)
                         (cadr breakdown)
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
                (when (not (%nilp rec))
                  (rks-sync-write rec 'mock-input)
                  (rks-sync-write rec 'shift-translated))
                #t))))))

;; Wave B: hoisted label bodies, callable from any Scheme wrapper.

(define (rks-setup-pre-loop!)
  "Wave B: thin wrapper for the pre-loop initial-state capture.
(The replay-sequence-continue logic runs at the replay_sequence:
label, which follows this call in the C flow.)"
  (rks-setup-initial-state-c!))

;; Phase 1 (Option 3): post-read_char event classification.
;; Predicates only — C performs the side effects.

(define %switch-frame-event-p
  (delay (%c '--rks-switch-frame-event-p)))

(define (rks-classify-event-simple!)
  "Classify the post-read_char key.  Returns a symbol:
  `menu-reject', `buffer-switched', `quit-in-other-frame',
  `switch-frame', or `fall-through'."
  (let ((key ((force %rks-key)))
        (quit-char ((force %quit-char))))
    (cond
     ((eq? key #t)                                 'menu-reject)
     ((and (integer? key) (integer? quit-char)
           (= key quit-char)
           (not (eq? ((force %current-buffer))
                     ((force %rks-starting-buffer)))))
      'quit-in-other-frame)
     (((%c 'bufferp) key)                          'buffer-switched)
     ((not (%nilp ((force %switch-frame-event-p) key)))
      'switch-frame)
     (else                                         'fall-through))))

(define %rks-replay-sequence-restore
  (delay (%c '--rks-replay-sequence-restore)))

(define (replay-sequence-continue)
  "Hoisted body of C `replay_sequence:' label.  Resets state and
recomputes the initial key binding from keybuf, then restores
this_command_key_count + echo from record slots via the C-side
helper.  Returns `continue'."
  (let ((mock ((force %rks-mock-input))))
    (rks-setup-replay-sequence-c!
     (if (> mock 0) ((force %rks-keybuf-ref) 0) #nil)
     (if (> mock 1) ((force %rks-keybuf-ref) 1) #nil)))
  ((force %rks-replay-sequence-restore))
  'continue)

(define (replay-key-continue)
  "Hoisted body of C `replay_key:' label.  Restores echo/keys state
and snapshots last_real_key_start.  Returns `continue'."
  (rks-iter-replay-restore!)
  (rks-iter-pre-read-cascade!)
  'continue)

(define (rks-iteration-prepare!)
  "Wave B: fold setup-capture + maybe-disable + replay-restore +
pre-read-cascade into one call.  Returns `mock', `done', or
`read-char' (the pre-read-cascade result)."
  (rks-iter-setup-capture!)
  (rks-iter-maybe-disable-text-conversion!)
  (rks-iter-replay-restore!)
  (rks-iter-pre-read-cascade!))

(define (rks-done-post-dynwind! dont-downcase-last)
  "Wave B: fold the post-dynwind done: body (downcase-undo,
shift-translated, fabricated-events) into one Scheme call."
  (rks-done-downcase-undo! dont-downcase-last)
  (rks-done-install-shift-translated!)
  (rks-done-fabricated-events!))

(define (rks-have-key-orchestrator! key prompt)
  "Wave B — full have_key: body folded into one Scheme call.
Returns one of `done', `continue', or `fall-through'.  C dispatches
`done' to its goto target; all other outcomes (the `replay_key:' and
`replay_sequence:' bodies were hoisted) let the loop continue
without taking a C goto."
  (define (cascade)
    (cond
     ((not (%nilp (rks-walk-translation-maps! prompt)))
      (replay-sequence-continue))
     ((not (%nilp (rks-try-shift-translation-simple! key)))
      (replay-sequence-continue))
     ((not (%nilp (rks-try-help-char! key)))
      'done)
     ((not (%nilp (rks-try-shift-translation-fn-key! key)))
      (replay-sequence-continue))
     (else 'fall-through)))
  (define (install-and-cascade)
    (rks-iter-install-binding! ((force %rks-new-binding)))
    (cascade))
  (let ((mc (rks-iter-mouse-click-prefix!)))
    (cond
     ((eq? mc 'replay-key)      (replay-key-continue))
     ((eq? mc 'replay-sequence) (replay-sequence-continue))
     (else
      (let ((bound (rks-follow-key-and-update-first-unbound!)))
        (if (not (%nilp bound))
            (install-and-cascade)
            (let ((reduction (rks-iter-unbound-event-reduction!)))
              (cond
               ((eq? reduction 'replay-key)      (replay-key-continue))
               ((eq? reduction 'replay-sequence) (replay-sequence-continue))
               (else (install-and-cascade))))))))))

;; Phase 4 Step 3a — top-level state machine for read_key_sequence.
;; Hoists the C while-loop into a tail-recursive Scheme loop.  Not
;; yet wired into the C bulk subr; lands as plumbing first.

(define %set-rks-delayed-switch-frame
  (delay (%c '--set-rks-delayed-switch-frame)))
(define %rks-vquit-flag-clear
  (delay (%c '--rks-vquit-flag-clear)))
(define %rks-first-event-init
  (delay (%c '--rks-first-event-init)))
(define %rks-raw-keybuf-push
  (delay (%c '--rks-raw-keybuf-push)))
(define %rks-read-char-and-kboard
  (delay (%c '--rks-read-char-and-kboard)))
;; Step 3b-proper.1 helpers.
(define %rks-loop-continue-p
  (delay (%c '--rks-loop-continue-p)))
(define %rks-buffer-switched-handler
  (delay (%c '--rks-buffer-switched-handler)))
(define %rks-quit-in-other-frame-handler
  (delay (%c '--rks-quit-in-other-frame-handler)))

(define (rks-state-machine prompt
                           can-return-switch-frame
                           prevent-redisplay
                           fix-current-buffer)
  "Phase 4 Step 3: hoisted read_key_sequence state machine.

PROMPT — read_char prompt string (or nil).
CAN-RETURN-SWITCH-FRAME / PREVENT-REDISPLAY / FIX-CURRENT-BUFFER —
Qt/Qnil booleans mirroring the C function-parameter args.

Returns:
  -1 (fixnum) — menu rejected; caller returns -1 from read_key_sequence.
  `done       — caller runs post-loop done-* dispatch and returns rks_t.

Entry assumes C has already done: dynwind_begin, keybuf-stack push,
state-record push, setup-prompt!, setup-pre-loop!."

  (define (have-key-step)
    (case (rks-have-key-orchestrator! ((force %rks-key)) prompt)
      ((done)            'done)
      ((replay-sequence) (replay-sequence-continue) (loop))
      ((replay-key)      (replay-key-continue) (loop))
      ((fall-through)    (loop))
      (else              (loop))))

  (define (fall-through-step)
    ((force %rks-vquit-flag-clear))
    ((force %rks-first-event-init) fix-current-buffer)
    ((force %rks-raw-keybuf-push) ((force %rks-key)))
    (have-key-step))

  (define (classify-step)
    (case (rks-classify-event-simple!)
      ((menu-reject)         -1)
      ((buffer-switched)
       ((force %rks-buffer-switched-handler) fix-current-buffer)
       (replay-sequence-continue)
       (loop))
      ((quit-in-other-frame)
       ((force %rks-quit-in-other-frame-handler))
       (replay-sequence-continue)
       (loop))
      ((switch-frame)
       (if (or (> ((force %rks-t)) 0)
               (%nilp can-return-switch-frame))
           (begin
             ((force %rks-vquit-flag-clear))
             ((force %set-rks-delayed-switch-frame) ((force %rks-key)))
             (replay-key-continue)
             (loop))
           (fall-through-step)))
      ((fall-through) (fall-through-step))
      (else           (fall-through-step))))

  (define (loop)
    ;; Mirror the C while-loop's exit condition.
    (if (%nilp ((force %rks-loop-continue-p)))
        'done
        (if (eq? (rks-first-unbound-short-circuit!) 'replay-sequence)
            (begin (replay-sequence-continue) (loop))
            (case (rks-iteration-prepare!)
              ((done)      'done)
              ((mock)      (have-key-step))
              ((read-char)
               (case ((force %rks-read-char-and-kboard)
                      prevent-redisplay
                      prompt
                      ((force %rks-current-binding))
                      (symbol-value 'last-nonmenu-event))
                 ((replay-sequence) (replay-sequence-continue) (loop))
                 ((continue)        (classify-step))
                 (else              (loop))))
              (else        (loop))))))

  ;; Entry point — equivalent to falling through to replay_sequence:.
  (replay-sequence-continue)
  (loop))

(define (rks-read-key-sequence-start! prompt)
  "Hoisted setup-half of the outer C `read_key_sequence' body
(M21 imp-4).  C has already: pushed a fresh <rks-state> record (from
`make-rks-state') onto the state stack, opened the Guile dynwind
region, and pushed the caller's keybuf.  This call takes over the
setup that must precede the HAVE_TEXT_CONVERSION block (which stays in
C, restoring the pre-hoist ordering — cr.org Finding 1):

  * load the 3 scalars (key-count / mock-input / current-binding)
    from the record into the C file-statics (entry-time resets are the
    fresh-record defaults produced by `make-rks-state');
  * rks-setup-prompt! / rks-setup-pre-loop! / the replay-entire-sequence
    keyremap setup.

C then runs the text-conversion block (reading-key-sequence flag /
one-time disable) and hands off to rks-read-key-sequence-run! for the
state machine.  Returns #t."
  (let ((rec ((force %rks-state-current))))
    ;; Entry-time resets are the `make-rks-state' defaults: key-count=0,
    ;; mock-input=0, current-binding=nil, used-mouse-menu-history=0,
    ;; disabled-conversion/fake-prefixed-keys/delayed-switch-frame=nil.
    (rks-sync-read rec 'key-count)
    (rks-sync-read rec 'mock-input)
    (rks-sync-read rec 'current-binding)
    (rks-setup-prompt! prompt)
    (rks-setup-pre-loop!)
    (rks-setup-replay-entire-sequence! rec))
  #t)

(define (rks-read-key-sequence-run! prompt
                                    can-return-switch-frame
                                    prevent-redisplay
                                    fix-current-buffer)
  "Hoisted state-machine half of the outer C `read_key_sequence' body
(M21 imp-4).  Runs *after* the HAVE_TEXT_CONVERSION block (which C
places between this and rks-read-key-sequence-start!), matching the
pre-hoist ordering:

  * run rks-state-machine;
  * on `done', run the pre-dynwind-end rks-done-compute-remapped! and
    rks-done-install-unread-switch-frame!.

Returns the state-machine result: fixnum -1 (menu-reject) or the
symbol `done'.  On -1 the caller pops the record itself (Finding D);
on `done' the caller calls rks-read-key-sequence-finish! after
dynwind_end."
  (let ((sm (rks-state-machine prompt can-return-switch-frame
                               prevent-redisplay fix-current-buffer)))
    (if (and (integer? sm) (= sm -1))
        -1
        (begin
          (rks-done-compute-remapped!)
          (rks-done-install-unread-switch-frame!)
          'done))))

(define (rks-read-key-sequence-finish! dont-downcase-last)
  "Hoisted finish-half of the outer C `read_key_sequence' body
(M21 imp-4).  Runs *after* dynwind_end (the name matches
rks-done-post-dynwind!).  Only reached on the non-reject path.

  * rks-done-post-dynwind! (downcase-undo, shift-translated,
    fabricated-events side effects);
  * store the 3 scalars back from the C file-statics to the record;
  * pop the record off the state stack.

Returns the final key count (rks_t, as a fixnum) which C returns
directly."
  (rks-done-post-dynwind! dont-downcase-last)
  (let ((rec ((force %rks-state-current))))
    (rks-sync-write rec 'key-count)
    (rks-sync-write rec 'mock-input)
    (rks-sync-write rec 'current-binding))
  ((force %rks-state-stack-pop))
  ((force %rks-t)))

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
  "M6h-r2: shift-translation with inline record sync."
  (let ((rec ((force %rks-state-current))))
    (when (not (%nilp rec))
      (rks-sync-read rec 'key-count)
      (rks-sync-read rec 'mock-input)
      (rks-sync-read rec 'current-binding))
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
                (when (not (%nilp rec))
                  (rks-sync-write rec 'mock-input)
                  (rks-sync-write rec 'shift-translated))
                #t))))))

(define (rks-first-unbound-short-circuit!)
  "Shrink the keybuf when a prefix has no binding.  If fired, calls
replay-sequence-continue and returns `replay-sequence'; otherwise
nil.  Wave B: the C goto replay_sequence is folded into this call."
  (let* ((fu  ((force %rks-first-unbound)))
         (kts ((force %rks-keytran-start))))
    (cond
     ((< fu kts)
      (let ((shift (+ fu 1)))
        ((force %rks-keybuf-shift-down) shift)
        ((force %set-rks-mock-input) (- ((force %rks-t)) shift))
        ((force %rks-keyremaps-shrink-by) shift))
      (replay-sequence-continue)
      'replay-sequence)
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
              (--rks-done-post-dynwind!
               ,rks-done-post-dynwind!)
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
              ;; Wave B — have_key: orchestrator
              (--rks-have-key-orchestrator!
               ,rks-have-key-orchestrator!)
              (--rks-classify-event-simple!
               ,rks-classify-event-simple!)
              ;; Phase 4 Step 3 — top-level state machine
              (--rks-state-machine
               ,rks-state-machine)
              ;; M6ac — mouse-click prefix expansion
              (--rks-iter-mouse-click-prefix!
               ,rks-iter-mouse-click-prefix!)
              ;; M6ad — unbound-event reduction cascade
              (--rks-iter-unbound-event-reduction!
               ,rks-iter-unbound-event-reduction!)
              ;; M6ae — text-conversion-disable check
              (--rks-iter-maybe-disable-text-conversion!
               ,rks-iter-maybe-disable-text-conversion!))))
