(define-module (emacs recent-keys)
  #:use-module (emacs elisp-ref)
  #:use-module (emacs-elisp runtime)
  #:declarative? #t
  #:export (recent-keys
            lossage-size
            record-char
            record-cmd-pseudo-event!
            init-recent-keys-registrations))

;;; M3 — recent-keys / lossage-size ported from keyboard.c.
;;;
;;; The recent-keys ring is C-owned in keyboard.c (recent_keys vector,
;;; recent_keys_index, total_keys, lossage_limit).  M17 ports the
;;; per-keystroke record_char body into this module — the roadmap's M17
;;; entry drops the old "record_char stays C" note; the whole body
;;; moves, and performance is deferred to M28 (no benchmark gate).
;;; The two user-facing DEFUNs ported here only run on `M-x recent-keys'
;;; and `M-x lossage-size' — fine for an FFI hop.
;;;
;;; See docs/keyboard.org §M3.  The C primitives this module wraps
;;; live in src/keyboard.c with the `--' prefix:
;;;   --recent-keys-ring, --recent-keys-index, --total-keys,
;;;   --lossage-limit, --min-num-recent-keys, --max-num-recent-keys,
;;;   --update-recent-keys, --make-event-array-from-vector.
;;; M17 adds the record-char shims: --recent-keys-index-set!,
;;; --total-keys-set!, --dribble-open-p, --dribble-write-event.


(define (%user-error msg)
  ;; Elisp `signal' isn't bound in Scheme top-level — go through the
  ;; elisp symbol table.  Same shape as `(user-error MSG)' from elisp.
  ((%c 'signal) 'user-error (list msg)))

;;; --- Helpers --------------------------------------------------------

(define (truthy? x)
  "Elisp truthiness: everything except #nil is true."
  (not (eq? x #nil)))

;;;;
;;;; lossage-size
;;;;

(define (lossage-size . args)
  "Return or set the maximum number of keystrokes recorded.
If called with a non-nil ARG, set the limit and return it.
Mirrors C Flossage_size; signals user-error on invalid input."
  (let ((arg (and (pair? args) (car args))))
    (cond
     ((or (not arg) (eq? arg #nil))
      ((%c '--lossage-limit)))
     (else
      (unless (and (integer? arg) (>= arg 0))
        (%user-error "Value must be a positive integer"))
      (let* ((osize  ((%c '--lossage-limit)))
             (minsz  ((%c '--min-num-recent-keys)))
             (maxsz  ((%c '--max-num-recent-keys))))
        (cond
         ((= arg osize)
          osize)
         ((< arg minsz)
          (%user-error (format #f "Value must be >= ~a" minsz)))
         ((> arg maxsz)
          (%user-error (format #f "Value must be <= ~a" maxsz)))
         (else
          (let* ((total ((%c '--total-keys)))
                 (kept  (if (> arg osize) total (min arg total))))
            ((%c '--update-recent-keys) arg kept)
            ((%c '--lossage-limit))))))))))

;;;;
;;;; recent-keys
;;;;

(define (recent-keys . args)
  "Return vector of last few events, not counting those from keyboard
macros.  If INCLUDE-CMDS is non-nil, include commands run as pseudo-events
of the form (nil . COMMAND).  Mirrors C Frecent_keys."
  (let ((include-cmds (and (pair? args)
                           (let ((v (car args))) (not (or (not v) (eq? v #nil)))))))
    (let ((ring  ((%c '--recent-keys-ring)))
          (idx   ((%c '--recent-keys-index)))
          (total ((%c '--total-keys)))
          (limit ((%c '--lossage-limit))))
      (cond
       ((or (zero? total)
            (and include-cmds (< total limit)))
        ;; Short ring: extract the prefix directly.  Returns a string
        ;; if every event fits in a unibyte char, otherwise a vector.
        ((%c '--make-event-array-from-vector) ring 0 total))
       (else
        ;; Full ring: walk circularly starting from the oldest, filter
        ;; out (nil . CMD) pseudo-events unless include-cmds is set.
        (let* ((start (if (< total limit) 0 idx))
               (acc '())
               (acc
                (let loop ((i start) (acc acc) (first? #t))
                  (cond
                   ((and (not first?) (= i idx)) acc)
                   (else
                    (let* ((e (vector-ref ring i))
                           (keep? (or include-cmds
                                      (not (pair? e))
                                      (not (or (eq? (car e) #nil)
                                               (not (car e))))))
                           (acc (if keep? (cons e acc) acc))
                           (j (if (>= (+ i 1) limit) 0 (+ i 1))))
                      (loop j acc #f)))))))
          (list->vector (reverse acc))))))))

;;;;
;;;; record-char
;;;;

;;; Private helper for record-char.  C is a cons whose car is help-echo
;;; or mouse-movement.  Walk back from IDX0 to read the previous ring
;;; slots and compute the `recorded' code (0, 1, -1, -2), performing the
;;; mouse-movement in-place ring replace as a side effect.  ev1/ev2/ev3
;;; may be any Lisp object (nil or a non-pair); every later read uses
;;; car-safe/cdr-safe, or a pair? check guards it earlier in the same
;;; `and'.
(define (record-char-recorded c ring idx0 limit)
  (let* ((ix1 (let ((i (- idx0 1))) (if (< i 0) (- limit 1) i)))
         (ev1 ((%c 'aref) ring ix1))
         (ix2 (let ((i (- ix1 1))) (if (< i 0) (- limit 1) i)))
         (ev2 ((%c 'aref) ring ix2))
         (ix3 (let ((i (- ix2 1))) (if (< i 0) (- limit 1) i)))
         (ev3 ((%c 'aref) ring ix3)))
    (cond
     ((eq? (car c) 'help-echo)
      ;; Don't record help-echo unless it shows a help message different
      ;; from the previously recorded one.
      (let ((help ((%c 'car-safe) ((%c 'cdr-safe) (cdr c)))))
        (cond
         ((not (string? help)) 1)
         ((and (pair? ev1)
               (eq? (car ev1) 'help-echo)
               (eq? ((%c 'car-safe) ((%c 'cdr-safe) (cdr ev1))) help))
          1)
         ((and (pair? ev1)
               (eq? (car ev1) 'mouse-movement)
               (pair? ev2)
               (eq? (car ev2) 'help-echo)
               (eq? ((%c 'car-safe) ((%c 'cdr-safe) (cdr ev2))) help))
          -1)
         ((and (pair? ev1)
               (eq? (car ev1) 'mouse-movement)
               (pair? ev2)
               (eq? (car ev2) 'mouse-movement)
               (pair? ev3)
               (eq? (car ev3) 'help-echo)
               (eq? ((%c 'car-safe) ((%c 'cdr-safe) (cdr ev3))) help))
          -2)
         (else 0))))
     ((eq? (car c) 'mouse-movement)
      ;; Only record one pair of mouse-movement on a window; further
      ;; movement on the same window replaces the last element.
      (let ((window ((%c 'car-safe) ((%c 'car-safe) (cdr c)))))
        (if (and (pair? ev1)
                 (eq? (car ev1) 'mouse-movement)
                 (eq? ((%c 'car-safe) ((%c 'car-safe) (cdr ev1))) window)
                 (pair? ev2)
                 (eq? (car ev2) 'mouse-movement)
                 (eq? ((%c 'car-safe) ((%c 'car-safe) (cdr ev2))) window))
            ;; Not macro-gated: C does this in-place replace even during
            ;; macro playback.
            (begin
              ((%c 'aset) ring ix1 c)
              1)
            0)))
     (else 0))))

;;; Private helper for record-char.  Compute the final (idx . total)
;;; to write back after `recorded' is known, performing the ring side
;;; effects: the recorded=0 append (copied event) and the recorded<0
;;; pop loop.  Returns a cons (IDX . TOTAL).  Avoids `let-values'
;;; (unbound in the interpreted guile-emacs environment).
(define (record-char-write-back recorded idx0 total0 limit c ring)
  (cond
   ((= recorded 0)
    (let ((total (if (< total0 limit) (+ total0 1) total0)))
      ;; Copy proper-list events in case some remapping modifies them by
      ;; side effect (bug#30955) — mirrors C `CONSP (c) ? Fcopy_sequence
      ;; (c) : c`.  A dotted pair (the (nil . CMD) pseudo-event) is freshly
      ;; consed by its writer, so nothing can mutate it; store it as-is
      ;; (guilemacs copy-sequence only accepts proper lists).
      ((%c 'aset) ring idx0
           (if (and (pair? c) (list? c)) ((%c 'copy-sequence) c) c))
      (cons (if (>= (+ idx0 1) limit) 0 (+ idx0 1)) total)))
   ((= recorded 1)
    ;; No ring write here: the mouse-movement replace already wrote
    ;; ring[ix1] in the dispatch above, and the help-echo dup writes
    ;; nothing.
    (cons idx0 total0))
   (else
    ;; recorded < 0: remove one or two events by putting nil at them and
    ;; moving the index backwards.
    (let loop ((rec recorded) (idx idx0) (total total0))
      (if (and (< rec 0) (> total 0))
          (let* ((total' (if (< total limit) (- total 1) total))
                 (idx'  (if (< (- idx 1) 0) (- limit 1) (- idx 1))))
            ((%c 'aset) ring idx' #nil)
            (loop (+ rec 1) idx' total'))
          (cons idx total))))))

(define (record-char c)
  "Port of C record_char (src/keyboard.c:4386-4529).

Append the input event C to the recent-keys ring, filtering repeated
help-echo and mouse-movement events, and mirror the dribble-file write.
C record_char now dispatches into this procedure (M17 imp-3);
record_menu_key and --rc-record-char reach it through record_char
unchanged.  Returns an unspecified value."
  ;; Guard: subr.el/read-passwd binds inhibit--record-char to avoid
  ;; recording passwords.  When not recording all keys and recording is
  ;; inhibited, do nothing at all — no ring write, no dribble write.
  (unless (and (not (truthy? (symbol-value 'record-all-keys)))
               (truthy? (symbol-value 'inhibit--record-char)))
    ;; Read the C globals once each and keep them as locals.  C re-reads
    ;; the globals on every access, but nothing in this body mutates them
    ;; in between, so one read each is equivalent — a deliberate
    ;; simplification, not a behavior change.
    (let* ((ring    ((%c '--recent-keys-ring)))
           (limit   ((%c '--lossage-limit)))
           (idx0    ((%c '--recent-keys-index)))
           (total0  ((%c '--total-keys)))
           ;; macro? is #t exactly when a kbd macro IS executing (i.e.
           ;; Vexecuting_kbd_macro is non-nil).  C names its guards with a
           ;; double negative (NILP (Vexecuting_kbd_macro)); pick a name
           ;; that reads correctly at each call site to avoid inverting it.
           (macro?  (truthy? (symbol-value 'executing-kbd-macro))))
      ;; Compute `recorded'.  For a plain (non help-echo/mouse-movement)
      ;; event this mirrors C's `else if (NILP (Vexecuting_kbd_macro))
      ;; store_kbd_macro_char (c);' — only fires for such plain events and
      ;; is itself macro-gated (unlike the mouse-movement ring write).
      (let ((recorded
             (if (and (pair? c)
                      (or (eq? (car c) 'help-echo)
                          (eq? (car c) 'mouse-movement)))
                 (record-char-recorded c ring idx0 limit)
                 (begin
                   (unless macro?
                     ((%c 'store-kbd-macro-event) c))
                   0))))
        ;; Final index/total write-back + counter bump.  Skipped entirely
        ;; during macro playback, matching C's `if (NILP (Vexecuting_kbd_macro))'
        ;; wrapping this whole section.
        (unless macro?
          (let* ((idx-total (record-char-write-back recorded idx0 total0 limit c ring))
                 (idx (car idx-total))
                 (total (cdr idx-total)))
            ((%c '--recent-keys-index-set!) idx)
            ((%c '--total-keys-set!) total)
            (set-symbol-value! 'num-nonmacro-input-events
                               (+ 1 (symbol-value 'num-nonmacro-input-events))))))
      ;; Dribble tail.  Unconditional on macro? here — the shim re-checks
      ;; both dribble-open and macro state internally; --dribble-open-p is
      ;; only a cheap pre-check to skip the call.
      (when (truthy? ((%c '--dribble-open-p)))
        ((%c '--dribble-write-event) c)))))

;;;;
;;;; record-cmd-pseudo-event!
;;;;

(define (record-cmd-pseudo-event! cmd)
  "Push the (nil . CMD) pseudo-event into the recent-keys ring,
rotating the ring when it is full.  C --record-recent-keys-cmd-pseudo-event
(M17 imp-3) dispatches into this procedure.  Reuses
record-char-write-back's append logic (recorded fixed at 0) so the ring
has one writer, not two — mirroring the C pseudo-event append exactly,
including that it does NOT bump num-nonmacro-input-events."
  (let* ((ring      ((%c '--recent-keys-ring)))
         (limit     ((%c '--lossage-limit)))
         (idx0      ((%c '--recent-keys-index)))
         (total0    ((%c '--total-keys)))
         (idx-total (record-char-write-back 0 idx0 total0 limit
                                            (cons #nil cmd) ring)))
    ((%c '--recent-keys-index-set!) (car idx-total))
    ((%c '--total-keys-set!) (cdr idx-total))))

;;;;
;;;; Registration
;;;;

(define (init-recent-keys-registrations)
  "Register the user-facing DEFUNs against their elisp symbols."
  (for-each (lambda (sym-fun)
              (set-symbol-function! (car sym-fun) (cadr sym-fun)))
            `((recent-keys  ,recent-keys)
              (lossage-size ,lossage-size))))
