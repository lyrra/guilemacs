(define-module (emacs read-key-sequence)
  #:use-module (emacs-elisp runtime)
  #:declarative? #t
  #:export (read-key-sequence-vs
            read-key-sequence-vs-string
            read-key-sequence-vs-vector
            discard-input
            set-input-mode
            current-input-mode
            posn-at-point
            input-pending-p
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
              (--input-pending-p       ,input-pending-p))))
