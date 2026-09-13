;;; display.scm --- M34 imp-1: the dispnew.c display/poll callers
;;;                 ((emacs display))
;;;
;;; Moves the *decision* logic of the six live src/dispnew.c call sites
;;; into Scheme.  The *mechanism* stays C: the
;;; wait_reading_process_output call, the struct timespec formation, the
;;; set_buffer_internal switch, the wrong_type_argument signal, the
;;; redisplay_preserve_echo_area calls, and the raw Qt / Qnil returns.
;;; See brief.org 4.
;;;
;;; Five exported procedures:
;;;
;;;   sit-for-pre-wait!      -- the sit_for early-exit test.
;;;   sit-for-timeout        -- the sit_for timeout parse and the
;;;                             gobble_input call.
;;;   sit-for-done?          -- the sit_for final input test.
;;;   redisplay-swallow!     -- the Fredisplay body.
;;;   maybe-gen-help-event!  -- the help-event decision.
;;;
;;; The gobble_input call is folded into sit-for-timeout: brief.org 4
;;; lists it as port item 4, but brief.org 7 expects five dispatchers
;;; and the six old sites gone.  The C write order is parse -> gobble ->
;;; wait, and the gobble runs only on the "continue" path (the Qt early
;;; return and the wrong-type signal skip it), so sit-for-timeout
;;; reproduces that order.  Its `#if defined (USABLE_SIGIO) ||
;;; defined (USABLE_SIGPOLL)` guard moves to the existing
;;; --sigio-or-poll-usable-p shim, so src/dispnew.c no longer holds the
;;; SIGIO branch.  The gobble reaches (emacs gobble) gobble-input!
;;; through the same lazy module-ref the C gobble_input stub uses.
;;;
;;; The module adds one C primitive, --detect-input-pending-run-timers
;;; (src/keyboard.c, brief.org 5.2); it reads the executing-kbd-macro
;;; name through symbol-value.
;;;
;;; Conventions (identical to M9-M33, cf. mod/emacs/process-wait.scm):
;;; defelisp delayed references for every C DEFUN ((force %--foo)); #nil
;;; is elisp nil; cross-module targets are resolved lazily; no
;;; module-level mutable state.

(define-module (emacs display)
  #:use-module (emacs elisp-ref)      ; defelisp
  #:use-module (emacs-elisp runtime)  ; symbol-value
  #:declarative? #t
  #:export (sit-for-pre-wait!
            sit-for-timeout
            sit-for-done?
            redisplay-swallow!
            maybe-gen-help-event!))

;;; --- delayed C references ------------------------------------------
(defelisp %--detect-input-pending-run-timers
  --detect-input-pending-run-timers)
(defelisp %--detect-input-pending             --detect-input-pending)
(defelisp %--sigio-or-poll-usable-p           --sigio-or-poll-usable-p)
(defelisp %symbol-value                       symbol-value)

;; (emacs kbd-buffer) holds the swallow_events port, (emacs help-echo)
;; the gen_help_event port, and (emacs gobble) the gobble_input port.
;; Resolve each lazily, like the other cross-module targets, so the
;; module does not eagerly import them.
(define %kbd-buffer-swallow-events!
  (delay (module-ref (resolve-module '(emacs kbd-buffer))
                     'kbd-buffer-swallow-events!)))
(define %gen-help-event
  (delay (module-ref (resolve-module '(emacs help-echo)) 'gen-help-event)))
(define %gobble-input!
  (delay (module-ref (resolve-module '(emacs gobble)) 'gobble-input!)))

;;; --- Helpers -------------------------------------------------------
;;; Each module carries its own copy.  See mod/emacs/xterm.scm:74.
(define (%nilp x) (eq? x #nil))
(define (%elisp-t? x) (or (eq? x #t) (eq? x 't)))
;; Elisp truthiness: everything except #nil is true.  Normalizes the
;; t/nil result of a delayed C reference.
(define (truthy? x) (not (eq? x #nil)))

;;; WAIT_READING_MAX is min (TYPE_MAXIMUM (time_t), INTMAX_MAX) in
;;; src/lisp.h:4708.  On this platform time_t is a 64-bit signed type,
;;; so WAIT_READING_MAX equals INTMAX_MAX.
(define %wait-reading-max 9223372036854775807)

;;; --- sit-for-pre-wait! ---------------------------------------------
;;; Port of the sit_for early-exit test (dispnew.c:6830-6833).  Call
;;; swallow_events (DO-DISPLAY), then test the timers/input test or the
;;; executing-kbd-macro flag.  Return #t to mean "return nil now", else
;;; #nil.  The C keeps the display_option > 1 redisplay and the raw
;;; Qnil return.
(define (sit-for-pre-wait! do-display)
  ((force %kbd-buffer-swallow-events!) do-display)
  (if (or (not (%nilp ((force %--detect-input-pending-run-timers)
                       (if do-display #t #nil))))
          (not (%nilp ((force %symbol-value) 'executing-kbd-macro))))
      #t
      #nil))

;;; --- sit-for-timeout -----------------------------------------------
;;; dtotimespec helper, a faithful port of lib/dtotimespec.c: convert
;;; the double SEC to a (SEC . NSEC) pair, rounding toward positive
;;; infinity and clamping to the extremal value on overflow.
(define (%dtotimespec sec)
  (let ((hz 1000000000))
    (cond
     ((not (< (- (expt 2 63)) sec))            ; sec <= TYPE_MINIMUM (time_t)
      (cons (- (expt 2 63)) 0))
     ((not (< sec (expt 2.0 63)))              ; sec >= 1.0 + TYPE_MAXIMUM
      (cons (- (expt 2 63) 1) (- hz 1)))
     (else
      (let* ((s (inexact->exact (truncate sec)))
             (frac (* hz (- sec s)))
             (ns (inexact->exact (truncate frac))))
        (when (< ns frac) (set! ns (+ ns 1)))
        (set! s (+ s (quotient ns hz)))
        (set! ns (remainder ns hz))
        (when (< ns 0)
          (set! s (- s 1))
          (set! ns (+ ns hz)))
        (cons s ns))))))

;;; The pure parse step of sit-for-timeout; see the procedure below.
;;; TIMEOUT is the Lisp object.  Return:
;;;   #t            -- the caller must return Qt ("wait forever").
;;;   (SEC . NSEC)  -- the wait pair; C forms the struct timespec.
;;;   'wrong-type  -- TIMEOUT is not a number; C signals
;;;                   wrong_type_argument (Qnumberp, timeout).
;;; The C keeps the integer_to_intmax / Fnatnump detail because Guile
;;; integers always fit; min clamps a bignum to WAIT_READING_MAX just as
;;; the C does.
(define (%sit-for-timeout-parse timeout)
  (cond
   ;; EXACT-INTEGER?, not INTEGER?: Guile's INTEGER? is true for an
   ;; inexact real with an integral value, e.g. (integer? 2.0) => #t.
   ;; Elisp's INTEGERP is false for a float, so the C order
   ;; INTEGERP -> FLOATP sends (sit-for 1.0) to dtotimespec.  With the
   ;; wrong test the parse returned (1.0 . 0): a flonum car that
   ;; display_sit_for_timeout then feeds to scm_to_intmax.  Mirror the C
   ;; test so the integral float reaches the float branch below.
   ((exact-integer? timeout)
    (if (<= timeout 0)
        #t
        (cons (min timeout %wait-reading-max) 0)))
   ((and (real? timeout) (not (exact? timeout)))
    (let ((seconds (exact->inexact timeout)))
      (if (not (< 0 seconds))
          #t
          (let ((t (%dtotimespec seconds)))
            (cons (min (car t) %wait-reading-max) (cdr t))))))
   ((%elisp-t? timeout) (cons 0 0))
   (else 'wrong-type)))

;;; Port of the sit_for timeout parse (dispnew.c:6839-6873) and the
;;; gobble_input call (dispnew.c:6876-6878).  The gobble runs only when
;;; the parse yields a (SEC . NSEC) pair: the C order is parse, then
;;; gobble, then wait, and the C early returns and signal skip it.  The
;;; platform test moves from the C preprocessor to
;;; --sigio-or-poll-usable-p.
(define (sit-for-timeout timeout)
  "Parse TIMEOUT and run the gobble-input side effect.

Return the result of %sit-for-timeout-parse: #t for \"return Qt\", a
(SEC . NSEC) pair for a wait, or 'wrong-type.  Side effect: when TIMEOUT
parses to a pair and the platform has USABLE_SIGIO or USABLE_SIGPOLL,
call (emacs gobble) gobble-input! once.  The C order is parse -> gobble
-> wait; the C early returns and the wrong-type signal skip the gobble,
so the gobble runs only on the pair result.  Callers that want only the
parse must call %sit-for-timeout-parse directly."
  (let ((r (%sit-for-timeout-parse timeout)))
    (when (and (pair? r)
               (truthy? ((force %--sigio-or-poll-usable-p))))
      ((force %gobble-input!)))
    r))

;;; --- sit-for-done? -------------------------------------------------
;;; Port of the sit_for final input test (dispnew.c:6887).  Return #t
;;; when the wait is done — the caller returns Qnil — that is when
;;; NBERS > 0 or input is pending; else #nil, and the caller returns Qt.
;;; The reading / curbuf-eq-winbuf set_buffer_internal switch stays C.
(define (sit-for-done? nbytes)
  (if (or (> nbytes 0)
          (not (%nilp ((force %--detect-input-pending)))))
      #t
      #nil))

;;; --- redisplay-swallow! --------------------------------------------
;;; Port of the Fredisplay body (dispnew.c:6898-6900).  Call
;;; swallow_events (true), then test the executing-kbd-macro flag.
;;; Return #t to mean "return nil now", else #nil.  The C keeps the
;;; redisplay_preserve_echo_area (2) call and the raw Qt return.
(define (redisplay-swallow!)
  ((force %kbd-buffer-swallow-events!) #t)
  (if (%nilp ((force %symbol-value) 'executing-kbd-macro))
      #nil
      #t))

;;; --- maybe-gen-help-event! -----------------------------------------
;;; Port of the help-event decision in update_mouse_position
;;; (dispnew.c:4085-4093).  HELP and PREVIOUS are help_echo_string and
;;; previous_help_echo_string.  When either is non-nil, call
;;; (emacs help-echo) gen-help-event and return #t (the caller returns
;;; 1); else #nil.  The help_echo_string bookkeeping (dispnew.c:4078-4079)
;;; stays C, as does the XSETFRAME conversion of the frame argument.
(define (maybe-gen-help-event! help previous frame window object pos)
  (if (or (not (%nilp help))
          (not (%nilp previous)))
      (begin
        ((force %gen-help-event) help frame window object pos)
        #t)
      #nil))
