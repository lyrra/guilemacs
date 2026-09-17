;;; process-wait.scm --- M32 imp-1: the process.c input-wait decision path
;;;                       ((emacs process-wait))
;;;
;;; Moves the *decision* logic of the live wait_reading_process_output
;;; (src/process.c, the copy at :5329, inside #ifdef subprocesses) out
;;; of C and into Scheme.  The *system call* stays C: select / pselect,
;;; the file-descriptor set build, the struct timespec arithmetic, the
;;; status_notify call, and the loop's own break/continue control.
;;; See docs/m32-plan.org A3.
;;;
;;; Two M32 exported procedures, plus three M36 ones:
;;;
;;;   wait-signal-drain   -- the read_kbd >= 0 / pending_signals choice
;;;                          (process.c:5392-5398).
;;;   wait-run-timers     -- the do/while timer loop (process.c:5483-5496).
;;;   wait-swallow!       -- M36: the site A swallow decision
;;;                          (process.c:5924-5937, pre-M36).
;;;   wait-input-pending? -- M36: the site B swallow decision
;;;                          (process.c:5944-5958, pre-M36).
;;;   wait-skip-select?   -- M36 imp-2: the no_avail decision
;;;                          (process.c:5713-5723, pre-M36).
;;;   accept-process-output-decision -- M39 imp-1: the accept-process-output
;;;                          timeout / just-this-one decision
;;;                          (process.c:4932-4970, pre-M39).
;;;
;;; The two breaks that leave the outer while (1) loop
;;; (requeued_command_events_pending_p at :5499-5501, and the
;;; wait_reading_process_output_1 call at :5504-5505) stay C: they
;;; cannot cross a live Scheme call frame.
;;;
;;; Conventions (identical to M9-M31): defelisp delayed references for
;;; every C DEFUN ((force %--foo)); #nil is elisp nil; no module-level
;;; mutable state.

(define-module (emacs process-wait)
  #:use-module (emacs elisp-ref)      ; %c, defelisp
  #:use-module (emacs-elisp runtime)
  #:declarative? #t
  #:export (wait-signal-drain
            wait-run-timers
            wait-swallow!
            wait-input-pending?
            wait-skip-select?
            accept-process-output-decision))

;; C shims.  --maybe-quit, --timers-run, --redisplay-preserve-echo-area
;; and the --pending-signals-* pair already exist (src/keyboard.c).
;; --pending-signals-p is a new M32 imp-1 entry: the module must read
;; the pending-signals flag (also written by a signal handler).
(defelisp %--maybe-quit                   --maybe-quit)
(defelisp %--pending-signals-p            --pending-signals-p)
(defelisp %--timers-run                   --timers-run)
(defelisp %--redisplay-preserve-echo-area --redisplay-preserve-echo-area)

;; (emacs timers) timer-check returns #nil (no active timer) or a
;; (SEC . NSEC) wait pair; its own loop consumes the #t "call again"
;; result.  Resolved lazily so the module does not eagerly import the
;; timer chain -- the same idiom gobble.scm uses for (emacs kbd-buffer).
(define %timer-check
  (delay (module-ref (resolve-module '(emacs timers)) 'timer-check)))

;; The signal drain target is already a Scheme procedure in (emacs
;; gobble); resolve it lazily, like the other cross-module targets.
(define %process-pending-signals!
  (delay (module-ref (resolve-module '(emacs gobble))
                     'process-pending-signals!)))

;; M36 imp-1: the swallow mechanism is already a Scheme procedure in
;; (emacs kbd-buffer) (the C swallow_events stub merely re-dispatched to
;; it).  Resolve it lazily, like the other cross-module targets.
(define %kbd-buffer-swallow-events!
  (delay (module-ref (resolve-module '(emacs kbd-buffer))
                     'kbd-buffer-swallow-events!)))

;; M36 imp-2: the detect family moved into (emacs kbd-buffer).  Resolve
;; both procedures lazily, like the swallow mechanism above.
(define %detect-input-pending?
  (delay (module-ref (resolve-module '(emacs kbd-buffer))
                     'detect-input-pending?)))
(define %detect-input-pending-run-timers?
  (delay (module-ref (resolve-module '(emacs kbd-buffer))
                     'detect-input-pending-run-timers?)))

;; Elisp truthiness: every value but #nil is true.  Each module carries
;; its own copy (see mod/emacs/recent-keys.scm).
(define (truthy? x)
  (not (eq? x #nil)))

(define (wait-signal-drain read-kbd)
  "Port of the signal-drain choice (src/process.c pre-M32 body): when
READ-KBD is non-negative, run maybe_quit -- the caller reads C-g as an
input character, so do not quit here; otherwise, when the
pending-signals flag is set, run process-pending-signals!.  Returns
nil."
  (if (>= read-kbd 0)
      ((force %--maybe-quit))
      (when (not (eq? ((force %--pending-signals-p)) #nil))
        ((force %process-pending-signals!))))
  #nil)

(define (wait-run-timers do-display)
  "Port of the do/while timer loop (src/process.c:5483-5496): each pass
calls timer-check; when the timers-run counter changed and DO-DISPLAY is
true, redisplay and loop again while input is not pending, else stop.
Returns the last timer delay: #nil (no active timer) or a (SEC . NSEC)
pair."
  (let loop ()
    (let* ((old-timers-run ((force %--timers-run)))
           (delay ((force %timer-check))))
      (if (and (not (= ((force %--timers-run)) old-timers-run))
               do-display)
          ;; A timer may have requeued itself and changed the delay;
          ;; retry unless input is now pending.  redisplay 9.
          (begin
            ((force %--redisplay-preserve-echo-area) 9)
            (if (not (eq? ((force %detect-input-pending?)) #nil))
                delay
                (loop)))
          delay))))

;; M36 imp-1: the two swallow_events call sites of the wait loop.  The C
;; stub swallowed nothing itself: it re-dispatched to
;; kbd-buffer-swallow-events! and mapped bool -> t/nil.  The decision
;; moves here; the C keeps the loop control and the static dispatch.

(define (wait-swallow! read-kbd do-display)
  "Port of the site A decision (src/process.c:5924-5937, pre-M36):
when READ-KBD is nonzero, test detect-input-pending-run-timers?; if
input is pending, swallow events, then retest.  Returns elisp t when
the wait loop must leave, else elisp nil (#nil); the C dispatcher
(src/process.c wait_swallow) reads the result with NILP.  Return #nil,
not Scheme #f, for false: this Guile reads #f as elisp true
(the elisp-nil convention: #f is not #nil)."
  (let ((dd (if do-display #t #nil)))
    (if (not (= read-kbd 0))
        (if (truthy? ((force %detect-input-pending-run-timers?) dd))
            (begin
              ((force %kbd-buffer-swallow-events!) dd)
              (if (truthy? ((force %detect-input-pending-run-timers?) dd))
                  #t
                  #nil))
            #nil)
        #nil)))

(define (wait-input-pending? read-kbd do-display)
  "Port of the site B decision (src/process.c:5944-5958, pre-M36):
when READ-KBD is 0 and input is pending, swallow events without running
timers.  Returns elisp t when it swallowed, else elisp nil (#nil);
return #nil, not Scheme #f, for false, because this Guile reads #f as
elisp true (#f is not #nil).

The C caller (src/process.c wait_input_pending) ignores the result on
purpose: the pre-M36 code left site B's retest disabled (#if 0:
'Exiting when read_kbd doesn't request that seems wrong').  Do not add
a retest or a break at site B."
  (if (and (= read-kbd 0)
           (truthy? ((force %detect-input-pending?))))
      (begin
        ((force %kbd-buffer-swallow-events!) (if do-display #t #nil))
        #t)
      #nil))

;; M36 imp-2: the no_avail decision of the wait loop (src/process.c
;; pre-M36 no_avail block at :5713-5723).  The retired C test read
;; detect_input_pending; the decision moves here.  C keeps nfds,
;; no_avail, and the FD_ZERO call.  Return elisp t or #nil; the C
;; dispatcher (src/process.c wait_skip_select) reads the result with
;; NILP, so return #nil, not a Scheme false value, for false.

(define (wait-skip-select? read-kbd)
  "Port of the no_avail decision (src/process.c:5713-5723, pre-M36):
when READ-KBD is nonzero and input is pending, the C skips the select
call.  Returns elisp t or #nil.  C keeps nfds, no_avail, and the
FD_ZERO call."
  (if (and (not (= read-kbd 0))
           (truthy? ((force %detect-input-pending?))))
      #t
      #nil))

;; M39 imp-1: the accept-process-output timeout decision (src/process.c
;; pre-M39 body at :4932-4970).  The C keeps CHECK_PROCESS, the thread
;; check, the XPROCESS pointer, and the wait_reading_process_output
;; call; this owns the timeout arithmetic and the just-this-one flag
;; mapping.  The caller (src/process.c accept_process_output_decision)
;; passes the already type-checked SECONDS (elisp nil, a fixnum, or a
;; float) and MILLISEC (elisp nil or a fixnum), the JUST-THIS-ONE value,
;; and whether PROCESS is non-nil.  A Scheme #f would read as elisp true
;; (#f is not #nil), so #nil is the elisp nil here.

;; TIMESPEC_HZ and dtotimespec mirror lib/timespec.h and
;; lib/dtotimespec.c.  dtotimespec rounds SEC toward positive infinity
;; into a (SEC . NSEC) pair with NSEC in [0, 1e9).
(define TIMESPEC-HZ 1000000000)

;; WAIT_READING_MAX = min (TYPE_MAXIMUM (time_t), INTMAX_MAX) on the
;; 64-bit build (src/lisp.h:4706): the float-timeout secs cap.
(define WAIT-READING-MAX (- (expt 2 63) 1))
(define TIME-T-MIN (- (expt 2 63)))

(define (dtotimespec sec)
  "Convert the double SEC to a (SEC . NSEC) pair, rounding toward
positive infinity (lib/dtotimespec.c).  Mirrors the C overflow guards."
  (cond
    ((not (< TIME-T-MIN sec)) (list TIME-T-MIN 0))
    ((not (< sec (+ 1 WAIT-READING-MAX))) (list WAIT-READING-MAX
                                                (- TIMESPEC-HZ 1)))
    (else
     (let* ((s (inexact->exact (truncate sec)))
            (frac (* TIMESPEC-HZ (- sec s)))
            (ns (inexact->exact (truncate frac)))
            (ns (+ ns (if (< ns frac) 1 0)))
            (s (+ s (quotient ns TIMESPEC-HZ)))
            (ns (remainder ns TIMESPEC-HZ)))
       (if (< ns 0)
           (list (- s 1) (+ ns TIMESPEC-HZ))
           (list s ns))))))

(define (accept-process-output-decision seconds millisec just-this-one
                                         have-process)
  "Port of the accept-process-output timeout decision
(src/process.c:4932-4970, pre-M39): fix up the obsolete MILLISEC
integer convention into a fractional SECONDS, turn SECONDS into a
(secs, nsecs) timeout with the WAIT_READING_MAX secs cap and the
nsecs = 0 default for a non-nil PROCESS, and map JUST-THIS-ONE to the
{-1, 0, 1} wait flag.  Returns (SECS NSECS JUST-THIS-ONE-FLAG) as
integers for wait_reading_process_output.  The C owns the type checks
and the final <= 0 -> t/#nil mapping."
  (let* ((sec (if (eq? millisec #nil)
                  seconds
                  (let ((ms (/ millisec 1000.0)))
                    (if (eq? seconds #nil)
                        ms
                        (+ ms seconds)))))
         (secs 0)
         (nsecs -1))
    (cond
      ((not (eq? sec #nil))
       (cond
         ((exact-integer? sec)
          (when (> sec 0)
            (set! secs sec)
            (set! nsecs 0)))
         ((inexact? sec)
          (when (> sec 0)
            (let ((t (dtotimespec sec)))
              (set! secs (min (car t) WAIT-READING-MAX))
              (set! nsecs (cadr t)))))))
      (have-process
       (set! nsecs 0)))
    (list secs nsecs
          ;; Match the pre-port C test `!FIXNUMP (just_this_one) ? 1 : -1':
          ;; only a fixnum (not a bignum) gives -1.  Use the Guile fixnum
          ;; bounds so a bignum just-this-one gives 1, like the C.
          (cond ((eq? just-this-one #nil) 0)
                ((and (exact-integer? just-this-one)
                      (<= most-negative-fixnum just-this-one
                          most-positive-fixnum))
                 -1)
                (else 1)))))
