;;; input-poll.scm --- M24: polling policy (emacs input-poll)
;;;
;;; Moves the polling *policy* — when to (re)start the poll atimer and
;;; at what period — out of src/keyboard.c and into Scheme.  The atimer
;;; *registration* stays C: --atimer-poll-restart! plus the raw
;;; `struct atimer *` poll_timer (a C pointer Scheme cannot hold) and the
;;; poll_for_input callback (a C function pointer).  See brief.org M24.
;;;
;;; Conventions (identical to M9-M24, cf. mod/emacs/timers.scm): #nil is
;;; elisp nil; %nilp is the local elisp-nil predicate (defined per-module,
;;; not exported from (emacs-elisp runtime)).  --interrupt-input-p is
;;; referenced through a defelisp delay ((force %--interrupt-input-p)), as
;;; elsewhere.  --atimer-poll-restart! is *not* — it is resolved through
;;; (%c '--atimer-poll-restart!) on every call, so the test suite can
;;; fset-stub it (cr.org Finding 2); a defelisp delay would cache the real
;;; C subr after the first (force ...) and defeat the stub.
;;;
;;; Unlike its siblings this module keeps module-level mutable state on
;;; purpose: *poll-timer-period* / *poll-timer-active?* are the cache the
;;; old C start_polling kept in the `poll_timer_time` static plus the
;;; `poll_timer == NULL` check.  That cache is the single piece of state
;;; M24 moves out of C (brief.org "Evidence for the design below").

(define-module (emacs input-poll)
  #:use-module (emacs elisp-ref)
  #:use-module (emacs-elisp runtime)
  #:declarative? #t
  #:export (start-polling!
            poll-timer-active?))

(defelisp %--interrupt-input-p    --interrupt-input-p)

(define (%nilp x) (eq? x #nil))

(define *poll-timer-period* #nil)   ; cached polling-period, mirrors old poll_timer_time
(define *poll-timer-active?* #f)    ; #t once --atimer-poll-restart! has armed poll_timer

(define (poll-timer-active?)
  "Report whether start-polling! has armed the poll atimer."
  *poll-timer-active?*)

(define (start-polling!)
  "Polling policy port of the old C `start_polling' (src/keyboard.c).

When Emacs uses interrupt-driven input (--interrupt-input-p non-nil) do
nothing.  Otherwise, if `polling-period' is a number and the cached
period differs (or the timer has not been armed yet), re-register the
poll atimer via --atimer-poll-restart! and record the armed period.

The when-to-restart decision and the cached period are the logic that
moved out of C; the atimer registration itself stays in the C shim."
  (when (%nilp ((force %--interrupt-input-p)))
    (let ((period (symbol-value 'polling-period)))
      (when (and (number? period)
                 (or (not *poll-timer-active?*)
                     (not (equal? period *poll-timer-period*))))
        ((%c '--atimer-poll-restart!))
        (set! *poll-timer-period* period)
        (set! *poll-timer-active?* #t))))
  #nil)
