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
;;; Two exported procedures:
;;;
;;;   wait-signal-drain  -- the read_kbd >= 0 / pending_signals choice
;;;                         (process.c:5392-5398).
;;;   wait-run-timers    -- the do/while timer loop (process.c:5483-5496).
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
            wait-run-timers))

;; C shims.  --maybe-quit, --timers-run, --redisplay-preserve-echo-area
;; and the --pending-signals-* pair already exist (src/keyboard.c).
;; --pending-signals-p and --detect-input-pending are new M32 imp-1
;; entries: the module must read the pending-signals flag (also written
;; by a signal handler) and the C detect_input_pending test.
(defelisp %--maybe-quit                   --maybe-quit)
(defelisp %--pending-signals-p            --pending-signals-p)
(defelisp %--timers-run                   --timers-run)
(defelisp %--redisplay-preserve-echo-area --redisplay-preserve-echo-area)
(defelisp %--detect-input-pending         --detect-input-pending)

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
            (if (not (eq? ((force %--detect-input-pending)) #nil))
                delay
                (loop)))
          delay))))
