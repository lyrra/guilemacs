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
;;; Two M32 exported procedures, plus two M36 ones:
;;;
;;;   wait-signal-drain   -- the read_kbd >= 0 / pending_signals choice
;;;                          (process.c:5392-5398).
;;;   wait-run-timers     -- the do/while timer loop (process.c:5483-5496).
;;;   wait-swallow!       -- M36: the site A swallow decision
;;;                          (process.c:5924-5937, pre-M36).
;;;   wait-input-pending? -- M36: the site B swallow decision
;;;                          (process.c:5944-5958, pre-M36).
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
            wait-input-pending?))

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
;; M36 imp-1: the do_display-taking C test for the swallow decisions.
;; detect_input_pending_run_timers stays C.
(defelisp %--detect-input-pending-run-timers --detect-input-pending-run-timers)

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
            (if (not (eq? ((force %--detect-input-pending)) #nil))
                delay
                (loop)))
          delay))))

;; M36 imp-1: the two swallow_events call sites of the wait loop.  The C
;; stub swallowed nothing itself: it re-dispatched to
;; kbd-buffer-swallow-events! and mapped bool -> t/nil.  The decision
;; moves here; the C keeps the loop control and the static dispatch.

(define (wait-swallow! read-kbd do-display)
  "Port of the site A decision (src/process.c:5924-5937, pre-M36):
when READ-KBD is nonzero, test detect_input_pending_run_timers; if
input is pending, swallow events, then retest.  Returns elisp t when
the wait loop must leave, else elisp nil (#nil); the C dispatcher
(src/process.c wait_swallow) reads the result with NILP.  Return #nil,
not Scheme #f, for false: this Guile reads #f as elisp true
(src/frame.c:66).  detect_input_pending_run_timers stays C."
  (let ((dd (if do-display #t #nil)))
    (if (not (= read-kbd 0))
        (if (truthy? ((force %--detect-input-pending-run-timers) dd))
            (begin
              ((force %kbd-buffer-swallow-events!) dd)
              (if (truthy? ((force %--detect-input-pending-run-timers) dd))
                  #t
                  #nil))
            #nil)
        #nil)))

(define (wait-input-pending? read-kbd do-display)
  "Port of the site B decision (src/process.c:5944-5958, pre-M36):
when READ-KBD is 0 and detect_input_pending reports input, swallow
events without running timers.  Returns elisp t when it swallowed,
else elisp nil (#nil); return #nil, not Scheme #f, for false, because
this Guile reads #f as elisp true (src/frame.c:66).

The C caller (src/process.c wait_input_pending) ignores the result on
purpose: the pre-M36 code left site B's retest disabled (#if 0:
'Exiting when read_kbd doesn't request that seems wrong').  Do not add
a retest or a break at site B.  detect_input_pending stays C."
  (if (and (= read-kbd 0)
           (truthy? ((force %--detect-input-pending))))
      (begin
        ((force %kbd-buffer-swallow-events!) (if do-display #t #nil))
        #t)
      #nil))
