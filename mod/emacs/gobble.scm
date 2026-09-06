;;; gobble.scm --- M25 imp-1 + imp-2: user-signal drain + async input
;;;                  ((emacs gobble))
;;;
;;; Moves the normal-context *policy* for user-signal drain and for the
;;; async-input/pending-signals dispatch out of src/keyboard.c and into
;;; Scheme.  The raw C data stays C (see per-imp notes):
;;;
;;; imp-1 (store-user-signal-events!):
;;;   - store-user-signal-events!  per-signal drain loop: for each
;;;                             registered signal with pending events,
;;;                             store one USER_SIGNAL_EVENT per pending
;;;                             count and reset it to zero.  The raw C
;;;                             user_signals list stays C because
;;;                             handle_user_signal touches it from a
;;;                             signal handler.
;;;
;;; imp-2 (handle-async-input! / process-pending-signals!):
;;;   - handle-async-input!      drain the input queue: call
;;;                             --gobble-input until it reports no more
;;;                             input (0) or a blocked read (< 0).
;;;   - process-pending-signals! clear the pending-signals flag, then
;;;                             handle-async-input!, then run due
;;;                             atimers.  Order matches the C original.
;;;
;;; Three C entry points are now thin dispatchers into this module:
;;; store_user_signal_events (imp-1), handle_async_input and
;;; process_pending_signals (imp-2).  Unlike add_user_signal (imp-1),
;;; neither imp-2 entry point has an early-init caller: all callers run
;;; during normal command-loop or wait-loop execution, so a Scheme
;;; dispatch is safe there (see
;;; early-init-c-body-before-defun-registration, docs/kb.org).
;;; add_user_signal stays a C body: init_signals calls it before
;;; syms_of_keyboard registers the --user-signal-* DEFUNs.  See brief.org
;;; M25 imp-1 and imp-2 and their close-outs.
;;;
;;; Conventions (identical to M9-M24): defelisp delayed references for
;;; every C DEFUN ((force %--foo)); elisp nil is #nil.  Every call
;;; re-reads the C state fresh through the shims — no module-level
;;; mutable cache (unlike (emacs input-poll)).  kbd-buffer-store-event!
;;; lives in (emacs kbd-buffer) but that module is resolved lazily (a
;;; delayed module-ref), never imported eagerly: an eager #:use-module
;;; would make gobble.scm depend on the whole kbd-buffer import chain
;;; (lispy-event -> lispy-position), which fails at prelude time when
;;; lispy-position is not yet loaded — the same idiom
;;; read-key-sequence.scm uses for kbd-buffer-readable-events.

(define-module (emacs gobble)
  #:use-module (emacs elisp-ref)      ; %c, defelisp
  #:use-module (emacs-elisp runtime)
  #:declarative? #t
  #:export (store-user-signal-events!
            handle-async-input!
            process-pending-signals!))

(defelisp %--user-signal-list               --user-signal-list)
(defelisp %--user-signal-pending            --user-signal-pending)
(defelisp %--user-signal-pending-decrement! --user-signal-pending-decrement!)
(defelisp %--ie-user-signal-event           --ie-user-signal-event)

;; imp-2 shims: --gobble-input (reused, also defelisp'd by kbd-buffer.scm
;; and read-key-sequence.scm under their own local names) plus the two new
;; single-purpose triggers for the C cells that must stay C.
(defelisp %--gobble-input           --gobble-input)
(defelisp %--pending-signals-clear! --pending-signals-clear!)
(defelisp %--do-pending-atimers!    --do-pending-atimers!)

;; kbd-buffer-store-event! lives in (emacs kbd-buffer), which is not
;; imported eagerly (see module comment).  Resolve it lazily at call
;; time via a delayed module-ref, mirroring read-key-sequence.scm.
(define %kbd-buffer-store-event!
  (delay (module-ref (resolve-module '(emacs kbd-buffer))
                     'kbd-buffer-store-event!)))

(define (store-user-signal-events!)
  "Port of store_user_signal_events (src/keyboard.c pre-M25 body):
for every registered signal with pending events, store one
USER_SIGNAL_EVENT per pending count and reset it to zero.  Returns nil."
  (for-each
   (lambda (sig)
     (let loop ((n ((force %--user-signal-pending) sig)))
       (when (> n 0)
         ((force %kbd-buffer-store-event!)
          ((force %--ie-user-signal-event) sig) #f)
         (loop ((force %--user-signal-pending-decrement!) sig)))))
   ((force %--user-signal-list)))
  #nil)

(define (handle-async-input!)
  "Port of handle_async_input (pre-imp-2 C body): call gobble-input
until it reports no more input (0) or a blocked read (negative).  The
dropped-platform HAVE_ANDROID urgent-query check was deleted, not
ported.  Returns nil."
  (let loop ()
    (when (> ((force %--gobble-input)) 0)
      (loop)))
  #nil)

(define (process-pending-signals!)
  "Port of process_pending_signals (pre-imp-2 C body): clear the
pending-signals flag, drain async input, then run any due atimers.
Order matches the C original exactly.  Returns nil."
  ((force %--pending-signals-clear!))
  (handle-async-input!)
  ((force %--do-pending-atimers!))
  #nil)
