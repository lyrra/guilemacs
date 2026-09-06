;;; gobble.scm --- M25 imp-1: user-signal registration + drain
;;;                  ((emacs gobble))
;;;
;;; Moves the normal-context *policy* for user-signal registration and
;;; drain out of src/keyboard.c and into Scheme.  The raw C list stays
;;; C: `handle_user_signal' touches it from a signal handler (reads
;;; p->name, bumps p->npending), so Scheme can never hold the node
;;; handle.  Scheme owns the *decision*:
;;;
;;;   - add-user-signal!        duplicate-check + delegate to the C
;;;                             --user-signal-add! primitive (list
;;;                             mutation + sigaction arming).
;;;   - store-user-signal-events!  per-signal drain loop: for each
;;;                             registered signal with pending events,
;;;                             store one USER_SIGNAL_EVENT per pending
;;;                             count and reset it to zero.
;;;
;;; Of the two C entry points, only store_user_signal_events (called
;;; from gobble_input, normal context) is a thin dispatcher into this
;;; module.  add_user_signal stays a C body: init_signals calls it before
;;; syms_of_keyboard registers the --user-signal-* DEFUNs, so a Scheme
;;; dispatch would force --user-signal-registered? before it exists.
;;; add-user-signal! remains the module's tested registration API (a
;;; building block for imp-2/imp-3) but is not wired to that early C
;;; entry.  See brief.org M25 imp-1 and its close-out.
;;;
;;; Conventions (identical to M9-M24): defelisp delayed references for
;;; every C DEFUN ((force %--foo)); elisp nil is #nil; truthy? is the
;;; local elisp-nil predicate defined per-module, not exported.  Every
;;; call re-reads the C list fresh through the shims — no module-level
;;; mutable cache (unlike (emacs input-poll)); imp-1 has no cross-call
;;; state to cache.  kbd-buffer-store-event! lives in (emacs kbd-buffer)
;;; but that module is resolved lazily (a delayed module-ref), never
;;; imported eagerly: an eager #:use-module would make gobble.scm depend
;;; on the whole kbd-buffer import chain (lispy-event -> lispy-position),
;;; which fails at prelude time when lispy-position is not yet loaded —
;;; the same idiom read-key-sequence.scm uses for kbd-buffer-readable-events.

(define-module (emacs gobble)
  #:use-module (emacs elisp-ref)      ; %c, defelisp
  #:use-module (emacs-elisp runtime)
  #:declarative? #t
  #:export (add-user-signal!
            store-user-signal-events!))

(defelisp %--user-signal-registered?        --user-signal-registered?)
(defelisp %--user-signal-add!               --user-signal-add!)
(defelisp %--user-signal-list               --user-signal-list)
(defelisp %--user-signal-pending            --user-signal-pending)
(defelisp %--user-signal-pending-decrement! --user-signal-pending-decrement!)
(defelisp %--ie-user-signal-event           --ie-user-signal-event)

;; kbd-buffer-store-event! lives in (emacs kbd-buffer), which is not
;; imported eagerly (see module comment).  Resolve it lazily at call
;; time via a delayed module-ref, mirroring read-key-sequence.scm.
(define %kbd-buffer-store-event!
  (delay (module-ref (resolve-module '(emacs kbd-buffer))
                     'kbd-buffer-store-event!)))

(define (truthy? x)
  "Elisp truthiness: everything except #nil is true."
  (not (eq? x #nil)))

(define (add-user-signal! sig name)
  "Register user signal SIG with NAME if not already registered.
Module-level registration API (tested by the corpus; not wired to the
C init entry add_user_signal, which stays C).  If SIG is not already
registered, register it via the --user-signal-add! primitive (which
does the list mutation and sigaction arming).  Returns nil."
  (unless (truthy? ((force %--user-signal-registered?) sig))
    ((force %--user-signal-add!) sig name))
  #nil)

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
