;;; sysdep-main.scm --- M32 imp-5: the sysdep.c EINTR drain decision
;;;                      ((emacs sysdep-main))
;;;
;;; Moves the *decision* of the emacs_full_write EINTR drain
;;; (src/sysdep.c:2721-2727) out of C and into Scheme.  The *mechanism*
;;; stays C: the write () system call, the partial-write retry loop, the
;;; byte counters, the errno == EINTR test, and the loop control.
;;; See docs/m32-plan.org A1 and docs/kb.org ** caller-porting-recipe.
;;;
;;; The C site keeps the `if (interruptible)' guard (decision D2).  It
;;; calls the static dispatcher sysdep_full_write_drain, which memoises
;;; the resolved procedure here (the recursive_edit_1 idiom, as imp-4
;;; did in eval.c).  The dispatcher runs only for a nonzero
;;; INTERRUPTIBLE, so this procedure owns the whole interior decision:
;;;
;;;   INTERRUPTIBLE > 0  -> maybe_quit, then drain signals;
;;;   INTERRUPTIBLE == -1 -> drain signals only.
;;;
;;; The pending-signals test is owned by the shared guarded drain
;;; (emacs process-error) send-process-drain-signals!, so this procedure
;;; tests nothing itself.  Reuse that one definition (brief.org decision
;;; D4) instead of adding a second copy; resolve it lazily so this module
;;; does not eagerly import (emacs process-error).
;;;
;;; maybe-quit is called from Scheme, as (emacs process-wait)
;;; wait-signal-drain already does.  Imp-1 proved that is safe.
;;;
;;; Conventions (identical to M9-M32): defelisp delayed references for
;;; every C DEFUN ((force %--foo)); #nil is elisp nil; no module-level
;;; mutable state.

(define-module (emacs sysdep-main)
  #:use-module (emacs elisp-ref)      ; %c, defelisp
  #:use-module (emacs-elisp runtime)
  #:declarative? #t
  #:export (full-write-drain!))

;; C shim.  --maybe-quit already exists (src/keyboard.c); imp-1 uses it.
(defelisp %--maybe-quit --maybe-quit)

;; The shared guarded drain lives in (emacs process-error).  Resolve it
;; lazily so this module does not eagerly import that one.
(define %send-process-drain-signals!
  (delay (module-ref (resolve-module '(emacs process-error))
                     'send-process-drain-signals!)))

(define (full-write-drain! interruptible)
  "Port of the emacs_full_write EINTR drain (src/sysdep.c:2721-2727).
When INTERRUPTIBLE is positive, run maybe_quit; then always run the
shared guarded signal drain.  The caller runs this only for a nonzero
INTERRUPTIBLE (the C `if (interruptible)' guard, decision D2).  Returns
nil."
  (when (> interruptible 0)
    ((force %--maybe-quit)))
  ((force %send-process-drain-signals!))
  #nil)
