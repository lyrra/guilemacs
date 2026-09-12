;;; eval-main.scm --- M32 imp-4: the eval.c caller of
;;;                    process_pending_signals
;;;                    ((emacs eval-main))
;;;
;;; Moves the *decision* of probably_quit (src/eval.c) out of C and into
;;; Scheme.  The *mechanism* stays C: process_quit_flag calls
;;; Fkill_emacs, Fthrow, and quit ().  Those make non-local exits, and
;;; quit () does not return, so that function stays C.  See
;;; docs/m32-plan.org A4 and docs/kb.org ** caller-porting-recipe.
;;;
;;; The C entry point probably_quit stays C (declared in lisp.h, called
;;; from the maybe_quit inline).  It becomes a thin dispatcher into
;;; probably-quit!, using the recursive_edit_1 idiom: a memoed static
;;; SCM plus scm_c_public_ref ("emacs eval-main", "probably-quit!").
;;;
;;; probably-quit! owns the if / else-if decision:
;;;
;;;   branch 1 (quit):    call back into the C helper
;;;                       --process-quit-flag!, which runs the static
;;;                       eval.c process_quit_flag.  It may not return
;;;                       (quit () does not return), the same contract
;;;                       as the --recursive-edit-quit! DEFUN.
;;;   branch 2 (signals): run the pending-signals drain, guarded by the
;;;                       pending-signals flag.
;;;
;;; The two branch tests arrive as arguments, computed by C.  They are
;;; NOT read here with symbol-value.  Reason (found at imp-4, evidence:
;;; a bootstrap SIGSEGV): probably_quit runs from the maybe_quit inline,
;;; and a symbol-value call from that C context re-enters the Guile VM
;;; twice (C -> Scheme -> C gsubr -> Scheme, through Fsymbol_value ->
;;; XSYMBOL), which is not re-entrant there.  C reads its own globals
;;; (Vquit_flag, Vinhibit_quit, pending_signals) and hands the two
;;; booleans in; Scheme still owns the decision.  See docs/kb.org ** M32.
;;;
;;; Branch 2 is identical to (emacs process-error)
;;; send-process-drain-signals!.  Reuse that one definition (brief.org
;;; decision D3) instead of adding a second copy.  It is resolved
;;; lazily, the way (emacs process-wait) resolves its cross-module
;;; targets, so this module does not eagerly import (emacs
;;; process-error).
;;;
;;; Conventions (identical to M9-M32): defelisp delayed references for
;;; every C DEFUN ((force %--foo)); #nil is elisp nil; no module-level
;;; mutable state.

(define-module (emacs eval-main)
  #:use-module (emacs elisp-ref)      ; %c, defelisp
  #:use-module (emacs-elisp runtime)
  #:declarative? #t
  #:export (probably-quit!))

;; The branch-1 callback: the eval.c DEFUN that runs the static
;; process_quit_flag.  quit () does not return.
(defelisp %--process-quit-flag! --process-quit-flag!)

;; The shared guarded drain lives in (emacs process-error).  Resolve it
;; lazily so this module does not eagerly import that one.
(define %send-process-drain-signals!
  (delay (module-ref (resolve-module '(emacs process-error))
                     'send-process-drain-signals!)))

(define (probably-quit! quit-p signals-p)
  "Port of probably_quit (src/eval.c pre-imp-4 body).  QUIT-P is the C
test `!NILP (Vquit_flag) && NILP (Vinhibit_quit)'; SIGNALS-P is the C
test `pending_signals'.  When QUIT-P, run the C process_quit_flag (which
may not return); else when SIGNALS-P, run the pending-signals drain.
Returns nil."
  (if quit-p
      ((force %--process-quit-flag!))
      (when signals-p
        ((force %send-process-drain-signals!))))
  #nil)
