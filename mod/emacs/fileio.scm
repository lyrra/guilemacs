;;; fileio.scm --- M34 imp-3: the fileio.c safe_run_hooks caller
;;;               ((emacs fileio))
;;;
;;; Moves the *decision* logic of the live src/fileio.c call site of the
;;; safe_run_hooks stub into Scheme.  The *mechanism* stays C: the
;;; do_auto_save message push, the quit-flag save and restore, and the
;;; auto_save_unwind.  See brief.org 4.
;;;
;;; One exported procedure:
;;;
;;;   fileio-run-auto-save-hook! -- the auto-save-hook run in do_auto_save.
;;;
;;; Conventions (identical to M9-M34, cf. mod/emacs/frame.scm):
;;; cross-module targets are resolved lazily with delay + module-ref; #nil
;;; is elisp nil; no defelisp (the target is a Scheme procedure); no
;;; module-level mutable state.

(define-module (emacs fileio)
  #:declarative? #t
  #:export (fileio-run-auto-save-hook!))

;; (emacs command-loop) holds the safe_run_hooks port.  Resolve it lazily,
;; so the module does not eagerly import (emacs command-loop).  See
;; brief.org 4.
(define %safe-run-hooks!
  (delay (module-ref (resolve-module '(emacs command-loop))
                     'safe-run-hooks!)))

;;; --- fileio-run-auto-save-hook! ------------------------------------
;;; Port of the site call in do_auto_save (src/fileio.c):
;;;   hook = Qauto_save_hook;
;;;   safe_run_hooks (hook);
;;; It takes no argument.  Call (emacs command-loop) safe-run-hooks! on the
;;; auto-save-hook symbol.  Return nothing.  See brief.org 4.
(define (fileio-run-auto-save-hook!)
  ((force %safe-run-hooks!) 'auto-save-hook))
