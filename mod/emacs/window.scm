;;; window.scm --- M34 imp-3: the window.c safe_run_hooks caller
;;;               ((emacs window))
;;;
;;; Moves the *decision* logic of the live src/window.c call site of the
;;; safe_run_hooks stub into Scheme.  The *mechanism* stays C: the
;;; run_window_change_functions frame walk, the writes of the local
;;; bool run_window_state_change_hook, and the safe_run_hooks definition.
;;; See brief.org 3.
;;;
;;; One exported procedure:
;;;
;;;   window-maybe-run-state-change-hook! -- the window-state-change-hook
;;;                                          run in run_window_change_functions.
;;;
;;; Conventions (identical to M9-M34, cf. mod/emacs/frame.scm):
;;; cross-module targets are resolved lazily with delay + module-ref; #nil
;;; is elisp nil; no defelisp (the target is a Scheme procedure); no
;;; module-level mutable state.

(define-module (emacs window)
  #:declarative? #t
  #:export (window-maybe-run-state-change-hook!))

;; (emacs command-loop) holds the safe_run_hooks port.  Resolve it lazily,
;; so the module does not eagerly import (emacs command-loop).  See
;; brief.org 3.
(define %safe-run-hooks!
  (delay (module-ref (resolve-module '(emacs command-loop))
                     'safe-run-hooks!)))

;;; --- Helpers -------------------------------------------------------
;;; Each module carries its own copy.  See mod/emacs/frame.scm:48.
;;; Only %nilp is needed: RUN-HOOK is the elisp boolean from C, so the
;;; wider truthy? test has no caller.
(define (%nilp x) (eq? x #nil))

;;; --- window-maybe-run-state-change-hook! ---------------------------
;;; Port of the site call in run_window_change_functions (src/window.c):
;;;   if (run_window_state_change_hook && !NILP (Vwindow_state_change_hook))
;;;     safe_run_hooks (Qwindow_state_change_hook);
;;; RUN-HOOK is the local C bool, passed as Qt / Qnil.  When it is true
;;; (non-nil), call (emacs command-loop) safe-run-hooks! on the
;;; window-state-change-hook symbol; else do nothing.  Return nothing.
;;;
;;; The !NILP (Vwindow_state_change_hook) guard needs no Scheme re-test:
;;; safe-run-hooks! reads the hook variable and does nothing when it is
;;; nil (mod/emacs/command-loop.scm:1088).  See brief.org imp-0 notes item 4.
(define (window-maybe-run-state-change-hook! run-hook)
  (unless (%nilp run-hook)
    ((force %safe-run-hooks!) 'window-state-change-hook)))
