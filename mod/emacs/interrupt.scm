;;; interrupt.scm --- M26 imp-1: suspend-emacs -> (emacs interrupt)
;;;
;;; Ports the body of C `Fsuspend_emacs' (src/keyboard.c) out of C and
;;; into Scheme.  The C DEFUN stays as a one-line thin dispatcher into
;;; this module's `suspend-emacs'.  See brief.org M26 imp-1.
;;;
;;; The suspend *policy* moves here: the multi-tty guard, the
;;; CHECK_STRING-style stuffstring check, the suspend-hook /
;;; suspend-resume-hook calls, the size-change recheck after resume,
;;; and the cannot-suspend branch decision.  The terminal mechanics it
;;; drives stay in C behind the four M26 shims (--multiple-tty-frames?,
;;; --tty-size, --sys-subshell, --change-frame-size) plus the pre-M26
;;; --reset-all-sys-modes / --init-all-sys-modes and --sys-suspend
;;; shims.  `stuff-buffered-input' (M22 imp-3) is reused from
;;; (emacs kbd-buffer), not re-ported.
;;;
;;; imp-2 (quit-throw-to-read-char) and imp-3 (handle-interrupt) land
;;; in this same module in later commits; this commit only adds
;;; `suspend-emacs'.
;;;
;;; Conventions (identical to M9-M24, cf. mod/emacs/input-poll.scm):
;;; #nil is elisp nil; %nilp is the local elisp-nil predicate (defined
;;; per-module, not exported from (emacs-elisp runtime)).  Every shim
;;; is called through (%c '--name) on each call — NOT a defelisp delay —
;;; so the test suite can fset-stub them (cr.org Finding 2), the same
;;; way input-poll.scm resolves --atimer-poll-restart!.  The plain
;;; `cannot-suspend' variable is read with symbol-value, which has no
;;; delay form.
;;;
;;; NOTE (close-out): a real end-to-end suspend/resume cannot be
;;; automated in the test suite — sys_suspend would stop the runner and
;;; sys_subshell would fork it (see the --sys-suspend doc).  Tests
;;; exercise only the parts that run before those calls; see
;;; test/keyboard/test-m26-imp1-suspend-emacs.scm.

(define-module (emacs interrupt)
  #:use-module (emacs elisp-ref)      ; %c, defelisp
  #:use-module (emacs-elisp runtime)
  #:declarative? #t
  #:export (suspend-emacs))

(define (%nilp x) (eq? x #nil))

;; Delayed reference to (emacs kbd-buffer) `stuff-buffered-input' (M22
;; imp-3), reused here, not re-ported.  Deliberately NOT an eager
;; #:use-module: interrupt is loaded by the prelude (prelude/load.scm)
;; BEFORE syms_of_keyboard registers the C DEFUNs, and (emacs kbd-buffer)
;; pulls in (emacs lispy-event), whose top-level forms force C DEFUNs at
;; load time (compiling kbd-buffer too early resolves them to #nil).
;; The delay defers the module load to the first suspend — at runtime,
;; after syms_of_keyboard.  Same pattern as read-char.scm's
;; %read-decoded-event-from-main-queue (FIX-20260821-guilemacs).
(define %stuff-buffered-input
  (delay (module-ref (resolve-module '(emacs kbd-buffer) #:ensure #t)
                     'stuff-buffered-input)))

(define (suspend-emacs stuffstring)
  "Port of C Fsuspend_emacs (src/keyboard.c): stop Emacs and return to
the superior process, or run a subshell when `cannot-suspend' is
non-nil.  STUFFSTRING, when non-nil, is stuffed as terminal input for
the parent after suspension.  Runs `suspend-hook' before suspending
and `suspend-resume-hook' after resuming.  Mirrors the C body line for
line; see brief.org M26 imp-1."
  ;; C: if (tty_list && tty_list->next)
  ;;       error ("There are other tty frames open; ...");
  (when (not (%nilp ((%c '--multiple-tty-frames?))))
    ((%c 'error)
     "There are other tty frames open; close them before suspending Emacs"))
  ;; C: if (!NILP (stuffstring)) CHECK_STRING (stuffstring);
  (unless (%nilp stuffstring)
    (unless ((%c 'stringp) stuffstring)
      ((%c 'signal) 'wrong-type-argument (list 'stringp stuffstring))))
  ;; C: run_hook (Qsuspend_hook);  -- plain run-hooks (an error here
  ;; must propagate, not be swallowed; the C original called run_hook).
  ((%c 'run-hooks) 'suspend-hook)
  ;; C: get_tty_size (...); old_width/old_height snapshot.
  (let* ((old-size ((%c '--tty-size)))
         (old-width (car old-size))
         (old-height (cdr old-size)))
    ;; C: reset_all_sys_modes ();
    ((%c '--reset-all-sys-modes))
    ;; C: record_unwind_protect_void (init_all_sys_modes);
    ;; Guile dynamic-wind's after-thunk runs on both normal exit and
    ;; non-local exit (error unwind), same as record_unwind_protect_void.
    (dynamic-wind
      (lambda () #t)
      (lambda ()
        ;; C: stuff_buffered_input (stuffstring);  (M22 imp-3, reused)
        ((force %stuff-buffered-input) stuffstring)
        ;; C: if (cannot_suspend) sys_subshell (); else sys_suspend ();
        (if (not (%nilp (symbol-value 'cannot-suspend)))
            ((%c '--sys-subshell))
            ((%c '--sys-suspend))))
      ;; after-thunk == dynwind_end running init_all_sys_modes.
      (lambda () ((%c '--init-all-sys-modes))))
    ;; C: post-resume size check; resize the selected frame if it moved.
    (let* ((size ((%c '--tty-size)))
           (width (car size))
           (height (cdr size)))
      (when (or (not (= width old-width))
                (not (= height old-height)))
        ((%c '--change-frame-size) width height))))
  ;; C: run_hook (Qsuspend_resume_hook);
  ((%c 'run-hooks) 'suspend-resume-hook)
  #nil)
