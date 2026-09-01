;;; test-m22-recursive-edit.scm --- M22 imp-2 parity corpus.
;;;
;;; M22 imp-2 moves three C bodies in src/keyboard.c to Scheme:
;;;   * Frecursive_edit body  -> (emacs recursive-edit) recursive-edit
;;;   * recursive_edit_1 body -> (emacs recursive-edit) recursive-edit-1
;;;   * cmd_error_internal    -> (emacs command-loop) cmd-error-internal!
;;;
;;; Sourced by test/keyboard/test-m22-recursive-edit.el via eval-scheme.
;;; Accumulates PASS/FAIL entries into `test-results` for readback from
;;; elisp.  Same harness as test-m22-input-pending.scm.
;;;
;;; Scope: cmd-error-internal! is exercised in isolation (it needs no
;;; input).  The recursive-edit level/buffer after-thunk cannot be driven
;;; end-to-end here: command-loop-main reads interactive input that this
;;; batch harness cannot supply (read-key-sequence blocks even with
;;; /dev/null stdin), and Scheme commands registered via
;;; set-symbol-function! are not `commandp`, so a bound key cannot make
;;; the loop throw.  This mirrors the existing note in
;;; ertest-recursive-edit.el that the full recursive-edit flow is not
;;; exercised in batch.  So the level stepping is pinned at the unit
;;; level (the increment!/decrement! shims the Scheme body uses) and the
;;; Scheme/C wiring is checked.

(use-modules (emacs recursive-edit))
(use-modules (emacs command-loop))
(use-modules (emacs elisp-ref))
(use-modules (emacs-elisp runtime))

(define test-results '())
(define (report name status)
  (set! test-results (cons (list name status) test-results)))
(define (check name expected actual)
  (if (equal? expected actual)
      (report name 'PASS)
      (report name (list 'FAIL 'expected expected 'got actual))))

(define (%sym name) (symbol-function name))

(define (%nilp x)
  (or (null? x) (not x)))

;;; C-only recursive-edit state accessors (M22 imp-2 shims).
(define %command-loop-level         (delay (%sym '--command-loop-level)))
(define %command-loop-level-inc!    (delay (%sym '--command-loop-level-increment!)))
(define %command-loop-level-dec!    (delay (%sym '--command-loop-level-decrement!)))
(define %signal-quit-p              (delay (%sym '--signal-quit-p)))
(define %signaling-function         (delay (%sym '--signaling-function)))
(define %signaling-function-set!    (delay (%sym '--signaling-function-set!)))
(define %update-mode-lines-set!     (delay (%sym '--update-mode-lines-set!)))
(define %redisplaying-p-clear!      (delay (%sym '--redisplaying-p-clear!)))
(define %input-blocked-p            (delay (%sym '--input-blocked-p)))
(define %temporarily-switch-single-kboard!
  (delay (%sym '--temporarily-switch-to-single-kboard!)))
(define %recursive-edit-quit!       (delay (%sym '--recursive-edit-quit!)))

;;; ---------------------------------------------------------------------
;;; 1. cmd-error-internal!  (isolated — no input needed)
;;;
;;; 1a. quit-condition data: clears signaling-function and quit-flag, sets
;;; inhibit-quit; signaling-function is nil after.

(let* ((saved-sig ((force %signaling-function)))
       (saved-qf  (symbol-value 'quit-flag))
       (saved-inh (symbol-value 'inhibit-quit))
       (saved-cef (symbol-value 'command-error-function)))
  (dynamic-wind
    (lambda ()
      ((force %signaling-function-set!) 'foo)
      (set-symbol-value! 'quit-flag 'C-g)
      (set-symbol-value! 'inhibit-quit #nil)
      (set-symbol-value! 'command-error-function #nil))
    (lambda ()
      (cmd-error-internal! '(quit . nil) "")
      (check "m22/cmd-error/quit-clears-quit-flag" #nil
             (symbol-value 'quit-flag))
      (check "m22/cmd-error/quit-sets-inhibit-quit" #t
             (not (%nilp (symbol-value 'inhibit-quit))))
      (check "m22/cmd-error/quit-clears-signaling" #nil
             ((force %signaling-function))))
    (lambda ()
      ((force %signaling-function-set!) saved-sig)
      (set-symbol-value! 'quit-flag saved-qf)
      (set-symbol-value! 'inhibit-quit saved-inh)
      (set-symbol-value! 'command-error-function saved-cef))))

;;; 1b. non-quit data with command-error-function bound: calls it with
;;; (DATA CONTEXT SIGNALING-FUNCTION); signaling-function is nil after.

(let* ((saved-sig ((force %signaling-function)))
       (saved-qf  (symbol-value 'quit-flag))
       (saved-inh (symbol-value 'inhibit-quit))
       (saved-cef (symbol-value 'command-error-function))
       (calls '()))
  (dynamic-wind
    (lambda ()
      ((force %signaling-function-set!) 'my-signal)
      (set-symbol-value! 'quit-flag 'C-g)
      (set-symbol-value! 'inhibit-quit #nil)
      (set-symbol-value! 'command-error-function
                         (lambda (d c s) (set! calls (list d c s)))))
    (lambda ()
      (let ((data '(error . "boom")))
        (cmd-error-internal! data "ctx: ")
        (check "m22/cmd-error/calls-cef-with-3-args"
               (list data "ctx: " 'my-signal) calls)
        (check "m22/cmd-error/non-quit-clears-quit-flag" #nil
               (symbol-value 'quit-flag))
        (check "m22/cmd-error/non-quit-sets-inhibit-quit" #t
               (not (%nilp (symbol-value 'inhibit-quit))))
        (check "m22/cmd-error/non-quit-signaling-nil-after" #nil
               ((force %signaling-function)))))
    (lambda ()
      ((force %signaling-function-set!) saved-sig)
      (set-symbol-value! 'quit-flag saved-qf)
      (set-symbol-value! 'inhibit-quit saved-inh)
      (set-symbol-value! 'command-error-function saved-cef))))

;;; 1c. the shims cmd-error-internal! relies on exist and resolve.
(check "m22/cmd-error/signal-quit-p-shim-bound"
       #t (procedure? (%sym '--signal-quit-p)))
(check "m22/cmd-error/signaling-function-shim-bound"
       #t (procedure? (%sym '--signaling-function)))
(check "m22/cmd-error/signaling-function-set-shim-bound"
       #t (procedure? (%sym '--signaling-function-set!)))

;;; ---------------------------------------------------------------------
;;; 2. recursive-edit level stepping (unit level) + wiring.
;;;
;;; 2a. The Scheme body steps command_loop_level with the increment! /
;;; decrement! shims: a round trip returns the level to its start.  This
;;; is the mechanism recursive-edit's after-thunk relies on to unwind the
;;; increment done on entry.

(let ((saved ((force %command-loop-level))))
  ((force %command-loop-level-inc!))
  (check "m22/recursive-edit/level-increments" (+ saved 1)
         ((force %command-loop-level)))
  ((force %command-loop-level-dec!))
  (check "m22/recursive-edit/level-decrements-restore" saved
         ((force %command-loop-level))))

;;; 2b. the Scheme functions and new shims are wired (the C dispatchers
;;; resolve recursive-edit / recursive-edit-1 / cmd-error-internal! via
;;; scm_c_public_ref).
(check "m22/recursive-edit/recursive-edit-bound" #t
       (procedure? recursive-edit))
(check "m22/recursive-edit/recursive-edit-1-bound" #t
       (procedure? recursive-edit-1))
(check "m22/recursive-edit/cmd-error-internal-bound" #t
       (procedure? cmd-error-internal!))
(check "m22/recursive-edit/input-blocked-shim-bound" #t
       (procedure? (%sym '--input-blocked-p)))
(check "m22/recursive-edit/level-inc-shim-bound" #t
       (procedure? (%sym '--command-loop-level-increment!)))
(check "m22/recursive-edit/level-dec-shim-bound" #t
       (procedure? (%sym '--command-loop-level-decrement!)))
(check "m22/recursive-edit/update-mode-lines-shim-bound" #t
       (procedure? (%sym '--update-mode-lines-set!)))
(check "m22/recursive-edit/redisplaying-p-clear-shim-bound" #t
       (procedure? (%sym '--redisplaying-p-clear!)))
(check "m22/recursive-edit/tmp-switch-single-kboard-shim-bound" #t
       (procedure? (%sym '--temporarily-switch-to-single-kboard!)))
(check "m22/recursive-edit/recursive-edit-quit-shim-bound" #t
       (procedure? (%sym '--recursive-edit-quit!)))

;;; ---------------------------------------------------------------------
;;; 3. symbol-value-safe (the helper Finding 1 in cr.org fixes).
;;;
;;; Two reachable paths: a bound variable returns (value X); a void
;;; variable (reading it throws a void-variable elisp-condition) returns
;;; (void).  The rethrow else-branch (any *non*-void-variable
;;; elisp-condition on read) is not reachable through the six variables
;;; recursive-edit-1 actually saves, so it stays dead in practice, as
;;; cr.org notes.  The `(apply throw key args)' fix there is verified
;;; against the same pattern already used at loader.scm:761 and :838.

(define svs (@@ (emacs recursive-edit) symbol-value-safe))

;;; 3a. bound variable.
(set-symbol-value! 'm22-svs-probe 'hello)
(check "m22/svs/bound-returns-value"
       (list 'value 'hello) (svs 'm22-svs-probe))

;;; 3b. void variable.  A symbol never bound in the value slot reads as
;;; void; symbol-value-safe must report (void), not a raw unbound value.
(check "m22/svs/void-returns-void"
       (list 'void) (svs 'm22-svs-never-bound))
