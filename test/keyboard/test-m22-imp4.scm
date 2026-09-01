;;; test-m22-imp4.scm --- M22 imp-4 parity corpus.
;;;
;;; imp-4 ports the C safe_run_hooks family to Scheme:
;;;   * safe_run_hooks_1 / safe_run_hook_funcall / safe_run_hooks_error
;;;     -> private safe-run-hook-funcall (emacs command-loop)
;;;   * run_hook_with_args (eval.c helper)
;;;     -> private run-hook-with-args-1 (emacs command-loop)
;;;     (reimplementation — run_hook_with_args is not static and stays
;;;     in C for six other call sites)
;;;   * safe_run_hooks   -> safe-run-hooks! (public)
;;;   * safe_run_hooks_2 -> safe-run-hooks-2! (public)
;;;   * safe_run_hooks_maybe_narrowed
;;;     -> safe-run-hooks-maybe-narrowed! (public)
;;;
;;; The C DEFUNs --safe-run-hooks / --safe-run-hooks-maybe-narrowed-
;;; selected were deleted; safe_run_hooks and safe_run_hooks_2 are thin
;;; dispatchers into the Scheme.  These tests exercise the Scheme
;;; procedures directly and through the (repointed) C entry points.
;;;
;;; Sourced by test/keyboard/test-m22-imp4.el via eval-scheme.
;;; Accumulates PASS/FAIL entries into `test-results` for readback from
;;; elisp.  Same harness as test-m22-imp3.scm.

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
(define (try-check name expected thunk)
  (catch #t
    (lambda () (check name expected (thunk)))
    (lambda (key . args)
      (report name (list 'ERROR key args)))))
(define (%sym name) (symbol-function name))

;;; ---------------------------------------------------------------------
;;; 1. New C shims resolve.
;;;
(define new-shims
  '(--get-large-narrowing-begv --get-large-narrowing-zv
    --buffer-beg --buffer-end))
(for-each (lambda (n)
            (check (string-append "m22/imp4/shims/" (symbol->string n))
                   #t (procedure? (%sym n))))
          new-shims)

;;; ---------------------------------------------------------------------
;;; 2. Hook bookkeeping helpers.
;;;
;;; A Scheme-side run log.  Each hook function calls (mark! TAG), which
;;; conses onto `*ran*`, so the log ends up reversed relative to run
;;; order.
(define *ran* '())
(define (reset-ran!) (set! *ran* '()))
(define (mark! tag) (set! *ran* (cons tag *ran*)))

;; Hook functions, defined as elisp functions so `functionp' is true
;; and `funcall' dispatches through the symbol.
(set-symbol-function! 'imp4-fn1 (lambda () (mark! 'one)))
(set-symbol-function! 'imp4-fn2 (lambda () (mark! 'two)))
(set-symbol-function! 'imp4-fn3 (lambda () (mark! 'three)))
(set-symbol-function! 'imp4-fn4 (lambda () (mark! 'four)))
(set-symbol-function! 'imp4-g1  (lambda () (mark! 'g1)))
(set-symbol-function! 'imp4-args (lambda (a b) (mark! (list a b))))
;; Signal an elisp error (thrown to 'elisp-condition), so safe-run-hook-
;; funcall's trampoline catches it — the same path a real elisp hook
;; function takes.
(set-symbol-function! 'imp4-err (lambda () ((%c 'error) "boom")))

(define (hook-fbound? n)
  (not (%nilp ((%c 'fboundp) n))))

;;; ---------------------------------------------------------------------
;;; 3. safe-run-hooks! — 0, 1, and 2+ functions.
;;;
;; 0 functions: an empty hook must run nothing and not crash.
((%c 'set-default) 'imp4-hook-empty #nil)
(reset-ran!)
(try-check "m22/imp4/run/empty/returns" #nil (lambda () (safe-run-hooks! 'imp4-hook-empty)))
(check "m22/imp4/run/empty/ran-nothing" '() *ran*)

;; 1 function.
((%c 'set-default) 'imp4-hook-one '(imp4-fn1))
(reset-ran!)
(safe-run-hooks! 'imp4-hook-one)
(check "m22/imp4/run/one/ran" '(one) *ran*)

;; 2+ functions, in order.
((%c 'set-default) 'imp4-hook-many '(imp4-fn1 imp4-fn2 imp4-fn3))
(reset-ran!)
(safe-run-hooks! 'imp4-hook-many)
(check "m22/imp4/run/many/ran-order" '(three two one) *ran*)

;; A single-function hook value (not a list) is treated as one function.
((%c 'set-default) 'imp4-hook-single 'imp4-fn1)
(reset-ran!)
(safe-run-hooks! 'imp4-hook-single)
(check "m22/imp4/run/single-symbol/ran" '(one) *ran*)

;;; ---------------------------------------------------------------------
;;; 4. Local value with a `t' element splices in the default value.
;;;
;;; Global (default) hook holds g1; the buffer-local value is
;;; (imp4-fn1 t imp4-fn2).  `t' must splice in g1 between fn1 and fn2.
((%c 'set-default) 'imp4-hook-splice '(imp4-g1))
((%c 'make-local-variable) 'imp4-hook-splice)
(set-symbol-value! 'imp4-hook-splice '(imp4-fn1 t imp4-fn2))
(reset-ran!)
(safe-run-hooks! 'imp4-hook-splice)
(check "m22/imp4/run/splice/ran-order" '(two g1 one) *ran*)

;;; ---------------------------------------------------------------------
;;; 5. Error recovery (docs/m22-plan.org Risk 3).
;;;
;;; A hook function that signals must be reported and removed from the
;;; hook, and the remaining functions must still run.
((%c 'set-default) 'imp4-hook-err '(imp4-fn1 imp4-err imp4-fn2))
(reset-ran!)
(safe-run-hooks! 'imp4-hook-err)
;; fn1 runs, imp4-err errors and is removed, fn2 still runs.
(check "m22/imp4/error/others-still-run" '(two one) *ran*)
;; The offending function is gone from the local (here default) value.
(check "m22/imp4/error/removed-from-local"
       '(imp4-fn1 imp4-fn2)
       (symbol-value 'imp4-hook-err))

;; A function that appears more than once is removed from every position.
((%c 'set-default) 'imp4-hook-dup '(imp4-fn1 imp4-err imp4-fn2 imp4-err))
(reset-ran!)
(safe-run-hooks! 'imp4-hook-dup)
(check "m22/imp4/error/all-occurrences-removed"
       '(imp4-fn1 imp4-fn2)
       (symbol-value 'imp4-hook-dup))

;;; ---------------------------------------------------------------------
;;; 6. Removal from the default list (second branch of the C search).
;;;
;;; Buffer-local value (imp4-fn1 t); the default holds the erroring
;;; function.  The t splice runs the default, imp4-err errors, and is
;;; removed from the *default* value (not the local value).
((%c 'set-default) 'imp4-hook-dflt '(imp4-err imp4-fn2))
((%c 'make-local-variable) 'imp4-hook-dflt)
(set-symbol-value! 'imp4-hook-dflt '(imp4-fn1 t))
(reset-ran!)
(safe-run-hooks! 'imp4-hook-dflt)
(check "m22/imp4/error/local-untouched"
       '(imp4-fn1 t)
       (symbol-value 'imp4-hook-dflt))
(check "m22/imp4/error/removed-from-default"
       '(imp4-fn2)
       ((%c 'default-value) 'imp4-hook-dflt))

;; The t-splice where the default is a single function (not a list):
;; it is run once via the single-funcall branch.
((%c 'set-default) 'imp4-hook-gg 'imp4-g1)
((%c 'make-local-variable) 'imp4-hook-gg)
(set-symbol-value! 'imp4-hook-gg '(imp4-fn1 t))
(reset-ran!)
(safe-run-hooks! 'imp4-hook-gg)
(check "m22/imp4/run/splice-single-fn-default/ran" '(g1 one) *ran*)

;;; ---------------------------------------------------------------------
;;; 7. safe-run-hooks-2! — two extra args reach the hook function.
;;;
((%c 'set-default) 'imp4-hook-args '(imp4-args))
(reset-ran!)
(safe-run-hooks-2! 'imp4-hook-args 'x 'y)
(check "m22/imp4/run2/args" '((x y)) *ran*)

;;; ---------------------------------------------------------------------
;;; 8. safe-run-hooks-maybe-narrowed! — smoke test with
;;; long-line-optimizations-p nil (the common batch case): no crash,
;;; hook still runs, and the buffer is not narrowed.
;;;
((%c 'set-default) 'imp4-hook-mn '(imp4-fn1))
((%c 'erase-buffer))
((%c 'insert) "abcdefghij")
(reset-ran!)
(safe-run-hooks-maybe-narrowed! 'imp4-hook-mn)
(check "m22/imp4/maybe-narrowed/ran" '(one) *ran*)
(check "m22/imp4/maybe-narrowed/not-narrowed"
       1 ((%c 'point-min)))

;;; ---------------------------------------------------------------------
;;; 9. safe-run-hooks-maybe-narrowed! — narrowing guard (cr.org
;;;    Finding 2).  The guard must compare the computed region against
;;;    the buffer's *absolute* bounds (BEG/Z), not the current narrowed
;;;    bounds (BEGV/ZV).  In batch the C long_line_optimizations_p flag
;;;    is never set, so force it on by rebinding the function slot, and
;;;    set a large region size.
;;;
(define llop-saved (%sym 'long-line-optimizations-p))
(define region-size-saved (symbol-value 'long-line-optimizations-region-size))
(set-symbol-function! 'long-line-optimizations-p (lambda () #t))
((%c 'set) 'long-line-optimizations-region-size 10000)
;; This section switches current-buffer to scratch buffers.  Save the
;; original buffer so it can be restored: the batch harness runs the
;; test files in randomized load order, and a left-behind current-buffer
;; (diverged from the selected window's buffer) breaks other files'
;; adjust-point display tests (e.g. imp3).
(define imp4-orig-buffer ((%c 'current-buffer)))

;; --buffer-beg is BEG (always 1); --buffer-end is Z (absolute end,
;; independent of narrowing).
(check "m22/imp4/shims/buffer-beg" 1 ((%c '--buffer-beg)))
((%c 'set-buffer) ((%c 'get-buffer-create) "imp4-mn"))
((%c 'erase-buffer))
((%c 'insert) "0123456789abcdefghij")   ;; 20 chars, so Z = 21
(check "m22/imp4/shims/buffer-end" 21 ((%c '--buffer-end)))

;; 9a. Buffer already narrowed to [5,15].  With a large region-size the
;; computed begv/zv clamp to the current bounds BEGV/ZV exactly
;; (5,15), so begv == point-min and zv == point-max.  C still narrows
;; (begv != BEG), which forces point-restore; the fixed guard must too.
((%c 'narrow-to-region) 5 15)            ;; BEGV=5, ZV=15
((%c 'goto-char) 10)
(set-symbol-function! 'imp4-mn-move
                      (lambda () (mark! 'mn) ((%c 'goto-char) 12)))
((%c 'set-default) 'imp4-hook-mn-move '(imp4-mn-move))
(reset-ran!)
(safe-run-hooks-maybe-narrowed! 'imp4-hook-mn-move)
(check "m22/imp4/maybe-narrowed/pre-narrowed/ran" '(mn) *ran*)
(check "m22/imp4/maybe-narrowed/pre-narrowed/point-restored"
       10 ((%c 'point)))

;; 9b. Un-narrowed buffer, point far from both edges: the computed region
;; covers the whole buffer (begv == BEG, zv == Z), so the guard must not
;; narrow, and point stays where the hook left it.
((%c 'set-buffer) ((%c 'get-buffer-create) "imp4-mn2"))
((%c 'erase-buffer))
((%c 'insert) "0123456789abcdefghij")   ;; Z = 21
((%c 'goto-char) 10)
(set-symbol-function! 'imp4-mn-move2
                      (lambda () (mark! 'mn2) ((%c 'goto-char) 12)))
((%c 'set-default) 'imp4-hook-mn-move2 '(imp4-mn-move2))
(reset-ran!)
(safe-run-hooks-maybe-narrowed! 'imp4-hook-mn-move2)
(check "m22/imp4/maybe-narrowed/full-region/ran" '(mn2) *ran*)
(check "m22/imp4/maybe-narrowed/full-region/point-left"
       12 ((%c 'point)))

;; Restore the long-line overrides and the original current buffer.
((%c 'set-buffer) imp4-orig-buffer)
((%c 'set) 'long-line-optimizations-region-size region-size-saved)
(set-symbol-function! 'long-line-optimizations-p llop-saved)
