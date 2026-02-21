;;; test-throw-propagation.el --- Test catch/throw/condition-case/unwind-protect through eval

;; Tests that catch, throw, condition-case, and unwind-protect work correctly
;; when used through eval. In guilemacs, these forms expand to Guile primitives.
;; This test suite verifies the eval interaction works correctly.

(test-begin "eval-control-flow")

;;; ============================================
;;; Section 1: Direct usage (baseline tests)
;;; ============================================

;; Test 1: Direct throw/catch
(test-equal "direct-catch-throw"
            'caught
            (catch 'test (throw 'test 'caught)))

;; Test 2: Nested catch with different tags
(test-equal "nested-catch-different-tags"
            'outer-caught
            (catch 'outer
              (catch 'inner
                (throw 'outer 'outer-caught))))

;; Test 3: throw through funcall
(test-equal "throw-through-funcall"
            'caught
            (catch 'test
              (funcall (lambda () (throw 'test 'caught)))))

;; Test 4: Direct condition-case no error
(test-equal "direct-condition-case-no-error"
            'success
            (condition-case err
                'success
              (error 'failed)))

;; Test 5: Direct condition-case catches error
(test-equal "direct-condition-case-catches"
            'caught
            (condition-case err
                (signal 'error '("test"))
              (error 'caught)))

;; Test 6: Direct unwind-protect runs cleanup
(let ((cleanup-ran nil))
  (unwind-protect
      'body-result
    (setq cleanup-ran t))
  (test-assert "direct-unwind-protect-cleanup"
               cleanup-ran))

;; Test 7: Direct unwind-protect returns body value
(test-equal "direct-unwind-protect-value"
            'body-result
            (unwind-protect
                'body-result
              nil))

;;; ============================================
;;; Section 2: Forms completely inside eval
;;; ============================================

;; Test 8: catch/throw inside eval (should work)
(test-equal "catch-throw-inside-eval"
            'caught
            (eval '(catch 'test (throw 'test 'caught))))

;; Test 9: condition-case inside eval (should work)
(test-equal "condition-case-inside-eval"
            'caught
            (eval '(condition-case err
                       (signal 'error '("test"))
                     (error 'caught))))

;; Test 10: unwind-protect inside eval (should work)
(test-equal "unwind-protect-inside-eval"
            'body-result
            (eval '(unwind-protect
                       'body-result
                     nil)))

;; Test 11: nested let with unwind-protect inside eval
(test-equal "let-unwind-protect-inside-eval"
            3
            (eval '(let ((x 1))
                     (unwind-protect
                         (+ x 2)
                       nil))))

;;; ============================================
;;; Section 3: Throw propagation through eval
;;; ============================================

;; Test 12: throw inside eval propagates to outer catch
(test-equal "throw-inside-eval-propagates"
            'caught
            (condition-case err
                (catch 'test
                  (eval '(throw 'test 'caught)))
              (error 'error-not-caught)))

;; Test 13: throw inside eval with nested catch
(test-equal "throw-inside-eval-nested"
            'caught
            (condition-case err
                (catch 'test
                  (catch 'other
                    (eval '(throw 'test 'caught))))
              (error 'error-not-caught)))

;; Test 14: throw from lambda through eval
;; With lexical binding, we use a dynamically-scoped variable for the thrower
(defvar test-thrower nil)
(setq test-thrower (lambda () (throw 'test 'caught)))
(test-equal "throw-lambda-through-eval"
            'caught
            (condition-case err
                (catch 'test
                  (eval '(funcall test-thrower)))
              (error 'error-not-caught)))

;;; ============================================
;;; Section 4: Signal propagation through eval
;;; ============================================

;; Test 15: signal inside eval propagates to outer condition-case
(test-equal "signal-inside-eval-propagates"
            'caught
            (condition-case err
                (eval '(signal 'error '("test")))
              (error 'caught)))

;; Test 16: signal inside nested eval
(test-equal "signal-nested-eval"
            'caught
            (condition-case err
                (condition-case inner-err
                    (eval '(signal 'error '("test")))
                  (wrong-type-argument 'wrong-type))
              (error 'caught)))

;;; ============================================
;;; Section 5: Unwind-protect through eval
;;; ============================================

;; Test 17: unwind-protect cleanup runs on normal exit through eval
;; With lexical binding, we use a dynamically-scoped variable
(defvar test-cleanup-ran-1 nil)
(setq test-cleanup-ran-1 nil)
(eval '(unwind-protect
           'body
         (setq test-cleanup-ran-1 t)))
(test-assert "unwind-cleanup-normal-exit"
             test-cleanup-ran-1)

;; Test 18: unwind-protect cleanup runs on error through eval
;; With lexical binding, we use a dynamically-scoped variable
(defvar test-cleanup-ran-2 nil)
(setq test-cleanup-ran-2 nil)
(condition-case err
    (eval '(unwind-protect
               (signal 'error '("test"))
             (setq test-cleanup-ran-2 t)))
  (error nil))
(test-assert "unwind-cleanup-on-error"
             test-cleanup-ran-2)

;;; ============================================
;;; Section 6: Quit signal hierarchy
;;; ============================================

;; Note: quit-to-toplevel behavior can't be tested in batch mode
;; (no command loop). For interactive testing, see test-quit-interactive.el.
;;
;; The command loop must use Qt (all conditions), not Qerror, because
;; quit is not a subtype of error. Fixed in keyboard.c:
;;   internal_condition_case(..., Qt, cmd_error)
;; instead of Qerror.

;; Test 19: quit is not under error hierarchy
(test-assert "quit-not-subtype-of-error"
             (not (memq 'error (get 'quit 'error-conditions))))

;; Test 20: error IS under error hierarchy (sanity check)
(test-assert "error-is-under-error"
             (memq 'error (get 'error 'error-conditions)))

;; Test 21: quit can be caught with condition-case when explicitly listed
(test-equal "quit-caught-when-explicit"
            'caught
            (condition-case err
                (signal 'quit '("test"))
              (quit 'caught)))

(test-end)
