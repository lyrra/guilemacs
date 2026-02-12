;; Tests for handler-bind-1 implementation
;; handler-bind-1 runs handlers in dynamic extent (before unwinding)
;; Unlike condition-case which unwinds first, then runs handler
;;
;; handler-bind-1 signature: (handler-bind-1 BODYFUN CONDITIONS1 HANDLER1 ...)
;; where CONDITIONS is a list of condition symbols
;; and HANDLER is a function taking (error-symbol . error-data)

;; =============================================================================
;; BASIC HANDLER-BIND-1 TESTS
;; =============================================================================

;; Test 1: Basic handler-bind-1 - handler is called
(deftest handler-bind-1-basic-called (t)
  (el-expr `(progn
    (setq hb-test1-called nil)
    (condition-case nil
        (handler-bind-1 (lambda () (signal 'error '(test)))
                        '(error)
                        (lambda (e) (setq hb-test1-called t)))
      (error nil))
    (princ hb-test1-called))))

;; Test 2: Handler receives error data
(deftest handler-bind-1-receives-error (t)
  (el-expr `(progn
    (setq hb-test2-data nil)
    (condition-case nil
        (handler-bind-1 (lambda () (signal 'error '(test-data)))
                        '(error)
                        (lambda (e) (setq hb-test2-data e)))
      (error nil))
    (princ (and (consp hb-test2-data)
                (eq (car hb-test2-data) 'error))))))

;; Test 3: Handler returning normally lets error propagate
(deftest handler-bind-1-propagates (t)
  (el-expr `(progn
    (setq hb-test3-handler-ran nil)
    (setq hb-test3-caught nil)
    (condition-case nil
        (handler-bind-1 (lambda () (signal 'error '(test)))
                        '(error)
                        (lambda (e) (setq hb-test3-handler-ran t)))
      (error (setq hb-test3-caught t)))
    (princ (and hb-test3-handler-ran hb-test3-caught)))))

;; Test 4: Handler can throw to outer catch
(deftest handler-bind-1-can-throw (handled)
  (el-expr `(progn
    (princ (catch 'done
             (handler-bind-1 (lambda () (signal 'error '(boom)))
                             '(error)
                             (lambda (e) (throw 'done 'handled))))))))

;; =============================================================================
;; CONDITION MATCHING TESTS
;; =============================================================================

;; Test 5: Specific condition matches
(deftest handler-bind-1-specific-match (t)
  (el-expr `(progn
    (setq hb-test5-called nil)
    (condition-case nil
        (handler-bind-1 (lambda () (signal 'void-function '(foo)))
                        '(void-function)
                        (lambda (e) (setq hb-test5-called t)))
      (error nil))
    (princ hb-test5-called))))

;; Test 6: General error handler catches derived errors
(deftest handler-bind-1-general-catches (t)
  (el-expr `(progn
    (setq hb-test6-caught nil)
    (condition-case nil
        (handler-bind-1 (lambda () (signal 'void-function '(bar)))
                        '(error)
                        (lambda (e) (setq hb-test6-caught t)))
      (error nil))
    (princ hb-test6-caught))))

;; Test 7: Non-matching handler not called
(deftest handler-bind-1-no-match (t)
  (el-expr `(progn
    (setq hb-test7-called nil)
    (condition-case nil
        (handler-bind-1 (lambda () (signal 'void-function '(baz)))
                        '(void-variable)
                        (lambda (e) (setq hb-test7-called t)))
      (error nil))
    (princ (not hb-test7-called)))))

;; =============================================================================
;; MULTIPLE HANDLERS TESTS
;; =============================================================================

;; Test 8: Multiple handlers - both can be called
(deftest handler-bind-1-multiple-handlers (2)
  (el-expr `(progn
    (setq hb-test8-count 0)
    (condition-case nil
        (handler-bind-1 (lambda () (signal 'error '(test)))
                        '(error)
                        (lambda (e) (setq hb-test8-count (+ hb-test8-count 1)))
                        '(error)
                        (lambda (e) (setq hb-test8-count (+ hb-test8-count 1))))
      (error nil))
    (princ hb-test8-count))))

;; =============================================================================
;; HANDLER-BIND-1 WITH UNWIND-PROTECT
;; =============================================================================

;; Test 9: unwind-protect cleanup runs after handler-bind-1 handler
(deftest handler-bind-1-unwind-protect (t)
  (el-expr `(progn
    (setq hb-test9-cleanup nil)
    (setq hb-test9-handler nil)
    (condition-case nil
        (handler-bind-1 (lambda ()
                          (unwind-protect
                              (signal 'error '(boom))
                            (setq hb-test9-cleanup t)))
                        '(error)
                        (lambda (e) (setq hb-test9-handler t)))
      (error nil))
    (princ (and hb-test9-handler hb-test9-cleanup)))))

;; Test 10: Handler runs before unwind (can see dynamic state)
(deftest handler-bind-1-sees-dynamic-state (bound-value)
  (el-expr `(progn
    (defvar hb-test10-dynvar 'original)
    (setq hb-test10-seen nil)
    (condition-case nil
        (let ((hb-test10-dynvar 'bound-value))
          (handler-bind-1 (lambda () (signal 'error '(test)))
                          '(error)
                          (lambda (e) (setq hb-test10-seen hb-test10-dynvar))))
      (error nil))
    (princ hb-test10-seen))))

;; =============================================================================
;; HANDLER-BIND-1 WITH CATCH/THROW
;; =============================================================================

;; Test 11: Handler can throw to escape
(deftest handler-bind-1-escape-via-throw (rescued)
  (el-expr `(progn
    (princ (catch 'rescue
             (handler-bind-1 (lambda () (signal 'error '(problem)))
                             '(error)
                             (lambda (e) (throw 'rescue 'rescued))))))))

;; Test 12: throw inside body works (no error)
(deftest handler-bind-1-body-throws (thrown)
  (el-expr `(progn
    (setq hb-test12-handler-ran nil)
    (princ (catch 'exit
             (handler-bind-1 (lambda () (throw 'exit 'thrown))
                             '(error)
                             (lambda (e) (setq hb-test12-handler-ran t))))))))

;; =============================================================================
;; EDGE CASES
;; =============================================================================

;; Test 13: No handlers - just runs body
(deftest handler-bind-1-no-handlers (42)
  (el-expr `(progn
    (princ (handler-bind-1 (lambda () 42))))))

;; Test 14: Handler-bind-1 with no error - returns body value
(deftest handler-bind-1-no-error (success)
  (el-expr `(progn
    (princ (handler-bind-1 (lambda () 'success)
                           '(error)
                           (lambda (e) nil))))))

;; Test 15: Nested handler-bind-1 and condition-case
(deftest handler-bind-1-with-condition-case (t)
  (el-expr `(progn
    (setq hb-test15-handler-ran nil)
    (setq hb-test15-result
          (condition-case err
              (handler-bind-1 (lambda () (signal 'error '(test)))
                              '(error)
                              (lambda (e) (setq hb-test15-handler-ran t)))
            (error 'caught)))
    (princ (and hb-test15-handler-ran
                (eq hb-test15-result 'caught))))))
