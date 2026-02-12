;; Tests for condition-case, catch/throw, and error signaling
;; These test the Guile-based condition system implementation

;; =============================================================================
;; BASIC CONDITION-CASE TESTS
;; =============================================================================

;; Test 1: Basic error catching
(deftest condition-case-basic (t)
  (el-expr `(progn
    (princ (condition-case err
               (error "test error")
             (error t))))))

;; Test 2: Specific condition type matching
(deftest condition-case-void-function (t)
  (el-expr `(progn
    (condition-case err
      (signal 'void-function nil)
      (void-function nil)
      (error (princ nil)))
    (princ t))))

;; Test 3: Error data is captured correctly
(deftest condition-case-error-data (t)
  (el-expr `(progn
    (princ (condition-case err
               (error "\"message %d\"" 42)
             (error (and (eq (car err) 'error)
                         (consp (cdr err)))))))))

;; Test 4: No error - returns body value
(deftest condition-case-no-error (success)
  (el-expr `(progn
    (princ (condition-case nil
               'success
             (error 'failed))))))

;; Test 5: Multiple handler clauses
(deftest condition-case-multiple-handlers (void-function)
  (el-expr `(progn
    (princ (condition-case nil
               (signal 'void-function '(foo))
             (void-variable 'void-variable)
             (void-function 'void-function)
             (error 'error))))))

;; =============================================================================
;; NESTED CONDITION-CASE TESTS
;; =============================================================================

;; Test 6: Nested condition-case - inner catches
(deftest condition-case-nested-inner (inner)
  (el-expr `(progn
    (princ (condition-case nil
               (condition-case nil
                   (error "inner error")
                 (error 'inner))
             (error 'outer))))))

;; Test 7: Nested condition-case - inner re-signals to outer
(deftest condition-case-nested-rethrow (outer)
  (el-expr `(progn
    (princ (condition-case nil
               (condition-case err
                   (error "propagate")
                 (error (signal (car err) (cdr err))))
             (error 'outer))))))

;; Test 8: Deeply nested condition-case
(deftest condition-case-deep-nest (5)
  (el-expr `(progn
    (princ (condition-case nil
               (condition-case nil
                   (condition-case nil
                       (condition-case nil
                           (condition-case nil
                               (error "deep")
                             (error 5))
                           (error 4))
                       (error 3))
                   (error 2))
             (error 1))))))

;; =============================================================================
;; CATCH/THROW TESTS
;; =============================================================================

;; Test 9: Basic catch/throw
(deftest catch-throw-basic (42)
  (el-expr `(progn
    (princ (catch 'done
             (throw 'done 42)
             'not-reached)))))

;; Test 10: Nested catch - inner catch catches, then outer body continues
(deftest catch-throw-nested-inner (outer-body)
  (el-expr `(progn
    (princ (catch 'outer
             (catch 'inner
               (throw 'inner 'inner)
               'not-reached)
             'outer-body)))))

;; Test 11: Nested catch - throws past inner to outer
(deftest catch-throw-nested-outer (outer)
  (el-expr `(progn
    (princ (catch 'outer
             (catch 'inner
               (throw 'outer 'outer)
               'not-reached)
             'outer-body)))))

;; Test 12: Catch with no throw - returns body value
(deftest catch-no-throw (body-value)
  (el-expr `(progn
    (princ (catch 'tag 'body-value)))))

;; Test 13: Same tag catches - inner catches, outer body continues
(deftest catch-same-tag (outer)
  (el-expr `(progn
    (princ (catch 'tag
             (catch 'tag
               (throw 'tag 'inner))
             'outer)))))

;; =============================================================================
;; UNWIND-PROTECT TESTS
;; =============================================================================

;; Test 14: unwind-protect cleanup runs on error
(deftest unwind-protect-on-error (t)
  (el-expr `(progn
    (setq cleanup-ran nil)
    (condition-case nil
        (unwind-protect
            (error "boom")
          (setq cleanup-ran t))
      (error nil))
    (princ cleanup-ran))))

;; Test 15: unwind-protect cleanup runs on throw
(deftest unwind-protect-on-throw (t)
  (el-expr `(progn
    (setq cleanup-ran nil)
    (catch 'exit
      (unwind-protect
          (throw 'exit 'done)
        (setq cleanup-ran t)))
    (princ cleanup-ran))))

;; Test 16: unwind-protect cleanup runs on normal exit
(deftest unwind-protect-normal-exit (t)
  (el-expr `(progn
    (setq cleanup-ran nil)
    (unwind-protect
        'normal
      (setq cleanup-ran t))
    (princ cleanup-ran))))

;; Test 17: unwind-protect returns body value on normal exit
(deftest unwind-protect-returns-value (body-value)
  (el-expr `(progn
    (princ (unwind-protect
               'body-value
             nil)))))

;; Test 18: Nested unwind-protect - all cleanups run
(deftest unwind-protect-nested (t)
  (el-expr `(progn
    (setq cleanup1 nil)
    (setq cleanup2 nil)
    (condition-case nil
        (unwind-protect
            (unwind-protect
                (error "boom")
              (setq cleanup1 t))
          (setq cleanup2 t))
      (error nil))
    (princ (and cleanup1 cleanup2)))))

;; =============================================================================
;; SIGNAL TESTS
;; =============================================================================

;; Test 19: signal with error-conditions property
(deftest signal-error-conditions (t)
  (el-expr `(progn
    (princ (condition-case nil
               (signal 'void-function '(test-fn))
             ;; void-function inherits from error
             (error t))))))

;; Test 20: signal arith-error
(deftest signal-arith-error (t)
  (el-expr `(progn
    (princ (condition-case nil
               (signal 'arith-error nil)
             (arith-error t)
             (error nil))))))

;; =============================================================================
;; ERROR FUNCTION TESTS
;; =============================================================================

;; Test 21: error with format string
(deftest error-format-string (t)
  (el-expr `(progn
    (princ (condition-case err
               (error "\"Value is %d\"" 42)
             (error (eq (car err) 'error)))))))

;; Test 22: user-error inherits from error (caught by error handler)
(deftest user-error-as-error (t)
  (el-expr `(progn
    (princ (condition-case nil
               (user-error "\"User message\"")
             (error t))))))

;; =============================================================================
;; INTERACTION TESTS
;; =============================================================================

;; Test 23: condition-case inside catch
(deftest condition-case-in-catch (caught)
  (el-expr `(progn
    (princ (catch 'outer
             (condition-case nil
                 (error "test")
               (error 'caught)))))))

;; Test 24: catch inside condition-case
(deftest catch-in-condition-case (thrown)
  (el-expr `(progn
    (princ (condition-case nil
               (catch 'tag
                 (throw 'tag 'thrown))
             (error 'error))))))

;; Test 25: throw from condition-case handler
(deftest throw-from-handler (escaped)
  (el-expr `(progn
    (princ (catch 'escape
             (condition-case nil
                 (error "test")
               (error (throw 'escape 'escaped))))))))

;; Test 26: Error in condition-case handler goes to outer
(deftest error-in-handler (outer)
  (el-expr `(progn
    (princ (condition-case nil
               (condition-case nil
                   (error "first")
                 (error (error "second")))
             (error 'outer))))))

;; =============================================================================
;; QUIT HANDLING
;; =============================================================================

;; Test 27: quit is caught by condition-case t
(deftest quit-caught-by-t (t)
  (el-expr `(progn
    (princ (condition-case nil
               (signal 'quit nil)
             (t t))))))

;; Note: :success handler in condition-case is not yet implemented in guilemacs
