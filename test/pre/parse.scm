;; Tests for parse-body-1 in compile-tree-il.scm
;; Specifically tests :documentation form handling in lambda bodies

;; =============================================================================
;; BASIC :DOCUMENTATION TESTS
;; =============================================================================

;; Test 1: Lambda with :documentation and literal string
(deftest parse-documentation-literal (executed)
  (el-expr `(progn
    (let ((f (lambda ()
               (:documentation "\"Test documentation\"")
               'executed)))
      (princ (funcall f))))))

;; Test 2: Lambda with :documentation and computed expression
(deftest parse-documentation-computed (executed)
  (el-expr `(progn
    (let ((f (lambda ()
               (:documentation (format "\"Doc for %s\"" "\"test\""))
               'executed)))
      (princ (funcall f))))))

;; Test 3: Lambda with :documentation using format function
(deftest parse-documentation-format (42)
  (el-expr `(progn
    (let ((f (lambda ()
               (:documentation (format "\"Value is %d\"" 42))
               42)))
      (princ (funcall f))))))

;; Test 4: Lambda body executes correctly with :documentation
(deftest parse-documentation-body-executes (result-value)
  (el-expr `(progn
    (let ((f (lambda ()
               (:documentation "\"Some doc\"")
               (setq test-var 'result-value)
               test-var)))
      (princ (funcall f))))))

;; Test 5: Lambda with :documentation and arguments
(deftest parse-documentation-with-args (6)
  (el-expr `(progn
    (let ((f (lambda (a b)
               (:documentation "\"Adds two numbers\"")
               (+ a b))))
      (princ (funcall f 2 4))))))

;; Test 6: Nested lambda with :documentation
(deftest parse-documentation-nested (inner-result)
  (el-expr `(progn
    (let ((outer (lambda ()
                   (:documentation "\"Outer function\"")
                   (let ((inner (lambda ()
                                  (:documentation "\"Inner function\"")
                                  'inner-result)))
                     (funcall inner)))))
      (princ (funcall outer))))))

;; Test 7: Lambda with :documentation as only declaration (no docstring)
(deftest parse-documentation-no-string-doc (success)
  (el-expr `(progn
    (let ((f (lambda ()
               (:documentation "\"Dynamic doc\"")
               'success)))
      (princ (funcall f))))))

;; Test 8: Lambda with both declare and :documentation
(deftest parse-documentation-with-declare (declared-result)
  (el-expr `(progn
    (let ((f (lambda ()
               (declare (pure t))
               (:documentation "\"Function with declare\"")
               'declared-result)))
      (princ (funcall f))))))

;; Test 9: defun-style with :documentation (via defalias to lambda)
(deftest parse-documentation-defalias (defalias-result)
  (el-expr `(progn
    (defalias 'test-fn-with-doc
      (lambda ()
        (:documentation "\"Defalias function doc\"")
        'defalias-result))
    (princ (test-fn-with-doc)))))

;; Test 10: :documentation with format expression
(deftest parse-documentation-internal-format (formatted)
  (el-expr `(progn
    (let ((f (lambda ()
               (:documentation (format "\"Test for %s\"" "\"formatting\""))
               'formatted)))
      (princ (funcall f))))))
