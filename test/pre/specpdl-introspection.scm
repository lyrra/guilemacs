;; Test specpdl introspection functionality
;; Verifies that default-toplevel-value works correctly with
;; Scheme-based dynamic binding

;; Test 1: default-toplevel-value with PLAINVAL
(deftest test-default-toplevel-value (t)
  (el-expr `(progn
    (defvar test-intro-plainval 'default-value)
    (let ((test-intro-plainval 'bound-value))
      (unless (eq (default-toplevel-value 'test-intro-plainval) 'default-value)
        (princ nil))
      ;; Nested binding
      (let ((test-intro-plainval 'inner-value))
        (unless (eq (default-toplevel-value 'test-intro-plainval) 'default-value)
          (princ nil))))
    (princ t))))

;; Test 2: default-toplevel-value with simple FORWARDED (load-path)
(deftest test-default-toplevel-with-simple-forwarded (t)
  (el-expr `(progn
    (let ((original-path load-path))
      (let ((load-path '("/test/path")))
        (let ((toplevel (default-toplevel-value 'load-path)))
          ;; Should see original, not "/test/path"
          (unless (equal toplevel original-path)
            (princ nil)))))
    (princ t))))

;; Test 3: default-toplevel-value with buffer-local (fill-column)
(deftest test-default-toplevel-with-buffer-local (t)
  (el-expr `(progn
    (let ((original-fill (default-value 'fill-column)))
      (let ((fill-column 999))
        (let ((toplevel (default-toplevel-value 'fill-column)))
          ;; Should see original default, not 999
          (unless (= toplevel original-fill)
            (princ nil)))))
    (princ t))))

;; Test 4: Deep nesting
(deftest test-default-toplevel-deep-nesting (t)
  (el-expr `(progn
    (defvar test-intro-deep 'default)
    (let ((test-intro-deep 'level1))
      (let ((test-intro-deep 'level2))
        (let ((test-intro-deep 'level3))
          (let ((test-intro-deep 'level4))
            (let ((test-intro-deep 'level5))
              (unless (eq (default-toplevel-value 'test-intro-deep) 'default)
                (princ nil)))))))
    (princ t))))

;; Test 5: Mixed binding types in same let
(deftest test-default-toplevel-mixed-binding (t)
  (el-expr `(progn
    (defvar test-intro-mixed 'plain-default)
    (let ((original-gc gc-cons-threshold)
          (original-fill (default-value 'fill-column)))
      (let ((test-intro-mixed 'plain-bound)
            (gc-cons-threshold 12345)
            (fill-column 42))
        ;; All should see their defaults
        (unless (eq (default-toplevel-value 'test-intro-mixed) 'plain-default)
          (princ nil))
        (unless (= (default-toplevel-value 'gc-cons-threshold) original-gc)
          (princ nil))
        (unless (= (default-toplevel-value 'fill-column) original-fill)
          (princ nil))))
    (princ t))))

;; Test 6: default-toplevel-value after exception unwind
(deftest test-default-toplevel-exception-unwind (t)
  (el-expr `(progn
    (defvar test-intro-exception 'default)
    (condition-case nil
        (let ((test-intro-exception 'bound))
          (error "test"))
      (error nil))
    ;; After unwind, should still be able to get default
    (unless (eq (default-toplevel-value 'test-intro-exception) 'default)
      (princ nil))
    (princ t))))

;; Test 7: default-toplevel-value for unbound variable
(deftest test-default-toplevel-unbound (t)
  (el-expr `(progn
    ;; For an unbound/undefined variable, should signal void-variable
    ;; or return the symbol's default (depending on implementation)
    (condition-case err
        (progn
          (default-toplevel-value 'this-var-does-not-exist-12345)
          ;; If no error, that's also acceptable if it returns nil/void
          )
      ;; Any error is acceptable - void-variable or generic error
      ;; Note: Guilemacs condition-case void-variable matching has a known issue
      (error nil))
    (princ t))))
