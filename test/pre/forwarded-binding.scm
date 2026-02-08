;; Test FORWARDED variable binding functionality
;; Tests the optimization for simple FORWARDED variables
;; (DEFVAR_LISP, DEFVAR_INT, DEFVAR_BOOL)

;; Test 1: DEFVAR_LISP (load-path)
(deftest test-defvar_lisp (t)
  (el-expr `(progn
    (let ((original load-path))
      (let ((load-path '("/test/path")))
        (unless (equal load-path '("/test/path"))
          (princ nil)))
      (unless (equal load-path original)
        (princ nil)))
    (princ t))))

;; Test 2: DEFVAR_INT (gc-cons-threshold)
(deftest test-defvar_int (t)
  (el-expr `(progn
    (let ((original gc-cons-threshold))
      (let ((gc-cons-threshold 999999))
        (unless (= gc-cons-threshold 999999)
          (princ nil)))
      (unless (= gc-cons-threshold original)
        (princ nil))
      (princ t)))))

;; Test 3: DEFVAR_BOOL (debug-on-error)
(deftest test-defvar_bool (t)
  (el-expr `(progn
    (let ((original debug-on-error))
      (let ((debug-on-error (not original)))
        (unless (eq debug-on-error (not original))
          (princ nil)))
      (unless (eq debug-on-error original)
        (princ nil))
      (princ t)))))

;; Test 4: Nested simple FORWARDED bindings
(deftest test-nested-simple-forwarded-bindings (t)
  (el-expr `(progn
    (let ((original-path load-path)
          (original-gc gc-cons-threshold))
      (let ((load-path '("/a"))
            (gc-cons-threshold 1000))
        (let ((load-path '("/b"))
              (gc-cons-threshold 2000))
          (unless (and (equal load-path '("/b"))
                       (= gc-cons-threshold 2000))
            (princ nil))))
      (unless (and (equal load-path original-path)
                   (= gc-cons-threshold original-gc))
        (princ nil))
      (princ t)))))

;; Test 5: Exception unwind for FORWARDED
(deftest test-exception-unwind-for-forwarded (t)
  (el-expr `(progn
    (let ((original gc-cons-threshold))
      (condition-case nil
          (let ((gc-cons-threshold 12345))
            (error "test"))
        (error nil))
      (unless (= gc-cons-threshold original)
        (princ nil))
      (princ t)))))

;; Test 6: Mixed PLAINVAL and FORWARDED in same let
(deftest test-mixed-plainval-and-forwarded (t)
  (el-expr `(progn
    (defvar test-plainval-mixed 'original)
    (let ((original-plainval test-plainval-mixed)
          (original-gc gc-cons-threshold))
      (let ((test-plainval-mixed 'bound)
            (gc-cons-threshold 54321))
        (unless (and (eq test-plainval-mixed 'bound)
                     (= gc-cons-threshold 54321))
          (princ nil)))
      (unless (and (eq test-plainval-mixed original-plainval)
                   (= gc-cons-threshold original-gc))
        (princ nil))
      (princ t)))))

;; Test 7: Deep nesting of FORWARDED (5 levels)
(deftest test-deep-nested-forwarded (t)
  (el-expr `(progn
    (let ((original gc-cons-threshold))
      (let ((result
             (let ((gc-cons-threshold 1))
               (let ((gc-cons-threshold 2))
                 (let ((gc-cons-threshold 3))
                   (let ((gc-cons-threshold 4))
                     (let ((gc-cons-threshold 5))
                       gc-cons-threshold)))))))
        (unless (= result 5)
          (princ nil)))
      (unless (= gc-cons-threshold original)
        (princ nil))
      (princ t)))))

;; Test 8: symbol-simple-forward-p predicate
(deftest test-symbol-simple-forward (t)
  (el-expr `(progn
    (let ()
      ;; gc-cons-threshold is DEFVAR_INT - should be simple forward
      (unless (symbol-simple-forward-p 'gc-cons-threshold)
        (princ nil))
      ;; load-path is DEFVAR_LISP - should be simple forward
      (unless (symbol-simple-forward-p 'load-path)
        (princ nil))
      ;; debug-on-error is DEFVAR_BOOL - should be simple forward
      (unless (symbol-simple-forward-p 'debug-on-error)
        (princ nil))
      ;; fill-column is DEFVAR_PER_BUFFER - should NOT be simple forward
      (if (symbol-simple-forward-p 'fill-column)
        (princ nil))
      ;; A regular defvar should NOT be simple forward
      (defvar test-not-forwarded 42)
      (if (symbol-simple-forward-p 'test-not-forwarded)
        (princ nil))
      (princ t)))))
