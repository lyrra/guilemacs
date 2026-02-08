;; Test complex variable binding functionality
;; Tests optimization for buffer-local, kboard, and LOCALIZED variables

;; Test 1: DEFVAR_PER_BUFFER (fill-column)
(deftest test-defvar_per_buffer (t)
  (el-expr `(progn
    (let ((original fill-column))
      (let ((fill-column 999))
        (unless (= fill-column 999)
          (princ nil)))
      (unless (= fill-column original)
        (princ nil))
      (princ t)))))

;; Test 2: Another DEFVAR_PER_BUFFER (tab-width)
(deftest test-defvar_per_buffer-2 (t)
  (el-expr `(progn
    (let ((original tab-width))
      (let ((tab-width 2))
        (unless (= tab-width 2)
          (princ nil)))
      (unless (= tab-width original)
        (princ nil))
      (print t)))))

;; Test 3: make-variable-buffer-local'd variable
(deftest test-make-variable-buffer-local-var (t)
  (el-expr `(progn
    (let ()
      (defvar test-complex-blv 'default-value)
      (make-variable-buffer-local 'test-complex-blv)
      (let ((test-complex-blv 'let-bound))
        (unless (eq test-complex-blv 'let-bound)
          (princ nil)))
      (unless (eq test-complex-blv 'default-value)
        (princ nil))
      (princ t)))))

;; Test 4: Nested complex bindings
(deftest test-nested-complex-bindings (t)
  (el-expr `(progn
    (let ((original fill-column))
      (let ((fill-column 10))
        (let ((fill-column 20))
          (let ((fill-column 30))
            (unless (= fill-column 30)
              (princ nil))))
        (unless (= fill-column 10)
          (princ nil)))
      (unless (= fill-column original)
        (princ nil))
        (princ t)))))

;; Test 5: Exception unwind for complex binding
(deftest test-exception-unwind-complex-bindings (t)
  (el-expr `(progn
    (let ((original fill-column))
      (condition-case nil
          (let ((fill-column 123))
            (error "test error"))
        (error nil))
      (unless (= fill-column original)
        (princ nil))
      (princ t)))))

;; Test 6: Mixed PLAINVAL + complex in same let
(deftest test-mixed-plainval-complex (t)
  (el-expr `(progn
    (defvar test-plainval-phase3 'plain-original)
    (let ((original-plain test-plainval-phase3)
          (original-fill fill-column))
      (let ((test-plainval-phase3 'plain-bound)
            (fill-column 77))
        (unless (and (eq test-plainval-phase3 'plain-bound)
                     (= fill-column 77))
          (princ nil)))
      (unless (and (eq test-plainval-phase3 original-plain)
                   (= fill-column original-fill))
        (princ nil)))
      (princ t))))

;; Test 7: Mixed simple FORWARDED + complex in same let
(deftest test-mixed-simple-forwarded-complex (t)
  (el-expr `(progn
    (let ((original-gc gc-cons-threshold)
          (original-fill fill-column))
      (let ((gc-cons-threshold 888888)
            (fill-column 44))
        (unless (and (= gc-cons-threshold 888888)
                     (= fill-column 44))
          (princ nil)))
      (unless (and (= gc-cons-threshold original-gc)
                   (= fill-column original-fill))
        (princ nil)))
    (princ t))))

;; Test 8: Deep nesting of complex (5 levels)
(deftest test-deep-nesting-complex (t)
  (el-expr `(progn
    (let ((original fill-column))
      (let ((result
             (let ((fill-column 1))
               (let ((fill-column 2))
                 (let ((fill-column 3))
                   (let ((fill-column 4))
                     (let ((fill-column 5))
                       fill-column)))))))
        (unless (= result 5)
          (princ nil)))
      (unless (= fill-column original)
        (princ nil))
      (princ t)))))

;; Test 9: Buffer-local with actual local value
; FIX-20260208-guilemacs: postpone until setq-local is defined in scheme (subr.el)
'(deftest test-buffer-local-with-actual-local (t)
  (el-expr `(progn
    (with-temp-buffer
      ;; Create a local value
      (setq-local fill-column 50)
      (let ((local-val fill-column))
        (let ((fill-column 100))
          (unless (= fill-column 100)
            (princ nil)))
        (unless (= fill-column local-val)
          (princ nil))))
    (princ t))))

;; Test 10: Verify symbol-simple-forward-p returns nil for complex
(deftest test-symbol-simple-forward-p-on-complex (t)
  (el-expr `(progn
    ;; fill-column is DEFVAR_PER_BUFFER - should NOT be simple forward
    (if (symbol-simple-forward-p 'fill-column)
      (princ nil))
    ;; tab-width is DEFVAR_PER_BUFFER - should NOT be simple forward
    (if (symbol-simple-forward-p 'tab-width)
      (princ nil))
    (princ t))))
