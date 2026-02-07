;; Test dynamic binding functionality
;; Tests the make-dynlet-one optimization for PLAINVAL and non-PLAINVAL variables


;; Test 1: Basic PLAINVAL let-binding
(deftest test-dynvar-1 (t)
  (el-expr `(progn
    (defvar test-dynvar-1 'original)
    (let ((result nil))
      (setq result
            (let ((test-dynvar-1 'bound))
              test-dynvar-1))
      (if (and (eq result 'bound)
               (eq test-dynvar-1 'original))
          (princ t)
        (princ nil))))))

;; Test 2: Nested let-bindings (tests for exponential blowup fix)
(deftest test-dynvar-2 (t)
  (el-expr `(progn
    (defvar test-dynvar-2 0)
    (let ((result
           (let ((test-dynvar-2 1))
             (let ((test-dynvar-2 2))
               (let ((test-dynvar-2 3))
                 (let ((test-dynvar-2 4))
                   (let ((test-dynvar-2 5))
                     test-dynvar-2)))))))
      (if (and (= result 5)
               (= test-dynvar-2 0))
          (princ t)
        (princ nil))))))

;; Test 3: let* sequential binding
(deftest test-dynvar-3 (t)
  (el-expr `(progn
    (defvar test-dynvar-3a 'a-orig)
    (defvar test-dynvar-3b 'b-orig)
    (let ((result
           (let* ((test-dynvar-3a 'a-new)
                  (test-dynvar-3b test-dynvar-3a))
             (cons test-dynvar-3a test-dynvar-3b))))
      (if (and (equal result '(a-new . a-new))
               (eq test-dynvar-3a 'a-orig)
               (eq test-dynvar-3b 'b-orig))
          (princ t)
        (princ nil))))))

;; Test 4: unwind-protect with dynamic binding
(deftest test-dynvar-4 (t)
  (el-expr `(progn
    (defvar test-dynvar-4 'original)
    (let ((unwound nil))
      (condition-case nil
          (let ((test-dynvar-4 'bound))
            (unwind-protect
                (progn
                  (if (eq test-dynvar-4 'bound)
                      nil
                    (princ nil)))
              (setq unwound t)))
        (error nil))
      (if (and unwound
               (eq test-dynvar-4 'original))
          (princ t)
        (princ nil))))))

;; Test 5: Multiple variables in one let
(deftest test-dynvar-4 (t)
  (el-expr `(progn
    (defvar test-dynvar-5a 1)
    (defvar test-dynvar-5b 2)
    (defvar test-dynvar-5c 3)
    (let ((result
           (let ((test-dynvar-5a 10)
                 (test-dynvar-5b 20)
                 (test-dynvar-5c 30))
             (+ test-dynvar-5a test-dynvar-5b test-dynvar-5c))))
      (if (and (= result 60)
               (= test-dynvar-5a 1)
               (= test-dynvar-5b 2)
               (= test-dynvar-5c 3))
          (princ t)
        (princ nil))))))

;; Test 6: Deep nesting stress test (10 levels)
(deftest test-dynvar-4 (t)
  (el-expr `(progn
    (defvar test-dynvar-6 0)
    (let ((result
           (let ((test-dynvar-6 1))
             (let ((test-dynvar-6 2))
               (let ((test-dynvar-6 3))
                 (let ((test-dynvar-6 4))
                   (let ((test-dynvar-6 5))
                     (let ((test-dynvar-6 6))
                       (let ((test-dynvar-6 7))
                         (let ((test-dynvar-6 8))
                           (let ((test-dynvar-6 9))
                             (let ((test-dynvar-6 10))
                               test-dynvar-6))))))))))))
      (if (and (= result 10)
               (= test-dynvar-6 0))
          (princ t)
        (princ nil))))))
