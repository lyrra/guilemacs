;; symbolp predicate tests
;; Returns t if OBJECT is a symbol (including t and nil)

(for-each (lambda (test-case)
            (match test-case
              ((name input expected)
               (deftestf name (expected)
                 (el-expr `(print (symbolp ,input)))))))
  '(
    ;; t and nil are symbols in Elisp
    (symbolp-t t t)
    (symbolp-nil nil t)

    ;; Regular symbols
    (symbolp-foo 'foo t)
    (symbolp-bar 'bar t)

    ;; Non-symbols should return nil
    (symbolp-zero 0 nil)
    (symbolp-positive 42 nil)
    (symbolp-negative -1 nil)
    (symbolp-float 3.14 nil)
    ))

(deftest zerop-0 (t) (el-expr `(print (zerop 0))))
(deftest zerop-1 (nil) (el-expr `(print (zerop 1))))

(deftest wholenump--1 (nil) (el-expr `(print (wholenump -1))))
(deftest wholenump-0 (t) (el-expr `(print (wholenump 0))))
(deftest wholenump-00 (nil) (el-expr `(print (wholenump 0.0))))
(deftest wholenump-1 (t) (el-expr `(print (wholenump 1))))

(deftest numberp-0 (t) (el-expr `(print (numberp 0))))
(deftest numberp-s (nil) (el-expr `(print (numberp "\"s\""))))

(deftest integerp-0 (t) (el-expr `(print (integerp 0))))
(deftest integerp-00 (nil) (el-expr `(print (integerp 0.0))))

(deftest floatp-0 (nil) (el-expr `(print (floatp 0))))
(deftest floatp-00 (t) (el-expr `(print (floatp 0.0))))
