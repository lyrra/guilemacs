;; Test natnump with various inputs
(for-each (lambda (test-case)
            (match test-case
              ((name input expected)
               (deftestf name (expected)
                 (el-expr `(print (natnump ,input)))))))
  '(
    ;; Basic positive cases - should return t
    (natnump-zero 0 t)
    (natnump-one 1 t)
    (natnump-small-positive 42 t)
    (natnump-large-positive 1000000 t)

    ;; Negative integers - should return nil
    (natnump-negative-one -1 nil)
    (natnump-negative-small -42 nil)
    (natnump-negative-large -1000000 nil)

    ;; Floats - should return nil (even if they represent integers)
    (natnump-float-zero 0.0 nil)
    (natnump-float-positive 1.0 nil)
    (natnump-float-negative -1.0 nil)
    (natnump-float-with-fraction 1.5 nil)

    ;; Non-numeric types - should return nil
    (natnump-nil nil nil)
    (natnump-t t nil)
    (natnump-symbol 'foo nil)

    ;; Fixnum boundaries
    (natnump-most-positive-fixnum most-positive-fixnum t)
    (natnump-most-negative-fixnum most-negative-fixnum nil)
    ))

;; Bignums require expressions that need evaluation
(for-each (lambda (test-case)
            (match test-case
              ((name expr expected)
               (deftestf name (expected)
                 (el-expr `(print (natnump ,expr)))))))
  '(
    (natnump-bignum-positive ("1+" most-positive-fixnum) t)
    (natnump-bignum-negative ("1-" most-negative-fixnum) nil)
    (natnump-bignum-very-large (expt 2 100) t)
    (natnump-bignum-very-negative (- (expt 2 100)) nil)
    ))

;; wholenump is an alias for natnump
(for-each (lambda (test-case)
            (match test-case
              ((name input expected)
               (deftestf name (expected)
                 (el-expr `(print (wholenump ,input)))))))
  '(
    (wholenump-zero 0 t)
    (wholenump-positive 42 t)
    (wholenump-negative -1 nil)
    ))

(deftest natnump-string (nil)
  (el-expr `(print (natnump "\"42\""))))

(deftest natnump-cons (nil)
  (el-expr `(print (natnump '(1 . 2)))))

(deftest natnump-list (nil)
  (el-expr `(print (natnump '(1 2 3)))))

(deftest natnump-vector (nil)
  (el-expr `(print (natnump "[1 2 3]"))))

;; Characters are integers in Emacs, so they should work
(deftest natnump-char-a (t)
  (el-expr `(print (natnump ?a))))

(deftest natnump-char-zero (t)
  (el-expr `(print (natnump "?\\0"))))
