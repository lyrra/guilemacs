;; integer-or-marker-p predicate tests
;; Returns t if OBJECT is an integer or a marker (editor pointer)

;; Test integer-or-marker-p with various inputs
(for-each (lambda (test-case)
            (match test-case
              ((name input expected)
               (deftestf name (expected)
                 (el-expr `(print (integer-or-marker-p ,input)))))))
  '(
    ;; Integers - should return t
    (integer-or-marker-p-zero 0 t)
    (integer-or-marker-p-one 1 t)
    (integer-or-marker-p-positive 42 t)
    (integer-or-marker-p-negative -42 t)
    (integer-or-marker-p-large 1000000 t)
    (integer-or-marker-p-most-positive-fixnum most-positive-fixnum t)
    (integer-or-marker-p-most-negative-fixnum most-negative-fixnum t)

    ;; Floats - should return nil (not integers)
    (integer-or-marker-p-float-zero 0.0 nil)
    (integer-or-marker-p-float-positive 1.0 nil)
    (integer-or-marker-p-float-negative -1.0 nil)
    (integer-or-marker-p-float-fraction 1.5 nil)

    ;; Non-numeric types - should return nil
    (integer-or-marker-p-nil nil nil)
    (integer-or-marker-p-t t nil)
    (integer-or-marker-p-symbol 'foo nil)
    ))

;; Bignums - should return t
(for-each (lambda (test-case)
            (match test-case
              ((name expr expected)
               (deftestf name (expected)
                 (el-expr `(print (integer-or-marker-p ,expr)))))))
  '(
    (integer-or-marker-p-bignum-positive ("1+" most-positive-fixnum) t)
    (integer-or-marker-p-bignum-negative ("1-" most-negative-fixnum) t)
    (integer-or-marker-p-bignum-very-large (expt 2 100) t)
    (integer-or-marker-p-bignum-very-negative (- (expt 2 100)) t)
    ))

;; Markers - should return t
;; NOTE: Marker tests are disabled until markers are implemented in Scheme
;; (deftest integer-or-marker-p-marker (t)
;;   (el-expr `(with-temp-buffer
;;               (print (integer-or-marker-p (point-marker))))))
;;
;; (deftest integer-or-marker-p-marker-at-point (t)
;;   (el-expr `(with-temp-buffer
;;               (insert "hello")
;;               (goto-char 3)
;;               (print (integer-or-marker-p (point-marker))))))
;;
;; (deftest integer-or-marker-p-copy-marker (t)
;;   (el-expr `(with-temp-buffer
;;               (insert "test")
;;               (let ((m (copy-marker 2)))
;;                 (print (integer-or-marker-p m))))))
