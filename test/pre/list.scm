;; Basic null tests
(deftest null-nil (t)
  (el-expr `(print (null nil))))

(deftest null-empty-list (t)
  (el-expr `(print (null '()))))

(deftest null-false-symbol (nil)
  (el-expr `(print (null 'false))))

(deftest null-zero (nil)
  (el-expr `(print (null 0))))

(deftest null-empty-string (nil)
  (el-expr `(let ((empty-str "\"\""))
              (print (null empty-str)))))

(deftest null-t (nil)
  (el-expr `(print (null t))))

(for-each (lambda (pair)
            (match pair
              ((name input expected)
               (deftestf name (expected)
                 (el-expr `(let ((x ,input))
                             (print (null x))))))))
  '(
    ;; Test null with various data types
    (null-integer 42 nil)
    (null-negative-integer -42 nil)
    (null-float 3.14 nil)
    (null-negative-float -3.14 nil)
    (null-string "\"hello\"" nil)
    (null-symbol 'symbol nil)
    (null-cons '(a . b) nil)
    (null-list '(1 2 3) nil)
    ;(null-vector [1 2 3] nil)
    (null-char ?a nil)

    ;; Test null with special values
    (null-most-positive-fixnum most-positive-fixnum nil)
    (null-most-negative-fixnum most-negative-fixnum nil)
    ))

;; Test null with bignum
(let ((big (expt 2 70)))
  (deftest null-bignum (nil)
    (el-expr `(print (null ,big)))))

;; Test null with variable bindings
(deftest null-variable-nil (t)
  (el-expr `(let ((x nil))
              (print (null x)))))

(deftest null-variable-non-nil (nil)
  (el-expr `(let ((x 'something))
              (print (null x)))))

;; Test null with nested expressions
(deftest null-car-nil-list (t)
  (el-expr `(print (null (car '(nil))))))

(deftest null-cdr-single-list (t)
  (el-expr `(print (null (cdr '(only))))))

(deftest not-car-nil-list (t)
  (el-expr `(print (not (car '(nil))))))

(for-each (lambda (pair)
            (match pair
              ((name oper input expected)
               (deftestf name (expected)
                 (el-expr `(let ((x ,input))
                             (print (,oper x))))))))
  '((car-nil car nil nil)
    (cdr-nil cdr nil nil)
    (caar-nil caar nil nil)
    (cadr-nil cadr nil nil)
    (cdar-nil cdar nil nil)
    (cddr-nil cddr nil nil)))

(for-each (lambda (pair)
            (match pair
              ((name oper input expected)
               (deftestf name (expected)
                 (el-expr `(let ((x ',input))
                             (print (,oper x))))))))
  '((car-1 car (1) 1)
    (cdr-1 cdr (0 . 1) 1)
    (caar-1 caar ((1)) 1)
    (cadr-1 cadr (0 . (1)) 1)
    (cdar-1 cdar ((0 . 1)) 1)
    (cddr-1 cddr (0 . (0 . 1)) 1)))
