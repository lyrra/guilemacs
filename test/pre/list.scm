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

(deftest rplaca (1)
  (el-expr `(let ((x (cons 0 0)))
              (rplaca x 1)
              (print (car x)))))

(deftest rplacd (1)
  (el-expr `(let ((x (cons 0 0)))
              (rplacd x 1)
              (print (cdr x)))))

;; --- length ---

(deftest length-nil (0)
  (el-expr `(print (length nil))))

(deftest length-empty-list (0)
  (el-expr `(print (length '()))))

(deftest length-single (1)
  (el-expr `(print (length '(a)))))

(deftest length-list (3)
  (el-expr `(print (length '(a b c)))))

(deftest length-string (5)
  (el-expr `(print (length "\"hello\""))))

(deftest length-empty-string (0)
  (el-expr `(print (length "\"\""))))

(deftest length-vector (3)
  (el-expr `(print (length "[1 2 3]"))))

(deftest length-empty-vector (0)
  (el-expr `(print (length "[]"))))

(deftest length-bool-vector (8)
  (el-expr `(print (length (make-bool-vector 8 nil)))))

;; --- length< ---

(deftest length<-shorter (t)
  (el-expr `(print (length< '(a b) 3))))

(deftest length<-equal (nil)
  (el-expr `(print (length< '(a b c) 3))))

(deftest length<-longer (nil)
  (el-expr `(print (length< '(a b c d) 3))))

(deftest length<-empty (t)
  (el-expr `(print (length< nil 1))))

(deftest length<-zero (nil)
  (el-expr `(print (length< '(a) 0))))

(deftest length<-string (t)
  (el-expr `(print (length< "\"ab\"" 3))))

(deftest length<-vector (t)
  (el-expr `(print (length< (vector 1) 2))))

;; --- length> ---

(deftest length>-longer (t)
  (el-expr `(print (length> '(a b c d) 3))))

(deftest length>-equal (nil)
  (el-expr `(print (length> '(a b c) 3))))

(deftest length>-shorter (nil)
  (el-expr `(print (length> '(a b) 3))))

(deftest length>-empty (nil)
  (el-expr `(print (length> nil 0))))

(deftest length>-one (t)
  (el-expr `(print (length> '(a) 0))))

(deftest length>-string (t)
  (el-expr `(print (length> "\"hello\"" 3))))

(deftest length>-vector (nil)
  (el-expr `(print (length> (vector 1 2) 3))))

;; --- length= ---

(deftest length=-match (t)
  (el-expr `(print (length= '(a b c) 3))))

(deftest length=-mismatch-short (nil)
  (el-expr `(print (length= '(a b) 3))))

(deftest length=-mismatch-long (nil)
  (el-expr `(print (length= '(a b c d) 3))))

(deftest length=-empty (t)
  (el-expr `(print (length= nil 0))))

(deftest length=-negative (nil)
  (el-expr `(print (length= '(a) -1))))

(deftest length=-string (t)
  (el-expr `(print (length= "\"hi\"" 2))))

(deftest length=-vector (t)
  (el-expr `(print (length= (vector 1 2 3) 3))))
