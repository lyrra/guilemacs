;;; numbers used in tests in floatfns are too large:
;;;   1.7976931348623157e+308
;;;   5e-324
;;;
;;; float precision

(let ((q 1.7976931348623157e+100)
      (r 5e-100))
  (deftest big-floor (t)
    (el-expr `(print (= (floor ,q ,r)
                        ,(floor-quotient q r))))))

;;; this test fails on vanilla guile:
;;; (floor-quotient 54043195528445955 3) => 18014398509481985
;;; (floor-quotient 54043195528445955 3.0) => 18014398509481984.0
'(deftest floor-1 (t)
  (el-expr `(print (= (floor 54043195528445955 3)
                      (floor 54043195528445955 3.0)))))

(deftest floor-2 (123)
  (el-expr `(print (floor 123.999))))

(deftest expt (33.1776)
  (el-expr `(print (expt 2.4 4.0))))

(for-each (lambda (num)
            (deftestf (string->symbol (format #f "round_~a" num))
                      ((inexact->exact (round num)))
              (el-expr `(let ((a ,num)) (print (round a))))))
          '(4.3 1.2 5.7))
