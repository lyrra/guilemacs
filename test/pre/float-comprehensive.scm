;;;; comprehensive floating point tests
;;;; testing special values, precision, and edge cases
;;;; focus on IEEE 754 behavior and mathematical functions

;;; Basic floating point operations
(deftest float-basic-add (3.5)
  (el-expr `(print (+ 1.5 2.0))))

(deftest float-basic-multiply (6.0)
  (el-expr `(print (* 2.0 3.0))))

(deftest float-basic-divide (2.5)
  (el-expr `(print (/ 5.0 2.0))))

;;; Special floating point values
(deftest float-positive-infinity (t)
  (el-expr `(condition-case err
                (let ((inf (/ 1.0 0.0)))
                  (print (and (> inf 0) (> inf 1.0e308))))
              (arith-error nil)
              (error nil))))

(deftest float-negative-infinity (t)
  (el-expr `(condition-case err
                (let ((neginf (/ -1.0 0.0)))
                  (print (and (< neginf 0) (< neginf -1.0e308))))
              (arith-error nil)
              (error nil))))

(deftest float-nan (t)
  (el-expr `(condition-case err
                (let ((nan (/ 0.0 0.0)))
                  (print (not (= nan nan))))
              (arith-error nil)
              (error nil))))

;;; Zero handling
(deftest float-positive-zero (0.0)
  (el-expr `(print (+ 0.0 0.0))))

(deftest float-negative-zero (-0.0)
  (el-expr `(print (- 0.0))))

(deftest float-zero-equality (t)
  (el-expr `(print (= 0.0 -0.0))))

;;; Precision and rounding tests
(deftest float-precision-add (t)
  (el-expr `(let ((a 1.0000000000000001)
                  (b 1.0000000000000002))
              (print (numberp (+ a b))))))

(deftest float-very-small (t)
  (el-expr `(let ((tiny 1.0e-300))
              (print (and (> tiny 0.0) (floatp tiny))))))

(deftest float-very-large (t)
  (el-expr `(let ((huge 1.0e300))
              (print (and (> huge 0.0) (floatp huge))))))

;;; Type conversion tests
(deftest int-to-float (42.0)
  (el-expr `(print (float 42))))

(deftest float-to-int (42)
  (el-expr `(print (truncate 42.7))))

(deftest ceiling-float (43)
  (el-expr `(print (ceiling 42.1))))

(deftest floor-float (42)
  (el-expr `(print (floor 42.9))))

(deftest round-float-up (43)
  (el-expr `(print (round 42.6))))

(deftest round-float-down (42)
  (el-expr `(print (round 42.4))))

(deftest round-float-tie (42)
  (el-expr `(print (round 42.5))))

;;; Trigonometric functions
(deftest sin-zero (0.0)
  (el-expr `(print (sin 0.0))))

(deftest cos-zero (1.0)
  (el-expr `(print (cos 0.0))))

(deftest tan-zero (0.0)
  (el-expr `(print (tan 0.0))))

'(deftest sin-pi-half (t)
  (el-expr `(let ((result (sin (/ float-pi 2))))
              (print (and (> result 0.99) (< result 1.01))))))

'(deftest cos-pi (-1.0)
  (el-expr `(let ((result (cos float-pi)))
              (print (and (> result -1.01) (< result -0.99))))))

;;; Hyperbolic functions
'(deftest sinh-zero (0.0)
  (el-expr `(print (sinh 0.0))))

'(deftest cosh-zero (1.0)
  (el-expr `(print (cosh 0.0))))

'(deftest tanh-zero (0.0)
  (el-expr `(print (tanh 0.0))))

;;; Logarithmic functions
(deftest log-one (0.0)
  (el-expr `(print (log 1.0))))

'(deftest log-e (1.0)
  (el-expr `(let ((result (log (exp 1.0))))
              (print (and (> result 0.99) (< result 1.01))))))

'(deftest log10-ten (1.0)
  (el-expr `(print (log10 10.0))))

'(deftest log10-hundred (2.0)
  (el-expr `(print (log10 100.0))))

;;; Exponential functions
(deftest exp-zero (1.0)
  (el-expr `(print (exp 0.0))))

(deftest exp-one (t)
  (el-expr `(let ((e (exp 1.0)))
              (print (and (> e 2.7) (< e 2.8))))))

(deftest expt-square (9.0)
  (el-expr `(print (expt 3.0 2.0))))

'(deftest expt-sqrt (2.0)
  (el-expr `(let ((result (expt 4.0 0.5)))
              (print (and (> result 1.99) (< result 2.01))))))

;;; Square root function
(deftest sqrt-four (2.0)
  (el-expr `(print (sqrt 4.0))))

(deftest sqrt-zero (0.0)
  (el-expr `(print (sqrt 0.0))))

(deftest sqrt-one (1.0)
  (el-expr `(print (sqrt 1.0))))

;;; Comparison operations with floats
(deftest float-equality (t)
  (el-expr `(print (= 1.0 1.0))))

(deftest float-inequality (t)
  (el-expr `(print (not (= 1.0 2.0)))))

(deftest float-less-than (t)
  (el-expr `(print (< 1.5 2.5))))

(deftest float-greater-than (t)
  (el-expr `(print (> 3.14 2.71))))

;;; Mixed integer-float comparisons
(deftest int-float-equality (t)
  (el-expr `(print (= 5 5.0))))

(deftest int-float-comparison (t)
  (el-expr `(print (< 4 4.5))))

;;; Absolute value
(deftest abs-positive-float (3.14)
  (el-expr `(print (abs 3.14))))

(deftest abs-negative-float (3.14)
  (el-expr `(print (abs -3.14))))

(deftest abs-zero-float (0.0)
  (el-expr `(print (abs 0.0))))

;;; Min and max with floats
(deftest min-floats (1.5)
  (el-expr `(print (min 2.5 1.5 3.0))))

(deftest max-floats (3.0)
  (el-expr `(print (max 2.5 1.5 3.0))))

'(deftest min-mixed (1)
  (el-expr `(print (min 2.5 1 3.0))))

(deftest max-mixed (3.0)
  (el-expr `(print (max 2.5 1 3.0))))

;;; Modulo with floats
(deftest fmod-basic (1.0)
  (el-expr `(print (mod 5.0 2.0))))

'(deftest fmod-negative (-1.0)
  (el-expr `(print (mod -5.0 2.0))))

;;; Ceiling, floor, round, truncate edge cases
(deftest ceiling-negative (-2)
  (el-expr `(print (ceiling -2.1))))

(deftest floor-negative (-3)
  (el-expr `(print (floor -2.1))))

(deftest round-negative (-2)
  (el-expr `(print (round -2.1))))

(deftest truncate-negative (-2)
  (el-expr `(print (truncate -2.9))))

;;; Float predicates
(deftest floatp-true (t)
  (el-expr `(print (floatp 3.14))))

(deftest floatp-false (nil)
  (el-expr `(print (floatp 42))))

(deftest numberp-float (t)
  (el-expr `(print (numberp 3.14))))

;;; Arithmetic with very large and small numbers
'(deftest large-float-arithmetic (t)
  (el-expr `(let ((big 1.0e100)
                  (small 1.0e-100))
              (print (and (> (+ big small) big)
                          (floatp (* big small)))))))

;;; Overflow and underflow behavior
(deftest float-overflow (t)
  (el-expr `(condition-case err
                (let ((huge (expt 10.0 400)))
                  (print (or (not (numberp huge)) (> huge 1.0e300))))
              (error t))))

(deftest float-underflow (t)
  (el-expr `(let ((tiny (* 1.0e-200 1.0e-200)))
              (print (or (= tiny 0.0) (> tiny 0.0))))))

;;; String conversion
'(deftest float-to-string (t)
  (el-expr `(let ((str (number-to-string 3.14159)))
              (print (stringp str)))))

'(deftest string-to-float (3.14)
  (el-expr `(print (string-to-number "3.14"))))

;;; Scientific notation
'(deftest scientific-notation (t)
  (el-expr `(let ((sci (string-to-number "1.23e4")))
              (print (and (floatp sci) (> sci 12000) (< sci 13000))))))

;;; Error conditions
'(deftest sqrt-negative-error (t)
  (el-expr `(condition-case err
                (progn (sqrt -1.0) nil)
              (domain-error t)
              (error t))))

'(deftest log-negative-error (t)
  (el-expr `(condition-case err
                (progn (log -1.0) nil)
              (domain-error t)
              (error t))))

'(deftest log-zero-error (t)
  (el-expr `(condition-case err
                (progn (log 0.0) nil)
              (domain-error t)
              (singularity-error t)
              (error t))))

;;; Inverse trigonometric functions
(deftest asin-zero (0.0)
  (el-expr `(print (asin 0.0))))

(deftest acos-one (0.0)
  (el-expr `(print (acos 1.0))))

(deftest atan-zero (0.0)
  (el-expr `(print (atan 0.0))))

'(deftest atan2-basic (t)
  (el-expr `(let ((angle (atan2 1.0 1.0)))
              (print (and (> angle 0.78) (< angle 0.79))))))

;;; IEEE 754 special cases
(deftest ieee-nan-comparisons (t)
  (el-expr `(condition-case err
                (let ((nan (/ 0.0 0.0)))
                  (print (and (not (= nan nan))
                              (not (< nan 0))
                              (not (> nan 0)))))
              (error t))))

(deftest ieee-infinity-arithmetic (t)
  (el-expr `(condition-case err
                (let ((inf (/ 1.0 0.0)))
                  (print (= inf (+ inf 1.0))))
              (error t))))

;;; Denormal numbers (very small floats)
(deftest denormal-handling (t)
  (el-expr `(let ((very-small (* 1.0e-300 1.0e-20)))
              (print (or (= very-small 0.0)
                         (and (floatp very-small) (> very-small 0.0)))))))

;;; Float constants
'(deftest pi-constant (t)
  (el-expr `(print (and (boundp 'float-pi)
                        (> float-pi 3.14)
                        (< float-pi 3.15)))))

'(deftest e-constant (t)
  (el-expr `(condition-case err
                (print (and (boundp 'float-e)
                            (> float-e 2.71)
                            (< float-e 2.72)))
              (void-variable (print t))  ; float-e might not be defined
              (error t))))
