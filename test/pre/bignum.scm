;;;; test operations handling bignum
;;;; especially the corner-cases
;;;; for some preliminary fixnum tests at limit see pre/fixnum.scm

;; we're past maxsize of a guile fixnum, ie we're in bignum territory

;; try some numbers around the fixnum/bignum boundary

(define %interesting-bignums
  (list (expt 2 61) ; next number after most-positive-fixnum
        (expt 2 62)
        (expt 2 63)
        (expt 2 64)
        (- (expt 2 62))
        (- (expt 2 63))
        (- (expt 2 64))
        (- (expt 2 62) 1)
        (- (expt 2 63) 1)
        (- (expt 2 64) 1)))

(for-each (lambda (num)
            (let ((name (string->symbol (format #f "num-~x" num))))
              (deftestf name (num)
                (el-expr `(print ,num)))))
          %interesting-bignums)

(for-each (lambda (num)
              (deftestf (string->symbol (format #f "number-to-string-~x" num))
                        ((format #f "~a" num))
                (el-expr `(print (number-to-string ,num))))

              (deftestf (string->symbol (format #f "string-to-number-~x" num))
                        (num)
                (el-expr `(print (string-to-number ,(format #f "\"~a\"" num))))))
          %interesting-bignums)

(let ((mpfx (- (expt 2 61) 1)) ; most-positive-fixnum
      (lnfx (- (expt 2 62) 1))) ; least-negative-fixnum

  (deftestf 'bignum-print-mpfx+1 ((+ mpfx 1))
    (el-expr `(print (+ 1 ,mpfx))))

  (deftestf 'bignum-print-mpfx+1 ((+ mpfx mpfx))
    (el-expr `(print (+ ,mpfx ,mpfx))))

  (deftestf 'bignum-print-mpfx+1 ((+ mpfx mpfx))
    (el-expr `(print (* 2 ,mpfx))))

  ;; in elisp, (print (= (* 2 ,fx) (+ ,fx ,fx)) => t
  (deftestf 'bignum-print-mpfx*2=mpfx+mpfx ('t)
    (el-expr `(print (= (* 2 ,mpfx) (+ ,mpfx ,mpfx)))))

  ;; in elisp, (print (= (* 2 ,fx) (+ ,fx ,fx)) => t
  (let ((mpfx2 (* 2 mpfx))) ; 2 * most-positive-fixnum
    (deftestf 'bignum-print-mpfx*2/2=mpfx ('t)
      (el-expr `(print (= ,mpfx (/ ,mpfx2 2)))))))

;;; run some operator taking two operands, and expect some value
;;; by swapping operator to its opposite or operand position will also swap expected value

(let ((make-arith-test
       (lambda (o a b e)
         (deftestf (string->symbol (format #f "~a-~a-~a-~a" o a b e)) (e)
           (el-expr `(princ (,o ,a ,b)))))))

  ;; bignum vs fixnum
  (let ((b (expt 2 64))
        (f (1+ (expt 2 34))))
    (make-arith-test '< f b 't)
    (make-arith-test '> b f 't)
    (make-arith-test '> f b 'nil)
    (make-arith-test '< b f 'nil))

  ;; bignum vs float
  (let ((b (expt 2 64))
        (f (+ 0.1 (1+ (expt 2 34)))))
    (make-arith-test '< f b 't)
    (make-arith-test '> b f 't)
    (make-arith-test '> f b 'nil)
    (make-arith-test '< b f 'nil)))

;;; minus
(for-each (lambda (num)
            (let ((name (string->symbol (format #f "minus-a0-~x" num))))
              (deftestf name ((- num))
                (el-expr `(print (- ,num))))))
          (append %interesting-bignums
                  '(0 -1 1)))

;;;
;;; in vanilla emacs all these equals 2305843009213693952 (- most-negative-fixnum)
(deftest divide-extreme-sign-ceiling (t)
  (el-expr `(print (= -2305843009213693952
                      (ceiling most-negative-fixnum -1.0)))))
(deftest divide-extreme-sign-floor (t)
  (el-expr `(print (= 2305843009213693952
                      (floor most-negative-fixnum -1.0)))))
(deftest divide-extreme-sign-round (t)
  (el-expr `(print (= -2305843009213693952
                      (round most-negative-fixnum -1.0)))))
(deftest divide-extreme-sign-truncate (t)
  (el-expr `(print (= -2305843009213693952
                      (truncate most-negative-fixnum -1.0)))))

;;; logarithm
(deftest logb-2 (62)
  (el-expr `(print (+ (logb most-positive-fixnum) 1))))

(deftest logb-3 (61)
  (el-expr `(print (logb (+ most-positive-fixnum 1)))))

(deftest bignum-abs (t)
  (el-expr `(print (= most-positive-fixnum
                      (- (abs most-negative-fixnum) 1)))))

;;; misc, test all fns functions

(for-each (lambda (trip)
            (match trip
              ((oper arity expect)
               (let* ((name (string->symbol (format #f "misc-fns-~a" oper)))
                      (a (expt 2 80))
                      (b (expt 2 78))
                      (e (if (procedure? expect)
                             (if (= arity 1)
                                 (expect a)
                                 (expect a b))
                             expect)))
                 (deftestf name (e)
                   (if (= arity 1)
                       (el-expr `(print (,oper ,a)))
                       (el-expr `(print (,oper ,a ,b)))))))))
          `((= 2 nil)
            (< 2 nil)
            (> 2 t)
            (<= 2 nil)
            (>= 2 t)
            (/= 2 t)
            (+ 2 ,(lambda (a b) (+ a b)))
            (- 2 ,(lambda (a b) (- a b)))
            (* 2 ,(lambda (a b) (* a b)))
            (/ 2 ,(lambda (a b) (/ a b)))
            (% 2 ,(lambda (a b) (remainder a b)))
            (mod 2 ,(lambda (a b) (modulo a b)))
            (max 2 ,(lambda (a b) (max a b)))
            (min 2 ,(lambda (a b) (min a b)))

            (logand 2 ,(lambda (a b) (logand a b)))
            (logior 2 ,(lambda (a b) (logior a b)))
            (logxor 2 ,(lambda (a b) (logxor a b)))
            (logcount 1 ,(lambda (a) (logcount a)))
            (ash 2 ,(lambda (a b) (ash a b)))
            (lognot 1 ,(lambda (a) (lognot a)))))

;;; format

;; disabled for now, see guilemacs FIX in editfns.c styled_format
;(for-each (lambda (num)
;           (deftestf (string->symbol (format #f "format-~x" num))
;                     ((format #f "~a" num))
;             (el-expr `(print (format "\"%i\"" ,num)))))
;         %interesting-bignums)
