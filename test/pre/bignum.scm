;;;; test operations handling bignum
;;;; especially the corner-cases
;;;; for some preliminary fixnum tests at limit see pre/fixnum.scm

(use-modules (rnrs arithmetic fixnums))

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
(let ((m 2305843009213693952)) ; (- most-negative-fixnum)
  (deftest divide-extreme-sign-ceiling (t)
    (el-expr `(print (= ,m
                        (ceiling most-negative-fixnum -1.0)))))
  (deftest divide-extreme-sign-floor (t)
    (el-expr `(print (= ,m
                        (floor most-negative-fixnum -1.0)))))
  (deftest divide-extreme-sign-round (t)
    (el-expr `(print (= ,m
                        (round most-negative-fixnum -1.0)))))
  (deftest divide-extreme-sign-truncate (t)
    (el-expr `(print (= ,m
                        (truncate most-negative-fixnum -1.0))))))

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
            ;(ash 2 ,(lambda (a b) (ash a b))) ; see separate tests for ash
            (lognot 1 ,(lambda (a) (lognot a)))))

;;; format

;; disabled for now, see guilemacs FIX in editfns.c styled_format
;(for-each (lambda (num)
;           (deftestf (string->symbol (format #f "format-~x" num))
;                     ((format #f "~a" num))
;             (el-expr `(print (format "\"%i\"" ,num)))))
;         %interesting-bignums)

;;; random

(deftest random-bignum (t)
  (el-expr `(print (integerp (random ,(expt 2 80))))))

;; note emacs READ will pass the forms to the
;; guile compiler which will optimize away
;; constant expressions such as "(ash 1 2)",
;; therefore we need to pass one of its arguments
;; as a variable
(deftest ash-bignum1 (t)
  (let ((a (expt 2 64)))
    (el-expr `(let ((b (expt 2 30)))
                (print (integerp (ash ,a b)))))))

(deftest ash-bignum2 (t)
  (let ((b (expt 2 30)))
    (el-expr `(let ((b ,(expt 2 30)))
                (print (integerp (ash 2 b)))))))

;; FIX: guilemacs, this is exhausting memory:
;; GC Warning: Repeated allocation of very large block (appr. size 17846272)
;(deftest ash-bignum2 (t)
;  (let ((a 1)
;        (b (expt 2 30)))
;    (el-expr `(print (ash ,a ,b)))))

(deftest mnf*8 (-18446744073709551616)
  (el-expr `(let ((mnf most-negative-fixnum))
              (print (* 8 mnf)))))

(deftest mpf*8 (18446744073709551608)
  (el-expr `(let ((mpf most-positive-fixnum))
              (print (* 8 mpf)))))

(deftestf 'abs ((abs (* 8 (least-fixnum))))
  (el-expr `(let ((num (* 8 most-negative-fixnum)))
              (print (abs num)))))
