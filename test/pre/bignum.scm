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
