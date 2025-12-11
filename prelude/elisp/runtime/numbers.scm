;;; Guilemacs Lisp
;;;
;;; Arithmetic & Math Operations
;;;
;;; Migrated from C DEFUN arithmetic and mathematical functions.
;;; Includes: basic ops (+, -, *, /), comparisons, bitwise ops, floating point, predicates.

;;;
;;; Basic Arithmetic Operations
;;;

(define elisp-+ (lambda args
                  (apply + (map check-number-coerce-marker args))))

(define elisp-- (lambda args
                  (apply - (map check-number-coerce-marker args))))

(define elisp-* (lambda args
                  (apply * (map check-number-coerce-marker args))))

(define (elisp-/-fold a lst seen-inexact)
  (if (null? lst)
      (cons a seen-inexact)
      (let ((b (car lst)))
        (elisp-/-fold (/ a b) (cdr lst) (or seen-inexact (inexact? b))))))

(define elisp-/ (lambda args
                  (if (null? args)
                      ((symbol-function 'signal) 'wrong-type-argument num)
                      (let ((a (car args)))
                        (if (null? (cdr args))
                            (if (exact? a)
                                (inexact->exact (truncate (car (elisp-/-fold 1.0 (list a) #f))))
                                (car (elisp-/-fold 1.0 (list a) #f)))
                            (let ((p (elisp-/-fold a (cdr args) (inexact? a))))
                              (if (cdr p) ; a float was seen among the operands
                                  (car p)
                                  (inexact->exact (truncate (car p))))))))))

(define elisp-1+ (lambda (a)
                   (1+ (check-number-coerce-marker a))))

(define elisp-1- (lambda (a)
                   (1- (check-number-coerce-marker a))))

;;;
;;; Min/Max Operations
;;;

(define elisp-min (lambda args
                    (apply min (map check-number-coerce-marker args))))

(define elisp-max (lambda args
                    (apply max (map check-number-coerce-marker args))))

;;;
;;; Comparison Operations
;;;

(define elisp-= (lambda args
                  (if (apply = (map check-number-coerce-marker args))
                      #t #nil)))

(define elisp-< (lambda args
                  (if (apply < (map check-number-coerce-marker args))
                      #t #nil)))

(define elisp-> (lambda args
                  (if (apply > (map check-number-coerce-marker args))
                      #t #nil)))

(define elisp-<= (lambda args
                   (if (apply <= (map check-number-coerce-marker args))
                       #t #nil)))

(define elisp->= (lambda args
                   (if (apply >= (map check-number-coerce-marker args))
                       #t #nil)))

(define elisp-/= (lambda args
                   (if (apply = (map check-number-coerce-marker args))
                       #nil #t)))

;;;
;;; Bitwise Operations
;;;

(define elisp-logand (lambda args
                       (map (lambda (num)
                              (unless (and (integer? num) (exact? num))
                                ((symbol-function 'signal) 'wrong-type-argument num)))
                            args)
                       (apply logand (map check-number-coerce-marker args))))

;;;
;;; Trigonometric Functions
;;;

;; Note: cos, sin, tan, acos, asin, atan are directly mapped from Guile

;;;
;;; Exponential & Logarithmic Functions
;;;

;; Note: abs, sqrt, exp, expt are directly mapped from Guile

(define elisp-log
  (lambda* (num #:optional base)
    (if (not base)
        (log num)
        (if (= base 10.0)
            (log10 num)
            (/ (log num) (log base))))))

;;;
;;; Rounding & Truncation Functions
;;;

(define elisp-truncate
  (lambda* (num #:optional div)
    (inexact->exact
     (if (not div)
         (truncate num)
         (truncate-quotient num div)))))

(define elisp-ceiling
  (lambda* (num #:optional div)
    (inexact->exact
     (if (not div)
         (ceiling num)
         (ceiling-quotient num div)))))

(define elisp-floor
  (lambda* (num #:optional div)
    (inexact->exact
     (if (not div)
         (floor num)
         (floor-quotient num div)))))

(define elisp-round
  (lambda* (num #:optional div)
    (inexact->exact
     (if (not div)
         (round num)
         (round-quotient num div)))))

;;;
;;; Floating-Point Rounding Functions
;;;

(define elisp-ftruncate
  (lambda (num)
    (unless (and (real? num) (not (exact? num)))
      ((symbol-function 'signal) 'wrong-type-argument num))
    (exact->inexact (truncate num))))

(define elisp-fceiling
  (lambda (num)
    (unless (and (real? num) (not (exact? num)))
      ((symbol-function 'signal) 'wrong-type-argument num))
    (exact->inexact (ceiling num))))

(define elisp-ffloor
  (lambda (num)
    (unless (and (real? num) (not (exact? num)))
      ((symbol-function 'signal) 'wrong-type-argument num))
    (exact->inexact (floor num))))

(define elisp-fround
  (lambda (num)
    (unless (and (real? num) (not (exact? num)))
      ((symbol-function 'signal) 'wrong-type-argument num))
    (exact->inexact (round num))))

;;;
;;; Special Floating-Point Predicates
;;;

(define elisp-isnan
  (lambda (num)
    (unless (and (real? num) (not (exact? num)))
      ((symbol-function 'signal) 'wrong-type-argument num))
    (nan? num)))

;;;
;;; Modulo & Remainder Operations
;;;

(define elisp-% (lambda (a b)
                  (remainder (check-number-coerce-marker a)
                             (check-number-coerce-marker b))))

(define elisp-mod (lambda (a b)
                    ((if (or (inexact? a) (inexact? b))
                         euclidean-remainder
                         modulo)
                     (check-number-coerce-marker a)
                     (check-number-coerce-marker b))))

;;;
;;; Registration with Elisp symbol table
;;; NOTE: All registrations commented out to avoid conflicts with prelude/load.scm
;;; These functions are defined here but registered in load.scm for now.
;;; Once we migrate functions from load.scm to this module, we can uncomment
;;; the registrations incrementally.
;;;

;; Basic arithmetic
;; (set-symbol-function! '+ elisp-+)
;; (set-symbol-function! '- elisp--)
;; (set-symbol-function! '* elisp-*)
;; (set-symbol-function! '/ elisp-/)
;; (set-symbol-function! '1+ elisp-1+)
;; (set-symbol-function! '1- elisp-1-)

;; Min/Max
;; (set-symbol-function! 'min elisp-min)
;; (set-symbol-function! 'max elisp-max)

;; Comparisons
;; (set-symbol-function! '= elisp-=)
;; (set-symbol-function! '< elisp-<)
;; (set-symbol-function! '> elisp->)
;; (set-symbol-function! '<= elisp-<=)
;; (set-symbol-function! '>= elisp->=)
;; (set-symbol-function! '/= elisp-/=)

;; Bitwise operations
;; (set-symbol-function! 'logcount logcount)
;; (set-symbol-function! 'lognot lognot)
;; (set-symbol-function! 'logior logior)
;; (set-symbol-function! 'logxor logxor)
;; (set-symbol-function! 'logand elisp-logand)
;; (set-symbol-function! 'ash ash)

;; Trigonometric
;; (set-symbol-function! 'cos cos)
;; (set-symbol-function! 'tan tan)
;; (set-symbol-function! 'sin sin)
;; (set-symbol-function! 'acos acos)
;; (set-symbol-function! 'atan atan)
;; (set-symbol-function! 'asin asin)

;; Exponential & Logarithmic
;; (set-symbol-function! 'abs abs)
;; (set-symbol-function! 'sqrt sqrt)
;; (set-symbol-function! 'exp exp)
;; (set-symbol-function! 'expt expt)
;; (set-symbol-function! 'log elisp-log)

;; Rounding & Truncation
;; (set-symbol-function! 'truncate elisp-truncate)
;; (set-symbol-function! 'ceiling elisp-ceiling)
;; (set-symbol-function! 'floor elisp-floor)
;; (set-symbol-function! 'round elisp-round)

;; Floating-point rounding
;; (set-symbol-function! 'ftruncate elisp-ftruncate)
;; (set-symbol-function! 'fceiling elisp-fceiling)
;; (set-symbol-function! 'ffloor elisp-ffloor)
;; (set-symbol-function! 'fround elisp-fround)

;; Special predicates
;; (set-symbol-function! 'isnan elisp-isnan)

;; Modulo & Remainder
;; (set-symbol-function! '% elisp-%)
;; (set-symbol-function! 'mod elisp-mod)
