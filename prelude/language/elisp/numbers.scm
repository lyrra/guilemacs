;;; Guilemacs Lisp
;;;
;;; Arithmetic & Math Operations
;;;
;;; Module: (language elisp numbers)
;;; Purpose: Arithmetic and mathematical operations for Elisp runtime
;;; Loading: via use-modules in load.scm
;;;
;;; EXPORTS (32+ functions):
;;;   Basic arithmetic: +, -, *, /, 1+, 1-
;;;   Min/Max: min, max
;;;   Comparisons: =, <, >, <=, >=, /=
;;;   Bitwise: logand, logior, logxor, lognot, logcount, ash
;;;   Trigonometric: cos, sin, tan, acos, asin, atan
;;;   Exponential: abs, sqrt, exp, expt, log
;;;   Rounding: truncate, ceiling, floor, round
;;;   Float rounding: ftruncate, fceiling, ffloor, fround
;;;   Special predicates: isnan
;;;   Modulo/Remainder: %, mod
;;;   Other: byteorder, float, number-to-string, random, number-or-marker-p
;;;   Registration: init-numbers-registrations
;;;
;;; NOTE: Phase 2 - Using flat module naming (language elisp numbers)

(define-module (language elisp numbers)
  #:use-module (rnrs bytevectors)
  #:use-module (emacs-elisp runtime)
  #:export (
    ;; Scheme implementation functions
    elisp-+
    elisp--
    elisp-*
    elisp-/
    elisp-1+
    elisp-1-
    elisp-min
    elisp-max
    elisp-=
    elisp-<
    elisp->
    elisp-<=
    elisp->=
    elisp-/=
    elisp-logand
    elisp-log
    elisp-truncate
    elisp-ceiling
    elisp-floor
    elisp-round
    elisp-ftruncate
    elisp-fceiling
    elisp-ffloor
    elisp-fround
    elisp-isnan
    elisp-%
    elisp-mod
    elisp-byteorder
    elisp-float
    elisp-number-to-string
    elisp-random
    elisp-number-or-marker-p
    init-numbers-registrations
  ))

;;;
;;;
;;;

;; The C primitive check-number-coerce-marker is defined in src/data.c
;; and exported in src/emacs.c via scm_c_define_gsubr
;; Since this file uses define-module, it doesn't automatically have access to the C primitives
;; We'll just stub it here and let the actual C function be called via a different mechanism
;; Real fix: Have the comparison operators call the C function directly
(define (check-number-coerce-marker obj)
  "Check if OBJ is a number, or a marker that can be coerced to a number.
Markers are coerced to their position value."
  (cond
    ((number? obj) obj)

    ;; Check if it's a marker using markerp and extract its position
    ((not (eq? ((symbol-function 'markerp) obj) #nil))
     ;; Call marker-position to get the numeric position
     (let ((pos ((symbol-function 'marker-position) obj)))
       (if (and pos (not (eq? pos #nil)) (number? pos))
           pos
           (error "Wrong type argument: numberp" obj))))
    (else
      (error "Wrong type argument: numberp" obj))))

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

(let-syntax
    ((frob (syntax-rules ()
             ((_ lisp-name fun-name)
              (define fun-name (lambda args
                                 (apply lisp-name (map check-number-coerce-marker args))))))))
  (frob min elisp-min)
  (frob max elisp-max))

;;;
;;; Comparison Operations
;;;

(let-syntax
    ((frob (syntax-rules ()
             ((_ lisp-name fun-name)
              (define fun-name (lambda args
                                 (if (apply lisp-name (map check-number-coerce-marker args))
                                     #t #nil)))))))
  (frob = elisp-=)
  (frob < elisp-<)
  (frob > elisp->)
  (frob <= elisp-<=)
  (frob >= elisp->=))

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

(let-syntax
    ((frob (syntax-rules ()
             ((_ el-name scm-op-arity1 scm-op-arity2)
              (define el-name
                (lambda* (num #:optional div)
                  (inexact->exact
                   (if (not div)
                       (scm-op-arity1 num)
                       (scm-op-arity2 num div)))))))))
  (frob elisp-truncate truncate truncate-quotient)
  (frob elisp-ceiling  ceiling  ceiling-quotient)
  (frob elisp-floor    floor    floor-quotient)
  (frob elisp-round    round    round-quotient))

;;;
;;; Floating-Point Rounding Functions
;;;

(let-syntax
    ((frob (syntax-rules ()
             ((_ el-name scm-op)
              (define el-name
                (lambda (num)
                  (unless (and (real? num) (not (exact? num)))
                    ((symbol-function 'signal) 'wrong-type-argument num))
                  (exact->inexact (scm-op num))))))))
  (frob elisp-ftruncate truncate)
  (frob elisp-fceiling ceiling)
  (frob elisp-ffloor floor)
  (frob elisp-fround round))

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

(define (elisp-byteorder)
  "Return the byteorder for the machine.
Returns 66 (ASCII uppercase B) for big endian machines or 108 (ASCII
lowercase l) for small endian machines."
  ;; Guile provides the native endianness
  (if (eq? (native-endianness) (endianness big))
      66   ; 'B' for big endian
      108)) ; 'l' for little endian



(define (elisp-float arg)
  "Return the floating point number equal to ARG."
  (cond
    ((integer? arg) (exact->inexact arg))
    ((number? arg) arg)  ; Already a float
    (else (error "Wrong type argument: numberp" arg))))



(define (elisp-number-to-string number)
  "Return the decimal representation of NUMBER as a string."
  (cond
    ((integer? number) (number->string number))
    ((number? number) (number->string number))
    (else (error "Wrong type argument: numberp" number))))



(define (elisp-random limit)
  "Return a pseudo-random integer.
By default, return a fixnum; all fixnums are equally likely.
With positive integer LIMIT, return random integer in interval [0,LIMIT)."
  (cond
    ((or (null? limit) (not limit))
     ;; Return random fixnum - use Guile's random
     (random 536870912))  ; Large range for fixnum
    ((eq? limit #t)
     ;; Seed from system entropy - not implemented in simple version
     #nil)
    ((string? limit)
     ;; Seed from string - not implemented in simple version
     #nil)
    ((and (integer? limit) (> limit 0))
     ;; Return random integer in [0, limit)
     (random limit))
    (else
     (error "Wrong type argument" limit))))



(define (elisp-number-or-marker-p object)
  "Return t if OBJECT is a number or a marker."
  ;; For now, markers are not implemented in Guile, so just check numbers
  (if (number? object) #t #nil))


;;; Registration with Elisp symbol table
;;; NOTE: All registrations commented out to avoid conflicts with prelude/load.scm
;;; These functions are defined here but registered in load.scm for now.
;;; Once we migrate functions from load.scm to this module, we can uncomment
;;; the registrations incrementally.
;;;

;; Basic arithmetic
(set-symbol-function! '+ elisp-+)
(set-symbol-function! '- elisp--)
(set-symbol-function! '* elisp-*)
(set-symbol-function! '/ elisp-/)
(set-symbol-function! '1+ elisp-1+)
(set-symbol-function! '1- elisp-1-)

;; Min/Max
(set-symbol-function! 'min elisp-min)
(set-symbol-function! 'max elisp-max)

;; Comparisons
(set-symbol-function! '= elisp-=)
(set-symbol-function! '< elisp-<)
(set-symbol-function! '> elisp->)
(set-symbol-function! '<= elisp-<=)
(set-symbol-function! '>= elisp->=)
(set-symbol-function! '/= elisp-/=)

;; Bitwise operations
(set-symbol-function! 'logcount logcount)
(set-symbol-function! 'lognot lognot)
(set-symbol-function! 'logior logior)
(set-symbol-function! 'logxor logxor)
(set-symbol-function! 'logand elisp-logand)
(set-symbol-function! 'ash ash)

;; Trigonometric
(set-symbol-function! 'cos cos)
(set-symbol-function! 'tan tan)
(set-symbol-function! 'sin sin)
(set-symbol-function! 'acos acos)
(set-symbol-function! 'atan atan)
(set-symbol-function! 'asin asin)

;; Exponential & Logarithmic
(set-symbol-function! 'abs abs)
(set-symbol-function! 'sqrt sqrt)
(set-symbol-function! 'exp exp)
(set-symbol-function! 'expt expt)
(set-symbol-function! 'log elisp-log)

;; Rounding & Truncation
(set-symbol-function! 'truncate elisp-truncate)
(set-symbol-function! 'ceiling elisp-ceiling)
(set-symbol-function! 'floor elisp-floor)
(set-symbol-function! 'round elisp-round)

;; Floating-point rounding
(set-symbol-function! 'ftruncate elisp-ftruncate)
(set-symbol-function! 'fceiling elisp-fceiling)
(set-symbol-function! 'ffloor elisp-ffloor)
(set-symbol-function! 'fround elisp-fround)

;; Special predicates
(set-symbol-function! 'isnan elisp-isnan)

;; Modulo & Remainder
(set-symbol-function! '% elisp-%)
(set-symbol-function! 'mod elisp-mod)

(set-symbol-function! 'byteorder elisp-byteorder)
(set-symbol-function! 'float elisp-float)
(set-symbol-function! 'number-to-string elisp-number-to-string)
(set-symbol-function! 'random elisp-random)
(set-symbol-function! 'number-or-marker-p elisp-number-or-marker-p)

;; Registration initialization function
;; Called by load.scm after module is loaded
(define (init-numbers-registrations)
  "Initialize symbol function registrations for numbers module."
    (set-symbol-function! '% elisp-%)
  (set-symbol-function! '/ elisp-/)
  (set-symbol-function! '/= elisp-/=)
  (set-symbol-function! '1+ elisp-1+)
  (set-symbol-function! '1- elisp-1-)
  (set-symbol-function! 'abs abs)
  (set-symbol-function! 'acos acos)
  (set-symbol-function! 'ash ash)
  (set-symbol-function! 'asin asin)
  (set-symbol-function! 'atan atan)
  (set-symbol-function! 'cos cos)
  (set-symbol-function! 'exp exp)
  (set-symbol-function! 'expt expt)
  (set-symbol-function! 'isnan
                      (lambda (num)
                        (unless (and (real? num) (not (exact? num)))
                          ((symbol-function 'signal) 'wrong-type-argument num))
                        (nan? num)))
  (set-symbol-function! 'log
  (lambda* (num #:optional base)
    (if (not base)
        (log num)
        (if (= base 10.0)
            (log10 num)
            (/ (log num) (log base))))))
  (set-symbol-function! 'logand elisp-logand)
  (set-symbol-function! 'logcount logcount)
  (set-symbol-function! 'logior logior)
  (set-symbol-function! 'lognot lognot)
  (set-symbol-function! 'logxor logxor)
  (set-symbol-function! 'mod elisp-mod)
  (set-symbol-function! 'sin sin)
  (set-symbol-function! 'sqrt sqrt)
  (set-symbol-function! 'tan tan))
