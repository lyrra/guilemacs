;; (force-output (current-error-port))
;; (format (current-error-port) "-- loading guile elisp prelude~%")
;; (format (current-error-port) "-- prelude path: ~s~%" %prelude-filename)
;; (force-output (current-error-port))
(set-current-module (resolve-module '(language elisp runtime)))
;; (format (current-error-port) "-- current-module: ~s~%" (current-module))
;; (force-output (current-error-port))

(use-modules (language elisp emacs))
(use-modules (system foreign-library))

(define elisp-+ (lambda args
                  (apply + (map check-number-coerce-marker args))))
(define elisp-- (lambda args
                  (apply - (map check-number-coerce-marker args))))
(define elisp-* (lambda args
                  (apply * (map check-number-coerce-marker args))))

(set-symbol-function! '+ elisp-+)
(set-symbol-function! '- elisp--)
(set-symbol-function! '* elisp-*)

(set-symbol-function! '/ /)
(set-symbol-function! 'logcount logcount)
(set-symbol-function! 'lognot lognot)
(set-symbol-function! 'logior logior)
(set-symbol-function! 'logxor logxor)
(set-symbol-function! 'ash ash)

(set-symbol-function! 'cos cos)
(set-symbol-function! 'tan tan)
(set-symbol-function! 'sin sin)
(set-symbol-function! 'acos acos)
(set-symbol-function! 'atan atan)
(set-symbol-function! 'asin asin)

(set-symbol-function! 'abs abs)
(set-symbol-function! 'sqrt sqrt)
(set-symbol-function! 'exp exp)
(set-symbol-function! 'expt expt)

(set-symbol-function! 'log
  (lambda* (num #:optional base)
    (if (not base)
        (log num)
        (if (= base 10.0)
            (log10 num)
            (/ (log num) (log base))))))

(let-syntax
    ((frob (syntax-rules ()
             ((_ el-name scm-op-arity1 scm-op-arity2)
              (set-symbol-function! 'el-name
                                    (lambda* (num #:optional div)
                                      (inexact->exact
                                       (if (not div)
                                           (scm-op-arity1 num)
                                           (scm-op-arity2 num div)))))))))
  (frob truncate truncate truncate-quotient)
  (frob ceiling  ceiling  ceiling-quotient)
  (frob floor    floor    floor-quotient)
  (frob round    round    round-quotient))

(let-syntax
    ((frob (syntax-rules ()
             ((_ el-name scm-op)
              (set-symbol-function! 'el-name
                                    (lambda (num)
                                      (unless (and (real? num) (not (exact? num)))
                                        ((symbol-function 'signal) 'wrong-type-argument num))
                                      (exact->inexact (scm-op num))))))))
  (frob ftruncate truncate)
  (frob fceiling ceiling)
  (frob ffloor floor)
  (frob fround round))

(set-symbol-function! 'isnan
                      (lambda (num)
                        (unless (and (real? num) (not (exact? num)))
                          ((symbol-function 'signal) 'wrong-type-argument num))
                        (nan? num)))

(define elisp-% (lambda (a b)
                  (remainder (check-number-coerce-marker a)
                             (check-number-coerce-marker b))))

(set-symbol-function! '% elisp-%)

(define elisp-mod (lambda (a b)
                    ((if (or (inexact? a) (inexact? b))
                         euclidean-remainder
                         modulo)
                     (check-number-coerce-marker a)
                     (check-number-coerce-marker b))))

(set-symbol-function! 'mod elisp-mod)

;; (format (current-error-port) "-- done loading guile elisp prelude~%")
;; (force-output (current-error-port))
