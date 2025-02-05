(use-modules (language elisp runtime))

; (format #t "-- loading guile elisp prelude~%")
; (format #t "-- prelude path: ~s~%" %prelude-filename)

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

(set-symbol-function! 'ceiling
  (lambda* (num #:optional div)
    (inexact->exact
     (if (not div)
         (ceiling num)
         (ceiling-quotient num div)))))

(set-symbol-function! 'floor
  (lambda* (num #:optional div)
    (inexact->exact
     (if (not div)
         (floor num)
         (floor-quotient num div)))))

(set-symbol-function! 'round
  (lambda* (num #:optional div)
    (inexact->exact
     (if (not div)
         (round num)
         (round-quotient num div)))))

(set-symbol-function! 'truncate
  (lambda* (num #:optional div)
    (inexact->exact
     (if (not div)
         (truncate num)
         (truncate-quotient num div)))))
