(use-modules (language elisp runtime))

; (format #t "-- loading guile elisp prelude~%")
; (format #t "-- prelude path: ~s~%" %prelude-filename)

(set-symbol-function! '/ /)
(set-symbol-function! 'logcount logcount)
(set-symbol-function! 'lognot lognot)
(set-symbol-function! 'logior logior)
(set-symbol-function! 'logxor logxor)
(set-symbol-function! 'ash ash)
