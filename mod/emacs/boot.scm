(define-module (emacs boot)
  #:use-module (emacs-elisp runtime)
  #:export
   (init-boot-registrations))

;;

(define (init-boot-registrations)
  "initialize primordial elisp functionality"
  (for-each (lambda (sym-fun)
              (set-symbol-function! (car sym-fun) (cadr sym-fun)))
            `(
              )))
