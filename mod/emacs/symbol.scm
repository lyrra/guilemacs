(define-module (emacs symbol)
  #:use-module ((emacs-elisp runtime)
                #:select (set-symbol-function!))
  #:declarative? #t
  #:export
   (init-symbol-registrations))

(define (init-symbol-registrations)
  (for-each (lambda (sym-fun)
              (set-symbol-function! (car sym-fun) (cadr sym-fun)))
            `((make-symbol ,make-symbol)
              )))
