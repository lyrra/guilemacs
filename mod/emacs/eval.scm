(define-module (emacs eval)
  #:use-module ((emacs-elisp runtime)
                #:select (set-symbol-function!))
  #:declarative? #t
  #:export
   (init-eval-registrations))

(define (init-eval-registrations)
  (for-each (lambda (sym-fun)
              (set-symbol-function! (car sym-fun) (cadr sym-fun)))
            `((values ,values)
              )))
