(define-module (emacs debug)
  #:use-module (emacs-elisp runtime)
  #:export
   (init-debug-registrations))

;

(define (init-debug-registrations)
  "initialize primordial elisp functionality"
  (for-each (lambda (sym-fun)
              (set-symbol-function! (car sym-fun) (cadr sym-fun)))
            `()))
