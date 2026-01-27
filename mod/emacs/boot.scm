(define-module (emacs boot)
  #:use-module (emacs-elisp runtime)
  #:export
   (init-boot-registrations))

;;

(define (elisp-boundp x) (symbol-bound? x))
(define (elisp-fboundp x) (symbol-fbound? x))
(define (elisp-makunbound x) (makunbound! x))
(define (elisp-fmakunbound x) (fmakunbound! x))

(define (init-boot-registrations)
  "initialize primordial elisp functionality"
  (for-each (lambda (sym-fun)
              (set-symbol-function! (car sym-fun) (cadr sym-fun)))
            `((boundp ,elisp-boundp)
              (fboundp ,elisp-fboundp)
              (makunbound ,elisp-makunbound)
              (fmakunbound ,elisp-fmakunbound)
              )))
