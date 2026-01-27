(define-module (emacs boot)
  #:use-module (emacs-elisp runtime)
  #:export
   (elisp-cons
    elisp-car
    elisp-cdr
    elisp-car-safe
    elisp-cdr-safe
    elisp-caar
    elisp-cadr
    elisp-cdar
    elisp-cddr
    elisp-list
    elisp-make-list
    elisp-not
    init-boot-registrations))

;;;
;;; Basic Cons Cell Operations (Foundation)
;;;

(define (elisp-cons car cdr)
  "Create a new cons, give it CAR and CDR as components, and return it."
  (cons car cdr))

;; info: (elisp) Cons Cells
(define (elisp-car list)
  "Return the car of LIST. If LIST is nil, return nil.
   Error if LIST is not nil and not a cons cell. See also `car-safe'."
  (cond
    ((null? list) #nil)
    ((eq? list #nil) #nil)
    ((pair? list) (car list))
    (else (error "Wrong type argument: listp" list))))

;; info: (elisp) Cons Cells
(define (elisp-cdr list)
  "Return the cdr of LIST. If LIST is nil, return nil.
   Error if LIST is not nil and not a cons cell. See also `cdr-safe'."
  (cond
    ((null? list) #nil)
    ((eq? list #nil) #nil)
    ((pair? list) (cdr list))
    (else (error "Wrong type argument: listp" list))))

(define (elisp-car-safe object)
  "Return the car of OBJECT if it is a cons cell, or else nil."
  (if (pair? object) (car object) #nil))

(define (elisp-cdr-safe object)
  "Return the cdr of OBJECT if it is a cons cell, or else nil."
  (if (pair? object) (cdr object) #nil))

(define (elisp-caar list) (elisp-car (elisp-car list)))
(define (elisp-cadr list) (elisp-car (elisp-cdr list)))
(define (elisp-cdar list) (elisp-cdr (elisp-car list)))
(define (elisp-cddr list) (elisp-cdr (elisp-cdr list)))

(define (elisp-list . elms)
  elms)

(define (elisp-make-list len obj)
  (make-list len obj))

(define (elisp-not x)
  (if (or (null? x) (eq? x #nil)) #t #nil))

;;

(define (init-boot-registrations)
  "initialize primordial elisp functionality"
  (for-each (lambda (sym-fun)
              (set-symbol-function! (car sym-fun) (cadr sym-fun)))
            `(
              (cons ,elisp-cons)
              (car ,elisp-car)
              (cdr ,elisp-cdr)
              ;; (car-safe ,elisp-car-safe)
              ;; (cdr-safe ,elisp-cdr-safe)
              (caar ,elisp-caar)
              (cadr ,elisp-cadr)
              (cdar ,elisp-cdar)
              (cddr ,elisp-cddr)
              (list ,elisp-list)
              (make-list ,elisp-make-list)
              (not ,elisp-not)
              )))
