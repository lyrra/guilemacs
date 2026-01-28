(define-module (emacs list)
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
    elisp-delq elisp-remq
    init-list-registrations))

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
  (if (nil? x) #t #nil))

(define (elisp-rplaca cell x)
  (set-car! cell x))

(define (elisp-rplacd cell x)
  (set-cdr! cell x))

(define (elisp-delq elt list)
  "Delete members of LIST which are `eq' to ELT, and return the result.
More precisely, this function skips any members `eq' to ELT at the
front of LIST, then removes members `eq' to ELT from the remaining
sublist by modifying its list structure, then returns the resulting list."
  ; FIX: could probably use a simple destructive filter:
  (filter! (lambda (x) (not (eq? elt x))) list)
  (let skip-front ((tail list))
    (cond
      ((or (null? tail) (eq? tail #nil)) #nil)
      ((eq? elt (car tail)) (skip-front (cdr tail)))
      (else
       (let remove-rest ((prev tail) (curr (cdr tail)))
         (cond
           ((or (null? curr) (eq? curr #nil)) tail)
           ((eq? elt (car curr))
            (set-cdr! prev (cdr curr))
            (remove-rest prev (cdr curr)))
           (else
            (remove-rest curr (cdr curr)))))))))

(define (elisp-remq elt list)
  "Return a copy of LIST with all elements `eq' to ELT removed."
  (let loop ((tail list) (result '()))
    (cond
      ((null? tail) (reverse result))
      ((eq? elt (car tail)) (loop (cdr tail) result))
      (else (loop (cdr tail) (cons (car tail) result))))))

(define (elisp-assq key alist)
  "Return non-nil if KEY is `eq' to the car of an element of ALIST.
The value is actually the first element of ALIST whose car is KEY.
Elements of ALIST that are not conses are ignored."
  (let loop ((tail alist))
    (cond
      ((or (null? tail) (eq? #nil tail)) #nil)
      ((not (pair? (car tail))) (loop (cdr tail))) ; Skip non-conses
      ((eq? key (car (car tail))) (car tail))
      (else (loop (cdr tail))))))

(define (elisp-memq elt list)
  "Return non-nil if ELT is an element of LIST. Comparison done with `eq'.
The value is actually the tail of LIST whose car is ELT."
  (or (memq elt list) #nil))

(define (elisp-memql elt list)
  "Return non-nil if ELT is an element of LIST.  Comparison done with `eql'.
The value is actually the tail of LIST whose car is ELT."
  (or (memv elt list) #nil))

(define (elisp-member elt list)
  "Return non-nil if ELT is an element of LIST. Comparison done with `equal'.
The value is actually the tail of LIST whose car is ELT."
  (or (member elt list) #nil))

;;

(define (init-list-registrations)
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
              (rplaca ,elisp-rplaca)
              (rplacd ,elisp-rplacd)
              (delq ,elisp-delq)
              (remq ,elisp-remq)
              (assq ,elisp-assq)
              (memq ,elisp-memq)
              (memql ,elisp-memql)
              (member ,elisp-member)
              )))
