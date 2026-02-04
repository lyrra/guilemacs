(define-module (emacs list)
  #:use-module (emacs-elisp runtime)
  #:declarative? #t
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
    elisp-delq elisp-remq elisp-assq
    nil-terminate!
    init-list-registrations))

;;;
;;; Basic Cons Cell Operations (Foundation)
;;;

(define-elisp-inline (cons a d)
  "Create a new cons, give it A and D as components, and return it."
  (cons a d))

;; info: (elisp) Cons Cells
(define-elisp-inline (car lst)
  (cond
    ((null? lst) #nil)
    ((eq? lst #nil) #nil)
    ((pair? lst) (car lst))
    (else (error "Wrong type argument: listp" lst))))

;; info: (elisp) Cons Cells
(define-elisp-inline (cdr lst)
  (cond
    ((null? lst) #nil)
    ((eq? lst #nil) #nil)
    ((pair? lst) (cdr lst))
    (else (error "Wrong type argument: listp" lst))))

(define-elisp-inline (car-safe object)
  "Return the car of OBJECT if it is a cons cell, or else nil."
  (if (pair? object) (car object) #nil))

(define-elisp-inline (cdr-safe object)
  "Return the cdr of OBJECT if it is a cons cell, or else nil."
  (if (pair? object) (cdr object) #nil))

(define-elisp-inline (caar lst) (elisp-car (elisp-car lst)))
(define-elisp-inline (cadr lst) (elisp-car (elisp-cdr lst)))
(define-elisp-inline (cdar lst) (elisp-cdr (elisp-car lst)))
(define-elisp-inline (cddr lst) (elisp-cdr (elisp-cdr lst)))

(define-elisp-inline (setcar cell newcar)
  "Set the car of CELL to be NEWCAR.  Returns NEWCAR."
  (if (pair? cell)
      (begin
        (set-car! cell newcar)
        newcar)
    (error "wrong-type-argument: consp")))

(define-elisp-inline (setcdr cell newcdr)
  "Set the cdr of CELL to be NEWCDR.  Returns NEWCDR."
  (if (pair? cell)
      (begin
        (set-cdr! cell newcdr)
        newcdr)
    (error "wrong-type-argument consp")))

(define (nil-terminate! lst)
  "Re-terminate a Guile ()-list with Elisp #nil."
  (if (null? lst)
      #nil
      (begin
        (let loop ((tail lst))
          (if (null? (cdr tail))
              (set-cdr! tail #nil)
              (loop (cdr tail))))
        lst)))

(define-elisp-inline (list . elms)
  (nil-terminate! elms))

(define-elisp-inline (make-list len obj)
  (make-list len obj))

(define-elisp-inline (not x)
  (if (nil? x) #t #nil))

(define-elisp-inline (rplaca cell x)
  (set-car! cell x))

(define-elisp-inline (rplacd cell x)
  (set-cdr! cell x))

(define (elisp-delq elt lst)
  "Delete members of LIST which are `eq' to ELT, and return the result.
More precisely, this function skips any members `eq' to ELT at the
front of LIST, then removes members `eq' to ELT from the remaining
sublist by modifying its list structure, then returns the resulting list."
  ; FIX: could probably use a simple destructive filter:
  (filter! (lambda (x) (not (eq? elt x))) lst)
  (let skip-front ((tail lst))
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

(define (elisp-remq elt lst)
  "Return a copy of LIST with all elements `eq' to ELT removed."
  (let loop ((tail lst) (result '()))
    (cond
      ((null? tail) (reverse result))
      ((eq? elt (car tail)) (loop (cdr tail) result))
      (else (loop (cdr tail) (cons (car tail) result))))))

(define (elisp-assq key alst)
  "Return non-nil if KEY is `eq' to the car of an element of ALIST.
The value is actually the first element of ALIST whose car is KEY.
Elements of ALIST that are not conses are ignored."
  (let loop ((tail alst))
    (cond
      ((or (null? tail) (eq? #nil tail)) #nil)
      ((not (pair? (car tail))) (loop (cdr tail))) ; Skip non-conses
      ((eq? key (car (car tail))) (car tail))
      (else (loop (cdr tail))))))

(define-elisp-inline (memq elt lst)
  "Return non-nil if ELT is an element of LIST. Comparison done with `eq'.
The value is actually the tail of LIST whose car is ELT."
  (or (memq elt lst) #nil))

(define-elisp-inline (memql elt lst)
  "Return non-nil if ELT is an element of LIST.  Comparison done with `eql'.
The value is actually the tail of LIST whose car is ELT."
  (or (memv elt lst) #nil))

(define-elisp-inline (member elt lst)
  "Return non-nil if ELT is an element of LIST. Comparison done with `equal'.
The value is actually the tail of LIST whose car is ELT."
  (or (member elt lst) #nil))

;;

(define (init-list-registrations)
  "initialize primordial elisp functionality"
  ;; Register non-inlined primitives
  (for-each (lambda (sym-fun)
              (format (current-error-port) "-- registering ~s~%" sym-fun)
              (set-symbol-function! (car sym-fun) (cadr sym-fun)))
            `((delq ,elisp-delq)
              (remq ,elisp-remq)
              (assq ,elisp-assq)
              (memq ,elisp-memq)
              (memql ,elisp-memql)
              (member ,elisp-member)
              )))
