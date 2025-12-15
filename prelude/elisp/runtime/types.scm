;;; Guilemacs Lisp
;;;
;;; Type Predicates - Foundation Layer
;;;
;;; Module: (language elisp runtime types)
;;; Purpose: Type predicates and type-related operations for Elisp runtime
;;; Loaded into: (language elisp runtime) via primitive-load
;;;
;;; EXPORTS (41 functions):
;;;   Type predicates: symbolp, integerp, floatp, numberp, natnump,
;;;                    characterp, stringp, vectorp, bool-vector-p,
;;;                    arrayp, sequencep, bufferp, subrp
;;;   List predicates: consp, atom, listp, nlistp, null, proper-list-p
;;;   Equality: eq, eql, equal
;;;   Cons operations: cons, car, cdr, car-safe, cdr-safe
;;;   Character ops: max-char
;;;   Utilities: identity, char-table-p
;;;   Extended: bare-symbol-p, boundp, condition-variable-p, hash-table-p,
;;;            integer-or-marker-p, mutexp, recordp, symbol-with-pos-p,
;;;            threadp, user-ptrp, vector-or-char-table-p
;;;   Helpers: elisp-symbol-equal
;;;   Registration: init-types-registrations
;;;
;;; NOTE: Module declaration commented out for Phase 1. Will be enabled
;;;       when load.scm is updated to use use-modules.
;;;
;;; (define-module (language elisp runtime types)
;;;   #:use-module (language elisp runtime)
;;;   #:export (...))

;;;
;;; Type Predicates
;;;

(define (elisp-symbolp object)
  "Return t if OBJECT is a symbol."
  (if (symbol? object) #t #nil))

(define (elisp-integerp object)
  "Return t if OBJECT is an integer."
  (if (and (number? object) (exact? object) (integer? object))
      #t #nil))

(define (elisp-floatp object)
  "Return t if OBJECT is a floating point number."
  (if (and (number? object) (inexact? object)) #t #nil))

(define (elisp-numberp object)
  "Return t if OBJECT is a number (floating point or integer)."
  (if (number? object) #t #nil))

(define (elisp-natnump object)
  "Return t if OBJECT is a nonnegative integer."
  (if (and (number? object) (exact? object) (integer? object) (>= object 0))
      #t #nil))

(define (elisp-characterp object)
  "Return non-nil if OBJECT is a character.
In Emacs Lisp, characters are represented by character codes."
  (if (and (integer? object)
           (>= object 0)
           (<= object 4194303))  ; MAX_CHAR
      #t #nil))

(define (elisp-stringp object)
  "Return t if OBJECT is a string."
  (if (string? object) #t #nil))

(define (elisp-vectorp object)
  "Return t if OBJECT is a vector."
  (if (vector? object) #t #nil))

(define (elisp-bool-vector-p object)
  "Return t if OBJECT is a bool-vector."
  ;; For now, check if it's a bitvector in Guile
  (if (bitvector? object) #t #nil))

(define (elisp-arrayp object)
  "Return t if OBJECT is an array (string, vector, char-table, or bool-vector)."
  (if (or (string? object)
          (vector? object)
          (eq? #t (elisp-char-table-p object))
          (eq? #t (elisp-bool-vector-p object))) #t #nil))

(define (elisp-sequencep object)
  "Return t if OBJECT is a sequence (list or array)."
  (if (or (pair? object) (null? object) (vector? object) (string? object))
      #t #nil))

(define (elisp-bufferp object)
  "Return t if OBJECT is an editor buffer."
  ;; Buffers are Emacs-specific objects, return nil for now
  #nil)

(define (elisp-subrp object)
  "Return t if OBJECT is a built-in function."
  (if (or (procedure? object)
          ;; Check if it's a wrapped C function
          (and (hash-table? object)
               (hash-ref object 'subrp #f)))
      #t #nil))

;;;
;;; List Type Predicates
;;;

(define (elisp-consp object)
  "Return t if OBJECT is a cons cell."
  (if (pair? object) #t #nil))

(define (elisp-atom object)
  "Return t if OBJECT is not a cons cell. This includes nil."
  (if (pair? object) #nil #t))

(define (elisp-listp object)
  "Return t if OBJECT is a list, that is, a cons cell or nil.
Otherwise, return nil."
  (if (or (pair? object) (null? object) (eq? object #nil)) #t #nil))

(define (elisp-nlistp object)
  "Return t if OBJECT is not a list. Lists include nil."
  (if (or (pair? object) (null? object) (eq? object #nil)) #nil #t))

(define (elisp-null object)
  "Return t if OBJECT is nil, and return nil otherwise."
  (if (or (null? object) (eq? object #nil)) #t #nil))

(define (elisp-proper-list-p object)
  "Return OBJECT's length if it is a proper list, nil otherwise.
A proper list is neither circular nor dotted (i.e., its last cdr is nil)."
  (let ((len 0)
        (slow object)
        (fast object))
    ;; Use Floyd's cycle detection algorithm
    (let loop ((current object) (len 0))
      (cond
        ((null? current) len)  ; Proper list - return length
        ((not (pair? current)) 'nil)  ; Dotted list - return nil
        (else
          ;; Check for cycles using tortoise and hare
          (set! fast (if (and (pair? fast) (pair? (cdr fast))) (cddr fast) #f))
          (set! slow (cdr slow))
          (if (and fast (eq? slow fast))
              'nil  ; Circular - return nil
              (loop (cdr current) (+ len 1))))))))

;;;
;;; Equality Predicates
;;;

(define (elisp-eq obj1 obj2)
  "Return t if the two args are the same Lisp object."
  (if (eq? obj1 obj2) #t #nil))

(define (elisp-eql obj1 obj2)
  "Return t if the two args are `eq' or are indistinguishable numbers."
  (if (eqv? obj1 obj2) #t #nil))

(define (elisp-equal obj1 obj2)
  "Return t if two Lisp objects have similar structure and contents."
  (if (equal? obj1 obj2) #t #nil))

;;;
;;; Basic Cons Cell Operations (Foundation)
;;;

(define (elisp-cons car cdr)
  "Create a new cons, give it CAR and CDR as components, and return it."
  (cons car cdr))

(define (elisp-car list)
  "Return the car of LIST. If LIST is nil, return nil.
Error if LIST is not nil and not a cons cell. See also `car-safe'."
  (cond
    ((null? list) #nil)
    ((eq? list #nil) #nil)
    ((pair? list) (car list))
    (else (error "Wrong type argument: listp" list))))

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

;;;
;;; Character Operations
;;;

(define (elisp-max-char)
  "Return the character with the maximum code."
  4194303)  ; MAX_CHAR constant

;;;
;;; Utility Functions
;;;

(define (elisp-identity arg)
  "Return the argument unchanged."
  arg)

;;; Helper for arrayp (placeholder for char-table support)
(define (elisp-char-table-p object)
  "Return t if OBJECT is a char-table."
  ;; Placeholder - char-tables not yet implemented
  #nil)

;;;

(define (elisp-bare-symbol-p object)
  "Return t if OBJECT is a symbol, but not a symbol together with position."
  ;; In Guile implementation, symbols don't have position information
  ;; so this is the same as symbolp for now
  (if (symbol? object) #t #nil))



(define (elisp-boundp symbol)
  "Return t if SYMBOL's value is not void."
  (cond
    ((not (symbol? symbol))
     (error "Wrong type argument: symbolp" symbol))
    (else
     ;; Check if symbol is bound in current environment
     (catch #t
       (lambda ()
         (symbol-bound? symbol)
         #t)
       (lambda (key . args)
         #nil)))))



(define (elisp-condition-variable-p object)
  "Return t if OBJECT is a condition variable."
  ;; Condition variables are Emacs-specific, return nil for now
  #nil)



(define (elisp-hash-table-p obj)
  "Return t if OBJ is a Lisp hash table object."
  ;; Check if it's a Guile hash table
  (if (hash-table? obj) #t #nil))



(define (elisp-integer-or-marker-p object)
  "Return t if OBJECT is an integer or a marker."
  ;; For now, markers are not implemented in Guile, so just check integers
  (if (integer? object) #t #nil))



(define (elisp-mutexp object)
  "Return t if OBJECT is a mutex."
  ;; Mutexes are Emacs-specific, return nil for now
  #nil)



(define (elisp-recordp object)
  "Return t if OBJECT is a record."
  ;; Records are Emacs-specific structures, return nil for now
  #nil)



(define (elisp-symbol-with-pos-p object)
  "Return t if OBJECT is a symbol together with position."
  ;; In Guile implementation, symbols don't have position information
  ;; so this always returns nil
  #nil)



(define (elisp-threadp object)
  "Return t if OBJECT is a thread."
  ;; Threads are Emacs-specific, return nil for now
  #nil)



(define (elisp-user-ptrp object)
  "Return t if OBJECT is a module user pointer."
  ;; User pointers are Emacs module-specific, return nil for now
  #nil)



(define (elisp-vector-or-char-table-p object)
  "Return t if OBJECT is a char-table or vector."
  (if (or (vector? object) (eq? #t (elisp-char-table-p object))) #t #nil))


;;; Registration with Elisp symbol table
;;; NOTE: All registrations commented out to avoid conflicts with prelude/load.scm
;;; These functions are defined here but registered in load.scm for now.
;;; Once we migrate functions from load.scm to this module, we can uncomment
;;; the registrations incrementally.
;;;

;; (set-symbol-function! 'symbolp elisp-symbolp)
;; (set-symbol-function! 'integerp elisp-integerp)
;; (set-symbol-function! 'floatp elisp-floatp)
;; (set-symbol-function! 'numberp elisp-numberp)
;; (set-symbol-function! 'natnump elisp-natnump)
;; (set-symbol-function! 'characterp elisp-characterp)
;; (set-symbol-function! 'stringp elisp-stringp)
;; (set-symbol-function! 'vectorp elisp-vectorp)
;; (set-symbol-function! 'bool-vector-p elisp-bool-vector-p)
;; (set-symbol-function! 'arrayp elisp-arrayp)
;; (set-symbol-function! 'sequencep elisp-sequencep)
;; (set-symbol-function! 'bufferp elisp-bufferp)
;; (set-symbol-function! 'subrp elisp-subrp)

;; (set-symbol-function! 'consp elisp-consp)
;; (set-symbol-function! 'atom elisp-atom)
;; (set-symbol-function! 'listp elisp-listp)
;; (set-symbol-function! 'nlistp elisp-nlistp)
;; (set-symbol-function! 'null elisp-null)
;; (set-symbol-function! 'proper-list-p elisp-proper-list-p)

;; (set-symbol-function! 'eq elisp-eq)
;; (set-symbol-function! 'eql elisp-eql)
;; (set-symbol-function! 'equal elisp-equal)

;; (set-symbol-function! 'cons elisp-cons)
;; (set-symbol-function! 'car elisp-car)
;; (set-symbol-function! 'cdr elisp-cdr)
;; (set-symbol-function! 'car-safe elisp-car-safe)
;; (set-symbol-function! 'cdr-safe elisp-cdr-safe)

;; (set-symbol-function! 'max-char elisp-max-char)

;; (set-symbol-function! 'identity elisp-identity)

;; Registration initialization function
;; Called by load.scm after module is loaded


(define (elisp-symbol-equal sym1 sym2)
  "Compare two symbols directly without converting to strings.
This is more efficient than string comparison of symbol names."
  (cond
    ((and (symbol? sym1) (symbol? sym2))
     (if (eq? sym1 sym2) #t #nil))
    ((symbol? sym1)
     (if (string? sym2)
         (if (string=? (symbol->string sym1) sym2) #t #nil)
         #nil))
    ((symbol? sym2)
     (if (string? sym1)
         (if (string=? sym1 (symbol->string sym2)) #t #nil)
         #nil))
    (else
     (if (equal? sym1 sym2) #t #nil))))

(define (init-types-registrations)
  "Initialize symbol function registrations for types module."
  (set-symbol-function! 'bare-symbol-p elisp-bare-symbol-p)
  (set-symbol-function! 'boundp elisp-boundp)
  (set-symbol-function! 'condition-variable-p elisp-condition-variable-p)
  (set-symbol-function! 'hash-table-p elisp-hash-table-p)
  (set-symbol-function! 'integer-or-marker-p elisp-integer-or-marker-p)
  (set-symbol-function! 'mutexp elisp-mutexp)
  (set-symbol-function! 'recordp elisp-recordp)
  (set-symbol-function! 'symbol-with-pos-p elisp-symbol-with-pos-p)
  (set-symbol-function! 'threadp elisp-threadp)
  (set-symbol-function! 'user-ptrp elisp-user-ptrp)
  (set-symbol-function! 'vector-or-char-table-p elisp-vector-or-char-table-p))
