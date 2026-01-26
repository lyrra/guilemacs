;;; Type Predicates
;;; Purpose: Type predicates and type-related operations for Elisp runtime
;;; Loading: via use-modules in load.scm
;;; Registration: init-types-registrations

(define-module (emacs types)
  #:use-module (emacs-elisp runtime)
  #:export (
    ;; Scheme implementation functions
    elisp-symbolp
    elisp-integerp
    elisp-floatp
    elisp-numberp
    elisp-natnump
    elisp-characterp
    elisp-stringp
    elisp-vectorp
    elisp-bool-vector-p
    elisp-arrayp
    elisp-sequencep
    elisp-bufferp
    elisp-subrp
    elisp-consp
    elisp-atom
    elisp-listp
    elisp-nlistp
    elisp-null
    elisp-proper-list-p
    elisp-eq
    elisp-eql
    elisp-equal
    elisp-cons
    elisp-car
    elisp-cdr
    elisp-car-safe
    elisp-cdr-safe
    elisp-max-char
    elisp-identity
    elisp-char-table-p
    elisp-bare-symbol-p
    elisp-boundp
    elisp-condition-variable-p
    elisp-hash-table-p
    elisp-integer-or-marker-p
    elisp-mutexp
    elisp-recordp
    elisp-symbol-with-pos-p
    elisp-threadp
    elisp-user-ptrp
    elisp-vector-or-char-table-p
    elisp-symbol-equal
    init-types-registrations
  ))

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
  ;; object: const
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
  ;; Check for exact integers (not floats)
  ;; TODO: Add marker check when markers are implemented in Scheme
  (if (and (integer? object) (exact? object))
      #t #nil))

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
  (for-each (lambda (sym-fun)
              (set-symbol-function! (car sym-fun) (cadr sym-fun)))
            `((bare-symbol-p          ,elisp-bare-symbol-p)
              (boundp                 ,elisp-boundp)
              (condition-variable-p   ,elisp-condition-variable-p)
              (hash-table-p           ,elisp-hash-table-p)
              ;(integer-or-marker-p    ,elisp-integer-or-marker-p)
              (mutexp                 ,elisp-mutexp)
              (recordp                ,elisp-recordp)
              (symbol-with-pos-p      ,elisp-symbol-with-pos-p)
              (threadp                ,elisp-threadp)
              (user-ptrp              ,elisp-user-ptrp)
              (vector-or-char-table-p ,elisp-vector-or-char-table-p)
              (sequencep  ,elisp-sequencep)
              (vectorp    ,elisp-vectorp)
              (nlistp     ,elisp-nlistp)
              (listp      ,elisp-listp)
              (atom       ,elisp-atom)
              (consp      ,elisp-consp)
              (symbolp    ,elisp-symbolp)
              (characterp ,elisp-characterp)
              (null       ,elisp-null)
              (numberp    ,elisp-numberp)
              (integerp   ,elisp-integerp)
              ;; (floatp ,elisp-floatp)
              (natnump ,elisp-natnump)
              ;; (stringp ,elisp-stringp)
              ;; (bool-vector-p ,elisp-bool-vector-p)
              ;; (arrayp ,elisp-arrayp)
              ;; (bufferp ,elisp-bufferp)
              ;; (subrp ,elisp-subrp)
              ;; (proper-list-p ,elisp-proper-list-p)
              ;; (eq ,elisp-eq)
              ;; (eql ,elisp-eql)
              ;; (equal ,elisp-equal)
              ;; (cons ,elisp-cons)
              ;; (car ,elisp-car)
              ;; (cdr ,elisp-cdr)
              ;; (car-safe ,elisp-car-safe)
              ;; (cdr-safe ,elisp-cdr-safe)
              ;; (max-char ,elisp-max-char)
              ;; (identity ,elisp-identity)
              )))
