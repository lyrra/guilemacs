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
    elisp-equal-including-properties
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
  (if (or (symbol? object)
          (eq? #t object)
          (eq? #nil object))
      #t #nil))

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
  "Return t if the two args are `eq' or are indistinguishable numbers.
Integers with the same value are `eql'.
Floating-point values with the same sign, exponent and fraction are `eql'.
This differs from numeric comparison: (eql 0.0 -0.0) returns nil and
\(eql 0.0e+NaN 0.0e+NaN) returns t, whereas `=' does the opposite."
  (if (eqv? obj1 obj2) #t #nil))

;; Lazy lookup for emacs-string-equal from text-properties module
;; We use a thunk pattern to avoid circular dependency at load time
(define *emacs-string-equal-proc* #f)
(define *emacs-string-equal-lookup-done* #f)

(define (get-emacs-string-equal)
  "Lazily look up emacs-string-equal from text-properties module."
  (unless *emacs-string-equal-lookup-done*
    (catch #t
      (lambda ()
        (let* ((mod (resolve-module '(emacs text-properties) #:ensure #f))
               (var (and mod (module-variable mod 'emacs-string-equal))))
          (when (and var (variable-bound? var))
            (let ((val (variable-ref var)))
              (when (procedure? val)
                (set! *emacs-string-equal-proc* val))))))
      (lambda (key . args)
        ;; Module not available yet, will retry later
        #f))
    (set! *emacs-string-equal-lookup-done* #t))
  *emacs-string-equal-proc*)

(define (elisp-equal obj1 obj2)
  "Return t if two Lisp objects have similar structure and contents.
They must have the same data type.
Conses are compared by comparing the cars and the cdrs.
Vectors and strings are compared element by element.
Numbers are compared via `eql', so integers do not equal floats.
\(Use `=' if you want integers and floats to be able to be equal.)
Symbols must match exactly."
  ;; Fast path: identical objects are always equal
  (if (eq? obj1 obj2)
      #t
      ;; Get the custom equal proc for emacs-string handling
      (let ((custom-equal (get-emacs-string-equal)))
        (if (and custom-equal
                 (or (string? obj1) (string? obj2)
                     (pair? obj1) (pair? obj2)
                     (vector? obj1) (vector? obj2)))
            ;; Use custom Scheme equal for strings, lists, vectors
            ;; (which may contain emacs-string wrappers)
            (if (custom-equal obj1 obj2) #t #nil)
            ;; Use Guile's equal? for all other types
            (if (equal? obj1 obj2) #t #nil)))))

;; Lazy lookup for text-properties module functions
(define *text-props-module* #f)
(define *text-props-lookup-done* #f)

(define (get-text-props-module)
  "Lazily look up text-properties module."
  (unless *text-props-lookup-done*
    (catch #t
      (lambda ()
        (set! *text-props-module* (resolve-module '(emacs text-properties) #:ensure #f)))
      (lambda (key . args) #f))
    (set! *text-props-lookup-done* #t))
  *text-props-module*)

(define (get-text-props-proc name)
  "Get a procedure from text-properties module."
  (let ((mod (get-text-props-module)))
    (and mod
         (let ((var (module-variable mod name)))
           (and var (variable-bound? var) (variable-ref var))))))

(define (get-string-intervals s)
  "Get intervals from a string or emacs-string.
Plain strings return '(). Uses runtime-safe accessors."
  (if (string? s)
      '()  ; plain string, no intervals
      ;; Assume emacs-string wrapper
      (let ((intervals-proc (get-text-props-proc 'emacs-string-intervals-runtime)))
        (if intervals-proc (intervals-proc s) '()))))

(define (get-string-content s)
  "Get raw string content from string or emacs-string wrapper."
  (if (string? s)
      s
      (let ((unwrap (get-text-props-proc 'unwrap-string)))
        (if unwrap (unwrap s) s))))

(define (compare-string-intervals s1 s2)
  "Compare text properties of two strings.
Returns #t if they have identical properties at all positions."
  (let ((interval-start (get-text-props-proc 'get-interval-start))
        (interval-end (get-text-props-proc 'get-interval-end))
        (interval-plist (get-text-props-proc 'get-interval-plist)))
    (if (not (and interval-start interval-end interval-plist))
        ;; Module not available - plain strings have no properties, so equal
        #t
        ;; Get intervals from both strings
        (let ((i1 (get-string-intervals s1))
              (i2 (get-string-intervals s2)))
          ;; Both have no properties - equal
          (if (and (null? i1) (null? i2))
              #t
              ;; One has properties, other doesn't - not equal
              (if (or (null? i1) (null? i2))
                  #f
                  ;; Both have intervals - compare them
                  (let ((len (string-length (get-string-content s1))))
                    (compare-intervals-walk i1 i2 0 len
                                           interval-start interval-end interval-plist))))))))

(define (compare-intervals-walk i1 i2 pos end interval-start interval-end interval-plist)
  "Walk through interval lists comparing properties.
Returns #t if all properties match, #f otherwise."
  (if (>= pos end)
      #t
      ;; Find intervals containing pos
      (let ((int1 (find-interval-at i1 pos interval-start interval-end))
            (int2 (find-interval-at i2 pos interval-start interval-end)))
        (let ((plist1 (if int1 (interval-plist int1) '()))
              (plist2 (if int2 (interval-plist int2) '())))
          ;; Compare plists using equal (not eq) for values
          (if (not (plists-equal-deep? plist1 plist2))
              #f
              ;; Advance to end of shorter interval
              (let ((end1 (if int1 (interval-end int1) end))
                    (end2 (if int2 (interval-end int2) end)))
                (compare-intervals-walk i1 i2 (min end1 end2) end
                                       interval-start interval-end interval-plist)))))))

(define (find-interval-at intervals pos interval-start interval-end)
  "Find interval containing pos."
  (let loop ((ints intervals))
    (if (null? ints)
        #f
        (let ((int (car ints)))
          (if (and (>= pos (interval-start int))
                   (< pos (interval-end int)))
              int
              (loop (cdr ints)))))))

(define (plists-equal-deep? p1 p2)
  "Compare property lists using equal for values (not eq).
This matches the behavior of equal-including-properties."
  (and (= (length p1) (length p2))
       (let loop ((lst p1))
         (if (null? lst)
             #t
             (let ((key (car lst))
                   (val (cadr lst)))
               (and (plist-has-equal-value? p2 key val)
                    (loop (cddr lst))))))))

(define (plist-has-equal-value? plist key val)
  "Check if plist has key with a value equal to val."
  (let loop ((lst plist))
    (cond
      ((null? lst) #f)
      ((eq? (car lst) key)
       (equal? (cadr lst) val))
      (else (loop (cddr lst))))))

(define (string-like? obj)
  "Return #t if obj is a string or emacs-string wrapper."
  (or (string? obj)
      ;; Check if it's an emacs-string wrapper by trying has-properties?
      ;; or unwrap-string. emacs-string? is a syntax transformer, not callable.
      (let ((unwrap (get-text-props-proc 'unwrap-string)))
        (and unwrap
             (catch #t
               (lambda () (string? (unwrap obj)))
               (lambda (key . args) #f))))))

(define (equal-including-properties-internal o1 o2)
  "Internal recursive comparison including text properties.
Returns Scheme boolean for easier recursion."
  (cond
    ;; Fast path: identical objects
    ((eq? o1 o2) #t)

    ;; Both strings (plain or emacs-string) - compare content and properties
    ((and (string-like? o1) (string-like? o2))
     (and (string=? (unwrap-string-content o1) (unwrap-string-content o2))
          (compare-string-intervals o1 o2)))

    ;; Both lists - recurse on car and cdr
    ((and (pair? o1) (pair? o2))
     (and (equal-including-properties-internal (car o1) (car o2))
          (equal-including-properties-internal (cdr o1) (cdr o2))))

    ;; Both vectors - recurse on elements
    ((and (vector? o1) (vector? o2))
     (and (= (vector-length o1) (vector-length o2))
          (let loop ((i 0))
            (or (>= i (vector-length o1))
                (and (equal-including-properties-internal
                      (vector-ref o1 i) (vector-ref o2 i))
                     (loop (+ i 1)))))))

    ;; Everything else - use Guile's equal?
    (else (equal? o1 o2))))

(define (elisp-equal-including-properties o1 o2)
  "Return t if two Lisp objects have similar structure and contents.
This is like `equal' except that it compares the text properties
of strings.  (`equal' ignores text properties.)"
  (if (equal-including-properties-internal o1 o2) #t #nil))

(define (unwrap-string-content s)
  "Get the raw string content, unwrapping emacs-string if needed."
  (get-string-content s))

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
              (eq ,elisp-eq)
              (eql ,elisp-eql)
              (equal ,elisp-equal)
              (equal-including-properties ,elisp-equal-including-properties)
              ;; (max-char ,elisp-max-char)
              ;; (identity ,elisp-identity)
              )))
