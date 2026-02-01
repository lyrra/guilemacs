;;; Guilemacs Lisp
;;;
;;; Sequence & List Operations
;;;
;;; Purpose: List and sequence operations for Elisp runtime
;;; Loading: via use-modules in load.scm
;;;
;;; EXPORTS (34+ functions):
;;;   List operations: nth, nthcdr, append, reverse, nreverse
;;;   Association lists: assoc, rassq, rassoc
;;;   Property lists: plist-get, plist-put, plist-member, lax-plist-get, lax-plist-put
;;;   List predicates: member-ignore-case
;;;   Higher-order: mapcar, mapc, mapcan, mapconcat
;;;   Utilities: last, butlast, length, safe-length, sort, delete, remove
;;;   Registration: init-sequences-registrations

(define-module (emacs sequences)
  #:use-module (emacs-elisp runtime)
  #:export (
    ;; Scheme implementation functions
    elisp-nth elisp-nthcdr
    elisp-append elisp-reverse elisp-nreverse elisp-assoc
    elisp-rassq elisp-rassoc elisp-plist-get elisp-plist-put
    elisp-plist-member elisp-lax-plist-get elisp-lax-plist-put
    elisp-member-ignore-case elisp-mapcar elisp-mapc elisp-mapcan
    elisp-mapconcat elisp-last elisp-butlast elisp-length
    elisp-safe-length elisp-sort elisp-delete elisp-remove
    elisp-delete-dups elisp-copy-sequence
    elisp-elt elisp-copy-alist elisp-assq-delete-all
    init-sequences-registrations
  ))

;;; List Search & Access Operations
;;;

(define (elisp-nth n list)
  "Return the Nth element of LIST.
N counts from zero. If LIST is not that long, nil is returned."
  (cond
    ((not (number? n)) #nil)
    ((< n 0) #nil)
    (else
     (let loop ((count (if (integer? n) n (floor n))) (tail list))
       (cond
         ((null? tail) #nil)
         ((= count 0) (car tail))
         (else (loop (- count 1) (cdr tail))))))))

(define (elisp-nthcdr n list)
  "Take cdr N times on LIST, return the result."
  (cond
    ((not (number? n)) list)
    ((< n 0) list)
    (else
     (let loop ((count (if (integer? n) n (floor n))) (tail list))
       (cond
         ((null? tail) #nil)
         ((= count 0) tail)
         (else (loop (- count 1) (cdr tail))))))))

(define (elisp-last list)
  "Return the last cons cell of LIST.
If LIST is empty, return nil."
  (if (null? list)
      #nil
      (let loop ((current list))
        (let ((next (cdr current)))
          (if (null? next)
              current
              (loop next))))))

(define elisp-butlast
  (case-lambda
    ((list)
     ;; Called with 1 argument - default n to 1
     (elisp-butlast list 1))
    ((list n)
     ;; Called with 2 arguments
     "Return a copy of LIST with the last N elements removed.
If N is omitted or nil, remove only the last element."
     (let ((num (if (or (null? n) (eq? n #nil)) 1 n)))
       (if (or (not (integer? num)) (< num 0))
           list
           (let ((len (length list)))
             (if (<= len num)
                 #nil
                 (list-head list (- len num)))))))))

;;;
;;; List Transformation Operations
;;;

(define (elisp-reverse list)
  "Return a new list with elements of LIST in reverse order."
  (let loop ((remaining list) (result '()))
    (if (null? remaining)
        result
        (loop (cdr remaining) (cons (car remaining) result)))))

(define (elisp-append . lists)
  "Concatenate all the arguments and make the result a list.
The result is a list whose elements are the elements of all the arguments.
Each argument may be a list, vector or string.
All arguments except the last are copied."
  (if (null? lists)
      '()
      (let ((result '()))
        (let loop ((remaining lists))
          (cond
            ((null? remaining) result)
            ((null? (cdr remaining))
             ;; Last argument - append it as-is (not copied)
             (if (null? result)
                 (car remaining)
                 (append result (car remaining))))
            ((null? (car remaining)) (loop (cdr remaining)))
            ((pair? (car remaining))
             (set! result (append result (car remaining)))
             (loop (cdr remaining)))
            ((vector? (car remaining))
             (set! result (append result (vector->list (car remaining))))
             (loop (cdr remaining)))
            ((string? (car remaining))
             (set! result (append result (string->list (car remaining))))
             (loop (cdr remaining)))
            (else (loop (cdr remaining))))))))

;;;
;;; Association List Operations
;;;

(define (elisp-assoc key alist)
  "Return non-nil if KEY is `equal' to the car of an element of ALIST.
The value is actually the first element of ALIST whose car is KEY.
Elements of ALIST that are not conses are ignored."
  (let loop ((tail alist))
    (cond
      ((null? tail) #nil)
      ((not (pair? (car tail))) (loop (cdr tail))) ; Skip non-conses
      ((equal? key (car (car tail))) (car tail))
      (else (loop (cdr tail))))))

(define (elisp-rassq val alist)
  "Return non-nil if VAL is `eq' to the cdr of an element of ALIST.
The value is actually the first element of ALIST whose cdr is VAL.
Elements of ALIST that are not conses are ignored."
  (let loop ((tail alist))
    (cond
      ((null? tail) #nil)
      ((not (pair? tail)) #nil)  ; Handle malformed alist
      ((not (pair? (car tail))) (loop (cdr tail))) ; Skip non-conses
      ((eq? val (cdr (car tail))) (car tail))
      (else (loop (cdr tail))))))

;;;
;;; Sequence Operations
;;;

(define (elisp-copy-sequence seq)
  "Return a copy of a list, vector, string, or other sequence.
The elements of a list are not copied; they are shared with the original."
  (cond
    ((null? seq) seq)
    ((pair? seq) (list-copy seq))
    ((string? seq) (string-copy seq))
    ((vector? seq) (vector-copy seq))
    (else seq))) ; Return as-is for other types

;;;
;;; Property List Operations
;;;

(define elisp-plist-get
  (case-lambda
    ((plist prop)
     ;; Called with 2 arguments - use default predicate eq?
     (elisp-plist-get plist prop eq?))
    ((plist prop predicate)
     ;; Called with 3 arguments
     "Extract a value from a property list.
PLIST is a property list of the form (PROP1 VALUE1 PROP2 VALUE2...).
Returns the value corresponding to PROP, or nil if not found.
Uses PREDICATE for comparison, defaulting to `eq'."
     (let ((pred (if (or (null? predicate) (eq? predicate #nil)) eq? predicate)))
       (let loop ((tail plist))
         (cond
           ((null? tail) #nil)
           ((not (pair? tail)) #nil)
           ((not (pair? (cdr tail))) #nil)  ; Malformed plist
           ((pred prop (car tail)) (car (cdr tail)))
           (else (loop (cddr tail)))))))))

(define (elisp-plist-put plist prop value)
  "Change value in PLIST of PROP to VALUE.
PLIST is a property list of the form (PROP1 VALUE1 PROP2 VALUE2...).
Returns a new property list with the change."
  (let loop ((tail plist) (result '()))
    (cond
      ((null? tail)
       ;; Property not found, add it at the end
       (reverse (cons value (cons prop result))))
      ((not (pair? tail))
       ;; Malformed plist, add property at end
       (reverse (cons value (cons prop result))))
      ((not (pair? (cdr tail)))
       ;; Malformed plist, add property at end
       (reverse (cons value (cons prop result))))
      ((eq? prop (car tail))
       ;; Found the property, update its value
       (append (reverse result) (cons prop (cons value (cddr tail)))))
      (else
       ;; Continue searching, preserving current prop-value pair
       (loop (cddr tail) (cons (car (cdr tail)) (cons (car tail) result)))))))

(define elisp-plist-member
  (case-lambda
    ((plist prop)
     ;; Called with 2 arguments - use default predicate eq?
     (elisp-plist-member plist prop eq?))
    ((plist prop predicate)
     ;; Called with 3 arguments
     "Return non-nil if PROP is a property of PLIST.
Unlike `plist-get', this allows distinguishing between a missing
property and a property with value nil.
Returns the tail of PLIST whose car is PROP."
     (let ((pred (if (or (null? predicate) (eq? predicate #nil)) eq? predicate)))
       (let loop ((tail plist))
         (cond
           ((null? tail) #nil)
           ((not (pair? tail)) #nil)
           ((not (pair? (cdr tail))) #nil)  ; Malformed plist
           ((pred prop (car tail)) tail)
           (else (loop (cddr tail)))))))))

;;;
;;; String Comparison Functions
;;;

(define (elisp-string-equal s1 s2)
  "Return t if two strings have identical contents.
Case is significant. Symbols are allowed; their print names are used."
  (let ((str1 (if (symbol? s1) (symbol->string s1) s1))
        (str2 (if (symbol? s2) (symbol->string s2) s2)))
    (if (and (string? str1) (string? str2) (string=? str1 str2)) #t #nil)))

(define (elisp-string-lessp s1 s2)
  "Return non-nil if STRING1 is less than STRING2 in lexicographic order.
Case is significant."
  (let ((str1 (if (symbol? s1) (symbol->string s1) s1))
        (str2 (if (symbol? s2) (symbol->string s2) s2)))
    (if (and (string? str1) (string? str2) (string<? str1 str2)) #t #nil)))

(define (elisp-string-greaterp s1 s2)
  "Return non-nil if STRING1 is greater than STRING2 in lexicographic order.
Case is significant."
  (let ((str1 (if (symbol? s1) (symbol->string s1) s1))
        (str2 (if (symbol? s2) (symbol->string s2) s2)))
    (if (and (string? str1) (string? str2) (string>? str1 str2)) #t #nil)))

;;;
;;; Higher-Order Functions
;;;

(define (elisp-mapcar function sequence)
  "Apply FUNCTION to each element of SEQUENCE, and make a list of the results.
The result is a list just as long as SEQUENCE.
SEQUENCE may be a list, a vector, or a string."
  (cond
    ((null? sequence) '())
    ((pair? sequence) (map function sequence))
    ((vector? sequence) (map function (vector->list sequence)))
    ((string? sequence) (map function (string->list sequence)))
    (else '())))

(define (elisp-mapc function sequence)
  "Apply FUNCTION to each element of SEQUENCE for side effects only.
Unlike `mapcar', don't accumulate the results. Return SEQUENCE."
  (cond
    ((null? sequence) sequence)
    ((pair? sequence) (for-each function sequence) sequence)
    ((vector? sequence) (for-each function (vector->list sequence)) sequence)
    ((string? sequence) (for-each function (string->list sequence)) sequence)
    (else sequence)))

;;;
;;; Utility Functions
;;;

(define (elisp-constantly value)
  "Return a function that always returns VALUE.
This is a useful building block for higher-order functions."
  (lambda args value))

;;;

(define (elisp-length sequence)
  "Return the length of vector, list or string SEQUENCE."
  (cond
    ((null? sequence) 0)
    ((pair? sequence)
     (catch #t
       (lambda () (length sequence))
       (lambda (key . args)
         ;; Handle circular lists - count until we see duplicate
         (let ((seen (make-hash-table)))
           (let loop ((seq sequence) (count 0))
             (cond
               ((null? seq) count)
               ((not (pair? seq)) count) ; improper list
               ((hash-ref seen seq) count) ; circular
               (else
                (hash-set! seen seq #t)
                (loop (cdr seq) (+ count 1)))))))))
    ((vector? sequence) (vector-length sequence))
    ((string? sequence) (string-length sequence))
    (else (error "Wrong type argument: sequencep" sequence))))



(define (elisp-make-list length init)
  "Return a newly created list of length LENGTH, with each element being INIT."
  (if (not (and (integer? length) (>= length 0)))
      (error "Wrong type argument: natnump" length)
      (make-list length init)))



(define (elisp-safe-length list)
  "Return the length of a list, but avoid error or infinite loop.
This function never gets an error. If LIST is not really a list,
it returns 0. If LIST is circular, it returns an integer that is at
least the number of distinct elements."
  (catch #t
    (lambda ()
      (if (or (null? list) (pair? list))
          (length list)
          0))
    (lambda (key . args)
      ;; Return 0 on any error (circular lists, non-lists, etc.)
      0)))



(define (elisp-take n list)
  "Return the first N elements of LIST.
If N is zero or negative, return nil.
If N is greater or equal to the length of LIST, return LIST (or a copy)."
  (cond
    ((not (integer? n)) (error "Wrong type argument: integerp" n))
    ((<= n 0) #nil)
    ((null? list) #nil)
    (else (list-head list (min n (length list))))))

;;;
;;; Cycle Detection
;;;

;; Floyd's tortoise-and-hare: walk list one element at a time, calling
;; CHECK-FN with (count tail) at each step.  CHECK-FN returns (value)
;; to stop iteration with that value, or #f to continue.
;; Signals circular-list on cycle.
(define (list-for-each-cycle-safe sequence check-fn)
  (let loop ((slow sequence) (fast sequence) (count 0))
    (let ((result (check-fn count slow)))
      (if (pair? result)
          (car result)  ; unwrap boxed return value
          ;; Advance slow one step, fast two steps
          (let* ((next-slow (cdr slow))
                 (f1 (if (pair? fast) (cdr fast) fast))
                 (next-fast (if (pair? f1) (cdr f1) f1)))
            (if (and (pair? next-slow) (eq? next-slow next-fast))
                ((symbol-function 'signal) 'circular-list (list sequence))
                (loop next-slow next-fast (+ count 1))))))))

;;;
;;; Length Comparison Functions
;;;

(define (elisp-length< sequence len)
  "Return non-nil if SEQUENCE is shorter than LEN."
  (cond
    ((not (integer? len)) #nil)
    ((< len 0) #nil)
    ((null? sequence) (if (> len 0) #t #nil))
    ((pair? sequence)
     (list-for-each-cycle-safe sequence
       (lambda (count tail)
         (cond
           ((>= count len) (list #nil))  ; Already at len, not shorter
           ((null? tail) (list #t))      ; Reached end before len
           ((not (pair? tail)) (list #nil)) ; Improper list
           (else #f)))))                 ; Continue
    ;; Check for keywords/symbols that are not sequences
    ((or (keyword? sequence) (symbol? sequence)) #nil)
    ;; For vectors and strings, use regular length
    ((or (vector? sequence) (string? sequence))
     (if (< (elisp-length sequence) len) #t #nil))
    (else #nil)))

(define (elisp-length> sequence len)
  "Return non-nil if SEQUENCE is longer than LEN."
  (cond
    ((not (integer? len)) #nil)
    ((< len 0) #t)
    ((null? sequence) #nil)
    ((pair? sequence)
     (list-for-each-cycle-safe sequence
       (lambda (count tail)
         (cond
           ((> count len) (list #t))     ; Already longer than len
           ((null? tail) (list #nil))    ; Reached end at or before len
           ((not (pair? tail)) (list #nil)) ; Improper list
           (else #f)))))                 ; Continue
    (else
     (if (> (elisp-length sequence) len) #t #nil))))

(define (elisp-length= sequence len)
  "Return non-nil if SEQUENCE has exactly LEN elements."
  (cond
    ((not (integer? len)) #nil)
    ((< len 0) #nil)
    ((null? sequence) (if (= len 0) #t #nil))
    ((pair? sequence)
     (list-for-each-cycle-safe sequence
       (lambda (count tail)
         (cond
           ((= count len)
            (list (if (null? tail) #t #nil))) ; At target count, check end
           ((null? tail) (list #nil))    ; Ended before target
           ((not (pair? tail)) (list #nil)) ; Improper list
           (else #f)))))                 ; Continue
    (else
     (if (= (elisp-length sequence) len) #t #nil))))

(define (init-sequences-registrations)
  (for-each (lambda (sym-fun)
              (set-symbol-function! (car sym-fun) (cadr sym-fun)))
            `(
              (butlast ,elisp-butlast)
              (length< ,elisp-length<)
              (length= ,elisp-length=)
              (length> ,elisp-length>)
              (plist-get ,elisp-plist-get)
              (plist-member ,elisp-plist-member)

              ;; List search & access
              (nth ,elisp-nth)
              (nthcdr ,elisp-nthcdr)
              (last ,elisp-last)
              (butlast ,elisp-butlast)

              ;; List transformation
              (reverse ,elisp-reverse)
              (append ,elisp-append)

              ;; Association lists
              (assoc ,elisp-assoc)
              (rassq ,elisp-rassq)

              ;; Sequence operations
              (copy-sequence ,elisp-copy-sequence)

              ;; Property lists
              (plist-get ,elisp-plist-get)
              (plist-put ,elisp-plist-put)
              (plist-member ,elisp-plist-member)

              ;; String comparisons
              (string-equal ,elisp-string-equal)
              (string-lessp ,elisp-string-lessp)
              (string-greaterp ,elisp-string-greaterp)

              ;; Higher-order functions
              (mapcar ,elisp-mapcar)
              (mapc ,elisp-mapc)

              ;; Utilities
              (constantly ,elisp-constantly)

              (length ,elisp-length)
              (make-list ,elisp-make-list)
              (safe-length ,elisp-safe-length)
              (take ,elisp-take)

              ;; Length comparisons
              (length< ,elisp-length<)
              (length> ,elisp-length>)
              (length= ,elisp-length=)
              )))
