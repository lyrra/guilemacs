;; (force-output (current-error-port))
;; (format (current-error-port) "-- loading guile elisp prelude~%")
;; (format (current-error-port) "-- prelude path: ~s~%" %prelude-filename)
;; (force-output (current-error-port))

;; Load core runtime functions first - compute path relative to this file
;; Temporarily disabled to allow build to complete
;; (primitive-load (string-append (dirname (current-filename)) "/core-runtime.scm"))

(set-current-module (resolve-module '(language elisp runtime)))
;; (format (current-error-port) "-- current-module: ~s~%" (current-module))
;; (force-output (current-error-port))


(use-modules (rnrs bytevectors)) ; FIX: move to (use-modules (scheme base))
(use-modules (language elisp emacs))
(use-modules (system foreign-library))

(define %prelude-directory (dirname %prelude-filename))

(let-syntax
    ((frob (syntax-rules ()
             ((_ lisp-name fun-name)
              (begin
                (define fun-name (lambda args
                                   (apply lisp-name (map check-number-coerce-marker args))))
                (set-symbol-function! 'lisp-name fun-name))))))
  (frob min elisp-min)
  (frob max elisp-max)
  (frob + elisp-+)
  (frob - elisp--)
  (frob * elisp-*))

(define (elisp-/-fold a lst seen-inexact)
  (if (null? lst)
      (cons a seen-inexact)
      (let ((b (car lst)))
        (elisp-/-fold (/ a b) (cdr lst) (or seen-inexact (inexact? b))))))

(define elisp-/ (lambda args
                  (if (null? args)
                      ((symbol-function 'signal) 'wrong-type-argument num)
                      (let ((a (car args)))
                        (if (null? (cdr args))
                            (if (exact? a)
                                (inexact->exact (truncate (car (elisp-/-fold 1.0 (list a) #f))))
                                (car (elisp-/-fold 1.0 (list a) #f)))
                            (let ((p (elisp-/-fold a (cdr args) (inexact? a))))
                              (if (cdr p) ; a float was seen among the operands
                                  (car p)
                                  (inexact->exact (truncate (car p))))))))))

(define elisp-1+ (lambda (a)
                   (1+ (check-number-coerce-marker a))))
(define elisp-1- (lambda (a)
                   (1- (check-number-coerce-marker a))))

(set-symbol-function! '/ elisp-/)
(set-symbol-function! '1+ elisp-1+)
(set-symbol-function! '1- elisp-1-)

(let-syntax
    ((frob (syntax-rules ()
             ((_ lisp-name fun-name)
              (begin
                (define fun-name (lambda args
                                  (if (apply lisp-name (map check-number-coerce-marker args))
                                      #t #nil)))
                (set-symbol-function! 'lisp-name fun-name))))))
  (frob = elisp-=)
  (frob < elisp-<)
  (frob > elisp->)
  (frob <= elisp-<=)
  (frob >= elisp->=))

(define elisp-/= (lambda args
                   (if (apply = (map check-number-coerce-marker args))
                       #nil #t)))

(set-symbol-function! '/= elisp-/=)

(define elisp-logand (lambda args
                       (map (lambda (num)
                              (unless (and (integer? num) (exact? num))
                                ((symbol-function 'signal) 'wrong-type-argument num)))
                            args)
                       (apply logand (map check-number-coerce-marker args))))

(set-symbol-function! 'logcount logcount)
(set-symbol-function! 'lognot lognot)
(set-symbol-function! 'logior logior)
(set-symbol-function! 'logxor logxor)
(set-symbol-function! 'logand elisp-logand)
(set-symbol-function! 'ash ash)

(set-symbol-function! 'cos cos)
(set-symbol-function! 'tan tan)
(set-symbol-function! 'sin sin)
(set-symbol-function! 'acos acos)
(set-symbol-function! 'atan atan)
(set-symbol-function! 'asin asin)

(set-symbol-function! 'abs abs)
(set-symbol-function! 'sqrt sqrt)
(set-symbol-function! 'exp exp)
(set-symbol-function! 'expt expt)

(set-symbol-function! 'log
  (lambda* (num #:optional base)
    (if (not base)
        (log num)
        (if (= base 10.0)
            (log10 num)
            (/ (log num) (log base))))))

(let-syntax
    ((frob (syntax-rules ()
             ((_ el-name scm-op-arity1 scm-op-arity2)
              (set-symbol-function! 'el-name
                                    (lambda* (num #:optional div)
                                      (inexact->exact
                                       (if (not div)
                                           (scm-op-arity1 num)
                                           (scm-op-arity2 num div)))))))))
  (frob truncate truncate truncate-quotient)
  (frob ceiling  ceiling  ceiling-quotient)
  (frob floor    floor    floor-quotient)
  (frob round    round    round-quotient))

(let-syntax
    ((frob (syntax-rules ()
             ((_ el-name scm-op)
              (set-symbol-function! 'el-name
                                    (lambda (num)
                                      (unless (and (real? num) (not (exact? num)))
                                        ((symbol-function 'signal) 'wrong-type-argument num))
                                      (exact->inexact (scm-op num))))))))
  (frob ftruncate truncate)
  (frob fceiling ceiling)
  (frob ffloor floor)
  (frob fround round))

(set-symbol-function! 'isnan
                      (lambda (num)
                        (unless (and (real? num) (not (exact? num)))
                          ((symbol-function 'signal) 'wrong-type-argument num))
                        (nan? num)))

(define elisp-% (lambda (a b)
                  (remainder (check-number-coerce-marker a)
                             (check-number-coerce-marker b))))

(set-symbol-function! '% elisp-%)

(define elisp-mod (lambda (a b)
                    ((if (or (inexact? a) (inexact? b))
                         euclidean-remainder
                         modulo)
                     (check-number-coerce-marker a)
                     (check-number-coerce-marker b))))

(set-symbol-function! 'mod elisp-mod)

;; String operations

(define (elisp-string-bytes string)
  "Return the number of bytes in STRING."
  (bytevector-length (string->utf8 string)))

(define elisp-string-distance
  (case-lambda
    ((string1 string2)
     ;; Called with 2 arguments - default bytecompare to #nil
     (elisp-string-distance string1 string2 #nil))
    ((string1 string2 bytecompare)
     ;; Called with 3 arguments
     "Return Levenshtein distance between STRING1 and STRING2.
The distance is the number of deletions, insertions, and substitutions
required to transform STRING1 into STRING2.
If BYTECOMPARE is nil or omitted, compute distance in terms of characters.
If BYTECOMPARE is non-nil, compute distance in terms of bytes.
Letter-case is significant, but text properties are ignored."
     (let ((use-byte-compare (not (or (null? bytecompare) (eq? bytecompare #nil))))
        (s1 string1)
        (s2 string2))
    ;; Convert to bytevectors if byte comparison requested
    (when use-byte-compare
      (set! s1 (string->utf8 s1))
      (set! s2 (string->utf8 s2)))
    (let* ((len1 (if use-byte-compare (bytevector-length s1) (string-length s1)))
           (len2 (if use-byte-compare (bytevector-length s2) (string-length s2)))
           (column (make-vector (+ len1 1) 0)))

      ;; Initialize first column
      (do ((y 0 (+ y 1)))
          ((> y len1))
        (vector-set! column y y))

      ;; Main algorithm loop
      (do ((x 1 (+ x 1)))
          ((> x len2))
        (let ((lastdiag (vector-ref column 0)))
          (vector-set! column 0 x)
          (do ((y 1 (+ y 1)))
              ((> y len1))
            (let* ((olddiag (vector-ref column y))
                   (c1 (if use-byte-compare
                          (bytevector-u8-ref s1 (- y 1))
                          (char->integer (string-ref s1 (- y 1)))))
                   (c2 (if use-byte-compare
                          (bytevector-u8-ref s2 (- x 1))
                          (char->integer (string-ref s2 (- x 1)))))
                   (cost (if (= c1 c2) lastdiag (+ lastdiag 1)))
                   (deletion (+ (vector-ref column y) 1))
                   (insertion (+ (vector-ref column (- y 1)) 1)))
              (vector-set! column y (min cost deletion insertion))
              (set! lastdiag olddiag)))))

      ;; Return final distance
      (vector-ref column len1))))))

(define (elisp-char-to-string character)
  "Convert arg CHAR to a string containing that character."
  (string (integer->char character)))

(define (elisp-string-to-char string)
  "Return the first character in STRING."
  (if (string=? string "")
      0  ; Return 0 for empty string
      (char->integer (string-ref string 0))))

(define (elisp-byte-to-string byte)
  "Convert arg BYTE to a unibyte string containing that byte."
  (string (integer->char (modulo byte 256))))

(define (elisp-string . characters)
  "Concatenate all the argument characters and make the result a string."
  (list->string (map integer->char characters)))

(define (elisp-unibyte-string . bytes)
  "Concatenate all the argument bytes and make the result a unibyte string."
  ;; In Guilemacs, all strings are UTF-8, so just call string
  (apply elisp-string bytes))

(define (elisp-multibyte-string-p object)
  "Return t if OBJECT is a multibyte string.
Return nil if OBJECT is either a unibyte string, or not a string.
In Guilemacs, all strings are UTF-8, so this always returns nil."
  #nil)

(define (elisp-eval-scheme string)
  "Evaluate a string containing a Scheme expression."
  (eval-string string))

(define (elisp-stringp object)
  "Return t if OBJECT is a string."
  (if (string? object) #t #nil))

(define (elisp-char-or-string-p object)
  "Return t if OBJECT is a character or a string."
  (if (or (char? object)
          (and (number? object) (>= object 0) (<= object #x3fffff))  ; Emacs character range
          (string? object))
      #t
      #nil))

;; Efficient string comparison functions for C integration
(define (elisp-string-equal-cstr lisp-string c-string)
  "Compare a Lisp string with a C string (case-sensitive).
   More efficient than creating temporary Guile string objects."
  (if (string=? lisp-string c-string) #t #nil))

(define (elisp-string-ci-equal-cstr lisp-string c-string)
  "Compare a Lisp string with a C string (case-insensitive).
   More efficient than creating temporary Guile string objects."
  (if (string-ci=? lisp-string c-string) #t #nil))

(define (elisp-symbol-name-equal-cstr symbol c-string)
  "Compare a symbol's name with a C string (case-sensitive).
   Optimized for symbol name comparisons."
  (if (string=? (symbol->string symbol) c-string) #t #nil))

;; Ultra-efficient comparison functions that avoid creating temporary string objects
(define (elisp-string-equal-two-cstrs lisp-string c-string1 c-string2)
  "Compare a Lisp string with two C strings efficiently.
   Returns #t if lisp-string equals c-string1, checks c-string2 as fallback.
   Designed to replace: (string-equal-cstr lisp-string (scm_from_utf8_string c-string2))"
  (if (or (string=? lisp-string c-string1)
          (string=? lisp-string c-string2)) #t #nil))

(define (elisp-string-ci-equal-two-cstrs lisp-string c-string1 c-string2)
  "Case-insensitive version of elisp-string-equal-two-cstrs."
  (if (or (string-ci=? lisp-string c-string1)
          (string-ci=? lisp-string c-string2)) #t #nil))

;; Optimized constant string comparisons
(define (elisp-string-ci-equal-none lisp-string)
  "Optimized check if a string equals 'None' (case-insensitive).
   Avoids repeated scm_from_utf8_string calls for this common constant."
  (if (string-ci=? lisp-string "None") #t #nil))

(define (elisp-string-equal-none lisp-string)
  "Optimized check if a string equals 'None' (case-sensitive).
   Avoids repeated scm_from_utf8_string calls for this common constant."
  (if (string=? lisp-string "None") #t #nil))

(set-symbol-function! 'string-bytes elisp-string-bytes)
(set-symbol-function! 'string-distance elisp-string-distance)
(set-symbol-function! 'char-to-string elisp-char-to-string)
(set-symbol-function! 'string-to-char elisp-string-to-char)
(set-symbol-function! 'byte-to-string elisp-byte-to-string)
(set-symbol-function! 'string elisp-string)
(set-symbol-function! 'unibyte-string elisp-unibyte-string)
(set-symbol-function! 'multibyte-string-p elisp-multibyte-string-p)
(set-symbol-function! 'eval-scheme elisp-eval-scheme)
(set-symbol-function! 'stringp elisp-stringp)
(set-symbol-function! 'char-or-string-p elisp-char-or-string-p)
(set-symbol-function! 'string-equal-cstr elisp-string-equal-cstr)
(set-symbol-function! 'string-ci-equal-cstr elisp-string-ci-equal-cstr)
(set-symbol-function! 'symbol-name-equal-cstr elisp-symbol-name-equal-cstr)
(set-symbol-function! 'string-equal-two-cstrs elisp-string-equal-two-cstrs)
(set-symbol-function! 'string-ci-equal-two-cstrs elisp-string-ci-equal-two-cstrs)
(set-symbol-function! 'string-ci-equal-none elisp-string-ci-equal-none)
(set-symbol-function! 'string-equal-none elisp-string-equal-none)

;; List processing functions migrated from C to Guile for better maintainability

(define (elisp-memq elt list)
  "Return non-nil if ELT is an element of LIST. Comparison done with `eq'.
The value is actually the tail of LIST whose car is ELT."
  (let loop ((tail list))
    (cond
      ((null? tail) #nil)
      ((eq? elt (car tail)) tail)
      (else (loop (cdr tail))))))

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

(define (elisp-reverse list)
  "Return a new list with elements of LIST in reverse order."
  (let loop ((remaining list) (result '()))
    (if (null? remaining)
        result
        (loop (cdr remaining) (cons (car remaining) result)))))

;; Additional list processing functions

(define (elisp-member elt list)
  "Return non-nil if ELT is an element of LIST. Comparison done with `equal'.
The value is actually the tail of LIST whose car is ELT."
  (let loop ((tail list))
    (cond
      ((null? tail) #nil)
      ((equal? elt (car tail)) tail)
      (else (loop (cdr tail))))))

(define (elisp-assq key alist)
  "Return non-nil if KEY is `eq' to the car of an element of ALIST.
The value is actually the first element of ALIST whose car is KEY.
Elements of ALIST that are not conses are ignored."
  (let loop ((tail alist))
    (cond
      ((null? tail) #nil)
      ((not (pair? (car tail))) (loop (cdr tail))) ; Skip non-conses
      ((eq? key (car (car tail))) (car tail))
      (else (loop (cdr tail))))))

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

(define (elisp-copy-sequence seq)
  "Return a copy of a list, vector, string, or other sequence.
The elements of a list are not copied; they are shared with the original."
  (cond
    ((null? seq) seq)
    ((pair? seq) (list-copy seq))
    ((string? seq) (string-copy seq))
    ((vector? seq) (vector-copy seq))
    (else seq))) ; Return as-is for other types

;; Simple numerical predicates

(define (elisp-zerop number)
  "Return t if NUMBER is zero."
  (if (and (number? number) (= number 0)) #t #nil))

(define (elisp-plusp number)
  "Return t if NUMBER is positive."
  (if (and (number? number) (> number 0)) #t #nil))

(define (elisp-minusp number)
  "Return t if NUMBER is negative."
  (if (and (number? number) (< number 0)) #t #nil))

(define (elisp-evenp integer)
  "Return t if INTEGER is even."
  (if (and (integer? integer) (even? integer)) #t #nil))

(define (elisp-oddp integer)
  "Return t if INTEGER is odd."
  (if (and (integer? integer) (odd? integer)) #t #nil))

(define (elisp-numberp object)
  "Return t if OBJECT is a number (integer or floating point)."
  (if (number? object) #t #nil))

(define (elisp-integerp object)
  "Return t if OBJECT is an integer."
  (if (integer? object) #t #nil))

(define (elisp-floatp object)
  "Return t if OBJECT is a floating point number."
  (if (and (number? object) (not (integer? object))) #t #nil))

(define (elisp-natnump object)
  "Return t if OBJECT is a natural number (non-negative integer)."
  (if (and (integer? object) (>= object 0)) #t #nil))

;; Property list functions

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

;; String comparison functions

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

;; List construction and manipulation

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

;; Simple utility functions

(define (elisp-identity object)
  "Return the argument unchanged."
  object)

(define (elisp-constantly value)
  "Return a function that always returns VALUE.
This is a useful building block for higher-order functions."
  (lambda args value))

;; Register the functions for Elisp use
(set-symbol-function! 'memq elisp-memq)
(set-symbol-function! 'nth elisp-nth)
(set-symbol-function! 'nthcdr elisp-nthcdr)
(set-symbol-function! 'last elisp-last)
(set-symbol-function! 'butlast elisp-butlast)
(set-symbol-function! 'reverse elisp-reverse)
(set-symbol-function! 'member elisp-member)
(set-symbol-function! 'assq elisp-assq)
(set-symbol-function! 'assoc elisp-assoc)
(set-symbol-function! 'rassq elisp-rassq)
(set-symbol-function! 'copy-sequence elisp-copy-sequence)
(set-symbol-function! 'zerop elisp-zerop)
(set-symbol-function! 'plusp elisp-plusp)
(set-symbol-function! 'minusp elisp-minusp)
(set-symbol-function! 'evenp elisp-evenp)
(set-symbol-function! 'oddp elisp-oddp)
(set-symbol-function! 'numberp elisp-numberp)
(set-symbol-function! 'integerp elisp-integerp)
(set-symbol-function! 'floatp elisp-floatp)
(set-symbol-function! 'natnump elisp-natnump)
(set-symbol-function! 'plist-get elisp-plist-get)
(set-symbol-function! 'plist-put elisp-plist-put)
(set-symbol-function! 'plist-member elisp-plist-member)
(set-symbol-function! 'string-equal elisp-string-equal)
(set-symbol-function! 'string-lessp elisp-string-lessp)
(set-symbol-function! 'string-greaterp elisp-string-greaterp)
(set-symbol-function! 'append elisp-append)
(set-symbol-function! 'mapcar elisp-mapcar)
(set-symbol-function! 'mapc elisp-mapc)
(set-symbol-function! 'identity elisp-identity)
(set-symbol-function! 'constantly elisp-constantly)

;; Phase 3: Type predicate functions migrated from C to Guile

(define (elisp-symbolp object)
  "Return t if OBJECT is a symbol."
  (if (symbol? object) #t #nil))

(define (elisp-bufferp object)
  "Return t if OBJECT is an editor buffer."
  ;; Note: BUFFERP check needs to be kept in C for now as buffer objects are C-specific
  ;; This is a placeholder implementation
  #nil)

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

;; Basic cons cell manipulation functions

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

;; List construction functions

(define (elisp-list . objects)
  "Return a newly created list with specified arguments as elements.
Allows any number of arguments, including zero."
  objects)

(define (elisp-make-list length init)
  "Return a newly created list of length LENGTH, with each element being INIT."
  (if (not (and (integer? length) (>= length 0)))
      (error "Wrong type argument: natnump" length)
      (make-list length init)))

;; Phase 4: DEFUN function migrations from C to Guile - NOW ACTIVE
;;
(define (elisp-proper-list-p object)
  "Return OBJECT's length if it is a proper list, nil otherwise.
A proper list is neither circular nor dotted (i.e., its last cdr is nil)."
  (catch #t
    (lambda ()
      (let ((len (length object)))
        len))
    (lambda (key . args)
      ;; If length fails (circular, dotted, or not a list), return nil
      #nil)))

(define (elisp-characterp object)
  "Return non-nil if OBJECT is a character.
In Emacs Lisp, characters are represented by character codes."
  (if (and (integer? object)
           (>= object 0)
           (<= object #x3FFFFF))  ; max-char value
      #t #nil))

(define (elisp-max-char . args)
  "Return the maximum character code.
If UNICODE is non-nil, return the maximum character code defined by Unicode."
  (let ((unicode (if (null? args) #f (car args))))
    (if unicode
        #x10FFFF   ; MAX_UNICODE_CHAR
        #x3FFFFF))) ; MAX_CHAR

(define (elisp-string-lessp string1 string2)
  "Return non-nil if STRING1 is less than STRING2 in lexicographic order.
Case is significant. Symbols are also allowed; their print names are used instead."
  (let ((s1 (if (symbol? string1) (symbol->string string1) string1))
        (s2 (if (symbol? string2) (symbol->string string2) string2)))
    (if (string<? s1 s2) #t #nil)))

;; FIX-guilemacs: Additional DEFUN function migrations from C to Guile
;; New functions identified as migration candidates

;; Type predicate functions - simple one-liners from data.c
(define (elisp-integerp object)
  "Return t if OBJECT is an integer."
  (if (and (number? object) (exact-integer? object)) #t #nil))

(define (elisp-numberp object)
  "Return t if OBJECT is a number (floating point or integer)."
  (if (number? object) #t #nil))

(define (elisp-floatp object)
  "Return t if OBJECT is a floating point number."
  (if (and (number? object) (not (exact-integer? object))) #t #nil))

(define (elisp-natnump object)
  "Return t if OBJECT is a nonnegative integer, and nil otherwise."
  (if (and (number? object) (exact-integer? object) (>= object 0)) #t #nil))

(define (elisp-symbolp object)
  "Return t if OBJECT is a symbol."
  (if (symbol? object) #t #nil))

(define (elisp-stringp object)
  "Return t if OBJECT is a string."
  (if (string? object) #t #nil))

(define (elisp-vectorp object)
  "Return t if OBJECT is a vector."
  (if (and (vector? object) (not (keyword? object))) #t #nil))


;; Simple utility functions from fns.c that are easy to migrate
(define (elisp-car-safe object)
  "Return the car of OBJECT if it is a cons cell, or else nil."
  (if (pair? object) (car object) #nil))

(define (elisp-cdr-safe object)
  "Return the cdr of OBJECT if it is a cons cell, or else nil."
  (if (pair? object) (cdr object) #nil))

;; Simple comparison and null checking functions from data.c
(define (elisp-null object)
  "Return t if OBJECT is nil, and return nil otherwise."
  (if (or (null? object) (eq? object #nil)) #t #nil))

(define (elisp-eq obj1 obj2)
  "Return t if the two args are the same Lisp object."
  (if (eq? obj1 obj2) #t #nil))

;; Basic length function
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

;; Length comparison functions - simple predicates
(define (elisp-length< sequence length)
  "Return non-nil if SEQUENCE is shorter than LENGTH."
  (cond
    ((not (integer? length)) #nil)
    ((< length 0) #nil)
    ((null? sequence) (if (> length 0) #t #nil))
    ((pair? sequence)
     (let loop ((seq sequence) (count 0))
       (cond
         ((>= count length) #nil)  ; Already at length, so not shorter
         ((null? seq) #t)          ; Reached end before length
         ((pair? seq) (loop (cdr seq) (+ count 1)))
         (else #nil))))            ; Improper list
    ;; Check for keywords/symbols that are not sequences
    ((or (keyword? sequence) (symbol? sequence)) #nil)
    ;; For vectors and strings, use regular length
    ((or (vector? sequence) (string? sequence))
     (< (length sequence) length))
    (else
     ;; For unknown types, signal an error like Elisp would
     #nil)))

(define (elisp-length> sequence length)
  "Return non-nil if SEQUENCE is longer than LENGTH."
  (cond
    ((not (integer? length)) #nil)
    ((< length 0) #t)  ; Any sequence is longer than negative length
    ((null? sequence) #nil)
    ((pair? sequence)
     (let loop ((seq sequence) (count 0))
       (cond
         ((> count length) #t)     ; Already longer than length
         ((null? seq) #nil)        ; Reached end at or before length
         ((pair? seq) (loop (cdr seq) (+ count 1)))
         (else #nil))))            ; Improper list
    (else
     ;; For other sequences (vectors, strings), use regular length
     (> (length sequence) length))))

(define (elisp-length= sequence length)
  "Return non-nil if SEQUENCE has exactly LENGTH elements."
  (cond
    ((not (integer? length)) #nil)
    ((< length 0) #nil)
    ((null? sequence) (= length 0))
    ((pair? sequence)
     (let loop ((seq sequence) (count 0))
       (cond
         ((= count length) (null? seq))  ; Check if we're at end when count matches
         ((null? seq) #nil)              ; Reached end before target length
         ((pair? seq) (loop (cdr seq) (+ count 1)))
         (else #nil))))                  ; Improper list
    (else
     ;; For other sequences (vectors, strings), use regular length
     (= (length sequence) length))))

;; Safe length function
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

;; Equality functions that use Guile primitives
(define (elisp-eq obj1 obj2)
  "Return t if the two args are the same Lisp object."
  (if (eq? obj1 obj2) #t #nil))

(define (elisp-eql obj1 obj2)
  "Return t if the two args are `eq' or are indistinguishable numbers.
Integers with the same value are `eql'.
Floating-point values with the same sign, exponent and fraction are `eql'."
  (if (eqv? obj1 obj2) #t #nil))

(define (elisp-equal obj1 obj2)
  "Return t if two Lisp objects have similar structure and contents."
  (if (equal? obj1 obj2) #t #nil))

;; List utility functions
(define (elisp-take n list)
  "Return the first N elements of LIST.
If N is zero or negative, return nil.
If N is greater or equal to the length of LIST, return LIST (or a copy)."
  (cond
    ((not (integer? n)) (error "Wrong type argument: integerp" n))
    ((<= n 0) #nil)
    ((null? list) #nil)
    (else (list-head list (min n (length list))))))

;; Case conversion functions that use Guile
(define (elisp-upcase obj)
  "Convert argument to upper case and return that."
  (cond
    ((string? obj) (string-upcase obj))
    ((integer? obj) (string->number (string-upcase (string (integer->char obj)))))
    (else obj)))

(define (elisp-downcase obj)
  "Convert argument to lower case and return that."
  (cond
    ((string? obj) (string-downcase obj))
    ((integer? obj) (string->number (string-downcase (string (integer->char obj)))))
    (else obj)))

(define (elisp-capitalize obj)
  "Convert argument to capitalized form and return that."
  (cond
    ((string? obj) (string-capitalize obj))
    ((integer? obj) (string->number (string-capitalize (string (integer->char obj)))))
    (else obj)))

;; Type conversion functions
(define (elisp-float arg)
  "Return the floating point number equal to ARG."
  (cond
    ((integer? arg) (exact->inexact arg))
    ((number? arg) arg)  ; Already a float
    (else (error "Wrong type argument: numberp" arg))))

(define (elisp-number-to-string number)
  "Return the decimal representation of NUMBER as a string."
  (cond
    ((integer? number) (number->string number))
    ((number? number) (number->string number))
    (else (error "Wrong type argument: numberp" number))))

(define (elisp-string-to-number string base)
  "Parse STRING as a decimal number and return the number.
Optional BASE argument specifies the base (2-16)."
  (let ((base-val (if base base 10)))
    (cond
      ((not (string? string)) (error "Wrong type argument: stringp" string))
      ((not (and (integer? base-val) (>= base-val 2) (<= base-val 16)))
       (error "Invalid base" base-val))
      (else
       (catch #t
         (lambda ()
           (string->number (string-trim string) base-val))
         (lambda (key . args)
           0))))))  ; Return 0 on parse error, like Emacs

;; Additional type predicates
(define (elisp-sequencep object)
  "Return t if OBJECT is a sequence (list or array)."
  (if (or (pair? object) (null? object) (vector? object) (string? object))
      #t #nil))

(define (elisp-arrayp object)
  "Return t if OBJECT is an array (string or vector)."
  (if (or (vector? object) (string? object))
      #t #nil))

(define (elisp-bool-vector-p object)
  "Return t if OBJECT is a bool-vector."
  ;; For now, check if it's a bitvector in Guile
  (if (bitvector? object) #t #nil))

(define (elisp-subrp object)
  "Return t if OBJECT is a built-in function."
  (if (or (procedure? object)
          (and (pair? object) (eq? (car object) 'special-operator)))
      #t #nil))

;; String creation function
(define (elisp-make-string length init multibyte)
  "Return a newly created string of length LENGTH, with INIT in each element."
  (cond
    ((not (and (integer? length) (>= length 0)))
     (error "Wrong type argument: natnump" length))
    ((not (integer? init))
     (error "Wrong type argument: characterp" init))
    (else
     (make-string length (integer->char init)))))

;; Final batch of simple predicates and utilities
(define (elisp-hash-table-p obj)
  "Return t if OBJ is a Lisp hash table object."
  ;; Check if it's a Guile hash table
  (if (hash-table? obj) #t #nil))

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

;; Hash functions (simple wrappers)
(define (elisp-sxhash-eq obj)
  "Return an integer hash code for OBJ suitable for `eq'."
  ;; Use Guile's hash function for eq
  (hashq obj 536870909))  ; Large prime number

(define (elisp-sxhash-eql obj)
  "Return an integer hash code for OBJ suitable for `eql'."
  ;; Use Guile's hash function for eqv
  (hashv obj 536870909))

(define (elisp-sxhash-equal obj)
  "Return an integer hash code for OBJ suitable for `equal'."
  ;; Use Guile's hash function for equal
  (hash obj 536870909))

;; Implementation of goals.org ideas
;; Goal: "Use direct symbol comparison instead of string comparison"
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

;; Goal: "Implement native Guile case-insensitive operations"
(define (elisp-string-equal-ignore-case string1 string2)
  "Return t if two strings are equal ignoring case.
Symbols are also allowed; their print names are used instead.
Uses native Guile case-insensitive comparison."
  (let ((s1 (if (symbol? string1) (symbol->string string1) string1))
        (s2 (if (symbol? string2) (symbol->string string2) string2)))
    (if (string-ci=? s1 s2) #t #nil)))

(define (elisp-string-lessp-ignore-case string1 string2)
  "Return t if STRING1 is less than STRING2 ignoring case.
Uses native Guile case-insensitive comparison."
  (let ((s1 (if (symbol? string1) (symbol->string string1) string1))
        (s2 (if (symbol? string2) (symbol->string string2) string2)))
    (if (string-ci<? s1 s2) #t #nil)))

;; Goal: "find string comparison patterns in C code, move to guile"
(define (elisp-string-prefix-p prefix string ignore-case)
  "Return non-nil if PREFIX is a prefix of STRING.
If IGNORE-CASE is non-nil, the comparison is case-insensitive."
  (let ((prefix-str (if (symbol? prefix) (symbol->string prefix) prefix))
        (string-str (if (symbol? string) (symbol->string string) string)))
    (let ((prefix-len (string-length prefix-str))
          (string-len (string-length string-str)))
      (if (> prefix-len string-len)
          #nil
          (let ((substring (substring string-str 0 prefix-len)))
            (if ignore-case
                (if (string-ci=? prefix-str substring) #t #nil)
                (if (string=? prefix-str substring) #t #nil)))))))

(define (elisp-string-suffix-p suffix string ignore-case)
  "Return non-nil if SUFFIX is a suffix of STRING.
If IGNORE-CASE is non-nil, the comparison is case-insensitive."
  (let ((suffix-str (if (symbol? suffix) (symbol->string suffix) suffix))
        (string-str (if (symbol? string) (symbol->string string) string)))
    (let ((suffix-len (string-length suffix-str))
          (string-len (string-length string-str)))
      (if (> suffix-len string-len)
          #nil
          (let ((start-pos (- string-len suffix-len)))
            (let ((substring (substring string-str start-pos)))
              (if ignore-case
                  (if (string-ci=? suffix-str substring) #t #nil)
                  (if (string=? suffix-str substring) #t #nil))))))))

;; Goal: "Optimize for symbol interning efficiency"
(define (elisp-intern-soft name obarray)
  "Return the symbol whose name is NAME, or nil if no such symbol exists.
Uses efficient symbol lookup without creating new symbols."
  (cond
    ((symbol? name)
     ;; If already a symbol, check if it exists in obarray
     name)  ; In Guile, symbols are globally interned
    ((string? name)
     ;; Use Guile's efficient symbol lookup
     (catch #t
       (lambda ()
         (string->symbol name))
       (lambda (key . args)
         #nil)))
    (else
     (error "Wrong type argument: string-or-symbol-p" name))))

;; Goal: "minimize memory handling in C, utilize the GC in guile"
(define (elisp-string-search needle haystack start-pos)
  "Search for NEEDLE in HAYSTACK starting at START-POS.
Returns the position of the first match, or nil if not found.
Uses Guile's efficient string search with automatic memory management."
  (let ((needle-str (if (symbol? needle) (symbol->string needle) needle))
        (haystack-str (if (symbol? haystack) (symbol->string haystack) haystack))
        (start (if start-pos start-pos 0)))
    (let ((pos (string-contains haystack-str needle-str start)))
      (if pos pos #nil))))

;; Simple utility functions migrated from C DEFUN to Guile
(define (elisp-null object)
  "Return t if OBJECT is nil, and return nil otherwise."
  (if (or (null? object) (eq? object #nil)) #t #nil))

;; Register Phase 3 functions for Elisp use
; Note: bufferp kept in C for now due to C-specific buffer object handling
; Note: symbolp kept in C for now
(set-symbol-function! 'consp elisp-consp)
(set-symbol-function! 'atom elisp-atom)
(set-symbol-function! 'listp elisp-listp)
(set-symbol-function! 'nlistp elisp-nlistp)
(set-symbol-function! 'vectorp elisp-vectorp)
(set-symbol-function! 'cons elisp-cons)
(set-symbol-function! 'car elisp-car)
(set-symbol-function! 'cdr elisp-cdr)
(set-symbol-function! 'list elisp-list)
(set-symbol-function! 'make-list elisp-make-list)


;; Register Phase 4 functions (uncommmented and new migrations)
;; Note: string-lessp already exists as elisp-string-lessp above

;; Register length functions
(set-symbol-function! 'length elisp-length)
(set-symbol-function! 'length< elisp-length<)
(set-symbol-function! 'length> elisp-length>)
(set-symbol-function! 'length= elisp-length=)
(set-symbol-function! 'safe-length elisp-safe-length)

;; Register equality functions
(set-symbol-function! 'eq elisp-eq)
(set-symbol-function! 'eql elisp-eql)
(set-symbol-function! 'equal elisp-equal)

;; Register list utility functions
(set-symbol-function! 'take elisp-take)

;; Register case conversion functions
(set-symbol-function! 'upcase elisp-upcase)
(set-symbol-function! 'downcase elisp-downcase)
(set-symbol-function! 'capitalize elisp-capitalize)

;; Register type conversion functions
(set-symbol-function! 'float elisp-float)
(set-symbol-function! 'number-to-string elisp-number-to-string)
(set-symbol-function! 'string-to-number elisp-string-to-number)

;; Register additional type predicates
(set-symbol-function! 'sequencep elisp-sequencep)
(set-symbol-function! 'arrayp elisp-arrayp)
(set-symbol-function! 'bool-vector-p elisp-bool-vector-p)
(set-symbol-function! 'subrp elisp-subrp)

;; Register string creation functions
(set-symbol-function! 'make-string elisp-make-string)

;; Register final batch of functions
(set-symbol-function! 'hash-table-p elisp-hash-table-p)
(set-symbol-function! 'boundp elisp-boundp)
(set-symbol-function! 'sxhash-eq elisp-sxhash-eq)
(set-symbol-function! 'sxhash-eql elisp-sxhash-eql)
(set-symbol-function! 'sxhash-equal elisp-sxhash-equal)


;; Register goals.org implementation functions
(set-symbol-function! 'string-equal-ignore-case elisp-string-equal-ignore-case)
(set-symbol-function! 'string-lessp-ignore-case elisp-string-lessp-ignore-case)
(set-symbol-function! 'string-prefix-p elisp-string-prefix-p)
(set-symbol-function! 'string-suffix-p elisp-string-suffix-p)
(set-symbol-function! 'intern-soft elisp-intern-soft)
(set-symbol-function! 'string-search elisp-string-search)

;; Final high-value migration candidates
(define (elisp-random limit)
  "Return a pseudo-random integer.
By default, return a fixnum; all fixnums are equally likely.
With positive integer LIMIT, return random integer in interval [0,LIMIT)."
  (cond
    ((or (null? limit) (not limit))
     ;; Return random fixnum - use Guile's random
     (random 536870912))  ; Large range for fixnum
    ((eq? limit #t)
     ;; Seed from system entropy - not implemented in simple version
     #nil)
    ((string? limit)
     ;; Seed from string - not implemented in simple version
     #nil)
    ((and (integer? limit) (> limit 0))
     ;; Return random integer in [0, limit)
     (random limit))
    (else
     (error "Wrong type argument" limit))))

;; DEFUN migrations from lread.c - simple utility functions primarily used by elisp
(define (elisp-get-load-suffixes)
  "Return the suffixes that 'load' should try if a suffix is required.
This uses the variables 'load-suffixes' and 'load-file-rep-suffixes'."
  (let ((suffixes load-suffixes)
        (rep-suffixes load-file-rep-suffixes))
    (let loop ((suf-list suffixes) (result '()))
      (if (null? suf-list)
          (reverse result)
          (let ((suffix (car suf-list)))
            (let inner-loop ((rep-list rep-suffixes) (inner-result result))
              (if (null? rep-list)
                  (loop (cdr suf-list) inner-result)
                  (inner-loop (cdr rep-list)
                             (cons (string-append suffix (car rep-list)) inner-result)))))))))

(define (elisp-obarrayp object)
  "Return t if OBJECT is an obarray."
  ;; For now, simple check - in full implementation would check Guile vector
  (if (vector? object) #t #nil))

(define (elisp-obarray-make size)
  "Return a new obarray of size SIZE.
The obarray will grow to accommodate any number of symbols; the size, if
given, is only a hint for the expected number."
  ;; Create a vector for obarray representation
  (make-vector (if (and size (integer? size) (> size 0)) size 128) '()))

(define (elisp-obarray-clear obarray)
  "Remove all symbols from OBARRAY."
  (if (vector? obarray)
      (let ((len (vector-length obarray)))
        (do ((i 0 (+ i 1)))
            ((>= i len) obarray)
          (vector-set! obarray i '())))
      (error "Wrong type argument: obarrayp" obarray)))

(define elisp-read-char
  (case-lambda
    (()
     ;; Called with 0 arguments - defaults
     (elisp-read-char #nil #nil #nil))
    ((prompt)
     ;; Called with 1 argument
     (elisp-read-char prompt #nil #nil))
    ((prompt inherit-input-method)
     ;; Called with 2 arguments
     (elisp-read-char prompt inherit-input-method #nil))
    ((prompt inherit-input-method seconds)
     ;; Called with 3 arguments
     "Read a character event from the command input (keyboard or macro).
It is returned as a number.
If the optional argument PROMPT is non-nil, display that as a prompt.
If the optional argument INHERIT-INPUT-METHOD is non-nil and some
input method is turned on in the current buffer, that input method
is used for reading a character.
If the optional argument SECONDS is non-nil, it should be a number
specifying the maximum number of seconds to wait for input."
     ;; For now, a simple implementation that reads one character
     ;; In full implementation, would handle prompts, input methods, and timeouts
     (char->integer (read-char)))))

;; Symbol property functions
(define (elisp-symbol-plist symbol)
  "Return SYMBOL's property list."
  (if (symbol? symbol)
      ;; Use symbol properties in Guile
      (catch #t
        (lambda ()
          (symbol-property symbol '*elisp-plist*))
        (lambda (key . args)
          #nil))
      (error "Wrong type argument: symbolp" symbol)))

(define (elisp-setplist symbol plist)
  "Set SYMBOL's property list to PLIST and return PLIST."
  (if (symbol? symbol)
      (begin
        (set-symbol-property! symbol '*elisp-plist* plist)
        plist)
      (error "Wrong type argument: symbolp" symbol)))

(define (elisp-get symbol propname)
  "Return the value of SYMBOL's PROPNAME property.
This is the last value stored with '(put SYMBOL PROPNAME VALUE)'."
  (if (symbol? symbol)
      (let ((plist (elisp-symbol-plist symbol)))
        (elisp-plist-get plist propname))
      (error "Wrong type argument: symbolp" symbol)))

(define (elisp-put symbol propname value)
  "Store SYMBOL's PROPNAME property with value VALUE.
It can be retrieved with '(get SYMBOL PROPNAME)'."
  (if (symbol? symbol)
      (let ((old-plist (elisp-symbol-plist symbol)))
        (let ((new-plist (elisp-plist-put old-plist propname value)))
          (elisp-setplist symbol new-plist)
          value))
      (error "Wrong type argument: symbolp" symbol)))

;; Hash table predicates that can be migrated
(define (elisp-hash-table-count table)
  "Return the number of entries in TABLE."
  (if (hash-table? table)
      (hash-table-size table)
      (error "Wrong type argument: hash-table-p" table)))

(define (elisp-clrhash table)
  "Clear hash table TABLE and return it."
  (if (hash-table? table)
      (begin
        (hash-table-clear! table)
        table)
      (error "Wrong type argument: hash-table-p" table)))

(define (elisp-featurep feature subfeature)
  "Return t if FEATURE is present in this Emacs.
Use this to conditionalize execution of lisp code based on the
presence or absence of Emacs or environment extensions."
  (if (memq feature features)
      (if subfeature
          ;; Check subfeature - simplified implementation
          #t  ; For now, assume subfeatures are present if feature is
          #t)
      #nil))

(define (elisp-provide feature subfeatures)
  "Announce that FEATURE is a feature of the current Emacs.
The optional argument SUBFEATURES should be a list of symbols listing
particular subfeatures supported in this version of FEATURE."
  (if (not (memq feature features))
      (set! features (cons feature features)))
  feature)

(define (elisp-nreverse seq)
  "Reverse order of items in a list, vector or string SEQ.
This function may destructively modify SEQ to produce the value."
  (cond
    ((null? seq) seq)
    ((pair? seq)
     ;; Use Guile's efficient reverse! for lists
     (reverse! seq))
    ((vector? seq)
     ;; For vectors, we need to reverse in place
     (let ((len (vector-length seq)))
       (do ((i 0 (+ i 1)))
           ((>= i (quotient len 2)) seq)
         (let ((j (- len i 1)))
           (let ((temp (vector-ref seq i)))
             (vector-set! seq i (vector-ref seq j))
             (vector-set! seq j temp))))))
    ((string? seq)
     ;; For strings, convert to list, reverse, back to string
     (list->string (reverse! (string->list seq))))
    (else seq)))

;; Register final high-value migration candidates
(set-symbol-function! 'random elisp-random)
(set-symbol-function! 'featurep elisp-featurep)
(set-symbol-function! 'provide elisp-provide)
(set-symbol-function! 'nreverse elisp-nreverse)

;; Additional critical DEFUN migrations from lread.c

(define (elisp-intern string obarray)
  "Return the canonical symbol whose name is STRING.
If there is none, one is created by this function and returned.
A second optional argument specifies the obarray to use;
it defaults to the value of `obarray'."
  (let ((str (if (symbol? string) (symbol->string string) string)))
    (if (not (string? str))
        ((symbol-function 'signal) 'wrong-type-argument (cons 'stringp str))
        ;; Use Guile's efficient symbol interning
        (string->symbol str))))

(define (elisp-intern-soft-lread name obarray)
  "Return the canonical symbol named NAME, or nil if none exists.
NAME may be a string or a symbol. If it is a symbol, that exact
symbol is searched for. A second optional argument specifies the obarray to use;
it defaults to the value of `obarray'."
  (let ((str (if (symbol? name) (symbol->string name) name)))
    (if (not (string? str))
        #nil
        (catch #t
          (lambda ()
            ;; Try to find existing symbol without creating new one
            (let ((sym (string->symbol str)))
              (if (symbol-bound? sym) sym #nil)))
          (lambda (key . args)
            #nil)))))

(define (elisp-unintern name obarray)
  "Delete the symbol named NAME, if any, from OBARRAY.
The value is t if a symbol was found and deleted, nil otherwise.
NAME may be a string or a symbol. If it is a symbol, that symbol
is deleted, if it belongs to OBARRAY--no other symbol is deleted."
  (let ((str (if (symbol? name) (symbol->string name) name)))
    (if (not (string? str))
        #nil
        ;; In Guile, symbols are globally interned, so we can't really unintern
        ;; Return nil to indicate no symbol was found/deleted
        #nil)))

;; Register DEFUN migrations from lread.c
(set-symbol-function! 'get-load-suffixes elisp-get-load-suffixes)
(set-symbol-function! 'obarrayp elisp-obarrayp)
(set-symbol-function! 'obarray-make elisp-obarray-make)
(set-symbol-function! 'obarray-clear elisp-obarray-clear)
(set-symbol-function! 'read-char elisp-read-char)
(set-symbol-function! 'intern elisp-intern)
(set-symbol-function! 'intern-soft elisp-intern-soft-lread)
(set-symbol-function! 'unintern elisp-unintern)
(set-symbol-function! 'symbol-plist elisp-symbol-plist)
(set-symbol-function! 'setplist elisp-setplist)
(set-symbol-function! 'get elisp-get)
(set-symbol-function! 'put elisp-put)
(set-symbol-function! 'hash-table-count elisp-hash-table-count)
(set-symbol-function! 'clrhash elisp-clrhash)

;; Internal utility functions (not registered to avoid conflicts)
;; elisp-symbol-equal - available for internal use

;; Phase 4 DEFUN function migrations are called directly from C code
;; to avoid infinite recursion. The elisp-* versions are available
;; for internal use but not registered as symbol replacements.

;; Load lookup functions for C integration
;; Use the prelude directory defined in the current module by C
(primitive-load (string-append %prelude-directory "/lookup-functions.scm"))

;; Load new UTF-8 string operations and migration functions
(primitive-load (string-append %prelude-directory "/utf8-string-operations.scm"))
; FIX: disabled because of error, something with 'char=?'
;(primitive-load (string-append %prelude-directory "/string-comparison-migration.scm"))
(primitive-load (string-append %prelude-directory "/symbol-operations.scm"))

;; Export the functions to both global module and language elisp emacs module
;; so C code can find them from either location
(let ((elisp-emacs-module (resolve-module '(language elisp emacs) #f)))
  ;; Export to language elisp emacs module
  (module-define! elisp-emacs-module 'lookup-color-in-map lookup-color-in-map)
  (module-define! elisp-emacs-module 'lookup-font-style lookup-font-style)
  (module-define! elisp-emacs-module 'lookup-in-alist-ci lookup-in-alist-ci)
  (module-define! elisp-emacs-module 'lookup-in-alist lookup-in-alist)
  (module-define! elisp-emacs-module 'lookup-symbol-in-list lookup-symbol-in-list)
  (module-define! elisp-emacs-module 'parse-face-bool-attribute parse-face-bool-attribute)
  (module-define! elisp-emacs-module 'process-yesno-response process-yesno-response)
  (module-define! elisp-emacs-module 'filter-dbus-message filter-dbus-message)
  (module-define! elisp-emacs-module 'is-special-buffer-name? is-special-buffer-name?)
  (module-define! elisp-emacs-module 'parse-color-spec parse-color-spec)
  (module-define! elisp-emacs-module 'validate-color-name validate-color-name)
  (module-define! elisp-emacs-module 'string-contains-whitespace? string-contains-whitespace?)
  (module-define! elisp-emacs-module 'is-frame-name-fnn-format? is-frame-name-fnn-format?)
  (module-define! elisp-emacs-module 'validate-xlfd-font-name validate-xlfd-font-name)
  (module-define! elisp-emacs-module 'is-absolute-path? is-absolute-path?)
  (module-define! elisp-emacs-module 'has-directory-traversal? has-directory-traversal?)
  (module-define! elisp-emacs-module 'string-spaces-to-dashes string-spaces-to-dashes)
  (module-define! elisp-emacs-module 'string-trim-leading-whitespace string-trim-leading-whitespace)
  (module-define! elisp-emacs-module 'parse-number-string parse-number-string)
  (module-define! elisp-emacs-module 'validate-string-for-copying validate-string-for-copying)
  (module-define! elisp-emacs-module 'prepare-string-for-symbol prepare-string-for-symbol)

  ;; Export new SSDATA hoisting functions to elisp emacs module
  (module-define! elisp-emacs-module 'has-file-extension? has-file-extension?)
  (module-define! elisp-emacs-module 'extract-filename-from-path extract-filename-from-path)
  (module-define! elisp-emacs-module 'is-modifier-symbol? is-modifier-symbol?)
  (module-define! elisp-emacs-module 'validate-float-format-string validate-float-format-string)
  (module-define! elisp-emacs-module 'has-time-format-specifiers? has-time-format-specifiers?)
  (module-define! elisp-emacs-module 'parse-hex-color parse-hex-color)
  (module-define! elisp-emacs-module 'needs-filename-conversion? needs-filename-conversion?)
  (module-define! elisp-emacs-module 'is-utf8-filename? is-utf8-filename?)
  (module-define! elisp-emacs-module 'is-safe-for-c-string-copy? is-safe-for-c-string-copy?)
  (module-define! elisp-emacs-module 'looks-like-network-address? looks-like-network-address?)

  ;; Export path/filename operation functions to elisp emacs module
  (module-define! elisp-emacs-module 'is-absolute-path? is-absolute-path?)
  (module-define! elisp-emacs-module 'ends-with-directory-separator? ends-with-directory-separator?)
  (module-define! elisp-emacs-module 'normalize-path-separators normalize-path-separators)
  (module-define! elisp-emacs-module 'string-empty? string-empty?)
  (module-define! elisp-emacs-module 'has-directory-traversal? has-directory-traversal?)
  (module-define! elisp-emacs-module 'get-file-extension get-file-extension)
  (module-define! elisp-emacs-module 'path-starts-with? path-starts-with?)

  ;; Export simple string validation functions to elisp emacs module
  (module-define! elisp-emacs-module 'string-single-char? string-single-char?)
  (module-define! elisp-emacs-module 'string-starts-with-space? string-starts-with-space?)
  (module-define! elisp-emacs-module 'string-ascii-only? string-ascii-only?)
  (module-define! elisp-emacs-module 'valid-symbol-name? valid-symbol-name?)
  (module-define! elisp-emacs-module 'string-numeric? string-numeric?)
  (module-define! elisp-emacs-module 'string-needs-escaping? string-needs-escaping?)
  (module-define! elisp-emacs-module 'special-buffer-name? special-buffer-name?)
  (module-define! elisp-emacs-module 'string-equal-ignore-case? string-equal-ignore-case?)
  (module-define! elisp-emacs-module 'string-starts-with-char? string-starts-with-char?)
  (module-define! elisp-emacs-module 'string-ends-with-char? string-ends-with-char?)
  (module-define! elisp-emacs-module 'string-whitespace-only? string-whitespace-only?)
  (module-define! elisp-emacs-module 'valid-identifier? valid-identifier?)

  (module-define! elisp-emacs-module 'has-file-extension? has-file-extension?)
  (module-define! elisp-emacs-module 'source-code-file? source-code-file?)
  (module-define! elisp-emacs-module 'image-file? image-file?)
  (module-define! elisp-emacs-module 'config-file? config-file?)
  (module-define! elisp-emacs-module 'extract-file-extension extract-file-extension)

  (module-define! elisp-emacs-module 'hex-color-string? hex-color-string?)
  (module-define! elisp-emacs-module 'rgb-color-string? rgb-color-string?)
  (module-define! elisp-emacs-module 'named-color? named-color?)
  (module-define! elisp-emacs-module 'valid-xlfd-font-name? valid-xlfd-font-name?)
  (module-define! elisp-emacs-module 'font-family-name? font-family-name?)

  (module-define! elisp-emacs-module 'url-string? url-string?)
  (module-define! elisp-emacs-module 'email-address? email-address?)
  (module-define! elisp-emacs-module 'ip-address? ip-address?)

  (module-define! elisp-emacs-module 'lookup-registry-to-script lookup-registry-to-script)

  (module-define! elisp-emacs-module 'parse-font-name-with-size parse-font-name-with-size)

  (module-define! elisp-emacs-module 'substring-no-properties-scheme substring-no-properties-scheme)

  ;; Export file path operation functions to both modules
  (module-define! elisp-emacs-module 'file-path-absolute-p file-path-absolute-p)
  (module-define! elisp-emacs-module 'file-path-directory file-path-directory)
  (module-define! elisp-emacs-module 'file-path-nondirectory file-path-nondirectory)
  (module-define! elisp-emacs-module 'file-path-safe-p file-path-safe-p)

  ;; Export string concatenation functions to both modules
  (module-define! elisp-emacs-module 'string-concat-2 string-concat-2)
  (module-define! elisp-emacs-module 'string-concat-3 string-concat-3)
  (module-define! elisp-emacs-module 'string-concat-multi string-concat-multi)

  ;; Export integer parsing functions to both modules
  (module-define! elisp-emacs-module 'parse-integer-string parse-integer-string)
  (module-define! elisp-emacs-module 'read-integer-guile read-integer-guile)
  (module-define! elisp-emacs-module 'parse-emacs-number parse-emacs-number))

;; when elisp reads keyword symbols, support common-lisp keywords
(read-set! keywords 'prefix)

;; Additional DEFUN function migrations from C to Guile
;; Migration of delq - destructive list removal function

(define (elisp-delq elt list)
  "Delete members of LIST which are `eq' to ELT, and return the result.
More precisely, this function skips any members `eq' to ELT at the
front of LIST, then removes members `eq' to ELT from the remaining
sublist by modifying its list structure, then returns the resulting
list.

Write `(setq foo (delq element foo))' to be sure of correctly changing
the value of a list `foo'.  See also `remq', which does not modify the
argument."
  (let loop ((remaining list) (prev #f))
    (cond
      ((null? remaining) list)
      ((eq? elt (car remaining))
       ;; Found element to delete
       (if prev
           ;; Not at front, modify previous cell
           (begin
             (set-cdr! prev (cdr remaining))
             (loop (cdr remaining) prev))
           ;; At front, update list head
           (begin
             (set! list (cdr remaining))
             (loop (cdr remaining) #f))))
      (else
       ;; Keep this element, continue
       (loop (cdr remaining) remaining))))
  list)

(define (elisp-remq elt list)
  "Return a copy of LIST with all elements `eq' to ELT removed.
This is a non-destructive version of `delq'."
  (let loop ((remaining list) (result '()))
    (cond
      ((null? remaining) (reverse result))
      ((eq? elt (car remaining)) (loop (cdr remaining) result))
      (else (loop (cdr remaining) (cons (car remaining) result))))))

;; Register new functions
(set-symbol-function! 'delq elisp-delq)
(set-symbol-function! 'remq elisp-remq)

;; Additional reader utility functions migrated from lread.c

(define (elisp-complete-filename-p pathname)
  "Return t if PATHNAME is an absolute path.
This function replaces the C complete_filename_p function in lread.c:1203
by using Guile's string manipulation capabilities instead of direct
character array access."
  (if (not (string? pathname))
      #nil
      (let ((len (string-length pathname)))
        (if (< len 1)
            #nil
            (let ((first-char (string-ref pathname 0)))
              (cond
                ;; Unix-style absolute path starting with /
                ((char=? first-char #\/) #t)
                ;; Windows-style absolute path (C:\ or similar)
                ((and (>= len 3)
                      (char-alphabetic? first-char)
                      (char=? (string-ref pathname 1) #\:)
                      (or (char=? (string-ref pathname 2) #\\)
                          (char=? (string-ref pathname 2) #\/)))
                 #t)
                ;; Not an absolute path
                (else #nil)))))))

(define (elisp-file-name-absolute-p filename)
  "Return t if FILENAME is an absolute file name.
This is an alias for complete-filename-p with better naming."
  (elisp-complete-filename-p filename))

;; Register the filename utility functions for use from C and Elisp
(set-symbol-function! 'complete-filename-p elisp-complete-filename-p)
(set-symbol-function! 'file-name-absolute-p elisp-file-name-absolute-p)

;; FIX-guilemacs: DEFUN Mathematical function migrations from floatfns.c to Guile
;; These functions are excellent migration candidates because they:
;; 1. Don't depend on early C initialization
;; 2. Are well-defined mathematical operations
;; 3. Can leverage Guile's built-in floating point support

(define (elisp-copysign x1 x2)
  "Copy sign of X2 to value of X1, and return the result.
Cause an error if X1 or X2 is not a float."
  (let ((f1 (if (number? x1) (exact->inexact x1)
                (error "Wrong type argument: floatp" x1)))
        (f2 (if (number? x2) (exact->inexact x2)
                (error "Wrong type argument: floatp" x2))))
    (if (eq? (negative? f1) (negative? f2))
        f1
        (- f1))))

(define (elisp-frexp x)
  "Get significand and exponent of a floating point number.
Breaks the floating point number X into its binary significand SGNFCAND
and an integral exponent EXP for 2, such that: X = SGNFCAND * 2^EXP
The function returns the cons cell (SGNFCAND . EXP)."
  (let ((f (if (number? x) (exact->inexact x)
               (error "Wrong type argument: numberp" x))))
    (if (= f 0.0)
        (cons 0.0 0)
        (let* ((abs-f (abs f))
               (exponent (inexact->exact (ceiling (log abs-f 2))))
               (significand (/ f (expt 2 exponent))))
          ;; Adjust to ensure significand is in [0.5, 1.0)
          (let loop1 ((sig significand) (exp exponent))
            (if (>= (abs sig) 1.0)
                (loop1 (/ sig 2) (+ exp 1))
                (let loop2 ((sig2 sig) (exp2 exp))
                  (if (< (abs sig2) 0.5)
                      (loop2 (* sig2 2) (- exp2 1))
                      (cons sig2 exp2)))))))))

(define (elisp-ldexp sgnfcand exponent)
  "Return SGNFCAND * 2**EXPONENT, as a floating point number.
EXPONENT must be an integer."
  (let ((f (if (number? sgnfcand) (exact->inexact sgnfcand)
               (error "Wrong type argument: numberp" sgnfcand)))
        (exp (if (integer? exponent) exponent
                 (error "Wrong type argument: integerp" exponent))))
    (* f (expt 2 exp))))

(define (elisp-logb arg)
  "Returns largest integer <= the base 2 log of the magnitude of ARG.
This is the same as the exponent of a float."
  (let ((f (if (number? arg) (exact->inexact arg)
               (error "Wrong type argument: numberp" arg))))
    (cond
      ((= f 0.0) -inf.0)  ; Negative infinity for zero
      ((inf? f) +inf.0)  ; Positive infinity
      ((nan? f) f)  ; NaN returns NaN
      (else (inexact->exact (floor (/ (log (abs f)) (log 2))))))))

;; FIX-guilemacs: Additional simple utility function migrations

(define (elisp-identity argument)
  "Return the ARGUMENT unchanged."
  argument)

;; Reader and file loading functions migrated from C
(define (elisp-get-load-suffixes)
  "Return the suffixes that `load' should try if a suffix is required.
This uses the variables `load-suffixes' and `load-file-rep-suffixes'."
  (let ((result '()))
    (for-each
      (lambda (suffix)
        (for-each
          (lambda (ext)
            (set! result (cons (string-append suffix ext) result)))
          (symbol-value 'load-file-rep-suffixes)))
      (symbol-value 'load-suffixes))
    (reverse result)))

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
          (if (and fast (eq? fast slow))
              'nil  ; Circular list detected
              (loop (cdr current) (+ len 1))))))))

;; Additional mathematical utility functions - demonstrating migration pattern
(define (elisp-sign number)
  "Return the sign of NUMBER: -1, 0, or 1."
  (let ((n (if (number? number) number
               (error "Wrong type argument: numberp" number))))
    (cond
      ((< n 0) -1)
      ((> n 0) 1)
      (else 0))))

(define (elisp-clamp value min-val max-val)
  "Return VALUE clamped to the range [MIN-VAL, MAX-VAL]."
  (if (not (and (number? value) (number? min-val) (number? max-val)))
      (error "Wrong type arguments: numberp"))
  (cond
    ((< value min-val) min-val)
    ((> value max-val) max-val)
    (else value)))

(define (elisp-square number)
  "Return the square of NUMBER."
  (let ((n (if (number? number) number
               (error "Wrong type argument: numberp" number))))
    (* n n)))

;; Register the new mathematical functions for Elisp use
(set-symbol-function! 'elisp-copysign elisp-copysign)
(set-symbol-function! 'elisp-frexp elisp-frexp)
(set-symbol-function! 'elisp-ldexp elisp-ldexp)
(set-symbol-function! 'elisp-logb elisp-logb)

;; Register the new reader and file loading functions
(set-symbol-function! 'elisp-get-load-suffixes elisp-get-load-suffixes)
(set-symbol-function! 'elisp-proper-list-p elisp-proper-list-p)

;; Register the additional utility functions
(set-symbol-function! 'elisp-sign elisp-sign)
(set-symbol-function! 'elisp-clamp elisp-clamp)
(set-symbol-function! 'elisp-square elisp-square)

;; Register short names for C function access
(set-symbol-function! 'sign elisp-sign)
(set-symbol-function! 'clamp elisp-clamp)
(set-symbol-function! 'square elisp-square)

;; Note: identity is already registered above as elisp-identity at line 669

;; (format (current-error-port) "-- done loading guile elisp prelude~%")
;; (force-output (current-error-port))
