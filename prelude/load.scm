;; (force-output (current-error-port))
;; (format (current-error-port) "-- loading guile elisp prelude~%")
;; (format (current-error-port) "-- prelude path: ~s~%" %prelude-filename)
;; (force-output (current-error-port))
(set-current-module (resolve-module '(language elisp runtime)))
;; (format (current-error-port) "-- current-module: ~s~%" (current-module))
;; (force-output (current-error-port))

(use-modules (rnrs bytevectors)) ; FIX: move to (use-modules (scheme base))
(use-modules (language elisp emacs))
(use-modules (system foreign-library))

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

(define (elisp-butlast list &optional n)
  "Return a copy of LIST with the last N elements removed.
If N is omitted or nil, remove only the last element."
  (let ((num (if (or (null? n) (eq? n #nil)) 1 n)))
    (if (or (not (integer? num)) (< num 0))
        list
        (let ((len (length list)))
          (if (<= len num)
              #nil
              (list-head list (- len num)))))))

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

(define (elisp-plist-get plist prop &optional predicate)
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
        (else (loop (cddr tail)))))))

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

(define (elisp-plist-member plist prop &optional predicate)
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
        (else (loop (cddr tail)))))))

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

(define (elisp-vectorp object)
  "Return t if OBJECT is a vector."
  (if (vector? object) #t #nil))

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

;; Phase 4: DEFUN function migrations from C to Guile - COMMENTED OUT FOR DEBUGGING
;;
;; (define (elisp-proper-list-p object)
;;   "Return OBJECT's length if it is a proper list, nil otherwise.
;; A proper list is neither circular nor dotted (i.e., its last cdr is nil)."
;;   (catch #t
;;     (lambda ()
;;       (let ((len (length object)))
;;         (scm_from_size_t len)))
;;     (lambda (key . args)
;;       ;; If length fails (circular, dotted, or not a list), return nil
;;       #nil)))
;;
;; (define (elisp-characterp object)
;;   "Return non-nil if OBJECT is a character.
;; In Emacs Lisp, characters are represented by character codes."
;;   (if (and (integer? object)
;;            (>= object 0)
;;            (<= object #x3FFFFF))  ; max-char value
;;       #t #nil))
;;
;; (define (elisp-max-char . args)
;;   "Return the maximum character code.
;; If UNICODE is non-nil, return the maximum character code defined by Unicode."
;;   (let ((unicode (if (null? args) #f (car args))))
;;     (if unicode
;;         (scm_from_uint32 #x10FFFF)  ; MAX_UNICODE_CHAR
;;         (scm_from_uint32 #x3FFFFF)))) ; MAX_CHAR
;;
;; (define (elisp-string-lessp string1 string2)
;;   "Return non-nil if STRING1 is less than STRING2 in lexicographic order.
;; Case is significant. Symbols are also allowed; their print names are used instead."
;;   (let ((s1 (if (symbol? string1) (symbol->string string1) string1))
;;         (s2 (if (symbol? string2) (symbol->string string2) string2)))
;;     (if (string<? s1 s2) #t #nil)))

;; Register Phase 3 functions for Elisp use
(set-symbol-function! 'symbolp elisp-symbolp)
; Note: bufferp kept in C for now due to C-specific buffer object handling
(set-symbol-function! 'consp elisp-consp)
(set-symbol-function! 'atom elisp-atom)
(set-symbol-function! 'listp elisp-listp)
(set-symbol-function! 'nlistp elisp-nlistp)
(set-symbol-function! 'vectorp elisp-vectorp)
(set-symbol-function! 'cons elisp-cons)
(set-symbol-function! 'car elisp-car)
(set-symbol-function! 'cdr elisp-cdr)
(set-symbol-function! 'car-safe elisp-car-safe)
(set-symbol-function! 'cdr-safe elisp-cdr-safe)
(set-symbol-function! 'list elisp-list)
(set-symbol-function! 'make-list elisp-make-list)

;; Phase 4 DEFUN function migrations are called directly from C code
;; to avoid infinite recursion. The elisp-* versions are available
;; for internal use but not registered as symbol replacements.

;; (format (current-error-port) "-- done loading guile elisp prelude~%")
;; (force-output (current-error-port))
