;;; Guilemacs Lisp
;;;
;;; String Operations
;;;
;;; String manipulation, comparison, and creation functions.
;;; Includes optimized C-string comparisons for C integration.

;;;
;;; String Metrics & Analysis
;;;

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

;;;
;;; String Creation & Conversion
;;;

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

;;;
;;; String Type Predicates
;;;

(define (elisp-multibyte-string-p object)
  "Return t if OBJECT is a multibyte string.
Return nil if OBJECT is either a unibyte string, or not a string.
In Guilemacs, all strings are UTF-8, so this always returns nil."
  #nil)

(define (elisp-stringp object)
  "Return t if OBJECT is a string or emacs-string wrapper (Phase 2)."
  (if (or (string? object)
          (and (defined? 'emacs-string-predicate)
               ((@ (emacs-string) emacs-string-predicate) object)))
      #t #nil))

(define (elisp-char-or-string-p object)
  "Return t if OBJECT is a character or a string (Phase 2: includes wrappers)."
  (if (or (char? object)
          (and (number? object) (>= object 0) (<= object #x3fffff))  ; Emacs character range
          (string? object)
          (and (defined? 'emacs-string-predicate)
               ((@ (emacs-string) emacs-string-predicate) object)))
      #t
      #nil))

;;;
;;; Optimized C-String Comparison Functions
;;;
;;; These functions are optimized for C integration, avoiding temporary
;;; Guile string object creation for frequently-used comparisons.
;;;

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

(define (elisp-string-ci-equal-none lisp-string)
  "Optimized check if a string equals 'None' (case-insensitive).
   Avoids repeated scm_from_utf8_string calls for this common constant."
  (if (string-ci=? lisp-string "None") #t #nil))

(define (elisp-string-equal-none lisp-string)
  "Optimized check if a string equals 'None' (case-sensitive).
   Avoids repeated scm_from_utf8_string calls for this common constant."
  (if (string=? lisp-string "None") #t #nil))

;;;
;;; Scheme Evaluation (Special)
;;;

(define (elisp-eval-scheme string)
  "Evaluate a string containing a Scheme expression."
  (eval-string string))

;;;

(define (elisp-capitalize obj)
  "Convert argument to capitalized form and return that."
  (cond
    ((string? obj) (string-capitalize obj))
    ((integer? obj) (string->number (string-capitalize (string (integer->char obj)))))
    (else obj)))



(define (elisp-downcase obj)
  "Convert argument to lower case and return that."
  (cond
    ((string? obj) (string-downcase obj))
    ((integer? obj) (string->number (string-downcase (string (integer->char obj)))))
    (else obj)))



(define (elisp-upcase obj)
  "Convert argument to upper case and return that."
  (cond
    ((string? obj) (string-upcase obj))
    ((integer? obj) (string->number (string-upcase (string (integer->char obj)))))
    (else obj)))



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



(define (elisp-string-search needle haystack start-pos)
  "Search for NEEDLE in HAYSTACK starting at START-POS.
Returns the position of the first match, or nil if not found.
Uses Guile's efficient string search with automatic memory management."
  (let ((needle-str (if (symbol? needle) (symbol->string needle) needle))
        (haystack-str (if (symbol? haystack) (symbol->string haystack) haystack))
        (start (if start-pos start-pos 0)))
    (let ((pos (string-contains haystack-str needle-str start)))
      (if pos pos #nil))))



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


;;; Registration with Elisp symbol table
;;; Phase 2: Registrations migrated from prelude/load.scm
;;;

;; String metrics
(set-symbol-function! 'string-bytes elisp-string-bytes)
(set-symbol-function! 'string-distance elisp-string-distance)

;; String creation & conversion
(set-symbol-function! 'char-to-string elisp-char-to-string)
(set-symbol-function! 'string-to-char elisp-string-to-char)
(set-symbol-function! 'byte-to-string elisp-byte-to-string)
(set-symbol-function! 'string elisp-string)
(set-symbol-function! 'unibyte-string elisp-unibyte-string)

;; String type predicates
(set-symbol-function! 'multibyte-string-p elisp-multibyte-string-p)
(set-symbol-function! 'stringp elisp-stringp)
(set-symbol-function! 'char-or-string-p elisp-char-or-string-p)

;; Optimized C-string comparisons
(set-symbol-function! 'string-equal-cstr elisp-string-equal-cstr)
(set-symbol-function! 'string-ci-equal-cstr elisp-string-ci-equal-cstr)
(set-symbol-function! 'symbol-name-equal-cstr elisp-symbol-name-equal-cstr)
(set-symbol-function! 'string-equal-two-cstrs elisp-string-equal-two-cstrs)
(set-symbol-function! 'string-ci-equal-two-cstrs elisp-string-ci-equal-two-cstrs)
(set-symbol-function! 'string-ci-equal-none elisp-string-ci-equal-none)
(set-symbol-function! 'string-equal-none elisp-string-equal-none)

;; Special
(set-symbol-function! 'eval-scheme elisp-eval-scheme)

(set-symbol-function! 'capitalize elisp-capitalize)
(set-symbol-function! 'downcase elisp-downcase)
(set-symbol-function! 'upcase elisp-upcase)
(set-symbol-function! 'string-equal-ignore-case elisp-string-equal-ignore-case)
(set-symbol-function! 'string-lessp-ignore-case elisp-string-lessp-ignore-case)
(set-symbol-function! 'string-prefix-p elisp-string-prefix-p)
(set-symbol-function! 'string-search elisp-string-search)
(set-symbol-function! 'string-suffix-p elisp-string-suffix-p)
(set-symbol-function! 'string-to-number elisp-string-to-number)