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
;;; Registration with Elisp symbol table
;;; NOTE: All registrations commented out to avoid conflicts with prelude/load.scm
;;; These functions are defined here but registered in load.scm for now.
;;; Once we migrate functions from load.scm to this module, we can uncomment
;;; the registrations incrementally.
;;;

;; String metrics
;; (set-symbol-function! 'string-bytes elisp-string-bytes)
;; (set-symbol-function! 'string-distance elisp-string-distance)

;; String creation & conversion
;; (set-symbol-function! 'char-to-string elisp-char-to-string)
;; (set-symbol-function! 'string-to-char elisp-string-to-char)
;; (set-symbol-function! 'byte-to-string elisp-byte-to-string)
;; (set-symbol-function! 'string elisp-string)
;; (set-symbol-function! 'unibyte-string elisp-unibyte-string)

;; String type predicates
;; (set-symbol-function! 'multibyte-string-p elisp-multibyte-string-p)
;; (set-symbol-function! 'stringp elisp-stringp)
;; (set-symbol-function! 'char-or-string-p elisp-char-or-string-p)

;; Optimized C-string comparisons
;; (set-symbol-function! 'string-equal-cstr elisp-string-equal-cstr)
;; (set-symbol-function! 'string-ci-equal-cstr elisp-string-ci-equal-cstr)
;; (set-symbol-function! 'symbol-name-equal-cstr elisp-symbol-name-equal-cstr)
;; (set-symbol-function! 'string-equal-two-cstrs elisp-string-equal-two-cstrs)
;; (set-symbol-function! 'string-ci-equal-two-cstrs elisp-string-ci-equal-two-cstrs)
;; (set-symbol-function! 'string-ci-equal-none elisp-string-ci-equal-none)
;; (set-symbol-function! 'string-equal-none elisp-string-equal-none)

;; Special
;; (set-symbol-function! 'eval-scheme elisp-eval-scheme)
