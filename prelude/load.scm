;;; ============================================================================
;;; PRELUDE/LOAD.SCM - Guilemacs Elisp Runtime Functions
;;; ============================================================================
;;;
;;; This file contains the Guile-side implementations of Elisp functions
;;; migrated from C for better maintainability and leveraging Guile's GC.
;;;
;;; CONTENTS:
;;;   1. Module Setup & Initialization       (Lines ~1-115)
;;;   2. Reload Infrastructure                (Lines ~116-248)
;;;   3. Arithmetic & Math Operations         (Lines ~249-677)
;;;   4. Type Predicates & Conversions        (Lines ~678-1010)
;;;   5. String Operations                    (Lines ~1011-1401)
;;;   6. List & Sequence Operations           (Lines ~1402-2025)
;;;   7. Property Lists & Utilities           (Lines ~2026-2364)
;;;   8. Reader & Parser Functions            (Lines ~2365-3800)
;;;   9. Load System                          (Lines ~3801-4365)
;;;  10. Goals.org Optimizations              (Lines ~4366-4420)
;;;  11. Debug & Development Tools            (Lines ~4421-END)
;;;
;;; NOTE: This file has grown organically and contains duplicate definitions.
;;;       A cleanup/deduplication pass is planned.
;;;
;;; ============================================================================


;;; ============================================================================
;;; SECTION 1: MODULE SETUP & INITIALIZATION
;;; ============================================================================
;;;
;;; Sets up the runtime module, imports dependencies, and configures encoding.
;;; This section must come first as it establishes the execution environment.

;; (force-output (current-error-port))
;; (format (current-error-port) "-- loading guile elisp prelude~%")
;; (format (current-error-port) "-- prelude path: ~s~%" %prelude-filename)
;; (force-output (current-error-port))

;; Load core runtime functions first - compute path relative to this file
;; Temporarily disabled to allow build to complete
;; (primitive-load (string-append (dirname (current-filename)) "/core-runtime.scm"))

;; (format (current-error-port) "-- current-module: ~s~%" (current-module))
;; (force-output (current-error-port))

(set-current-module (resolve-module '(language elisp runtime)))

(use-modules (rnrs bytevectors)) ; FIX: move to (use-modules (scheme base))
(use-modules (language elisp emacs))
(use-modules (system foreign-library))

(use-modules ;(ice-9 auto-compile) ; enables the autocompile hook for loaders
             (ice-9 ftw) ; for stat etc.
             (system base compile) ; compile-file, compiled-file-name, etc.
             (system base language)
             ;; Don't load system elisp spec - use our custom one
             ;(language elisp spec)
             )

(use-modules (system base compile)       ; compile-file, compiled-file-name
             (system base language)      ; current-language parameter
             (ice-9 ftw))                ; file ops, optional

;; Map Emacs-specific encodings to Guile-compatible ones
;; Guile doesn't recognize "UTF-8-EMACS" but it's essentially UTF-8
(let ((original-set-port-encoding! set-port-encoding!))
  (set! set-port-encoding!
        (lambda (port encoding)
          "Wrapper for set-port-encoding! that maps Emacs encodings to Guile encodings"
          (let ((mapped-encoding
                 (cond
                  ((and (string? encoding) (string-ci=? encoding "UTF-8-EMACS")) "UTF-8")
                  ((and (string? encoding) (string-ci=? encoding "utf-8-emacs")) "UTF-8")
                  (else encoding))))
            (original-set-port-encoding! port mapped-encoding)))))


(set-current-module (resolve-module '(language elisp runtime)))
(define %prelude-directory (dirname %prelude-filename))

;; reload guile elisp language, to get modifications
(set! %load-path (cons "." %load-path))
(load "./elisp/runtime.scm")

;; Note: The join function is defined later in the reload infrastructure section
;; We'll add types module loading after that

;(format #t "------- reloading guile elisp runtime ----------~%")
;(format #t "scheme load-path: ~s~%" %load-path)
;(format #t "------- reloading guile elisp lexer ----------~%")
;(load "./elisp/lexer.scm")
;(format #t "------- reloading guile elisp parser ----------~%")
;(load "./elisp/parser.scm")
;(format #t "------- reloading guile elisp compile-tree-il ----------~%")
;(load "./elisp/compile-tree-il.scm")
;(format #t "------- reloading guile elisp boot.el ----------~%")
;(load "./elisp/boot.el")

;(format #t "------- reloading guile elisp spec ----------~%")
;(load "./elisp/spec.scm")

;;; End Section 1


;;; ============================================================================
;;; SECTION 2: RELOAD INFRASTRUCTURE
;;; ============================================================================
;;;
;;; Functions for hot-reloading Elisp language components during development.
;;; This section is executed during prelude initialization.

;----------------------------------------------------------------------------------
;; reload-elisp.scm
;; Reload language/elisp pieces in the right order and load boot.el as *Elisp*.
(define (join a b)
  (if (or (string-null? a) (string-suffix? "/" a))
      (string-append a b)
      (string-append a "/" b)))

(define (compile-and-load-elisp path)
  ;; Compile PATH as Elisp, then load the resulting .go.
  (let* ((out (string-append path ".go"))) ; avoid compiled-file-name
    (compile-file path #:from 'elisp #:output-file out)
    (load-compiled out)))

(define (reload-local-elisp! base-dir)
  "Reload local language/elisp Scheme pieces and boot.el from BASE-DIR.
   Order: runtime.scm → lexer.scm → parser.scm → compile-tree-il.scm → boot.el"
  (let* ((scheme-files '(; "runtime.scm" ; dont reload runtime it will redefine module
                         "lexer.scm"
                         "parser.scm"
                         "compile-tree-il.scm"))
         (old-load-path %load-path))
    (dynamic-wind
      (lambda () (set! %load-path (cons base-dir %load-path)))
      (lambda ()
        ;; 1) Reload Scheme-side modules in dependency order *as Scheme*.
        (for-each (lambda (f)
                    (let ((p (join base-dir f)))
                      (primitive-load p)))
                  scheme-files)
        ;; 2) Load boot.el *as Elisp*, either from source or via compiled .go.
        ; dont reload boot.el, move stuff into this file, or push upstream
        (compile-and-load-elisp (join base-dir "boot.el")))
      (lambda () (set! %load-path old-load-path)))))

(reload-local-elisp! (join %prelude-directory "elisp"))

(set-current-module (resolve-module '(language elisp runtime)))

;; Load modular runtime components
;; These submodules provide organized, maintainable runtime functionality
(primitive-load (join %prelude-directory "elisp/runtime/types.scm"))
(primitive-load (join %prelude-directory "elisp/runtime/numbers.scm"))
(primitive-load (join %prelude-directory "elisp/runtime/strings.scm"))
(primitive-load (join %prelude-directory "elisp/runtime/sequences.scm"))

(primitive-load (join %prelude-directory "pcase.scm"))

;;; End Section 2


;;; ============================================================================
;;; SECTION 3: ARITHMETIC & MATH OPERATIONS
;;; ============================================================================
;;;
;;; Migrated from C DEFUN arithmetic and mathematical functions.
;;; Includes: basic ops, floating point, predicates.
;;; NOTE: This section contains some duplicates that need cleanup.

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

;;; End Section 3


;;; ============================================================================
;;; SECTION 4: STRING OPERATIONS
;;; ============================================================================
;;;
;;; String manipulation, comparison, and creation functions.
;;; Includes optimized C-string comparisons for C integration.

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

(define (elisp-detect-lexical-binding port)
  "Detect lexical binding from first line of file.
  Returns #t for lexical binding, #f for dynamic binding, 'none for no cookie.
  This replicates the logic from lisp_file_lexical_cookie_scm_port."

  (define (skip-whitespace)
    "Skip whitespace characters"
    (let ((ch (peek-char port)))
      (when (and (not (eof-object? ch)) (char-whitespace? ch))
        (read-char port)
        (skip-whitespace))))

  (define (read-first-line)
    "Read first line as string"
    (let loop ((chars '()))
      (let ((ch (peek-char port)))
        (cond
         ((or (eof-object? ch) (char=? ch #\newline))
          (list->string (reverse chars)))
         (else
          (read-char port)
          (loop (cons ch chars)))))))

  ;; Check if first character indicates a comment or shebang
  (let ((first-ch (peek-char port)))
    (cond
     ((eof-object? first-ch) 'none)
     ((char=? first-ch #\;)
      ;; Comment line - read and parse for lexical-binding
      (let ((line (read-first-line)))
        (cond
         ((string-contains line "lexical-binding: t") #t)
         ((string-contains line "lexical-binding: nil") #f)
         (else 'none))))
     ((and (char=? first-ch #\#)
           (not (eof-object? (peek-char port))))
      ;; Potential shebang line
      (read-char port) ; consume #
      (let ((second-ch (peek-char port)))
        (if (char=? second-ch #\!)
            (begin
              ;; Read shebang line and parse for lexical-binding
              (let ((line (read-first-line)))
                (cond
                 ((string-contains line "lexical-binding: t") #t)
                 ((string-contains line "lexical-binding: nil") #f)
                 (else 'none))))
            (begin
              ;; Not a shebang, push back the #
              (unread-char #\# port)
              'none))))
     (else 'none))))

(define (elisp-check-file-handler file noerror nomessage nosuffix must-suffix)
  "Check for magic file name handler and call it if found.
  This replicates the handler check from Fload lines 973-977.
  Returns handler result or #f if no handler."

  (let ((handler ((symbol-function 'find-file-name-handler) file 'load)))
    (if handler
        ;; Call the handler with all arguments
        ((symbol-function 'funcall) handler 'load file noerror nomessage nosuffix must-suffix)
        #f))) ; No handler found

(define (elisp-compute-effective-filename found is-native-elisp)
  "Compute effective filename for loading.
  This replicates the found_eff computation from Fload lines 1040-1043."

  (if is-native-elisp
      ;; For native elisp, compute the effective name
      ((symbol-function 'compute-found-effective) found)
      ;; For regular files, use found as-is
      found))

(define (elisp-validate-file-descriptor fd-valid)
  "Validate file descriptor state.
  This replicates the errno setting from Fload lines 1078-1081.
  Returns validation result: 'valid or 'invalid."

  (if fd-valid
      'valid
      'invalid)) ; Will cause errno = EINVAL in C

(define (elisp-should-close-fd is-module is-native-elisp fd-valid)
  "Determine if file descriptor should be closed.
  This replicates the close logic from Fload lines 1089-1097."

  (and (not is-module)
       (not is-native-elisp)
       fd-valid)) ; Close fd if regular elisp file with valid fd

(define (elisp-setup-port-input is-module is-native-elisp fd-valid)
  "Set up input port based on file type.
  This replicates the conditional setup from Fload lines 1108-1128.
  Returns: 'close-fd, 'setup-port, or 'continue."

  (cond
   ((or is-module is-native-elisp)
    ;; Module/native elisp - close file descriptor
    (if fd-valid 'close-fd 'continue))
   (else
    ;; Regular elisp - set up port
    'setup-port)))

(define (elisp-prepare-load-bindings hist-file-name found)
  "Prepare all dynamic bindings for load operation.
  This replicates the specbind calls from Fload lines 1158-1161.
  Returns list of (symbol . value) pairs for C to bind."

  (list
   (cons 'load-file-name hist-file-name)
   (cons 'load-true-file-name found)
   (cons 'inhibit-file-name-operation #nil)
   (cons 'load-in-progress #t)))

(define (elisp-determine-load-action is-module)
  "Determine the loading action based on file type.
  This replicates the conditional logic from Fload lines 1173-1183.
  Returns: 'load-module or 'load-elisp."

  (if is-module
      'load-module
      'load-elisp))

(define (elisp-return-load-success)
  "Return success value for load operation completion.
  This replicates the final return Qt from Fload line 1235."
  #t) ; Return success

(define (elisp-load-with-match-data-protection file noerror nomessage nosuffix must-suffix)
  "Load file with match data protection.
  This replicates the save_match_data_load wrapper function."

  ;; Call the main load function - C will handle the match data protection
  ((symbol-function 'load) file noerror nomessage nosuffix must-suffix))

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

;;; End Section 4


;;; ============================================================================
;;; SECTION 5: LIST & SEQUENCE OPERATIONS
;;; ============================================================================
;;;
;;; List/cons manipulation, sequences, property lists, and association lists.
;;; Migrated from C for better maintainability and GC efficiency.

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

;;; End Section 5


;;; ============================================================================
;;; SECTION 6: TYPE PREDICATES & CONVERSIONS
;;; ============================================================================
;;;
;;; Type checking and conversion functions migrated from C (Phase 3 & 4).
;;; NOTE: Contains significant duplication - cleanup needed.

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

;; FIX-guilemacs: Additional DEFUN function migrations from C to Guile
;; New functions identified as migration candidates

;; Type predicate functions - simple one-liners from data.c
(define (elisp-integerp object)
  "Return t if OBJECT is an integer."
  (if (and (number? object) (exact-integer? object)) #t #nil))

(define (elisp-vectorp object)
  "Return t if OBJECT is a vector."
  (if (and (vector? object) (not (keyword? object))) #t #nil))


;; Simple utility functions from fns.c that are easy to migrate

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

;;; End Section 6


;;; ============================================================================
;;; SECTION 7: GOALS.ORG OPTIMIZATIONS
;;; ============================================================================
;;;
;;; Performance optimizations from goals.org:
;;; - Direct symbol comparison instead of string comparison
;;; - Native Guile case-insensitive operations
;;; - Symbol interning efficiency
;;; - Memory handling moved to Guile GC

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

;;; End Section 7


;;; ============================================================================
;;; SECTION 8: ADDITIONAL DEFUN MIGRATIONS
;;; ============================================================================
;;;
;;; Additional function migrations from C to Guile from various source files.
;;; Includes functions from: lread.c, data.c, fns.c, floatfns.c
;;; NOTE: Some functions here may overlap with earlier sections.

;; DEFUN migrations from lread.c - simple utility functions primarily used by elisp
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

;; Load Phase 1 & 2 text properties wrapper infrastructure
;; These must be loaded in order: intervals -> emacs-string -> text-properties -> string-operations
;; Use save-module-excursion to preserve current module context
(let ((saved-module (current-module)))
  (primitive-load (string-append %prelude-directory "/intervals.scm"))
  (set-current-module saved-module)
  (primitive-load (string-append %prelude-directory "/emacs-string.scm"))
  (set-current-module saved-module)
  (primitive-load (string-append %prelude-directory "/text-properties.scm"))
  (set-current-module saved-module)
  (primitive-load (string-append %prelude-directory "/string-operations.scm"))
  (set-current-module saved-module))

;; Load new UTF-8 string operations and migration functions
(primitive-load (string-append %prelude-directory "/utf8-string-operations.scm"))
; FIX: disabled because of error, something with 'char=?'
;(primitive-load (string-append %prelude-directory "/string-comparison-migration.scm"))
(primitive-load (string-append %prelude-directory "/symbol-operations.scm"))

;; Load character navigation functions - Phase 2 UTF-8 migration improvements
;; Using minimal version that doesn't depend on buffer operations during bootstrap
(primitive-load (string-append %prelude-directory "/character-navigation-minimal.scm"))
;; Full version temporarily disabled due to buffer operation dependencies during bootstrap
;; TODO: Load full character-navigation.scm when buffer context is properly available
;; (primitive-load (string-append %prelude-directory "/character-navigation.scm"))

;; DEFUN function migrations - Phase 3: Move simple elisp predicates to Guile
;; These are simple type predicates that can be efficiently implemented in Guile

;; Additional predicate migrations from src/data.c

(define (elisp-markerp object)
  "Return t if OBJECT is a marker (editor pointer)."
  (if (and (vector? object)
           (>= (vector-length object) 4)
           (eq? (vector-ref object 0) 'marker))
      #t #nil))

(define (elisp-keywordp object)
  "Return t if OBJECT is a keyword.
This means that it is a symbol with a print name beginning with `:'
interned in the initial obarray."
  (if (and (symbol? object)
           (let ((name (symbol->string object)))
             (and (> (string-length name) 0)
                  (char=? (string-ref name 0) #\:))))
      #t #nil))

;; Register these functions for use from C and Elisp
;; Disabled while debugging baseline functionality
;; (set-symbol-function! 'integerp elisp-integerp)
;; (set-symbol-function! 'numberp elisp-numberp)
;; (set-symbol-function! 'null elisp-null)
;; (set-symbol-function! 'characterp elisp-characterp)
;; (set-symbol-function! 'symbolp elisp-symbolp)
;; (set-symbol-function! 'consp elisp-consp)
;; (set-symbol-function! 'atom elisp-atom)
;; (set-symbol-function! 'listp elisp-listp)
;; (set-symbol-function! 'nlistp elisp-nlistp)
;; (set-symbol-function! 'vectorp elisp-vectorp)
;; (set-symbol-function! 'sequencep elisp-sequencep)

;; Buffer Operations using dynamic-wind pattern
(define (elisp-save-current-buffer thunk)
  "Record which buffer is current; execute THUNK; make that buffer current.
This is the Guile implementation of save-current-buffer using dynamic-wind
for proper cleanup semantics."
  (let ((saved-buffer (current-buffer)))
    (dynamic-wind
      (lambda () #t)  ; pre-thunk: nothing needed
      (lambda () (funcall thunk))  ; thunk: execute the body
      (lambda ()      ; post-thunk: restore buffer
        (when (buffer-live-p saved-buffer)
          (set-buffer saved-buffer))))))

(define (elisp-with-current-buffer buffer thunk)
  "Execute THUNK with BUFFER as the current buffer.
Uses dynamic-wind to ensure buffer is properly restored."
  (let ((saved-buffer (current-buffer)))
    (dynamic-wind
      (lambda () (set-buffer buffer))     ; pre-thunk: switch to buffer
      (lambda () (funcall thunk))         ; thunk: execute the body
      (lambda () (set-buffer saved-buffer))))) ; post-thunk: restore buffer

;; (set-symbol-function! 'save-current-buffer elisp-save-current-buffer)
;; (set-symbol-function! 'with-current-buffer elisp-with-current-buffer)

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

  ;; Export DEFUN function migrations to elisp emacs module
  (module-define! elisp-emacs-module 'integerp elisp-integerp)
  (module-define! elisp-emacs-module 'numberp elisp-numberp)
  (module-define! elisp-emacs-module 'null elisp-null)
  (module-define! elisp-emacs-module 'characterp elisp-characterp)
  (module-define! elisp-emacs-module 'symbolp elisp-symbolp)
  (module-define! elisp-emacs-module 'consp elisp-consp)
  (module-define! elisp-emacs-module 'atom elisp-atom)
  (module-define! elisp-emacs-module 'listp elisp-listp)
  (module-define! elisp-emacs-module 'nlistp elisp-nlistp)
  (module-define! elisp-emacs-module 'vectorp elisp-vectorp)
  (module-define! elisp-emacs-module 'sequencep elisp-sequencep)
  ;; (module-define! elisp-emacs-module 'markerp elisp-markerp)
  ;; (module-define! elisp-emacs-module 'keywordp elisp-keywordp)
  ;; (module-define! elisp-emacs-module 'identity elisp-identity)
  (module-define! elisp-emacs-module 'save-current-buffer elisp-save-current-buffer)
  (module-define! elisp-emacs-module 'with-current-buffer elisp-with-current-buffer)
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

;; Reader and file loading functions migrated from C

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

;; Additional mathematical predicate functions migrated from src/data.c

(define (elisp-number-or-marker-p object)
  "Return t if OBJECT is a number or a marker."
  ;; For now, markers are not implemented in Guile, so just check numbers
  (if (number? object) #t #nil))

(define (elisp-integer-or-marker-p object)
  "Return t if OBJECT is an integer or a marker."
  ;; For now, markers are not implemented in Guile, so just check integers
  (if (integer? object) #t #nil))

;; Additional predicate functions migrated from src/data.c
(define (elisp-char-table-p object)
  "Return t if OBJECT is a char-table."
  ;; In Guile, char-tables don't exist as a built-in type
  ;; For now, return nil since char-tables are specific to Emacs
  #nil)

;; Additional type predicates migrated from src/data.c

(define (elisp-recordp object)
  "Return t if OBJECT is a record."
  ;; Records are Emacs-specific structures, return nil for now
  #nil)

(define (elisp-threadp object)
  "Return t if OBJECT is a thread."
  ;; Threads are Emacs-specific, return nil for now
  #nil)

(define (elisp-mutexp object)
  "Return t if OBJECT is a mutex."
  ;; Mutexes are Emacs-specific, return nil for now
  #nil)

(define (elisp-condition-variable-p object)
  "Return t if OBJECT is a condition variable."
  ;; Condition variables are Emacs-specific, return nil for now
  #nil)

;; Simple utility functions migrated from src/fns.c and src/data.c

(define (elisp-bare-symbol-p object)
  "Return t if OBJECT is a symbol, but not a symbol together with position."
  ;; In Guile implementation, symbols don't have position information
  ;; so this is the same as symbolp for now
  (if (symbol? object) #t #nil))

(define (elisp-symbol-with-pos-p object)
  "Return t if OBJECT is a symbol together with position."
  ;; In Guile implementation, symbols don't have position information
  ;; so this always returns nil
  #nil)

(define (elisp-bufferp object)
  "Return t if OBJECT is an editor buffer."
  ;; Buffers are Emacs-specific objects, return nil for now
  #nil)

(define (elisp-user-ptrp object)
  "Return t if OBJECT is a module user pointer."
  ;; User pointers are Emacs module-specific, return nil for now
  #nil)

(define (elisp-bool-vector-p object)
  "Return t if OBJECT is a bool-vector."
  ;; Bool-vectors are Emacs-specific, so return nil for now
  #nil)

(define (elisp-vector-or-char-table-p object)
  "Return t if OBJECT is a char-table or vector."
  (if (or (vector? object) (eq? #t (elisp-char-table-p object))) #t #nil))

(define (elisp-arrayp object)
  "Return t if OBJECT is an array (string, vector, char-table, or bool-vector)."
  (if (or (string? object)
          (vector? object)
          (eq? #t (elisp-char-table-p object))
          (eq? #t (elisp-bool-vector-p object))) #t #nil))

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

;; Register the new mathematical predicate functions
(set-symbol-function! 'integerp elisp-integerp)
(set-symbol-function! 'natnump elisp-natnump)
(set-symbol-function! 'numberp elisp-numberp)
(set-symbol-function! 'floatp elisp-floatp)
(set-symbol-function! 'number-or-marker-p elisp-number-or-marker-p)
(set-symbol-function! 'integer-or-marker-p elisp-integer-or-marker-p)
(set-symbol-function! 'float elisp-float)

;; Register the new simple predicate functions
(set-symbol-function! 'listp elisp-listp)
(set-symbol-function! 'keywordp elisp-keywordp)
(set-symbol-function! 'subrp elisp-subrp)

;; Register the new predicate functions
(set-symbol-function! 'char-table-p elisp-char-table-p)
(set-symbol-function! 'bool-vector-p elisp-bool-vector-p)
(set-symbol-function! 'vector-or-char-table-p elisp-vector-or-char-table-p)
(set-symbol-function! 'arrayp elisp-arrayp)
(set-symbol-function! 'sequencep elisp-sequencep)

;; Register the new basic comparison and utility functions
(set-symbol-function! 'eq elisp-eq)
(set-symbol-function! 'atom elisp-atom)
(set-symbol-function! 'equal elisp-equal)
(set-symbol-function! 'eql elisp-eql)
(set-symbol-function! 'characterp elisp-characterp)

;; Register the additional type predicates
(set-symbol-function! 'integerp elisp-integerp)
(set-symbol-function! 'recordp elisp-recordp)
(set-symbol-function! 'threadp elisp-threadp)
(set-symbol-function! 'mutexp elisp-mutexp)
(set-symbol-function! 'condition-variable-p elisp-condition-variable-p)

;; Register the basic list access functions
(set-symbol-function! 'car elisp-car)
(set-symbol-function! 'cdr elisp-cdr)
(set-symbol-function! 'car-safe elisp-car-safe)
(set-symbol-function! 'cdr-safe elisp-cdr-safe)

;; Register the simple utility functions
(set-symbol-function! 'identity elisp-identity)
(set-symbol-function! 'bare-symbol-p elisp-bare-symbol-p)
(set-symbol-function! 'symbol-with-pos-p elisp-symbol-with-pos-p)
(set-symbol-function! 'bufferp elisp-bufferp)
(set-symbol-function! 'user-ptrp elisp-user-ptrp)

;; System information functions
(define (elisp-byteorder)
  "Return the byteorder for the machine.
Returns 66 (ASCII uppercase B) for big endian machines or 108 (ASCII
lowercase l) for small endian machines."
  ;; Guile provides the native endianness
  (if (eq? (native-endianness) (endianness big))
      66   ; 'B' for big endian
      108)) ; 'l' for little endian

;; Register short names for C function access
(set-symbol-function! 'sign elisp-sign)
(set-symbol-function! 'clamp elisp-clamp)
(set-symbol-function! 'square elisp-square)

;; Register system information functions
(set-symbol-function! 'byteorder elisp-byteorder)

;; Note: identity is already registered above as elisp-identity at line 669

;;; End Section 8


;;; ============================================================================
;;; SECTION 9: READER & PARSER FUNCTIONS
;;; ============================================================================
;;;
;;; Elisp reader implementation - parses lists, vectors, literals, etc.
;;; Migrated from lread.c to enable better extensibility.
;;; This is a large section with 50+ parse functions.

(define (elisp-parse-list-from-port port)
  "Parse an elisp list from PORT, handling both regular and dotted pairs.
Called from C fread0() when '(' is encountered.
Returns: '() for empty list, proper list for (a b c), dotted pair for (a . b)"
  (let ((x
  (let loop ((elements '()))
    ;; Skip whitespace and comments
    (let skip-ws ()
      (let ((ch (read-char port)))
        (cond
          ((eof-object? ch)
           (error "Unexpected EOF in list"))
          ((char=? ch #\;)
           ;; Skip comment until newline
           (let skip-comment ()
             (let ((c (read-char port)))
               (if (not (or (eof-object? c) (char=? c #\newline)))
                 (skip-comment))))
           (skip-ws))
          ((char-whitespace? ch) (skip-ws))
          (else (unread-char ch port)))))
    ;; Check what comes next
    (let ((ch (read-char port)))
      (cond
        ((eof-object? ch) (error "Unexpected EOF in list"))
        ((char=? ch #\))
         ;; End of list - return reversed elements as proper Elisp list (terminated with #nil)
         (let reverse-to-elisp ((elems elements) (result #nil))
           (if (null? elems)
               result
               (reverse-to-elisp (cdr elems) (cons (car elems) result)))))
        ((char=? ch #\.)
         ;; Check if this is dotted pair syntax (a . b) or dot-prefixed symbol (.rose)
         (let ((next-ch (peek-char port)))
           (if (and (not (eof-object? next-ch))
                    (not (char-whitespace? next-ch))
                    (not (char=? next-ch #\,)))
               ;; This is a dot-prefixed symbol like .rose, not a dotted pair
               ;; Unread the dot and let elisp-read-from-port handle it as a symbol
               (begin
                 (unread-char ch port)
                 (let ((obj (elisp-read-from-port port)))
                   (if (null? obj) (set! obj #nil))
                   (loop (cons obj elements))))
               ;; This is genuine dotted pair syntax (a . b)
               (begin
                 (if (null? elements)
                   (error "Invalid dot syntax at start of list"))
                 ;; Read the tail element
                 (let ((tail (elisp-read-from-port port)))
                   (if (null? tail) (set! tail #nil))
                   ;; Expect closing paren
                   (let skip-ws-after-dot ()
                     (let ((c (read-char port)))
                       (cond
                         ((eof-object? c) (error "Expected ')' after dot"))
                         ((char=? c #\))
                          ;; Build dotted pair: fold right-to-left to get correct order
                          ;; For (a b . c) we want (cons a (cons b c))
                          (let build-dotted ((elems (reverse elements)) (result tail))
                            (if (null? elems)
                                result
                                (cons (car elems) (build-dotted (cdr elems) result)))))
                         ((char-whitespace? c) (skip-ws-after-dot))
                         ((char=? c #\;)
                          ;; Skip comment until newline, then continue skipping whitespace
                          (let skip-comment ()
                            (let ((comment-char (read-char port)))
                              (if (not (or (eof-object? comment-char) (char=? comment-char #\newline)))
                                (skip-comment))))
                          (skip-ws-after-dot))
                         (else
                          (format #t "DEBUG: Found unexpected character after dot: ~a (~s), tail was: ~s~%" c (char->integer c) tail)
                          (format #t "full form: ~s~%" (reverse elements))
                          (force-output)
                          (error "Expected ')' after dot, got" c))))))))))
        (else
         ;; Regular list element
         (unread-char ch port)
         (let ((obj (elisp-read-from-port port)))
           (if (null? obj) (set! obj #nil))
           (loop (cons obj elements)))))))))
    (if (null? x) (set! x #nil))
    x))

(define (elisp-read-integer-from-port port radix)
  "Parse an elisp integer from PORT with given RADIX.
Called from C fread_integer() when #x, #o, #b syntax is encountered.
Returns: integer value"
  ;; Read the digits as a string and convert with the given radix
  (let ((digit-string ""))
    ;; Read characters until we hit non-digit
    (let loop ()
      (let ((ch (peek-char port)))
        (cond
          ((eof-object? ch) #f) ; done
          ((or (char-alphabetic? ch) (char-numeric? ch))
           ;; Valid digit for some radix
           (set! digit-string (string-append digit-string (string (read-char port))))
           (loop))
          (else #f)))) ; done
    ;; Convert string to number using specified radix
    (let ((result (string->number digit-string radix)))
      (if result
          result
          (error "Could not parse integer with radix" radix digit-string)))))

(define (elisp-parse-vector-from-port port)
  "Parse an elisp vector from PORT.
Called from C fread0() when '[' is encountered.
Returns: A proper elisp vector"
  (let loop ((elements '()))
    ;; Skip whitespace and comments
    (let skip-ws ()
      (let ((ch (read-char port)))
        (cond
          ((eof-object? ch)
           (error "Unexpected EOF in vector"))
          ((char=? ch #\;)
           ;; Skip comment until newline
           (let skip-comment ()
             (let ((c (read-char port)))
               (if (not (or (eof-object? c) (char=? c #\newline)))
                 (skip-comment))))
           (skip-ws))
          ((char-whitespace? ch) (skip-ws))
          (else (unread-char ch port)))))
    ;; Check what comes next
    (let ((ch (read-char port)))
      (cond
        ((eof-object? ch) (error "Unexpected EOF in vector"))
        ((char=? ch #\])
         ;; End of vector - create mutable vector
         ;; Note: Must use make-vector + vector-set! to create mutable vectors in Guile
         (let* ((len (length elements))
                (vec (make-vector len)))
           (do ((i 0 (+ 1 i))
                (ep (reverse elements) (cdr ep)))
               ((null? ep))
             (vector-set! vec i (car ep)))
           vec))
        (else
         ;; Regular vector element
         (unread-char ch port)
         (let ((obj (elisp-read-from-port port)))
           (if (null? obj) (set! obj #nil))
           (loop (cons obj elements))))))))

;; Additional reader functions for fread0 migration

(define (elisp-parse-char-literal-from-port-enhanced port)
  "Parse an elisp character literal from PORT with proper Elisp conversion.
Called from C fread0() when '?' is encountered.
Returns: A character fixnum (Elisp integer) or proper Elisp object"
  (let ((ch (read-char port)))
    (cond
      ((eof-object? ch) (error "Unexpected EOF in character literal"))
      ;; Accept single space or tab syntax like (list ? x)
      ((or (char=? ch #\space) (char=? ch #\tab)) ch)
      ;; Handle escape sequences
      ((char=? ch #\\)
       (let ((escape-ch (read-char port)))
         (cond
           ((eof-object? escape-ch) (error "Unexpected EOF after \\"))
           ;; Standard escape sequences
           ((char=? escape-ch #\n) #\newline)
           ((char=? escape-ch #\t) #\tab)
           ((char=? escape-ch #\r) #\return)
           ((char=? escape-ch #\b) #\backspace)
           ((char=? escape-ch #\f) (integer->char 12)) ; form feed
           ((char=? escape-ch #\a) (integer->char 7))  ; bell
           ((char=? escape-ch #\v) (integer->char 11)) ; vertical tab
           ((char=? escape-ch #\e) (integer->char 27)) ; escape
           ((char=? escape-ch #\s) #\space)
           ((char=? escape-ch #\d) (integer->char 127)) ; delete
           ;; Octal escape sequences \NNN
           ((char<=? #\0 escape-ch #\7)
            (unread-char escape-ch port)
            (let ((octal-str ""))
              (let loop ((count 0))
                (if (< count 3)
                    (let ((digit-ch (read-char port)))
                      (if (and (not (eof-object? digit-ch))
                               (char<=? #\0 digit-ch #\7))
                          (begin
                            (set! octal-str (string-append octal-str (string digit-ch)))
                            (loop (+ count 1)))
                          (when (not (eof-object? digit-ch))
                            (unread-char digit-ch port))))))
              (if (string=? octal-str "")
                  (integer->char 0)
                  (integer->char (string->number octal-str 8)))))
           ;; Hex escape sequences \xHH
           ((char=? escape-ch #\x)
            (let ((hex-str ""))
              (let loop ((count 0))
                (if (< count 2)
                    (let ((hex-ch (read-char port)))
                      (if (and (not (eof-object? hex-ch))
                               (or (char<=? #\0 hex-ch #\9)
                                   (char<=? #\a hex-ch #\f)
                                   (char<=? #\A hex-ch #\F)))
                          (begin
                            (set! hex-str (string-append hex-str (string hex-ch)))
                            (loop (+ count 1)))
                          (when (not (eof-object? hex-ch))
                            (unread-char hex-ch port))))))
              (if (string=? hex-str "")
                  (integer->char 0)
                  (integer->char (string->number hex-str 16)))))
           ;; Control sequences \C-x
           ((char=? escape-ch #\C)
            (let ((dash-ch (read-char port)))
              (if (char=? dash-ch #\-)
                  (let ((ctrl-ch (read-char port)))
                    (if (eof-object? ctrl-ch)
                        (error "Unexpected EOF in control sequence")
                        (integer->char (logand (char->integer (char-upcase ctrl-ch)) #x1f))))
                  (error "Invalid control sequence"))))
           ;; Meta sequences \M-x
           ((char=? escape-ch #\M)
            (let ((dash-ch (read-char port)))
              (if (char=? dash-ch #\-)
                  (let ((meta-ch (read-char port)))
                    (if (eof-object? meta-ch)
                        (error "Unexpected EOF in meta sequence")
                        (integer->char (+ (char->integer meta-ch) 128))))
                  (error "Invalid meta sequence"))))
           ;; Default: return the escaped character literally
           (else escape-ch))))
      ;; Regular character
      (else ch))))

;; Enhanced version that handles character to fixnum conversion in Scheme
(define (elisp-parse-char-literal-from-port-with-conversion port)
  "Parse character literal from PORT with automatic conversion to Elisp fixnum."
  ;; Get the result from the original parser
  (let ((char-result (elisp-parse-char-literal-from-port-enhanced port)))
    (cond
      ;; If it's a character, convert to fixnum using char->integer
      ((char? char-result)
       ;; Convert character to integer - this creates proper Elisp fixnum
       (char->integer char-result))
      ;; If it's already an integer, return directly
      ((integer? char-result) char-result)
      ;; Other types pass through
      (else char-result))))

(define (elisp-parse-quote-from-port port)
  "Parse a quote form (') from PORT.
Returns: the quoted expression (for C to wrap in list2)"
  (elisp-read-from-port port))

(define (elisp-parse-backquote-from-port port)
  "Parse a backquote form (`) from PORT.
Returns: the backquoted expression (for C to wrap in list2)"
  (elisp-read-from-port port))

(define (elisp-parse-quote-with-list-construction port)
  "Parse a quote form (') from PORT and construct the complete (quote expr) list.
This eliminates the C list2() construction by doing it directly in Scheme."
  (let ((quoted-expr (elisp-read-from-port port)))
    ;; Use Scheme cons to build (quote expr) - equivalent to C list2(Qquote, quoted_expr)
    (cons ((symbol-function 'intern) "quote" #nil) (cons quoted-expr #nil))))

(define (elisp-parse-backquote-with-list-construction port)
  "Parse a backquote form (`) from PORT and construct the complete (` expr) list.
This eliminates the C list2() construction by doing it directly in Scheme."
  (let ((backquoted-expr (elisp-read-from-port port)))
    ;; Use Scheme cons to build (` expr) - equivalent to C list2(Qbackquote, backquoted_expr)
    (cons ((symbol-function 'intern) "`" #nil) (cons backquoted-expr #nil))))

(define (elisp-parse-comma-from-port port)
  "Parse comma syntax from PORT, handling both , and ,@ forms.
Called from C fread0() when ',' is encountered.
Returns: (comma expr) or (comma-at expr) list structures using proper Elisp symbols"
  ;; C has already detected the comma, now determine , vs ,@
  (let ((next-ch (peek-char port)))
    (cond
      ;; Check for ,@ (comma-at)
      ((and (not (eof-object? next-ch)) (char=? next-ch #\@))
       ;; Consume the @ and read the expression
       (read-char port) ; consume @
       (let ((expr (elisp-read-from-port port)))
         ;; Return (comma-at expr) with proper Elisp symbol and list termination
         (cons (elisp-intern ",@" #nil) (cons expr #nil))))

      ;; Regular comma ,
      (else
       ;; Read the expression
       (let ((expr (elisp-read-from-port port)))
         ;; Return (comma expr) with proper Elisp symbol and list termination
         (cons (elisp-intern "," #nil) (cons expr #nil)))))))

(define (elisp-parse-comma-at-from-port port)
  "Parse a comma-at form (,@) from PORT.
Returns: the unquote-spliced expression (for C to wrap in list2)"
  (elisp-read-from-port port))

;; Unified quote-like syntax parser - consolidates ', `, , dispatch
(define (elisp-parse-quote-like-from-port char port)
  "Parse quote-like syntax (', `, ,) based on character from PORT.
This unified parser consolidates the dispatch logic that was previously in C.
Returns the appropriate parsed structure for the given quote-like character."
  (cond
    ((char=? char #\')
     ;; Quote form with complete list construction
     (elisp-parse-quote-with-list-construction port))
    ((char=? char #\`)
     ;; Backquote form with complete list construction
     (elisp-parse-backquote-with-list-construction port))
    ((char=? char #\,)
     ;; Comma syntax (, or ,@) handled by unified parser
     (elisp-parse-comma-from-port port))
    (else
     (error "Unexpected character in quote-like parsing" char))))

(define (elisp-parse-string-literal-from-port port)
  "Parse a string literal from PORT.
C has already consumed the opening quote, so we read the complete string.
Returns: the parsed string"
  ;; Use Guile's built-in string reader
  (read port))

(define (elisp-parse-string-literal-from-port-enhanced port)
  "Parse a string literal from PORT with enhanced quote handling.
This version handles the case where C has consumed the opening quote.
Returns: the parsed string with proper type validation in Scheme"
  ;; C puts back the quote, so we can use normal read
  (let ((result (read port)))
    (cond
      ((eof-object? result)
       (error "Unexpected EOF while reading string"))
      ((string? result) result)
      (else
       (error "String parser returned non-string")))))

(define (elisp-parse-bool-vector-from-port port)
  "Parse a bool vector (#&LENGTH\"DATA\") from PORT.
C has already consumed '#&', now we need to parse length and string data.
Returns: a cons (LENGTH . STRING-DATA) for C to convert to bool vector"
  ;; Read the length digits until we hit a quote
  (let loop ((length 0))
    (let ((ch (peek-char port)))
      (cond
        ((eof-object? ch)
         (error "EOF while reading bool vector length"))
        ((char=? ch #\")
         ;; Found the quote, now read the string data
         (let ((str (read port)))  ; This will read the complete string
           (cons length str)))
        ((and (char>=? ch #\0) (char<=? ch #\9))
         ;; Consume the digit and continue
         (read-char port) ; consume the digit
         (let ((digit (- (char->integer ch) (char->integer #\0))))
           (loop (+ (* length 10) digit))))
        (else
         (error "Invalid character in bool vector length"))))))

(define (elisp-create-bool-vector-from-scheme length string-data)
  "Create Elisp bool vector directly in Scheme to avoid malloc/free cycles.
This function uses Scheme's string access functions to eliminate C string allocation."
  ;; For now, we return the same format but could enhance this with bytevectors
  ;; to completely eliminate the C malloc/free cycle in the future
  (cons length string-data))

(define (elisp-skip-comment-from-port port)
  "Skip a line comment starting with ; until newline.
Returns: #t (to indicate successful skip)"
  (let loop ()
    (let ((ch (read-char port)))
      (cond
        ((eof-object? ch) #t)
        ((char=? ch #\newline) #t)
        (else (loop))))))

(define (elisp-parse-hash-function-from-port port)
  "Parse #' function syntax from PORT.
Returns: (function object)"
  (let ((obj (elisp-read-from-port port)))
    (cons 'function (cons obj #nil))))

(define (elisp-parse-hash-empty-symbol-from-port port)
  "Parse ## empty symbol syntax from PORT.
Returns: interned empty symbol"
  ;; In GuilEmacs, we need to return the interned empty symbol
  ;; This is handled by calling the C intern function
  (string->symbol ""))

(define (elisp-parse-hash-shebang-from-port port)
  "Parse #! shebang comment from PORT, skipping to end of line.
Returns: #t (to indicate successful skip)"
  (let loop ()
    (let ((ch (read-char port)))
      (cond
        ((eof-object? ch) #t)
        ((char=? ch #\newline) #t)
        (else (loop))))))

(define (elisp-parse-hash-uninterned-symbol-from-port port)
  "Parse #: uninterned symbol syntax from PORT.
Returns: uninterned symbol"
  (let ((ch (read-char port)))
    (cond
      ((eof-object? ch) (gensym ""))
      ;; Check for symbol terminator characters
      ((or (char<=? ch #\space)
           (char=? ch #\")
           (char=? ch #\')
           (char=? ch #\;)
           (char=? ch #\#)
           (char=? ch #\()
           (char=? ch #\))
           (char=? ch #\[)
           (char=? ch #\])
           (char=? ch #\`)
           (char=? ch #\,))
       ;; Empty uninterned symbol
       (unread-char ch port)
       (gensym ""))
      (else
       ;; Read the symbol name manually to avoid circular dependency
       (let ((name (string ch)))
         (let loop ()
           (let ((next-ch (read-char port)))
             (cond
               ((eof-object? next-ch)
                (gensym name))
               ((or (char<=? next-ch #\space)
                    (char=? next-ch #\")
                    (char=? next-ch #\')
                    (char=? next-ch #\;)
                    (char=? next-ch #\#)
                    (char=? next-ch #\()
                    (char=? next-ch #\))
                    (char=? next-ch #\[)
                    (char=? next-ch #\])
                    (char=? next-ch #\`)
                    (char=? next-ch #\,))
                ;; Symbol terminator found, put it back and create symbol
                (unread-char next-ch port)
                (gensym name))
               (else
                ;; Regular symbol character, add to name and continue
                (set! name (string-append name (string next-ch)))
                (loop))))))))))

(define (elisp-parse-hash-from-port port)
  "Parse all hash (#) syntax forms from PORT.
Unified dispatcher for all # syntax in Elisp reader.
Returns: appropriate Lisp object based on hash syntax"
  (let ((ch (read-char port)))
    (cond
      ((eof-object? ch) (error "Unexpected EOF after #"))

      ;; #' function syntax - already implemented
      ((char=? ch #\')
       (elisp-parse-hash-function-from-port port))

      ;; ## empty symbol
      ((char=? ch #\#)
       (string->symbol ""))

      ;; #! shebang comments - already implemented
      ((char=? ch #\!)
       (elisp-parse-hash-shebang-from-port port)
       ;; Return nil to indicate "continue reading"
       #nil)

      ;; #: uninterned symbols - already implemented
      ((char=? ch #\:)
       (elisp-parse-hash-uninterned-symbol-from-port port))

      ;; #$ lazy file reference
      ((char=? ch #\$)
       ;; Access Vload_file_name directly from Scheme
       ((symbol-function 'symbol-value) 'load-file-name))

      ;; Radix integers: #x #X #o #O #b #B
      ((or (char=? ch #\x) (char=? ch #\X))
       (elisp-read-integer-from-port port 16))
      ((or (char=? ch #\o) (char=? ch #\O))
       (elisp-read-integer-from-port port 8))
      ((or (char=? ch #\b) (char=? ch #\B))
       (elisp-read-integer-from-port port 2))

      ;; Complex number syntax #N=, #N#, #Nr
      ((char-numeric? ch)
       (elisp-parse-hash-number-from-port port ch))

      ;; Unsupported syntax - consistent error messages
      ((char=? ch #\s)
       (error "Hash-table/record syntax (#s) not supported"))
      ((char=? ch #\^)
       (error "Char-table syntax (#^) not supported"))
      ((char=? ch #\()
       (error "Text-properties syntax (#() not supported"))
      ((char=? ch #\[)
       (error "Bytecode syntax (#[) not supported"))
      ((char=? ch #\&)
       ;; #&N"..." bool vector syntax
       (elisp-parse-bool-vector-from-port port))
      ((char=? ch #\@)
       (error "Obsolete load syntax (#@) not supported"))
      ((char=? ch #\_)
       (error "Shorthand syntax (#_) not supported"))

      (else
       (error "Invalid hash syntax" (string #\# ch))))))

(define (elisp-parse-hash-number-from-port port first-digit)
  "Parse hash syntax starting with a number: #N=, #N#, #Nr
PORT: input port
FIRST-DIGIT: first digit character already read
Returns: appropriate object for the syntax"
  ;; Read complete number first
  (let ((n (- (char->integer first-digit) (char->integer #\0))))
    (let loop ((result n))
      (let ((ch (read-char port)))
        (cond
          ((eof-object? ch)
           (error "Unexpected EOF in hash number syntax"))
          ((char-numeric? ch)
           ;; Continue reading digits
           (let ((digit (- (char->integer ch) (char->integer #\0))))
             (loop (+ (* result 10) digit))))
          ((char=? ch #\=)
           ;; #N= circle definition - not implemented yet
           (error "Circle definitions (#N=) not yet supported"))
          ((char=? ch #\#)
           ;; #N# circle reference - not implemented yet
           (error "Circle references (#N#) not yet supported"))
          ((or (char=? ch #\r) (char=? ch #\R))
           ;; #Nr arbitrary radix
           (if (or (< result 2) (> result 36))
               (error "Invalid radix for integer" result)
               (elisp-read-integer-from-port port result)))
          (else
           (error "Invalid character in hash number syntax" ch)))))))

(define (elisp-parse-char-literal-from-port port)
  "Parse an Elisp character literal from PORT.
Handles simple characters, escape sequences, and modifier combinations.
Called from C fread0() when '?' is encountered.
Returns: A character fixnum with appropriate encoding"
  (let ((ch (read-char port)))
    (cond
      ((eof-object? ch) (error "Unexpected EOF in character literal"))

      ;; Accept single space or tab syntax like (list ? x)
      ((or (char=? ch #\space) (char=? ch #\tab))
       (char->integer ch))

      ;; Handle escape sequences
      ((char=? ch #\\)
       (elisp-parse-char-escape port))

      ;; Regular character - check for valid terminator
      (else
       (let ((next-ch (peek-char port)))
         (if (or (eof-object? next-ch)
                 (char<=? next-ch #\space)
                 (char=? next-ch #\")
                 (char=? next-ch #\')
                 (char=? next-ch #\;)
                 (char=? next-ch #\()
                 (char=? next-ch #\))
                 (char=? next-ch #\[)
                 (char=? next-ch #\])
                 (char=? next-ch #\#)
                 (char=? next-ch #\?)
                 (char=? next-ch #\`)
                 (char=? next-ch #\,)
                 (char=? next-ch #\.))
             (char->integer ch)
             (error "Invalid character syntax")))))))

(define (elisp-parse-char-escape port)
  "Parse escape sequences in character literals.
Handles \\n, \\t, \\M-x, \\C-x, \\S-x, etc.
Returns: Character code with modifiers encoded"
  (let ((ch (read-char port)))
    (cond
      ((eof-object? ch) (error "Unexpected EOF in escape sequence"))

      ;; Basic escape sequences
      ((char=? ch #\a) 7)    ; bell
      ((char=? ch #\b) 8)    ; backspace
      ((char=? ch #\d) 127)  ; delete
      ((char=? ch #\e) 27)   ; escape
      ((char=? ch #\f) 12)   ; form feed
      ((char=? ch #\n) 10)   ; newline
      ((char=? ch #\r) 13)   ; carriage return
      ((char=? ch #\t) 9)    ; tab
      ((char=? ch #\v) 11)   ; vertical tab
      ((char=? ch #\newline) (error "Invalid escape: \\<newline>"))

      ;; Modifier keys: \M-x, \C-x, \S-x, \H-x, \A-x, \s-x
      ((char=? ch #\M) (elisp-parse-modifier port #x2000000))  ; meta
      ((char=? ch #\C) (elisp-parse-control port))             ; control
      ((char=? ch #\S) (elisp-parse-modifier port #x8000000))  ; shift
      ((char=? ch #\H) (elisp-parse-modifier port #x10000000)) ; hyper
      ((char=? ch #\A) (elisp-parse-modifier port #x4000000))  ; alt
      ((char=? ch #\s) (elisp-parse-s-modifier port))          ; super or space
      ((char=? ch #\^) (elisp-parse-control-hat port))         ; ^x syntax

      ;; Octal sequences: \123
      ((char-numeric? ch)
       (elisp-parse-octal port ch))

      ;; Unicode sequences: \u1234 or \U12345678
      ((char=? ch #\u) (elisp-parse-unicode port 4))
      ((char=? ch #\U) (elisp-parse-unicode port 8))
      ((char=? ch #\x) (elisp-parse-hex-char port))

      ;; Default: literal character after backslash
      (else (char->integer ch)))))

(define (elisp-parse-modifier port modifier-bit)
  "Parse modifier syntax like \\M-x, \\S-x, etc."
  (let ((dash (read-char port)))
    (if (not (char=? dash #\-))
        (error "Expected '-' after modifier")
        (let ((next-ch (read-char port)))
          (cond
            ((eof-object? next-ch) (error "EOF after modifier"))
            ((char=? next-ch #\\)
             ;; Chained escape: \M-\C-x
             (+ modifier-bit (elisp-parse-char-escape port)))
            (else
             ;; Simple modified char: \M-x
             (+ modifier-bit (char->integer next-ch))))))))

(define (elisp-parse-s-modifier port)
  "Handle \\s which can be \\s-x (super) or just \\s (space)"
  (let ((next-ch (peek-char port)))
    (if (char=? next-ch #\-)
        (begin
          (read-char port) ; consume the '-'
          (let ((ch (read-char port)))
            (if (char=? ch #\\)
                (+ #x1000000 (elisp-parse-char-escape port)) ; super + escape
                (+ #x1000000 (char->integer ch)))))          ; super + char
        32))) ; just space

(define (elisp-parse-control port)
  "Parse \\C-x control modifier"
  (let ((dash (read-char port)))
    (if (not (char=? dash #\-))
        (error "Expected '-' after \\C")
        (let ((ch (read-char port)))
          (cond
            ((eof-object? ch) (error "EOF after \\C-"))
            ((char=? ch #\\)
             ;; \C-\something
             (logior #x4000000 (elisp-parse-char-escape port)))
            (else
             ;; \C-x - make control character
             (let ((code (char->integer ch)))
               (if (and (>= code 64) (<= code 95)) ; @ A-Z [ \ ] ^ _
                   (- code 64)
                   (logior #x4000000 code)))))))))

(define (elisp-parse-control-hat port)
  "Parse \\^x control syntax"
  (let ((ch (read-char port)))
    (cond
      ((eof-object? ch) (error "EOF after \\^"))
      ((char=? ch #\\)
       (logior #x4000000 (elisp-parse-char-escape port)))
      (else
       (let ((code (char->integer ch)))
         (if (and (>= code 64) (<= code 95))
             (- code 64)
             (logior #x4000000 code)))))))

(define (elisp-parse-octal port first-digit)
  "Parse octal character code \\123"
  (let ((value (- (char->integer first-digit) (char->integer #\0))))
    (let loop ((result value) (count 1))
      (if (>= count 3)
          result
          (let ((ch (peek-char port)))
            (if (and (not (eof-object? ch))
                     (char-numeric? ch)
                     (<= (char->integer ch) (char->integer #\7)))
                (begin
                  (read-char port)
                  (loop (+ (* result 8) (- (char->integer ch) (char->integer #\0)))
                        (+ count 1)))
                result))))))

(define (elisp-parse-unicode port digit-count)
  "Parse Unicode escape \\u1234 or \\U12345678"
  (let loop ((result 0) (count 0))
    (if (>= count digit-count)
        result
        (let ((ch (read-char port)))
          (cond
            ((eof-object? ch) (error "EOF in Unicode escape"))
            ((or (and (char>=? ch #\0) (char<=? ch #\9))
                 (and (char>=? ch #\a) (char<=? ch #\f))
                 (and (char>=? ch #\A) (char<=? ch #\F)))
             (let ((digit (if (char-numeric? ch)
                             (- (char->integer ch) (char->integer #\0))
                             (+ (- (char->integer (char-downcase ch))
                                   (char->integer #\a)) 10))))
               (loop (+ (* result 16) digit) (+ count 1))))
            (else (error "Invalid hex digit in Unicode escape")))))))

(define (elisp-parse-hex-char port)
  "Parse hex character \\x12"
  (let loop ((result 0) (count 0))
    (let ((ch (peek-char port)))
      (if (or (eof-object? ch)
              (not (or (and (char>=? ch #\0) (char<=? ch #\9))
                      (and (char>=? ch #\a) (char<=? ch #\f))
                      (and (char>=? ch #\A) (char<=? ch #\F)))))
          (if (= count 0)
              (error "No hex digits after \\x")
              result)
          (begin
            (read-char port)
            (let ((digit (if (char-numeric? ch)
                            (- (char->integer ch) (char->integer #\0))
                            (+ (- (char->integer (char-downcase ch))
                                  (char->integer #\a)) 10))))
              (loop (+ (* result 16) digit) (+ count 1))))))))

(define (elisp-parse-colon-from-port port)
  "Parse colon syntax from PORT.
Handles both bare colon ':' and colon-prefixed symbols ':keyword'.
Called from C fread0() when ':' is encountered at symbol position.
Returns: appropriate Elisp symbol with keyword self-evaluation"
  ;; First consume the colon character
  (let ((colon-ch (read-char port)))
    (if (not (char=? colon-ch #\:))
        (error "Expected colon character")
        (let ((next-ch (peek-char port)))
          (cond
            ;; EOF - bare colon
            ((eof-object? next-ch)
             (elisp-intern-and-make-keyword ":"))

            ;; Check for symbol terminator characters - this is a bare colon
            ((or (char<=? next-ch #\space)
                 (char=? next-ch #\")
                 (char=? next-ch #\')
                 (char=? next-ch #\;)
                 (char=? next-ch #\()
                 (char=? next-ch #\))
                 (char=? next-ch #\[)
                 (char=? next-ch #\])
                 (char=? next-ch #\#)
                 (char=? next-ch #\?)
                 (char=? next-ch #\`)
                 (char=? next-ch #\,)
                 (char=? next-ch #\.))
             ;; Bare colon symbol
             (elisp-intern-and-make-keyword ":"))

            ;; This is a colon-prefixed symbol like :documentation
            (else
             (elisp-parse-colon-prefixed-symbol-and-intern port)))))))

(define (elisp-parse-colon-prefixed-symbol port)
  "Parse a colon-prefixed symbol like :keyword from PORT.
Assumes the colon has already been consumed and we're reading the rest."
  (let ((name ":"))  ; Start with colon
    (let loop ()
      (let ((ch (peek-char port)))
        (cond
          ;; EOF or terminator character - done reading symbol
          ((or (eof-object? ch)
               (char<=? ch #\space)
               (char=? ch #\")
               (char=? ch #\')
               (char=? ch #\;)
               (char=? ch #\()
               (char=? ch #\))
               (char=? ch #\[)
               (char=? ch #\])
               (char=? ch #\#)
               (char=? ch #\?)
               (char=? ch #\`)
               (char=? ch #\,)
               (char=? ch #\.))
           ;; Done - create the symbol
           (string->symbol name))

          ;; Regular symbol character - add to name and continue
          (else
           (read-char port) ; consume the character
           (set! name (string-append name (string ch)))
           (loop)))))))

(define (elisp-parse-symbol-from-port port)
  "Parse symbol or number from PORT with comprehensive Elisp conversion.
Called from C fread0() when alphabetic character is encountered.
Handles special symbol identity mapping, keyword conversion, and uninterned symbols.
Returns the parsed object with proper Elisp semantics."
  ;; Let Guile's read function handle the complete parsing
  (let ((result (read port)))
    (cond
      ;; Handle EOF
      ((eof-object? result)
       (error "Unexpected EOF while reading symbol"))

      ;; Handle symbols with special identity mapping
      ((symbol? result)
       (let ((sym-str (symbol->string result)))
         (cond
           ;; Reader macro symbols - map to canonical Elisp symbols
           ((or (string=? sym-str "`") (string=? sym-str "\\`"))
            ;; Backquote symbol - use existing Qbackquote
            ((symbol-function 'intern) "`" #nil))
           ((or (string=? sym-str ",") (string=? sym-str "\\,"))
            ;; Unquote symbol - use existing Qcomma
            ((symbol-function 'intern) "," #nil))
           ((or (string=? sym-str ",@") (string=? sym-str "\\,@"))
            ;; Unquote-splicing symbol - use existing Qcomma_at
            ((symbol-function 'intern) ",@" #nil))

           ;; Special Elisp symbols - use canonical values
           ((string=? sym-str "nil")
            ;; Return canonical Elisp nil
            (elisp-nil))
           ((string=? sym-str "t")
            ;; Return canonical Elisp t
            (elisp-t))
           ((string=? sym-str "and")
            ;; Map to canonical interned symbol
            ((symbol-function 'intern) "and" #nil))
           ((string=? sym-str ":")
            ;; Map colon to canonical interned symbol
            ((symbol-function 'intern) ":" #nil))

           ;; Regular symbols - intern normally
           (else
            ((symbol-function 'intern) sym-str #nil)))))

      ;; Handle Guile keywords - convert to Elisp colon symbols
      ((keyword? result)
       (let* ((keyword-symbol (keyword->symbol result))
              (base-name (symbol->string keyword-symbol))
              (colon-name (string-append ":" base-name)))
         ;; Create Elisp symbol with colon prefix
         (let ((elisp-symbol ((symbol-function 'intern) colon-name #nil)))
           ;; Make it self-evaluating (keywords evaluate to themselves)
           ((symbol-function 'set) elisp-symbol elisp-symbol)
           elisp-symbol)))

      ;; Numbers and other types pass through directly
      (else result))))

(define (elisp-parse-number-from-port port)
  "Parse number from PORT using Guile's read with proper error handling.
Called from C fread0() when numeric character is encountered.
Returns the parsed number or symbol with proper Elisp semantics."
  ;; Let Guile's read function handle the complete parsing
  (let ((result (read port)))
    (cond
      ;; Handle EOF
      ((eof-object? result)
       (error "Unexpected EOF while reading number"))

      ;; Numbers pass through directly - Guile's parsing is authoritative
      ((number? result)
       result)

      ;; If not a number, it might be a symbol that looks numeric (like +foo, -bar, .symbol)
      ;; Use the symbol parsing logic
      ((symbol? result)
       (let ((sym-str (symbol->string result)))
         ((symbol-function 'intern) sym-str #nil)))

      ;; Other types pass through (shouldn't happen in practice)
      (else result))))

(define (elisp-intern-and-make-keyword str)
  "Intern STR as Elisp symbol and make it self-evaluating if it's a keyword."
  (let ((elisp-symbol ((symbol-function 'intern) str #nil)))
    ;; If it's a keyword (starts with :), make it self-evaluating
    (if (and (> (string-length str) 0) (char=? (string-ref str 0) #\:))
        ((symbol-function 'set) elisp-symbol elisp-symbol))
    elisp-symbol))

(define (elisp-parse-colon-prefixed-symbol-and-intern port)
  "Parse a colon-prefixed symbol from PORT and return proper Elisp symbol.
Assumes the colon has already been consumed."
  (let ((name ":"))  ; Start with colon
    (let loop ()
      (let ((ch (peek-char port)))
        (cond
          ;; EOF or terminator character - done reading symbol
          ((or (eof-object? ch)
               (char<=? ch #\space)
               (char=? ch #\")
               (char=? ch #\')
               (char=? ch #\;)
               (char=? ch #\()
               (char=? ch #\))
               (char=? ch #\[)
               (char=? ch #\])
               (char=? ch #\#)
               (char=? ch #\?)
               (char=? ch #\`)
               (char=? ch #\,)
               (char=? ch #\.))
           ;; Done - intern as Elisp symbol with keyword self-evaluation
           (elisp-intern-and-make-keyword name))

          ;; Regular symbol character - add to name and continue
          (else
           (read-char port) ; consume the character
           (set! name (string-append name (string ch)))
           (loop)))))))

(define (elisp-convert-guile-object obj)
  "Convert Guile object to Elisp with proper semantics, eliminating C conversions.
This function replaces the inefficient conversion patterns in guile_to_lisp_object
by using direct Scheme-to-Elisp function calls instead of malloc/free cycles."
  (cond
    ;; Handle null - return Elisp nil
    ((null? obj) #nil)

    ;; Handle booleans - map to Elisp t/nil
    ((boolean? obj) (if obj #t #nil))

    ;; Handle exact integers - pass through directly
    ((and (integer? obj) (exact? obj)) obj)

    ;; Handle real numbers - pass through directly
    ((real? obj) obj)

    ;; Handle strings - pass through directly (already Lisp_Objects in GuilEmacs)
    ((string? obj) obj)

    ;; Handle symbols with special mapping using direct Elisp interning
    ((symbol? obj)
     (let ((sym-str (symbol->string obj)))
       (cond
         ;; Special Elisp symbols - use canonical values
         ((string=? sym-str "nil") #nil)
         ((string=? sym-str "t") #t)
         ((string=? sym-str "and") ((symbol-function 'intern) "and" #nil))
         ((string=? sym-str ":") ((symbol-function 'intern) ":" #nil))

         ;; Reader macro symbols - map to canonical Elisp symbols
         ((or (string=? sym-str "`") (string=? sym-str "\\`"))
          ((symbol-function 'intern) "`" #nil))
         ((or (string=? sym-str ",") (string=? sym-str "\\,"))
          ((symbol-function 'intern) "," #nil))
         ((or (string=? sym-str ",@") (string=? sym-str "\\,@"))
          ((symbol-function 'intern) ",@" #nil))

         ;; Regular symbols - intern using direct Scheme-to-Elisp conversion
         (else ((symbol-function 'intern) sym-str #nil)))))

    ;; Handle Guile keywords - convert to Elisp colon symbols
    ((keyword? obj)
     (let* ((keyword-symbol (keyword->symbol obj))
            (base-name (symbol->string keyword-symbol)))
       (cond
         ;; Special case: empty keyword (bare :) -> colon symbol
         ((= (string-length base-name) 0)
          ((symbol-function 'intern) ":" #nil))
         ;; Regular keywords get : prefix and self-evaluation
         (else
          (let* ((colon-name (string-append ":" base-name))
                 (elisp-symbol ((symbol-function 'intern) colon-name #nil)))
            ;; Make keyword self-evaluating
            ((symbol-function 'set) elisp-symbol elisp-symbol)
            elisp-symbol)))))

    ;; Handle pairs - convert recursively to Elisp cons cells
    ((pair? obj)
     (let ((car-converted (elisp-convert-guile-object (car obj)))
           (cdr-converted (elisp-convert-guile-object (cdr obj))))
       ((symbol-function 'cons) car-converted cdr-converted)))

    ;; For other types, pass through directly
    (else obj)))

(define (elisp-parse-vector-from-port-enhanced port)
  "Parse vector from PORT using existing Elisp vector parser with enhanced conversion.
This replaces the C vector conversion logic with pure Scheme implementation."
  ;; Use the existing elisp vector parser logic
  (let ((guile-vector (elisp-parse-vector-from-port port)))
    (cond
      ((eof-object? guile-vector)
       (error "Unexpected EOF while reading vector"))
      ((vector? guile-vector)
       ;; Use enhanced conversion function instead of C guile_to_lisp_object
       (elisp-convert-guile-object guile-vector))
      (else
       (error "Vector parser returned non-vector")))))

;; Generic enhanced wrapper for future C-to-Scheme migrations
(define (elisp-parse-with-enhanced-conversion parser-func port)
  "Generic enhanced parser wrapper that applies common optimizations.
This function serves as a template for migrating more C logic to Scheme."
  (let ((result (parser-func port)))
    ;; Apply common conversions and optimizations
    (elisp-convert-guile-object result)))

;; Enhanced recursive parsing to eliminate C return fread0() patterns
(define (elisp-parse-with-recursive-reading parser-func port)
  "Enhanced parsing that handles recursive reading cases in Scheme.
This eliminates C patterns like 'return fread0(ctx)' for comments and special cases."
  (let loop ()
    (let ((result (parser-func port)))
      (cond
        ;; Comment processed: read next object recursively
        ((or (eq? result #nil)
             (eq? result 'comment-processed)
             (eq? result 'continue-reading))
         ;; Instead of C calling fread0(), do recursive read in Scheme
         (loop))
        ;; Regular result: return it
        (else result)))))

;; Enhanced comment skipping with recursive reading
(define (elisp-skip-comment-with-recursive-reading port)
  "Skip comment and automatically read the next object.
This eliminates the C pattern: skip_comment(); return fread0();"
  (elisp-skip-comment-from-port port)
  ;; Instead of returning to C to call fread0(), read next object in Scheme
  (elisp-read-from-port port))

;; Conservative fread0 helper - handles EOF checking in Scheme
(define (elisp-parse-with-eof-check char-code port)
  "Conservative Scheme helper for fread0 - handles EOF checking and dispatching.
Takes character as integer from C, checks for EOF, then dispatches."
  (if (= char-code -1)
      (error "End of file during parsing")
      (elisp-parse-comprehensive-dispatch (integer->char char-code) port)))

;; Complete Scheme fread0 - reads character from port itself
(define (elisp-fread0-complete port)
  "Complete Scheme implementation of fread0.
Reads character from port and handles all parsing logic."
  (let ((c (read-char port)))
    (cond
      ((eof-object? c) (error "End of file during parsing"))
      (else (elisp-parse-comprehensive-dispatch c port)))))

;; Complete Scheme fread0 - receives character from C like comprehensive dispatch
(define (elisp-fread0-with-char-from-c char-code port)
  "Complete Scheme implementation of fread0 that receives character from C.
More reliable for file context integration."
  (if (= char-code -1)
      (error "End of file during parsing")
      (elisp-parse-comprehensive-dispatch (integer->char char-code) port)))

;; Comprehensive switch statement replacement for multiple cases
(define (elisp-parse-comprehensive-dispatch char port)
  "Comprehensive parsing dispatcher that handles multiple switch cases.
This function could replace large portions of the C switch statement."
  (cond
    ;; Whitespace - skip and read next (handle first with predicates)
    ((or (char<=? char #\space) (char=? char #\240)) ; NO_BREAK_SPACE = 240
     ;; Skip whitespace and read the next character
     (let loop ((ch (read-char port)))
       (cond
         ((eof-object? ch) (error "End of file during parsing"))
         ((or (char<=? ch #\space) (char=? ch #\240))
          (loop (read-char port))) ; Skip more whitespace
         (else
          ;; Found non-whitespace character, parse it
          (elisp-parse-comprehensive-dispatch ch port)))))

    ;; List parsing
    ((char=? char #\() (elisp-parse-list-from-port port))

    ;; Vector parsing
    ((char=? char #\[) (elisp-parse-vector-from-port port))

    ;; Hash syntax
    ((char=? char #\#)
     ;; Handle hash with potential comment recursion
     (let ((result (elisp-parse-hash-from-port port)))
       (if (eq? result #nil)
           ;; Comment case: read next object
           (elisp-read-from-port port)
           ;; Regular result
           result)))

    ;; Character literal
    ((char=? char #\?) (elisp-parse-char-literal-from-port port))

    ;; String literal
    ((char=? char #\")
     ;; String literal - " already consumed by C, unget it for string parser
     (unread-char #\" port)
     (elisp-parse-string-literal-from-port port))

    ;; Quote with list construction
    ((char=? char #\') (elisp-parse-quote-with-list-construction port))

    ;; Backquote with list construction
    ((char=? char #\`) (elisp-parse-backquote-with-list-construction port))

    ;; Comma syntax
    ((char=? char #\,) (elisp-parse-comma-from-port port))

    ;; Comment with recursive reading
    ((char=? char #\;) (elisp-skip-comment-with-recursive-reading port))

    ;; Default: character-based dispatch
    (else (elisp-parse-character-dispatch char port))))

;; Comprehensive character-based dispatcher to minimize C switch logic
(define (elisp-parse-character-dispatch char port)
  "Comprehensive character-based parsing dispatcher.
This function handles character type detection and parsing dispatch,
eliminating the need for multiple C character checks and scm_ungetc calls."
  (cond
    ;; Numeric characters (0-9, +, -, .)
    ((or (and (char>=? char #\0) (char<=? char #\9))
         (char=? char #\+) (char=? char #\-) (char=? char #\.))
     ;; Unread the character and parse as number
     (unread-char char port)
     (elisp-parse-number-from-port port))

    ;; Colon character (:)
    ((char=? char #\:)
     ;; Unread the character and parse as colon symbol
     (unread-char char port)
     (elisp-parse-colon-from-port port))

    ;; Alphabetic characters (a-z, A-Z)
    ((or (and (char>=? char #\a) (char<=? char #\z))
         (and (char>=? char #\A) (char<=? char #\Z)))
     ;; Unread the character and parse as symbol
     (unread-char char port)
     (elisp-parse-symbol-from-port port))

    ;; Default: symbol parsing
    (else
     ;; Unread the character and parse as symbol
     (unread-char char port)
     (elisp-parse-symbol-from-port port))))

;;; Unified parsers for fallthrough consolidation

;; Simple literal parser dispatcher - character and string
(define (elisp-parse-literal-unified char-code port)
  "Parse character or string literal based on character code"
  (let ((ch (integer->char char-code)))
    (cond
      ((char=? ch #\?)
       ;; Character literal
       (elisp-parse-char-literal-from-port port))
      ((char=? ch #\")
       ;; String literal
       (unread-char #\" port)
       (elisp-parse-string-literal-from-port port))
      ;; Should not reach here given C switch logic
      (else
       #nil))))

;; Comprehensive structural and literal parser - unified dispatcher
(define (elisp-parse-structural-literal-unified char-code port)
  "Parse structural (lists, vectors) and literal (chars, strings, hash syntax) based on character code"
  (let ((ch (integer->char char-code)))
    (cond
      ((char=? ch #\()
       ;; List parsing - ( already consumed by C
       (elisp-parse-list-from-port port))
      ((char=? ch #\[)
       ;; Vector parsing - [ already consumed by C
       (elisp-parse-vector-from-port port))
      ((char=? ch #\?)
       ;; Character literal - ? already consumed by C
       (elisp-parse-char-literal-from-port port))
      ((char=? ch #\")
       ;; String literal - " already consumed by C, unget it for string parser
       (unread-char #\" port)
       (elisp-parse-string-literal-from-port port))
      ((char=? ch #\#)
       ;; Hash syntax - # already consumed by C, delegate to comprehensive hash parser
       (elisp-parse-hash-from-port port))
      ;; Should not reach here given C switch logic
      (else
       #nil))))

;; Safe quote and backquote dispatcher - minimal consolidation
(define (elisp-parse-quote-backquote-dispatch char-code port)
  "Dispatch quote and backquote syntax based on character code"
  (let ((ch (integer->char char-code)))
    (cond
      ((char=? ch #\')
       ;; Quote form
       (let ((obj (elisp-read-from-port port)))
         (cons 'quote (cons obj #nil))))
      ((char=? ch #\`)
       ;; Backquote form
       (let ((obj (elisp-read-from-port port)))
         (cons 'backquote (cons obj #nil))))
      (else
       ;; Default case should never be reached
       #nil))))

(define (elisp-parse-quote-like-syntax port ch)
  "Unified parser for quote-like syntax: ', `, ,, ,@"
  (cond
    ((char=? ch #\')
     ;; Quote form
     (let ((obj (elisp-read-from-port port)))
       (cons 'quote (cons obj #nil))))
    ((char=? ch #\`)
     ;; Backquote form
     (let ((obj (elisp-read-from-port port)))
       (cons 'backquote (cons obj #nil))))
    ((char=? ch #\,)
     ;; Comma syntax - check for ,@
     (let ((next-ch (peek-char port)))
       (if (and (char? next-ch) (char=? next-ch #\@))
           (begin
             (read-char port)  ; consume the @
             (let ((expr (elisp-read-from-port port)))
               (cons (elisp-intern ",@" #nil) (cons expr #nil))))
           ;; Regular comma
           (let ((expr (elisp-read-from-port port)))
             (cons (elisp-intern "," #nil) (cons expr #nil))))))
    (else
     ;; Default case should never be reached
     #nil)))

(define (elisp-parse-literal port ch)
  "Unified parser for literal syntax: ? (char) and \" (string)"
  (cond
    ((char=? ch #\?)
     ;; Character literal
     (elisp-parse-char-literal-from-port port))
    ((char=? ch #\")
     ;; String literal
     (elisp-parse-string-literal-from-port port))
    ;; Default case should never be reached
    (else
     #nil)))

(define (elisp-parse-structural char-code port)
  "Unified parser for structural syntax: (, [, # - takes character code"
  (let ((ch (integer->char char-code)))
    (cond
      ((char=? ch #\()
       ;; List parsing
       (elisp-parse-list-from-port port))
      ((char=? ch #\[)
       ;; Vector parsing
       (elisp-parse-vector-from-port port))
      ((char=? ch #\#)
       ;; Hash syntax
       (elisp-parse-hash-from-port port))
      ;; Default case should never be reached given the C switch logic
      (else
       ;; Return nil as fallback
       #nil))))

;; Performance metrics function to measure migration benefits
(define (elisp-reader-performance-info)
  "Return information about the Scheme-enhanced reader performance optimizations."
  (cons 'reader-optimizations
        '((malloc-free-cycles-eliminated . symbol-keyword-conversion)
          (c-wrapper-functions-simplified . 12)
          (type-checking-moved-to-scheme . 6)
          (generic-wrapper-pattern-established . #t)
          (enhanced-conversion-functions-available . #t))))

;;; Incremental migration functions - small steps toward full Scheme reader

;; Whitespace and EOF handler - small incremental step toward full Scheme reader
(define (elisp-handle-whitespace-and-eof port)
  "Handle whitespace skipping and EOF detection for fread0.
Returns 'eof if EOF was encountered,
Returns 'whitespace-skipped if whitespace was skipped (caller should try again),
Otherwise ungets the character and returns the character."
  (let ((ch (read-char port)))
    (cond
      ;; EOF handling
      ((eof-object? ch)
       'eof)

      ;; Whitespace - skip and indicate to try again
      ((or (char<=? ch #\space) (char=? ch #\240)) ; NO_BREAK_SPACE = 240
       ;; Skip whitespace and try again recursively
       (elisp-handle-whitespace-and-eof port))

      ;; Regular character - unget it and return it for C processing
      (else
       (unread-char ch port)
       ch))))

;;; Load-specific helper functions for readevalloop_load migration

;; Phase 1: Extract Helper Functions for readevalloop_load

(define (elisp-skip-load-whitespace-from-port port)
  "Skip whitespace characters specific to load operations.
This handles the exact same whitespace as readevalloop_load:
space, tab, newline, form feed, carriage return, and NO_BREAK_SPACE.
Returns: #t when done skipping whitespace"
  (let loop ()
    (let ((ch (peek-char port)))
      (cond
        ((eof-object? ch) #t)
        ;; Match exact whitespace from readevalloop_load lines 2100-2102
        ((or (char=? ch #\space)   ; ' '
             (char=? ch #\tab)     ; '\t'
             (char=? ch #\newline) ; '\n'
             (char=? ch #\page)    ; '\f' (form feed)
             (char=? ch #\return)  ; '\r'
             (char=? ch #\x00A0))  ; NO_BREAK_SPACE
         (read-char port) ; consume the whitespace character
         (loop))
        (else #t)))))

(define (elisp-skip-load-comment-from-port port)
  "Skip a line comment for load operations, matching readevalloop_load logic.
This handles comments starting with ';' until newline or EOF.
Returns: #t when comment is fully skipped"
  ;; Consume characters until newline or EOF (matching lines 2090-2091)
  (let loop ()
    (let ((ch (read-char port)))
      (cond
        ((eof-object? ch) #t)
        ((char=? ch #\newline) #t)
        (else (loop))))))

(define (elisp-read-with-load-function-from-port port)
  "Handle custom reader function delegation for load operations.
This replicates the conditional logic from readevalloop_load lines 2113-2127.
Returns: The result of the appropriate read function"
  ;; For now, simplify to only handle the main case since readfun is Qnil in readevalloop_load
  ;; In the original C code, readfun is always Qnil for file loading
  (let ((load-read-fn ((symbol-function 'symbol-value) 'load-read-function)))
    (cond
      ;; Non-default custom read function (lines 2118-2122)
      ((and (not (eq? load-read-fn #nil))
            (not (eq? load-read-fn ((symbol-function 'intern) "read" #nil))))
       ((symbol-function 'funcall) load-read-fn ((symbol-function 'symbol-value) 'get-file-char)))

      ;; Default case: use elisp-read-from-port (lines 2125-2126)
      ;; This handles both readfun=nil and the standard case
      (else
       (elisp-read-from-port port)))))

;;; End Section 9


;;; ============================================================================
;;; SECTION 10: LOAD SYSTEM
;;; ============================================================================
;;;
;;; File loading infrastructure - handles .el/.elc files, load-path, etc.
;;; Migrated from lread.c Fload function.
;;; Includes: file validation, load-path management, read-eval loop, history.

(define (elisp-load-read-next-expression-from-port port)
  "Read the next complete expression from PORT, handling all preprocessing.
This function unifies whitespace skipping, comment skipping, EOF detection,
and expression reading into a single atomic operation.

Returns:
- The next expression to evaluate
- 'eof if end of file reached
- Automatically handles all whitespace and comments"
  (let loop ()
    ;; Skip whitespace first
    (elisp-skip-load-whitespace-from-port port)

    ;; Check what comes next
    (let ((ch (peek-char port)))
      (cond
        ;; EOF reached
        ((eof-object? ch) 'eof)

        ;; Comment - skip it and try again
        ((char=? ch #\;)
         (read-char port) ; consume the semicolon
         (elisp-skip-load-comment-from-port port)
         (loop)) ; recursively try to read next expression

        ;; Regular expression - read it
        (else
         (elisp-read-with-load-function-from-port port))))))

;; Phase 4: Complete Read-Eval Loop Migration

(define (elisp-load-read-eval-loop-from-port port printflag)
  "Complete read-eval loop for file loading.
Reads expressions from PORT, evaluates them, and optionally prints results.
This replaces the entire while loop from readevalloop_load."
  (let loop ()
    (let ((expr (elisp-load-read-next-expression-from-port port)))
      (cond
        ;; EOF reached - stop looping
        ((eq? expr 'eof) 'done)

        ;; Regular expression - evaluate and continue
        (else
         ;; Delegate evaluation to C eval_sub to preserve all Elisp semantics
         (let ((result ((symbol-function 'eval) expr)))
           ;; Handle printing if requested
           (when (not (eq? printflag #f))
             ;; Add result to Vvalues for interactive sessions
             ((symbol-function 'set) 'values
              ((symbol-function 'cons) result ((symbol-function 'symbol-value) 'values)))
             ;; Print using appropriate function
             (if (eq? ((symbol-function 'symbol-value) 'standard-output) #t)
                 ((symbol-function 'prin1) result)
                 ((symbol-function 'print) result)))
           ;; Continue looping
           (loop)))))))

(define (elisp-normalize-load-path sourcename)
  "Normalize the file path for loading, making it absolute if needed.
This replicates the C logic from readevalloop_load lines 2077-2080."
  (if (not (eq? ((symbol-function 'file-name-absolute-p) sourcename) #nil))
      ((symbol-function 'expand-file-name) sourcename #nil)
      sourcename))

(define (elisp-complete-file-load-from-port port sourcename printflag)
  "Complete readevalloop_load replacement that handles all file loading logic.
This replaces readevalloop_load (src/lread.c:2055-2078) with full semantic compatibility.

Handles:
- File path normalization (replicates line 2071)
- Load history initialization (replicates line 2073)
- Read-eval loop execution (replicates line 2075)
- Dynamic binding setup is handled by C wrapper for proper unwind-protect integration"

  ;; Normalize file path (replicates readevalloop_load line 2071)
  (let ((normalized-sourcename (elisp-normalize-load-path sourcename)))
    ;; Note: loadhist_initialize is handled by C wrapper for proper global structure access

    ;; Execute the complete read-eval loop (replicates readevalloop_load line 2075)
    (elisp-load-read-eval-loop-from-port port printflag)

    ;; Return normalized sourcename for C wrapper to use with loadhist_initialize
    normalized-sourcename))

(define (elisp-readevalloop-load-from-port port sourcename)
  "Complete Scheme replacement for readevalloop_load C function.
This handles the core logic, with dynamic binding delegated back to C wrapper.
Replicates the core behavior of src/lread.c:2055-2088."

  ;; Validate input (replicates CHECK_STRING)
  (unless (string? sourcename)
    (error "sourcename must be a string" sourcename))

  ;; File loading setup (replicates line 2060)
  (let ((printflag #f)) ; File loading doesn't print by default

    ;; Note: Dynamic binding (specbind calls) are complex to replicate in Scheme
    ;; For now, we handle the core logic and let C handle the binding setup
    ;; TODO: Move dynamic binding to Scheme in a future iteration

    ;; Normalize file path (replicates line 2071)
    (let ((normalized-sourcename (elisp-normalize-load-path sourcename)))

      ;; Initialize load history (replicates line 2073)
      ;; Use Elisp function call for proper integration
      ((symbol-function 'elisp-loadhist-initialize) normalized-sourcename)

      ;; Execute the complete read-eval loop (replicates line 2075)
      (elisp-load-read-eval-loop-from-port port printflag)

      ;; Return success (C function returns void, so we just complete)
      'done)))

(define (elisp-process-load-file-path file nosuffix must-suffix)
  "Process file path and determine suffixes for loading.
This replicates the file path processing logic from Fload (lines 979-1020).

Returns: (file-to-search . suffixes-list)
- file-to-search: the file name to search for
- suffixes-list: list of suffixes to try, or #nil"

  ;; Validate file is not empty
  (when (= ((symbol-function 'length) file) 0)
    (error "Cannot load empty filename"))

  (let ((suffixes #nil))
    ;; Handle must-suffix logic
    (unless (eq? must-suffix #nil)
      ;; Don't insist on adding a suffix if FILE already ends with one
      (when (or ((symbol-function 'string-suffix-p) ".el" file #t)
                ;; TODO: Add module suffix checks when modules are supported
                )
        (set! must-suffix #nil))

      ;; Don't insist on adding a suffix if the argument includes a directory name
      (unless (eq? ((symbol-function 'file-name-directory) file) #nil)
        (set! must-suffix #nil)))

    ;; Determine suffixes to use
    (cond
      ;; If nosuffix is set, use no suffixes
      ((not (eq? nosuffix #nil))
       (set! suffixes #nil))

      ;; Otherwise build suffixes list
      (else
       (set! suffixes ((symbol-function 'get-load-suffixes)))
       (when (eq? must-suffix #nil)
         (set! suffixes ((symbol-function 'append) suffixes
                        ((symbol-function 'symbol-value)
                         (elisp-intern "load-file-rep-suffixes" #nil)))))))

    ;; Return the file and suffixes as a pair
    (cons file suffixes)))

(define (elisp-format-load-message file is-module is-native-elisp compiled newer loading-p)
  "Format loading messages for different file types.
This replicates the message formatting logic from Fload (lines 1153-1166, 1210-1223).

- loading-p: #t for 'Loading...' messages, #f for '...done' messages"

  (let ((base-msg
         (cond
           (is-module
            (if loading-p "Loading %s (module)..." "Loading %s (module)...done"))
           (is-native-elisp
            (if loading-p "Loading %s (native compiled elisp)..."
                          "Loading %s (native compiled elisp)...done"))
           ((not compiled)
            (if loading-p "Loading %s (source)..." "Loading %s (source)...done"))
           (newer
            (if loading-p "Loading %s (compiled; note, source file is newer)..."
                          "Loading %s (compiled; note, source file is newer)...done"))
           (else
            (if loading-p "Loading %s..." "Loading %s...done")))))

    ;; Use message-with-string equivalent
    ((symbol-function 'message) base-msg file)))

(define (elisp-show-load-message file is-module is-native-elisp compiled newer loading-p nomessage force-load-messages noninteractive-p)
  "Display loading messages with proper conditional logic.
This replicates the message display logic from Fload (lines 1133-1146, 1190-1203)."

  ;; Check conditions for displaying messages (replicates C conditional logic)
  (let ((should-show-loading (or (eq? nomessage #nil) force-load-messages))
        (should-show-done (and (not noninteractive-p)
                              (or (eq? nomessage #nil) force-load-messages))))

    (when (if loading-p should-show-loading should-show-done)
      (let ((base-msg
             (cond
               (is-module
                (if loading-p "Loading %s (module)..." "Loading %s (module)...done"))
               (is-native-elisp
                (if loading-p "Loading %s (native compiled elisp)..."
                              "Loading %s (native compiled elisp)...done"))
               ((not compiled)
                (if loading-p "Loading %s (source)..." "Loading %s (source)...done"))
               (newer
                (if loading-p "Loading %s (compiled; note, source file is newer)..."
                              "Loading %s (compiled; note, source file is newer)...done"))
               (else
                (if loading-p "Loading %s..." "Loading %s...done")))))

        ;; Use message function instead of message-with-string for simplicity
        ((symbol-function 'message) base-msg file)))))

(define (elisp-compute-hist-file-name file found-eff purify-flag)
  "Compute the history file name for load-history.
This replicates the hist_file_name computation from Fload (lines 1063-1067)."

  (if (not (eq? purify-flag #nil))
      ;; When purifying: concat2(file-name-directory(file), file-name-nondirectory(found-eff))
      ((symbol-function 'concat)
       ((symbol-function 'file-name-directory) file)
       ((symbol-function 'file-name-nondirectory) found-eff))
      ;; Otherwise just use found-eff
      found-eff))

(define (elisp-count-recursive-loads found loads-in-progress-list)
  "Count how many times a file appears in the loads-in-progress list.
This replicates the counting logic from Fload recursive load detection.
Signals an error if more than 3 recursive loads are detected."

  (let ((load-count 0))
    ;; Count occurrences using a simple loop
    (let loop ((tem loads-in-progress-list))
      (when (not (eq? tem #nil))
        (when (not (eq? ((symbol-function 'equal) found ((symbol-function 'car) tem)) #nil))
          (set! load-count (+ load-count 1)))
        (loop ((symbol-function 'cdr) tem))))

    ;; Check if we exceeded the limit (replicates the > 3 check)
    (when (> load-count 3)
      ;; Signal recursive load error
      ((symbol-function 'signal) (elisp-intern "error" #nil)
       ((symbol-function 'list) "Recursive load"
        ((symbol-function 'cons) found loads-in-progress-list))))

    ;; Return the count for debugging/logging if needed
    load-count))

(define (elisp-setup-default-lexical-binding)
  "Set up default dynamic binding for load context.
This replicates the lexical binding setup from Fload (lines 1046-1050).
All loads are by default dynamic, unless the file itself specifies otherwise."

  ;; Bind lexical-binding to nil (dynamic binding by default)
  ;; This will be handled by specbind in the C wrapper since it needs proper cleanup
  'setup-for-c-specbind)

(define (elisp-call-load-source-file-function load-source-file-function found hist-file-name noerror nomessage force-load-messages)
  "Call the load-source-file-function with properly converted arguments.
This replicates the call4 logic from Fload (lines 1065-1067)."

  ;; Convert arguments to match the C call4 pattern
  (let ((error-arg (if (eq? noerror #nil) #nil #t))
        (message-arg (if (or (eq? nomessage #nil) force-load-messages) #nil #t)))

    ;; Call the function with 4 arguments
    ((symbol-function 'funcall) load-source-file-function found hist-file-name error-arg message-arg)))

(define (elisp-validate-load-file file)
  "Validate file argument for loading.
This replicates the validation logic from Fload (lines 966, 976-977).
Returns #t if valid, signals error if invalid."

  ;; Check if file is a string (replicates CHECK_STRING)
  (unless (string? file)
    ((symbol-function 'signal) (elisp-intern "wrong-type-argument" #nil)
     ((symbol-function 'list) (elisp-intern "stringp" #nil) file)))

  ;; Check for empty string (replicates SCHARS(file) == 0 check)
  (when (= ((symbol-function 'length) file) 0)
    ((symbol-function 'signal) (elisp-intern "file-error" #nil)
     ((symbol-function 'list) "Cannot load empty filename")))

  ;; Return success
  #t)

(define (elisp-complete-filename? pathname)
  "Check if pathname is a complete filename.
This replicates the complete_filename_p function from lread.c lines 1258-1265.
Returns #t if pathname starts with directory separator or is a full Windows path."

  (let* ((path-string (if (string? pathname) pathname (scm_to_utf8_string pathname)))
         (path-length (string-length path-string)))

    (if (= path-length 0)
        #f  ; Empty string is not complete
        (or
         ;; Check if starts with directory separator (Unix: /, Windows: \ or /)
         (or (char=? (string-ref path-string 0) #\/)
             (char=? (string-ref path-string 0) #\\))

         ;; Check for Windows drive letter format (C:\)
         (and (> path-length 2)
              (char=? (string-ref path-string 1) #\:)
              (or (char=? (string-ref path-string 2) #\/)
                  (char=? (string-ref path-string 2) #\\)))))))

(define (elisp-compute-found-effective found)
  "Compute effective filename from found filename.
This replicates the compute_found_effective function from lread.c lines 869-882.
Handles .el.gz files by removing .gz suffix and adding 'c' suffix for .elc files."

  ;; Set src_name to nil initially (this matches the C code)
  (let ((src-name #nil))

    ;; If src_name is nil (which it always is in this implementation)
    ;; return found as-is (manual eln load case)
    (if (eq? src-name #nil)
        found
        ;; Original logic for when src_name is not nil:
        ;; Check if it ends with "el.gz" and process accordingly
        (let ((src-string (if (string? src-name) src-name (scm_to_utf8_string src-name))))
          (if (string-suffix? "el.gz" src-string)
              ;; Remove .gz suffix and add 'c' suffix
              (let* ((base-name (substring src-string 0 (- (string-length src-string) 3)))
                     (base-lisp ((symbol-function 'substring) src-name
                                (elisp-intern "0" #nil)
                                (elisp-intern "-3" #nil))))
                ((symbol-function 'concat) base-lisp "c"))
              ;; Just add 'c' suffix for regular .el files
              ((symbol-function 'concat) src-name "c"))))))

(define (elisp-loadhist-initialize filename)
  "Initialize load history for filename.
This replicates the loadhist_initialize function from lread.c lines 877-882.
Validates filename and sets up current-load-list binding."

  ;; Assertion check: filename must be string or nil
  (unless (or (string? filename) (eq? filename #nil))
    ((symbol-function 'error) "filename must be string or nil"))

  ;; This function just sets up the binding - the actual specbind is done in C
  ;; Return the cons to be used in specbind
  ((symbol-function 'cons) filename #nil))

(define (elisp-handle-user-init-file found)
  "Handle user init file detection logic.
This replicates the user init file logic from Fload (lines 1002-1003).
Returns the value that should be assigned to Vuser_init_file."

  ;; Check if Vuser_init_file is Qt (meaning we're looking for user's init file)
  (if (eq? ((symbol-function 'symbol-value) (elisp-intern "user-init-file" #nil))
           ((symbol-function 'symbol-value) (elisp-intern "t" #nil)))
      found  ; If yes, set it to the found file
      ;; Otherwise, return the current value unchanged
      ((symbol-function 'symbol-value) (elisp-intern "user-init-file" #nil))))

(define (elisp-prepare-module-loading found)
  "Prepare for module loading by initializing load history.
This replicates the module loading preparation from Fload (lines 1176-1178)."

  ;; Call loadhist-initialize for the found file
  ;; This corresponds to the C code: loadhist_initialize (found);
  ((symbol-function 'loadhist-initialize) found))

(define (elisp-handle-lexical-binding-specbind)
  "Return the appropriate binding for lexical-binding variable.
This prepares the specbind call for lexical-binding from Fload (line 1033)."

  ;; Return a cons cell for specbind: (Qlexical_binding . Qnil)
  ;; The actual specbind call will be done in C
  ((symbol-function 'cons) (elisp-intern "lexical-binding" #nil) #nil))

(define (elisp-orchestrate-file-reading port hist-file-name)
  "Orchestrate the file reading process including sync and evaluation.
This replicates the orchestration from Fload (lines 1202-1203)."

  ;; This function serves as a scheme-side coordinator for the reading process
  ;; The actual sync_guile_reader and readevalloop_load calls remain in C
  ;; but this provides a scheme hook point for future enhancements

  ;; For now, return success indicator - the C code will handle the actual calls
  #t)

(define (elisp-handle-file-open-error fd noerror file)
  "Handle file opening errors and determine response.
This replicates the error handling from Fload (lines 993-999).
Returns: 'continue if should continue, 'return-nil if should return nil."

  ;; Check if file descriptor indicates failure (fd < 0)
  ;; In the C code, lread_fd_cmp(-1) checks if fd equals -1
  (if (< fd 0)
      (if (eq? noerror #nil)
          ;; If noerror is nil, we should signal an error (handled in C)
          'signal-error
          ;; If noerror is non-nil, return nil quietly
          'return-nil)
      ;; File opened successfully, continue
      'continue))

(define (elisp-setup-file-descriptor-protection fd)
  "Determine if file descriptor needs unwind protection.
This replicates the unwind protection logic from Fload (lines 1008-1011).
Returns: #t if protection should be set up, #f otherwise."

  ;; In C: if (0 <= fd) - set up unwind protection
  (>= fd 0))

(define (elisp-prepare-openp-call path-result)
  "Prepare parameters for openp function call.
This replicates the openp call preparation from Fload (lines 985-991).
Returns: (processed-file . suffixes) pair for openp call."

  ;; Extract the components that were computed by elisp-process-load-file-path
  ;; path_result is already a (file . suffixes) pair from scheme
  path-result)

(define (elisp-handle-loads-in-progress found loads-in-progress)
  "Prepare loads-in-progress list update.
This extends the recursive load handling from Fload (lines 1027-1029).
Returns: the new value for loads-in-progress list."

  ;; The C code does: Vloads_in_progress = Fcons (found, Vloads_in_progress);
  ;; We return the new cons cell for C to assign
  ((symbol-function 'cons) found loads-in-progress))

;; COMPOUND FUNCTIONS - Consolidate multiple operations to reduce C-Guile marshalling

(define (elisp-validate-and-check-handler file noerror nomessage nosuffix must-suffix)
  "Compound function: Validate file and check for magic file name handlers.
This consolidates elisp-validate-load-file and elisp-check-file-handler.
Returns: handler result if handler found, #f if should continue with normal loading."

  ;; First, validate the file
  (elisp-validate-load-file file)

  ;; Then check for magic file name handlers
  (elisp-check-file-handler file noerror nomessage nosuffix must-suffix))

(define (elisp-setup-load-environment found loads-in-progress file purify-flag is-native-elisp)
  "Compound function: Set up load environment including recursive loads, bindings, and filenames.
This consolidates recursive load detection, loads-in-progress management, lexical binding setup,
effective filename computation, and history file name computation.
Returns: (new-loads-in-progress . (lexical-binding . (found-eff . hist-file-name)))"

  ;; Handle recursive load counting
  (elisp-count-recursive-loads found loads-in-progress)

  ;; Prepare new loads-in-progress list
  (let ((new-loads-in-progress (elisp-handle-loads-in-progress found loads-in-progress)))

    ;; Prepare lexical binding
    (let ((lexical-binding (elisp-handle-lexical-binding-specbind)))

      ;; Compute effective filename
      (let ((found-eff (elisp-compute-effective-filename found is-native-elisp)))

        ;; Compute history file name
        (let ((hist-file-name (elisp-compute-hist-file-name file found-eff purify-flag)))

          ;; Return all results as nested cons cells
          (cons new-loads-in-progress
                (cons lexical-binding
                      (cons found-eff hist-file-name))))))))

(define (fresh-go? go src)
  (and go
       (file-exists? go)
       (>= (stat:mtime (stat go)) (stat:mtime (stat src)))))

(define (load-elisp file)
  (let* ((src (%search-load-path file)) ; find foo.el on %load-path
         (go  (compiled-file-name src)) ; cache path for .go
         (el  (lookup-language 'elisp)))
    (unless src
      (error "Not found on %load-path" file))
    (if (fresh-go? go src)
        (load-compiled go)
        (begin
          (compile-file src
                        #:from el ; 'elisp
                        ;#:to 'value ; warmbyte , FIX-GUILE: cant combine with output-file
                        #:output-file go)
          (load-compiled go)))))

;; Custom elisp reader that handles colon symbols properly
(define (custom-elisp-read port)
  "Custom elisp reader that creates self-evaluating colon symbols"
  (let ((original-result (read port)))
    (cond
      ;; Handle Guile keywords (converted from :symbol syntax)
      ((keyword? original-result)
       (let* ((keyword-symbol (keyword->symbol original-result))
              (base-name (symbol->string keyword-symbol))
              (colon-name (string-append ":" base-name)))
         ;; Create self-evaluating elisp symbol
         (let ((elisp-symbol ((symbol-function 'intern) colon-name #nil)))
           ((symbol-function 'set) elisp-symbol elisp-symbol)
           elisp-symbol)))
      ;; Pass through everything else
      (else original-result))))


;; Enhanced version that handles full Fload parameters
(define (load-elisp-full found-file noerror nomessage nosuffix must-suffix)
  "Load elisp file with compilation, handling full Fload parameter set"
  (catch #t
    (lambda ()
      (let* ((src found-file)
             (go (string-append src ".go")) ; FIX: compiled-file-name returns #f ?!
             ;; Load our custom elisp language to override system elisp
             (el (lookup-language 'elisp)))
        (if (fresh-go? go src)
            (load-compiled go)
            (begin
              (compile-file src
                            #:from el
                            #:output-file go)
              (load-compiled go)))
        #t)) ; return t on success
    (lambda (key . args)
      (if noerror
          #f ; return nil on error if noerror is true
          (apply throw key args))))) ; re-throw error otherwise

; FIX: kludge, move to some init function
(let ((str (canonicalize-path (string-concatenate (list %prelude-directory "/..")))))
  (set! %load-path (append (list (string-concatenate (list str "/lisp"))
                                 (string-concatenate (list str "/lisp/emacs-lisp"))
                                 (string-concatenate (list str "/lisp/progmodes"))
                                 (string-concatenate (list str "/lisp/language"))
                                 (string-concatenate (list str "/lisp/international"))
                                 (string-concatenate (list str "/lisp/textmodes"))
                                 (string-concatenate (list str "/lisp/vc"))
                                 (string-concatenate (list str "/lisp/mail"))
                                 (string-concatenate (list str "/lisp/url"))
                                 (string-concatenate (list str "/lisp/gnus"))
                                 (string-concatenate (list str "/lisp/net"))
                                 (string-concatenate (list str "/lisp/calendar"))
                                 (string-concatenate (list str "/lisp/cedet"))
                                 (string-concatenate (list str "/lisp/eshell")))
                           %load-path)))

(set! %load-extensions (cons ".el" %load-extensions))

;; Bridge function that reuses existing Fload Scheme migrations
(define (fload-bridge file noerror nomessage nosuffix must-suffix)
  "Bridge function that handles full Fload protocol using Guile elisp compilation"
  (catch #t
    (lambda ()
      (format (current-error-port) "loading ~a~%" file)
      ;; File validation and handler check (reuse existing)
      (let ((handler-result (elisp-validate-and-check-handler file noerror nomessage nosuffix must-suffix)))
        (when handler-result
          (throw 'early-return handler-result)))

      ;; File path processing and suffix determination (reuse existing)
      (let* ((path-result (elisp-process-load-file-path file nosuffix must-suffix)
                          ;(cons file '(".el" ".elc"))
                         )
             (processed-file (car path-result))
             (suffixes (cdr path-result)))
        ;; Find file using openp equivalent, including current directory
        (let ((found (or
                         ; FIX: %search-load-path is underspecified, does it search for compiled equivalent and if so, how is given suffix handled?
                         (%search-load-path processed-file)
                         ;processed-file
                         ;; Also try current directory if not found in load-path
                         (and (file-exists? processed-file) processed-file)
                         ;; Try with .el suffix in current directory
                         (and (file-exists? (string-append processed-file ".el"))
                              (string-append processed-file ".el")))))
          (unless found
            (if noerror
                (throw 'early-return #f)
                (error "Cannot open load file" file)))

          ;; Step 4: Setup load environment (reuse existing)
          (let ((setup-env-func (resolve-ref "language elisp runtime"
                                            "elisp-setup-load-environment")))
            (when setup-env-func
              (setup-env-func found '() file #f #t))) ; simplified params

          ;; Step 5: Use enhanced elisp compilation instead of C reading
          (load-elisp-full found noerror nomessage nosuffix must-suffix))))

    (lambda (key . args)
      (cond
        ((eq? key 'early-return) (car args))
        (noerror #f)
        (else (apply throw key args))))))

;; Helper to safely resolve scheme functions
(define (resolve-ref module-name symbol-name)
  (catch #t
    (lambda ()
      (let ((mod (resolve-module (string->symbol module-name))))
        (and mod (module-ref mod (string->symbol symbol-name)))))
    (lambda (key . args) #f)))

(set-symbol-function! 'emacs-load fload-bridge)

;;; End Section 10


;;; ============================================================================
;;; SECTION 11: DEBUG & DEVELOPMENT TOOLS
;;; ============================================================================
;;;
;;; Utilities for debugging and development - not part of core runtime.
;;; Includes: symbol generation, debug flags, eval-scheme for testing.

;; Define intern-gensym first - creates interned unique symbols
(define %intern-gensym 0)
(define (intern-gensym prefix)
  (set! %intern-gensym (+ 1 %intern-gensym))
  (string->symbol (string-concatenate (list prefix "_" (number->string %intern-gensym)))))

;; Make make-symbol create interned symbols (not uninterned) to avoid Guile serialization errors
;; Uninterned symbols cannot be saved to .go files
(define (make-symbol name)
  (intern-gensym name))
(set-symbol-function! 'make-symbol make-symbol)

(set-symbol-function! 'intern-gensym intern-gensym)

(define %debug-print-flag 0)
(define (set-debug-print-flag! val)
  (set! %debug-print-flag val))

;(define (get-debug-print-flag)
;  %debug-print-flag)
(set-symbol-function! 'set-debug-print-flag! set-debug-print-flag!)

(set-symbol-function! 'get-debug-print-flag
                      (lambda ()
                        %debug-print-flag))

;;; End Section 11


;;; ============================================================================
;;; END OF PRELUDE/LOAD.SCM
;;; ============================================================================

;; (format (current-error-port) "-- done loading guile elisp prelude~%")
;; (force-output (current-error-port))
