;;; Guilemacs Lisp
;;;
;;; Utility Functions
;;;
;;; Miscellaneous utility functions migrated from C to Guile.
;;; Includes: symbol properties, obarray operations, hash tables,
;;; features/provide, list utilities, predicates, file utilities,
;;; math utilities, I/O functions, and buffer operations.

;;;
;;; Load System Utilities
;;;

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

;;;
;;; Obarray Operations
;;;

(define (elisp-obarrayp object)
  "Return t if OBJECT is an obarray."
  (if (vector? object) #t #nil))

(define (elisp-obarray-make size)
  "Return a new obarray of size SIZE.
The obarray will grow to accommodate any number of symbols; the size, if
given, is only a hint for the expected number."
  (make-vector (if (and size (integer? size) (> size 0)) size 128) '()))

(define (elisp-obarray-clear obarray)
  "Remove all symbols from OBARRAY."
  (if (vector? obarray)
      (let ((len (vector-length obarray)))
        (do ((i 0 (+ i 1)))
            ((>= i len) obarray)
          (vector-set! obarray i '())))
      (error "Wrong type argument: obarrayp" obarray)))

(define (elisp-intern string obarray)
  "Return the canonical symbol whose name is STRING.
If there is none, one is created by this function and returned.
A second optional argument specifies the obarray to use;
it defaults to the value of `obarray'."
  (let ((str (if (symbol? string) (symbol->string string) string)))
    (if (not (string? str))
        ((symbol-function 'signal) 'wrong-type-argument (cons 'stringp str))
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
        #nil)))

;;;
;;; Symbol Property Functions
;;;

(define (elisp-symbol-plist symbol)
  "Return SYMBOL's property list."
  (if (symbol? symbol)
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

;;;
;;; Hash Table Operations
;;;

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

;;;
;;; Feature/Provide System
;;;

(define (elisp-featurep feature subfeature)
  "Return t if FEATURE is present in this Emacs.
Use this to conditionalize execution of lisp code based on the
presence or absence of Emacs or environment extensions."
  (if (memq feature features)
      (if subfeature
          #t  ; Simplified: assume subfeatures are present if feature is
          #t)
      #nil))

(define (elisp-provide feature subfeatures)
  "Announce that FEATURE is a feature of the current Emacs.
The optional argument SUBFEATURES should be a list of symbols listing
particular subfeatures supported in this version of FEATURE."
  (if (not (memq feature features))
      (set! features (cons feature features)))
  feature)

;;;
;;; List Utilities
;;;

(define (elisp-nreverse seq)
  "Reverse order of items in a list, vector or string SEQ.
This function may destructively modify SEQ to produce the value."
  (cond
    ((null? seq) seq)
    ((pair? seq) (reverse! seq))
    ((vector? seq)
     (let ((len (vector-length seq)))
       (do ((i 0 (+ i 1)))
           ((>= i (quotient len 2)) seq)
         (let ((j (- len i 1)))
           (let ((temp (vector-ref seq i)))
             (vector-set! seq i (vector-ref seq j))
             (vector-set! seq j temp))))))
    ((string? seq)
     (list->string (reverse! (string->list seq))))
    (else seq)))

(define (elisp-delq elt list)
  "Delete members of LIST which are `eq' to ELT, and return the result.
More precisely, this function skips any members `eq' to ELT at the
front of LIST, then removes members `eq' to ELT from the remaining
sublist by modifying its list structure, then returns the resulting list."
  (let skip-front ((tail list))
    (cond
      ((null? tail) '())
      ((eq? elt (car tail)) (skip-front (cdr tail)))
      (else
       (let remove-rest ((prev tail) (curr (cdr tail)))
         (cond
           ((null? curr) tail)
           ((eq? elt (car curr))
            (set-cdr! prev (cdr curr))
            (remove-rest prev (cdr curr)))
           (else
            (remove-rest curr (cdr curr)))))))))

(define (elisp-remq elt list)
  "Return a copy of LIST with all elements `eq' to ELT removed.
This is like `delq', but it does not modify the original list."
  (let loop ((tail list) (result '()))
    (cond
      ((null? tail) (reverse result))
      ((eq? elt (car tail)) (loop (cdr tail) result))
      (else (loop (cdr tail) (cons (car tail) result))))))

;;;
;;; Type Predicates
;;;

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

;;;
;;; File Utilities
;;;

(define (elisp-complete-filename-p pathname)
  "Return non-nil if PATHNAME is an absolute file name.
On Unix, this is a name starting with a `/'; on MS-DOS and Windows,
it can also be a name starting with `~' or starting with a drive letter
and a colon."
  (if (not (string? pathname))
      #nil
      (let ((len (string-length pathname)))
        (if (= len 0)
            #nil
            (let ((first-char (string-ref pathname 0)))
              (if (or (char=? first-char #\/)
                      (char=? first-char #\~))
                  #t
                  #nil))))))

(define (elisp-file-name-absolute-p filename)
  "Return t if FILENAME is an absolute file name."
  (elisp-complete-filename-p filename))

;;;
;;; Mathematical Utilities
;;;

(define (elisp-copysign x1 x2)
  "Return a value with the magnitude of X1 and the sign of X2."
  (if (or (not (number? x1)) (not (number? x2)))
      (error "Wrong type argument: numberp")
      (let ((abs-x1 (abs x1)))
        (if (negative? x2)
            (- abs-x1)
            abs-x1))))

(define (elisp-frexp x)
  "Return a list (SIGNIFICAND EXPONENT) where X = SIGNIFICAND * 2^EXPONENT.
SIGNIFICAND is in the range [0.5, 1.0)."
  (if (not (number? x))
      (error "Wrong type argument: numberp" x)
      (if (= x 0)
          (list 0 0)
          (let* ((abs-x (abs x))
                 (exponent (inexact->exact (ceiling (log abs-x 2))))
                 (significand (/ abs-x (expt 2 exponent))))
            (if (negative? x)
                (list (- significand) exponent)
                (list significand exponent))))))

(define (elisp-ldexp sgnfcand exponent)
  "Return SGNFCAND * 2^EXPONENT."
  (if (or (not (number? sgnfcand)) (not (integer? exponent)))
      (error "Wrong type argument")
      (* sgnfcand (expt 2 exponent))))

(define (elisp-logb arg)
  "Return the binary exponent of ARG as an integer."
  (if (not (number? arg))
      (error "Wrong type argument: numberp" arg)
      (if (= arg 0)
          most-negative-fixnum  ; Return large negative value for zero
          (inexact->exact (floor (log (abs arg) 2))))))

(define (elisp-sign number)
  "Return -1, 0, or 1 according to the sign of NUMBER."
  (cond
    ((not (number? number)) (error "Wrong type argument: numberp" number))
    ((> number 0) 1)
    ((< number 0) -1)
    (else 0)))

(define (elisp-clamp x min max)
  "Return X constrained to the range [MIN, MAX]."
  (cond
    ((< x min) min)
    ((> x max) max)
    (else x)))

(define (elisp-square x)
  "Return X squared."
  (if (not (number? x))
      (error "Wrong type argument: numberp" x)
      (* x x)))

;;;
;;; I/O Functions
;;;

(define elisp-read-char
  (case-lambda
    (()
     (elisp-read-char #nil #nil #nil))
    ((prompt)
     (elisp-read-char prompt #nil #nil))
    ((prompt inherit-input-method)
     (elisp-read-char prompt inherit-input-method #nil))
    ((prompt inherit-input-method seconds)
     "Read a character event from the command input (keyboard or macro).
It is returned as a number.
If the optional argument PROMPT is non-nil, display that as a prompt.
If the optional argument INHERIT-INPUT-METHOD is non-nil and some
input method is turned on in the current buffer, that input method
is used for reading a character.
If the optional argument SECONDS is non-nil, it should be a number
specifying the maximum number of seconds to wait for input."
     (char->integer (read-char)))))

;;;
;;; Buffer Operations
;;;

(define (elisp-save-current-buffer thunk)
  "Record which buffer is current; execute THUNK; make that buffer current.
This is the Guile implementation of save-current-buffer using dynamic-wind
for proper cleanup semantics."
  (let ((saved-buffer (current-buffer)))
    (dynamic-wind
      (lambda () #t)
      (lambda () (funcall thunk))
      (lambda ()
        (when (buffer-live-p saved-buffer)
          (set-buffer saved-buffer))))))

(define (elisp-with-current-buffer buffer thunk)
  "Execute THUNK with BUFFER as the current buffer.
Uses dynamic-wind to ensure buffer is properly restored."
  (let ((saved-buffer (current-buffer)))
    (dynamic-wind
      (lambda () (set-buffer buffer))
      (lambda () (funcall thunk))
      (lambda () (set-buffer saved-buffer)))))

;;;
;;; Registration with Elisp symbol table
;;; NOTE: All registrations commented out to avoid conflicts with prelude/load.scm
;;; These functions are defined here but registered in load.scm for now.
;;; Once we migrate functions from load.scm to this module, we can uncomment
;;; the registrations incrementally.
;;;

;; Load system
;; (set-symbol-function! 'get-load-suffixes elisp-get-load-suffixes)

;; Obarray operations
;; (set-symbol-function! 'obarrayp elisp-obarrayp)
;; (set-symbol-function! 'obarray-make elisp-obarray-make)
;; (set-symbol-function! 'obarray-clear elisp-obarray-clear)
;; (set-symbol-function! 'intern elisp-intern)
;; (set-symbol-function! 'intern-soft elisp-intern-soft-lread)
;; (set-symbol-function! 'unintern elisp-unintern)

;; Symbol properties
;; (set-symbol-function! 'symbol-plist elisp-symbol-plist)
;; (set-symbol-function! 'setplist elisp-setplist)
;; (set-symbol-function! 'get elisp-get)
;; (set-symbol-function! 'put elisp-put)

;; Hash tables
;; (set-symbol-function! 'hash-table-count elisp-hash-table-count)
;; (set-symbol-function! 'clrhash elisp-clrhash)

;; Feature/provide
;; (set-symbol-function! 'featurep elisp-featurep)
;; (set-symbol-function! 'provide elisp-provide)

;; List utilities
;; (set-symbol-function! 'nreverse elisp-nreverse)
;; (set-symbol-function! 'delq elisp-delq)
;; (set-symbol-function! 'remq elisp-remq)

;; Type predicates
;; (set-symbol-function! 'markerp elisp-markerp)
;; (set-symbol-function! 'keywordp elisp-keywordp)

;; File utilities
;; (set-symbol-function! 'file-name-absolute-p elisp-file-name-absolute-p)

;; Mathematical utilities
;; (set-symbol-function! 'copysign elisp-copysign)
;; (set-symbol-function! 'frexp elisp-frexp)
;; (set-symbol-function! 'ldexp elisp-ldexp)
;; (set-symbol-function! 'logb elisp-logb)
;; (set-symbol-function! 'clamp elisp-clamp)

;; I/O functions
;; (set-symbol-function! 'read-char elisp-read-char)

;; Buffer operations
;; (set-symbol-function! 'save-current-buffer elisp-save-current-buffer)
;; (set-symbol-function! 'with-current-buffer elisp-with-current-buffer)
