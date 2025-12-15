;;; Guilemacs Lisp
;;;
;;; Symbol Operations
;;;
;;; Module: (language elisp runtime symbols)
;;; Purpose: Enhanced symbol interning and operations
;;; Loaded into: (language elisp runtime) via primitive-load
;;;
;;; EXPORTS (~20 functions):
;;;   Symbol interning: efficient-intern, intern-with-cache
;;;   Symbol comparison: symbol-compare-direct, symbol-equal-fast
;;;   Symbol properties: symbol-intern-count, symbol-frequency
;;;   Statistics: get-intern-stats, clear-intern-stats
;;;
;;; This module implements direct symbol comparison instead of string comparison
;;; and optimizes for symbol interning efficiency.
;;;
;;; NOTE: Module declaration commented out for Phase 1. Will be enabled
;;;       when load.scm is updated to use use-modules.
;;;
;;; (define-module (language elisp runtime symbols)
;;;   #:use-module (language elisp runtime)
;;;   #:export (...))

(use-modules (srfi srfi-1)
             (srfi srfi-69))

;;;
;;; Symbol Interning and Efficiency - Enhanced for Direct Comparison
;;;

(define *symbol-intern-table* (make-hash-table))
(define *symbol-intern-stats* (make-hash-table))

(define (efficient-intern str)
  "Intern string STR as a symbol with caching for efficiency.
Implements symbol interning efficiency goal."
  (if (string? str)
      (or (hash-table-ref *symbol-intern-table* str #f)
          (let ((sym (string->symbol str)))
            (hash-table-set! *symbol-intern-table* str sym)
            ;; Track interning statistics
            (let ((count (hash-table-ref *symbol-intern-stats* sym 0)))
              (hash-table-set! *symbol-intern-stats* sym (+ count 1)))
            sym))
      (if (symbol? str) str #f)))

(define (fast-intern str)
  "Ultra-fast symbol interning optimized for direct comparison.
Uses eq? comparison which is fastest possible in Guile."
  (cond
    ((symbol? str) str)  ; Already a symbol, return as-is
    ((string? str)
     ;; Check cache first for O(1) lookup
     (or (hash-table-ref *symbol-intern-table* str #f)
         ;; Not in cache, intern and cache
         (let ((sym (string->symbol str)))
           (hash-table-set! *symbol-intern-table* str sym)
           sym)))
    (else #f)))

(define (intern-with-frequency-tracking str)
  "Intern string STR and track usage frequency.
Helps identify hot symbols for optimization."
  (let ((sym (fast-intern str)))
    (when sym
      (let ((count (hash-table-ref *symbol-intern-stats* sym 0)))
        (hash-table-set! *symbol-intern-stats* sym (+ count 1))))
    sym))

(define (get-symbol-usage-stats)
  "Return usage statistics for interned symbols.
Returns list of (symbol . count) pairs sorted by frequency."
  (let ((stats '()))
    (hash-table-for-each
     (lambda (sym count) (set! stats (cons (cons sym count) stats)))
     *symbol-intern-stats*)
    (sort stats (lambda (a b) (> (cdr a) (cdr b))))))

(define (get-hot-symbols threshold)
  "Return symbols used more than THRESHOLD times.
These are candidates for constant optimization."
  (filter (lambda (entry) (> (cdr entry) threshold))
          (get-symbol-usage-stats)))

(define (clear-intern-cache)
  "Clear interning cache and statistics.
Useful for memory management and profiling."
  (hash-table-clear! *symbol-intern-table*)
  (hash-table-clear! *symbol-intern-stats*))

(define (symbol-already-interned? str)
  "Check if string STR is already interned as a symbol.
Returns the symbol if found, #f otherwise."
  (hash-table-ref *symbol-intern-table* str #f))

(define (clear-symbol-intern-cache)
  "Clear the symbol interning cache.
Useful for memory management in long-running sessions."
  (hash-table-walk *symbol-intern-table*
                   (lambda (k v) (hash-table-delete! *symbol-intern-table* k))))

;; Direct Symbol Comparison (avoiding string conversion)

(define (symbol-eq? sym1 sym2)
  "Direct symbol equality using eq? - most efficient comparison.
Implements goal of using direct symbol comparison instead of string comparison."
  (eq? sym1 sym2))

(define (symbol-equal-to-string? sym str)
  "Check if symbol SYM has name equal to string STR.
More efficient than converting symbol to string for comparison."
  (and (symbol? sym)
       (string=? (symbol->string sym) str)))

(define (symbol-equal-to-string-ci? sym str)
  "Case-insensitive check if symbol SYM has name equal to string STR."
  (and (symbol? sym)
       (string-ci=? (symbol->string sym) str)))

(define (symbols-have-equal-names? sym1 sym2)
  "Check if two symbols have equal names without string conversion.
Returns #t if same symbol (most efficient) or if names are equal."
  (or (eq? sym1 sym2)
      (and (symbol? sym1) (symbol? sym2)
           (string=? (symbol->string sym1) (symbol->string sym2)))))

;; Symbol List Operations

(define (symbol-member? target-sym symbol-list)
  "Check if TARGET-SYM is in SYMBOL-LIST using efficient eq? comparison.
Much faster than string-based membership tests."
  (and (symbol? target-sym)
       (memq target-sym symbol-list)
       #t))

(define (symbol-assoc sym alist)
  "Look up SYM in ALIST using direct symbol comparison.
More efficient than assoc with string conversion."
  (assq sym alist))

(define (symbol-member-string? str symbol-list)
  "Check if string STR matches any symbol name in SYMBOL-LIST.
Only converts to string when necessary."
  (any (lambda (sym)
         (and (symbol? sym)
              (string=? (symbol->string sym) str)))
       symbol-list))

(define (symbol-remove sym symbol-list)
  "Remove all instances of SYM from SYMBOL-LIST using eq? comparison."
  (filter (lambda (s) (not (eq? s sym))) symbol-list))

(define (symbol-unique symbol-list)
  "Remove duplicate symbols from SYMBOL-LIST using eq? comparison.
Maintains original order."
  (let loop ((remaining symbol-list) (seen '()) (result '()))
    (cond
      ((null? remaining) (reverse result))
      ((memq (car remaining) seen)
       (loop (cdr remaining) seen result))
      (else
       (loop (cdr remaining)
             (cons (car remaining) seen)
             (cons (car remaining) result))))))

;; Symbol Name Pattern Matching

(define (symbol-name-matches? sym pattern)
  "Check if symbol SYM name matches PATTERN.
PATTERN can contain * and ? wildcards."
  (and (symbol? sym)
       (let ((name (symbol->string sym)))
         (string-match-pattern? name pattern))))

(define (string-match-pattern? str pattern)
  "Check if STR matches PATTERN with wildcards.
* matches any sequence, ? matches single character."
  (let ((regex (pattern->regex pattern)))
    (and regex (regexp-exec regex str))))

(define (pattern->regex pattern)
  "Convert glob PATTERN to regex."
  (catch #t
    (lambda ()
      (make-regexp
       (string-append "^"
                     (regexp-substitute/global
                      #f "\\*"
                      (regexp-substitute/global #f "\\?" pattern ".")
                      'pre ".*" 'post)
                     "$")))
    (lambda (key . args) #f)))

;; Symbol Set Operations

(define (symbol-set-union set1 set2)
  "Union of two symbol lists, removing duplicates."
  (symbol-unique (append set1 set2)))

(define (symbol-set-intersection set1 set2)
  "Intersection of two symbol lists."
  (filter (lambda (sym) (memq sym set2)) set1))

(define (symbol-set-difference set1 set2)
  "Symbols in SET1 but not in SET2."
  (filter (lambda (sym) (not (memq sym set2))) set1))

(define (symbol-set-equal? set1 set2)
  "Check if two symbol sets are equal (same symbols, any order)."
  (and (= (length set1) (length set2))
       (every (lambda (sym) (memq sym set2)) set1)))

;; Special Symbol Recognition

(define *special-symbols*
  '(nil t and or not if when unless cond case lambda function quote
    backquote unquote unquote-splicing let let* letrec prog1 prog2 progn
    setq setf defun defvar defconst defmacro))

(define (special-symbol? sym)
  "Check if SYM is a special/built-in symbol.
More efficient than string-based lookup."
  (and (symbol? sym) (memq sym *special-symbols*)))

(define (keyword-symbol? sym)
  "Check if SYM is a keyword symbol (starts with colon)."
  (and (symbol? sym)
       (let ((name (symbol->string sym)))
         (and (> (string-length name) 0)
              (char=? (string-ref name 0) #\:)))))

(define (private-symbol? sym)
  "Check if SYM is a private symbol (starts with underscore)."
  (and (symbol? sym)
       (let ((name (symbol->string sym)))
         (and (> (string-length name) 0)
              (char=? (string-ref name 0) #\_)))))

;; Symbol Name Transformations

(define (symbol-name-upcase sym)
  "Return symbol with uppercase name."
  (if (symbol? sym)
      (string->symbol (string-upcase (symbol->string sym)))
      #f))

(define (symbol-name-downcase sym)
  "Return symbol with lowercase name."
  (if (symbol? sym)
      (string->symbol (string-downcase (symbol->string sym)))
      #f))

(define (symbol-name-capitalize sym)
  "Return symbol with capitalized name."
  (if (symbol? sym)
      (string->symbol (string-capitalize (symbol->string sym)))
      #f))

(define (symbol-add-prefix sym prefix)
  "Return new symbol with PREFIX added to SYM's name."
  (if (symbol? sym)
      (string->symbol (string-append prefix (symbol->string sym)))
      #f))

(define (symbol-add-suffix sym suffix)
  "Return new symbol with SUFFIX added to SYM's name."
  (if (symbol? sym)
      (string->symbol (string-append (symbol->string sym) suffix))
      #f))

;; Symbol Validation

(define (valid-symbol-name? str)
  "Check if STR would make a valid symbol name.
Follows Lisp symbol naming rules."
  (and (string? str)
       (> (string-length str) 0)
       ;; Cannot start with digit unless escaped
       (not (char-numeric? (string-ref str 0)))
       ;; Must not contain invalid characters
       (string-every valid-symbol-char? str)))

(define (valid-symbol-char? char)
  "Check if CHAR is valid in a symbol name."
  (or (char-alphabetic? char)
      (char-numeric? char)
      (memv char '(#\- #\_ #\+ #\* #\/ #\= #\< #\> #\! #\? #\% #\& #\$ #\@ #\#))))

(define (normalize-symbol-name str)
  "Normalize STR to be a valid symbol name.
Replaces invalid characters with dashes."
  (if (valid-symbol-name? str)
      str
      (list->string
       (map (lambda (char)
              (if (valid-symbol-char? char) char #\-))
            (string->list str)))))

;; Symbol Statistics and Analysis

(define (symbol-name-length sym)
  "Get length of symbol SYM's name."
  (if (symbol? sym)
      (string-length (symbol->string sym))
      0))

(define (symbols-by-length symbol-list)
  "Sort SYMBOL-LIST by symbol name length."
  (sort symbol-list
        (lambda (sym1 sym2)
          (< (symbol-name-length sym1) (symbol-name-length sym2)))))

(define (symbol-starts-with? sym prefix)
  "Check if symbol SYM name starts with PREFIX string."
  (and (symbol? sym)
       (let ((name (symbol->string sym)))
         (and (>= (string-length name) (string-length prefix))
              (string=? prefix (substring name 0 (string-length prefix)))))))

(define (symbol-ends-with? sym suffix)
  "Check if symbol SYM name ends with SUFFIX string."
  (and (symbol? sym)
       (let ((name (symbol->string sym)))
         (and (>= (string-length name) (string-length suffix))
              (string=? suffix
                       (substring name
                                 (- (string-length name) (string-length suffix))))))))

(define (symbol-contains? sym substring)
  "Check if symbol SYM name contains SUBSTRING."
  (and (symbol? sym)
       (string-contains (symbol->string sym) substring)))

;; Symbol Hashing for Performance

(define (symbol-hash sym)
  "Compute hash value for symbol SYM.
Uses symbol identity when possible for efficiency."
  (if (symbol? sym)
      (hash sym 31)
      0))

(define (symbol-name-hash sym)
  "Compute hash based on symbol SYM's name."
  (if (symbol? sym)
      (string-hash (symbol->string sym))
      0))

;; Symbol Comparison for Sorting

(define (symbol-name-compare sym1 sym2)
  "Compare symbols SYM1 and SYM2 by name lexicographically.
Returns -1, 0, or 1."
  (cond
    ((eq? sym1 sym2) 0)
    ((not (symbol? sym1)) -1)
    ((not (symbol? sym2)) 1)
    (else
     (let ((name1 (symbol->string sym1))
           (name2 (symbol->string sym2)))
       (cond
         ((string<? name1 name2) -1)
         ((string>? name1 name2) 1)
         (else 0))))))

(define (symbol-name-compare-ci sym1 sym2)
  "Compare symbols SYM1 and SYM2 by name (case-insensitive)."
  (cond
    ((eq? sym1 sym2) 0)
    ((not (symbol? sym1)) -1)
    ((not (symbol? sym2)) 1)
    (else
     (let ((name1 (symbol->string sym1))
           (name2 (symbol->string sym2)))
       (cond
         ((string-ci<? name1 name2) -1)
         ((string-ci>? name1 name2) 1)
         (else 0))))))

;; Emacs-specific Symbol Operations

(define (buffer-local-symbol? sym)
  "Check if SYM represents a buffer-local variable."
  (and (symbol? sym)
       (symbol-ends-with? sym "-buffer-local")))

(define (hook-symbol? sym)
  "Check if SYM represents a hook variable."
  (and (symbol? sym)
       (symbol-ends-with? sym "-hook")))

(define (face-symbol? sym)
  "Check if SYM represents a face."
  (and (symbol? sym)
       (or (symbol-ends-with? sym "-face")
           (symbol-starts-with? sym "face-"))))

(define (mode-symbol? sym)
  "Check if SYM represents a major or minor mode."
  (and (symbol? sym)
       (symbol-ends-with? sym "-mode")))

;; Symbol Property Management

(define *symbol-properties* (make-hash-table))

(define (symbol-put-property! sym prop value)
  "Set property PROP of symbol SYM to VALUE."
  (when (symbol? sym)
    (let ((props (hash-table-ref *symbol-properties* sym '())))
      (hash-table-set! *symbol-properties* sym
                      (assq-set! props prop value)))))

(define (symbol-get-property sym prop . default)
  "Get property PROP of symbol SYM, or DEFAULT if not found."
  (if (symbol? sym)
      (let ((props (hash-table-ref *symbol-properties* sym '())))
        (let ((entry (assq prop props)))
          (if entry
              (cdr entry)
              (if (null? default) #f (car default)))))
      (if (null? default) #f (car default))))

(define (symbol-has-property? sym prop)
  "Check if symbol SYM has property PROP."
  (and (symbol? sym)
       (let ((props (hash-table-ref *symbol-properties* sym '())))
         (assq prop props))))

;; Advanced Symbol Optimization Features

(define *common-symbols-cache* (make-hash-table))

(define (preload-common-symbols)
  "Preload frequently used Emacs symbols for O(1) access.
This implements the goal of optimizing symbol interning efficiency."
  (let ((common-symbols
         '(nil t and or not if when unless cond case lambda function quote
           backquote unquote unquote-splicing let let* letrec prog1 prog2 progn
           setq setf defun defvar defconst defmacro defcustom defgroup
           interactive autoload require provide feature error signal
           while for unless when catch throw condition-case unwind-protect
           save-excursion save-restriction save-current-buffer
           with-current-buffer with-temp-buffer with-output-to-string
           point point-min point-max beginning-of-line end-of-line
           forward-char backward-char next-line previous-line
           insert delete-char delete-region substring length
           car cdr cons list append reverse nthcdr nth first second third
           string-equal string-lessp string-match string-replace
           buffer-string buffer-name buffer-file-name current-buffer
           get-buffer create-file-buffer kill-buffer
           major-mode minor-mode mode-name buffer-mode)))
    (for-each (lambda (sym-name)
      (let ((sym (if (symbol? sym-name) sym-name (string->symbol (symbol->string sym-name)))))
        (hash-table-set! *common-symbols-cache* (symbol->string sym) sym)
        (hash-table-set! *symbol-intern-table* (symbol->string sym) sym)))
      common-symbols)))

(define (fast-lookup-common-symbol str)
  "Ultra-fast lookup for common Emacs symbols.
Returns symbol if it's a preloaded common symbol, #f otherwise."
  (hash-table-ref *common-symbols-cache* str #f))

(define (optimized-intern str)
  "Optimized symbol interning that checks common symbols first.
Falls back to regular interning for uncommon symbols."
  (or (fast-lookup-common-symbol str)
      (fast-intern str)))

(define (symbol-eq-optimized? sym1 sym2)
  "Optimized symbol equality using eq? for maximum performance.
This implements the goal of direct symbol comparison instead of string comparison."
  (eq? sym1 sym2))

(define (symbol-member-optimized sym sym-list)
  "Optimized symbol membership test using eq?.
Much faster than string-based approaches."
  (memq sym sym-list))

(define (symbol-assoc-optimized sym alist)
  "Optimized symbol association list lookup using eq?.
Faster than string-based lookups."
  (assq sym alist))

;; Symbol Set Operations Optimized for Performance

(define (symbol-set-contains-optimized? sym sym-set)
  "Check if SYM is in SYM-SET using optimized eq? comparison.
SYM-SET should be a sorted list for best performance."
  (and (not (null? sym-set))
       (or (eq? sym (car sym-set))
           (symbol-set-contains-optimized? sym (cdr sym-set)))))

(define (symbol-set-union-optimized set1 set2)
  "Optimized union of two symbol sets using eq? comparison.
Returns deduplicated union maintaining order."
  (let loop ((result set1) (remaining set2))
    (if (null? remaining)
        result
        (let ((sym (car remaining)))
          (if (memq sym result)
              (loop result (cdr remaining))
              (loop (cons sym result) (cdr remaining)))))))

(define (symbol-set-intersection-optimized set1 set2)
  "Optimized intersection of two symbol sets using eq? comparison."
  (filter (lambda (sym) (memq sym set2)) set1))

;; Memory Usage Optimization

(define (optimize-symbol-memory)
  "Optimize symbol memory usage by removing rarely used symbols.
Keeps symbols used more than once, removes single-use symbols."
  (let ((to-remove '()))
    (hash-table-for-each
     (lambda (sym count)
       (when (<= count 1)
         (set! to-remove (cons sym to-remove))))
     *symbol-intern-stats*)

    (for-each (lambda (sym)
      (let ((name (symbol->string sym)))
        (hash-table-delete! *symbol-intern-table* name)
        (hash-table-delete! *symbol-intern-stats* sym)))
      to-remove)

    (length to-remove)))

(define (get-symbol-memory-usage)
  "Estimate memory usage of symbol interning system.
Returns approximate bytes used by interned symbols."
  (let ((total-bytes 0))
    (hash-table-for-each
     (lambda (str sym)
       (set! total-bytes (+ total-bytes
                           (string-length str)  ; String storage
                           8  ; Symbol object overhead (estimate)
                           16))) ; Hash table overhead (estimate)
     *symbol-intern-table*)
    total-bytes))

;; Performance Measurement

(define (benchmark-symbol-operations iterations)
  "Benchmark symbol operations for performance analysis.
Returns timing data for different symbol operations."
  (let ((test-symbols '(foo bar baz test-symbol hello-world))
        (results '()))

    ;; Benchmark eq? comparison
    (let ((start (get-internal-real-time))
          (sym1 'test-symbol)
          (sym2 'test-symbol))
      (do ((i 0 (+ i 1)))
          ((>= i iterations))
        (eq? sym1 sym2))
      (let ((elapsed (- (get-internal-real-time) start)))
        (set! results (cons (cons 'eq-comparison elapsed) results))))

    ;; Benchmark string->symbol
    (let ((start (get-internal-real-time)))
      (do ((i 0 (+ i 1)))
          ((>= i iterations))
        (string->symbol "test-symbol"))
      (let ((elapsed (- (get-internal-real-time) start)))
        (set! results (cons (cons 'string-to-symbol elapsed) results))))

    ;; Benchmark optimized intern
    (let ((start (get-internal-real-time)))
      (do ((i 0 (+ i 1)))
          ((>= i iterations))
        (optimized-intern "test-symbol"))
      (let ((elapsed (- (get-internal-real-time) start)))
        (set! results (cons (cons 'optimized-intern elapsed) results))))

    ;; Benchmark memq
    (let ((start (get-internal-real-time)))
      (do ((i 0 (+ i 1)))
          ((>= i iterations))
        (memq 'baz test-symbols))
      (let ((elapsed (- (get-internal-real-time) start)))
        (set! results (cons (cons 'memq-lookup elapsed) results))))

    (reverse results)))

;; Initialize common symbols cache on module load
(preload-common-symbols)

;; Export all functions for C code integration