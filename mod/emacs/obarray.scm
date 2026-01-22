;;; obarray.scm --- obarray emulation for vanilla Guile
;;;
;;; Copyright (C) 2025 Free Software Foundation, Inc.
;;;
;;; Strategy:
;;; - Global obarray uses Guile's string->symbol but tracks all symbols
;;;   in a hash table for mapatoms support
;;; - Custom obarrays are hash tables mapping string -> symbol
;;; - Single source of truth: *global-symbols* hash table
;;;

(define-module (emacs obarray)
  #:use-module (ice-9 hash-table)
  #:export (;; Core obarray operations
            guilemacs-intern
            guilemacs-intern-soft
            guilemacs-find-symbol
            guilemacs-unintern
            guilemacs-mapatoms
            ;; Obarray management
            guilemacs-make-obarray
            guilemacs-obarray-clear
            ;; Predicates
            guilemacs-global-obarray?
            ;; Symbol tracking
            *global-symbols*
            register-symbol!
            ;; For C integration
            obarray-intern
            obarray-find-symbol
            obarray-mapatoms
            obarray-unintern
            obarray-clear))

;; Late-bound reference to for-each-elisp-symbol from runtime module.
;; We can't use #:use-module because runtime loads after obarray.
(define for-each-elisp-symbol-ref #f)

(define (get-for-each-elisp-symbol)
  "Get the for-each-elisp-symbol function from runtime module.
Uses lazy initialization to avoid circular dependency."
  (unless for-each-elisp-symbol-ref
    (let ((mod (resolve-module '(emacs-elisp runtime) #:ensure #f)))
      (when mod
        (let ((var (module-variable mod 'for-each-elisp-symbol)))
          (when (and var (variable-bound? var))
            (set! for-each-elisp-symbol-ref (variable-ref var)))))))
  for-each-elisp-symbol-ref)

;;; ----------------------------------------------------------------------------
;;; Global symbol tracking - single source of truth
;;; ----------------------------------------------------------------------------

;; All symbols interned in global obarray are tracked here.
;; Key: string, Value: symbol
;; This is the authoritative source for mapatoms.
(define *global-symbols* (make-hash-table 8192))

;; Counter for unique symbol names in custom obarrays
(define *obarray-counter* 0)

;;; ----------------------------------------------------------------------------
;;; Predicates
;;; ----------------------------------------------------------------------------

(define (guilemacs-global-obarray? obarray)
  "Return #t if OBARRAY represents the global obarray.
The global obarray is indicated by #nil, #f, or a Lisp_Obarray object
that C marks as global."
  ;; In practice, C will pass the actual obarray object.
  ;; We check for #nil/#f which mean 'use default'.
  ;; C code will also pass a flag or we detect by checking if it's
  ;; NOT a hash-table (custom obarrays are hash tables).
  (or (not obarray)
      (eq? obarray #nil)
      ;; If it's not a hash-table, assume it's the global obarray marker from C
      (not (hash-table? obarray))))

;;; ----------------------------------------------------------------------------
;;; Core operations
;;; ----------------------------------------------------------------------------

(define (register-symbol! str sym)
  "Register SYM under STR in global symbol table.
Used by C code when interning symbols during bootstrap."
  (hash-set! *global-symbols* str sym))

(define* (guilemacs-intern str #:optional (obarray #nil))
  "Intern string STR in OBARRAY, returning the symbol.
For global obarray: handles nil/t specially, tracks symbol, handles keywords.
For custom obarray: creates unique symbol, stores in hash table."
  (cond
   ;; Global obarray
   ((guilemacs-global-obarray? obarray)
    ;; Special case: "nil" must return #nil (Elisp canonical nil)
    (cond
     ((string=? str "nil") #nil)
     ((string=? str "t") #t)
     (else
      ;; Check if already tracked
      (let ((existing (hash-ref *global-symbols* str #f)))
        (if existing
            existing
            ;; Create new symbol via Guile's string->symbol
            (let ((sym (string->symbol str)))
              ;; Track it
              (hash-set! *global-symbols* str sym)
              ;; Handle keywords (symbols starting with :)
              ;; Keywords are self-evaluating in Elisp
              (when (and (> (string-length str) 0)
                         (char=? (string-ref str 0) #\:))
                ;; Mark as keyword - C will handle SET_SYMBOL_VAL
                ;; For now, just return the symbol; C does the rest
                #f)
              sym))))))

   ;; Custom obarray (hash table)
   ((hash-table? obarray)
    (let ((existing (hash-ref obarray str #f)))
      (if existing
          existing
          ;; Create unique symbol name to avoid collision with global symbols
          (let* ((unique-name (string-append "__ob"
                                             (number->string *obarray-counter*)
                                             "_" str))
                 (sym (string->symbol unique-name)))
            (set! *obarray-counter* (1+ *obarray-counter*))
            (hash-set! obarray str sym)
            sym))))

   (else
    (error "Invalid obarray" obarray))))

(define* (guilemacs-intern-soft str #:optional (obarray #nil))
  "Look up STR in OBARRAY without creating a new symbol.
Returns the symbol if found, #nil otherwise."
  (cond
   ;; Global obarray
   ((guilemacs-global-obarray? obarray)
    ;; In vanilla Guile, string->symbol always succeeds.
    ;; For better Emacs compatibility, we could check *global-symbols*
    ;; but that would break code expecting intern-soft to always work
    ;; on global obarray. Match current behavior: always return symbol.
    (cond
     ((string=? str "nil") #nil)
     ((string=? str "t") #t)
     (else
      ;; Check tracked symbols first
      (let ((existing (hash-ref *global-symbols* str #f)))
        (if existing
            existing
            ;; Return symbol anyway (Guile always interns)
            ;; This matches current guilemacs behavior
            (string->symbol str))))))

   ;; Custom obarray - true soft lookup
   ((hash-table? obarray)
    (or (hash-ref obarray str #f) #nil))

   (else
    (error "Invalid obarray" obarray))))

(define* (guilemacs-find-symbol str #:optional (obarray #nil))
  "Find symbol named STR in OBARRAY.
Returns (values symbol found?) - multiple values for C consumption."
  (cond
   ;; Global obarray
   ((guilemacs-global-obarray? obarray)
    (cond
     ((string=? str "nil") (values #nil #t))
     ((string=? str "t") (values #t #t))
     (else
      ;; Guile always finds/creates symbols
      (let ((sym (or (hash-ref *global-symbols* str #f)
                     (string->symbol str))))
        (values sym #t)))))

   ;; Custom obarray
   ((hash-table? obarray)
    (let ((sym (hash-ref obarray str #f)))
      (if sym
          (values sym #t)
          (values #nil #nil))))

   (else
    (error "Invalid obarray" obarray))))

(define* (guilemacs-unintern name #:optional (obarray #nil))
  "Remove symbol named NAME from OBARRAY.
NAME can be a string or symbol.
Returns #t if removed, #nil otherwise."
  (let ((str (if (symbol? name) (symbol->string name) name)))
    (cond
     ;; Global obarray - can't truly unintern from Guile
     ;; but we can remove from our tracking table
     ((guilemacs-global-obarray? obarray)
      (if (hash-ref *global-symbols* str #f)
          (begin
            (hash-remove! *global-symbols* str)
            #t)
          #nil))

     ;; Custom obarray
     ((hash-table? obarray)
      (if (hash-ref obarray str #f)
          (begin
            (hash-remove! obarray str)
            #t)
          #nil))

     (else
      (error "Invalid obarray" obarray)))))

(define* (guilemacs-mapatoms proc #:optional (obarray #nil))
  "Call PROC on each symbol in OBARRAY."
  (cond
   ;; Global obarray - iterate our tracking table AND runtime modules
   ((guilemacs-global-obarray? obarray)
    ;; Use a seen table to avoid calling proc twice for same symbol
    (let ((seen (make-hash-table)))
      ;; First iterate *global-symbols* (symbols interned via Fintern)
      (hash-for-each
       (lambda (str sym)
         (unless (hashq-ref seen sym)
           (hashq-set! seen sym #t)
           (proc sym)))
       *global-symbols*)
      ;; Then iterate runtime modules (symbols created by Guile's reader)
      (let ((for-each-fn (get-for-each-elisp-symbol)))
        (when for-each-fn
          (for-each-fn
           (lambda (sym)
             (unless (hashq-ref seen sym)
               (hashq-set! seen sym #t)
               (proc sym))))))))

   ;; Custom obarray
   ((hash-table? obarray)
    (hash-for-each (lambda (str sym) (proc sym)) obarray))

   (else
    (error "Invalid obarray" obarray))))

;;; ----------------------------------------------------------------------------
;;; Obarray management
;;; ----------------------------------------------------------------------------

(define* (guilemacs-make-obarray #:optional (size 67))
  "Create a new custom obarray with SIZE buckets."
  (make-hash-table size))

(define* (guilemacs-obarray-clear #:optional (obarray #nil))
  "Clear all symbols from OBARRAY."
  (cond
   ((guilemacs-global-obarray? obarray)
    ;; Can't clear the global obarray
    #nil)
   ((hash-table? obarray)
    (hash-clear! obarray)
    #t)
   (else
    (error "Invalid obarray" obarray))))

;;; ----------------------------------------------------------------------------
;;; C integration interface
;;; These are the entry points called from lread.c
;;; ----------------------------------------------------------------------------

(define (obarray-intern string obarray-or-nil)
  "C entry point for intern.
OBARRAY-OR-NIL is the obarray or #nil for global."
  (guilemacs-intern string obarray-or-nil))

(define (obarray-find-symbol string obarray-or-nil)
  "C entry point for find-symbol.
Returns multiple values: (symbol found?)."
  (guilemacs-find-symbol string obarray-or-nil))

(define (obarray-mapatoms proc obarray-or-nil)
  "C entry point for mapatoms."
  (guilemacs-mapatoms proc obarray-or-nil))

(define (obarray-unintern name obarray-or-nil)
  "C entry point for unintern."
  (guilemacs-unintern name obarray-or-nil))

(define (obarray-clear obarray-or-nil)
  "C entry point for obarray-clear."
  (guilemacs-obarray-clear obarray-or-nil))

;;; ----------------------------------------------------------------------------
;;; End of obarray.scm
;;; ----------------------------------------------------------------------------
