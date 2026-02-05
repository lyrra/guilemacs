;; Copyright (C) Free Software Foundation, Inc.
;; SPDX-License-Identifier: GPL-3.0-or-later

(define-module (emacs-elisp runtime)
  #:declarative? #f
  #:use-module (ice-9 format)
  #:use-module (ice-9 pretty-print)
  #:use-module ((system base compile)
                #:select (compile compile-file))
  #:use-module ((system base language)
                #:select (lookup-language))
  #:use-module ((language tree-il)
                #:select (unparse-tree-il parse-tree-il))
  #:export (nil-value
            t-value
            value-slot-module
            function-slot-module
            elisp-bool
            ensure-dynamic!
            symbol-name
            symbol-value
            set-symbol-value!
            symbol-function
            set-symbol-function!
            symbol-plist
            set-symbol-plist!
            symbol-bound?
            symbol-fbound?
            symbol-default-bound?
            symbol-default-value
            set-symbol-default-value!
            bind-symbol
            makunbound!
            fmakunbound!
            symbol-desc
            proclaim-special!
            special?
            emacs!
            unbound
            lexical-binding?
            set-lexical-binding-mode
            log!
            guile-tracelog-write
            guile-tracelog-print
            guile-tracelog-set
            ;emacs-read
            ;emacs-load
            eval-elisp
            compile-elisp
            local-eval-elisp
            %make-lisp-string
            make-lisp-string
            %debugflag
            debugflag
            set-debugflag!
            make-symbol
            intern-gensym
            %lisp-string
            lisp-string?
            elisp-load-with-match-data-protection
            for-each-elisp-symbol
            scheme->tree-il
            define-elisp-inline
            set-inline-source!
            get-inline-source)
  #:export-syntax (defspecial prim))

;;; This module provides runtime support for the Elisp front-end.

;;; Inline source compilation.
;;;
;;; When `define-elisp-inline' defines a primitive, we need to store a
;;; pre-compiled tree-il lambda that the elisp compiler can splice into
;;; call sites.  The body is written as Scheme (using Guile primitives),
;;; compiled to tree-il, then `toplevel' refs are resolved to absolute
;;; module refs so the tree-il works in any module context.
;;;
;;; The resolution walks the module import chain to find the actual
;;; defining module for each binding — no heuristics or guessing.

(define (resolve-binding-module mod name)
  "Find which module provides NAME in MOD's binding environment.
Walks the import chain to find the module that locally defines NAME."
  (cond
   ((module-local-variable mod name)
    (module-name mod))
   (else
    (let loop ((uses (module-uses mod)))
      (cond
       ((null? uses) '(guile))
       ((module-local-variable (car uses) name)
        (module-name (car uses)))
       (else (loop (cdr uses))))))))

(define (absolutize-refs sexp mod)
  "Walk tree-il s-expression SEXP, replacing (toplevel NAME) with
absolute (@ defining-module NAME) by consulting MOD's binding chain."
  (cond
   ((not (pair? sexp)) sexp)
   ((and (eq? (car sexp) 'toplevel)
         (pair? (cdr sexp))
         (symbol? (cadr sexp))
         (null? (cddr sexp)))
    (let ((name (cadr sexp)))
      `(@ ,(resolve-binding-module mod name) ,name)))
   (else
    (cons (absolutize-refs (car sexp) mod)
          (absolutize-refs (cdr sexp) mod)))))

(define (scheme->tree-il expr mod)
  "Compile a Scheme expression to tree-il with all references resolved
to absolute module refs.  Compiles in MOD's context, then absolutizes
toplevel refs via MOD's import chain."
  (let* ((til (compile expr #:from 'scheme #:to 'tree-il #:env mod))
         (sexp (unparse-tree-il til))
         (fixed (absolutize-refs sexp mod)))
    (parse-tree-il fixed)))

(define-syntax define-elisp-inline
  (lambda (x)
    (define (make-scheme-name name-stx)
      (datum->syntax name-stx
        (string->symbol
          (string-append "elisp-"
            (symbol->string (syntax->datum name-stx))))))
    (syntax-case x ()
      ((_ (name . formals) body ...)
       (with-syntax ((sname (make-scheme-name #'name)))
         #'(begin
             (define (sname . formals) body ...)
             (set-symbol-function! 'name sname)
             (set-inline-source! 'name
               (scheme->tree-il '(lambda formals body ...)
                                (current-module)))))))))

;; Maps elisp symbol -> lambda expression for inlinable primitives.
;; The compiler can inline these at call sites.
(define %inline-source-table (make-hash-table))

(define (set-inline-source! elisp-sym lambda-expr)
  (hashq-set! %inline-source-table elisp-sym lambda-expr))

(define (get-inline-source elisp-sym)
  (hashq-ref %inline-source-table elisp-sym))

(define %debugflag 0)

(define (set-debugflag! x)
  (set! %debugflag x))

(define (debugflag)
  %debugflag)

;;; Values for t and nil. (FIXME remove this abstraction)

(define nil-value #nil)

(define t-value #t)

(define make-lisp-string identity)
(define lisp-string? string?)

(define %lisp-string
  (lambda (str)
    ((module-ref (resolve-module '(emacs-elisp runtime)) 'lisp-string?) str)))
(define %make-lisp-string
  (lambda (str)
    ((module-ref (resolve-module '(emacs-elisp runtime)) 'make-lisp-string) str)))
;;; Modules for the binding slots.
;;; Note: Naming those value-slot and/or function-slot clashes with the
;;; submodules of these names!

(define value-slot-module (define-module* '(elisp-symbols) #:pure #t))

(define function-slot-module (define-module* '(elisp-functions) #:pure #t))

(define plist-slot-module (define-module* '(elisp-plists) #:pure #t))

(define nil_ 'nil)
(define t_ 't)

;; Guilemacs: Iterate over all known elisp symbols for mapatoms support.
;; This is needed because we cannot enumerate Guile's global symbol table
;; directly. We collect symbols from all three slot modules.
(define (for-each-elisp-symbol proc)
  "Call PROC on each known elisp symbol.
This iterates over all symbols that have been registered in the
value-slot-module, function-slot-module, or plist-slot-module."
  (let ((seen (make-hash-table)))
    ;; Helper to call proc only once per symbol
    (define (visit name var)
      (let ((sym (string->symbol (symbol->string name))))
        (unless (hashq-ref seen sym)
          (hashq-set! seen sym #t)
          (proc sym))))
    ;; Iterate all three modules
    (module-for-each visit value-slot-module)
    (module-for-each visit function-slot-module)
    (module-for-each visit plist-slot-module)))

;;; Routines for access to elisp dynamically bound symbols.  This is
;;; used for runtime access using functions like symbol-value or set,
;;; where the symbol accessed might not be known at compile-time.  These
;;; always access the dynamic binding and can not be used for the
;;; lexical!

(define lexical-binding #t)

(define (lexical-binding?)
  lexical-binding)

(define (set-lexical-binding-mode x)
  (set! lexical-binding x))

;; Define intern-gensym first - creates interned unique symbols
(define %intern-gensym-counter 0)
(define (intern-gensym prefix)
  (set! %intern-gensym-counter (+ 1 %intern-gensym-counter))
  (string->symbol (string-concatenate (list prefix "_" (number->string %intern-gensym-counter)))))

;; make-symbol should create interned symbols to avoid Guile serialization errors
;; Uninterned symbols cannot be saved to .go files
;; Use Guile's native make-symbol to create uninterned symbols
(define (make-symbol name)
  ;(intern-gensym name)
  ((@ (guile) make-symbol) name))

;; unbound marker - now using interned symbol
(define unbound (make-symbol "unbound"))

(define dynamic? vector?)
(define (make-dynamic)
  (vector #f 4 0 0 unbound))
(define (dynamic-ref x)
  (vector-ref x 4))
(define (dynamic-set! x v)
  (vector-set! x 4 v))
(define (dynamic-unset! x)
  (vector-set! x 4 unbound))
(define (dynamic-bound? x)
  (not (eq? (vector-ref x 4) unbound)))
(define (dynamic-bind x v thunk)
  (let ((old (vector-ref x 4)))
   (dynamic-wind
     (lambda () (vector-set! x 4 v))
     thunk
     (lambda () (vector-set! x 4 old)))))

(define (ensure-present! module sym thunk)
  (or (module-local-variable module sym)
      (let ((variable (make-variable (thunk))))
        (module-add! module sym variable)
        variable)))

(define (ensure-desc! module sym)
  (ensure-present! module
                   sym
                   (lambda ()
                     (let ((x (make-dynamic)))
                       (vector-set! x 0 sym)
                       x))))

(define (schemify symbol)
  (case symbol
    ((#nil) nil_)
    ((#t) t_)
    (else symbol)))

(define (symbol-name symbol)
  (symbol->string (schemify symbol)))

(define (symbol-desc symbol)
  (let ((symbol (schemify symbol)))
    (let ((module value-slot-module))
      (variable-ref (ensure-desc! module symbol)))))

(define (ensure-dynamic! sym)
  (vector-set! (symbol-desc sym) 3 1))

(define (symbol-dynamic symbol)
  (ensure-dynamic! symbol)
  (symbol-desc symbol))

(define (symbol-value symbol)
  (dynamic-ref (symbol-desc symbol)))

(define (set-symbol-value! symbol value)
  (dynamic-set! (symbol-desc symbol) value)
  value)

(define (symbol-function symbol)
  (let ((var (module-variable function-slot-module (schemify symbol))))
    (if (and var (variable-bound? var))
        (variable-ref var)
        #nil)))

(define (set-symbol-function! symbol value)
  (set! symbol (schemify symbol))
  (ensure-present! function-slot-module symbol (lambda () #nil))
  (let ((module function-slot-module))
   (module-define! module symbol value)
   (module-export! module (list symbol)))
  value)

(define (symbol-plist symbol)
  (set! symbol (schemify symbol))
  (ensure-present! plist-slot-module symbol (lambda () #nil))
  (let ((module plist-slot-module))
    (module-ref module symbol)))

(define (set-symbol-plist! symbol value)
  (set! symbol (schemify symbol))
  (ensure-present! plist-slot-module symbol (lambda () #nil))
  (let ((module plist-slot-module))
   (module-define! module symbol value)
   (module-export! module (list symbol)))
  value)

(define (symbol-bound? symbol)
  (set! symbol (schemify symbol))
  (and
   (module-bound? value-slot-module symbol)
   (let ((var (module-variable value-slot-module
                               symbol)))
     (and (variable-bound? var)
          (if (dynamic? (variable-ref var))
              (dynamic-bound? (variable-ref var))
              #t)))))

(define symbol-default-bound? symbol-bound?)

(define symbol-default-value symbol-value)

(define set-symbol-default-value! set-symbol-value!)

(define (symbol-fbound? symbol)
  (set! symbol (schemify symbol))
  (and
   (module-bound? function-slot-module symbol)
   (variable-bound?
    (module-variable function-slot-module symbol))
   ;; Must return #t, not the function value itself - fboundp callers expect t
   (not (eq? #nil (variable-ref (module-variable function-slot-module symbol))))))

;; Sentinel for detecting "not found" in hash table lookups.
(define *buffer-local-unset* (list 'buffer-local-unset))

;; Lazily-cached handle for the C `buffer-local-hash' DEFUN.
;; Not available at module load time (syms_of_buffer runs later),
;; but always available by the time bind-symbol is first called.
(define %buffer-local-hash-fn #f)
(define (buffer-local-hash-fn)
  (or %buffer-local-hash-fn
      (let ((fn (symbol-function 'buffer-local-hash)))
        (set! %buffer-local-hash-fn fn)
        fn)))

;; bind-symbol: dynamically bind SYMBOL to VALUE during THUNK.
;;
;; Three paths (conditional is inside the winder/unwinder so THUNK
;; appears exactly once, preserving O(N) tree-il growth):
;;
;; 1. Fast path (PLAINVAL, no trapped writes): pure Scheme vector-set!
;;    on the descriptor's slot 4.  Fully transparent to peval.
;;
;; 2. Buffer-local path: symbol is in the current buffer's per-buffer
;;    hash table (DEFVAR_PER_BUFFER variables).  Uses hashq-ref/hashq-set!
;;    directly — pure Scheme, transparent to peval.  The hash table is
;;    captured at bind time so the unwinder restores to the correct buffer
;;    even after buffer switches in the body.
;;
;; 3. Slow path (other FORWARDED, LOCALIZED, VARALIAS, trapped): goes
;;    through C's symbol-value / set-symbol-value!.
(define (bind-symbol symbol value thunk)
  (let* ((desc (symbol-desc symbol))
         (redirect (vector-ref desc 1))
         (trapped  (vector-ref desc 2))
         (fast (and (= redirect 4)     ;; SYMBOL_PLAINVAL
                    (= trapped  0)))    ;; no trapped write
         ;; For non-fast: check if symbol lives in buffer-local hash.
         ;; buffer-local-hash returns the current buffer's hash table.
         (hash (if fast #f ((buffer-local-hash-fn))))
         (hash-val (if hash
                       (hashq-ref hash symbol *buffer-local-unset*)
                       *buffer-local-unset*))
         (buf-local? (not (eq? hash-val *buffer-local-unset*)))
         (old (cond
                (fast      (vector-ref desc 4))
                (buf-local? hash-val)
                (else      (symbol-value symbol)))))
    (dynamic-wind
      (lambda ()
        (cond
          (fast       (vector-set! desc 4 value))
          (buf-local? (hashq-set! hash symbol value))
          (else       (set-symbol-value! symbol value))))
      thunk
      (lambda ()
        (cond
          (fast       (vector-set! desc 4 old))
          (buf-local? (hashq-set! hash symbol old))
          (else       (set-symbol-value! symbol old)))))))

(define (makunbound! symbol)
  (if (module-bound? value-slot-module symbol)
      (let ((var (module-variable value-slot-module
                                  symbol)))
        (if (and (variable-bound? var) (dynamic? (variable-ref var)))
            (dynamic-unset! (variable-ref var))
            (variable-unset! var))))
    symbol)

(define (fmakunbound! symbol)
  (if (module-bound? function-slot-module symbol)
      (variable-unset! (module-variable function-slot-module symbol)))
  symbol)

(define (special? sym)
  ;; Check both the Guile-side tracking (symbol-desc vector index 3)
  ;; AND the C-level SYMBOL_DECLARED_SPECIAL flag (via special-variable-p).
  ;; C-level DEFVAR_LISP variables like throw-on-input set the C flag
  ;; but not the Guile-side flag, so we need to check both.
  (or (eqv? (vector-ref (symbol-desc sym) 3) 1)
      ;; Check C-level special-variable-p if available
      (let ((svp-fn (symbol-function 'special-variable-p)))
        (and (not (eq? svp-fn #nil))
             (not (eq? #nil (svp-fn sym)))))))

(define (proclaim-special! sym)
  (vector-set! (symbol-desc sym) 3 1)
  #nil)

(define (emacs! ref set boundp dref dset dboundp bind)
  (set! symbol-value ref)
  (set! set-symbol-value! set)
  (set! symbol-bound? boundp)
  (set! symbol-default-value dref)
  (set! set-symbol-default-value! dset)
  (set! symbol-default-bound? dboundp)
  ;; bind-symbol is now pure Scheme (uses dynamic-wind + vector-set!
  ;; for PLAINVAL, falls back to symbol-value/set-symbol-value! for
  ;; others).  Don't replace with C Fbind_symbol.
  ;; (set! bind-symbol bind)
  (set! lexical-binding? (lambda () (symbol-value 'lexical-binding)))
  (set! set-lexical-binding-mode (lambda (x) (set-symbol-value! 'lexical-binding x))))

(define (eval-elisp form)
  (let ((lang (lookup-language 'emacs-elisp)))
    (eval (compile form #:from lang #:to 'tree-il) (current-module))))

(define (compile-elisp form)
  (compile (compile form #:from 'emacs-elisp #:to 'bytecode)
           #:from 'bytecode #:to 'value))

(set-symbol-value! nil_ #nil)
(set-symbol-value! t_ #t)

(define (make-string s) s)

;;; Define a predefined macro for use in the function-slot module.

(define (make-id template-id . data)
  (let ((append-symbols
         (lambda (symbols)
           (string->symbol
            (apply string-append (map symbol->string symbols))))))
    (datum->syntax template-id
                   (append-symbols
                    (map (lambda (datum)
                           ((if (identifier? datum)
                                syntax->datum
                                identity)
                            datum))
                         data)))))

(define-syntax defspecial
  (lambda (x)
    (syntax-case x ()
      ((_ name args body ...)
       (with-syntax ((scheme-name (make-id #'name 'compile- #'name)))
         #'(begin
             (define scheme-name
               (cons 'special-operator (lambda args body ...)))
             (set-symbol-function! 'name scheme-name)))))))

(define %traceflags #f)
;(define %traceport (open-file "getrace.log" "w"))

(define (guile-tracelog-write obj)
  (when %traceflags
    ;(display str %traceport)
    ;(force-output %traceport)
    ;'(c-guile-tracelog-write (if (string? str) str (format #f "~a" str)))
    (c-guile-tracelog-writeln (object->string obj))))

(define (guile-tracelog-print obj)
  (when %traceflags
    ;(pretty-print str %traceport)
    ;(force-output %traceport)
    ;'(c-guile-tracelog-write (if (string? str) str (format #f "~a" str)))
    (c-guile-tracelog-writeln (object->string obj))))

(define (guile-tracelog-set flags)
  (c-guile-tracelog-set flags)
  (set! %traceflags flags))

(define (elisp-load-with-match-data-protection file noerror nomessage nosuffix must-suffix)
  "Load file with match data protection.
This replicates the save_match_data_load wrapper function."
  ;; Dynamically resolve elisp-load from reader module (loaded after runtime)
  ; FIX-20260117: use a module import instead:
  (let ((elisp-load (module-ref (resolve-module '(emacs reader)) 'elisp-load)))
    (elisp-load file noerror nomessage nosuffix must-suffix)))

(define (emacs-read port)
  (format #t "using emacs-read!~%")
  (read port))

;;; FIX: move to (emacs) ?
;(define (emacs-load filename)
;  (format #t "current-reader: ~s~%" (fluid-ref current-reader))
;  (fluid-set! current-reader emacs-read)
;  (compile-file
;           filename
;           #:from 'emacs-elisp
;           #:to 'value)
;  #t)
