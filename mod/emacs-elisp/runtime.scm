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
  #:use-module (emacs bindings)
  #:re-export (push-binding! pop-binding!)
  #:export (nil-value
            t-value
            catch-all
            elisp-handler-bind
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
            get-inline-source
            buffer-local-hash-fn
            buffer-local-ref
            buffer-local-set!
            symbol-simple-forward-p
            prepare-complex-binding
            do-complex-bind
            do-complex-unbind
            pop-and-restore-value)
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

;; catch-all: like Guile's catch with #t, but handler receives (key args-list)
;; instead of (key arg1 arg2 ...). This makes it easier to use from elisp
;; where we can't easily use rest parameters in handlers.
(define (catch-all thunk handler)
  (catch #t
    thunk
    (lambda args
      (handler (car args) (cdr args)))))

;; elisp-handler-bind: implements handler-bind semantics using Guile's
;; with-throw-handler.  Handlers run within the dynamic extent of
;; the error (before unwinding).  If a handler returns normally, the
;; exception continues propagating to outer handlers.
;;
;; bodyfun: thunk to execute
;; conditions-handlers: flat list (conditions1 handler1 conditions2 handler2 ...)
;;   where conditions is a list of condition symbols
;;   and handler is a procedure taking (error-symbol . error-data)
(define (elisp-handler-bind bodyfun conditions-handlers)
  ;; Helper to check if error-symbol matches conditions list
  (define (error-matches? error-symbol conditions)
    (let ((error-conditions (get-error-conditions error-symbol)))
      (if (null? conditions)
          #f
          (let loop ((conds conditions))
            (cond
             ((null? conds) #f)
             ((memq (car conds) error-conditions) #t)
             (else (loop (cdr conds))))))))

  ;; Get error-conditions property from symbol plist
  (define (get-error-conditions sym)
    (let ((plist (symbol-plist sym)))
      (let loop ((pl plist))
        (cond
         ((null? pl) '())
         ((eq? (car pl) 'error-conditions) (cadr pl))
         (else (loop (cddr pl)))))))

  ;; Build nested handlers from inside out
  ;; Each with-throw-handler wraps the next
  (let loop ((pairs conditions-handlers))
    (if (or (null? pairs) (not (pair? pairs)))
        ;; No more handlers, run the body
        (bodyfun)
        ;; Install handler for this conditions/handler pair
        (let ((conditions (car pairs))
              (handler (cadr pairs))
              (rest (if (> (length pairs) 2) (cddr pairs) '())))
          ;; Use with-throw-handler to run handler in dynamic context
          ;; If handler returns normally, exception continues propagating
          (with-throw-handler 'elisp-condition
            (lambda ()
              ;; Recurse to install remaining handlers, then run body
              (loop rest))
            (lambda (key error-symbol error-data)
              ;; Check if error matches this handler's conditions
              (when (error-matches? error-symbol conditions)
                ;; Matches - call handler with (error-symbol . error-data)
                ;; If handler returns, with-throw-handler re-raises
                (handler (cons error-symbol error-data)))))))))

(define lisp-string? string?)

(define %lisp-string
  (lambda (str)
    ((module-ref (resolve-module '(emacs-elisp runtime)) 'lisp-string?) str)))
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

;; make-symbol returns a true uninterned symbol (vanilla elisp contract).
;; (symbol-name (make-symbol "x")) MUST return "x" — user code such as
;; json-serialize relies on it.  Uninterned symbols that survive into
;; compiled output are caught by sanitize-uninterned-symbols in the
;; tree-il compiler.
(define (make-symbol name)
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

;; Lazily-cached handle for the C `set-default' DEFUN.
;; Used by bind-symbol's unwind path when a PLAINVAL variable was
;; changed to LOCALIZED (via make-local-variable) during the body,
;; and for the let-default path (SPECPDL_LET_DEFAULT equivalent).
(define %set-default-fn #f)
(define (set-default-fn)
  (or %set-default-fn
      (let ((fn (symbol-function 'set-default)))
        (set! %set-default-fn fn)
        fn)))

;; Lazily-cached handles for local-variable-p and default-value.
;; Used by bind-symbol to distinguish "has local value" from
;; "in hash but no local value" (SPECPDL_LET_DEFAULT path).
(define %local-variable-p-fn #f)
(define (local-variable-p sym)
  (let ((fn (or %local-variable-p-fn
                (let ((f (symbol-function 'local-variable-p)))
                  (set! %local-variable-p-fn f)
                  f))))
    (not (eq? #nil (fn sym)))))

(define %default-value-fn #f)
(define (default-value sym)
  (let ((fn (or %default-value-fn
                (let ((f (symbol-function 'default-value)))
                  (set! %default-value-fn f)
                  f))))
    (fn sym)))

;; Lazily-cached handle for local-variable-if-set-p.
;; Returns #t for variables that are automatically buffer-local
;; (via make-variable-buffer-local), even if no local value exists yet.
(define %local-variable-if-set-p-fn #f)
(define (local-variable-if-set-p sym)
  (let ((fn (or %local-variable-if-set-p-fn
                (let ((f (symbol-function 'local-variable-if-set-p)))
                  (set! %local-variable-if-set-p-fn f)
                  f))))
    (not (eq? #nil (fn sym)))))

;; Lazily-cached handle for symbol-simple-forward-p.
;; Returns #t for "simple" FORWARDED variables (DEFVAR_INT, DEFVAR_BOOL,
;; DEFVAR_LISP) that don't depend on buffer/kboard context.
;; Returns #f for buffer-local forwards, kboard forwards, and non-forwarded.
(define %symbol-simple-forward-p-fn #f)
(define (symbol-simple-forward-p sym)
  (let ((fn (or %symbol-simple-forward-p-fn
                (let ((f (symbol-function 'symbol-simple-forward-p)))
                  (set! %symbol-simple-forward-p-fn f)
                  f))))
    (not (eq? #nil (fn sym)))))

;; Phase 5: Scheme accessors for per-buffer hash table.
;; Available to all Scheme code (mod/emacs/buffer-locals.scm etc.).
(define (buffer-local-ref buf sym)
  "Read SYM's value in BUF's per-buffer hash table."
  (hashq-ref ((buffer-local-hash-fn) buf) sym))

(define (buffer-local-set! buf sym val)
  "Set SYM's value in BUF's per-buffer hash table."
  (hashq-set! ((buffer-local-hash-fn) buf) sym val))

;; True if SYMBOL is a C per-buffer slot variable (DEFVAR_PER_BUFFER,
;; i.e. SYMBOL_FORWARDED with a BUFFER_OBJFWD forward).  These have a C
;; slot mirror in struct buffer that `populate_buffer_local_hash'
;; re-reads after `kill-all-local-variables', so let-bindings must keep
;; that mirror in sync (see buffer-local-let-set!).  Note this also
;; matches kboard forwards (redirect 3, non-simple); harmless, since
;; only DEFVAR_PER_BUFFER slots land in the per-buffer hash.
(define (per-buffer-forwarded? sym)
  (and (= (vector-ref (symbol-desc sym) 1) 3)  ; SYMBOL_FORWARDED
       (not (symbol-simple-forward-p sym))))

;; Lazily-cached handle for buffer-live-p.
(define %buffer-live-p-fn #f)
(define (buffer-live-p buf)
  (let ((fn (or %buffer-live-p-fn
                (let ((f (symbol-function 'buffer-live-p)))
                  (set! %buffer-live-p-fn f)
                  f))))
    (not (eq? #nil (fn buf)))))

;; Lazily-cached handle for current-buffer.
(define %current-buffer-fn #f)
(define (current-buffer-fn)
  (or %current-buffer-fn
      (let ((f (symbol-function 'current-buffer)))
        (set! %current-buffer-fn f)
        f)))

(define (buffer-local-let-set! hash buffer symbol value)
  "Write a let-bound buffer-local value, keeping both stores consistent.
HASH is the bind-time buffer's per-buffer hash; BUFFER the bind-time
buffer; SYMBOL the variable being bound.

For C per-buffer slot variables (DEFVAR_PER_BUFFER, e.g.
`default-directory'), write through the C `set' path so the C slot
mirror is updated too: `kill-all-local-variables' re-populates the
per-buffer hash from those C slots (populate_buffer_local_hash), and
vanilla's reset_buffer_local_variables skips idx == -1 slots such as
default-directory, so the let-bound value must live in the slot to
survive a kill-all-local-variables in the body.  (`set-symbol-value!'
reaches C `set' after emacs! replaces the pure-Scheme version.)

If the bind-time buffer was killed inside the body, skip the C slot
write and fall back to the hash only (mirroring vanilla's
\"If restoring in a dead buffer, do nothing\"; the old hashq-set!
path was immune to killed buffers).

For hash-only locals (make-local-variable), the hash is the store."
  (if (and (per-buffer-forwarded? symbol)
           (buffer-live-p buffer))
      (let* ((set-buffer-fn (symbol-function 'set-buffer))
             (save ((current-buffer-fn))))
        (set-buffer-fn buffer)
        (set-symbol-value! symbol value)
        (set-buffer-fn save))
      (hashq-set! hash symbol value)))

;; bind-symbol: dynamically bind SYMBOL to VALUE during THUNK.
;;
;; Four paths (conditional is inside the winder/unwinder so THUNK
;; appears exactly once, preserving O(N) tree-il growth):
;;
;; 1. Fast path (PLAINVAL, no trapped writes): pure Scheme vector-set!
;;    on the descriptor's slot 4.  Fully transparent to peval.
;;
;; 2. Buffer-local path: symbol has an actual local value in the
;;    current buffer (local-variable-p is true).  Uses hashq-ref/hashq-set!
;;    directly — pure Scheme, transparent to peval.  The hash table is
;;    captured at bind time so the unwinder restores to the correct buffer
;;    even after buffer switches in the body.
;;
;; 3. Default-value path: symbol is buffer-local-capable but has NO
;;    local value in this buffer (either a DEFVAR_PER_BUFFER in the hash,
;;    or a LOCALIZED/FORWARDED variable made buffer-local via
;;    make-variable-buffer-local).  Like C's SPECPDL_LET_DEFAULT, we
;;    save/restore the default value via set-default, so that
;;    kill-all-local-variables inside the body doesn't lose the
;;    let-bound value.
;;
;; 4. Slow path (other FORWARDED, LOCALIZED, VARALIAS, trapped): goes
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
         (in-hash? (not (eq? hash-val *buffer-local-unset*)))
         ;; Check whether the variable has an actual local value.
         ;; If it's buffer-local-capable but has no local, we use
         ;; the default-value path (SPECPDL_LET_DEFAULT).
         (has-local? (and (not fast) (local-variable-p symbol)))
         (buf-local? (and in-hash? has-local?))
         ;; let-default?: buffer-local-capable but no local value.
         ;; Covers both DEFVAR_PER_BUFFER (in-hash, no local) and
         ;; make-variable-buffer-local'd LOCALIZED vars (not in hash,
         ;; but local-variable-if-set-p is true, no local value).
         (let-default? (and (not fast)
                            (not buf-local?)
                            (not has-local?)
                            (local-variable-if-set-p symbol)))
         ;; Bind-time buffer: needed to keep the C slot mirror in sync
         ;; for DEFVAR_PER_BUFFER variables (see buffer-local-let-set!).
         (buf (and (not fast) ((current-buffer-fn))))
         (old (cond
                (fast         (vector-ref desc 4))
                (buf-local?   hash-val)
                (let-default? (default-value symbol))
                (else         (symbol-value symbol))))
         ;; Determine binding kind for specpdl tracking:
         ;; 0 = LET, 1 = LET_LOCAL, 2 = LET_DEFAULT
         (kind (cond (buf-local?   1)
                     (let-default? 2)
                     (else         0))))
    (dynamic-wind
      (lambda ()
        ;; Track in Scheme binding registry (Phase 4: C specpdl removed)
        (push-binding! symbol old kind #f)
        (cond
          (fast         (vector-set! desc 4 value))
          (buf-local?   (buffer-local-let-set! hash buf symbol value))
          (let-default? ((set-default-fn) symbol value))
          (else         (set-symbol-value! symbol value))))
      thunk
      (lambda ()
        ;; Pop binding and get the old value from registry (Phase 4: C specpdl removed).
        ;; This allows set-default-toplevel-value to modify the old value
        ;; that will be restored on unbind (for interpreted code).
        ;; Note: compiled code uses inline dynamic-wind with captured old values,
        ;; so set-default-toplevel-value won't affect compiled code paths.
        (let* ((entry (pop-binding!))
               (restore-val (if entry (vector-ref entry 1) old)))
          (cond
            ;; Fast path: re-check that the variable is still PLAINVAL +
            ;; untrapped.  If make-local-variable was called during the
            ;; body, the redirect changed to LOCALIZED and slot 4 is now
            ;; a BLV pointer — we must NOT overwrite it.  Instead, restore
            ;; the default value via set-default (mirroring C's
            ;; do_one_unbind fallthrough to set_default_internal).
            ((and fast
                  (= (vector-ref desc 1) 4)    ;; still SYMBOL_PLAINVAL
                  (= (vector-ref desc 2) 0))   ;; still no trapped write
             (vector-set! desc 4 restore-val))
            (fast
             ;; Was PLAINVAL at bind-time but changed since.
             ((set-default-fn) symbol restore-val))
            (buf-local?   (buffer-local-let-set! hash buf symbol restore-val))
            (let-default? ((set-default-fn) symbol restore-val))
            (else         (set-symbol-value! symbol restore-val))))))))

;; Helper functions for inline dynamic-wind on complex bindings.
;; These allow make-dynlet-one to emit dynamic-wind directly, making the
;; body transparent to peval while encapsulating binding complexity here.
;;
;; Context vector layout:
;; [0] old-value
;; [1] binding-kind (0=LET, 1=LET_LOCAL, 2=LET_DEFAULT)
;; [2] hash table (buffer's hash, or #f)
;; [3] symbol
;; [4] buf-local? flag
;; [5] let-default? flag
;; [6] bind-time buffer (for C slot mirror sync, see buffer-local-let-set!)

(define (prepare-complex-binding symbol)
  "Prepare for binding a complex (buffer-local, kboard, etc.) variable.
Returns a context vector with all information needed to bind/unbind.
Called before dynamic-wind; captures current buffer's hash table."
  (let* ((hash ((buffer-local-hash-fn)))
         (hash-val (hashq-ref hash symbol *buffer-local-unset*))
         (in-hash? (not (eq? hash-val *buffer-local-unset*)))
         (has-local? (local-variable-p symbol))
         (buf-local? (and in-hash? has-local?))
         (let-default? (and (not buf-local?)
                            (not has-local?)
                            (local-variable-if-set-p symbol)))
         (old (cond
                (buf-local?   hash-val)
                (let-default? (default-value symbol))
                (else         (symbol-value symbol))))
         (kind (cond (buf-local?   1)
                     (let-default? 2)
                     (else         0))))
    (vector old kind hash symbol buf-local? let-default?
            ((current-buffer-fn)))))

(define (do-complex-bind ctx value)
  "Set new value using context from prepare-complex-binding.
Called as dynamic-wind winder."
  (let ((symbol (vector-ref ctx 3))
        (buf-local? (vector-ref ctx 4))
        (let-default? (vector-ref ctx 5))
        (hash (vector-ref ctx 2))
        (buf (vector-ref ctx 6))
        (old (vector-ref ctx 0))
        (kind (vector-ref ctx 1)))
    ;; Track in Scheme binding registry (Phase 4: C specpdl removed)
    (push-binding! symbol old kind #f)
    ;; Set new value via appropriate path
    (cond
      (buf-local?   (buffer-local-let-set! hash buf symbol value))
      (let-default? ((set-default-fn) symbol value))
      (else         (set-symbol-value! symbol value)))))

(define (do-complex-unbind ctx)
  "Restore old value using context from prepare-complex-binding.
Called as dynamic-wind unwinder."
  (let ((symbol (vector-ref ctx 3))
        (buf-local? (vector-ref ctx 4))
        (let-default? (vector-ref ctx 5))
        (hash (vector-ref ctx 2))
        (buf (vector-ref ctx 6))
        (ctx-old (vector-ref ctx 0)))
    ;; Pop binding and get the old value from registry (Phase 4: C specpdl removed).
    ;; This allows set-default-toplevel-value to modify the old value
    ;; that will be restored on unbind.
    (let* ((entry (pop-binding!))
           (restore-val (if entry (vector-ref entry 1) ctx-old)))
      ;; Restore old value via appropriate path
      (cond
        (buf-local?   (buffer-local-let-set! hash buf symbol restore-val))
        (let-default? ((set-default-fn) symbol restore-val))
        (else         (set-symbol-value! symbol restore-val))))))

(define (pop-and-restore-value fallback)
  "Pop binding from registry and return the old-value to restore.
Uses FALLBACK if the binding stack is empty.  This allows
set-default-toplevel-value to modify the value that will be restored
when a let binding exits."
  (let ((entry (pop-binding!)))
    (if entry
        (vector-ref entry 1)
        fallback)))

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
