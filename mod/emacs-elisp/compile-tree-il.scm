;; Copyright (C) Free Software Foundation, Inc.
;; SPDX-License-Identifier: GPL-3.0-or-later

(define-module (emacs-elisp compile-tree-il)
  #:use-module (emacs-elisp bindings)
  #:use-module (emacs-elisp runtime)
  #:use-module (language tree-il)
  #:use-module (system base pmatch)
  #:use-module (system base compile)
  #:use-module (system base target)
  #:use-module (srfi srfi-1)
  #:use-module (srfi srfi-8)
  #:use-module (srfi srfi-11)
  #:use-module (srfi srfi-26)
  #:use-module (ice-9 format)
  #:use-module (ice-9 pretty-print)
  #:export (compile-tree-il
            compile-progn
            compile-eval-when-compile
            compile-if
            compile-defconst
            compile-defvar
            compile-setq
            compile-let
            compile-flet
            compile-labels
            compile-let*
            compile-guile-ref
            compile-guile-private-ref
            compile-guile-primitive
            compile-%function
            compile-function
            compile-defmacro
            compile-defun
            #{compile-`}#
            compile-quote
            compile-%funcall
            compile-%set-lexical-binding-mode))

;; Override Guile's gensym to create interned symbols (avoids .go serialization errors)
(define gensym
  (let ((counter 0))
    (lambda args
      (set! counter (+ counter 1))
      (string->symbol (string-append
                       (if (null? args) "g" (car args))
                       (number->string counter))))))

;;; Certain common parameters (like the bindings data structure or
;;; compiler options) are not always passed around but accessed using
;;; fluids to simulate dynamic binding (hey, this is about elisp).

;;; The bindings data structure to keep track of symbol binding related
;;; data.

(define bindings-data (make-fluid))

;;; Find the source properties of some parsed expression if there are
;;; any associated with it.

(define (location x)
  (and (pair? x)
       (let ((props (source-properties x)))
         (and (not (null? props))
              props))))

;;; Values to use for Elisp's nil and t.

(define (nil-value loc)
  (make-const loc (@ (emacs-elisp runtime) nil-value)))

(define (t-value loc)
  (make-const loc (@ (emacs-elisp runtime) t-value)))

;;; Modules that contain the value and function slot bindings.

(define runtime '(emacs-elisp runtime))

(define value-slot (@ (emacs-elisp runtime) value-slot-module))

(define function-slot (@ (emacs-elisp runtime) function-slot-module))

;;; The backquoting works the same as quasiquotes in Scheme, but the
;;; forms are named differently; to make easy adaptions, we define these
;;; predicates checking for a symbol being the car of an
;;; unquote/unquote-splicing/backquote form.

(define (unquote? sym)
  (and (symbol? sym) (eq? sym '#{,}#)))

(define (unquote-splicing? sym)
  (and (symbol? sym) (eq? sym '#{,@}#)))

;;; Build a call to a primitive procedure nicely.

(define (call-primitive loc sym . args)
  (make-primcall loc sym args))

;;; Error reporting routine for syntax/compilation problems or build
;;; code for a runtime-error output.

(define (report-error loc . args)
  (apply error args))

(define (access-variable loc symbol handle-lexical handle-dynamic)
  (cond
   ((get-lexical-binding (fluid-ref bindings-data) symbol)
    => handle-lexical)
   (else
    (handle-dynamic))))

(define (reference-variable loc symbol)
  (access-variable
   loc
   symbol
   (lambda (lexical)
     (if (symbol? lexical)
         (make-lexical-ref loc symbol lexical)
         (make-call loc lexical '())))
   (lambda ()
     (make-call loc
                (make-module-ref loc runtime 'symbol-value #t)
                (list (make-const loc symbol))))))

(define (global? symbol)
  (module-variable value-slot symbol))

(define (ensure-globals! loc names body)
  (if (and (every global? names)
           (every symbol-interned? names))
      body
      (list->seq
       loc
       `(,@(map
            (lambda (name)
              (symbol-desc name)
              (make-call loc
                         (make-module-ref loc runtime 'symbol-desc #t)
                         (list (make-const loc name))))
            names)
         ,body))))

(define (set-variable! loc symbol value)
  (access-variable
   loc
   symbol
   (lambda (lexical)
     (if (symbol? lexical)
         (make-lexical-set loc symbol lexical value)
         (make-call loc lexical (list value))))
   (lambda ()
     (ensure-globals!
      loc
      (list symbol)
      (make-call loc
                 (make-module-ref loc runtime 'set-symbol-value! #t)
                 (list (make-const loc symbol)
                       value))))))

(define (access-function loc symbol handle-lexical handle-global)
  (cond
   ((get-function-binding (fluid-ref bindings-data) symbol)
    => handle-lexical)
   (else
    (handle-global))))

(define (reference-function loc symbol)
  (access-function
   loc
   symbol
   (lambda (gensym) (make-lexical-ref loc symbol gensym))
   (lambda ()
     ;; Direct module ref into (elisp-functions) — avoids symbol-function call overhead
     (make-module-ref loc '(elisp-functions) symbol #t))))

(define (set-function! loc symbol value)
  (access-function
   loc
   symbol
   (lambda (gensym) (make-lexical-set loc symbol gensym value))
   (lambda ()
     (make-call
      loc
      (make-module-ref loc runtime 'set-symbol-function! #t)
      (list (make-const loc symbol) value)))))

(define (bind-lexically? sym decls)
  (let ((decl (assq-ref decls sym)))
    (or (eq? decl 'lexical)
        (and
         (lexical-binding?)
         (not (special? sym))))))

(define (parse-let-binding loc binding)
  (pmatch binding
    ((unquote var)
     (guard (symbol? var))
     (let ((var* (if ((@ (guile) symbol-interned?) var) var (gensym (symbol->string var)))))
       (cons var* #nil)))
    ((,var)
     (guard (symbol? var))
     (let ((var* (if ((@ (guile) symbol-interned?) var) var (gensym (symbol->string var)))))
       (cons var* #nil)))
    ((,var ,val)
     (guard (symbol? var))
     (let ((var* (if ((@ (guile) symbol-interned?) var) var (gensym (symbol->string var)))))
       (cons var* val)))
    (else
     (report-error loc "malformed variable binding" binding))))

(define (parse-flet-binding loc binding)
  (pmatch binding
    ((,var ,args . ,body)
     (guard (symbol? var))
     (cons var `(function (lambda ,args ,@body))))
    (else
     (report-error loc "malformed function binding" binding))))

(define (parse-declaration expr)
  (pmatch expr
    ((lexical . ,vars)
     (map (cut cons <> 'lexical) vars))
    (else
     '())))

(define (parse-body-1 body lambda?)
  (let loop ((lst body)
             (decls '())
             (intspec #f)
             (doc #f))
    (pmatch lst
      (((declare . ,x) . ,tail)
       (loop tail (append-reverse x decls) intspec doc))
      (((interactive) . ,tail)
       (guard lambda? (not intspec))
       (loop tail decls (cons 'interactive-form #nil) doc))
      (((interactive ,x) . ,tail)
       (guard lambda? (not intspec))
       (loop tail decls (cons 'interactive-form x) doc))
      ((,x . ,tail)
       (guard lambda? (or (string? x) (%lisp-string x)) (not doc) (not (null? tail)))
       (loop tail decls intspec x))
      (else
       (values (append-map parse-declaration decls)
               intspec
               doc
               lst)))))

(define (parse-lambda-body body)
  (parse-body-1 body #t))

(define (parse-body body)
  (receive (decls intspec doc body) (parse-body-1 body #f)
    (values decls body)))

;;; Partition the argument list of a lambda expression into required,
;;; optional and rest arguments.

(define (parse-lambda-list lst)
  (define (%match lst null optional rest symbol list*)
    (pmatch lst
      (() (null))
      (nil (null))
      ((&optional . ,tail) (optional tail))
      ((&rest . ,tail) (rest tail))
      ((,arg . ,tail) (guard (symbol? arg)) (symbol arg tail))
      ((,arg . ,tail) (guard (list? arg)) (list* arg tail))
      (else (fail))))
  (define (return rreq ropt rest)
    (values #t (reverse rreq) (reverse ropt) rest))
  (define (fail)
    (values #f #f #f #f))
  (define (parse-req lst rreq)
    (%match lst
            (lambda () (return rreq '() #f))
            (lambda (tail) (parse-opt tail rreq '()))
            (lambda (tail) (parse-rest tail rreq '()))
            (lambda (arg tail) (parse-req tail (cons arg rreq)))
            (lambda (arg tail) (fail))))
  (define (parse-opt lst rreq ropt)
    (%match lst
            (lambda () (return rreq ropt #f))
            (lambda (tail) (fail))
            (lambda (tail) (parse-rest tail rreq ropt))
            (lambda (arg tail) (parse-opt tail rreq (cons (list arg) ropt)))
            (lambda (arg tail) (parse-opt tail rreq (cons arg ropt)))))
  (define (parse-rest lst rreq ropt)
    (%match lst
            (lambda () (fail))
            (lambda (tail) (fail))
            (lambda (tail) (fail))
            (lambda (arg tail) (parse-post-rest tail rreq ropt arg))
            (lambda (arg tail) (fail))))
  (define (parse-post-rest lst rreq ropt rest)
    (%match lst
            (lambda () (return rreq ropt rest))
            (lambda () (fail))
            (lambda () (fail))
            (lambda (arg tail) (fail))
            (lambda (arg tail) (fail))))
  (parse-req lst '()))

(define (make-simple-lambda loc meta req opt init rest vars body)
  (make-lambda loc
               meta
               (make-lambda-case #f req opt rest #f init vars body #f)))

(define (make-dynlet src fluids vals body)
  (let ((f (map (lambda (x) (gensym "fluid ")) fluids))
        (v (map (lambda (x) (gensym "valud ")) vals)))
    (make-let src (map (lambda (_) 'fluid) fluids) f fluids
              (make-let src (map (lambda (_) 'val) vals) v vals
                        (let lp ((f f) (v v))
                          (if (null? f)
                              body
                              (make-call src
                                         (make-module-ref src runtime 'bind-symbol #t)
                                         (list (make-lexical-ref #f 'fluid (car f))
                                               (make-lexical-ref #f 'val (car v))
                                               (make-lambda
                                                src '()
                                                (make-lambda-case
                                                 src '() #f #f #f '() '()
                                                 (lp (cdr f) (cdr v))
                                                 #f))))))))))

(define (sanitize-uninterned-symbols expr replacements)
  "Recursively replace uninterned symbols with interned equivalents.
REPLACEMENTS is an alist mapping uninterned symbols to their interned versions."
  (cond
   ((symbol? expr)
    (let ((replacement (assq expr replacements)))
      (if replacement
          (cdr replacement)
          expr)))
   ((pair? expr)
    (cons (sanitize-uninterned-symbols (car expr) replacements)
          (sanitize-uninterned-symbols (cdr expr) replacements)))
   (else expr)))

(define (find-uninterned-symbols expr)
  "Find all uninterned symbols in an expression and create interned replacements."
  (let ((uninterned '()))
    (let walk ((e expr))
      (cond
       ((symbol? e)
        (when (and (not ((@ (guile) symbol-interned?) e))
                   (not (assq e uninterned)))
          (set! uninterned (cons (cons e (string->symbol (symbol->string e)))
                                uninterned))))
       ((pair? e)
        (walk (car e))
        (walk (cdr e)))))
    uninterned))

(define (compile-lambda loc meta args body)
  ;; Find and replace all uninterned symbols in the lambda expression
  ;; This is needed because Guile can't serialize uninterned symbols to .go files
  (let* ((full-expr (cons args body))
         (replacements (find-uninterned-symbols full-expr))
         (sanitized (if (null? replacements)
                        full-expr
                        (sanitize-uninterned-symbols full-expr replacements)))
         (sanitized-args (car sanitized))
         (sanitized-body (cdr sanitized)))
    (receive (valid? req-ids opts rest-id)
             (parse-lambda-list sanitized-args)
      (if valid?
        (let* ((all-ids (append req-ids
                                (and opts (map car opts))
                                (or (and=> rest-id list) '())))
               (all-vars (map (lambda (ignore) (gensym)) all-ids)))
          (let*-values (((decls intspec doc forms)
                         (parse-lambda-body sanitized-body))
                        ((lexical dynamic)
                         (partition
                          (compose (cut bind-lexically? <> decls)
                                   car)
                          (map list all-ids all-vars)))
                        ((lexical-ids lexical-vars) (unzip2 lexical))
                        ((dynamic-ids dynamic-vars) (unzip2 dynamic)))
            (with-dynamic-bindings
             (fluid-ref bindings-data)
             dynamic-ids
             (lambda ()
               (with-lexical-bindings
                (fluid-ref bindings-data)
                lexical-ids
                lexical-vars
                (lambda ()
                  (ensure-globals!
                   loc
                   dynamic-ids
                   (let* ((tree-il
                           (compile-expr
                            (if rest-id
                                `(let ((,rest-id (if ,rest-id
                                                     ,rest-id
                                                     nil)))
                                   ,@forms)
                                `(progn ,@forms))))
                          (full-body
                           (if (null? dynamic)
                               tree-il
                               (make-dynlet
                                loc
                                (map (cut make-const loc <>) dynamic-ids)
                                (map (cut make-lexical-ref loc <> <>)
                                     dynamic-ids
                                     dynamic-vars)
                                tree-il))))
                     (make-simple-lambda loc
                                         (append (if intspec
                                                     (list intspec)
                                                     '())
                                                 (if doc
                                                     (list (cons 'emacs-documentation doc))
                                                     '())
                                                 meta)
                                         req-ids
                                         (if (null? opts) #f (map car opts))
                                         (map (lambda (x)
                                                (if (pair? (cdr x))
                                                    (compile-expr (car (cdr x)))
                                                    (make-const loc #nil)))
                                              opts)
                                         rest-id
                                         all-vars
                                         full-body)))))))))
        (report-error "invalid function" `(lambda ,sanitized-args ,@sanitized-body))))))

;;; Handle macro and special operator bindings.

(define (find-operator name type)
  (and
   (symbol? name)
   (module-defined? function-slot name)
   (let ((op (module-ref function-slot name)))
     (if (and (pair? op) (eq? (car op) type))
         (cdr op)
         #f))))

(define (contains-unquotes? expr)
  (if (pair? expr)
      (if (or (unquote? (car expr)) (unquote-splicing? (car expr)))
          #t
          (or (contains-unquotes? (car expr))
              (contains-unquotes? (cdr expr))))
      #f))

;;; Process a backquoted expression by building up the needed
;;; cons/append calls.  For splicing, it is assumed that the expression
;;; spliced in evaluates to a list.  The emacs manual does not really
;;; state either it has to or what to do if it does not, but Scheme
;;; explicitly forbids it and this seems reasonable also for elisp.

(define (unquote-cell? expr)
  (and (list? expr) (= (length expr) 2) (unquote? (car expr))))

(define (unquote-splicing-cell? expr)
  (and (list? expr) (= (length expr) 2) (unquote-splicing? (car expr))))

;; Helper function to replace uninterned symbols in expressions
(define (replace-uninterned-symbols expr)
  (cond
   ((symbol? expr)
    (let ((interned? ((@ (guile) symbol-interned?) expr)))
      (if interned?
          expr  ; Keep interned symbols
          (string->symbol (symbol->string expr)))))  ; Convert to interned symbol
   ((pair? expr)
    ;; Recursively process pairs
    (cons (replace-uninterned-symbols (car expr))
          (replace-uninterned-symbols (cdr expr))))
   (else
    ;; Leave other types unchanged
    expr)))

(define (process-backquote loc expr)
  (if (contains-unquotes? expr)
      (if (pair? expr)
          (if (or (unquote-cell? expr) (unquote-splicing-cell? expr))
              (compile-expr (cadr expr))
              (let* ((head (car expr))
                     (processed-tail (process-backquote loc (cdr expr)))
                     (head-is-list-2 (and (list? head)
                                          (= (length head) 2)))
                     (head-unquote (and head-is-list-2
                                        (unquote? (car head))))
                     (head-unquote-splicing (and head-is-list-2
                                                 (unquote-splicing?
                                                  (car head)))))
                (if head-unquote-splicing
                    (call-primitive loc
                                    'append
                                    (compile-expr (cadr head))
                                    processed-tail)
                    (call-primitive loc 'cons
                                    (if head-unquote
                                        (compile-expr (cadr head))
                                        (process-backquote loc head))
                                    processed-tail))))
          (report-error loc
                        "non-pair expression contains unquotes"
                        expr))
      ;; Replace uninterned symbols before making constants
      (make-const loc (replace-uninterned-symbols expr))))

;;; Special operators

(defspecial progn (loc args)
  (list->seq loc
             (if (null? args)
                 (list (nil-value loc))
                 ; NOTE: map = map-in-order is too ingrained in usage, to consider this a user-side bug, but rather a scheme-spec-bug
                 (map compile-expr-1 args))))

(defspecial eval-when-compile (loc args)
  (make-const loc (with-native-target
                   (lambda ()
                     (eval-elisp `(progn ,@args))))))

(define toplevel? (make-fluid))

(define compile-time-too? (make-fluid))

(defspecial eval-when (loc args)
  (pmatch args
    ((,situations . ,forms)
     (let ((compile? (or (memq ':compile-toplevel situations)
                         (memq 'compile situations)))
           (load? (or (memq ':load-toplevel situations)
                      (memq 'load situations)))
           (execute? (or (memq ':execute situations)
                         (memq 'eval situations))))
       (cond
        ((not (fluid-ref toplevel?))
         (if execute?
             (compile-expr `(progn ,@forms))
             (make-const loc #nil)))
        (load?
         (with-fluids ((compile-time-too?
                        (cond (compile? #t)
                              (execute? (fluid-ref compile-time-too?))
                              (else #f))))
           (when (fluid-ref compile-time-too?)
             (eval-elisp `(progn ,@forms)))
           (compile-expr-1 `(progn ,@forms))))
        ((or compile? (and execute? (fluid-ref compile-time-too?)))
         (eval-elisp `(progn ,@forms))
         (make-const loc #nil))
        (else
         (make-const loc #nil)))))))

(defspecial if (loc args)
  (pmatch args
    ((,cond ,then . ,else)
     (make-conditional
      loc
      (call-primitive loc 'not
       (call-primitive loc 'nil? (compile-expr cond)))
      (compile-expr then)
      (compile-expr `(progn ,@else))))
    (else (report-error loc "Bad if" args))))

(defspecial defconst (loc args)
  (pmatch args
    ((,sym ,value . ,doc)
     (proclaim-special! sym)
     (make-seq
      loc
      (make-call loc
                 (make-module-ref loc runtime 'proclaim-special! #t)
                 (list (make-const loc sym)))
      (make-seq loc
                (set-variable! loc sym (compile-expr value))
                (make-const loc sym))))
    (else (report-error loc "Bad defconst" args))))

(defspecial defvar (loc args)
  (pmatch args
    ((,sym)
     (proclaim-special! sym)
     (make-seq loc
               (make-call loc
                          (make-module-ref loc runtime 'proclaim-special! #t)
                          (list (make-const loc sym)))
               (make-const loc sym)))
    ((,sym ,value . ,doc)
     (proclaim-special! sym)
     (make-seq
      loc
      (make-call loc
                 (make-module-ref loc runtime 'proclaim-special! #t)
                 (list (make-const loc sym)))
      (make-seq
       loc
       (make-conditional
        loc
        (make-call loc
                   (make-module-ref loc runtime 'symbol-default-bound? #t)
                   (list (make-const loc sym)))
        (make-void loc)
        (make-call loc
                   (make-module-ref loc runtime 'set-symbol-default-value! #t)
                   (list (make-const loc sym)
                         (compile-expr value))))
       (make-const loc sym))))
    (else (report-error loc "Bad defvar" args))))

(defspecial setq (loc args)
  (define (car* x) (if (null? x) '() (car x)))
  (define (cdr* x) (if (null? x) '() (cdr x)))
  (define (cadr* x) (car* (cdr* x)))
  (define (cddr* x) (cdr* (cdr* x)))
  (list->seq
   loc
   (let loop ((args args) (last (nil-value loc)))
     (if (null? args)
         (list last)
         (let ((sym (car args))
               (val (compile-expr (cadr* args))))
           (if (not (symbol? sym))
               (report-error loc "expected symbol in setq" args)
               (cons
                (set-variable! loc sym val)
                (loop (cddr* args)
                      (reference-variable loc sym)))))))))

(defspecial let (loc args)
  (pmatch args
    ((,varlist . ,body)
     (let ((bindings (map (cut parse-let-binding loc <>) varlist)))
       (receive (decls forms) (parse-body body)
         (receive (lexical dynamic)
                  (partition
                   (compose (cut bind-lexically? <> decls)
                            car)
                   bindings)
           (let ((make-values (lambda (for)
                                (map (lambda (el) (compile-expr (cdr el)))
                                     for)))
                 (make-body (lambda () (compile-expr `(progn ,@forms)))))
             (ensure-globals!
              loc
              (map car dynamic)
              (if (null? lexical)
                  (if (null? dynamic)
                      (make-body)
                      (make-dynlet loc
                                   (map (compose (cut make-const loc <>) car)
                                        dynamic)
                                   (map (compose compile-expr cdr)
                                        dynamic)
                                   (make-body)))
                  (let* ((lexical-syms (map (lambda (el) (gensym)) lexical))
                         (dynamic-syms (map (lambda (el) (gensym)) dynamic))
                         (all-syms (append lexical-syms dynamic-syms))
                         (vals (append (make-values lexical)
                                       (make-values dynamic))))
                    (make-let loc
                              all-syms
                              all-syms
                              vals
                              (with-lexical-bindings
                               (fluid-ref bindings-data)
                               (map car lexical)
                               lexical-syms
                               (lambda ()
                                 (if (null? dynamic)
                                     (make-body)
                                     (make-dynlet loc
                                                  (map
                                                   (compose (cut make-const
                                                                 loc
                                                                 <>)
                                                            car)
                                                   dynamic)
                                                  (map
                                                   (lambda (sym)
                                                     (make-lexical-ref
                                                      loc
                                                      sym
                                                      sym))
                                                   dynamic-syms)
                                                  (make-body))))))))))))))
    (else (report-error loc "bad let args"))))

(defspecial let* (loc args)
  (pmatch args
    ((,varlist . ,body)
     (let ((bindings (map (cut parse-let-binding loc <>) varlist)))
       (receive (decls forms) (parse-body body)
         (let iterate ((tail bindings))
           (if (null? tail)
               (compile-expr `(progn ,@forms))
               (let ((sym (caar tail))
                     (value (compile-expr (cdar tail))))
                 (if (bind-lexically? sym decls)
                     (let ((target (gensym)))
                       (make-let loc
                                 `(,target)
                                 `(,target)
                                 `(,value)
                                 (with-lexical-bindings
                                  (fluid-ref bindings-data)
                                  `(,sym)
                                  `(,target)
                                  (lambda () (iterate (cdr tail))))))
                     (ensure-globals!
                      loc
                      (list sym)
                      (make-dynlet loc
                                   (list (make-const loc sym))
                                   (list value)
                                   (iterate (cdr tail)))))))))))
    (else (report-error loc "Bad let*" args))))

(defspecial flet (loc args)
  (pmatch args
    ((,bindings . ,body)
     (let ((names+vals (map (cut parse-flet-binding loc <>) bindings)))
       (receive (decls forms) (parse-body body)
         (let ((names (map car names+vals))
               (vals (map cdr names+vals))
               (gensyms (map (lambda (x) (gensym)) names+vals)))
           (with-function-bindings
            (fluid-ref bindings-data)
            names
            gensyms
            (lambda ()
              (make-let loc
                        names
                        gensyms
                        (map compile-expr vals)
                        (compile-expr `(progn ,@forms)))))))))
    (else (report-error loc "bad flet" args))))

(defspecial labels (loc args)
  (pmatch args
    ((,bindings . ,body)
     (let ((names+vals (map (cut parse-flet-binding loc <>) bindings)))
       (receive (decls forms) (parse-body body)
         (let ((names (map car names+vals))
               (vals (map cdr names+vals))
               (gensyms (map (lambda (x) (gensym)) names+vals)))
           (with-function-bindings
            (fluid-ref bindings-data)
            names
            gensyms
            (lambda ()
              (make-letrec #f
                           loc
                           names
                           gensyms
                           (map compile-expr vals)
                           (compile-expr `(progn ,@forms)))))))))
    (else (report-error loc "bad labels" args))))

;;; guile-ref allows building TreeIL's module references from within
;;; elisp as a way to access data within the Guile universe.  The module
;;; and symbol referenced are static values, just like (@ module symbol)
;;; does!

(defspecial guile-ref (loc args)
  (pmatch args
    ((,module ,sym) (guard (and (list? module) (symbol? sym)))
     (make-module-ref loc module sym #t))
    (else (report-error loc "bad guile-ref" args))))

(defspecial guile-private-ref (loc args)
  (pmatch args
    ((,module ,sym) (guard (and (list? module) (symbol? sym)))
     (make-module-ref loc module sym #f))
    (else (report-error loc "bad guile-private-ref" args))))

;;; guile-primitive allows to create primitive references, which are
;;; still a little faster.

(defspecial guile-primitive (loc args)
  (pmatch args
    ((,sym)
     (make-primitive-ref loc sym))
    (else (report-error loc "bad guile-primitive" args))))

(defspecial %function (loc args)
  (pmatch args
    (((lambda ,args . ,body))
     (compile-lambda loc '() args body))
    (((closure ,env ,args . ,body))
     (let ((bindings (map (lambda (x) (list (car x) (cdr x)))
                          (filter pair? env))))
       (compile-expr
        (let ((form `(let ,bindings
                       (declare ,@(map (lambda (x) (list 'lexical x))
                                       bindings))
                       (function (lambda ,args
                                   (declare
                                    (lexical
                                     ,@(filter-map
                                        (lambda (x)
                                          (cond
                                           ((memq x '(&optional &rest))
                                            #f)
                                           ((symbol? x)
                                            x)
                                           ((list? x)
                                            (car x))))
                                        args)))
                                   ,@body)))))
          form))))
    ((,sym) (guard (symbol? sym))
     (reference-function loc sym))
    ((,x)
     (make-const loc x))
    (else (report-error loc "bad function" args))))

(defspecial function (loc args)
  (pmatch args
    ((,sym) (guard (symbol? sym))
     (make-const loc sym))
    (else ((cdr compile-%function) loc args))))

(defspecial defmacro (loc args)
  (pmatch args
    ((,name ,args . ,body)
     (if (not (symbol? name))
         (report-error loc "expected symbol as macro name" name)
         (let* ((tree-il
                 (make-seq
                  loc
                  (set-function!
                   loc
                   name
                   (make-call
                    loc
                    (make-module-ref loc '(guile) 'cons #t)
                    (list (make-const loc 'macro)
                          (compile-lambda loc
                                          `((name . ,name))
                                          args
                                          body))))
                  (make-const loc name))))
           (when (fluid-ref toplevel?)
             (with-native-target
              (lambda ()
                (eval tree-il (current-module)))))
           tree-il)))
    (else (report-error loc "bad defmacro" args))))

(defspecial #{`}# (loc args)
  (pmatch args
    ((,val)
     (process-backquote loc val))
    (else (report-error loc "bad backquote" args))))

(defspecial quote (loc args)
  (pmatch args
    ((,val)
     (make-const loc val))
    (else (report-error loc "bad quote" args))))

(defspecial %funcall (loc args)
  (pmatch args
    ((,function . ,arguments)
     (make-call loc
                (compile-expr function)
                (map compile-expr arguments)))
    (else (report-error loc "bad %funcall" args))))

(defspecial %set-lexical-binding-mode (loc args)
  (pmatch args
    ((,val)
     (set-lexical-binding-mode val)
     (make-void loc))
    (else (report-error loc "bad %set-lexical-binding-mode" args))))

(define (eget s p)
  (if (symbol-fbound? 'get)
      ((symbol-function 'get) s p)
      #nil))

;;; Compile a compound expression to Tree-IL.

(define (compile-pair loc expr)
  (let ((operator (car expr))
        (arguments (cdr expr)))
    (cond
     ((find-operator operator 'special-operator)
      => (lambda (special-operator-function)
           (special-operator-function loc arguments)))
     ((find-operator operator 'macro)
      => (lambda (macro-function)
           (compile-expr-1 (apply macro-function arguments))))
     ((and (symbol? operator)
           (eget operator '%compiler-macro))
      => (lambda (compiler-macro-function)
           (let ((new (compiler-macro-function expr)))
             (if (eq? new expr)
                 (compile-expr `(%funcall (%function ,operator) ,@arguments))
                 (compile-expr-1 new)))))
     (else
      (compile-expr `(%funcall (%function ,operator) ,@arguments))))))

;;; Compile a symbol expression.  This is a variable reference or maybe
;;; some special value like nil.

(define (compile-symbol loc sym)
  (case sym
    ((nil) (nil-value loc))
    ((t) (t-value loc))
    (else
     (let ((sym-name (symbol->string sym)))
       (cond
        ;; Keywords (colon-prefixed symbols) are self-evaluating
        ((and (> (string-length sym-name) 0)
              (char=? (string-ref sym-name 0) #\:))
         (make-const loc sym))
        ;; Uninterned symbols: check if bound in lexical environment first
        ((not ((@ (guile) symbol-interned?) sym))
         (let ((binding (get-lexical-binding (fluid-ref bindings-data) sym)))
           (if binding
               ;; If bound, treat as a variable reference
               (reference-variable loc sym)
               ;; Otherwise, this is likely a quoted/constant uninterned symbol
               ;; We can't serialize it, so intern it
               (make-const loc (string->symbol sym-name)))))
        ;; Regular symbols are variable references
        (else
         (reference-variable loc sym)))))))

;;; Compile a single expression to TreeIL.

(define (compile-expr-1 expr)
  (let ((loc (location expr)))
    (cond
     ((symbol? expr)
      (compile-symbol loc expr))
     ((pair? expr)
      (compile-pair loc expr))
     (else (make-const loc expr)))))

(define (compile-expr expr)
  (if (fluid-ref toplevel?)
      (with-fluids ((toplevel? #f))
        (compile-expr-1 expr))
      (compile-expr-1 expr)))

(define (compile-tree-il expr env opts)
  ;; Sanitize uninterned symbols before compilation to avoid Guile serialization errors
  (let* ((replacements (find-uninterned-symbols expr))
         (sanitized-expr (if (null? replacements)
                             expr
                             (begin
                               (format #t "[sanitize] Found ~a uninterned symbols in expr, replacing...~%" (length replacements))
                               (for-each (lambda (pair)
                                          (let ((sym-name (symbol->string (car pair))))
                                            (when (string-contains sym-name "--cl-")
                                              (format #t "  *** Found --cl- symbol: ~S -> ~S~%" (car pair) (cdr pair)))
                                            (format #t "  ~S -> ~S~%" (car pair) (cdr pair))))
                                        replacements)
                               (sanitize-uninterned-symbols expr replacements))))
         (tree-il (with-fluids ((bindings-data (make-bindings))
                                (toplevel? #t)
                                (compile-time-too? #f))
                    (compile-expr-1 sanitized-expr))))
    (when (logbit? 16 %debugflag)
      (format (current-error-port) "---------------------------------------------------------------~%")
      (format (current-error-port) "expr: ~s~%" expr)
      (format (current-error-port) "tree-il: ~s~%" (tree-il->scheme tree-il))
      (pretty-print (tree-il->scheme tree-il) (current-error-port)))
    (values tree-il env env)))
