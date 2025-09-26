;;; pcase.scm --- Scheme support for rewriting Elisp pcase macros

;; Helpers shared by the upcoming Guile-based pcase implementation.

(define (pcase--true? value)
  (not (eq? value nil-value)))

(define (pcase--maybe-elisp-function sym)
  (let ((fun (symbol-function sym)))
    (if (eq? fun nil-value) #f fun)))

(define (pcase--elisp-function sym)
  (let ((fun (pcase--maybe-elisp-function sym)))
    (if fun fun (error "pcase: missing elisp function" sym))))

(define (pcase--call sym . args)
  (apply (pcase--elisp-function sym) args))

(define (pcase--macro-function sym)
  (let ((mf (pcase--maybe-elisp-function 'macro-function)))
    (if mf (mf sym) #f)))

(define (pcase--require feature)
  (let ((featurep (pcase--maybe-elisp-function 'featurep)))
    (cond
      ((and featurep (pcase--true? (featurep feature))) #t)
      (else
       (let ((require (pcase--maybe-elisp-function 'require)))
         (if require
             (require feature)
             #f))))))

(define (pcase--ensure-macroexp!)
  (pcase--require 'macroexp)
  (pcase--require 'help-fns))

(define (pcase--macroexp-progn forms)
  (pcase--ensure-macroexp!)
  (pcase--call 'macroexp-progn forms))

(define (pcase--macroexp-let* bindings body)
  (pcase--ensure-macroexp!)
  (apply (pcase--elisp-function 'macroexp-let*)
         (cons bindings body)))

(define (pcase--macroexp-let2 test var form . body)
  (pcase--ensure-macroexp!)
  (apply (pcase--elisp-function 'macroexp-let2)
         (cons test (cons var (cons form body)))))

(define (pcase--macroexp-if test then else)
  (pcase--ensure-macroexp!)
  (pcase--call 'macroexp-if test then else))

(define (pcase--macroexp-warn message expansion object)
  (pcase--ensure-macroexp!)
  (pcase--call 'macroexp-warn-and-return
               message
               expansion
               nil-value
               nil-value
               object))

(define (pcase--macroexp-parse-body body)
  (pcase--ensure-macroexp!)
  (pcase--call 'macroexp-parse-body body))

(define (pcase--macroexp-fgrep env form)
  (pcase--ensure-macroexp!)
  (pcase--call 'macroexp--fgrep env form))

(define (pcase--macroexp-copyable? form)
  (pcase--ensure-macroexp!)
  (pcase--call 'macroexp-copyable-p form))

(define (pcase--define-symbol-prop sym prop value)
  (pcase--call 'define-symbol-prop sym prop value))

(define (pcase--put sym prop value)
  (pcase--call 'put sym prop value))

(define (pcase--get sym prop)
  (pcase--call 'get sym prop))

(define (pcase--mapatoms proc)
  (pcase--call 'mapatoms proc))

(define (pcase--help-fns-short-filename file)
  (pcase--ensure-macroexp!)
  (pcase--call 'help-fns-short-filename file))

(define (pcase--help-add-fundoc-usage doc usage)
  (pcase--ensure-macroexp!)
  (pcase--call 'help-add-fundoc-usage doc usage))

(define (pcase--help-split-fundoc doc symbol)
  (pcase--ensure-macroexp!)
  (pcase--call 'help-split-fundoc doc symbol))

(define (pcase--help-insert-xref-button label event symbol file kind)
  (pcase--ensure-macroexp!)
  (pcase--call 'help-insert-xref-button label event symbol file kind))

(define (pcase--find-lisp-object-file-name object type)
  (pcase--call 'find-lisp-object-file-name object type))

(define (pcase--make-hash-table . args)
  (apply (pcase--elisp-function 'make-hash-table) args))

(define (pcase--hash-table-get table key)
  ((pcase--elisp-function 'gethash) key table))

(define (pcase--hash-table-put! table key value)
  ((pcase--elisp-function 'puthash) key value table))

(define (pcase--hash-table-clear! table)
  ((pcase--elisp-function 'clrhash) table))

(define (pcase--hash-table-for-each table proc)
  ((pcase--elisp-function 'maphash) proc table))

(define (pcase--gensym prefix)
  (if prefix
      (pcase--call 'gensym prefix)
      (pcase--call 'gensym)))

(define (pcase--intern-gensym prefix)
  (pcase--call 'intern-gensym prefix))

;; Placeholder wiring: delegate to the existing Elisp implementation while
;; we build out the Scheme port.  This validates that Scheme-defined macros
;; can be installed via set-symbol-function! without behavioral changes.
(let ((existing (symbol-function 'pcase)))
  (unless (and (pair? existing) (eq? (car existing) 'macro))
    (pcase--require 'pcase)
    (set! existing (symbol-function 'pcase)))
  (when (and (pair? existing) (eq? (car existing) 'macro))
    (let* ((orig existing)
           (orig-fn (pcase--macro-function 'pcase)))
      (when orig-fn
        (define (pcase--scheme-placeholder form . rest)
          (apply orig-fn (cons form rest)))
        (set-symbol-function! 'pcase (cons 'macro pcase--scheme-placeholder))
        (pcase--put 'pcase 'pcase-original orig)))))

;; ----------------------------------------------------------------------------
;; Scheme reimplementations of core helpers (built alongside the Elisp version
;; so we can validate behavior before switching the macro binding).

(define (pcase-scm--null? obj)
  (or (eq? obj nil-value) (null? obj)))

(define (pcase-scm--proper-list obj)
  (cond
   ((eq? obj nil-value) '())
   ((pair? obj) obj)
   (else '())))

(define (pcase-scm--car-safe obj)
  (if (pair? obj) (car obj) nil-value))

(define (pcase-scm--match val upat)
  (let ((head (pcase-scm--car-safe upat)))
    (if (and (symbol? head)
             (or (eq? head 'or) (eq? head 'and)))
        (cons head
              (map (lambda (sub) (pcase-scm--match val sub))
                   (pcase-scm--proper-list (if (pair? upat) (cdr upat) nil-value))))
        (cons 'match (cons val upat)))))

(define (pcase-scm--and match matches)
  (if (pcase-scm--null? matches)
      match
      (cons 'and (cons match matches))))
