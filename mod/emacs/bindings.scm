;;; Scheme Binding Registry for Guilemacs
;;;
;;; This module provides a Scheme-based binding stack to replace the C specpdl
;;; for tracking dynamic variable bindings. The actual bind/unbind is done via
;;; Guile's dynamic-wind; this registry is for introspection functions like
;;; `default-toplevel-value'.
;;;
;;; See docs/specbind2.org for migration plan.

(define-module (emacs bindings)
  #:use-module (ice-9 match)
  #:use-module (emacs-elisp runtime)
  #:export (;; Core operations
            push-binding!
            pop-binding!
            binding-stack-empty?

            ;; Introspection
            find-toplevel-binding
            set-toplevel-binding!
            find-all-bindings
            symbol-has-binding?
            symbol-lexbound?
            let-shadows-buffer-binding?

            ;; For testing/debugging
            binding-stack-depth
            clear-binding-stack!
            with-binding-stack

            ;; Constants for binding kinds
            BINDING-LET
            BINDING-LET-LOCAL
            BINDING-LET-DEFAULT

            ;; Elisp-callable functions
            elisp-default-toplevel-value
            elisp-set-default-toplevel-value!
            init-bindings-registrations))

;;; ==========================================================================
;;; Binding Kind Constants
;;; ==========================================================================

;; These match the C constants in eval.c
(define BINDING-LET         0)  ;; Plain dynamic let-binding
(define BINDING-LET-LOCAL   1)  ;; Buffer-local let-binding
(define BINDING-LET-DEFAULT 2)  ;; Global binding for localized var

;;; ==========================================================================
;;; Thread-Local Binding Stack
;;; ==========================================================================

;; Use Guile's parameter for thread-local storage.
;; Each thread has its own binding stack.
;;
;; Stack entries are vectors: #(symbol old-value kind where)
;;   symbol:    the symbol being bound
;;   old-value: the value before this binding
;;   kind:      BINDING-LET, BINDING-LET-LOCAL, or BINDING-LET-DEFAULT
;;   where:     buffer for LET-LOCAL, #f otherwise

(define *binding-stack* (make-parameter '()))

;;; ==========================================================================
;;; Core Operations
;;; ==========================================================================

(define (push-binding! symbol old-value kind where)
  "Push a binding entry onto the stack.
SYMBOL is the symbol being bound.
OLD-VALUE is its value before the binding.
KIND is BINDING-LET, BINDING-LET-LOCAL, or BINDING-LET-DEFAULT.
WHERE is the buffer for LET-LOCAL bindings, #f otherwise."
  (*binding-stack*
   (cons (vector symbol old-value kind where)
         (*binding-stack*))))

(define (pop-binding!)
  "Pop the most recent binding from the stack.
Returns the popped entry, or #f if stack was empty."
  (let ((stack (*binding-stack*)))
    (if (null? stack)
        #f
        (let ((entry (car stack)))
          (*binding-stack* (cdr stack))
          entry))))

(define (binding-stack-empty?)
  "Return #t if the binding stack is empty."
  (null? (*binding-stack*)))

(define (binding-stack-depth)
  "Return the number of entries on the binding stack."
  (length (*binding-stack*)))

(define (clear-binding-stack!)
  "Clear the binding stack. For testing only!"
  (*binding-stack* '()))

(define-syntax with-binding-stack
  (syntax-rules ()
    "Execute BODY with a fresh binding stack, restoring original after."
    ((_ body ...)
     (parameterize ((*binding-stack* '()))
       body ...))))

;;; ==========================================================================
;;; Introspection Functions
;;; ==========================================================================

(define (find-toplevel-binding symbol)
  "Find the toplevel (outermost) binding for SYMBOL.
Returns the old-value from the outermost binding, or #f if no binding exists.
This is used by `default-toplevel-value' to find the value before any let bindings."
  (let loop ((stack (*binding-stack*))
             (found #f))
    (if (null? stack)
        found
        (let ((entry (car stack)))
          (if (eq? (vector-ref entry 0) symbol)
              ;; Found a binding - keep the old-value but continue
              ;; looking for an even older binding
              (loop (cdr stack) (vector-ref entry 1))
              (loop (cdr stack) found))))))

(define (elisp-default-toplevel-value symbol)
  "Return SYMBOL's toplevel default value.
Toplevel means outside of any let binding.
Signals void-variable if the symbol has no value."
  (let ((value (find-toplevel-binding symbol)))
    (if value
        value
        ;; No binding in registry - fall back to default-value
        (let ((default ((@@ (elisp-functions) default-value) symbol)))
          (if (eq? default (@ (emacs-elisp runtime) unbound))
              ((@@ (elisp-functions) signal) 'void-variable (list symbol))
              default)))))

(define (set-toplevel-binding! symbol value)
  "Set the old-value of the toplevel (outermost) binding for SYMBOL.
Returns #t if a binding was found and modified, #f otherwise.
This is used by `set-default-toplevel-value' to modify the toplevel value."
  (let loop ((stack (*binding-stack*))
             (found-entry #f))
    (if (null? stack)
        ;; Reached end - modify the outermost binding if we found one
        (if found-entry
            (begin
              (vector-set! found-entry 1 value)
              #t)
            #f)
        (let ((entry (car stack)))
          (if (eq? (vector-ref entry 0) symbol)
              ;; Found a binding - remember it but continue
              ;; looking for an even older binding
              (loop (cdr stack) entry)
              (loop (cdr stack) found-entry))))))

(define (elisp-set-default-toplevel-value! symbol value)
  "Set SYMBOL's toplevel default value to VALUE.
Toplevel means outside of any let binding.
Returns nil."
  ;; 1. Update the Scheme binding registry (for interpreted code)
  ;; 2. Set the default value directly (for unbound case and compiled code)
  (let ((found (set-toplevel-binding! symbol value)))
    ;; If no binding exists in registry, set the default directly
    (unless found
      ((@@ (elisp-functions) set-default) symbol value)))
  #nil)

(define (find-all-bindings symbol)
  "Find all bindings for SYMBOL on the stack.
Returns a list of binding entries, most recent first.
For debugging and testing."
  (filter (lambda (entry)
            (eq? (vector-ref entry 0) symbol))
          (*binding-stack*)))

(define (symbol-has-binding? symbol)
  "Check if SYMBOL has any binding on the stack.
Returns #t if at least one binding exists, #f otherwise.
This is used by defvaralias to prevent aliasing let-bound variables."
  (let loop ((stack (*binding-stack*)))
    (if (null? stack)
        #f
        (let ((entry (car stack)))
          (if (eq? (vector-ref entry 0) symbol)
              #t
              (loop (cdr stack)))))))

(define (symbol-lexbound? symbol)
  "Check if SYMBOL is lexically bound in the interpreter environment.
This walks the binding stack looking for `internal-interpreter-environment'
and checks if SYMBOL is in that environment.
Returns #t if lexically bound, #f otherwise."
  (let loop ((stack (*binding-stack*)))
    (if (null? stack)
        #f
        (let ((entry (car stack)))
          (if (eq? (vector-ref entry 0) 'internal-interpreter-environment)
              ;; Found an interpreter environment binding
              ;; Check if symbol is in the old environment
              (let ((env (vector-ref entry 1)))
                (if (and (pair? env) (assq symbol env))
                    #t
                    (loop (cdr stack))))
              (loop (cdr stack)))))))

(define (let-shadows-buffer-binding? symbol buffer)
  "Check if a let-binding shadows a buffer-local binding.
Returns #t if SYMBOL has a LET-LOCAL binding for BUFFER on the stack."
  (let loop ((stack (*binding-stack*)))
    (if (null? stack)
        #f
        (let ((entry (car stack)))
          (if (and (eq? (vector-ref entry 0) symbol)
                   (> (vector-ref entry 2) BINDING-LET)  ;; LET-LOCAL or LET-DEFAULT
                   (not (eq? (vector-ref entry 2) BINDING-LET-LOCAL))  ;; bug#62419
                   (eq? (vector-ref entry 3) buffer))
              #t
              (loop (cdr stack)))))))

;;; ==========================================================================
;;; Debugging Helpers
;;; ==========================================================================

(define (binding-entry->string entry)
  "Convert a binding entry to a human-readable string."
  (let ((sym (vector-ref entry 0))
        (old (vector-ref entry 1))
        (kind (vector-ref entry 2))
        (where (vector-ref entry 3)))
    (format #f "#<binding ~a old=~s kind=~a where=~s>"
            sym old
            (case kind
              ((0) "LET")
              ((1) "LET-LOCAL")
              ((2) "LET-DEFAULT")
              (else "?"))
            where)))

(define (print-binding-stack)
  "Print the current binding stack. For debugging."
  (format #t "Binding stack (~a entries):~%" (binding-stack-depth))
  (for-each (lambda (entry)
              (format #t "  ~a~%" (binding-entry->string entry)))
            (*binding-stack*)))

(define (init-bindings-registrations)
  (for-each (lambda (sym-fun)
              (set-symbol-function! (car sym-fun) (cadr sym-fun)))
            `((default-toplevel-value ,elisp-default-toplevel-value)
              (set-default-toplevel-value ,elisp-set-default-toplevel-value!))))
