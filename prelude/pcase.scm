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

(define (pcase-scm--split-match sym splitter match)
  (let ((head (pcase-scm--car-safe match)))
    (cond
     ((eq? head 'match)
      (let ((match-sym (if (and (pair? match) (pair? (cdr match))) (cadr match) #f)))
        (if (not (eq? match-sym sym))
            (cons match match)
            (let* ((res (splitter (cddr match)))
                   (then-branch (and (pair? res) (car res)))
                   (else-branch (and (pair? res) (cdr res))))
              (cons (if then-branch then-branch match)
                    (if else-branch else-branch match))))))
     ((and (symbol? head) (or (eq? head 'or) (eq? head 'and)))
      (let* ((neutral (if (eq? head 'or) ':pcase--fail ':pcase--succeed))
             (zero    (if (eq? head 'or) ':pcase--succeed ':pcase--fail))
             (alts (pcase-scm--proper-list (cdr match)))
             (then-alts '())
             (else-alts '()))
        (for-each
         (lambda (alt)
           (let* ((split (pcase-scm--split-match sym splitter alt))
                  (then (car split))
                  (els (cdr split)))
             (if (not (eq? then neutral))
                 (set! then-alts (cons then then-alts)))
             (if (not (eq? els neutral))
                 (set! else-alts (cons els else-alts)))))
         alts)
        (let ((normalized-then
               (cond ((pcase-scm--member zero then-alts) zero)
                     ((null? then-alts) neutral)
                     ((null? (cdr then-alts)) (car then-alts))
                     (else (cons head (reverse then-alts)))))
              (normalized-else
               (cond ((pcase-scm--member zero else-alts) zero)
                     ((null? else-alts) neutral)
                     ((null? (cdr else-alts)) (car else-alts))
                     (else (cons head (reverse else-alts))))))
          (cons normalized-then normalized-else))))
     ((or (eq? match ':pcase--succeed) (eq? match ':pcase--fail))
      (cons match match))
     (else (error "pcase-scm--split-match: unknown match" match)))))

(define (pcase-scm--member elt lst)
  (cond
   ((or (eq? lst nil-value) (null? lst)) #f)
   ((eq? (car lst) elt) lst)
   (else (pcase-scm--member elt (cdr lst)))))

(define (pcase-scm--split-rest sym splitter rest)
  (let ((then-rest '())
        (else-rest '()))
    (for-each
     (lambda (branch)
       (let* ((match (car branch))
              (code&vars (cdr branch))
              (split (pcase-scm--split-match sym splitter match))
              (then (car split))
              (els (cdr split)))
         (if (not (eq? then ':pcase--fail))
             (set! then-rest (cons (cons then code&vars) then-rest)))
         (if (not (eq? els ':pcase--fail))
             (set! else-rest (cons (cons els code&vars) else-rest)))))
     (pcase-scm--proper-list rest))
    (cons (reverse then-rest) (reverse else-rest))))

(define (pcase-scm--small-branch? code)
  (and (pair? code)
       (pcase-scm--null? (cdr code))
       (let ((first (car code)))
         (or (not (pair? first))
             (let loop ((elts first))
               (cond
                ((pcase-scm--null? elts) #t)
                ((pair? elts)
                 (if (pair? (car elts))
                     #f
                     (loop (cdr elts))))
                (else #t))))))

(define (pcase-scm--if test then else)
  (cond
   ((eq? else ':pcase--dontcare)
    (list 'progn (list 'ignore test) then))
   ((eq? then ':pcase--dontcare)
    (list 'progn (list 'ignore test) else))
   (else (pcase--macroexp-if test then else))))

(define (pcase-scm--ignore-errors thunk)
  (with-exception-handler
      (lambda (_exn) nil-value)
    (lambda () (thunk))
    #:unwind? #t))

(define (pcase-scm--list-member? elem lst)
  (let loop ((rest (pcase-scm--proper-list lst)))
    (cond
     ((pcase-scm--null? rest) #f)
     ((equal? (car rest) elem) #t)
     ((pair? rest) (loop (cdr rest)))
     (else #f))))

(define (pcase-scm--split-equal elem pat)
  (cond
   ((and (eq? (pcase-scm--car-safe pat) 'quote)
         (let ((quoted (if (and (pair? pat) (pair? (cdr pat))) (cadr pat) nil-value)))
           (equal? quoted elem)))
    (cons ':pcase--succeed ':pcase--fail))
   ((eq? (pcase-scm--car-safe pat) 'quote)
    (cons ':pcase--fail nil-value))
   ((and (eq? (pcase-scm--car-safe pat) 'pred)
         (symbol? (cadr pat))
         (pcase--true? (pcase--get (cadr pat) 'side-effect-free)))
    (let ((res
           (pcase-scm--ignore-errors
            (lambda ()
              (if (pcase--true? (pcase--call (cadr pat) elem))
                  (cons ':pcase--succeed nil-value)
                  (cons ':pcase--fail nil-value))))))
      (if (eq? res nil-value) nil-value res)))
   (else nil-value)))

(define (pcase-scm--split-member elems pat)
  (cond
   ((and (eq? (pcase-scm--car-safe pat) 'quote)
         (pcase-scm--list-member? (cadr pat) elems))
    nil-value)
   ((eq? (pcase-scm--car-safe pat) 'quote)
    (cons ':pcase--fail nil-value))
   ((and (eq? (pcase-scm--car-safe pat) 'pred)
         (symbol? (cadr pat))
         (pcase--true? (pcase--get (cadr pat) 'side-effect-free)))
    (let ((res
           (pcase-scm--ignore-errors
            (lambda ()
              (let ((p (cadr pat)))
                (if (let loop ((rest (pcase-scm--proper-list elems)) (ok #t))
                      (cond
                       ((not ok) #f)
                       ((pcase-scm--null? rest) #t)
                       ((pair? rest)
                        (loop (cdr rest)
                              (and ok (pcase--true? (pcase--call p (car rest))))))
                       (else ok)))
                    (cons ':pcase--succeed nil-value)
                    nil-value))))))
      (if (eq? res nil-value) nil-value res)))
   (else nil-value)))

;; Temporary bridge: use the original Elisp helpers when available while their
;; Scheme counterparts are under construction.
(define (pcase-scm--split-pred vars upat pat)
  (let ((orig (pcase--maybe-elisp-function 'pcase--split-pred)))
    (if orig
        (orig vars upat pat)
        nil-value)))

(define (pcase-scm--mark-used sym)
  (when (symbol? sym)
    (pcase--put sym 'pcase-used t-value)))

(define (pcase-scm--app-subst-match match sym fun nsym)
  (let ((orig (pcase--maybe-elisp-function 'pcase--app-subst-match)))
    (if orig
        (orig match sym fun nsym)
        match)))

(define (pcase-scm--app-subst-rest rest sym fun nsym)
  (map (lambda (branch)
         (let ((new-match (pcase-scm--app-subst-match (car branch) sym fun nsym)))
           (cons new-match (cdr branch))))
       (pcase-scm--proper-list rest)))
