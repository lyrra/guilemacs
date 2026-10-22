;;; SRFI-64 tests for the standalone loader and Elisp reader/evaluator.

(use-modules (srfi srfi-64)
             (emacs loader)
             (emacs-elisp runtime))

;; Pinned case count.  A suite that loses a case must fail (cr.org of the
;; M59 imp-5 round, F3: the round file is reused, so name the round).
;; M60 imp-14: 6 -> 8, the 2 `defalias' cases of row 34.
(define expected-passes 8)

;; No SRFI-64 log file: it would land in the working directory (cr.org F4).
(set! test-log-to-file #f)

(define repo-root (getenv "GUILEMACS_ROOT"))
(unless repo-root
  (error "GUILEMACS_ROOT must be set by run-mod-tests.sh"))

(define (fixture file)
  (string-append repo-root "/test/mod/" file))
(define runtime-module (resolve-module '(emacs-elisp runtime)))

(define (load-fixture file)
  "Load FILE with the standalone runtime as the current module."
  (save-module-excursion
   (lambda ()
     (set-current-module runtime-module)
     (elisp-load (fixture file)))))

(test-begin "Guilemacs standalone loader and reader")
(define test-runner (test-runner-current))

;; Initialize in plain Guile.  This suite does not start Emacs or loadup.el.
;; The handler keeps the condition key and arguments, so a failure names its
;; cause instead of a bare #f (cr.org N2).
(define init-result
  (catch #t
    (lambda ()
      (save-module-excursion
       (lambda () (init-loader (string-append repo-root "/prelude"))))
      #t)
    (lambda (key . args) (cons 'error (cons key args)))))
(test-assert (format #f "init-loader starts in plain Guile (result: ~s)"
                     init-result)
             (eq? #t init-result))

;; This fixture defines and calls an Elisp function, then stores its result.
(let ((result
       (catch #t
         (lambda () (load-fixture "standalone-loader.el") 'loaded)
         (lambda (key . args) (list 'error key args)))))
  (test-eq (format #f "loader reads and evaluates standalone Elisp (result: ~s)"
                   result)
           'loaded result))
(test-equal "evaluated Elisp side effect is observable"
            42
            (and (symbol-bound? 'standalone-loader-test-result)
                 (symbol-value 'standalone-loader-test-result)))

;; A reader-only path would not signal this error.  Evaluation must raise
;; void-function for the deliberately unbound call.
(let ((result
       (catch #t
         (lambda () (load-fixture "standalone-loader-error.el") 'loaded)
         (lambda (key . args) key))))
  (test-eq (format #f "loader propagates void-function from evaluation (key: ~s)"
                   result)
           'void-function result))

;; The elisp `set' cell of row 33 (M60 imp-13): `set' stores the VALUE
;; cell and returns NEWVAL, and a non-symbol raises.  The C owner is
;; src/data.c :1317.  The reader applies this cell for every `:keyword'
;; form (reader.scm :1358).
(let* ((set-fn (and (symbol-fbound? 'set) (symbol-function 'set)))
       (ret (and set-fn (apply set-fn '(standalone-set-test-var 42))))
       (stored (and (symbol-bound? 'standalone-set-test-var)
                    (symbol-value 'standalone-set-test-var)))
       (err (catch #t
              (lambda () (apply set-fn '("standalone-set-test-str" 1)) 'no-error)
              (lambda (key . args) (cons key args)))))
  ;; Guile stores a `misc-error' payload FLAT: a format string and its
  ;; argument list are 2 ADJACENT elements.  `init-loader' gives `error'
  ;; the elisp binding, so the measured shape is
  ;;   (misc-error #f "~A ~S" (MSG OBJ) #f).
  ;; The FORMATTED text is the stable token, so both shapes match it.
  (define (payload-text items)
    (cond ((or (null? items) (null? (cdr items))) #f)
          ((and (string? (car items)) (list? (cadr items)))
           (apply format #f (car items) (cadr items)))
          (else (payload-text (cdr items)))))
  (test-assert "elisp `set' stores the value cell and returns NEWVAL"
               (and (eq? #t (symbol-fbound? 'set))
                    (equal? 42 ret)
                    (equal? 42 stored)
                    (pair? err)
                    (eq? 'misc-error (car err))
                    (equal? (format #f "Wrong type argument: symbolp ~S"
                                    "standalone-set-test-str")
                            (payload-text (cdr err))))))

;; Row 33 on the real reader path: this fixture holds a :keyword form,
;; so `elisp-intern-and-make-keyword' (reader.scm :1358) applies the
;; `set' cell while it reads.  An empty cell raised wrong-type-arg.
;; The module `equal?' is not the Guile one (it does not compare lists),
;; so the 3 elements and the terminating nil are pinned one by one.
(let ((result (catch #t
                (lambda () (load-fixture "standalone-keyword.el") 'loaded)
                (lambda (key . args) (list 'error key args)))))
  (test-assert (format #f "reader handles a :keyword form (result: ~s)" result)
               (and (eq? 'loaded result)
                    (symbol-bound? 'standalone-keyword-test-result)
                    (let ((v (symbol-value 'standalone-keyword-test-result)))
                      (and (eq? (car v) (string->symbol ":keyword-a"))
                           (equal? (cadr v) 1)
                           (eq? (caddr v) (string->symbol ":keyword-b"))
                           (null? (cdddr v)))))))

;;; M60 imp-14 -- row 34: the `defalias' cell (utils.scm :235), the
;;; UNEVALLED `function' form (loader.scm :1209) and the symbol-cell
;;; indirection of `elisp-loader-apply' (loader.scm :1106).  C owner is
;;; `Fdefalias' (src/data.c :706).  The suite runs in plain Guile, so the
;;; 2 cases below are the automatic gate of the row.

;; The MESSAGE of the Guile `misc-error' of an elisp `(error FMT . ARGS)'
;; call, or #f.  Guile stores the payload FLAT: the format string and its
;; argument list are 2 ADJACENT elements.  The case above has its own
;; copy of this walk inside its `let'; this one is shared by the 2 cases
;; of row 34.
(define (row34-error-text items)
  (cond ((or (null? items) (null? (cdr items))) #f)
        ((and (string? (car items)) (list? (cadr items)))
         (apply format #f (car items) (cadr items)))
        (else (row34-error-text (cdr items)))))

;; Case 1 -- the CELL and the CALL.  `standalone-alias.el' is the real
;; reader and evaluator path: `defun', `#'x' (which reads to
;; `(function x)'), `defalias', then a CALL of the alias.  The cell must
;; hold the SOURCE SYMBOL, not a procedure: C stores the definition as
;; written and resolves it at CALL time (`indirect_function').  The
;; `defalias' return value is the SYMBOL, not the definition (bug#11686).
(let* ((alias-fn (and (symbol-fbound? 'defalias) (symbol-function 'defalias)))
       (result (catch #t
                 (lambda () (load-fixture "standalone-alias.el") 'loaded)
                 (lambda (key . args) (list 'error key args))))
       (ret (and alias-fn
                 (apply alias-fn '(standalone-alias-return-probe
                                   standalone-alias-source))))
       (cell (and (symbol-fbound? 'standalone-alias-target)
                  (symbol-function 'standalone-alias-target))))
  (test-assert (format #f "elisp `defalias' writes the SYMBOL cell, returns SYMBOL and the CALL follows the cell (result: ~s, cell: ~s)"
                       result cell)
               (and (eq? 'loaded result)
                    (eq? 'standalone-alias-source cell)
                    (eq? 'standalone-alias-return-probe ret)
                    (symbol-bound? 'standalone-alias-test-result)
                    (equal? 42 (symbol-value 'standalone-alias-test-result)))))

;; Case 2 -- the RAISE.  A ring A -> B -> A must raise
;; `cyclic-function-indirection' and must NOT hang; the raise names the
;; symbol of the CALL, not the symbol that closes the ring.  A non-symbol
;; ARG 1 must raise the `symbolp' shape of `elisp-put'.  The 100-link
;; count of the resolver is a guilemacs SAFETY: C has no count here.
(let* ((alias-fn (and (symbol-fbound? 'defalias) (symbol-function 'defalias)))
       (eval-form (module-ref (resolve-module '(emacs loader))
                              'elisp-loader-eval))
       (ring (and alias-fn
                  (begin
                    (apply alias-fn '(standalone-alias-ring-a
                                      standalone-alias-ring-b))
                    (apply alias-fn '(standalone-alias-ring-b
                                      standalone-alias-ring-a)))))
       (cycle (and ring
                   (catch #t
                     (lambda () (eval-form '(standalone-alias-ring-a)) 'no-error)
                     (lambda (key . args) (cons key args)))))
       (type-err (and alias-fn
                      (catch #t
                        (lambda ()
                          (apply alias-fn '("standalone-alias-str"
                                            standalone-alias-source))
                          'no-error)
                        (lambda (key . args) (cons key args)))))
       (text (and (pair? type-err) (row34-error-text (cdr type-err)))))
  (test-assert (format #f "elisp `defalias' raises `cyclic-function-indirection' on a symbol ring and `symbolp' on a non-symbol (cycle: ~s, type: ~s)"
                       cycle (and (pair? type-err) (car type-err)))
               (and (eq? 'cyclic-function-indirection (and (pair? cycle) (car cycle)))
                    (equal? '(standalone-alias-ring-a) (cdr cycle))
                    (eq? 'misc-error (and (pair? type-err) (car type-err)))
                    ;; The FORMATTED text is the stable token: the
                    ;; payload shape differs between Guile versions.
                    (equal? "Wrong type argument: symbolp \"standalone-alias-str\""
                            text))))

(test-end "Guilemacs standalone loader and reader")

(let ((passes (test-runner-pass-count test-runner))
      (fails  (test-runner-fail-count test-runner)))
  (format #t "~a: ~a passed, ~a failed (expected ~a passed)~%"
          "Guilemacs standalone loader and reader" passes fails
          expected-passes)
  (exit (if (and (zero? fails) (= passes expected-passes)) 0 1)))
