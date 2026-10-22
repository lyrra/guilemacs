;;; SRFI-64 tests for the standalone loader and Elisp reader/evaluator.

(use-modules (srfi srfi-64)
             (emacs loader)
             (emacs-elisp runtime))

;; Pinned case count.  A suite that loses a case must fail (cr.org of the
;; M59 imp-5 round, F3: the round file is reused, so name the round).
(define expected-passes 6)

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

(test-end "Guilemacs standalone loader and reader")

(let ((passes (test-runner-pass-count test-runner))
      (fails  (test-runner-fail-count test-runner)))
  (format #t "~a: ~a passed, ~a failed (expected ~a passed)~%"
          "Guilemacs standalone loader and reader" passes fails
          expected-passes)
  (exit (if (and (zero? fails) (= passes expected-passes)) 0 1)))
