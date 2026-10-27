;;; SRFI-64 tests for the FIRST STOP of the 4 real lisp/ files.
;;
;; ROUND M60 imp-25: the BEHAVIOR replacement for the 4 rows of
;; milestone.org section 2.2, which imp-23 deleted with its 21
;; source-inspection checks.
;;
;; FIRST STOP at base commit 2ffeec125, and REFERENCE COMMAND
;; (milestone.org section 2.2):
;;
;;   lisp/emacs-lisp/byte-run.el   done
;;   lisp/emacs-lisp/macroexp.el   void-function (defsubst)
;;   lisp/custom.el                void-function (defsubst)
;;   lisp/startup.el               void-function (nconc)
;;
;;   GUILEMACS_ROOT=$PWD GUILE_AUTO_COMPILE=0 \
;;     guile -L mod test/m60/probe-imp3.scm purecopy
;;
;; COST: 4 cases in 1 guile process, MEASURED `real' 0.040s ... 0.044s
;; (3 runs, this host).  The runner starts 1 process per suite, so the
;; cases get a clean `init-loader' state in their own file and
;; standalone-tests.scm keeps its pin of 61.  PIN: 4 passes.
;;
;; The check reads the loader RESULT plus the error key and arguments,
;; never source text or a count, so a moved stop point is RED.
;;
;; 2 PINS, 1 BEHAVIOR: test/m60/test-m60-imp9.el s3/purecopy-first-stops
;; pins the same 4 answers from the probe console text and needs a built
;; tree; this pin needs plain `guile' only.  A row that moves a stop
;; point must re-pin BOTH.
;;
;; custom.el prints `loading widget' on STDERR before its raise (the
;; loader's `loading <name>' message, not an elisp `message').  Its
;; POSITION IS NOT STABLE: stdout is block-buffered on a pipe, so a 2>&1
;; capture can put it first.  No line position, no console line count.
;;
;; LIMIT: plain `guile' only, no Emacs and no C build.  `defsubst',
;; `nconc' and later stops stay OPEN: 3 of the 4 files still stop, so no
;; standalone Elisp path is complete.

(use-modules (srfi srfi-64)
             (emacs loader)
             (emacs-elisp runtime))

;; Pinned case count: a suite that loses a case must fail.  Each suite
;; pins its own count (docs/kb.org test-mod-standalone-suite).
(define expected-passes 4)

;; No SRFI-64 log file: it would land in the working directory.
(set! test-log-to-file #f)

;; The runner sets GUILEMACS_ROOT.  A $PWD default could silently test
;; another tree, so a missing value is a hard error.
(define repo-root (getenv "GUILEMACS_ROOT"))
(unless repo-root
  (error "GUILEMACS_ROOT must be set by run-mod-tests.sh"))

;; ORDER RULE 1: `test-begin' creates the runner, so it comes BEFORE
;; `(test-runner-current)'.  The reverse order makes the count block
;; below raise `struct-vtable: Wrong type argument'.
(test-begin "Guilemacs loading-path stops")

;; ORDER RULE 2: `(srfi srfi-64)' exports no `test-runner'; bind
;; `(test-runner-current)', as test/mod/faces-tests.scm does.
(define test-runner (test-runner-current))

;; ORDER RULE 3: `init-loader' leaves the current module at
;; (emacs-elisp runtime) (test/m60/probe-imp3.scm header), so call it
;; inside `save-module-excursion'.  A bare `set-current-module' after the
;; call loses the srfi-64 bindings.
;;
;; The result is `#t' on a good boot and `(error KEY . ARGS)' on a bad
;; boot, so case 1 names the cause of a broken boot.
(define init-result
  (catch #t
    (lambda ()
      (save-module-excursion
       (lambda () (init-loader (string-append repo-root "/prelude"))))
      #t)
    (lambda (key . args) (cons 'error (cons key args)))))

;; The answer is `(ok VALUE)' for a completed load and `(error KEY
;; . ARGS)' for a raise, never console text.
;;
;; ORDER RULE 4: the argument is a BASE NAME.  `init-loader' fills
;; `%load-path' with the lisp/ directories, so the base name resolves; a
;; hand-built path would not prove that.  The full path of each file is
;; in its case text.
(define (first-stop name)
  (catch #t
    (lambda () (list 'ok (load-elisp name)))
    (lambda (key . args) (cons* 'error key args))))

(define (stop-is-done? name)
  (equal? (first-stop name) (list 'ok 'done)))

;; The error argument list is the 1 element list (ARG), so the assertion
;; is `(equal? (cddr result) (list arg))'.
(define (raises? name key arg)
  (let ((r (first-stop name)))
    (and (pair? r) (eq? (car r) 'error)
         (eq? (cadr r) key)
         (equal? (cddr r) (list arg)))))

;; Case 1 fails when `init-loader' fails and shows `init: (error KEY
;; . ARGS)', so a broken boot names its own cause.  Do not add a 5th
;; case for the boot.
(test-assert (format #f "lisp/emacs-lisp/byte-run.el loads to the end (init: ~s)"
                     init-result)
             (and (eq? #t init-result)
                  (stop-is-done? "byte-run.el")))
(test-assert "lisp/emacs-lisp/macroexp.el stops on (defsubst)"
             (raises? "macroexp.el" 'void-function 'defsubst))
(test-assert "lisp/custom.el stops on (defsubst)"
             (raises? "custom.el" 'void-function 'defsubst))
(test-assert "lisp/startup.el stops on (nconc)"
             (raises? "startup.el" 'void-function 'nconc))

(test-end "Guilemacs loading-path stops")

(let ((passes (test-runner-pass-count test-runner))
      (fails  (test-runner-fail-count test-runner)))
  (format #t "~a: ~a passed, ~a failed (expected ~a passed)~%"
          "Guilemacs loading-path stops" passes fails expected-passes)
  (exit (if (and (zero? fails) (= passes expected-passes)) 0 1)))
