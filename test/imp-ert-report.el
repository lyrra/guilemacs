;;; imp-ert-report.el --- register a corpus (NAME STATUS) result as a real ERT test.  -*- lexical-binding: t; -*-
;;;
;;; Every M2x-M40 imp/audit wrapper (test/keyboard/test-mNN-impM.el,
;;; test/m39/*.el, test/m40/*.el) runs a Scheme corpus that produces a
;;; list of (NAME STATUS) results, then needs each result to also become
;;; a genuine ERT test -- tool/run-tests.scm's run-tests-loadup-emacs
;;; parses ERT's own "passed N/M name" batch protocol output to build the
;;; harness's pass/fail counts, so a corpus check that is only princ'd is
;;; invisible to that accounting and to the exit code.
;;;
;;; This used to be, at each of the ~55 call sites:
;;;   (eval `(ert-deftest ,(intern name) ()
;;;            (should (eq ',status 'PASS))))
;;; Two problems with that:
;;;   - `eval' + backquote is an obfuscated way to do what `ert-deftest'
;;;     itself macro-expands into: a call to `make-ert-test' and
;;;     `ert-set-test' (lisp/emacs-lisp/ert.el, the ert-deftest macro
;;;     body).  Both are ordinary functions; nothing here needs `eval'.
;;;   - none of the ~55 wrapper files declare lexical-binding, so writing
;;;     a plain `(lambda () (should (eq status 'PASS)))' directly at each
;;;     call site, inside a `dolist', would close over STATUS
;;;     dynamically: by the time ERT calls the test body (after the whole
;;;     file has finished loading), the `let*'-bound STATUS is long out
;;;     of dynamic scope.  The original code dodged this by splicing
;;;     STATUS's *value* into the generated form as a literal via
;;;     backquote, so the lambda closed over nothing.
;;;
;;; This file is the fix for both: it declares its own lexical-binding,
;;; so the `lambda' below is a real lexical closure over its own
;;; parameter -- correct regardless of whether the *caller* enables
;;; lexical-binding, exactly like `apply-partially' in lisp/subr.el
;;; (itself lexical-binding: t) is safe to call from dynamic-binding
;;; code.  Callers pass NAME and STATUS as plain arguments; no eval, no
;;; backquote, at either end.
;;;
;;; A name collision -- two corpora in the same batch producing the
;;; identical NAME string -- is not swallowed here or by the old code:
;;; `ert-set-test' itself signals "Test `NAME' redefined (or loaded
;;; twice)" in batch mode.  That guard predates this file; nothing here
;;; adds or removes it.
;;;
;;; Load with:
;;;   (require 'imp-ert-report)
;;; `require' is idempotent, so calling it from every wrapper file that
;;; gets loaded into the same batch is fine.  test/ is on load-path
;;; (tool/run-tests.scm passes "-L :." and `cd test' happens first), so
;;; this resolves the same way from test/keyboard/, test/m39/, and
;;; test/m40/.

(defun imp-register-check-as-ert-test (name status)
  "Register NAME as a real ERT test asserting STATUS is the symbol PASS.
NAME is a string, interned once.  STATUS is a corpus result's cadr: the
symbol PASS on success, or a (FAIL ...) / (INFO ...) list otherwise."
  (ert-set-test (intern name)
                (make-ert-test :name (intern name)
                               :body (lambda () (should (eq status 'PASS))))))

;; A handful of the M39/M40 wrapper files use a simpler convention: a
;; plain boolean local (e.g. RES, OK, MADE) instead of a corpus
;; (NAME STATUS) pair, asserted via `(should ',res)' / `(should ,ok)'
;; (both splice the boolean's *value* into the generated form -- t/nil
;; self-quote, so `,ok' and `',res' come out the same either way).  Same
;; fix, same reasoning as `imp-register-check-as-ert-test' above: no
;; eval, a real lexical closure over the function's own parameter.
(defun imp-register-bool-as-ert-test (name value)
  "Register NAME as a real ERT test asserting VALUE is non-nil.
NAME is a string, interned once."
  (ert-set-test (intern name)
                (make-ert-test :name (intern name)
                               :body (lambda () (should value)))))

(provide 'imp-ert-report)

;;; imp-ert-report.el ends here
