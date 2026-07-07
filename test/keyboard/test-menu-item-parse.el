;;; test-menu-item-parse.el --- M10 imp-1.3 SRFI-64 suite

;; Wraps test/keyboard/test-menu-item-parse.scm — the Scheme test
;; corpus for (emacs menu-item-parse) parse-menu-item.
;;
;; Loads the Scheme file via eval-scheme, then reads back
;; `test-results` (list of (NAME STATUS) pairs) and reports each
;; via test-assert.  See docs/m10-plan.org §imp-1.3 for context.

(test-begin "menu-item-parse")

;; Run the Scheme test corpus.  Populates test-results in the
;; (guile-user) module.
(eval-scheme
 "(primitive-load \"test/keyboard/test-menu-item-parse.scm\")")

;; Read each result back and assert PASS.  Failing tests will
;; report the (name (FAIL 'expected E 'got A)) form as a mismatch.
(dolist (result (eval-scheme "(reverse test-results)"))
  (let ((name (car result))
        (status (cadr result)))
    (test-assert name (eq status 'PASS))))

(test-end)
