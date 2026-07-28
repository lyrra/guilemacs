;;; test-menu-bar-items.el --- M10 imp-4.1 test suite for menu-bar-items
;;;
;;; Wraps test/keyboard/test-menu-bar-items.scm — the Scheme test
;;; corpus for (emacs menu-bar-items).
;;;
;;; Loads the Scheme file via eval-scheme, then reads back
;;; `test-results` (list of (NAME STATUS) pairs) and reports each
;;; via princ.  See docs/m10-plan.org §imp-4.1 for context.

(princ "=== menu-bar-items test suite ===\n")

;; Run the Scheme test corpus.  Populates test-results in the
;; (guile-user) module.
(eval-scheme
 "(primitive-load \"test/keyboard/test-menu-bar-items.scm\")")

;; Read each result back and report PASS/FAIL.
(let ((results (eval-scheme "(reverse test-results)"))
      (pass 0)
      (fail 0))
  (dolist (result results)
    (let* ((name (car result))
           (status (cadr result))
           (ok (eq status 'PASS)))
      (if ok
          (setq pass (1+ pass))
        (setq fail (1+ fail)))
      (princ (format "%s %s%s\n" (if ok "PASS" "FAIL") name
                     (if ok "" (format " %S" (cdr result)))))))
  (princ (format "=== %d passed, %d failed, %d total ===\n"
                 pass fail (+ pass fail))))
