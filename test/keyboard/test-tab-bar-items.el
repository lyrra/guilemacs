;;; test-tab-bar-items.el --- M10 imp-2.2 test suite for tab-bar-items

(princ "=== tab-bar-items test suite ===\n")

;; Run the Scheme test corpus.
(eval-scheme
 "(primitive-load \"test/keyboard/test-tab-bar-items.scm\")")

;; Read results back and report.
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
