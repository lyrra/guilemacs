;;; test-m19-fixes.el --- regression tests for the M19 cr.org findings
;;;
;;; Wraps test/keyboard/test-m19-fixes.scm — the Scheme regression
;;; corpus for the two defects reported in cr.org on (emacs
;;; lispy-position):
;;;   * Finding 1 — vscroll-on-right? now tests `(eq? vtype #t)`.
;;;   * Finding 2 — the orchestrator now routes window_part values to
;;;     the correct leaf functions.
;;;
;;; Loads the Scheme file via eval-scheme, then reads back
;;; `test-results` (list of (NAME STATUS) pairs) and reports each via
;;; princ.

(princ "=== m19-fixes test suite ===\n")

(let* ((dir (file-name-directory (or load-file-name default-directory)))
       (corpus (expand-file-name "test-m19-fixes.scm" dir)))
  (condition-case err
      (eval-scheme
       (format "(primitive-load %S)" corpus))
    (error (princ (format "M19F-CORPUS-LOAD-ERROR: %S\n" err)))))

(let ((results (condition-case e
                   (eval-scheme "(reverse test-results)")
                 (error (princ (format "M19F-READBACK-ERROR: %S\n" e)) '())))
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
