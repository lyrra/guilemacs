;;; test-m28-imp5-f3.el --- M28 imp-5 family 3 (--frame- / --window- audit).
;;;
;;; Verifies the M28 imp-5 family-3 decision-audit commit in brief.org:
;;; all 12 --frame- and 4 --window- shims stay C (raw C state), and the
;;; --frame-relative-event-pos write companion stays C too (defers to
;;; M30).  Zero reclaims: no C DEFUN is deleted, no Scheme caller
;;; changes.  The recorded reasons live in docs/kb.org.
;;;
;;; Wraps test/keyboard/test-m28-imp5-f3.scm — the Scheme test corpus.
;;; Loads the Scheme file via eval-scheme, then reads back `test-results`
;;; (list of (NAME STATUS) pairs) and reports each via princ.  Same
;;; harness as test-m28-imp5.el.

(princ "=== m28-imp5 family-3 --frame- / --window- audit test suite ===\n")

(let* ((dir (file-name-directory (or load-file-name default-directory)))
       (corpus (expand-file-name "test-m28-imp5-f3.scm" dir)))
  (condition-case err
      (eval-scheme
       (format "(primitive-load %S)" corpus))
    (error (princ (format "M28I5F3-CORPUS-LOAD-ERROR: %S\n" err)))))

(let ((results (condition-case e
                   (eval-scheme "(reverse test-results)")
                 (error (princ (format "M28I5F3-READBACK-ERROR: %S\n" e)) '())))
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
