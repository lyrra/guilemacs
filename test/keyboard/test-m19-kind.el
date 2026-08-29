;;; test-m19-kind.el --- M19 imp-3: --ie-kind-from-name → Scheme lookup
;;;
;;; Wraps test/keyboard/test-m19-kind.scm — the corpus for the port of
;;; the event-kind symbol→integer lookup from the C --ie-kind-from-name
;;; body to (emacs lispy-position) ie-kind-from-name.  Loads the Scheme
;;; file via eval-scheme, then reads back `test-results` (list of
;;; (NAME STATUS) pairs) and reports each via princ.

(princ "=== m19-kind test suite ===\n")

(let* ((dir (file-name-directory (or load-file-name default-directory)))
       (corpus (expand-file-name "test-m19-kind.scm" dir)))
  (condition-case err
      (eval-scheme
       (format "(primitive-load %S)" corpus))
    (error (princ (format "M19K-CORPUS-LOAD-ERROR: %S\n" err)))))

(let ((results (condition-case e
                   (eval-scheme "(reverse test-results)")
                 (error (princ (format "M19K-READBACK-ERROR: %S\n" e)) '())))
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
