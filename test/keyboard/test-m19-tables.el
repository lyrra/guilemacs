;;; test-m19-tables.el --- M19 imp-4: surviving key-name tables remain readable
;;;
;;; Wraps test/keyboard/test-m19-tables.scm — the corpus that proves
;;; the five accessor-backed key-name tables in src/keyboard.c are
;;; still readable after imp-4 deletes the dead lispy_kana_keys and
;;; lispy_drag_n_drop_names tables, and that the wheel_syms cache is
;;; still sized 4 after the literal swap.  Loads the Scheme file via
;;; eval-scheme, then reads back `test-results` (list of (NAME STATUS)
;;; pairs) and reports each via princ.

(princ "=== m19-tables test suite ===\n")

(let* ((dir (file-name-directory (or load-file-name default-directory)))
       (corpus (expand-file-name "test-m19-tables.scm" dir)))
  (condition-case err
      (eval-scheme
       (format "(primitive-load %S)" corpus))
    (error (princ (format "M19T-CORPUS-LOAD-ERROR: %S\n" err)))))

(let ((results (condition-case e
                   (eval-scheme "(reverse test-results)")
                 (error (princ (format "M19T-READBACK-ERROR: %S\n" e)) '())))
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
