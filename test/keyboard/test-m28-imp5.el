;;; test-m28-imp5.el --- M28 imp-5 family 2 (--ie-kind-from-name reclaim) suite.
;;;
;;; Verifies the M28 imp-5 family-2 reclaim in src/keyboard.c (brief.org):
;;; the --ie-kind-from-name double-hop DEFUN is deleted and its Scheme
;;; callers now call the (emacs lispy-position) port directly; the other
;;; 19 --ie- shims and the 4 --set-ie- write companions stay C with a
;;; recorded reason (docs/kb.org family-2 decision audit).
;;;
;;; Wraps test/keyboard/test-m28-imp5.scm — the Scheme test corpus.
;;; Loads the Scheme file via eval-scheme, then reads back `test-results`
;;; (list of (NAME STATUS) pairs) and reports each via princ.  Same
;;; harness as test-m28-imp1.el.

(princ "=== m28-imp5 family-2 reclaim test suite ===\n")

(let* ((dir (file-name-directory (or load-file-name default-directory)))
       (corpus (expand-file-name "test-m28-imp5.scm" dir)))
  (condition-case err
      (eval-scheme
       (format "(primitive-load %S)" corpus))
    (error (princ (format "M28I5-CORPUS-LOAD-ERROR: %S\n" err)))))

(let ((results (condition-case e
                   (eval-scheme "(reverse test-results)")
                 (error (princ (format "M28I5-READBACK-ERROR: %S\n" e)) '())))
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
