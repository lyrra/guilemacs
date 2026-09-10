;;; test-m28-imp5-f6.el --- M28 imp-5 family 6 (the tail) reclaim +
;;; stay-C audit.
;;;
;;; Verifies the M28 imp-5 family-6 reclaim commit in brief.org: the
;;; thin forwarders whose Scheme side is self-sufficient are deleted,
;;; the rest stay C (raw C state), and the recorded reasons live in
;;; docs/kb.org.
;;;
;;; Wraps test/keyboard/test-m28-imp5-f6.scm — the Scheme test corpus.
;;; Loads the Scheme file via eval-scheme, then reads back `test-results`
;;; (list of (NAME STATUS) pairs) and reports each via princ.  Same
;;; harness as test-m28-imp5-f5.el.

(princ "=== m28-imp5 family-6 (the tail) reclaim + audit test suite ===\n")

(let* ((dir (file-name-directory (or load-file-name default-directory)))
       (corpus (expand-file-name "test-m28-imp5-f6.scm" dir)))
  (condition-case err
      (eval-scheme
       (format "(primitive-load %S)" corpus))
    (error (princ (format "M28I5F6-CORPUS-LOAD-ERROR: %S\n" err)))))

(let ((results (condition-case e
                   (eval-scheme "(reverse test-results)")
                 (error (princ (format "M28I5F6-READBACK-ERROR: %S\n" e)) '())))
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
