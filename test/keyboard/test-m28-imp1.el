;;; test-m28-imp1.el --- M28 imp-1 (reclaim 5 residual M8/M10 shims) suite.
;;;
;;; Verifies the M28 imp-1 reclaim in src/keyboard.c (brief.org M28
;;; imp-1): the 3 dispatcher DEFUNs are deleted and their Scheme callers
;;; in (emacs lispy-event) now call the (emacs lispy-position) ports
;;; directly; the 2 rc shims stay C with a recorded reason.
;;;
;;; Wraps test/keyboard/test-m28-imp1.scm — the Scheme test corpus.
;;; Loads the Scheme file via eval-scheme, then reads back `test-results`
;;; (list of (NAME STATUS) pairs) and reports each via princ.  Same
;;; harness as test-m19-shims.el.

(princ "=== m28-imp1 reclaim test suite ===\n")

(let* ((dir (file-name-directory (or load-file-name default-directory)))
       (corpus (expand-file-name "test-m28-imp1.scm" dir)))
  (condition-case err
      (eval-scheme
       (format "(primitive-load %S)" corpus))
    (error (princ (format "M28I1-CORPUS-LOAD-ERROR: %S\n" err)))))

(let ((results (condition-case e
                   (eval-scheme "(reverse test-results)")
                 (error (princ (format "M28I1-READBACK-ERROR: %S\n" e)) '())))
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
