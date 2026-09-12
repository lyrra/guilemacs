;;; test-m31-imp2-reporting.el --- M31 imp-2: reporting guards.
;;;
;;; cr.org (M31 imp-2 review) found no code defect; its findings were
;;; in reporting.  This corpus pins the two tracked-file invariants the
;;; review checked, so a later edit cannot silently break them:
;;; the M31 imp-2 .el file stays registered after the M31 imp-1 row in
;;; tool/run-tests.scm, and test/keyboard/test-m23-imp5.el keeps
;;; auto-save-interval out of its source-scan list while keeping
;;; (auto-save-interval 300) in gm5-cases.
;;;
;;; Wraps test/keyboard/test-m31-imp2-reporting.scm -- the Scheme proof
;;; corpus.  Loads the Scheme file via eval-scheme, then reads back
;;; `test-results' (list of (NAME STATUS) pairs).  Each pair is
;;; reported via princ AND turned into an ERT test so the harness counts
;;; it.  A corpus load error, a readback error or an empty corpus is a
;;; real FAIL (never a silent 0 failed).  Same shape as test-m31-imp2.el.

(princ "=== m31 imp-2 reporting guards test suite ===\n")

(let* ((dir (file-name-directory (or load-file-name default-directory)))
       (root (expand-file-name "../.." dir))
       (corpus (expand-file-name "test-m31-imp2-reporting.scm" dir))
       (load-error nil))
  ;; The corpus reads the build tree, so tell it where the repo root is.
  (eval-scheme (format "(define %%m31-root %S)" root))
  (condition-case err
      (eval-scheme
       (format "(primitive-load %S)" corpus))
    (error (setq load-error err)))
  (let* ((results
          (cond
           (load-error
            (list (list "m31-imp2r/corpus-load"
                        (cons 'FAIL (format "%S" load-error)))))
           (t
            (condition-case e
                (let ((r (eval-scheme "(reverse test-results)")))
                  (if (or (not (listp r)) (null r))
                      (list (list "m31-imp2r/corpus-empty"
                                  (cons 'FAIL "corpus produced no results")))
                    r))
              (error
               (list (list "m31-imp2r/readback"
                           (cons 'FAIL (format "%S" e)))))))))
         (pass 0)
         (fail 0))
    (dolist (result results)
      (let* ((name (car result))
             (status (cadr result))
             (ok (eq status 'PASS)))
        ;; Define the ERT test so the harness metric sees it.
        (eval `(ert-deftest ,(intern (format "m31-imp2r/%s" name)) ()
                 (should (eq ',status 'PASS))))
        (if ok
            (progn
              (setq pass (1+ pass))
              (princ (format "PASS %s\n" name)))
          (setq fail (1+ fail))
          (princ (format "FAIL %s %S\n" name (cdr result))))))
    (princ (format "=== %d passed, %d failed, %d total ===\n"
                   pass fail (+ pass fail)))))
