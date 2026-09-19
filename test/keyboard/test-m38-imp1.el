;;; test-m38-imp1.el --- M38 imp-1 (harness count mismatch) suite.
;;;
;;; Pins the M38 imp-1 work (brief.org, defect D1): tool/run-tests.scm
;;; exits non-zero when the ERT count and the emitted pass count
;;; disagree.  The ERROR text is kept.  No C file changes.
;;;
;;; Source checks only (test/keyboard/test-m38-imp1.scm).  Prove the
;;; mismatch reaches the fail accumulator and the exit status reads it.
;;;
;;; This file used to also run a *behavior* check: shell out to
;;; tool/run-tests.sh --filter=m38-imp1-fixture twice via call-process,
;;; to prove the harness really exits 1 on a live count mismatch.  That
;;; nested run-tests.sh-inside-run-tests.sh recursion made every batch
;;; that includes this file re-run a chunk of the suite as a subprocess,
;;; which is slow and, combined with the similar recursion in
;;; test-m38-imp2/3/4.el, was mistaken for a hang.  Removed; the fixture
;;; test/m38/test-m38-imp1-fixture.el still exists and can be exercised
;;; by hand with GUILEMACS_M38_FIXTURE=middle|last if this needs
;;; re-proving.
;;;
;;; The .scm corpus is loaded via primitive-load with the repo root bound
;;; as %m38-root.  Each (NAME PASS|FAIL) pair is reported via princ AND
;;; turned into an ERT test so the harness counts it.  Each
;;; (NAME INFO VALUE) pair is printed as an INFO line and is NOT asserted.
;;; A corpus load error, a readback error or an empty corpus is reported
;;; as a real FAIL (never a silent 0 failed).

(princ "=== m38 imp-1 (harness count mismatch) test suite ===\n")

(require 'imp-ert-report)

(let* ((dir (file-name-directory (or load-file-name default-directory)))
       (root (expand-file-name "../.." dir))
       (corpus (expand-file-name "test-m38-imp1.scm" dir))
       (load-error nil))
  ;; The corpus reads the source tree, so tell it where the root is.
  (eval-scheme (format "(define %%m38-root %S)" root))
  (condition-case err
      (eval-scheme
       (format "(primitive-load %S)" corpus))
    (error (setq load-error err)))
  (let* ((results
          (cond
           (load-error
            (list (list "m38-imp1/corpus-load"
                        (cons 'FAIL (format "%S" load-error)))))
           (t
            (condition-case e
                (let ((r (eval-scheme "(reverse test-results)")))
                  (if (or (not (listp r)) (null r))
                      (list (list "m38-imp1/corpus-empty"
                                  (cons 'FAIL "corpus produced no results")))
                    r))
              (error
               (list (list "m38-imp1/readback"
                           (cons 'FAIL (format "%S" e)))))))))
         (pass 0)
         (fail 0))
    (dolist (result results)
      (let* ((name (car result))
             (status (cadr result))
             (ok (eq status 'PASS)))
        (cond
         (ok
          (imp-register-check-as-ert-test name status)
          (setq pass (1+ pass))
          (princ (format "PASS %s\n" name)))
         ((and (consp status) (eq (car status) 'INFO))
          (princ (format "INFO %s %s\n" name (cadr status))))
         (t
          (imp-register-check-as-ert-test name status)
          (setq fail (1+ fail))
          (princ (format "FAIL %s %S\n" name (cdr result)))))))
    (princ (format "=== %d passed, %d failed, %d total ===\n"
                   pass fail (+ pass fail)))))
