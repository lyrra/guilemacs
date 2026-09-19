;;; test-m38-imp2.el --- M38 imp-2 (comment-blind dropped-token scan) suite.
;;;
;;; Pins the M38 imp-2 work (brief.org, defect D2): the m29 dropped-token
;;; scan strips the C comments from src/keyboard.c before the token scan,
;;; so the HAVE_NS doc comment (added by M36 imp-4) is not a hit, and the
;;; match is strict (whole C identifier).  No C file changes.
;;;
;;; Source checks only (test/keyboard/test-m38-imp2.scm).  Prove the
;;; stripper rules, the positive/negative controls, the strict match, and
;;; the clean src/keyboard.c.
;;;
;;; This file used to also run a *behavior* check: shell out to
;;; tool/run-tests.sh --filter=m29-imp5 and --filter=m29-imp6 via
;;; call-process, to prove those filters exit 0 for real.  That nested
;;; run-tests.sh-inside-run-tests.sh recursion made any batch including
;;; this file re-run chunks of the suite as a subprocess -- slow, and
;;; combined with the similar (much larger, --filter=keyboard) recursion
;;; in test-m38-imp3/4.el, was mistaken for a hang.  Removed; run
;;; ./tool/run-tests.sh --filter=m29-imp5 (and m29-imp6) by hand if this
;;; needs re-proving.
;;;
;;; The .scm corpus is loaded via primitive-load with the repo root bound
;;; as %m38-root.  Each (NAME PASS|FAIL) pair is reported via princ AND
;;; turned into an ERT test so the harness counts it.  Each
;;; (NAME INFO VALUE) pair is printed as an INFO line and is NOT asserted.
;;; A corpus load error, a readback error or an empty corpus is reported
;;; as a real FAIL (never a silent 0 failed).

(princ "=== m38 imp-2 (comment-blind dropped-token scan) test suite ===\n")

(require 'imp-ert-report)

(let* ((dir (file-name-directory (or load-file-name default-directory)))
       (root (expand-file-name "../.." dir))
       (corpus (expand-file-name "test-m38-imp2.scm" dir))
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
            (list (list "m38-imp2/corpus-load"
                        (cons 'FAIL (format "%S" load-error)))))
           (t
            (condition-case e
                (let ((r (eval-scheme "(reverse test-results)")))
                  (if (or (not (listp r)) (null r))
                      (list (list "m38-imp2/corpus-empty"
                                  (cons 'FAIL "corpus produced no results")))
                    r))
              (error
               (list (list "m38-imp2/readback"
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
