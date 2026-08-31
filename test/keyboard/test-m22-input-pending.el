;;; test-m22-input-pending.el --- M22 imp-1 parity test suite.
;;;
;;; imp-1: get-input-pending! port of C get_input_pending (used by
;;; detect_input_pending and friends) and the recent-keys ring resize
;;; port of C update_recent_keys (used by lossage-size).
;;;
;;; Wraps test/keyboard/test-m22-input-pending.scm — the Scheme test
;;; corpus.  Loads the Scheme file via eval-scheme, then reads back
;;; `test-results` (list of (NAME STATUS) pairs) and reports each via
;;; princ.  Same harness as test-m21-read-key-sequence.el.  See
;;; docs/m22-plan.org §imp-1 and brief.org.

(princ "=== m22 input-pending test suite ===\n")

;; Run the Scheme test corpus.  Populates test-results in the
;; (guile-user) module.  Resolve the corpus path from load-file-name so
;; it works both from the repo root (run-all-tests.el) and from the
;; harness, which loads this file with CWD=test/.
(let* ((dir (file-name-directory (or load-file-name default-directory)))
       (corpus (expand-file-name "test-m22-input-pending.scm" dir)))
  (condition-case err
      (eval-scheme
       (format "(primitive-load %S)" corpus))
    (error (princ (format "M22-CORPUS-LOAD-ERROR: %S\n" err)))))

;; Read each result back and report PASS/FAIL.
(let ((results (condition-case e
                   (eval-scheme "(reverse test-results)")
                 (error (princ (format "M22-READBACK-ERROR: %S\n" e)) '())))
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
