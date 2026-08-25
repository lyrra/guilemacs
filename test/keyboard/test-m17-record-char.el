;;; test-m17-record-char.el --- M17 imp-3 test suite for the C-to-Scheme
;;; cutover of record_char and the --record-recent-keys-cmd-pseudo-event
;;; writer
;;;
;;; Wraps test/keyboard/test-m17-record-char.scm — the Scheme test corpus
;;; for the imp-3 dispatchers of record_char (into (emacs recent-keys)
;;; record-char) and --record-recent-keys-cmd-pseudo-event (into
;;; record-cmd-pseudo-event!).  See docs/m17-plan.org §imp-3 and
;;; brief.org.
;;;
;;; Loads the Scheme file via eval-scheme, then reads back
;;; `test-results` (list of (NAME STATUS) pairs) and reports each
;;; via princ.  Same harness as test-m16-help-echo.el (M16 imp-3).

(princ "=== m17-record-char test suite ===\n")

;; Run the Scheme test corpus.  Populates test-results in the
;; (guile-user) module.  Resolve the corpus path from load-file-name so
;; it works both from the repo root (run-all-tests.el) and from the
;; harness, which loads this file with CWD=test/.
(let* ((dir (file-name-directory (or load-file-name default-directory)))
       (corpus (expand-file-name "test-m17-record-char.scm" dir)))
  (condition-case err
      (eval-scheme
       (format "(primitive-load %S)" corpus))
    (error (princ (format "M17RC-CORPUS-LOAD-ERROR: %S\n" err)))))

;; Read each result back and report PASS/FAIL.
(let ((results (condition-case e
                   (eval-scheme "(reverse test-results)")
                 (error (princ (format "M17RC-READBACK-ERROR: %S\n" e)) '())))
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
