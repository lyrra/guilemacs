;;; test-m24-input-poll.el --- M24 (emacs input-poll) test suite.
;;;
;;; Covers the M24 polling-policy cutover (brief.org M24): the new
;;; --atimer-poll-restart! C shim in src/keyboard.c and the Scheme
;;; body (emacs input-poll) start-polling! that replaces the old C
;;; start_polling body.
;;;
;;; Wraps test/keyboard/test-m24-input-poll.scm -- the Scheme test
;;; corpus.  Loads the Scheme file via eval-scheme, then reads back
;;; `test-results` (list of (NAME STATUS) pairs) and reports each via
;;; princ.  Same harness as test-m20-menu-prompt.el.  See brief.org M24.

(princ "=== m24-input-poll test suite ===\n")

;; Run the Scheme test corpus.  Populates test-results in the
;; (guile-user) module.  Resolve the corpus path from load-file-name so
;; it works both from the repo root and from the harness, which loads
;; this file with CWD=test/.
(let* ((dir (file-name-directory (or load-file-name default-directory)))
       (corpus (expand-file-name "test-m24-input-poll.scm" dir)))
  (condition-case err
      (eval-scheme
       (format "(primitive-load %S)" corpus))
    (error (princ (format "M24IP-CORPUS-LOAD-ERROR: %S\n" err)))))

;; Read each result back and report PASS/FAIL.
(let ((results (condition-case e
                   (eval-scheme "(reverse test-results)")
                 (error (princ (format "M24IP-READBACK-ERROR: %S\n" e)) '())))
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
