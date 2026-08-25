;;; test-m16-help-echo.el --- M16 imp-3 test suite for the C-to-Scheme
;;; cutover of the help-echo functions
;;;
;;; Wraps test/keyboard/test-m16-help-echo.scm — the Scheme test corpus
;;; for the imp-3 dispatchers of show_help_echo, gen_help_event, and
;;; kbd_buffer_store_help_event.  See docs/m16-plan.org §imp-3 and
;;; brief.org.
;;;
;;; Loads the Scheme file via eval-scheme, then reads back
;;; `test-results` (list of (NAME STATUS) pairs) and reports each
;;; via princ.  Same harness as test-m16-bodies.el (M16 imp-2).

(princ "=== m16-help-echo test suite ===\n")

;; Run the Scheme test corpus.  Populates test-results in the
;; (guile-user) module.  Resolve the corpus path from load-file-name so
;; it works both from the repo root (run-all-tests.el) and from the
;; harness, which loads this file with CWD=test/.
(let* ((dir (file-name-directory (or load-file-name default-directory)))
       (corpus (expand-file-name "test-m16-help-echo.scm" dir)))
  (condition-case err
      (eval-scheme
       (format "(primitive-load %S)" corpus))
    (error (princ (format "M16H-CORPUS-LOAD-ERROR: %S\n" err)))))

;; Read each result back and report PASS/FAIL.
(let ((results (condition-case e
                   (eval-scheme "(reverse test-results)")
                 (error (princ (format "M16H-READBACK-ERROR: %S\n" e)) '())))
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
