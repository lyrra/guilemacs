;;; test-m26-imp2-quit-throw.el --- M26 imp-2 (emacs interrupt) test suite.
;;;
;;; Covers the M26 imp-2 cutover (brief.org M26): the from_signal == false
;;; body of C quit_throw_to_read_char now lives in (emacs interrupt) as
;;; quit-throw-to-read-char.
;;;
;;; Wraps test/keyboard/test-m26-imp2-quit-throw.scm -- the Scheme
;;; test corpus.  Loads the Scheme file via eval-scheme, then reads back
;;; `test-results` (list of (NAME STATUS) pairs) and reports each via
;;; princ.  Same harness as test-m26-imp1-suspend-emacs.el.  See brief.org
;;; M26 imp-2.

(princ "=== m26-imp2-quit-throw test suite ===\n")

;; Run the Scheme test corpus.  Populates test-results in the
;; (guile-user) module.  Resolve the corpus path from load-file-name so
;; it works both from the repo root and from the harness, which loads
;; this file with CWD=test/.
(let* ((dir (file-name-directory (or load-file-name default-directory)))
       (corpus (expand-file-name "test-m26-imp2-quit-throw.scm" dir)))
  (condition-case err
      (eval-scheme
       (format "(primitive-load %S)" corpus))
    (error (princ (format "M26QT-CORPUS-LOAD-ERROR: %S\n" err)))))

;; Read each result back and report PASS/FAIL.
(let ((results (condition-case e
                   (eval-scheme "(reverse test-results)")
                 (error (princ (format "M26QT-READBACK-ERROR: %S\n" e)) '())))
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
