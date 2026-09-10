;;; test-m12-umm.el --- M12 imp-1+imp-2 test suite for the used-mouse-menu flag
;;;
;;; Wraps test/keyboard/test-m12-umm.scm — the Scheme test corpus for
;;; the used-mouse-menu-flag field of <rc-state> (brief.org M12 imp-1
;;; + imp-2): the main-queue install path, the X-menu read block, the
;;; rc-exit! two-value contract, and the three wrong-kboard -2 exits of
;;; read-char-main (the drain path itself lives in
;;; ertest-read-char.el).
;;;
;;; Loads the Scheme file via eval-scheme, then reads back
;;; `test-results` (list of (NAME STATUS) pairs) and reports each
;;; via princ.  Same harness as test-main-queue.el (M12 imp-3).

(princ "=== M12 imp-1+imp-2 used-mouse-menu flag suite ===\n")

;; Run the Scheme test corpus.  Populates test-results in the
;; (guile-user) module.  Resolve the corpus path from load-file-name so
;; it works both from the repo root (run-all-tests.el) and from the
;; harness, which loads this file with CWD=test/.
(let* ((dir (file-name-directory (or load-file-name default-directory)))
       (corpus (expand-file-name "test-m12-umm.scm" dir)))
  (eval-scheme
   (format "(primitive-load %S)" corpus)))

;; Read each result back and report PASS/FAIL.
(let ((results (eval-scheme "(reverse test-results)"))
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
