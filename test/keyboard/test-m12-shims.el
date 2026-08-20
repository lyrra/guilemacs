;;; test-m12-shims.el --- M12 imp-1 test suite for the C shim DEFUNs
;;;
;;; Wraps test/keyboard/test-m12-shims.scm — the Scheme test corpus
;;; for the 8 imp-1 C shims in src/keyboard.c (getctag prompt-tag
;;; save/set, single-kboard flag, kboard side-queue tail-append,
;;; rec-free end-time deadline, and the tty keyboard-coding decode
;;; trio).  See docs/m12-plan.org §imp-1.
;;;
;;; Loads the Scheme file via eval-scheme, then reads back
;;; `test-results` (list of (NAME STATUS) pairs) and reports each
;;; via princ.  Same harness as test-kbd-wait-loop.el (M11 imp-2).

(princ "=== m12-shims test suite ===\n")

;; Run the Scheme test corpus.  Populates test-results in the
;; (guile-user) module.  Resolve the corpus path from load-file-name so
;; it works both from the repo root (run-all-tests.el) and from the
;; harness, which loads this file with CWD=test/.
(let* ((dir (file-name-directory (or load-file-name default-directory)))
       (corpus (expand-file-name "test-m12-shims.scm" dir)))
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
