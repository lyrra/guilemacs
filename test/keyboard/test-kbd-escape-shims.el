;;; test-kbd-escape-shims.el --- M11 imp-1.3 test suite for the
;;; kbd-buffer C-escape shims
;;;
;;; Wraps test/keyboard/test-kbd-escape-shims.scm — the Scheme test
;;; corpus for the 15 imp-1.3 C-escape shims (quit/read-char,
;;; wait-reading-process-output, activate-menubar-hook, multibyte
;;; decode, noninteractive-getchar, mouse-position-hook,
;;; text-conversion trio, keyboard-hold pair, X selection-request
;;; pair, rc kbp write-back, gobble-input).  See
;;; docs/m11-plan.org §imp-1.3 for context.
;;;
;;; Loads the Scheme file via eval-scheme, then reads back
;;; `test-results` (list of (NAME STATUS) pairs) and reports each
;;; via princ.  Same harness as test-menu-bar-items.el (M10).

(princ "=== kbd-escape-shims test suite ===\n")

;; Run the Scheme test corpus.  Populates test-results in the
;; (guile-user) module.
(eval-scheme
 "(primitive-load \"test/keyboard/test-kbd-escape-shims.scm\")")

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
