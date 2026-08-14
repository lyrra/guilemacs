;;; test-kbd-dispatch.el --- M11 imp-3 test suite for the Scheme
;;; event-kind dispatch port ((emacs kbd-buffer) dispatch-event!)
;;;
;;; Wraps test/keyboard/test-kbd-dispatch.scm — the Scheme test corpus
;;; for the C `switch (event->kind)` block (src/keyboard.c:5195-5480).
;;; See docs/m11-plan.org §imp-3 and brief.org.
;;;
;;; Loads the Scheme file via eval-scheme, then reads back
;;; `test-results` (list of (NAME STATUS) pairs) and reports each
;;; via princ.  Same harness as test-kbd-wait-loop.el (M11 imp-2).

(princ "=== kbd-dispatch test suite ===\n")

;; Run the Scheme test corpus.  Populates test-results in the
;; (guile-user) module.  Resolve the corpus path from load-file-name so
;; it works both from the repo root (run-all-tests.el) and from the
;; harness, which loads this file with CWD=test/.
(let* ((dir (file-name-directory (or load-file-name default-directory)))
       (corpus (expand-file-name "test-kbd-dispatch.scm" dir)))
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
