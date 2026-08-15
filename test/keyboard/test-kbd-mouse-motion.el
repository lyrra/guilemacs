;;; test-kbd-mouse-motion.el --- M11 imp-4 test suite for the Scheme
;;; mouse-motion fallback port ((emacs kbd-buffer) mouse-motion-synthesize!)
;;;
;;; Wraps test/keyboard/test-kbd-mouse-motion.scm — the Scheme test
;;; corpus for the imp-4 DEFUNs and the pure movement-construction
;;; helpers (--frame-last-mouse-device, --make-lispy-position nil
;;; tolerance, --make-scroll-bar-position shape).  The full synthesize
;;; path is not reachable on a termcap batch build (no mouse / no
;;; mouse_position_hook), so these are the CI-safe assertions.  See
;;; brief.org §imp-4 and docs/m11-plan.org §imp-4.
;;;
;;; Loads the Scheme file via eval-scheme, then reads back
;;; `test-results` (list of (NAME STATUS) pairs) and reports each
;;; via princ.  Same harness as test-kbd-dispatch.el (M11 imp-3).

(princ "=== kbd-mouse-motion test suite ===\n")

;; Run the Scheme test corpus.  Populates test-results in the
;; (guile-user) module.  Resolve the corpus path from load-file-name so
;; it works both from the repo root (run-all-tests.el) and from the
;; harness, which loads this file with CWD=test/.
(let* ((dir (file-name-directory (or load-file-name default-directory)))
       (corpus (expand-file-name "test-kbd-mouse-motion.scm" dir)))
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
