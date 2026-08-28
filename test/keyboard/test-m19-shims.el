;;; test-m19-shims.el --- M19 imp-2 test suite for the menu/tab-bar/
;;; hscroll helper ports and shims in (emacs lispy-position)
;;;
;;; Wraps test/keyboard/test-m19-shims.scm — the Scheme test corpus for
;;; the 9 new imp-2 C shims in src/keyboard.c and the exported helper
;;; ports (coords-in-menu-bar-window?, line-number-mode-hscroll?,
;;; mouse-click-menu-bar-intercept, tab-bar-enrich-position,
;;; posn-at-x-y), plus the --mlp-dispatch retirement checks.  See
;;; docs/m19-plan.org §imp-2 and brief.org.
;;;
;;; Loads the Scheme file via eval-scheme, then reads back
;;; `test-results` (list of (NAME STATUS) pairs) and reports each via
;;; princ.  Same harness as test-m18-shims.el.

(princ "=== m19-shims test suite ===\n")

;; Run the Scheme test corpus.  Populates test-results in the
;; (guile-user) module.  Resolve the corpus path from load-file-name so
;; it works both from the repo root (run-all-tests.el) and from the
;; harness, which loads this file with CWD=test/.
(let* ((dir (file-name-directory (or load-file-name default-directory)))
       (corpus (expand-file-name "test-m19-shims.scm" dir)))
  (condition-case err
      (eval-scheme
       (format "(primitive-load %S)" corpus))
    (error (princ (format "M19S-CORPUS-LOAD-ERROR: %S\n" err)))))

;; Read each result back and report PASS/FAIL.
(let ((results (condition-case e
                   (eval-scheme "(reverse test-results)")
                 (error (princ (format "M19S-READBACK-ERROR: %S\n" e)) '())))
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
