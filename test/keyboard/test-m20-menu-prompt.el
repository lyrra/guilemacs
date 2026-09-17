;;; test-m20-menu-prompt.el --- M20 imp-1 + imp-2 test suite.
;;;
;;; imp-1: the four new C shims in src/keyboard.c
;;; (--rc-clear-echo-at-next-pause, --x-popup-menu-1,
;;; --store-kbd-macro-char, --menu-bar-hpos-vpos-raw).  imp-2: the
;;; Scheme bodies in (emacs menu-prompt) — record-menu-key,
;;; read-menu-command, read-char-x-menu-prompt.
;;;
;;; Wraps test/keyboard/test-m20-menu-prompt.scm — the Scheme test
;;; corpus.  Loads the Scheme file via eval-scheme, then reads back
;;; `test-results` (list of (NAME STATUS) pairs) and reports each via
;;; princ.  Same harness as test-m19-shims.el.  See docs/m20-plan.org
;;; and brief.org.

(princ "=== m20-menu-prompt test suite ===\n")

;; M38 imp-3: shared input-state reset (brief.org §8.2); unwind-protect so
;; the defaults are restored on the normal and the non-local exit path
;; (brief.org §8.1).  This corpus writes num-nonmacro-input-events and
;; grows the recent-keys ring (brief.org §5.1).  The ring has no clean
;; reset from elisp, so the m22-imp3 victim measures a delta instead
;; (Pattern B, brief.org §8.3).
(let ((dir (file-name-directory (or load-file-name default-directory))))
  (unless (fboundp 'm38-imp3-reset-input-state)
    (load (expand-file-name "test-m38-imp3-reset.el" dir) nil t)))
(let ((m38-imp3-entry-buffer (current-buffer)))
 (unwind-protect
  (progn
;; Run the Scheme test corpus.  Populates test-results in the
;; (guile-user) module.  Resolve the corpus path from load-file-name so
;; it works both from the repo root (run-all-tests.el) and from the
;; harness, which loads this file with CWD=test/.
(let* ((dir (file-name-directory (or load-file-name default-directory)))
       (corpus (expand-file-name "test-m20-menu-prompt.scm" dir)))
  (condition-case err
      (eval-scheme
       (format "(primitive-load %S)" corpus))
    (error (princ (format "M20MP-CORPUS-LOAD-ERROR: %S\n" err)))))

;; Read each result back and report PASS/FAIL.
(let ((results (condition-case e
                   (eval-scheme "(reverse test-results)")
                 (error (princ (format "M20MP-READBACK-ERROR: %S\n" e)) '())))
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
  )
  (condition-case e
      (m38-imp3-reset-input-state m38-imp3-entry-buffer)
    (error (princ (format "ERROR: M38-IMP3-RESET-ERROR %S\n" e))))))
