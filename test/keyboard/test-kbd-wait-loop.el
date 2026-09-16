;;; test-kbd-wait-loop.el --- M11 imp-2 test suite for the Scheme
;;; wait-loop port ((emacs kbd-buffer))
;;;
;;; Wraps test/keyboard/test-kbd-wait-loop.scm — the Scheme test
;;; corpus for kbd-buffer-get-event / noninteractive-fast-path? (the
;;; prelude + wait loop + post-wait prologue of C kbd_buffer_get_event,
;;; src/keyboard.c:4965-5127).  See docs/m11-plan.org §imp-2.
;;;
;;; Loads the Scheme file via eval-scheme, then reads back
;;; `test-results` (list of (NAME STATUS) pairs) and reports each
;;; via princ.  Same harness as test-kbd-escape-shims.el (M11 imp-1.3).

(princ "=== kbd-wait-loop test suite ===\n")

;; M38 imp-3: shared input-state reset (brief.org §8.2); unwind-protect so
;; the defaults are restored on the normal and the non-local exit path
;; (brief.org §8.1).  This corpus writes last-event-device and
;; last-event-frame (brief.org §5.1).
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
       (corpus (expand-file-name "test-kbd-wait-loop.scm" dir)))
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
  )
  (condition-case e
      (m38-imp3-reset-input-state m38-imp3-entry-buffer)
    (error (princ (format "M38-IMP3-RESET-ERROR: %S\n" e))))))
