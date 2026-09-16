;;; test-m13-store.el --- M13 imp-2 test suite for kbd-buffer-store-event!
;;;
;;; Wraps test/keyboard/test-m13-store.scm — the Scheme test corpus
;;; for the (emacs kbd-buffer) port of C kbd_buffer_store_buffered_event:
;;; the already-holding guard, the ASCII modifier fold, the quit-char
;;; branch (hold-quit copy + focus/handle_interrupt), the stop-char
;;; branch (stubbed sys_suspend), the ring append + last-slot silent
;;; drop, and the while-no-input quit-flag check (including the
;;; selection-request symbol trap).  See docs/m13-plan.org §imp-2.
;;;
;;; Loads the Scheme file via eval-scheme, then reads back
;;; `test-results` (list of (NAME STATUS) pairs) and reports each
;;; via princ.  Same harness as test-m13-shims.el (M13 imp-1).

(princ "=== m13-store test suite ===\n")

;; M38 imp-3: load the shared input-state reset (brief.org §8.2) and run
;; the corpus inside unwind-protect, so the C/Scheme defaults are
;; restored on the normal AND the non-local exit path (brief.org §8.1).
;; This corpus writes last-event-frame (brief.org §5.1).
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
       (corpus (expand-file-name "test-m13-store.scm" dir)))
  (condition-case err
      (eval-scheme
       (format "(primitive-load %S)" corpus))
    (error (princ (format "M13-STORE-CORPUS-LOAD-ERROR: %S\n" err)))))

;; Read each result back and report PASS/FAIL.
(let ((results (condition-case e
                   (eval-scheme "(reverse test-results)")
                 (error (princ (format "M13-STORE-READBACK-ERROR: %S\n" e)) '())))
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
