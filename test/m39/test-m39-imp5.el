;;; test-m39-imp5.el --- M39 close-out: one live process through all four ported modules.

;;; M39 ported src/process.c decision logic into four Scheme modules:
;;;   (emacs process-wait)      -- mod/emacs/process-wait.scm
;;;   (emacs process-io)        -- mod/emacs/process-io.scm
;;;   (emacs process-accessors) -- mod/emacs/process-accessors.scm
;;;   (emacs process-signal)    -- mod/emacs/process-signal.scm
;;;
;;; test-m39-imp1.el through test-m39-imp4(-e2e).el each prove one module's
;;; functions individually.  This close-out corpus instead drives ONE real
;;; subprocess through its whole lifecycle, calling into all four modules
;;; in the order a real caller would -- configure it, talk to it, wait for
;;; its output, signal it, confirm it is gone -- so the suite has one place
;;; that shows the ported API working together, not just piece by piece.
;;; It doubles as a usage example for the four modules.
;;;
;;; Uses a real "cat" subprocess: it echoes back whatever is written to its
;;; stdin, so accept-process-output has real output to wait for.  Every
;;; step here is exercised through the same public elisp subrs the C side
;;; calls (process-send-string, accept-process-output, signal-process,
;;; ...); none of the Scheme functions are called directly, because the
;;; point is to prove the C-to-Scheme wiring end to end, the same as
;;; process.c's real callers do.

(princ "=== m39 imp-5 close-out: process lifecycle suite ===\n")

(require 'imp-ert-report)

(defmacro m39-imp5--check (name &rest body)
  "Run BODY, register NAME as a real ERT test on whether it returned
non-nil, and print PASS/FAIL.  A signal escaping BODY counts as FAIL and
is reported, not silently swallowed."
  (declare (indent 1))
  `(let ((ok (condition-case err
                 (progn ,@body)
               (error (princ (format "  (%s signaled: %S)\n" ,name err))
                      nil))))
     (imp-register-bool-as-ert-test ,name ok)
     (princ (format "%s %s\n" (if ok "PASS" "FAIL") ,name))))

(let* ((buf (generate-new-buffer " *m39-imp5-cat*"))
       (proc (condition-case err
                 (start-process "m39-imp5-cat" buf "cat")
               (error (princ (format "INFO m39/imp5/no-cat %S\n" err)) nil))))
  (unwind-protect
      (if (not (processp proc))
          (princ "INFO m39/imp5/skipped no cat(1) subprocess available\n")

        ;;; --- 1. process-accessors: configure the process ---------------
        (m39-imp5--check "m39/imp5/accessors/query-on-exit-flag-roundtrip"
          (set-process-query-on-exit-flag proc nil)
          (not (process-query-on-exit-flag proc)))
        (m39-imp5--check "m39/imp5/accessors/plist-roundtrip"
          (set-process-plist proc '(:m39 imp5))
          (equal (process-plist proc) '(:m39 imp5)))
        (m39-imp5--check "m39/imp5/accessors/coding-system-cons"
          (consp (process-coding-system proc)))
        (m39-imp5--check "m39/imp5/accessors/mark-is-marker-in-buffer"
          (let ((mk (process-mark proc)))
            (and (markerp mk) (eq (marker-buffer mk) buf))))
        (m39-imp5--check "m39/imp5/accessors/buffer-is-cat-buffer"
          (eq (process-buffer proc) buf))

        ;;; --- 2. process-io: write to the process ------------------------
        (m39-imp5--check "m39/imp5/io/send-string-live"
          (process-send-string proc "m39-imp5-roundtrip\n")
          t)
        (m39-imp5--check "m39/imp5/io/send-region-live"
          (with-temp-buffer
            (insert "m39-imp5-region\n")
            (process-send-region proc (point-min) (point-max)))
          t)

        ;;; --- 3. process-wait: wait for cat to echo it back --------------
        ;; Poll accept-process-output in small steps rather than one long
        ;; wait, so a slow/loaded machine still gets multiple chances
        ;; without ever blocking longer than ~2s total.
        (let ((got nil))
          (dotimes (_ 20)
            (unless got
              (accept-process-output proc 0 100)
              (with-current-buffer buf
                (goto-char (point-min))
                (setq got (and (search-forward "m39-imp5-roundtrip" nil t)
                               (progn (goto-char (point-min))
                                      (search-forward "m39-imp5-region" nil t)))))))
          (m39-imp5--check "m39/imp5/wait/echo-arrived" got))

        ;;; --- 4. process-signal: stop, continue, then terminate ----------
        (m39-imp5--check "m39/imp5/signal/stop-returns-process"
          (eq (stop-process proc) proc))
        (m39-imp5--check "m39/imp5/signal/continue-returns-process"
          (eq (continue-process proc) proc))
        (m39-imp5--check "m39/imp5/signal/still-running-before-kill"
          (eq (process-status proc) 'run))
        (m39-imp5--check "m39/imp5/signal/kill-process-no-error"
          (kill-process proc)
          t)
        ;; Give the OS a moment to reap it before checking status.
        (dotimes (_ 20)
          (when (eq (process-status proc) 'run)
            (accept-process-output proc 0 50)))
        (m39-imp5--check "m39/imp5/signal/status-not-run-after-kill"
          (not (eq (process-status proc) 'run)))
        ;; Signaling the now-dead process does NOT raise a Lisp error here:
        ;; it returns the raw kill(2) result, -1 (ESRCH, no such process).
        ;; Worth pinning as behavior a caller needs to know -- easy to
        ;; assume (wrongly) that this signals, since dead-process access
        ;; errors elsewhere in Emacs.  Not covered by test-m39-imp4-e2e.el,
        ;; which only ever signals a live process (this Emacs's own pid)
        ;; or a live pipe.
        (m39-imp5--check "m39/imp5/signal/signal-after-death-returns-neg1"
          (eql (signal-process proc 0) -1)))

    (when (processp proc) (ignore-errors (delete-process proc)))
    (when (buffer-live-p buf) (kill-buffer buf))))

;;; --- 5. The corpus is registered in run-tests.scm ---------------------
;; The one piece of infrastructure bookkeeping worth keeping from the old
;; audit style: prove the harness actually runs this file, not a claim
;; about C source shape.
(let ((rt (with-temp-buffer
            (insert-file-contents
             (expand-file-name "../../tool/run-tests.scm"
                                (file-name-directory (or load-file-name
                                                          default-directory))))
            (buffer-string))))
  (m39-imp5--check "m39/imp5/registered-in-run-tests.scm"
    (and (string-match-p "\"test/m39/test-m39-imp5\\.el\"" rt) t)))

(princ "=== m39 imp-5 close-out suite done ===\n")
