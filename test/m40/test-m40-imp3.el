;;; test-m40-imp3.el --- M40 imp-3 (residual Group A accessors) suite.
;;;
;;; Pins the M40 imp-3 port (brief.org): the decision of two residual
;;; src/process.c Group A accessors moved into (emacs process-accessors)
;;; -- process-tty-name (a multi-slot read plus the stdin / stdout /
;;; stderr stream test) and process-inherit-coding-system-flag (a plain
;;; slot read).  The struct slots stay C; the module reads them through
;;; the table-driven bridge --process-ref (the new read rows tty_name,
;;; stderrproc, pty_in, pty_out).  The two C DEFUNs are removed.  The
;;; other 10 residual Group A names stay C.
;;;
;;; Wraps test/m40/test-m40-imp3.scm -- the Scheme corpus.  This file
;;; creates the live processes the corpus reads (a pty process and a
;;; pipe process), binds the repo root as %m40-root, and loads the
;;; Scheme file via eval-scheme.  Each (NAME PASS|FAIL) pair is reported
;;; via princ AND turned into an ERT test so the harness counts it.  A
;;; corpus load error, a readback error or an empty corpus is reported
;;; as a real FAIL.  When no command is available the corpus reports the
;;; runtime checks as INFO (an environment gap, not a code regression).

(princ "=== m40 imp-3 (residual Group A accessors) test suite ===\n")

(require 'imp-ert-report)

(let* ((dir (file-name-directory (or load-file-name default-directory)))
       (root (expand-file-name "../.." dir))
       (corpus (expand-file-name "test-m40-imp3.scm" dir))
       (cat (executable-find "cat"))
       (outbuf (and cat (get-buffer-create " *m40-imp3-out*")))
       (pty (and cat
                 (condition-case nil
                     (make-process :name "m40-imp3-pty" :command (list cat)
                                   :connection-type 'pty
                                   :buffer outbuf :noquery t)
                   (error nil))))
       (pipe (and cat
                  (condition-case nil
                      (make-process :name "m40-imp3-pipe" :command (list cat)
                                    :connection-type 'pipe
                                    :buffer outbuf :noquery t)
                    (error nil))))
       (load-error nil))
  ;; The corpus reads the build tree, so tell it where the root is.
  (eval-scheme (format "(define %%m40-root %S)" root))
  (condition-case err
      (eval-scheme
       (format "(primitive-load %S)" corpus))
    (error (setq load-error err)))
  (let* ((results
          (cond
           (load-error
            (list (list "m40-imp3/corpus-load"
                        (cons 'FAIL (format "%S" load-error)))))
           (t
            (condition-case e
                (let ((r (eval-scheme "(reverse test-results)")))
                  (if (or (not (listp r)) (null r))
                      (list (list "m40-imp3/corpus-empty"
                                  (cons 'FAIL "corpus produced no results")))
                    r))
              (error
               (list (list "m40-imp3/readback"
                           (cons 'FAIL (format "%S" e)))))))))
         (pass 0)
         (fail 0))
    (dolist (result results)
      (let* ((name (car result))
             (status (cadr result))
             (ok (eq status 'PASS)))
        (cond
         (ok
          (imp-register-check-as-ert-test (format "m40-imp3/%s" name) status)
          (setq pass (1+ pass))
          (princ (format "PASS %s\n" name)))
         ((and (consp status) (eq (car status) 'INFO))
          (princ (format "INFO %s %s\n" name (cadr status))))
         (t
          (imp-register-check-as-ert-test (format "m40-imp3/%s" name) status)
          (setq fail (1+ fail))
          (princ (format "FAIL %s %S\n" name (cdr result)))))))
    ;; --- end-to-end through the elisp names, at the elisp level.  The
    ;; corpus above reaches the module through `symbol-function'; a real
    ;; caller (and a compiled elisp caller) resolves the name in the
    ;; elisp function slot.  Call the names directly, as elisp does, on a
    ;; live pty process: process-tty-name must return a string, and the
    ;; unknown-stream branch must signal.  When no command is available
    ;; the e2e is INFO-skipped.
    (if (not (processp pty))
        (princ "INFO m40-imp3/e2e skipped (no pty process)\n")
      (let ((tty (condition-case err (process-tty-name pty)
                   (error (cons 'ERROR err))))
            (stdin (condition-case err (process-tty-name pty 'stdin)
                     (error (cons 'ERROR err))))
            (unknown (condition-case err (process-tty-name pty 'bogus)
                       'no-error
                     (error 'signaled))))
        (let ((tty-ok (or (null tty) (stringp tty)))
              (stdin-ok (or (stringp stdin) (null stdin)))
              (unknown-ok (eq unknown 'signaled)))
          (imp-register-bool-as-ert-test "m40-imp3/e2e/tty-name-string" tty-ok)
          (if tty-ok (setq pass (1+ pass)) (setq fail (1+ fail)))
          (princ (format "%s m40-imp3/e2e/tty-name-string %S\n"
                         (if tty-ok "PASS" "FAIL") tty))
          (imp-register-bool-as-ert-test "m40-imp3/e2e/tty-name-stdin" stdin-ok)
          (if stdin-ok (setq pass (1+ pass)) (setq fail (1+ fail)))
          (princ (format "%s m40-imp3/e2e/tty-name-stdin %S\n"
                         (if stdin-ok "PASS" "FAIL") stdin))
          (imp-register-bool-as-ert-test
           "m40-imp3/e2e/tty-name-unknown-stream-signals" unknown-ok)
          (if unknown-ok (setq pass (1+ pass)) (setq fail (1+ fail)))
          (princ (format "%s m40-imp3/e2e/tty-name-unknown-stream-signals %S\n"
                         (if unknown-ok "PASS" "FAIL") unknown)))))
    ;; The inherit flag reader, at the elisp level.
    (if (not (processp pipe))
        (princ "INFO m40-imp3/e2e/inherit skipped (no pipe process)\n")
      (let ((res (condition-case err
                     (progn
                       (set-process-inherit-coding-system-flag pipe t)
                       (let ((t-val (process-inherit-coding-system-flag pipe)))
                         (set-process-inherit-coding-system-flag pipe nil)
                         (cons t-val (process-inherit-coding-system-flag pipe))))
                   (error (cons 'ERROR err)))))
        (let ((ok (and (eq (car-safe res) t) (null (cdr-safe res)))))
          (imp-register-bool-as-ert-test "m40-imp3/e2e/inherit-then-nil" ok)
          (if ok (setq pass (1+ pass)) (setq fail (1+ fail)))
          (princ (format "%s m40-imp3/e2e/inherit-then-nil %S\n"
                         (if ok "PASS" "FAIL") res)))))
    (princ (format "=== %d passed, %d failed, %d total ===\n"
                   pass fail (+ pass fail)))))

;; Clean up the live processes and the scratch buffer.
(ignore-errors (delete-process (get-process "m40-imp3-pty")))
(ignore-errors (delete-process (get-process "m40-imp3-pipe")))
(ignore-errors (kill-buffer (get-buffer " *m40-imp3-out*")))
