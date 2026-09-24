;;; test-m40-imp4a.el --- M40 imp-4a (Group C small-gate decisions) suite.
;;;
;;; Pins the M40 imp-4a port (brief.org): the decision of four
;;; src/process.c Group C names moved into (emacs process-lifecycle) --
;;; set-process-window-size (the NETCONN_P / infd < 0 / failed-ioctl
;;; gate), set-process-coding-system (the Fcheck_coding_system order and
;;; the infd < 0 || outfd < 0 early return), process-datagram-address
;;; (the DATAGRAM_CONN_P nil result), and set-process-datagram-address
;;; (the len == 0 || len != table-len gate).  The mechanism stays C; the
;;; C keeps each DEFUN and calls the module through a small dispatcher.
;;;
;;; Wraps test/m40/test-m40-imp4a.scm -- the Scheme corpus.  This file
;;; binds the repo root as %m40-root, makes the live process the e2e
;;; checks use (a pipe process), and loads the Scheme file via
;;; eval-scheme.  Each (NAME PASS|FAIL) pair is
;;; reported via princ AND turned into an ERT test so the harness counts
;;; it.  A corpus load error, a readback error or an empty corpus is
;;; reported as a real FAIL.  When a process cannot be made the e2e for
;;; it is INFO-skipped (an environment gap, not a code regression).

(princ "=== m40 imp-4a (Group C small-gate decisions) test suite ===\n")

(require 'imp-ert-report)

(let* ((dir (file-name-directory (or load-file-name default-directory)))
       (root (expand-file-name "../.." dir))
       (corpus (expand-file-name "test-m40-imp4a.scm" dir))
       (cat (executable-find "cat"))
       (outbuf (and cat (get-buffer-create " *m40-imp4a-out*")))
       (pipe (and cat
                  (condition-case nil
                      (make-process :name "m40-imp4a-pipe" :command (list cat)
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
            (list (list "m40-imp4a/corpus-load"
                        (cons 'FAIL (format "%S" load-error)))))
           (t
            (condition-case e
                (let ((r (eval-scheme "(reverse test-results)")))
                  (if (or (not (listp r)) (null r))
                      (list (list "m40-imp4a/corpus-empty"
                                  (cons 'FAIL "corpus produced no results")))
                    r))
              (error
               (list (list "m40-imp4a/readback"
                           (cons 'FAIL (format "%S" e)))))))))
         (pass 0)
         (fail 0))
    (dolist (result results)
      (let* ((name (car result))
             (status (cadr result))
             (ok (eq status 'PASS)))
        (cond
         (ok
          (imp-register-check-as-ert-test (format "m40-imp4a/%s" name) status)
          (setq pass (1+ pass))
          (princ (format "PASS %s\n" name)))
         ((and (consp status) (eq (car status) 'INFO))
          (princ (format "INFO %s %s\n" name (cadr status))))
         (t
          (imp-register-check-as-ert-test (format "m40-imp4a/%s" name) status)
          (setq fail (1+ fail))
          (princ (format "FAIL %s %S\n" name (cdr result)))))))
    ;; --- end-to-end through the elisp names, at the elisp level.  The
    ;; four DEFUNs stay C; the names must still be callable and the
    ;; module decision must drive the result.  When no process is
    ;; available the e2e is INFO-skipped.
    (if (not (processp pipe))
        (princ "INFO m40-imp4a/e2e skipped (no pipe process)\n")
      (let ((win (condition-case err (set-process-window-size pipe 30 100)
                   (error (cons 'ERROR err))))
            (cod (condition-case err
                     (progn (set-process-coding-system pipe 'utf-8 'utf-8)
                            'ok)
                   (error (cons 'ERROR err)))))
        (let ((win-ok (memq win '(t nil)))
              (cod-ok (eq cod 'ok)))
          (imp-register-bool-as-ert-test "m40-imp4a/e2e/window-size-boolean"
                                         win-ok)
          (if win-ok (setq pass (1+ pass)) (setq fail (1+ fail)))
          (princ (format "%s m40-imp4a/e2e/window-size-boolean %S\n"
                         (if win-ok "PASS" "FAIL") win))
          (imp-register-bool-as-ert-test "m40-imp4a/e2e/coding-system-ok"
                                         cod-ok)
          (if cod-ok (setq pass (1+ pass)) (setq fail (1+ fail)))
          (princ (format "%s m40-imp4a/e2e/coding-system-ok %S\n"
                         (if cod-ok "PASS" "FAIL") cod)))))
    (princ (format "=== %d passed, %d failed, %d total ===\n"
                   pass fail (+ pass fail)))))

;; Clean up the live processes and the scratch buffer.
(ignore-errors (delete-process (get-process "m40-imp4a-pipe")))
(ignore-errors (kill-buffer (get-buffer " *m40-imp4a-out*")))
