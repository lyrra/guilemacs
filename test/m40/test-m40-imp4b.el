;;; test-m40-imp4b.el --- M40 imp-4b (remaining Group C decisions) suite.
;;;
;;; Pins the M40 imp-4b port (brief.org): the decision of the four
;;; remaining src/process.c Group C names moved into (emacs
;;; process-lifecycle) -- delete-process (the connection-kind branch
;;; selector NETCONN1_P || SERIALCONN1_P || PIPECONN1_P), process-send-eof
;;; (the DATAGRAM_CONN_P early return and the alive gate),
;;; internal-default-process-filter (the insert-or-discard gate), and
;;; internal-default-process-sentinel (the outer gate and the inner
;;; BUFFER_LIVE_P gate).  The mechanism stays C; the C keeps each DEFUN
;;; and calls the module through a small dispatcher.
;;;
;;; Wraps test/m40/test-m40-imp4b.scm -- the Scheme corpus.  This file
;;; binds the repo root as %m40-root, makes the live process the e2e
;;; checks use (a pipe process), and loads the Scheme file via
;;; eval-scheme.  Each (NAME PASS|FAIL) pair is reported via princ AND
;;; turned into an ERT test so the harness counts it.  A corpus load
;;; error, a readback error or an empty corpus is reported as a real
;;; FAIL.  When a process cannot be made the e2e for it is INFO-skipped
;;; (an environment gap, not a code regression).  No datagram network
;;; process is made (brief.org section 4.2: it aborts Guile).

(princ "=== m40 imp-4b (remaining Group C decisions) test suite ===\n")

(require 'imp-ert-report)

(let* ((dir (file-name-directory (or load-file-name default-directory)))
       (root (expand-file-name "../.." dir))
       (corpus (expand-file-name "test-m40-imp4b.scm" dir))
       (cat (executable-find "cat"))
       (outbuf (and cat (get-buffer-create " *m40-imp4b-out*")))
       (pipe (and cat
                  (condition-case nil
                      (make-process :name "m40-imp4b-pipe" :command (list cat)
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
            (list (list "m40-imp4b/corpus-load"
                        (cons 'FAIL (format "%S" load-error)))))
           (t
            (condition-case e
                (let ((r (eval-scheme "(reverse test-results)")))
                  (if (or (not (listp r)) (null r))
                      (list (list "m40-imp4b/corpus-empty"
                                  (cons 'FAIL "corpus produced no results")))
                    r))
              (error
               (list (list "m40-imp4b/readback"
                           (cons 'FAIL (format "%S" e)))))))))
         (pass 0)
         (fail 0))
    (dolist (result results)
      (let* ((name (car result))
             (status (cadr result))
             (ok (eq status 'PASS)))
        (cond
         (ok
          (imp-register-check-as-ert-test (format "m40-imp4b/%s" name) status)
          (setq pass (1+ pass))
          (princ (format "PASS %s\n" name)))
         ((and (consp status) (eq (car status) 'INFO))
          (princ (format "INFO %s %s\n" name (cadr status))))
         (t
          (imp-register-check-as-ert-test (format "m40-imp4b/%s" name) status)
          (setq fail (1+ fail))
          (princ (format "FAIL %s %S\n" name (cdr result)))))))
    ;; --- end-to-end through the elisp names, at the elisp level.  The
    ;; four DEFUNs stay C; the names must still be callable and the
    ;; module decision must drive the result.  When no process is
    ;; available the e2e is INFO-skipped.
    (if (not (processp pipe))
        (princ "INFO m40-imp4b/e2e skipped (no pipe process)\n")
      (let ((eof (condition-case err (process-send-eof pipe)
                   (error (cons 'ERROR err)))))
        (let ((eof-ok (eq eof pipe)))
          (imp-register-bool-as-ert-test "m40-imp4b/e2e/send-eof-returns-process"
                                         eof-ok)
          (if eof-ok (setq pass (1+ pass)) (setq fail (1+ fail)))
          (princ (format "%s m40-imp4b/e2e/send-eof-returns-process %S\n"
                         (if eof-ok "PASS" "FAIL") eof))))
      ;; delete-process is the last e2e: it kills the pipe process.
      (let ((del (condition-case err (delete-process pipe)
                   (error (cons 'ERROR err)))))
        (let ((del-ok (eq del nil)))
          (imp-register-bool-as-ert-test "m40-imp4b/e2e/delete-process-returns-nil"
                                         del-ok)
          (if del-ok (setq pass (1+ pass)) (setq fail (1+ fail)))
          (princ (format "%s m40-imp4b/e2e/delete-process-returns-nil %S\n"
                         (if del-ok "PASS" "FAIL") del)))))
    (princ (format "=== %d passed, %d failed, %d total ===\n"
                   pass fail (+ pass fail)))))

;; Clean up the live process and the scratch buffer.
(ignore-errors (delete-process (get-process "m40-imp4b-pipe")))
(ignore-errors (kill-buffer (get-buffer " *m40-imp4b-out*")))
