;;; test-m40-imp2.el --- M40 imp-2 (send_process multibyte decision) suite.
;;;
;;; Pins the M40 imp-2 port (brief.org): the multibyte-versus-unibyte
;;; decision of send_process (src/process.c, the previous predicate at
;;; :6843-6846) moved into (emacs process-io) as
;;; process-string-needs-encoding? and send-process-object-multibyte?,
;;; and src/process.c now calls the C dispatcher
;;; send_process_object_multibyte_decision.  The two arms, the
;;; coding-system setup, the byte-position code, and the NETCONN_P rule
;;; stay C.
;;;
;;; Wraps test/m40/test-m40-imp2.scm -- the Scheme corpus.  This file
;;; creates the two buffers the corpus reads (one unibyte, one
;;; multibyte) through with-current-buffer, so the batch's current
;;; buffer is restored and no state leaks; it binds the repo root as
;;; %m40-root and loads the Scheme file via eval-scheme.  Each
;;; (NAME PASS|FAIL) pair is reported via princ AND turned into an ERT
;;; test so the harness counts it.  A corpus load error, a readback
;;; error or an empty corpus is reported as a real FAIL.

(princ "=== m40 imp-2 (send_process multibyte decision) test suite ===\n")

(require 'imp-ert-report)

(let* ((dir (file-name-directory (or load-file-name default-directory)))
       (root (expand-file-name "../.." dir))
       (corpus (expand-file-name "test-m40-imp2.scm" dir))
       (load-error nil))
  ;; The corpus reads these buffers by name.  Configure each in its own
  ;; with-current-buffer, which restores the current buffer afterwards.
  (let ((ub (get-buffer-create "m40-imp2-unibyte"))
        (mb (get-buffer-create "m40-imp2-multibyte")))
    (with-current-buffer ub (set-buffer-multibyte nil))
    (with-current-buffer mb (set-buffer-multibyte t)))
  ;; The corpus reads the build tree, so tell it where the root is.
  (eval-scheme (format "(define %%m40-root %S)" root))
  (condition-case err
      (eval-scheme
       (format "(primitive-load %S)" corpus))
    (error (setq load-error err)))
  (let* ((results
          (cond
           (load-error
            (list (list "m40-imp2/corpus-load"
                        (cons 'FAIL (format "%S" load-error)))))
           (t
            (condition-case e
                (let ((r (eval-scheme "(reverse test-results)")))
                  (if (or (not (listp r)) (null r))
                      (list (list "m40-imp2/corpus-empty"
                                  (cons 'FAIL "corpus produced no results")))
                    r))
              (error
               (list (list "m40-imp2/readback"
                           (cons 'FAIL (format "%S" e)))))))))
         (pass 0)
         (fail 0))
    (dolist (result results)
      (let* ((name (car result))
             (status (cadr result))
             (ok (eq status 'PASS)))
        (cond
         (ok
          (imp-register-check-as-ert-test (format "m40-imp2/%s" name) status)
          (setq pass (1+ pass))
          (princ (format "PASS %s\n" name)))
         ((and (consp status) (eq (car status) 'INFO))
          (princ (format "INFO %s %s\n" name (cadr status))))
         (t
          (imp-register-check-as-ert-test (format "m40-imp2/%s" name) status)
          (setq fail (1+ fail))
          (princ (format "FAIL %s %S\n" name (cdr result)))))))
    ;; --- end-to-end through the subr and its C dispatcher
    ;; (src/process.c send_process_object_multibyte_decision).  The corpus
    ;; above only calls the Scheme procedures.  A live subprocess owns a
    ;; real output fd, so `process-send-string' reaches the send_process
    ;; decision and runs the C -> Scheme dispatcher: a multibyte string
    ;; runs the then arm, an ASCII string the else arm, and both must run
    ;; without error.  A pipe process has no output fd (send on it always
    ;; signals), so use a real command.  When no command is available the
    ;; e2e is INFO-skipped, never a FAIL: it is an environment gap, not a
    ;; code regression.
    (let* ((cat (executable-find "cat"))
           (proc (and cat
                      (condition-case err
                          (make-process :name "m40-imp2-proc" :command (list cat)
                                        :noquery t)
                        (error nil))))
           (made (processp proc)))
      (if (not cat)
          (princ "INFO m40-imp2/e2e skipped (no cat executable)\n")
        (imp-register-bool-as-ert-test "m40-imp2/e2e/make-process" made)
        (if made
            (setq pass (1+ pass))
          (setq fail (1+ fail)))
        (princ (format "%s m40-imp2/e2e/make-process\n"
                       (if made "PASS" "FAIL")))
        (when made
          ;; A multibyte string runs the then arm; an ASCII string runs
          ;; the else arm.  Both go through the C -> Scheme dispatcher.
          (let ((mb (condition-case err
                        (progn (process-send-string proc "x\u00e4") nil)
                      (error (cons 'ERROR err))))
                (ascii (condition-case err
                           (progn (process-send-string proc "abc") nil)
                         (error (cons 'ERROR err)))))
            (let ((mb-ok (null mb))
                  (ascii-ok (null ascii)))
              (imp-register-bool-as-ert-test
               "m40-imp2/e2e/send-multibyte-string" mb-ok)
              (if mb-ok (setq pass (1+ pass)) (setq fail (1+ fail)))
              (princ (format "%s m40-imp2/e2e/send-multibyte-string %S\n"
                             (if mb-ok "PASS" "FAIL") mb))
              (imp-register-bool-as-ert-test
               "m40-imp2/e2e/send-ascii-string" ascii-ok)
              (if ascii-ok (setq pass (1+ pass)) (setq fail (1+ fail)))
              (princ (format "%s m40-imp2/e2e/send-ascii-string %S\n"
                             (if ascii-ok "PASS" "FAIL") ascii))))
          (ignore-errors (delete-process proc)))))
    (princ (format "=== %d passed, %d failed, %d total ===\n"
                   pass fail (+ pass fail)))))
