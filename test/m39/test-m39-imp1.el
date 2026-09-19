;;; test-m39-imp1.el --- M39 imp-1 (accept-process-output decision) suite.
;;;
;;; Pins the M39 imp-1 port (brief.org): the decision logic of
;;; Faccept_process_output (src/process.c, pre-M39 body at :4932-4970)
;;; moved into (emacs process-wait) as accept-process-output-decision,
;;; and src/process.c now calls the C dispatcher
;;; accept_process_output_decision.  The wait_reading_process_output
;;; call stays C.
;;;
;;; Wraps test/m39/test-m39-imp1.scm -- the Scheme audit corpus.
;;; Binds the repo root as %m39-root, loads the Scheme file via
;;; eval-scheme, then reads back `test-results' (list of (NAME STATUS)
;;; pairs).  Each (NAME PASS|FAIL) pair is reported via princ AND turned
;;; into an ERT test so the harness counts it.  Each (NAME INFO VALUE)
;;; pair is printed as an INFO line and is NOT asserted.  A corpus load
;;; error, a readback error or an empty corpus is reported as a real
;;; FAIL (never a silent 0 failed).

(princ "=== m39 imp-1 (accept-process-output decision) test suite ===\n")

(require 'imp-ert-report)

(let* ((dir (file-name-directory (or load-file-name default-directory)))
       (root (expand-file-name "../.." dir))
       (corpus (expand-file-name "test-m39-imp1.scm" dir))
       (load-error nil))
  ;; The corpus reads the build tree, so tell it where the root is.
  (eval-scheme (format "(define %%m39-root %S)" root))
  (condition-case err
      (eval-scheme
       (format "(primitive-load %S)" corpus))
    (error (setq load-error err)))
  (let* ((results
          (cond
           (load-error
            (list (list "m39-imp1/corpus-load"
                        (cons 'FAIL (format "%S" load-error)))))
           (t
            (condition-case e
                (let ((r (eval-scheme "(reverse test-results)")))
                  (if (or (not (listp r)) (null r))
                      (list (list "m39-imp1/corpus-empty"
                                  (cons 'FAIL "corpus produced no results")))
                    r))
              (error
               (list (list "m39-imp1/readback"
                           (cons 'FAIL (format "%S" e)))))))))
         (pass 0)
         (fail 0))
    (dolist (result results)
      (let* ((name (car result))
             (status (cadr result))
             (ok (eq status 'PASS)))
        (cond
         (ok
          (imp-register-check-as-ert-test (format "m39-imp1/%s" name) status)
          (setq pass (1+ pass))
          (princ (format "PASS %s\n" name)))
         ((and (consp status) (eq (car status) 'INFO))
          (princ (format "INFO %s %s\n" name (cadr status))))
         (t
          (imp-register-check-as-ert-test (format "m39-imp1/%s" name) status)
          (setq fail (1+ fail))
          (princ (format "FAIL %s %S\n" name (cdr result)))))))
    ;; --- F2: end-to-end through the subr accept-process-output and its
    ;; C dispatcher (src/process.c accept_process_output_decision).  Call
    ;; the subr so the C readback runs; the corpus above only calls the
    ;; Scheme procedure.  Use immediate or ~1ms timeouts only -- a huge
    ;; float would block for WAIT_READING_MAX seconds.  With no PROCESS
    ;; there is no subprocess output, so the pre-port result is nil.
    (dolist (c (list (cons "m39-imp1/e2e/no-args"
                           (lambda () (accept-process-output)))
                     (cons "m39-imp1/e2e/zero-seconds"
                           (lambda () (accept-process-output nil 0)))
                     (cons "m39-imp1/e2e/float-small"
                           (lambda () (accept-process-output nil 0.001)))))
      (let* ((name (car c))
             (val (condition-case err
                      (funcall (cdr c))
                    (error (cons 'ERROR err))))
             (ok (null val)))
        (imp-register-bool-as-ert-test name ok)
        (cond (ok
               (setq pass (1+ pass))
               (princ (format "PASS %s -> %S\n" name val)))
              (t
               (setq fail (1+ fail))
               (princ (format "FAIL %s -> %S (want nil)\n" name val))))))
    (princ (format "=== %d passed, %d failed, %d total ===\n"
                   pass fail (+ pass fail)))))
