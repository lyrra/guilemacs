;;; test-m39-imp2.el --- M39 imp-2 (process read/write decisions) suite.
;;;
;;; Pins the M39 imp-2 port (brief.org): the decision logic of
;;; send_process (src/process.c, pre-M39 body at :6790-6795) and
;;; Fprocess_send_region (:7033-7034) moved into (emacs process-io) as
;;; send-process-state-decision and process-send-region-gap-move?, and
;;; src/process.c now calls the C dispatchers send_process_state_decision
;;; and process_send_region_gap_move.  The write loop, the coding setup,
;;; and the buffer and string access stay C.
;;;
;;; Wraps test/m39/test-m39-imp2.scm -- the Scheme audit corpus.
;;; Binds the repo root as %m39-root, loads the Scheme file via
;;; eval-scheme, then reads back `test-results' (list of (NAME STATUS)
;;; pairs).  Each (NAME PASS|FAIL) pair is reported via princ AND turned
;;; into an ERT test so the harness counts it.  Each (NAME INFO VALUE)
;;; pair is printed as an INFO line and is NOT asserted.  A corpus load
;;; error, a readback error or an empty corpus is reported as a real
;;; FAIL (never a silent 0 failed).

(princ "=== m39 imp-2 (process read/write decisions) test suite ===\n")

(require 'imp-ert-report)

(let* ((dir (file-name-directory (or load-file-name default-directory)))
       (root (expand-file-name "../.." dir))
       (corpus (expand-file-name "test-m39-imp2.scm" dir))
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
            (list (list "m39-imp2/corpus-load"
                        (cons 'FAIL (format "%S" load-error)))))
           (t
            (condition-case e
                (let ((r (eval-scheme "(reverse test-results)")))
                  (if (or (not (listp r)) (null r))
                      (list (list "m39-imp2/corpus-empty"
                                  (cons 'FAIL "corpus produced no results")))
                    r))
              (error
               (list (list "m39-imp2/readback"
                           (cons 'FAIL (format "%S" e)))))))))
         (pass 0)
         (fail 0))
    (dolist (result results)
      (let* ((name (car result))
             (status (cadr result))
             (ok (eq status 'PASS)))
        (cond
         (ok
          (imp-register-check-as-ert-test (format "m39-imp2/%s" name) status)
          (setq pass (1+ pass))
          (princ (format "PASS %s\n" name)))
         ((and (consp status) (eq (car status) 'INFO))
          (princ (format "INFO %s %s\n" name (cadr status))))
         (t
          (imp-register-check-as-ert-test (format "m39-imp2/%s" name) status)
          (setq fail (1+ fail))
          (princ (format "FAIL %s %S\n" name (cdr result)))))))
    ;; --- end-to-end through the subrs and their C dispatchers
    ;; (src/process.c send_process_state_decision and
    ;; process_send_region_gap_move).  The corpus above only calls the
    ;; Scheme procedures.  A pipe process exercises both dispatcher call
    ;; sites; after delete-process the state gate must signal.  The live
    ;; send result is INFO-only: a pipe process may have no output fd in
    ;; this build, and the dispatcher runs either way.
    (let* ((pipe (condition-case err
                     (make-pipe-process :name "m39-imp2-pipe" :noquery t)
                   (error nil)))
           (made (processp pipe)))
      (imp-register-bool-as-ert-test "m39-imp2/e2e/make-pipe-process" made)
      (if made
          (setq pass (1+ pass))
        (setq fail (1+ fail)))
      (princ (format "%s m39-imp2/e2e/make-pipe-process\n"
                     (if made "PASS" "FAIL")))
      (when made
        (princ (format "INFO m39-imp2/e2e/live-send-string %S\n"
                       (condition-case err (process-send-string pipe "hello")
                         (error (cons 'ERROR err)))))
        (princ (format "INFO m39-imp2/e2e/live-send-region %S\n"
                       (condition-case err
                           (with-temp-buffer
                             (insert "abcdef")
                             (process-send-region pipe (point-min) (point-max)))
                         (error (cons 'ERROR err)))))
        (ignore-errors (delete-process pipe)))
      ;; Both subrs must signal on the dead process: send-string runs the
      ;; state gate; send-region runs the gap-move dispatcher before
      ;; send_process errors.
      (dolist (c (list (cons "m39-imp2/e2e/send-string-dead-errors"
                             (lambda () (process-send-string pipe "x")))
                       (cons "m39-imp2/e2e/send-region-dead-errors"
                             (lambda ()
                               (with-temp-buffer
                                 (insert "abcdef")
                                 (process-send-region pipe (point-min)
                                                      (point-max)))))))
        (let* ((name (car c))
               (errored (condition-case err
                            (progn (funcall (cdr c)) nil)
                          (error t))))
          (imp-register-bool-as-ert-test name errored)
          (if errored
              (setq pass (1+ pass))
            (setq fail (1+ fail)))
          (princ (format "%s %s\n" (if errored "PASS" "FAIL") name)))))
    (princ (format "=== %d passed, %d failed, %d total ===\n"
                   pass fail (+ pass fail)))))
