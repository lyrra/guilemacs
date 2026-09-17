;;; test-m39-imp4-e2e.el --- M39 imp-4 end-to-end signal-family suite.
;;;
;;; The companion corpus test/m39/test-m39-imp4.scm pins the static wire
;;; (the retired DEFUNs, the --signal-* bridge, the module).  This file
;;; pins the live behaviour: the moved names are elisp functions; the
;;; stop/continue connection gate selects the connection branch for a
;;; pipe; signal-process accepts an integer, a signal-name symbol, and a
;;; process object; and internal-default-signal-process resolves a
;;; process name, a process number, and a process object.
;;;
;;; The signals are harmless: the tests use signal 0 (the existence probe)
;;; and SIGCONT, and they target this Emacs or a short-lived child.

(princ "=== m39 imp-4 (process signal family) e2e suite ===\n")

(let* ((pass 0)
       (fail 0)
       (check (lambda (name thunk)
                (let ((res (condition-case err (funcall thunk) (error nil))))
                  (eval `(ert-deftest ,(intern name) () (should ',res)))
                  (if res (setq pass (1+ pass)) (setq fail (1+ fail)))
                  (princ (format "%s %s\n" (if res "PASS" "FAIL") name))))))
  ;; The eight moved names still register as elisp functions.
  (dolist (n '(internal-default-interrupt-process interrupt-process
               kill-process quit-process stop-process continue-process
               internal-default-signal-process signal-process))
    (funcall check (format "m39-imp4/e2e/fboundp/%s" n)
             (lambda () (fboundp n))))

  ;; signal-process accepts an integer process number.
  (funcall check "m39-imp4/e2e/signal-process-integer"
           (lambda () (eql 0 (signal-process (emacs-pid) 0))))

  ;; signal-process accepts a signal-name symbol.
  (funcall check "m39-imp4/e2e/signal-process-symbol"
           (lambda () (eql 0 (signal-process (emacs-pid) 'SIGCONT))))

  ;; internal-default-signal-process resolves a process number.
  (funcall check "m39-imp4/e2e/default-signal-number"
           (lambda () (eql 0 (internal-default-signal-process
                              (emacs-pid) 0 nil))))

  ;; the stop/continue connection gate: a pipe takes the connection branch.
  (let* ((pipe (condition-case err
                   (make-pipe-process :name "m39-imp4-pipe" :noquery t)
                 (error nil)))
         (made (processp pipe)))
    (when made
      (funcall check "m39-imp4/e2e/stop-process-pipe-returns-process"
               (lambda () (eq (stop-process pipe) pipe)))
      (funcall check "m39-imp4/e2e/continue-process-pipe-returns-process"
               (lambda () (eq (continue-process pipe) pipe)))
      (ignore-errors (delete-process pipe))))

  ;; a real subprocess: signal-process and internal-default-signal-process
  ;; resolve a process object and a process name.
  (let* ((proc (condition-case err
                   (start-process "m39-imp4-sleep" nil "sleep" "60")
                 (error nil)))
         (made (processp proc)))
    (when made
      (accept-process-output proc 0 100)
      (funcall check "m39-imp4/e2e/signal-process-object"
               (lambda () (eql 0 (signal-process proc 'SIGCONT))))
      (funcall check "m39-imp4/e2e/default-signal-object"
               (lambda () (eql 0 (internal-default-signal-process proc 0 nil))))
      (funcall check "m39-imp4/e2e/default-signal-name"
               (lambda () (eql 0 (internal-default-signal-process
                                  (process-name proc) 0 nil))))
      ;; D1: a non-number, non-string PROCESS resolves through the static
      ;; get_process, so a *buffer* resolves to its process.  The process
      ;; must live in a named buffer for get-buffer-process to find it.
      (let ((buf (get-buffer-create "m39-imp4-bufproc")))
        (let ((bproc (condition-case err
                         (start-process "m39-imp4-bufsleep" buf "sleep" "60")
                       (error nil))))
          (when (processp bproc)
            (accept-process-output bproc 0 100)
            (funcall check "m39-imp4/e2e/default-signal-buffer"
                     (lambda () (eql 0 (internal-default-signal-process buf 0 nil))))
            (ignore-errors (delete-process bproc)))))
      ;; D5/D9: a byte-compiled caller of a reinstalled name still works.
      (funcall check "m39-imp4/e2e/byte-compiled-caller"
               (lambda () (eql 0 (funcall (byte-compile
                                           (lambda () (signal-process (emacs-pid) 0)))))))
      (ignore-errors (delete-process proc))))

  (princ (format "=== %d passed, %d failed, %d total ===\n"
                 pass fail (+ pass fail))))
