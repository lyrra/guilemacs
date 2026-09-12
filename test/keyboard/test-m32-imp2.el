;;; test-m32-imp2.el --- M32 imp-2 (process.c error paths) suite.
;;;
;;; Pins the M32 imp-2 port (brief.org): the two process.c error-handler
;;; bodies moved into the new module (emacs process-error), the
;;; send_process EINTR-loop drain moved there too, and the C function
;;; cmd_error_internal is retired (process.c was its last caller).  The
;;; C entry points stay C as thin static dispatchers.
;;;
;;; Wraps test/keyboard/test-m32-imp2.scm -- the Scheme audit corpus.
;;; Binds the repo root as %m32-root, loads the Scheme file via
;;; eval-scheme, then reads back `test-results' (list of (NAME STATUS)
;;; pairs).  Each (NAME PASS|FAIL) pair is reported via princ AND turned
;;; into an ERT test so the harness counts it.  Each (NAME INFO VALUE)
;;; pair is printed as an INFO line and is NOT asserted.  A corpus load
;;; error, a readback error or an empty corpus is reported as a real
;;; FAIL (never a silent 0 failed).

(princ "=== m32 imp-2 (process.c error paths) test suite ===\n")

;; The corpus emits one (NAME STATUS) pair per check.  A corpus FAIL, a
;; corpus load error and a readback error must all surface as a real
;; FAIL -- never as a silent "0 failed".  Each PASS/FAIL pair also
;; becomes an ERT test so the harness counts it instead of trusting the
;; princ lines.  INFO pairs are printed, not asserted.
(let* ((dir (file-name-directory (or load-file-name default-directory)))
       (root (expand-file-name "../.." dir))
       (corpus (expand-file-name "test-m32-imp2.scm" dir))
       (load-error nil))
  ;; The corpus reads the build tree, so tell it where the root is.
  (eval-scheme (format "(define %%m32-root %S)" root))
  (condition-case err
      (eval-scheme
       (format "(primitive-load %S)" corpus))
    (error (setq load-error err)))
  (let* ((results
          (cond
           (load-error
            (list (list "m32-imp2/corpus-load"
                        (cons 'FAIL (format "%S" load-error)))))
           (t
            (condition-case e
                (let ((r (eval-scheme "(reverse test-results)")))
                  (if (or (not (listp r)) (null r))
                      (list (list "m32-imp2/corpus-empty"
                                  (cons 'FAIL "corpus produced no results")))
                    r))
              (error
               (list (list "m32-imp2/readback"
                           (cons 'FAIL (format "%S" e)))))))))
         (pass 0)
         (fail 0))
    (dolist (result results)
      (let* ((name (car result))
             (status (cadr result))
             (ok (eq status 'PASS)))
        (cond
         (ok
          ;; Define the ERT test so the harness metric sees it.
          ;; The corpus name is already namespaced (m32/imp2/...), so use
          ;; it verbatim; do not prepend a second m32-imp2/ prefix.
          (eval `(ert-deftest ,(intern name) ()
                   (should (eq ',status 'PASS))))
          (setq pass (1+ pass))
          (princ (format "PASS %s\n" name)))
         ((and (consp status) (eq (car status) 'INFO))
          ;; Informational (printed, not asserted): counts.
          (princ (format "INFO %s %s\n" name (cadr status))))
         (t
          (eval `(ert-deftest ,(intern name) ()
                   (should (eq ',status 'PASS))))
          (setq fail (1+ fail))
          (princ (format "FAIL %s %S\n" name (cdr result)))))))
    (princ (format "=== %d passed, %d failed, %d total ===\n"
                   pass fail (+ pass fail)))))
