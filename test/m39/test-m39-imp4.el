;;; test-m39-imp4.el --- M39 imp-4 (process signal family) corpus suite.
;;;
;;; Pins the M39 imp-4 port (brief.org): the decision of the src/process.c
;;; signal family moved into (emacs process-signal), the mechanism (the
;;; kill(2) syscall, abbr_to_signal, process_send_signal, the stop/continue
;;; fd work) stays C, and each moved elisp name is reinstalled through
;;; define-elisp-inline.
;;;
;;; Wraps test/m39/test-m39-imp4.scm -- the Scheme audit corpus.  Binds the
;;; repo root as %m39-root, loads the Scheme file via eval-scheme, then
;;; reads back `test-results'.  Each (NAME PASS|FAIL) pair is reported via
;;; princ AND turned into an ERT test.  A corpus load error, a readback
;;; error or an empty corpus is reported as a real FAIL (never a silent 0
;;; failed).
;;;
;;; The live signal behaviour is exercised by the companion file
;;; test/m39/test-m39-imp4-e2e.el.

(princ "=== m39 imp-4 (process signal family) test suite ===\n")

(let* ((dir (file-name-directory (or load-file-name default-directory)))
       (root (expand-file-name "../.." dir))
       (corpus (expand-file-name "test-m39-imp4.scm" dir))
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
            (list (list "m39-imp4/corpus-load"
                        (cons 'FAIL (format "%S" load-error)))))
           (t
            (condition-case e
                (let ((r (eval-scheme "(reverse test-results)")))
                  (if (or (not (listp r)) (null r))
                      (list (list "m39-imp4/corpus-empty"
                                  (cons 'FAIL "corpus produced no results")))
                    r))
              (error
               (list (list "m39-imp4/readback"
                           (cons 'FAIL (format "%S" e)))))))))
         (pass 0)
         (fail 0))
    (dolist (result results)
      (let* ((name (car result))
             (status (cadr result))
             (ok (eq status 'PASS)))
        (cond
         (ok
          (eval `(ert-deftest ,(intern (format "m39-imp4/%s" name)) ()
                   (should (eq ',status 'PASS))))
          (setq pass (1+ pass))
          (princ (format "PASS %s\n" name)))
         ((and (consp status) (eq (car status) 'INFO))
          (princ (format "INFO %s %s\n" name (cadr status))))
         (t
          (eval `(ert-deftest ,(intern (format "m39-imp4/%s" name)) ()
                   (should (eq ',status 'PASS))))
          (setq fail (1+ fail))
          (princ (format "FAIL %s %S\n" name (cdr result)))))))
    (princ (format "=== %d passed, %d failed, %d total ===\n"
                   pass fail (+ pass fail)))))
