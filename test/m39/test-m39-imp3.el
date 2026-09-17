;;; test-m39-imp3.el --- M39 imp-3 (process Group A accessors) corpus suite.
;;;
;;; Pins the M39 imp-3 port (brief.org): the decision of the src/process.c
;;; Group A accessors moved into (emacs process-accessors), the slot stays
;;; C, and each accessor reaches it through the table-driven C bridge
;;; --process-ref / --process-set!.
;;;
;;; Wraps test/m39/test-m39-imp3.scm -- the Scheme audit corpus.  Binds the
;;; repo root as %m39-root, loads the Scheme file via eval-scheme, then
;;; reads back `test-results' (list of (NAME STATUS) pairs).  Each (NAME
;;; PASS|FAIL) pair is reported via princ AND turned into an ERT test so
;;; the harness counts it.  Each (NAME INFO VALUE) pair is printed as an
;;; INFO line and is NOT asserted.  A corpus load error, a readback error
;;; or an empty corpus is reported as a real FAIL (never a silent 0
;;; failed).
;;;
;;; The live accessor behaviour is exercised by the companion file
;;; test/m39/test-m39-imp3-e2e.el.  The two files are split because the
;;; guilemacs elisp loader is fragile with a large single test file (a
;;; corpus wrapper plus a full e2e block segfaults the loader).

(princ "=== m39 imp-3 (process Group A accessors) test suite ===\n")

(let* ((dir (file-name-directory (or load-file-name default-directory)))
       (root (expand-file-name "../.." dir))
       (corpus (expand-file-name "test-m39-imp3.scm" dir))
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
            (list (list "m39-imp3/corpus-load"
                        (cons 'FAIL (format "%S" load-error)))))
           (t
            (condition-case e
                (let ((r (eval-scheme "(reverse test-results)")))
                  (if (or (not (listp r)) (null r))
                      (list (list "m39-imp3/corpus-empty"
                                  (cons 'FAIL "corpus produced no results")))
                    r))
              (error
               (list (list "m39-imp3/readback"
                           (cons 'FAIL (format "%S" e)))))))))
         (pass 0)
         (fail 0))
    (dolist (result results)
      (let* ((name (car result))
             (status (cadr result))
             (ok (eq status 'PASS)))
        (cond
         (ok
          (eval `(ert-deftest ,(intern (format "m39-imp3/%s" name)) ()
                   (should (eq ',status 'PASS))))
          (setq pass (1+ pass))
          (princ (format "PASS %s\n" name)))
         ((and (consp status) (eq (car status) 'INFO))
          (princ (format "INFO %s %s\n" name (cadr status))))
         (t
          (eval `(ert-deftest ,(intern (format "m39-imp3/%s" name)) ()
                   (should (eq ',status 'PASS))))
          (setq fail (1+ fail))
          (princ (format "FAIL %s %S\n" name (cdr result)))))))
    (princ (format "=== %d passed, %d failed, %d total ===\n"
                   pass fail (+ pass fail)))))
