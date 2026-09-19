;;; test-m37-imp1.el --- M37 imp-1 (reclaim step + imp-0 corrections) suite.
;;;
;;; Pins the M37 imp-1 work (brief.org): the surface is unchanged, all
;;; five read-path --=-shims keep a definition and a live Scheme caller
;;; (so none is dead and imp-1 deletes nothing), the kept C drain
;;; control and the nr == -2 arm stay, the corrected census rows and the
;;; two added Q1 consumers are recorded, the stale xterm.scm comment is
;;; fixed, and the corpus is registered in tool/run-tests.scm.  imp-1
;;; changes no C file.
;;;
;;; Wraps test/keyboard/test-m37-imp1.scm -- the Scheme audit corpus.
;;;
;;; Binds the repo root as %m37-root, loads the Scheme file via
;;; primitive-load, then reads back `test-results' (list of (NAME STATUS)
;;; pairs).  Each (NAME PASS|FAIL) pair is reported via princ AND turned
;;; into an ERT test so the harness counts it.  Each (NAME INFO VALUE)
;;; pair is printed as an INFO line and is NOT asserted.  A corpus load
;;; error, a readback error or an empty corpus is reported as a real
;;; FAIL (never a silent 0 failed).

(princ "=== m37 imp-1 (reclaim step) test suite ===\n")

(require 'imp-ert-report)

(let* ((dir (file-name-directory (or load-file-name default-directory)))
       (root (expand-file-name "../.." dir))
       (corpus (expand-file-name "test-m37-imp1.scm" dir))
       (load-error nil))
  ;; The corpus reads the source tree, so tell it where the root is.
  (eval-scheme (format "(define %%m37-root %S)" root))
  (condition-case err
      (eval-scheme
       (format "(primitive-load %S)" corpus))
    (error (setq load-error err)))
  (let* ((results
          (cond
           (load-error
            (list (list "m37-imp1/corpus-load"
                        (cons 'FAIL (format "%S" load-error)))))
           (t
            (condition-case e
                (let ((r (eval-scheme "(reverse test-results)")))
                  (if (or (not (listp r)) (null r))
                      (list (list "m37-imp1/corpus-empty"
                                  (cons 'FAIL "corpus produced no results")))
                    r))
              (error
               (list (list "m37-imp1/readback"
                           (cons 'FAIL (format "%S" e)))))))))
         (pass 0)
         (fail 0))
    (dolist (result results)
      (let* ((name (car result))
             (status (cadr result))
             (ok (eq status 'PASS)))
        (cond
         (ok
          (imp-register-check-as-ert-test name status)
          (setq pass (1+ pass))
          (princ (format "PASS %s\n" name)))
         ((and (consp status) (eq (car status) 'INFO))
          (princ (format "INFO %s %s\n" name (cadr status))))
         (t
          (imp-register-check-as-ert-test name status)
          (setq fail (1+ fail))
          (princ (format "FAIL %s %S\n" name (cdr result)))))))
    (princ (format "=== %d passed, %d failed, %d total ===\n"
                   pass fail (+ pass fail)))))
