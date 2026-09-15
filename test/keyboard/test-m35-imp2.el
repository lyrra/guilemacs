;;; test-m35-imp2.el --- M35 imp-2 (residual-stub disposition) suite.
;;;
;;; Pins the M35 imp-2 disposition (brief.org): every residual keyboard
;;; stub keeps C, because each keeps a live buildable C caller and M35
;;; adds no new porting.  gen_help_event and safe_run_hooks each name
;;; M36+; the other seven stubs name M36+ or the final remnant.  The
;;; census is corrected to 15 caller files (14 buildable + NS) for
;;; kbd_buffer_store_event.  imp-2 changes no C file and retires no stub.
;;;
;;; Wraps test/keyboard/test-m35-imp2.scm -- the Scheme audit corpus.
;;; The corpus pins each definition, each live buildable C caller, the
;;; caller-file census, and the record in docs/kb.org and
;;; docs/m35-plan.org.
;;;
;;; Binds the repo root as %m35-root, loads the Scheme file via
;;; eval-scheme, then reads back `test-results' (list of (NAME STATUS)
;;; pairs).  Each (NAME PASS|FAIL) pair is reported via princ AND turned
;;; into an ERT test so the harness counts it.  Each (NAME INFO VALUE)
;;; pair is printed as an INFO line and is NOT asserted.  A corpus load
;;; error, a readback error or an empty corpus is reported as a real
;;; FAIL (never a silent 0 failed).

(princ "=== m35 imp-2 (residual-stub disposition) test suite ===\n")

;; The corpus emits one (NAME STATUS) pair per check.  A corpus FAIL, a
;; corpus load error and a readback error must all surface as a real
;; FAIL -- never as a silent "0 failed".  Each PASS/FAIL pair also
;; becomes an ERT test so the harness counts it instead of trusting the
;; princ lines.  INFO pairs are printed, not asserted.
(let* ((dir (file-name-directory (or load-file-name default-directory)))
       (root (expand-file-name "../.." dir))
       (corpus (expand-file-name "test-m35-imp2.scm" dir))
       (load-error nil))
  ;; The corpus reads the source tree, so tell it where the root is.
  (eval-scheme (format "(define %%m35-root %S)" root))
  (condition-case err
      (eval-scheme
       (format "(primitive-load %S)" corpus))
    (error (setq load-error err)))
  (let* ((results
          (cond
           (load-error
            (list (list "m35-imp2/corpus-load"
                        (cons 'FAIL (format "%S" load-error)))))
           (t
            (condition-case e
                (let ((r (eval-scheme "(reverse test-results)")))
                  (if (or (not (listp r)) (null r))
                      (list (list "m35-imp2/corpus-empty"
                                  (cons 'FAIL "corpus produced no results")))
                    r))
              (error
               (list (list "m35-imp2/readback"
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
          ;; The corpus name is already namespaced (m35/imp2/...), so use
          ;; it verbatim; do not prepend a second m35-imp2/ prefix.
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
