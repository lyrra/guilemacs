;;; test-m29-imp6.el --- M29 imp-6 (close-out) suite.
;;;
;;; Pins the M29 end state (brief.org M29 imp-6): the dropped-platform
;;; paths are gone from the tree and the build, src/keyboard.c keeps no
;;; dropped-platform token, the config-variance arms stay, the imp-5
;;; sweep result stays, and there is no over-deletion (AH_TEMPLATE
;;; [MSDOS] and the cygwin / mingw32 / haiku opsys cases stay in
;;; configure.ac; FRAME_MSDOS_P and nextstep/ stay).  The remnant line
;;; counts are printed (INFO), not asserted.
;;;
;;; Wraps test/keyboard/test-m29-imp6.scm -- the Scheme audit corpus.
;;; Binds the repo root as %m29-root, loads the Scheme file via
;;; eval-scheme, then reads back `test-results` (list of (NAME STATUS)
;;; pairs).  Each (NAME PASS|FAIL) pair is reported via princ AND turned
;;; into an ERT test so the harness counts it.  Each (NAME INFO VALUE)
;;; pair is printed as an INFO line and is NOT asserted (m28-imp6
;;; style).  A corpus load error, a readback error or an empty corpus is
;;; reported as a real FAIL (never a silent 0 failed).

(princ "=== m29-imp6 close-out (end-state) test suite ===\n")

;; The corpus emits one (NAME STATUS) pair per check.  A corpus FAIL, a
;; corpus load error and a readback error must all surface as a real
;; FAIL -- never as a silent "0 failed".  Each PASS/FAIL pair also
;; becomes an ERT test so the harness counts it instead of trusting the
;; princ lines.  INFO pairs are printed, not asserted.
(let* ((dir (file-name-directory (or load-file-name default-directory)))
       (root (expand-file-name "../.." dir))
       (corpus (expand-file-name "test-m29-imp6.scm" dir))
       (load-error nil))
  ;; The corpus reads the build tree, so tell it where the root is.
  (eval-scheme (format "(define %%m29-root %S)" root))
  (condition-case err
      (eval-scheme
       (format "(primitive-load %S)" corpus))
    (error (setq load-error err)))
  (let* ((results
          (cond
           (load-error
            (list (list "m29-imp6/corpus-load"
                        (cons 'FAIL (format "%S" load-error)))))
           (t
            (condition-case e
                (let ((r (eval-scheme "(reverse test-results)")))
                  (if (or (not (listp r)) (null r))
                      (list (list "m29-imp6/corpus-empty"
                                  (cons 'FAIL "corpus produced no results")))
                    r))
              (error
               (list (list "m29-imp6/readback"
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
          (eval `(ert-deftest ,(intern (format "m29-imp6/%s" name)) ()
                   (should (eq ',status 'PASS))))
          (setq pass (1+ pass))
          (princ (format "PASS %s\n" name)))
         ((and (consp status) (eq (car status) 'INFO))
          ;; Informational (printed, not asserted): remnant line counts.
          (princ (format "INFO %s %s\n" name (cadr status))))
         (t
          (eval `(ert-deftest ,(intern (format "m29-imp6/%s" name)) ()
                   (should (eq ',status 'PASS))))
          (setq fail (1+ fail))
          (princ (format "FAIL %s %S\n" name (cdr result)))))))
    (princ (format "=== %d passed, %d failed, %d total ===\n"
                   pass fail (+ pass fail)))))
