;;; test-m31-imp3.el --- M31 imp-3 (close-out) suite.
;;;
;;; Pins the M31 end state (brief.org M31 imp-3): the three converted
;;; declarations (last-event-device, cannot-suspend, auto-save-interval)
;;; keep no DEFVAR_* site in src/keyboard-globals.c and no storage cell
;;; in the generated src/globals.h, each is special after boot with its
;;; C default (#nil, #nil, 300), one write-then-read round trip holds,
;;; and there is no over-deletion (the 8 DEFVAR_KBOARD sites and the 31
;;; DEFSYM sites stay).  The remnant line counts, the site counts and
;;; the DEFUN count are printed (INFO), not asserted.
;;;
;;; Wraps test/keyboard/test-m31-imp3.scm -- the Scheme audit corpus.
;;; Binds the repo root as %m31-root, loads the Scheme file via
;;; eval-scheme, then reads back `test-results' (list of (NAME STATUS)
;;; pairs).  Each (NAME PASS|FAIL) pair is reported via princ AND turned
;;; into an ERT test so the harness counts it.  Each (NAME INFO VALUE)
;;; pair is printed as an INFO line and is NOT asserted.  A corpus load
;;; error, a readback error or an empty corpus is reported as a real
;;; FAIL (never a silent 0 failed).

(princ "=== m31 imp-3 close-out (end-state) test suite ===\n")

;; The corpus emits one (NAME STATUS) pair per check.  A corpus FAIL, a
;; corpus load error and a readback error must all surface as a real
;; FAIL -- never as a silent "0 failed".  Each PASS/FAIL pair also
;; becomes an ERT test so the harness counts it instead of trusting the
;; princ lines.  INFO pairs are printed, not asserted.
(let* ((dir (file-name-directory (or load-file-name default-directory)))
       (root (expand-file-name "../.." dir))
       (corpus (expand-file-name "test-m31-imp3.scm" dir))
       (load-error nil))
  ;; The corpus reads the build tree, so tell it where the root is.
  (eval-scheme (format "(define %%m31-root %S)" root))
  (condition-case err
      (eval-scheme
       (format "(primitive-load %S)" corpus))
    (error (setq load-error err)))
  (let* ((results
          (cond
           (load-error
            (list (list "m31-imp3/corpus-load"
                        (cons 'FAIL (format "%S" load-error)))))
           (t
            (condition-case e
                (let ((r (eval-scheme "(reverse test-results)")))
                  (if (or (not (listp r)) (null r))
                      (list (list "m31-imp3/corpus-empty"
                                  (cons 'FAIL "corpus produced no results")))
                    r))
              (error
               (list (list "m31-imp3/readback"
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
          (eval `(ert-deftest ,(intern (format "m31-imp3/%s" name)) ()
                   (should (eq ',status 'PASS))))
          (setq pass (1+ pass))
          (princ (format "PASS %s\n" name)))
         ((and (consp status) (eq (car status) 'INFO))
          ;; Informational (printed, not asserted): counts.
          (princ (format "INFO %s %s\n" name (cadr status))))
         (t
          (eval `(ert-deftest ,(intern (format "m31-imp3/%s" name)) ()
                   (should (eq ',status 'PASS))))
          (setq fail (1+ fail))
          (princ (format "FAIL %s %S\n" name (cdr result)))))))
    (princ (format "=== %d passed, %d failed, %d total ===\n"
                   pass fail (+ pass fail)))))
