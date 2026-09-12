;;; test-m31-imp1.el --- M31 imp-1: two DEFVAR_* names move to Scheme.
;;;
;;; Pins the M31 imp-1 change (brief.org M31 imp-1): last-event-device
;;; (DEFVAR_LISP, default nil) and cannot-suspend (DEFVAR_BOOL, default
;;; false) leave src/keyboard-globals.c because no C file reads their C
;;; variables.  A boot-loaded module (mod/emacs/command-loop.scm)
;;; declares both special and sets the C default (#nil for both).
;;;
;;; Wraps test/keyboard/test-m31-imp1.scm -- the Scheme proof corpus.
;;; Loads the Scheme file via eval-scheme, then reads back `test-results'
;;; (list of (NAME STATUS) pairs).  The elisp side of the write-then-read
;;; check (cannot-suspend) is done here and appended to the results.
;;; Each pair is reported via princ AND turned into an ERT test so the
;;; harness counts it.  A corpus load error, a readback error or an empty
;;; corpus is a real FAIL (never a silent 0 failed).  Same shape as
;;; test-m30-imp5.el.

(princ "=== m31 imp-1 (last-event-device + cannot-suspend to Scheme) test suite ===\n")

;; The corpus emits one (NAME STATUS) pair per check.  A corpus FAIL, a
;; corpus load error and a readback error must all surface as a real
;; FAIL -- never as a silent "0 failed".  Each pair also becomes an ERT
;; test so the harness counts it instead of trusting the princ lines.
(let* ((dir (file-name-directory (or load-file-name default-directory)))
       (root (expand-file-name "../.." dir))
       (corpus (expand-file-name "test-m31-imp1.scm" dir))
       (load-error nil))
  ;; The corpus reads the build tree (the two static scans), so tell it
  ;; where the repo root is.
  (eval-scheme (format "(define %%m31-root %S)" root))
  (condition-case err
      (eval-scheme
       (format "(primitive-load %S)" corpus))
    (error (setq load-error err)))
  (let* ((scheme-results
          (cond
           (load-error
            (list (list "m31-imp1/corpus-load"
                        (cons 'FAIL (format "%S" load-error)))))
           (t
            (condition-case e
                (let ((r (eval-scheme "(reverse test-results)")))
                  (if (or (not (listp r)) (null r))
                      (list (list "m31-imp1/corpus-empty"
                                  (cons 'FAIL "corpus produced no results")))
                    r))
              (error
               (list (list "m31-imp1/readback"
                           (cons 'FAIL (format "%S" e)))))))))
         ;; Check 5 (elisp side): write-then-read cannot-suspend from
         ;; elisp.  The C default was false (nil); setq a fresh value,
         ;; read it back, restore the boot value.
         (elisp-results
          (let ((old (symbol-value 'cannot-suspend))
                (ok nil) (got nil))
            (condition-case _e
                (progn
                  (setq cannot-suspend 'm31-imp1-elisp)
                  (setq got (symbol-value 'cannot-suspend))
                  (setq ok (eq got 'm31-imp1-elisp)))
              (error nil))
            (setq cannot-suspend old)
            (list (list "m31/imp1/write-read/cannot-suspend"
                        (if ok 'PASS (list 'FAIL 'expected 'm31-imp1-elisp 'got got))))))
         (results (append scheme-results elisp-results))
         (pass 0)
         (fail 0))
    (dolist (result results)
      (let* ((name (car result))
             (status (cadr result))
             (ok (eq status 'PASS)))
        ;; Define the ERT test so the harness metric sees it.
        (eval `(ert-deftest ,(intern (format "m31-imp1/%s" name)) ()
                 (should (eq ',status 'PASS))))
        (if ok
            (progn
              (setq pass (1+ pass))
              (princ (format "PASS %s\n" name)))
          (setq fail (1+ fail))
          (princ (format "FAIL %s %S\n" name (cdr result))))))
    (princ (format "=== %d passed, %d failed, %d total ===\n"
                   pass fail (+ pass fail)))))
