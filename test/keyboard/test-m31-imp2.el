;;; test-m31-imp2.el --- M31 imp-2: dead SIGDANGER arm + auto-save-interval.
;;;
;;; Pins the M31 imp-2 change (brief.org M31 imp-2).  Two jobs:
;;; the dead #ifdef SIGDANGER arm (keyboard.c / lisp.h / sysdep.c) is
;;; deleted, and auto-save-interval (DEFVAR_INT, default 300) leaves
;;; src/keyboard-globals.c because no C file reads its C variable after
;;; the arm goes.  A boot-loaded module (mod/emacs/command-loop.scm)
;;; declares the name special and sets the C default (300).
;;;
;;; Wraps test/keyboard/test-m31-imp2.scm -- the Scheme proof corpus.
;;; Loads the Scheme file via eval-scheme, then reads back `test-results'
;;; (list of (NAME STATUS) pairs).  Each pair is reported via princ AND
;;; turned into an ERT test so the harness counts it.  A corpus load
;;; error, a readback error or an empty corpus is a real FAIL (never a
;;; silent 0 failed).  Same shape as test-m31-imp1.el.

(princ "=== m31 imp-2 (SIGDANGER arm + auto-save-interval to Scheme) test suite ===\n")

;; The corpus emits one (NAME STATUS) pair per check.  A corpus FAIL, a
;; corpus load error and a readback error must all surface as a real
;; FAIL -- never as a silent "0 failed".  Each pair also becomes an ERT
;; test so the harness counts it instead of trusting the princ lines.
(let* ((dir (file-name-directory (or load-file-name default-directory)))
       (root (expand-file-name "../.." dir))
       (corpus (expand-file-name "test-m31-imp2.scm" dir))
       (load-error nil))
  ;; The corpus reads the build tree (the static scans), so tell it
  ;; where the repo root is.
  (eval-scheme (format "(define %%m31-root %S)" root))
  (condition-case err
      (eval-scheme
       (format "(primitive-load %S)" corpus))
    (error (setq load-error err)))
  (let* ((results
          (cond
           (load-error
            (list (list "m31-imp2/corpus-load"
                        (cons 'FAIL (format "%S" load-error)))))
           (t
            (condition-case e
                (let ((r (eval-scheme "(reverse test-results)")))
                  (if (or (not (listp r)) (null r))
                      (list (list "m31-imp2/corpus-empty"
                                  (cons 'FAIL "corpus produced no results")))
                    r))
              (error
               (list (list "m31-imp2/readback"
                           (cons 'FAIL (format "%S" e)))))))))
         (pass 0)
         (fail 0))
    (dolist (result results)
      (let* ((name (car result))
             (status (cadr result))
             (ok (eq status 'PASS)))
        ;; Define the ERT test so the harness metric sees it.
        (eval `(ert-deftest ,(intern (format "m31-imp2/%s" name)) ()
                 (should (eq ',status 'PASS))))
        (if ok
            (progn
              (setq pass (1+ pass))
              (princ (format "PASS %s\n" name)))
          (setq fail (1+ fail))
          (princ (format "FAIL %s %S\n" name (cdr result))))))
    (princ (format "=== %d passed, %d failed, %d total ===\n"
                   pass fail (+ pass fail)))))
