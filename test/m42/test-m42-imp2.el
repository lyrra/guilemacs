;;; test-m42-imp2.el --- M42 imp-2 (the TTY raw-input read path) suite.
;;;
;;; The FFI implementation landed in f2ea65bf and was retired. The two
;;; portable C syscall leaves are restored; Scheme keeps the read policy,
;;; decoding, quit handling, and event storage.
;;;
;;; Wraps test/m42/test-m42-imp2.scm -- the Scheme corpus.  Binds the
;;; repo root as %m42-root, loads the Scheme file via eval-scheme, then
;;; reads back `test-results' (list of (NAME STATUS) pairs).  Each
;;; (NAME PASS|FAIL) pair is reported via princ AND turned into an ERT
;;; test so the harness counts it.  A corpus load error, a readback
;;; error or an empty corpus is reported as a real FAIL (never a silent
;;; 0 failed).
;;;
;;; The corpus probes the real C leaves' non-TTY behavior and exercises
;;; the Scheme policy with those leaves stubbed. It also checks the
;;; retirement pins in mod/emacs/gobble.scm and src/keyboard.c.

(princ "=== m42 imp-2 (the TTY raw-input read path) test suite ===\n")

(require 'imp-ert-report)

(defvar m42-imp2--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))

(let* ((dir (file-name-directory (or load-file-name default-directory)))
       (corpus (expand-file-name "test-m42-imp2.scm" dir))
       (load-error nil))
  ;; The corpus reads the build tree, so tell it where the root is.
  (eval-scheme (format "(define %%m42-root %S)" m42-imp2--root))
  (condition-case err
      (eval-scheme
       (format "(primitive-load %S)" corpus))
    (error (setq load-error err)))
  (let* ((results
          (cond
           (load-error
            (list (list "m42-imp2/corpus-load"
                        (cons 'FAIL (format "%S" load-error)))))
           (t
            (condition-case e
                (let ((r (eval-scheme "(reverse test-results)")))
                  (if (or (not (listp r)) (null r))
                      (list (list "m42-imp2/corpus-empty"
                                  (cons 'FAIL "corpus produced no results")))
                    r))
              (error
               (list (list "m42-imp2/readback"
                           (cons 'FAIL (format "%S" e)))))))))
         (pass 0)
         (fail 0))
    (dolist (result results)
      (let* ((name (car result))
             (status (cadr result))
             (ok (eq status 'PASS)))
        (cond
         (ok
          (imp-register-check-as-ert-test (format "m42-imp2/%s" name) status)
          (setq pass (1+ pass))
          (princ (format "PASS %s\n" name)))
         ((and (consp status) (eq (car status) 'INFO))
          (princ (format "INFO %s %s\n" name (cadr status))))
         (t
          (imp-register-check-as-ert-test (format "m42-imp2/%s" name) status)
          (setq fail (1+ fail))
          (princ (format "FAIL %s %S\n" name (cdr result)))))))

    (princ (format "=== %d passed, %d failed, %d total ===\n"
                   pass fail (+ pass fail)))))
