;;; test-m29-imp5.el --- M29 imp-5 (dropped-platform sweep) suite.
;;;
;;; Pins the M29 imp-5 sweep (brief.org M29 imp-5): no dropped-platform
;;; token survives in src/keyboard.c, every config-variance arm stays,
;;; the seven Lisp / etc leftovers are gone, no live build file names a
;;; deleted path, and there is no over-deletion (AH_TEMPLATE([MSDOS])
;;; and the cygwin / mingw32 opsys cases stay in configure.ac;
;;; FRAME_MSDOS_P stays in src/keyboard.c).
;;;
;;; Wraps test/keyboard/test-m29-imp5.scm -- the Scheme audit corpus.
;;; Binds the repo root as %m29-root, loads the Scheme file via
;;; eval-scheme, then reads back `test-results` (list of (NAME STATUS)
;;; pairs).  Each pair is reported via princ AND turned into an ERT test
;;; so the harness counts it.  A corpus load error, a readback error or
;;; an empty corpus is reported as a real FAIL (never a silent 0 failed).

(princ "=== m29-imp5 (dropped-platform sweep) test suite ===\n")

;; The corpus emits one (NAME STATUS) pair per check.  A corpus FAIL, a
;; corpus load error and a readback error must all surface as a real
;; FAIL -- never as a silent "0 failed".  Each pair also becomes an ERT
;; test so the harness counts it instead of trusting the princ lines.
(let* ((dir (file-name-directory (or load-file-name default-directory)))
       (root (expand-file-name "../.." dir))
       (corpus (expand-file-name "test-m29-imp5.scm" dir))
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
            (list (list "m29-imp5/corpus-load"
                        (cons 'FAIL (format "%S" load-error)))))
           (t
            (condition-case e
                (let ((r (eval-scheme "(reverse test-results)")))
                  (if (or (not (listp r)) (null r))
                      (list (list "m29-imp5/corpus-empty"
                                  (cons 'FAIL "corpus produced no results")))
                    r))
              (error
               (list (list "m29-imp5/readback"
                           (cons 'FAIL (format "%S" e)))))))))
         (pass 0)
         (fail 0))
    (dolist (result results)
      (let* ((name (car result))
             (status (cadr result))
             (ok (eq status 'PASS)))
        ;; Define the ERT test so the harness metric sees it.
        (eval `(ert-deftest ,(intern (format "m29-imp5/%s" name)) ()
                 (should (eq ',status 'PASS))))
        (if ok
            (progn
              (setq pass (1+ pass))
              (princ (format "PASS %s\n" name)))
          (setq fail (1+ fail))
          (princ (format "FAIL %s %S\n" name (cdr result))))))
    (princ (format "=== %d passed, %d failed, %d total ===\n"
                   pass fail (+ pass fail)))))
