;;; test-m29-imp1.el --- M29 imp-1 (Android build-arm removal) suite.
;;;
;;; Pins the M29 imp-1 removal at HEAD ce11ca1 (brief.org M29 imp-1): no
;;; Android build-arm token survives in configure.ac or the Makefiles, no
;;; build file names a deleted Android source, and every Android source
;;; or directory listed in the brief is gone.  The two gnulib
;;; gl_CHECK_FUNCS_ANDROID calls stay (they are gnulib, not Emacs build
;;; support).
;;;
;;; Wraps test/keyboard/test-m29-imp1.scm -- the Scheme audit corpus.
;;; Binds the repo root as %m29-root, loads the Scheme file via
;;; eval-scheme, then reads back `test-results` (list of (NAME STATUS)
;;; pairs) and reports each via princ.  Same harness as
;;; test-m28-imp6.el.

(princ "=== m29-imp1 (Android build-arm removal) test suite ===\n")

(let* ((dir (file-name-directory (or load-file-name default-directory)))
       (root (expand-file-name "../.." dir))
       (corpus (expand-file-name "test-m29-imp1.scm" dir)))
  ;; The corpus reads the build tree, so tell it where the root is.
  (eval-scheme (format "(define %%m29-root %S)" root))
  (condition-case err
      (eval-scheme
       (format "(primitive-load %S)" corpus))
    (error (princ (format "M29I1-CORPUS-LOAD-ERROR: %S\n" err)))))

(let ((results (condition-case e
                   (eval-scheme "(reverse test-results)")
                 (error (princ (format "M29I1-READBACK-ERROR: %S\n" e)) '())))
      (pass 0)
      (fail 0))
  (dolist (result results)
    (let* ((name (car result))
           (status (cadr result)))
      (cond
       ((eq status 'PASS)
        (setq pass (1+ pass))
        (princ (format "PASS %s\n" name)))
       (t
        (setq fail (1+ fail))
        (princ (format "FAIL %s %S\n" name (cdr result)))))))
  (princ (format "=== %d passed, %d failed, %d total ===\n"
                 pass fail (+ pass fail))))
