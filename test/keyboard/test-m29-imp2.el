;;; test-m29-imp2.el --- M29 imp-2 (Haiku build-arm removal) suite.
;;;
;;; Pins the M29 imp-2 removal (brief.org M29 imp-2): no Haiku
;;; build-arm token survives in configure.ac or the Makefiles, no build
;;; file names a deleted Haiku object or header, and every Haiku source
;;; listed in the brief is gone.  The opsys=haiku host case, the
;;; HAVE_BE_APP apparatus, and the dead HAVE_HAIKU arm in src/keyboard.c
;;; stay.
;;;
;;; Wraps test/keyboard/test-m29-imp2.scm -- the Scheme audit corpus.
;;; Binds the repo root as %m29-root, loads the Scheme file via
;;; eval-scheme, then reads back `test-results` (list of (NAME STATUS)
;;; pairs) and reports each via princ.  Same harness as
;;; test-m29-imp1.el.

(princ "=== m29-imp2 (Haiku build-arm removal) test suite ===\n")

(let* ((dir (file-name-directory (or load-file-name default-directory)))
       (root (expand-file-name "../.." dir))
       (corpus (expand-file-name "test-m29-imp2.scm" dir)))
  ;; The corpus reads the build tree, so tell it where the root is.
  (eval-scheme (format "(define %%m29-root %S)" root))
  (condition-case err
      (eval-scheme
       (format "(primitive-load %S)" corpus))
    (error (princ (format "M29I2-CORPUS-LOAD-ERROR: %S\n" err)))))

(let ((results (condition-case e
                   (eval-scheme "(reverse test-results)")
                 (error (princ (format "M29I2-READBACK-ERROR: %S\n" e)) '())))
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
