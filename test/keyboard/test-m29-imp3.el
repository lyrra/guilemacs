;;; test-m29-imp3.el --- M29 imp-3 (W32 / Cygwin build-arm removal) suite.
;;;
;;; Pins the M29 imp-3 removal (brief.org M29 imp-3): no W32 / Cygwin
;;; build-arm token survives in configure.ac or the Makefiles, no build
;;; file names a deleted W32 file or nt/ path, and every W32 source,
;;; src/cygw32.c, src/cygw32.h, lib-src/ntlib.{c,h}, and nt/ listed in
;;; the brief is gone.  The opsys cygwin
;;; / mingw32 host cases and HAVE_W32=no stay; the dead HAVE_NTGUI /
;;; DOS_NT arms in src/keyboard.c and doc/emacs/msdos.texi stay.
;;;
;;; Wraps test/keyboard/test-m29-imp3.scm -- the Scheme audit corpus.
;;; Binds the repo root as %m29-root, loads the Scheme file via
;;; eval-scheme, then reads back `test-results` (list of (NAME STATUS)
;;; pairs) and reports each via princ.  Same harness as
;;; test-m29-imp2.el.

(princ "=== m29-imp3 (W32 / Cygwin build-arm removal) test suite ===\n")

(let* ((dir (file-name-directory (or load-file-name default-directory)))
       (root (expand-file-name "../.." dir))
       (corpus (expand-file-name "test-m29-imp3.scm" dir)))
  ;; The corpus reads the build tree, so tell it where the root is.
  (eval-scheme (format "(define %%m29-root %S)" root))
  (condition-case err
      (eval-scheme
       (format "(primitive-load %S)" corpus))
    (error (princ (format "M29I3-CORPUS-LOAD-ERROR: %S\n" err)))))

(let ((results (condition-case e
                   (eval-scheme "(reverse test-results)")
                 (error (princ (format "M29I3-READBACK-ERROR: %S\n" e)) '())))
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
