;;; test-m29-imp4.el --- M29 imp-4 (MS-DOS build-arm removal) suite.
;;;
;;; Pins the M29 imp-4 removal (brief.org M29 imp-4): no MS-DOS
;;; build-arm token survives in src/Makefile.in or the doc/emacs files,
;;; no build file names a deleted MS-DOS file, and every MS-DOS source,
;;; the msdos/ directory, and doc/emacs/msdos.texi / msdos-xtra.texi
;;; listed in the brief is gone.  AH_TEMPLATE([MSDOS]) stays in
;;; configure.ac; the dead DOS_NT / HAVE_X_WINDOWS arms in
;;; src/keyboard.c stay; doc/misc/efaq-w32.texi keeps its node and the
;;; @xref{Cygwin}; nextstep/ stays.
;;;
;;; Wraps test/keyboard/test-m29-imp4.scm -- the Scheme audit corpus.
;;; Binds the repo root as %m29-root, loads the Scheme file via
;;; eval-scheme, then reads back `test-results` (list of (NAME STATUS)
;;; pairs) and reports each via princ.  Same harness as
;;; test-m29-imp3.el.

(princ "=== m29-imp4 (MS-DOS build-arm removal) test suite ===\n")

(let* ((dir (file-name-directory (or load-file-name default-directory)))
       (root (expand-file-name "../.." dir))
       (corpus (expand-file-name "test-m29-imp4.scm" dir)))
  ;; The corpus reads the build tree, so tell it where the root is.
  (eval-scheme (format "(define %%m29-root %S)" root))
  (condition-case err
      (eval-scheme
       (format "(primitive-load %S)" corpus))
    (error (princ (format "M29I4-CORPUS-LOAD-ERROR: %S\n" err)))))

(let ((results (condition-case e
                   (eval-scheme "(reverse test-results)")
                 (error (princ (format "M29I4-READBACK-ERROR: %S\n" e)) '())))
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
