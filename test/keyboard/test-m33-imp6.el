;;; test-m33-imp6.el --- M33 imp-6 (2 DEFVAR_* names move to Scheme).
;;;
;;; Pins the M33 imp-6 port (brief.org): the DEFVAR_* sites and the
;;; default assignments for extra-keyboard-modifiers (INT, default 0)
;;; and mwheel-coalesce-scroll-events (BOOL, default true) are deleted
;;; from src/keyboard-globals.c, and the two rows are added to the M23
;;; declaration table in mod/emacs/command-loop.scm.  No compiled C
;;; file reads either cell: src/xterm.c reads through (emacs xterm),
;;; src/pgtkterm.c reads through (emacs pgtk), and the main queue reads
;;; with symbol-value.  The C keeps x_emacs_to_x_modifiers, the
;;; scm_to_intmax dispatcher, and the fabs tests.
;;;
;;; NOTE: src/pgtkterm.c is NOT compiled (HAVE_PGTK undefined), so its
;;; cleanliness is proven by the keyword scan, not by the build.
;;;
;;; Wraps test/keyboard/test-m33-imp6.scm -- the Scheme audit corpus.
;;; Binds the repo root as %m33-root, loads the Scheme file via
;;; eval-scheme, then reads back `test-results' (list of (NAME STATUS)
;;; pairs).  Each (NAME PASS|FAIL) pair is reported via princ AND turned
;;; into an ERT test so the harness counts it.  Each (NAME INFO VALUE)
;;; pair is printed as an INFO line and is NOT asserted.  A corpus load
;;; error, a readback error or an empty corpus is reported as a real
;;; FAIL (never a silent 0 failed).

(princ "=== m33 imp-6 (2 DEFVAR_* names move to Scheme) test suite ===\n")

(let* ((dir (file-name-directory (or load-file-name default-directory)))
       (root (expand-file-name "../.." dir))
       (corpus (expand-file-name "test-m33-imp6.scm" dir))
       (load-error nil))
  ;; The corpus reads the build tree, so tell it where the root is.
  (eval-scheme (format "(define %%m33-root %S)" root))
  (condition-case err
      (eval-scheme
       (format "(primitive-load %S)" corpus))
    (error (setq load-error err)))
  (let* ((results
          (cond
           (load-error
            (list (list "m33-imp6/corpus-load"
                        (cons 'FAIL (format "%S" load-error)))))
           (t
            (condition-case e
                (let ((r (eval-scheme "(reverse test-results)")))
                  (if (or (not (listp r)) (null r))
                      (list (list "m33-imp6/corpus-empty"
                                  (cons 'FAIL "corpus produced no results")))
                    r))
              (error
               (list (list "m33-imp6/readback"
                           (cons 'FAIL (format "%S" e)))))))))
         (pass 0)
         (fail 0))
    (dolist (result results)
      (let* ((name (car result))
             (status (cadr result))
             (ok (eq status 'PASS)))
        (cond
         (ok
          (eval `(ert-deftest ,(intern (format "m33-imp6/%s" name)) ()
                   (should (eq ',status 'PASS))))
          (setq pass (1+ pass))
          (princ (format "PASS %s\n" name)))
         ((and (consp status) (eq (car status) 'INFO))
          (princ (format "INFO %s %s\n" name (cadr status))))
         (t
          (eval `(ert-deftest ,(intern (format "m33-imp6/%s" name)) ()
                   (should (eq ',status 'PASS))))
          (setq fail (1+ fail))
          (princ (format "FAIL %s %S\n" name (cdr result)))))))
    (princ (format "=== %d passed, %d failed, %d total ===\n"
                   pass fail (+ pass fail)))))
