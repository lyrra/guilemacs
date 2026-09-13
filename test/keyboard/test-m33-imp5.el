;;; test-m33-imp5.el --- M33 imp-5 (pgtkterm.c read path).
;;;
;;; Pins the M33 imp-5 port (brief.org): the help-echo guards, the
;;; show-help guard, the extra-keyboard-modifiers read, and the 2
;;; mwheel-coalesce-scroll-events reads moved out of src/pgtkterm.c and
;;; into the module (emacs pgtk), procedures pgtk-clear-help-echo?,
;;; pgtk-help-event-action, pgtk-extra-keyboard-modifiers, and
;;; pgtk-mwheel-coalesce-scroll-events?.  The C mechanism (frame
;;; conversion, help_echo_string = Qnil, pgtk_emacs_to_gtk_modifiers,
;;; do_help, any_help_event_p, gen_help_event, the scroll accumulator,
;;; the 2 fabs tests) stays C.
;;;
;;; NOTE: src/pgtkterm.c is NOT compiled at imp-5 (HAVE_PGTK undefined),
;;; so this corpus is the proof by inspection.
;;;
;;; Wraps test/keyboard/test-m33-imp5.scm -- the Scheme audit corpus.
;;; Binds the repo root as %m33-root, loads the Scheme file via
;;; eval-scheme, then reads back `test-results' (list of (NAME STATUS)
;;; pairs).  Each (NAME PASS|FAIL) pair is reported via princ AND turned
;;; into an ERT test so the harness counts it.  Each (NAME INFO VALUE)
;;; pair is printed as an INFO line and is NOT asserted.  A corpus load
;;; error, a readback error or an empty corpus is reported as a real
;;; FAIL (never a silent 0 failed).

(princ "=== m33 imp-5 (pgtkterm.c read path) test suite ===\n")

(let* ((dir (file-name-directory (or load-file-name default-directory)))
       (root (expand-file-name "../.." dir))
       (corpus (expand-file-name "test-m33-imp5.scm" dir))
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
            (list (list "m33-imp5/corpus-load"
                        (cons 'FAIL (format "%S" load-error)))))
           (t
            (condition-case e
                (let ((r (eval-scheme "(reverse test-results)")))
                  (if (or (not (listp r)) (null r))
                      (list (list "m33-imp5/corpus-empty"
                                  (cons 'FAIL "corpus produced no results")))
                    r))
              (error
               (list (list "m33-imp5/readback"
                           (cons 'FAIL (format "%S" e)))))))))
         (pass 0)
         (fail 0))
    (dolist (result results)
      (let* ((name (car result))
             (status (cadr result))
             (ok (eq status 'PASS)))
        (cond
         (ok
          (eval `(ert-deftest ,(intern (format "m33-imp5/%s" name)) ()
                   (should (eq ',status 'PASS))))
          (setq pass (1+ pass))
          (princ (format "PASS %s\n" name)))
         ((and (consp status) (eq (car status) 'INFO))
          (princ (format "INFO %s %s\n" name (cadr status))))
         (t
          (eval `(ert-deftest ,(intern (format "m33-imp5/%s" name)) ()
                   (should (eq ',status 'PASS))))
          (setq fail (1+ fail))
          (princ (format "FAIL %s %S\n" name (cdr result)))))))
    (princ (format "=== %d passed, %d failed, %d total ===\n"
                   pass fail (+ pass fail)))))
