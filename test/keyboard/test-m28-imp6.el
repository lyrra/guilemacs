;;; test-m28-imp6.el --- M28 imp-6 (close-out) suite.
;;;
;;; Pins the M28 end state at HEAD 9689988 (brief.org M28 imp-6): every
;;; DEFUN reclaimed during the M28 cascade reads back as nil, --kbd-empty-p
;;; (the one M28 addition) resolves, and a sample of the stay-C families
;;; still registers its shims.  The remnant line counts are printed, not
;;; asserted.
;;;
;;; Wraps test/keyboard/test-m28-imp6.scm — the Scheme test corpus.
;;; Loads the Scheme file via eval-scheme, then reads back `test-results`
;;; (list of (NAME STATUS) pairs) and reports each via princ.  Same
;;; harness as test-m28-imp5-f6.el.

(princ "=== m28-imp6 close-out (end-state) test suite ===\n")

(let* ((dir (file-name-directory (or load-file-name default-directory)))
       (corpus (expand-file-name "test-m28-imp6.scm" dir)))
  (condition-case err
      (eval-scheme
       (format "(primitive-load %S)" corpus))
    (error (princ (format "M28I6-CORPUS-LOAD-ERROR: %S\n" err)))))

(let ((results (condition-case e
                   (eval-scheme "(reverse test-results)")
                 (error (princ (format "M28I6-READBACK-ERROR: %S\n" e)) '())))
      (pass 0)
      (fail 0))
  (dolist (result results)
    (let* ((name (car result))
           (status (cadr result)))
      (cond
       ((eq status 'PASS)
        (setq pass (1+ pass))
        (princ (format "PASS %s\n" name)))
       ((and (consp status) (eq (car status) 'INFO))
        ;; Informational (printed, not asserted): remnant line counts.
        (princ (format "INFO %s %s\n" name (cadr status))))
       (t
        (setq fail (1+ fail))
        (princ (format "FAIL %s %S\n" name (cdr result)))))))
  (princ (format "=== %d passed, %d failed, %d total ===\n"
                 pass fail (+ pass fail))))
