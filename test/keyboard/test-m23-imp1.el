;;; test-m23-imp1.el --- M23 imp-1 special-variable declaration tests.
;;;
;;; imp-1 moves the 30 genuinely-local DEFVAR_* call sites out of
;;; syms_of_keyboard into (emacs ...) module init-*-registrations
;;; functions as proclaim-special! + set-symbol-default-value! pairs.
;;; See brief.org and mod/emacs/{command-loop,read-char,echo,...}.scm.
;;;
;;; Wraps test/keyboard/test-m23-imp1.scm — the Scheme test corpus.
;;; Loads the Scheme file via eval-scheme, then reads back `test-results`
;;; (list of (NAME STATUS) pairs) and reports each via princ.  Same
;;; harness as test-m22-imp4.el.

(princ "=== m23 imp-1 test suite ===\n")

(let* ((dir (file-name-directory (or load-file-name default-directory)))
       (corpus (expand-file-name "test-m23-imp1.scm" dir)))
  (condition-case err
      (eval-scheme
       (format "(primitive-load %S)" corpus))
    (error (princ (format "M23-IMP1-CORPUS-LOAD-ERROR: %S\n" err)))))

(let ((results (condition-case e
                   (eval-scheme "(reverse test-results)")
                 (error (princ (format "M23-IMP1-READBACK-ERROR: %S\n" e)) '())))
      (pass 0)
      (fail 0))
  (dolist (result results)
    (let* ((name (car result))
           (status (cadr result))
           (ok (eq status 'PASS)))
      (if ok
          (setq pass (1+ pass))
        (setq fail (1+ fail)))
      (princ (format "%s %s%s\n" (if ok "PASS" "FAIL") name
                     (if ok "" (format " %S" (cdr result)))))))
  (princ (format "=== %d passed, %d failed, %d total ===\n"
                 pass fail (+ pass fail))))
