;;; elisp-stringp.el --- the (emacs strings) predicate arms.
;;;
;;; Wraps test/strings/elisp-stringp.scm -- a SCHEME-MODULE behaviour
;;; test.  It calls the procedures of (emacs strings) directly, because
;;; the behaviour under test is not reachable from elisp:
;;; `elisp-stringp' holds an emacs-string wrapper arm behind both an
;;; `or' short-circuit and a `defined?' guard that reads the dynamic
;;; current module.  An elisp (stringp X) call satisfies neither
;;; condition, so test/pre/stringp.scm cannot cover the arm however many
;;; cases it holds -- see the corpus header for the full reasoning.
;;;
;;; Each (NAME PASS|FAIL) pair the corpus reports is princ'd AND turned
;;; into a real ERT test, so the harness counts it and the exit code
;;; reflects it.  A corpus load error or an empty corpus is a real FAIL.

(princ "=== (emacs strings) predicate-arm suite ===\n")

(require 'imp-ert-report)

(let* ((dir (file-name-directory (or load-file-name default-directory)))
       (corpus (expand-file-name "elisp-stringp.scm" dir))
       (load-error nil))
  (condition-case err
      (eval-scheme (format "(primitive-load %S)" corpus))
    (error (setq load-error err)))
  (let* ((results
          (cond
           (load-error
            (list (list "strings/corpus-load"
                        (cons 'FAIL (format "%S" load-error)))))
           (t
            (condition-case e
                (let ((r (eval-scheme "(reverse test-results)")))
                  (if (or (not (listp r)) (null r))
                      (list (list "strings/corpus-empty"
                                  (cons 'FAIL "corpus produced no results")))
                    r))
              (error
               (list (list "strings/readback"
                           (cons 'FAIL (format "%S" e)))))))))
         (pass 0)
         (fail 0))
    (dolist (result results)
      (let* ((name (car result))
             (status (cadr result))
             (ok (eq status 'PASS)))
        (if ok
            (progn
              (imp-register-check-as-ert-test (format "strings/%s" name) status)
              (setq pass (1+ pass))
              (princ (format "PASS %s\n" name)))
          (imp-register-check-as-ert-test (format "strings/%s" name) status)
          (setq fail (1+ fail))
          (princ (format "FAIL %s %S\n" name (cdr result))))))
    (princ (format "=== %d passed, %d failed, %d total ===\n"
                   pass fail (+ pass fail)))))
