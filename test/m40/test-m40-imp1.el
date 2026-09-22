;;; test-m40-imp1.el --- M40 imp-1 (multibyte predicates) suite.
;;;
;;; Pins the M40 imp-1 port (brief.org): the recorded deviation of
;;; multibyte-string-p (mod/emacs/strings.scm returns nil for every
;;; object; see docs/m40-plan.org §3.1) and a buffer read of
;;; enable-multibyte-characters that takes a buffer argument
;;; (mod/emacs/process-io.scm).  imp-1 adds no C.
;;;
;;; Wraps test/m40/test-m40-imp1.scm -- the Scheme corpus.  This file
;;; creates the two buffers the corpus reads (one unibyte, one
;;; multibyte) through with-current-buffer, so the batch's current
;;; buffer is restored and no state leaks; it binds the repo root as
;;; %m40-root and loads the Scheme file via eval-scheme.  Each
;;; (NAME PASS|FAIL) pair is reported via princ AND turned into an ERT
;;; test so the harness counts it.  A corpus load error, a readback
;;; error or an empty corpus is reported as a real FAIL.

(princ "=== m40 imp-1 (faithful multibyte predicates) test suite ===\n")

(require 'imp-ert-report)

(let* ((dir (file-name-directory (or load-file-name default-directory)))
       (root (expand-file-name "../.." dir))
       (corpus (expand-file-name "test-m40-imp1.scm" dir))
       (load-error nil))
  ;; The corpus reads these buffers by name.  Configure each in its own
  ;; with-current-buffer, which restores the current buffer afterwards.
  (let ((ub (get-buffer-create "m40-imp1-unibyte"))
        (mb (get-buffer-create "m40-imp1-multibyte")))
    (with-current-buffer ub (set-buffer-multibyte nil))
    (with-current-buffer mb (set-buffer-multibyte t)))
  ;; The corpus reads the build tree, so tell it where the root is.
  (eval-scheme (format "(define %%m40-root %S)" root))
  (condition-case err
      (eval-scheme
       (format "(primitive-load %S)" corpus))
    (error (setq load-error err)))
  (let* ((results
          (cond
           (load-error
            (list (list "m40-imp1/corpus-load"
                        (cons 'FAIL (format "%S" load-error)))))
           (t
            (condition-case e
                (let ((r (eval-scheme "(reverse test-results)")))
                  (if (or (not (listp r)) (null r))
                      (list (list "m40-imp1/corpus-empty"
                                  (cons 'FAIL "corpus produced no results")))
                    r))
              (error
               (list (list "m40-imp1/readback"
                           (cons 'FAIL (format "%S" e)))))))))
         (pass 0)
         (fail 0))
    (dolist (result results)
      (let* ((name (car result))
             (status (cadr result))
             (ok (eq status 'PASS)))
        (cond
         (ok
          (imp-register-check-as-ert-test (format "m40-imp1/%s" name) status)
          (setq pass (1+ pass))
          (princ (format "PASS %s\n" name)))
         ((and (consp status) (eq (car status) 'INFO))
          (princ (format "INFO %s %s\n" name (cadr status))))
         (t
          (imp-register-check-as-ert-test (format "m40-imp1/%s" name) status)
          (setq fail (1+ fail))
          (princ (format "FAIL %s %S\n" name (cdr result)))))))
    (princ (format "=== %d passed, %d failed, %d total ===\n"
                   pass fail (+ pass fail)))))
