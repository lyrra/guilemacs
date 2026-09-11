;;; test-m30-imp1.el --- M30 imp-1 (table-driven cell subr) suite.
;;;
;;; Pins the M30 imp-1 C core (brief.org M30 imp-1): the cell table and
;;; the two subrs --cell-ref and --cell-set! exist, and the table path
;;; agrees with the old per-cell DEFUN path for one cell per kind
;;; (bool --set-echoing!, fixnum --set-raw-keybuf-count, object
;;; --set-frame-relative-event-pos).  A missing name must signal.
;;;
;;; Wraps test/keyboard/test-m30-imp1.scm -- the Scheme proof corpus.
;;; Loads the Scheme file via eval-scheme, then reads back `test-results`
;;; (list of (NAME STATUS) pairs).  Each pair is reported via princ AND
;;; turned into an ERT test so the harness counts it.  A corpus load
;;; error, a readback error or an empty corpus is a real FAIL (never a
;;; silent 0 failed).  Same shape as test-m29-imp5.el.

(princ "=== m30-imp1 (table-driven cell subr) test suite ===\n")

;; The corpus emits one (NAME STATUS) pair per check.  A corpus FAIL, a
;; corpus load error and a readback error must all surface as a real
;; FAIL -- never as a silent "0 failed".  Each pair also becomes an ERT
;; test so the harness counts it instead of trusting the princ lines.
(let* ((dir (file-name-directory (or load-file-name default-directory)))
       (corpus (expand-file-name "test-m30-imp1.scm" dir))
       (load-error nil))
  (condition-case err
      (eval-scheme
       (format "(primitive-load %S)" corpus))
    (error (setq load-error err)))
  (let* ((results
          (cond
           (load-error
            (list (list "m30-imp1/corpus-load"
                        (cons 'FAIL (format "%S" load-error)))))
           (t
            (condition-case e
                (let ((r (eval-scheme "(reverse test-results)")))
                  (if (or (not (listp r)) (null r))
                      (list (list "m30-imp1/corpus-empty"
                                  (cons 'FAIL "corpus produced no results")))
                    r))
              (error
               (list (list "m30-imp1/readback"
                           (cons 'FAIL (format "%S" e)))))))))
         (pass 0)
         (fail 0))
    (dolist (result results)
      (let* ((name (car result))
             (status (cadr result))
             (ok (eq status 'PASS)))
        ;; Define the ERT test so the harness metric sees it.
        (eval `(ert-deftest ,(intern (format "m30-imp1/%s" name)) ()
                 (should (eq ',status 'PASS))))
        (if ok
            (progn
              (setq pass (1+ pass))
              (princ (format "PASS %s\n" name)))
          (setq fail (1+ fail))
          (princ (format "FAIL %s %S\n" name (cdr result))))))
    (princ (format "=== %d passed, %d failed, %d total ===\n"
                   pass fail (+ pass fail)))))
