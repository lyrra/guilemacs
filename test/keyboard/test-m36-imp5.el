;;; test-m36-imp5.el --- M36 imp-5 (close-out) suite.
;;;
;;; Pins the M36 imp-5 close-out (brief.org): the brief.org 4 surface
;;; anchors match the record, the combined surface is under the 11,960
;;; budget, the seven M36+ stubs stay retired (no definition, no extern,
;;; no live buildable C caller), the unbuilt NS-only and PGTK-only
;;; callers are recorded, criterion 4 stays true, no --=-shim is
;;; orphaned, and M36 is marked closed in the docs.  imp-5 changes no C
;;; file and retires no stub.
;;;
;;; Wraps test/keyboard/test-m36-imp5.scm -- the Scheme audit corpus.
;;;
;;; Binds the repo root as %m36-root, loads the Scheme file via
;;; eval-scheme, then reads back `test-results' (list of (NAME STATUS)
;;; pairs).  Each (NAME PASS|FAIL) pair is reported via princ AND turned
;;; into an ERT test so the harness counts it.  Each (NAME INFO VALUE)
;;; pair is printed as an INFO line and is NOT asserted.  A corpus load
;;; error, a readback error or an empty corpus is reported as a real
;;; FAIL (never a silent 0 failed).

(princ "=== m36 imp-5 (close-out) test suite ===\n")

(let* ((dir (file-name-directory (or load-file-name default-directory)))
       (root (expand-file-name "../.." dir))
       (corpus (expand-file-name "test-m36-imp5.scm" dir))
       (load-error nil))
  ;; The corpus reads the source tree, so tell it where the root is.
  (eval-scheme (format "(define %%m36-root %S)" root))
  (condition-case err
      (eval-scheme
       (format "(primitive-load %S)" corpus))
    (error (setq load-error err)))
  (let* ((results
          (cond
           (load-error
            (list (list "m36-imp5/corpus-load"
                        (cons 'FAIL (format "%S" load-error)))))
           (t
            (condition-case e
                (let ((r (eval-scheme "(reverse test-results)")))
                  (if (or (not (listp r)) (null r))
                      (list (list "m36-imp5/corpus-empty"
                                  (cons 'FAIL "corpus produced no results")))
                    r))
              (error
               (list (list "m36-imp5/readback"
                           (cons 'FAIL (format "%S" e)))))))))
         (pass 0)
         (fail 0))
    (dolist (result results)
      (let* ((name (car result))
             (status (cadr result))
             (ok (eq status 'PASS)))
        (cond
         (ok
          (eval `(ert-deftest ,(intern name) ()
                   (should (eq ',status 'PASS))))
          (setq pass (1+ pass))
          (princ (format "PASS %s\n" name)))
         ((and (consp status) (eq (car status) 'INFO))
          (princ (format "INFO %s %s\n" name (cadr status))))
         (t
          (eval `(ert-deftest ,(intern name) ()
                   (should (eq ',status 'PASS))))
          (setq fail (1+ fail))
          (princ (format "FAIL %s %S\n" name (cdr result)))))))
    (princ (format "=== %d passed, %d failed, %d total ===\n"
                   pass fail (+ pass fail)))))
