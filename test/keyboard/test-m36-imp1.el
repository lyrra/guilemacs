;;; test-m36-imp1.el --- M36 imp-1 (retire two stubs) suite.
;;;
;;; Pins the M36 imp-1 retirements (brief.org): swallow_events and
;;; timer_check lose their definition, their extern, and their live
;;; buildable C caller.  Their decision logic moves into (emacs
;;; process-wait); the C keeps the loop control and the static dispatch.
;;; timer_check had no live buildable caller at HEAD: its only in-tree
;;; call was in the dead "#else /* not subprocesses */" MS-DOS copy,
;;; which imp-1 deletes.  Its one remaining caller is NS-only
;;; (src/nsmenu.m), which does not count (HAVE_NS is undefined).
;;;
;;; Wraps test/keyboard/test-m36-imp1.scm -- the Scheme audit corpus.
;;; The corpus pins each definition, each live buildable C caller, the
;;; new module procedures, the dead-copy deletion, and the surface
;;; anchors.
;;;
;;; Binds the repo root as %m36-root, loads the Scheme file via
;;; eval-scheme, then reads back `test-results' (list of (NAME STATUS)
;;; pairs).  Each (NAME PASS|FAIL) pair is reported via princ AND turned
;;; into an ERT test so the harness counts it.  Each (NAME INFO VALUE)
;;; pair is printed as an INFO line and is NOT asserted.  A corpus load
;;; error, a readback error or an empty corpus is reported as a real
;;; FAIL (never a silent 0 failed).

(princ "=== m36 imp-1 (retire two stubs) test suite ===\n")

(let* ((dir (file-name-directory (or load-file-name default-directory)))
       (root (expand-file-name "../.." dir))
       (corpus (expand-file-name "test-m36-imp1.scm" dir))
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
            (list (list "m36-imp1/corpus-load"
                        (cons 'FAIL (format "%S" load-error)))))
           (t
            (condition-case e
                (let ((r (eval-scheme "(reverse test-results)")))
                  (if (or (not (listp r)) (null r))
                      (list (list "m36-imp1/corpus-empty"
                                  (cons 'FAIL "corpus produced no results")))
                    r))
              (error
               (list (list "m36-imp1/readback"
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
