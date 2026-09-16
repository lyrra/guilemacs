;;; test-m38-imp1.el --- M38 imp-1 (harness count mismatch) suite.
;;;
;;; Pins the M38 imp-1 work (brief.org, defect D1): tool/run-tests.scm
;;; exits non-zero when the ERT count and the emitted pass count
;;; disagree.  The ERROR text is kept.  No C file changes.
;;;
;;; Two parts:
;;;   * Behavior checks (this file).  Run the real harness on the
;;;     registered fixture test/m38/test-m38-imp1-fixture.el with the
;;;     MIDDLE ERT test failing (GUILEMACS_M38_FIXTURE=middle) and again
;;;     with the LAST ERT test failing (GUILEMACS_M38_FIXTURE=last).  ERT
;;;     then prints a "passed 3/3" index with only two passed names -- a
;;;     count mismatch.  The harness must exit exactly 1 and name the
;;;     signal.  The last-fail case pins review finding F1.
;;;   * Source checks (test/keyboard/test-m38-imp1.scm).  Prove the
;;;     mismatch reaches the fail accumulator and the exit status reads it.
;;;
;;; The .scm corpus is loaded via primitive-load with the repo root bound
;;; as %m38-root.  Each (NAME PASS|FAIL) pair is reported via princ AND
;;; turned into an ERT test so the harness counts it.  Each
;;; (NAME INFO VALUE) pair is printed as an INFO line and is NOT asserted.
;;; A corpus load error, a readback error or an empty corpus is reported
;;; as a real FAIL (never a silent 0 failed).

(princ "=== m38 imp-1 (harness count mismatch) test suite ===\n")

(let* ((dir (file-name-directory (or load-file-name default-directory)))
       (root (expand-file-name "../.." dir))
       (corpus (expand-file-name "test-m38-imp1.scm" dir))
       (load-error nil))
  ;; --- Behavior checks: the harness exits EXACTLY 1 on a count mismatch,
  ;; in both the middle-fail and the last-fail position, and names the
  ;; signal.  The fixture is registered in its own group, outside the
  ;; keyboard group, and is normally green.  The nested log is kept in a
  ;; file (not /dev/null), so the check can also assert the signal text.
  (dolist (mode '("middle" "last"))
    (let* ((log (make-temp-file (format "m38-imp1-%s-" mode)))
           (status
            (condition-case nil
                (call-process
                 "sh" nil nil nil "-c"
                 (format "cd %S && GUILEMACS_M38_FIXTURE=%s ./tool/run-tests.sh --filter=m38-imp1-fixture >%S 2>&1"
                         root mode log))
              (error nil)))
           (out (if (file-exists-p log)
                    (with-temp-buffer
                      (insert-file-contents log)
                      (buffer-string))
                  "")))
      (when (file-exists-p log) (delete-file log))
      (eval `(ert-deftest ,(intern (format "m38-imp1/behavior/%s-fail-exits-1" mode)) ()
               (should (eql ,status 1))
               (should (string-match "ERROR:" ,out))
               (should (string-match "ERT count mismatch" ,out))))))

  ;; --- Source checks: the fix shape in the live tool/run-tests.scm.
  ;; The corpus reads the source tree, so tell it where the root is.
  (eval-scheme (format "(define %%m38-root %S)" root))
  (condition-case err
      (eval-scheme
       (format "(primitive-load %S)" corpus))
    (error (setq load-error err)))
  (let* ((results
          (cond
           (load-error
            (list (list "m38-imp1/corpus-load"
                        (cons 'FAIL (format "%S" load-error)))))
           (t
            (condition-case e
                (let ((r (eval-scheme "(reverse test-results)")))
                  (if (or (not (listp r)) (null r))
                      (list (list "m38-imp1/corpus-empty"
                                  (cons 'FAIL "corpus produced no results")))
                    r))
              (error
               (list (list "m38-imp1/readback"
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
