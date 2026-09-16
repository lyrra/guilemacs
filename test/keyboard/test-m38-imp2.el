;;; test-m38-imp2.el --- M38 imp-2 (comment-blind dropped-token scan) suite.
;;;
;;; Pins the M38 imp-2 work (brief.org, defect D2): the m29 dropped-token
;;; scan strips the C comments from src/keyboard.c before the token scan,
;;; so the HAVE_NS doc comment (added by M36 imp-4) is not a hit, and the
;;; match is strict (whole C identifier).  No C file changes.
;;;
;;; Two parts:
;;;   * Behavior checks (this file).  Run the real harness with
;;;     --filter=m29-imp5 and --filter=m29-imp6.  Each must exit exactly 0
;;;     (brief.org gate commands).  This proves exit criterion 4.
;;;   * Source checks (test/keyboard/test-m38-imp2.scm).  Prove the
;;;     stripper rules, the positive/negative controls, the strict match,
;;;     and the clean src/keyboard.c.
;;;
;;; The .scm corpus is loaded via primitive-load with the repo root bound
;;; as %m38-root.  Each (NAME PASS|FAIL) pair is reported via princ AND
;;; turned into an ERT test so the harness counts it.  Each
;;; (NAME INFO VALUE) pair is printed as an INFO line and is NOT asserted.
;;; A corpus load error, a readback error or an empty corpus is reported
;;; as a real FAIL (never a silent 0 failed).

(princ "=== m38 imp-2 (comment-blind dropped-token scan) test suite ===\n")

(let* ((dir (file-name-directory (or load-file-name default-directory)))
       (root (expand-file-name "../.." dir))
       (corpus (expand-file-name "test-m38-imp2.scm" dir))
       (load-error nil))
  ;; --- Behavior checks: the two m29 filters must exit EXACTLY 0.  The
  ;; error message D2 produced is gone, so the harness is green.
  (dolist (filter '("m29-imp5" "m29-imp6"))
    (let* ((log (make-temp-file (format "m38-imp2-%s-" filter)))
           (status
            (condition-case nil
                (call-process
                 "sh" nil nil nil "-c"
                 (format "cd %S && ./tool/run-tests.sh --filter=%s >%S 2>&1"
                         root filter log))
              (error nil))))
      (when (file-exists-p log) (delete-file log))
      (eval `(ert-deftest ,(intern (format "m38-imp2/behavior/%s-exits-0"
                                           filter)) ()
               (should (eql ,status 0))))))

  ;; --- Source checks: the stripper rules and the scan shape.
  ;; The corpus reads the source tree, so tell it where the root is.
  (eval-scheme (format "(define %%m38-root %S)" root))
  (condition-case err
      (eval-scheme
       (format "(primitive-load %S)" corpus))
    (error (setq load-error err)))
  (let* ((results
          (cond
           (load-error
            (list (list "m38-imp2/corpus-load"
                        (cons 'FAIL (format "%S" load-error)))))
           (t
            (condition-case e
                (let ((r (eval-scheme "(reverse test-results)")))
                  (if (or (not (listp r)) (null r))
                      (list (list "m38-imp2/corpus-empty"
                                  (cons 'FAIL "corpus produced no results")))
                    r))
              (error
               (list (list "m38-imp2/readback"
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
