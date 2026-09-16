;;; test-m38-imp3.el --- M38 imp-3 (input-state leak isolation) suite.
;;;
;;; Pins the M38 imp-3 work (brief.org, defect D3): the keyboard corpora
;;; run in one emacs process, so an input-state name one corpus writes
;;; leaks into every corpus that follows.  imp-3 makes each writer clear
;;; its state back to the C/Scheme default, makes the two no-reset
;;; victims measure their own effect, and disposes the doc-anchor
;;; failure.  No C file changes.
;;;
;;; Two parts:
;;;   * Behavior checks (this file).  Run the real harness with
;;;     --filter=keyboard TWICE and assert an exit status of exactly 0 in
;;;     each run (exit criterion 3, brief.org §10).  A recursion guard
;;;     (GUILEMACS_M38_IMP3_GATE) keeps the nested run from spawning
;;;     another pair.
;;;   * Source checks (test/keyboard/test-m38-imp3.scm).  Prove the
;;;     writer map, the shared helper, the Pattern B victims, the
;;;     kbd_buffer drain, the doc-anchor skip, the unchanged victims and
;;;     the unchanged C surface.
;;;
;;; The .scm corpus is loaded via primitive-load with the repo root bound
;;; as %m38-root and the two log paths / exit statuses as
;;; %m38-imp3-run1, %m38-imp3-run2, %m38-imp3-exit1, %m38-imp3-exit2.
;;; Each (NAME PASS|FAIL) pair is reported via princ AND turned into an
;;; ERT test so the harness counts it.  Each (NAME INFO VALUE) pair is
;;; printed as an INFO line and is NOT asserted.  A corpus load error, a
;;; readback error or an empty corpus is reported as a real FAIL (never
;;; a silent 0 failed).

(princ "=== m38 imp-3 (input-state leak isolation) test suite ===\n")

(let* ((dir (file-name-directory (or load-file-name default-directory)))
       (root (expand-file-name "../.." dir))
       (corpus (expand-file-name "test-m38-imp3.scm" dir))
       (logs nil)
       (load-error nil))
  ;; --- Behavior checks: two --filter=keyboard runs must exit EXACTLY 0.
  ;; The nested run loads this same file, so set the recursion guard in
  ;; the child; then the child skips this block and runs only the source
  ;; checks.
  (if (getenv "GUILEMACS_M38_IMP3_GATE")
      (princ "INFO m38/imp3/behavior/skipped nested run (recursion guard)\n")
    (let* ((log1 (make-temp-file "m38-imp3-kb-run1-"))
           (log2 (make-temp-file "m38-imp3-kb-run2-"))
           (cmd (format "cd %S && GUILEMACS_M38_IMP3_GATE=1 ./tool/run-tests.sh --filter=keyboard >%S 2>&1"
                        root "%s"))
           (st1 (condition-case nil
                    (call-process "sh" nil nil nil "-c" (format cmd log1))
                  (error nil)))
           (st2 (condition-case nil
                    (call-process "sh" nil nil nil "-c" (format cmd log2))
                  (error nil))))
      (setq logs (list log1 log2))
      (eval `(ert-deftest m38-imp3/behavior/keyboard-run1-exits-0 ()
               (should (eql ,st1 0))))
      (eval `(ert-deftest m38-imp3/behavior/keyboard-run2-exits-0 ()
               (should (eql ,st2 0))))
      (princ (format "INFO m38/imp3/behavior/keyboard-run1-exit %S\n" st1))
      (princ (format "INFO m38/imp3/behavior/keyboard-run2-exit %S\n" st2))
      ;; The corpus reads these paths and statuses; do not delete the
      ;; logs until after the readback below.
      (eval-scheme (format "(define %%m38-imp3-run1 %S)" log1))
      (eval-scheme (format "(define %%m38-imp3-run2 %S)" log2))
      (eval-scheme (format "(define %%m38-imp3-exit1 %S)" st1))
      (eval-scheme (format "(define %%m38-imp3-exit2 %S)" st2))))

  ;; --- Source checks: the writer map, the helper, the victims.
  (eval-scheme (format "(define %%m38-root %S)" root))
  (condition-case err
      (eval-scheme
       (format "(primitive-load %S)" corpus))
    (error (setq load-error err)))
  (let* ((results
          (cond
           (load-error
            (list (list "m38-imp3/corpus-load"
                        (cons 'FAIL (format "%S" load-error)))))
           (t
            (condition-case e
                (let ((r (eval-scheme "(reverse test-results)")))
                  (if (or (not (listp r)) (null r))
                      (list (list "m38-imp3/corpus-empty"
                                  (cons 'FAIL "corpus produced no results")))
                    r))
              (error
               (list (list "m38-imp3/readback"
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
                   pass fail (+ pass fail)))
    ;; Remove the two temp logs now that the corpus has read them.
    (dolist (log logs)
      (when (and log (file-exists-p log)) (delete-file log)))))
