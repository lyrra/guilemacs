;;; test-m42-imp4.el --- M42 imp-4 (pty cases 3-6) suite.
;;;
;;; imp-4 extends the imp-3 pty harness (test/pty-driver.py and
;;; test/m42/pty-runner.el) with four behaviour cases (brief.org):
;;;
;;;   case-3/meta-key-*      the meta decode, one sub-case per
;;;                          %--tty-meta-key value (1 strips and sets the
;;;                          meta modifier, 2 does neither, 0 strips only).
;;;   case-4/quit-byte       the quit-char batch break: bytes after the
;;;                          quit byte in the same batch are dropped, but
;;;                          the path still returns the read count.  The
;;;                          driver clears ISIG on the pty first, so the
;;;                          kernel delivers the raw quit byte; the child
;;;                          binds `inhibit-quit' so the stored C-g cannot
;;;                          abort the report (brief.org).
;;;   case-4/meta-quit-guard the strip/compute order: a meta quit byte
;;;                          (0x87) breaks the batch as code 7 mods meta.
;;;   case-5/terminal-loss   the measured terminal-loss case: the child
;;;                          ignores SIGHUP and the driver closes the pty
;;;                          master, so the slave read fails with EIO and
;;;                          the path returns -2 (brief.org).
;;;                          A host that cannot give EIO reports an
;;;                          environment-gated INFO skip, never PASS/FAIL.
;;;   case-6/continuation    a second call on the same terminal; the child
;;;                          binds `inhibit-quit' as in case 4.
;;;
;;; The pty driver owns the pty pair and the emacs under test; the
;;; runner starts it and parses its report into (NAME STATUS) pairs.
;;; This wrapper turns each pair into a real ERT test via
;;; `imp-register-check-as-ert-test' (PASS/FAIL) or
;;; `imp-register-skip-as-ert-test' (INFO), so the harness counts it and
;;; the exit code reflects it.
;;;
;;; The skip path: a host that refuses a pty
;;; (/dev/ptmx EACCES, errno 13) or holds no built src/emacs prints one
;;; INFO line per case.  Each INFO case becomes a real ERT test whose
;;; body calls `ert-skip', so ERT reports a controlled skip -- neither a
;;; PASS nor a FAIL -- and tool/run-tests.scm keeps pass + skipped = tot.
;;; This is the case on this host (brief.org).

(princ "=== m42 imp-4 (pty cases 3-6) test suite ===\n")

(require 'imp-ert-report)

;; pty-runner.el sits next to this file; test/m42/ is not on load-path.
(let ((dir (file-name-directory (or load-file-name default-directory))))
  (add-to-list 'load-path dir)
  (require 'pty-runner))

(let* ((results
        (condition-case err
            (m42-imp4-run-driver)
          (error (list (cons "m42-imp4/runner"
                             (cons 'FAIL (format "%S" err)))))))
       (pass 0)
       (fail 0)
       (info 0))
  (if (null results)
      (setq results (list (cons "m42-imp4/report"
                                (cons 'FAIL "runner produced no report")))))
  (dolist (result results)
    (let* ((name (car result))
           (status (cdr result))
           (ok (eq status 'PASS)))
      (cond
       (ok
        (imp-register-check-as-ert-test name status)
        (setq pass (1+ pass))
        (princ (format "PASS %s\n" name)))
       ((and (consp status) (eq (car status) 'INFO))
        ;; Environment gap, not a code regression.  Register it as a
        ;; real ERT test that reports a controlled skip, so
        ;; tool/run-tests.scm sees "skipped N/M name" and keeps
        ;; pass + skipped = tot.  The princ'd INFO line stays for the log.
        (imp-register-skip-as-ert-test name (cadr status))
        (setq info (1+ info))
        (princ (format "INFO %s %s\n" name (cadr status))))
       (t
        (imp-register-check-as-ert-test name status)
        (setq fail (1+ fail))
        (princ (format "FAIL %s %S\n" name (cdr result)))))))

  (princ (format "=== %d passed, %d failed, %d skipped, %d total ===\n"
                 pass fail info (+ pass fail info))))

;;; --------------------------------------------------------------------
;;; Harness self-checks.  These need no pty and no child process, so they
;;; run on this host too (brief.org).  They pin the new
;;; report shapes -- the code:mods order string, the two-call shape and
;;; the -2 return -- and the runner's skip path.

(ert-deftest m42-imp4/parse-pass ()
  (should (equal (m42-imp3--parse-line "PASS m42-imp4/case-3-meta-key-1")
                 '("m42-imp4/case-3-meta-key-1" . PASS))))

(ert-deftest m42-imp4/parse-info ()
  (should (equal (m42-imp3--parse-line
                  "INFO m42-imp4/case-5-terminal-loss skipped (no pty: errno 13)")
                 '("m42-imp4/case-5-terminal-loss" INFO
                   "skipped (no pty: errno 13)"))))

(ert-deftest m42-imp4/parse-fail ()
  (should (equal (m42-imp3--parse-line "FAIL m42-imp4/case-4-quit-byte measured 5")
                 '("m42-imp4/case-4-quit-byte" FAIL . "measured 5"))))

(ert-deftest m42-imp4/runner-returns-all-case-names ()
  ;; The runner always yields one pair per imp-4 case: the driver's real
  ;; report, or the environment-gap INFO pairs.  Never a stray FAIL pair
  ;; and never an imp-3 name (the --group selector keeps the groups apart).
  (should (equal (mapcar #'car (m42-imp4-run-driver))
                 '("m42-imp4/case-3-meta-key-1"
                   "m42-imp4/case-3-meta-key-2"
                   "m42-imp4/case-3-meta-key-0"
                   "m42-imp4/case-4-quit-byte"
                   "m42-imp4/case-4-meta-quit-guard"
                   "m42-imp4/case-5-terminal-loss"
                   "m42-imp4/case-6-continuation"))))

(ert-deftest m42-imp4/runner-imp3-group-unchanged ()
  ;; The imp-3 selector must keep returning exactly the two imp-3 names,
  ;; so adding the imp-4 group does not disturb the imp-3 self-check.
  (should (equal (mapcar #'car (m42-imp3-run-driver))
                 '("m42-imp3/case-1-no-input" "m42-imp3/case-2-short-read"))))

(ert-deftest m42-imp4/driver-selftest ()
  ;; --selftest exercises the parser (single-call, code:mods, two-call and
  ;; the -2 terminal-loss return) and the child-source builder.
  (let ((python (executable-find "python3")))
    (when python
      (should (zerop (call-process
                      python nil nil nil (m42-pty--driver)
                      "--selftest"))))))

(ert-deftest m42-imp4/skip-probe-leaves-no-stray-test ()
  ;; A self-check must be able to build an INFO skip test without
  ;; injecting a stray test into the global ERT table.
  (let* ((name "m42-imp4/skip-probe")
         (reason "probe: no pty")
         (sym (intern name))
         (test (imp-skip-ert-test name reason))
         (result (ert-run-test test)))
    (should-not (ert-test-boundp sym))
    (should (ert-test-skipped-p result))
    (should-not (ert-test-passed-p result))
    (should (string-match-p (regexp-quote reason)
                            (ert-reason-for-test-result result)))))

(provide 'test-m42-imp4)
;;; test-m42-imp4.el ends here
