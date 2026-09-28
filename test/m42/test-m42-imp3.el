;;; test-m42-imp3.el --- M42 imp-3 (the pty harness, cases 1-2) suite.
;;;
;;; imp-3 runs the real TTY raw-input read path (tty_read_avail_input,
;;; src/keyboard.c, and its Scheme half (emacs gobble)
;;; tty-read-avail-input!) on a pseudo-terminal.  imp-3 changes no C and
;;; no Scheme; it adds this harness and the first two behavior cases
;;; (brief.org sections 4 and 7):
;;;
;;;   case-1/no-input    the pty holds no bytes.  The path returns 0,
;;;                      stores no event, and does not block.
;;;   case-2/short-read  two bytes, far below the 4095 batch cap.  The
;;;                      path returns 2, decodes it, stores exactly two
;;;                      events in order, and does not wait for a full
;;;                      batch.
;;;
;;; The pty driver (test/m42/pty-driver.py) owns the pty pair and the
;;; emacs under test, writes the case bytes to the master, and reads the
;;; child report from a pipe.  The runner (test/m42/pty-runner.el)
;;; starts the driver and parses its report into (NAME STATUS) pairs.
;;;
;;; This wrapper turns each pair into a real ERT test via
;;; `imp-register-check-as-ert-test', so the harness counts it and the
;;; exit code reflects it.  A princ'd line alone is invisible to that
;;; accounting.
;;;
;;; The skip path (brief.org D3): a host that refuses a pty
;;; (/dev/ptmx EACCES, errno 13) or holds no built src/emacs prints one
;;; INFO line per case.  An INFO case is never registered as an ERT
;;; test, so it is neither a PASS nor a FAIL -- it stays visible as a
;;; skip.  This is the case on the imp-3 host (brief.org section 8).

(princ "=== m42 imp-3 (the pty harness, cases 1-2) test suite ===\n")

(require 'imp-ert-report)

;; pty-runner.el sits next to this file; test/m42/ is not on load-path.
(let ((dir (file-name-directory (or load-file-name default-directory))))
  (add-to-list 'load-path dir)
  (require 'pty-runner))

(let* ((results
        (condition-case err
            (m42-imp3-run-driver)
          (error (list (cons "m42-imp3/runner"
                             (cons 'FAIL (format "%S" err)))))))
       (pass 0)
       (fail 0)
       (info 0))
  (if (null results)
      (setq results (list (cons "m42-imp3/report"
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
        ;; Environment gap, not a code regression.  Do not FAIL.
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
;;; run on the imp-3 host too (brief.org section 8).  They pin the two
;;; defects that a real-run review cannot see here: the runner's report
;;; parser, and the driver's child probe and report format.

(defun m42-imp3--driver-source ()
  "Return the text of pty-driver.py next to this file, or nil."
  (let ((path (expand-file-name "pty-driver.py" (m42-imp3--dir))))
    (and (file-readable-p path)
         (with-temp-buffer
           (insert-file-contents path)
           (buffer-string)))))

(ert-deftest m42-imp3/parse-pass ()
  (should (equal (m42-imp3--parse-line "PASS m42-imp3/case-1-no-input")
                 '("m42-imp3/case-1-no-input" . PASS))))

(ert-deftest m42-imp3/parse-info ()
  (should (equal (m42-imp3--parse-line
                  "INFO m42-imp3/case-2 skipped (no pty: errno 13 Permission denied)")
                 '("m42-imp3/case-2" INFO
                   "skipped (no pty: errno 13 Permission denied)"))))

(ert-deftest m42-imp3/parse-fail ()
  (should (equal (m42-imp3--parse-line "FAIL m42-imp3/case-1 return 0 stored 0")
                 '("m42-imp3/case-1" FAIL . "return 0 stored 0"))))

(ert-deftest m42-imp3/parse-junk-is-nil ()
  (should (null (m42-imp3--parse-line "not a report line"))))

(ert-deftest m42-imp3/parse-many ()
  (should (equal (m42-imp3--parse "PASS a\nINFO b skipped (x)\n")
                 '(("a" . PASS) ("b" INFO "skipped (x)")))))

(ert-deftest m42-imp3/skip-status-is-info-not-pass ()
  ;; The no-pty / no-emacs path must never look like a PASS (brief.org D3).
  (dolist (pair (m42-imp3--skip "no pty"))
    (should (eq (car (cdr pair)) 'INFO))
    (should-not (equal (cdr pair) 'PASS))))

(ert-deftest m42-imp3/runner-returns-both-case-names ()
  ;; The runner always yields one pair per case: the driver's real report,
  ;; or the environment-gap INFO pairs.  Never a stray single FAIL pair.
  (should (equal (mapcar #'car (m42-imp3-run-driver))
                 '("m42-imp3/case-1-no-input" "m42-imp3/case-2-short-read"))))

(ert-deftest m42-imp3/driver-resolves-function-via-module-ref ()
  ;; A bare (tty-read-avail-input! term) is unbound in the eval-scheme
  ;; module, so the probe must take it through module-ref.  (The matching
  ;; negative -- that the generated child source carries no bare call --
  ;; is asserted by the driver's own --selftest, which builds the probe.)
  (should (string-match-p "module-ref mod 'tty-read-avail-input!"
                          (m42-imp3--driver-source))))

(ert-deftest m42-imp3/driver-reports-order-as-string ()
  ;; An empty stored-order list must not print as the opaque
  ;; "#<scheme ()>" object, which the driver regex would reject.
  (should (string-match-p "order-str" (m42-imp3--driver-source))))

(ert-deftest m42-imp3/driver-calls-forced-defelisp-leaves ()
  ;; %terminal-list and %--kbd-buffer-nr-stored are defelisp promises
  ;; that force to procedures; the probe must call them (double parens)
  ;; or it reads a procedure instead of the terminal list / count.
  (let ((src (m42-imp3--driver-source)))
    (should (string-match-p "((force (module-ref mod '%terminal-list)))" src))
    (should (string-match-p "((force nr))" src))))

(ert-deftest m42-imp3/driver-selftest ()
  (let ((python (executable-find "python3")))
    (when python
      (should (zerop (call-process
                      python nil nil nil
                      (expand-file-name "pty-driver.py" (m42-imp3--dir))
                      "--selftest"))))))
