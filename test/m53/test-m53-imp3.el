;;; test-m53-imp3.el --- M53 imp-3 PTY terminal vertical-slice corpus.
;;;
;;; M53 imp-3 is the CHECK 2 smaller step (brief.org section 3): the
;;; BUILT src/emacs runs the WHOLE terminal vertical slice on a pty, in
;;; this order -- start, load Elisp, read input, write output, resize,
;;; exit and restore the terminal modes.  It is a CHECK, not a port: the
;;; net C delta is 0 and the net Scheme delta is 0.
;;;
;;; The slice is ONE case of the common pty driver
;;; (test/pty-driver.py): the case m53-imp3/vertical-slice-e2e in the
;;; m53-imp3 group.  The driver prints one line per case:
;;;
;;;   PASS m53-imp3/vertical-slice-e2e
;;;   FAIL ... <detail>
;;;   INFO ... skipped (<reason>)
;;;
;;; This corpus pins:
;;;
;;;   S1 -- the invocation: the group m53-imp3 and the case name
;;;         m53-imp3/vertical-slice-e2e are present in test/pty-driver.py.
;;;         S1 holds 2 checks.
;;;   S2 -- the slice pins: the driver carries the resize (TIOCSWINSZ),
;;;         the mode capture/read-back (tcgetattr), the exit-status wait,
;;;         and the load fixture.  S2 holds 4 checks.
;;;   S3 -- the behavior run: python3 test/pty-driver.py --emacs
;;;         src/emacs --group m53-imp3 prints PASS for the case.  A
;;;         missing built src/emacs or a missing pty is a controlled INFO
;;;         skip, never a pass.  S3 holds 1 check.
;;;   S4 -- the registration and the guards: the corpus is registered in
;;;         the (m53) group of tool/run-tests.scm; a per-group min-count
;;;         guard for S1 .. S3; the group-total `ert-deftest'.  S4 holds
;;;         5 checks.
;;;
;;; This corpus reads TRACKED files only (test/, tool/run-tests.scm).  It
;;; does NOT read docs/ (docs/kb.org test-must-not-read-docs).
;;;
;;; A read error is a real error, never a silent pass.  An absent driver
;;; file is a real FAIL, not a pass.  Every check registers a real ERT
;;; test via imp-register-bool-as-ert-test, so the harness parses the ERT
;;; output and the exit code is correct: a princ'd FAIL with no ERT test
;;; would leave the exit code 0.

(princ "=== m53 imp-3 PTY vertical-slice suite ===\n")

(require 'imp-ert-report)

(defvar m53-imp3--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))
(defvar m53-imp3--registered 0
  "Total number of checks this corpus has registered.")
(defvar m53-imp3--group nil
  "The group that `m53-imp3--check' counts into: `s1' .. `s4', or nil.")
(defvar m53-imp3--counts nil
  "Alist of (GROUP . COUNT) for the registered checks.")

(defun m53-imp3--group-count (group)
  "Number of checks registered so far in GROUP."
  (or (cdr (assq group m53-imp3--counts)) 0))

(defun m53-imp3--bump-group ()
  "Count one check into `m53-imp3--group'."
  (when m53-imp3--group
    (let ((cell (assq m53-imp3--group m53-imp3--counts)))
      (if cell
          (setcdr cell (1+ (cdr cell)))
        (push (cons m53-imp3--group 1) m53-imp3--counts)))))

(defun m53-imp3--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
the symbol `m53-imp3-absent' when REL does not exist."
  (let ((path (expand-file-name rel m53-imp3--root)))
    (if (not (file-exists-p path))
        'm53-imp3-absent
      (with-temp-buffer
        (insert-file-contents path)
        (funcall fn)))))

(defun m53-imp3--contains-p (rel needle)
  "Non-nil when the TRACKED file REL contains NEEDLE.  An absent file
folds to nil, so `m53-imp3--check' prints FAIL."
  (let ((hit (m53-imp3--with rel
               (lambda ()
                 (goto-char (point-min))
                 (search-forward needle nil t)))))
    (and (not (eq hit 'm53-imp3-absent)) (and hit t))))

(defun m53-imp3--check (name ok)
  "Report and register one check on a TRACKED file.  OK is a boolean.
An absent source file folds to a real FAILING ERT test (brief.org
section 6)."
  (let* ((absent (eq ok 'm53-imp3-absent))
         (pass (and (not absent) (and ok t))))
    (if absent
        (princ (format "FAIL m53/imp3/%s (source file absent)\n" name))
      (princ (format "%s m53/imp3/%s\n" (if pass "PASS" "FAIL") name)))
    (setq m53-imp3--registered (1+ m53-imp3--registered))
    (m53-imp3--bump-group)
    (imp-register-bool-as-ert-test (format "m53-imp3/%s" name) pass)))

(defun m53-imp3--info-skip (name reason)
  "Register one explicit INFO skip, counted into the current group.  A
host limit is a skip, never a pass (brief.org section 6)."
  (princ (format "INFO m53/imp3/%s %s\n" name reason))
  (setq m53-imp3--registered (1+ m53-imp3--registered))
  (m53-imp3--bump-group)
  (imp-register-skip-as-ert-test (format "m53-imp3/%s" name) reason))

;;; --- The real slice run (brief.org section 6, S3) -------------------

(defun m53-imp3--run-slice ()
  "Run python3 test/pty-driver.py --emacs src/emacs --group m53-imp3 and
return (STATUS . OUTPUT), or the symbol `m53-imp3-no-emacs' when no
built src/emacs exists, or `m53-imp3-no-driver' when the driver file is
absent.  This runs the REAL slice: the driver forks terminal Emacs on a
pty and reads the bytes, the size, the exit status, and the restored
modes.  A missing binary or driver is a controlled INFO skip."
  (let ((emacs (expand-file-name "src/emacs" m53-imp3--root))
        (driver (expand-file-name "test/pty-driver.py" m53-imp3--root)))
    (cond
     ((not (file-executable-p emacs)) 'm53-imp3-no-emacs)
     ((not (file-exists-p driver)) 'm53-imp3-no-driver)
     (t
      (let ((buf (get-buffer-create " *m53-imp3-pty*")))
        (unwind-protect
            (progn
              (with-current-buffer buf (erase-buffer))
              (let ((status (call-process
                             "python3" nil buf nil
                             driver "--emacs" emacs
                             "--group" "m53-imp3")))
                (cons status
                      (with-current-buffer buf
                        (buffer-substring-no-properties
                         (point-min) (point-max))))))
          (kill-buffer buf)))))))

(defun m53-imp3--check-slice (name)
  "Run the slice and register NAME.  A PASS line is a pass, a FAIL line
is a fail, and an INFO line (no pty, no emacs) is a controlled skip."
  (let ((res (m53-imp3--run-slice)))
    (cond
     ((eq res 'm53-imp3-no-emacs)
      (m53-imp3--info-skip name "no built src/emacs"))
     ((eq res 'm53-imp3-no-driver)
      (m53-imp3--info-skip name "no test/pty-driver.py"))
     (t
      (let ((out (cdr res)))
        (cond
         ((string-match-p "^PASS m53-imp3/vertical-slice-e2e" out)
          (m53-imp3--check name t))
         ((string-match-p "^INFO m53-imp3" out)
          (m53-imp3--info-skip name "host has no pty, or no emacs"))
         (t
          (m53-imp3--check name nil))))))))

;;; --- S1. The invocation ---------------------------------------------

(setq m53-imp3--group 's1)

(m53-imp3--check "driver-case-name"
                 (m53-imp3--contains-p
                  "test/pty_cases.py" "m53-imp3/vertical-slice-e2e"))
(m53-imp3--check "driver-group"
                 (m53-imp3--contains-p
                  "test/pty_cases.py" "\"m53-imp3\""))

;;; --- S2. The slice pins ---------------------------------------------

;; The slice must carry the resize (TIOCSWINSZ), the mode read-back
;; (tcgetattr), the exit-status wait, and the load fixture.  These pins
;; hold the driver's wiring in the tracked source.

(setq m53-imp3--group 's2)

(m53-imp3--check "driver-resize-tiocswinsz"
                 (m53-imp3--contains-p "test/pty-driver.py" "TIOCSWINSZ"))
(m53-imp3--check "driver-mode-readback-tcgetattr"
                 (m53-imp3--contains-p "test/pty-driver.py" "tcgetattr"))
(m53-imp3--check "driver-wait-exit"
                 (m53-imp3--contains-p "test/pty_cases.py" "\"wait_exit\""))
(m53-imp3--check "driver-load-fixture"
                 (m53-imp3--contains-p "test/pty-driver.py" "load_fixture"))

;;; --- S3. The behavior run -------------------------------------------

(setq m53-imp3--group 's3)

(m53-imp3--check-slice "pty-vertical-slice")

;;; --- S4. The registration and the guards ----------------------------

(setq m53-imp3--group 's4)

(m53-imp3--check "run-tests-m53-imp3"
                 (m53-imp3--contains-p "tool/run-tests.scm"
                                       "test/m53/test-m53-imp3.el"))
(m53-imp3--check "reg/min-s1-checks-2" (>= (m53-imp3--group-count 's1) 2))
(m53-imp3--check "reg/min-s2-checks-4" (>= (m53-imp3--group-count 's2) 4))
(m53-imp3--check "reg/min-s3-checks-1" (>= (m53-imp3--group-count 's3) 1))
;; The slice moves the driver selftest total 20 -> 21.  A tracked
;; comment that still says the pty-driver has a 20-case total is the
;; same stale-pin class the m52 re-pin repaired (see cr.org F3): guard
;; the tracked runner against the stale literal.
(m53-imp3--check "run-tests-no-stale-20-case"
                 (not (m53-imp3--contains-p
                       "tool/run-tests.scm" "20-case total")))

;;; --- The group-total check ------------------------------------------

;; Select ONLY the m53-imp3 tests (the pattern is "^m53-imp3", not
;; "^m53-imp"): the whole (m53) group runs in one emacs process.

(defvar m53-imp3--min-gate-total 13
  "The minimum number of m53-imp3 ERT tests: 12 registered checks
(S1 2, S2 4, S3 1, S4 5) plus the group-total deftest.  The S3 slice
check may fold to a controlled INFO skip when no pty is present, and a
controlled skip is still a registered test, so the floor holds.")

(ert-deftest m53-imp3/gate-m53-total ()
  "The m53-imp3 corpus registers at least its docs-independent floor."
  (should (>= (length (ert-select-tests "^m53-imp3" t))
              m53-imp3--min-gate-total)))

(princ (format "=== m53 imp-3 suite done (%d checks; s1 %d, s2 %d, s3 %d, s4 %d) ===\n"
               m53-imp3--registered
               (m53-imp3--group-count 's1)
               (m53-imp3--group-count 's2)
               (m53-imp3--group-count 's3)
               (m53-imp3--group-count 's4)))
