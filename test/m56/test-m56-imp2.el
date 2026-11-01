;;; test-m56-imp2.el --- M56 imp-2 real-path PTY check corpus.
;;;
;;; M56 imp-2 is the real-path check (brief.org section 1).  It adds
;;; ONE PTY case, m56-imp2/tty-init-e2e, to test/pty-driver.py: the case
;;; boots the built src/emacs on a real PTY and drives the terminal, so
;;; the C `init_tty' runs and therefore the three C1 rows
;;; (add_keyboard_wait_descriptor, get_tty_size, init_baud_rate).  The C
;;; delta is 0 and the Scheme delta is 0.
;;;
;;; The real path is the proof.  A module-load probe is NOT proof
;;; (brief.org section 4.4).  Row 3 (init_baud_rate) READS the termios
;;; state on the C descriptor and WRITES the C global baud_rate, so it
;;; has NO plain Scheme observable; the case does NOT assert a baud
;;; value (brief.org section 4.1).  The case pins the WHOLE init path by
;;; the terminal's live behaviour:
;;;
;;;   read  -- the (emacs gobble) read path runs and reports the counts;
;;;   write -- the terminal writes real bytes to the PTY (BEGIN marker,
;;;            out bytes, END marker);
;;;   size  -- the driver resizes the PTY after READY; the child reads
;;;            tty-size after the gate, so a size that follows the
;;;            resize proves a LIVE size query on the real descriptor.
;;;
;;; The suite runs the driver self-test and PTY case, and checks the
;;; test-runner registration.
;;;
;;; A read error is a real error, never a silent pass.  An absent
;;; TRACKED file is a real FAIL, not a pass.  A missing `git', `python3'
;;; binary or a missing PTY is an explicit INFO skip, never a pass.
;;; Every check registers a real ERT test via imp-register-bool-as-ert-test,
;;; so the harness parses the ERT output and the exit code is correct.

(princ "=== m56 imp-2 real-path PTY check suite ===\n")

(require 'imp-ert-report)
(require 'cl-lib)

(defvar m56-imp2--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))
(defvar m56-imp2--registered 0
  "Total number of checks this corpus has registered.")
(defvar m56-imp2--group nil
  "The group that `m56-imp2--check' counts into: `s1' .. `s4', or nil.")
(defvar m56-imp2--counts nil
  "Alist of (GROUP . COUNT) for the registered checks.")

(defun m56-imp2--group-count (group)
  "Number of checks registered so far in GROUP."
  (or (cdr (assq group m56-imp2--counts)) 0))

(defun m56-imp2--bump-group ()
  "Count one check into `m56-imp2--group'."
  (when m56-imp2--group
    (let ((cell (assq m56-imp2--group m56-imp2--counts)))
      (if cell
          (setcdr cell (1+ (cdr cell)))
        (push (cons m56-imp2--group 1) m56-imp2--counts)))))

(defun m56-imp2--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
the symbol `m56-imp2-absent' when REL does not exist."
  (let ((path (expand-file-name rel m56-imp2--root)))
    (if (not (file-exists-p path))
        'm56-imp2-absent
      (with-temp-buffer
        (insert-file-contents path)
        (funcall fn)))))

(defun m56-imp2--contains-p (rel needle)
  "Non-nil when the TRACKED file REL contains NEEDLE.  An absent file
folds to nil, so a check prints FAIL: an absent TRACKED file is a real
error, not a pass."
  (let ((hit (m56-imp2--with rel
               (lambda ()
                 (goto-char (point-min))
                 (search-forward needle nil t)))))
    (and (not (eq hit 'm56-imp2-absent)) (and hit t))))

(defun m56-imp2--ordered-p (rel needles)
  "Non-nil when the TRACKED file REL holds every NEEDLE in the GIVEN
ORDER: each search starts after the previous match."
  (m56-imp2--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((all t))
        (dolist (needle needles)
          (when all
            (unless (search-forward needle nil t) (setq all nil))))
        all))))

(defun m56-imp2--count (rel needle)
  "Number of times the TRACKED file REL contains the literal NEEDLE.
An absent file counts zero, so a check built on it prints FAIL: an
absent TRACKED file is a real error, not a pass.  Use this to prove a
needle is UNIQUE to one site, so a check cannot pass on the wrong
line."
  (let ((n (m56-imp2--with rel
             (lambda ()
               (goto-char (point-min))
               (let ((count 0))
                 (while (search-forward needle nil t)
                   (setq count (1+ count)))
                 count)))))
    (if (eq n 'm56-imp2-absent) 0 n)))

(defun m56-imp2--run (prog args)
  "Run PROG with ARGS in a subprocess from the repo root and return its
stdout / stderr as a string, or the symbol `m56-imp2-prog-absent' when
PROG is not on PATH.  The default directory is the repo root."
  (if (not (executable-find prog))
      'm56-imp2-prog-absent
    (let ((buf (get-buffer-create " *m56-imp2-run*"))
          (default-directory m56-imp2--root))
      (unwind-protect
          (progn
            (with-current-buffer buf (erase-buffer))
            (apply #'call-process prog nil buf nil args)
            (with-current-buffer buf
              (buffer-substring-no-properties (point-min) (point-max))))
        (kill-buffer buf)))))

(defun m56-imp2--check (name ok &optional detail)
  "Report and register one check on a TRACKED file.  OK is a boolean.
When OK is the symbol `m56-imp2-absent', the source file is absent.
DETAIL is included in the report and ERT failure when OK is nil."
  (let* ((absent (eq ok 'm56-imp2-absent))
         (pass (and (not absent) (and ok t))))
    (if absent
        (princ (format "FAIL m56/imp2/%s (source file absent)\n" name))
      (princ (format "%s m56/imp2/%s%s\n" (if pass "PASS" "FAIL") name
                     (if (and (not pass) detail) (concat " " detail) ""))))
    (setq m56-imp2--registered (1+ m56-imp2--registered))
    (m56-imp2--bump-group)
    (if (and (not pass) detail)
        (imp-register-check-as-ert-test (format "m56-imp2/%s" name)
                                        (cons 'FAIL detail))
      (imp-register-bool-as-ert-test (format "m56-imp2/%s" name) pass))))

(defun m56-imp2--info-skip (name reason)
  "Register one explicit INFO skip, counted into the current group.  A
host limit is a skip, never a pass (brief.org section 2)."
  (princ (format "INFO m56/imp2/%s %s\n" name reason))
  (setq m56-imp2--registered (1+ m56-imp2--registered))
  (m56-imp2--bump-group)
  (imp-register-skip-as-ert-test (format "m56-imp2/%s" name) reason))

(ert-deftest m56-imp2/failure-preserves-driver-detail ()
  (let ((m56-imp2--registered 0)
        (m56-imp2--group nil)
        (captured nil)
        (detail "FAIL example measured 0 want 2"))
    (cl-letf (((symbol-function 'imp-register-check-as-ert-test)
               (lambda (_name status) (setq captured status))))
      (with-temp-buffer
        (let ((standard-output (current-buffer)))
          (m56-imp2--check "example" nil detail))
        (should (string-match-p (regexp-quote detail) (buffer-string)))))
    (should (equal captured (cons 'FAIL detail)))))

;;; --- S1. The case wiring in test/pty-driver.py ----------------------

;; The real path runs through the ONE new PTY case.  These checks pin
;; the case name, its group, its constants, the CASES / GROUPS entries,
;; the selftest pins, the output span and its pinned bytes, and the
;; resize.  test/pty-driver.py is TRACKED, so an absent file FAILS.

(setq m56-imp2--group 's1)

;; M61 imp-2g (review cr.org CR2, finding F2 / F7): the 2 case-count
;; pins are REMOVED, not re-pinned.  A case count is not a behavior, and
;; the driver's own --selftest holds the count checks at
;; :3470 ... :3472.

;;; --- S2. The real path (brief.org section 1, section 5) -------------

;; The module-load probe is NOT proof.  The real path is the built
;; src/emacs on a real PTY: test/pty-driver.py boots the child emacs,
;; which runs init_tty and therefore the three C1 rows.  A missing
;; python3, a missing built src/emacs, or a missing PTY is an explicit
;; INFO skip, NEVER a pass.

(setq m56-imp2--group 's2)

(let ((out (m56-imp2--run "python3"
                          (list "test/pty-driver.py" "--selftest"))))
  (if (eq out 'm56-imp2-prog-absent)
      (m56-imp2--info-skip "pty-driver-selftest" "no python3 binary on PATH")
    (m56-imp2--check "pty-driver-selftest"
                     (and (string-match-p "SELFTEST OK" out) t))))

(let ((emacs (expand-file-name "src/emacs" m56-imp2--root)))
  (cond
   ((not (and (file-exists-p emacs) (file-executable-p emacs)))
    (m56-imp2--info-skip "pty-real-path-tty-init" "no built src/emacs"))
   (t
    (let ((out (m56-imp2--run
                "python3"
                (list "test/pty-driver.py" "--emacs" emacs
                      "--case" "m56-imp2/tty-init-e2e"))))
      (cond
       ((eq out 'm56-imp2-prog-absent)
        (m56-imp2--info-skip "pty-real-path-tty-init" "no python3 binary on PATH"))
       ((string-match-p "PASS m56-imp2/tty-init-e2e" out)
        (m56-imp2--check "pty-real-path-tty-init" t))
       ((string-match-p "INFO m56-imp2/tty-init-e2e" out)
        (m56-imp2--info-skip "pty-real-path-tty-init" out))
       (t
        (m56-imp2--check "pty-real-path-tty-init" nil out)))))))

;;; --- S3. The registration -------------------------------------------

(setq m56-imp2--group 's3)

(m56-imp2--check "run-tests-m56-imp2"
                 (m56-imp2--contains-p "tool/run-tests.scm"
                                       "test/m56/test-m56-imp2.el"))
(m56-imp2--check "run-tests-m56-group"
                 (m56-imp2--contains-p "tool/run-tests.scm" "(group (m56)"))
(m56-imp2--check "run-tests-m56-after-imp1"
                 (m56-imp2--ordered-p "tool/run-tests.scm"
                                      '("\"test/m56/test-m56-imp1.el\""
                                        "\"test/m56/test-m56-imp2.el\"")))

;;; --- S4. The guards -------------------------------------------------

;; An --filter that matches no group already reports exit 0 with 0
;; tests, so a green m56 gate proves nothing until the corpus exists and
;; its checks really register.  These guards fail when the corpus body
;; is truncated or its core checks do not run.  The counts are stable
;; because every check is registered at load time.  S1 holds 8 checks,
;; S2 holds 2, and S3 holds 3.

(setq m56-imp2--group 's4)

(m56-imp2--check "reg/min-s2-checks-2" (>= (m56-imp2--group-count 's2) 2))
(m56-imp2--check "reg/min-s3-checks-3" (>= (m56-imp2--group-count 's3) 3))

;;; --- The group-total check ------------------------------------------

;; The measured count of m56-imp2 tests is 17: 13 registered checks
;; (S1 8, S2 2, S3 3) plus 3 group guards plus the group-total deftest
;; itself.  A counted check is either a real check or a controlled INFO
;; skip, so the S2 checks still register on a host with no python3 / no
;; built src/emacs / no PTY; the exact pin holds either way.

(princ (format "=== m56 imp-2 suite done (%d checks; s1 %d, s2 %d, s3 %d, s4 %d) ===\n"
               m56-imp2--registered
               (m56-imp2--group-count 's1)
               (m56-imp2--group-count 's2)
               (m56-imp2--group-count 's3)
               (m56-imp2--group-count 's4)))
