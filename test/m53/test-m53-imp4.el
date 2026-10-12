;;; test-m53-imp4.el --- M53 imp-4 close-out corpus (re-measure and record).
;;;
;;; M53 imp-4 is the close-out (brief.org section 1).  It moves no C
;;; and no Scheme: the net C delta is 0 and the net Scheme delta is 0.
;;; It re-measures the surface, runs the gates, and records the result.
;;; This corpus pins the end state against the TRACKED tree, so a stale
;;; number or a missing registration fails the run.
;;;
;;; It pins three groups, S1 .. S3:
;;;
;;;   S1 -- the re-measured surface of brief.org section 3, measured at
;;;         the imp-4 base HEAD be857de94: src/term.c (6,078 lines, 29
;;;         ^DEFUN (, 4 --tty-* leaf DEFUNs, 33 scm_c_public_ref
;;;         sites); mod/emacs/tty-output.scm (343 lines); and the
;;;         tree-wide scm_c_public_ref count over src/*.[chm] (257).
;;;         S1 holds 6 checks.
;;;   S2 -- the registration: the corpus is registered in the (m53)
;;;         group of tool/run-tests.scm after test-m53-imp3.el, and
;;;         test/pty-driver.py still holds the 21-case total pin.  Read
;;;         tracked runner files only.  S2 holds 4 checks.
;;;   S3 -- the guards: a per-group min-count guard for S1 and one for
;;;         S2, and the group-total check.  The total check is an
;;;         `ert-deftest', so its body runs after every corpus of the
;;;         group has loaded and sees them all, whatever order
;;;         tool/run-tests.scm picked.
;;;
;;; This corpus reads TRACKED files only (src/, mod/, tool/run-tests.scm,
;;; test/pty-driver.py).  It does NOT read docs/
;;; (docs/kb.org test-must-not-read-docs): a gitignored or untracked
;;; record can only pass or skip, so a record check proves nothing.  It
;;; does NOT run a nested m53 gate subprocess.  The in-process
;;; `ert-deftest' replaces a nested gate.
;;;
;;; A read error is a real error, never a silent pass.  An absent src/
;;; file is a real FAIL, not a pass.  Every check registers a real ERT
;;; test via imp-register-bool-as-ert-test, so the harness parses the
;;; ERT output and the exit code is correct: a princ'd FAIL with no ERT
;;; test would leave the exit code 0.

(princ "=== m53 imp-4 close-out suite ===\n")

(require 'imp-ert-report)

(defvar m53-imp4--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))
(defvar m53-imp4--registered 0
  "Total number of checks this corpus has registered.")
(defvar m53-imp4--group nil
  "The group that `m53-imp4--check' counts into: `s1' .. `s3', or nil.")
(defvar m53-imp4--counts nil
  "Alist of (GROUP . COUNT) for the registered checks.")

(defun m53-imp4--group-count (group)
  "Number of checks registered so far in GROUP."
  (or (cdr (assq group m53-imp4--counts)) 0))

(defun m53-imp4--bump-group ()
  "Count one check into `m53-imp4--group'."
  (when m53-imp4--group
    (let ((cell (assq m53-imp4--group m53-imp4--counts)))
      (if cell
          (setcdr cell (1+ (cdr cell)))
        (push (cons m53-imp4--group 1) m53-imp4--counts)))))

(defun m53-imp4--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
the symbol `m53-imp4-absent' when REL does not exist."
  (let ((path (expand-file-name rel m53-imp4--root)))
    (if (not (file-exists-p path))
        'm53-imp4-absent
      (with-temp-buffer
        (insert-file-contents path)
        (funcall fn)))))

(defun m53-imp4--contains-p (rel needle)
  "Non-nil when the TRACKED file REL (repo-root-relative) contains
NEEDLE.  An absent file folds to nil, so `m53-imp4--check' prints FAIL:
an absent src/ file is a real error, not a pass (brief.org section 5)."
  (let ((hit (m53-imp4--with rel
               (lambda ()
                 (goto-char (point-min))
                 (search-forward needle nil t)))))
    (and (not (eq hit 'm53-imp4-absent)) (and hit t))))

(defun m53-imp4--line-of (rel needle)
  "1-based line number of the first literal NEEDLE in REL, or nil.
An absent file folds to nil."
  (m53-imp4--with rel
    (lambda ()
      (goto-char (point-min))
      (when (search-forward needle nil t)
        (line-number-at-pos (match-beginning 0))))))

(defun m53-imp4--lines (rel)
  "Count the newlines of REL the way `wc -l' does."
  (m53-imp4--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (search-forward "\n" nil t) (setq n (1+ n)))
        n))))

(defun m53-imp4--count (rel regexp)
  "Count the matches of REGEXP in REL."
  (m53-imp4--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (re-search-forward regexp nil t) (setq n (1+ n)))
        n))))

(defun m53-imp4--count-defun-leaf (rel)
  "Count the matches of `^DEFUN (\"--tty-' in REL.  Do NOT pin the leaves
with `grep -c -- '--tty-'': that count is higher, because each leaf name
also occurs in a sibling docstring (brief.org section 3 / section 5)."
  (m53-imp4--count rel "^DEFUN (\"--tty-"))

(defun m53-imp4--count-scm-ref ()
  "Count scm_c_public_ref over the TOP src/ directory, one file at a
time, over src/*.[chm] (the brief.org section 3 tree-wide measure).  Do
NOT use a recursive `grep -r src/': that also counts the .scm, .go, and
sub-directory files (brief.org section 3)."
  (let ((total 0)
        (dir (expand-file-name "src" m53-imp4--root)))
    (dolist (f (directory-files dir t "\\.[chm]\\'"))
      (setq total (+ total (or (m53-imp4--count f "scm_c_public_ref") 0))))
    total))

(defun m53-imp4--check (name ok)
  "Report and register one check on a TRACKED file.  OK is a boolean.
The count callers pass `(eql N value)': when the source file is absent
the reader returns the symbol `m53-imp4-absent', so `eql' yields nil and
this prints FAIL.  When OK is the symbol `m53-imp4-absent' itself the
file is absent, and this prints FAIL too.  Either way this registers a
real FAILING ERT test, so an absent src/ file is a real error, not a
pass: the harness parses ERT's batch output for its exit code, so a
princ'd FAIL with no ERT test would leave the exit code 0."
  (let* ((absent (eq ok 'm53-imp4-absent))
         (pass (and (not absent) (and ok t))))
    (if absent
        (princ (format "FAIL m53/imp4/%s (source file absent)\n" name))
      (princ (format "%s m53/imp4/%s\n" (if pass "PASS" "FAIL") name)))
    (setq m53-imp4--registered (1+ m53-imp4--registered))
    (m53-imp4--bump-group)
    (imp-register-bool-as-ert-test (format "m53-imp4/%s" name) pass)))

(defun m53-imp4--info-skip (name reason)
  "Register one explicit INFO skip, counted into the current group.  A
host limit is a skip, never a pass (brief.org section 8)."
  (princ (format "INFO m53/imp4/%s %s\n" name reason))
  (setq m53-imp4--registered (1+ m53-imp4--registered))
  (m53-imp4--bump-group)
  (imp-register-skip-as-ert-test (format "m53-imp4/%s" name) reason))

;;; --- S1. The re-measured surface (brief.org section 3) --------------

;; One check per brief.org section 3 value row, re-measured at the imp-4
;; base HEAD be857de94.  An absent src/ file fails: the count reader
;; returns `m53-imp4-absent' and `eql' yields nil (brief.org section 5).

(setq m53-imp4--group 's1)

;; Row 1: src/term.c lines = 6,078.
(m53-imp4--check "term.c-lines-6078"
                 (eql 6078 (m53-imp4--lines "src/term.c")))
;; Row 2: src/term.c ^DEFUN ( count = 29.
(m53-imp4--check "term.c-defun-count-29"
                 (eql 29 (m53-imp4--count "src/term.c" "^DEFUN (")))
;; Row 3: the 4 --tty-* leaf DEFUNs.  Count the DEFUN forms, not the
;; bare leaf tokens (each name also occurs in a sibling docstring).
(m53-imp4--check "term.c-leaf-defun-count-4"
                 (eql 4 (m53-imp4--count-defun-leaf "src/term.c")))
;; Row 4: src/term.c scm_c_public_ref sites = 33.
(m53-imp4--check "term.c-scm-ref-33"
                 (eql 33 (m53-imp4--count "src/term.c" "scm_c_public_ref")))
;; Row 5: mod/emacs/tty-output.scm lines = 343.
(m53-imp4--check "tty-output.scm-lines-343"
                 (eql 343 (m53-imp4--lines "mod/emacs/tty-output.scm")))
;; Row 6: the tree-wide scm_c_public_ref count over src/*.[chm] = 257.
(m53-imp4--check "tree-wide-scm-ref-257"
                 (eql 257 (m53-imp4--count-scm-ref)))

;;; --- S2. The registration (brief.org section 5) ---------------------

;; test/pty-driver.py and tool/run-tests.scm are tracked files.

(setq m53-imp4--group 's2)

(m53-imp4--check "run-tests-m53-imp4"
                 (m53-imp4--contains-p "tool/run-tests.scm"
                                       "test/m53/test-m53-imp4.el"))
(m53-imp4--check "run-tests-m53-imp4-after-imp3"
                 (let ((imp3 (m53-imp4--line-of "tool/run-tests.scm"
                                                "test/m53/test-m53-imp3.el"))
                       (imp4 (m53-imp4--line-of "tool/run-tests.scm"
                                                "test/m53/test-m53-imp4.el")))
                   (and (integerp imp3) (integerp imp4) (< imp3 imp4))))
(m53-imp4--check "run-tests-m53-group"
                 (m53-imp4--contains-p "tool/run-tests.scm" "(group (m53)"))
(m53-imp4--check "pty-driver-total-21"
                 (m53-imp4--contains-p
                  "test/pty-driver.py"
                  "\"total-case-count\", len(CASES), 21"))

;;; --- S3. The guards -------------------------------------------------

;; An --filter that matches no group already reports exit 0 with 0
;; tests, so a green m53 gate proves nothing until the corpus exists and
;; its checks really register.  These guards fail when the corpus body
;; is truncated or its core checks do not run.  The counts are stable
;; because every check is registered at load time.  S1 holds 6 checks;
;; S2 holds 4 checks.

(setq m53-imp4--group 's3)

(m53-imp4--check "reg/min-s1-checks-6" (>= (m53-imp4--group-count 's1) 6))
(m53-imp4--check "reg/min-s2-checks-4" (>= (m53-imp4--group-count 's2) 4))

;;; --- The group-total check ------------------------------------------

;; Select ONLY the m53-imp4 tests (the pattern is "^m53-imp4", not
;; "^m53-imp"): the whole (m53) group runs in one emacs process.  The
;; floor is measured from a real run: 12 registered checks (S1 6, S2 4,
;; S3 2) plus the group-total deftest itself.  No check can fold to a
;; controlled skip -- this corpus needs no guile and no pty -- so the
;; floor is exact.

(defvar m53-imp4--min-gate-total 13
  "The minimum number of m53-imp4 ERT tests: 12 registered checks (S1 6,
S2 4, S3 2) plus the group-total deftest.")

(ert-deftest m53-imp4/gate-m53-total ()
  "The m53-imp4 corpus registers at least its docs-independent floor."
  (should (>= (length (ert-select-tests "^m53-imp4" t))
              m53-imp4--min-gate-total)))

(princ (format "=== m53 imp-4 close-out suite done (%d tracked checks; s1 %d, s2 %d, s3 %d) ===\n"
               m53-imp4--registered
               (m53-imp4--group-count 's1)
               (m53-imp4--group-count 's2)
               (m53-imp4--group-count 's3)))
