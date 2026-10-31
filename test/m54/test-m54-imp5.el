;;; test-m54-imp5.el --- M54 imp-5 close-out corpus (re-measure and record).
;;;
;;; M54 imp-5 is the close-out (brief.org section 1).  It moves no C and
;;; no Scheme: the net C delta is 0 and the net Scheme delta is 0.  It
;;; re-measures the surface, runs the gates, and records the result.
;;; This corpus pins the end state against the TRACKED tree, so a stale
;;; number or a missing registration fails the run.
;;;
;;; It pins three groups, S1 .. S3:
;;;
;;;   S1 -- the re-measured surface of brief.org section 5, measured at
;;;         the imp-5 base HEAD 2cc354f87: src/term.c (6,214 lines, 29
;;;         ^DEFUN (, 4 --tty-* leaf DEFUNs, 36 scm_c_public_ref
;;;         sites); mod/emacs/tty-output.scm (454 lines); and the
;;;         tree-wide scm_c_public_ref count over src/*.[chm] (260).
;;;         S1 holds 6 checks.
;;;   S2 -- the registration: the corpus is registered in the (m54)
;;;         group of tool/run-tests.scm after test-m54-imp4.el, and
;;;         test/pty-driver.py still holds the 26-case total pin.  Read
;;;         tracked runner files only.  S2 holds 3 checks.
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
;;; does NOT run a nested m54 gate subprocess.  The in-process
;;; `ert-deftest' replaces a nested gate.
;;;
;;; A read error is a real error, never a silent pass.  An absent src/
;;; file is a real FAIL, not a pass.  Every check registers a real ERT
;;; test via imp-register-bool-as-ert-test, so the harness parses the
;;; ERT output and the exit code is correct: a princ'd FAIL with no ERT
;;; test would leave the exit code 0.

(princ "=== m54 imp-5 close-out suite ===\n")

(require 'imp-ert-report)

(defvar m54-imp5--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))
(defvar m54-imp5--registered 0
  "Total number of checks this corpus has registered.")
(defvar m54-imp5--group nil
  "The group that `m54-imp5--check' counts into: `s1' .. `s3', or nil.")
(defvar m54-imp5--counts nil
  "Alist of (GROUP . COUNT) for the registered checks.")

(defun m54-imp5--group-count (group)
  "Number of checks registered so far in GROUP."
  (or (cdr (assq group m54-imp5--counts)) 0))

(defun m54-imp5--bump-group ()
  "Count one check into `m54-imp5--group'."
  (when m54-imp5--group
    (let ((cell (assq m54-imp5--group m54-imp5--counts)))
      (if cell
          (setcdr cell (1+ (cdr cell)))
        (push (cons m54-imp5--group 1) m54-imp5--counts)))))

(defun m54-imp5--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
the symbol `m54-imp5-absent' when REL does not exist."
  (let ((path (expand-file-name rel m54-imp5--root)))
    (if (not (file-exists-p path))
        'm54-imp5-absent
      (with-temp-buffer
        (insert-file-contents path)
        (funcall fn)))))

(defun m54-imp5--contains-p (rel needle)
  "Non-nil when the TRACKED file REL (repo-root-relative) contains
NEEDLE.  An absent file folds to nil, so `m54-imp5--check' prints FAIL:
an absent src/ file is a real error, not a pass (brief.org section 7)."
  (let ((hit (m54-imp5--with rel
               (lambda ()
                 (goto-char (point-min))
                 (search-forward needle nil t)))))
    (and (not (eq hit 'm54-imp5-absent)) (and hit t))))

(defun m54-imp5--line-of (rel needle)
  "1-based line number of the first literal NEEDLE in REL, or nil.
An absent file folds to nil."
  (m54-imp5--with rel
    (lambda ()
      (goto-char (point-min))
      (when (search-forward needle nil t)
        (line-number-at-pos (match-beginning 0))))))

(defun m54-imp5--check (name ok)
  "Report and register one check on a TRACKED file.  OK is a boolean.
The count callers pass `(eql N value)': when the source file is absent
the reader returns the symbol `m54-imp5-absent', so `eql' yields nil and
this prints FAIL.  When OK is the symbol `m54-imp5-absent' itself the
file is absent, and this prints FAIL too.  Either way this registers a
real FAILING ERT test, so an absent src/ file is a real error, not a
pass: the harness parses ERT's batch output for its exit code, so a
princ'd FAIL with no ERT test would leave the exit code 0."
  (let* ((absent (eq ok 'm54-imp5-absent))
         (pass (and (not absent) (and ok t))))
    (if absent
        (princ (format "FAIL m54/imp5/%s (source file absent)\n" name))
      (princ (format "%s m54/imp5/%s\n" (if pass "PASS" "FAIL") name)))
    (setq m54-imp5--registered (1+ m54-imp5--registered))
    (m54-imp5--bump-group)
    (imp-register-bool-as-ert-test (format "m54-imp5/%s" name) pass)))

;;; --- S1. REMOVED by M61 imp-2b (milestone.org findings F2) -----------

;; S1 held the source-text pins of src/term.c (lines, ^DEFUN ( count,
;; --tty-* leaf count, scm_c_public_ref sites), the
;; mod/emacs/tty-output.scm line count, and the tree-wide
;; scm_c_public_ref count.  A source-inspection test proves no behavior,
;; so the assertions are removed and NOT re-pinned
;; (docs/milestone-overview.org =Test rules for ports=, docs/arch.org
;; =Testing=).  The measured numbers live in the commit message of M61
;; imp-2b.

;;; --- S2. The registration (brief.org section 8) ---------------------

;; test/pty-driver.py and tool/run-tests.scm are tracked files.

(setq m54-imp5--group 's2)

(m54-imp5--check "run-tests-m54-imp5"
                 (m54-imp5--contains-p "tool/run-tests.scm"
                                       "test/m54/test-m54-imp5.el"))
(m54-imp5--check "run-tests-m54-imp5-after-imp4"
                 (let ((imp4 (m54-imp5--line-of "tool/run-tests.scm"
                                                "test/m54/test-m54-imp4.el"))
                       (imp5 (m54-imp5--line-of "tool/run-tests.scm"
                                                "test/m54/test-m54-imp5.el")))
                   (and (integerp imp4) (integerp imp5) (< imp4 imp5))))
(m54-imp5--check "run-tests-m54-group"
                 (m54-imp5--contains-p "tool/run-tests.scm" "(group (m54)"))
;; M61 imp-2g (review cr.org CR2, finding F2 / F7): the
;; `total-case-count', len(CASES), 42 pin is REMOVED, not re-pinned.
;; The driver's own --selftest holds the count checks at :3470 ... :3472.

;;; --- S3. The guards -------------------------------------------------

;; An --filter that matches no group already reports exit 0 with 0
;; tests, so a green m54 gate proves nothing until the corpus exists and
;; its checks really register.  These guards fail when the corpus body
;; is truncated or its core checks do not run.  The counts are stable
;; because every check is registered at load time.  S2 holds 3 checks.
;; S1 is gone (M61 imp-2b, findings F2), so it has no guard: a group that
;; holds no check needs none.

(setq m54-imp5--group 's3)

(m54-imp5--check "reg/min-s2-checks-3" (>= (m54-imp5--group-count 's2) 3))

;;; --- The group-total check ------------------------------------------

;; Select ONLY the m54-imp5 tests (the pattern is "^m54-imp5", not
;; "^m54-imp"): the whole (m54) group runs in one emacs process.  The
;; floor is measured from a real run: 4 registered checks (S2 3, S3 1)
;; plus the group-total deftest itself.  No check can fold to a
;; controlled skip -- this corpus needs no guile and no pty -- so the
;; floor is exact.  M61 imp-2b lowered it from 13 when findings F2
;; removed the 6 S1 source-text pins and the S1 guard; M61 imp-2g lowered
;; it to 5 when review cr.org CR2 removed the pty-driver count pin.

(defvar m54-imp5--min-gate-total 5
  "The minimum number of m54-imp5 ERT tests: 4 registered checks (S2 3,
S3 1) plus the group-total deftest.")

(ert-deftest m54-imp5/gate-m54-total ()
  "The m54-imp5 corpus registers at least its docs-independent floor."
  (should (>= (length (ert-select-tests "^m54-imp5" t))
              m54-imp5--min-gate-total)))

(princ (format "=== m54 imp-5 close-out suite done (%d tracked checks; s1 %d, s2 %d, s3 %d) ===\n"
               m54-imp5--registered
               (m54-imp5--group-count 's1)
               (m54-imp5--group-count 's2)
               (m54-imp5--group-count 's3)))
