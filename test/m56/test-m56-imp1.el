;;; test-m56-imp1.el --- M56 imp-1 deferred M54 input-stream descriptor audit corpus.
;;;
;;; M56 imp-1 is the deferred M54 input-stream descriptor row AUDIT
;;; (brief.org section 1).  It is docs only: the C delta is 0 and the
;;; Scheme delta is 0.  It traces the three C1 rows on the REAL tty
;;; init path and records the A1 / A2 verdict (docs/m56-plan.org).
;;;
;;; The three C1 rows are:
;;;   add_keyboard_wait_descriptor (src/process.c:8361)
;;;   get_tty_size                 (src/sysdep.c:1342, + policy :1293)
;;;   init_baud_rate               (src/sysdep.c:425)
;;;
;;; This corpus pins the measured surface, the three C sites, the
;;; tracked evidence for each class, the real tty init path, and the
;;; registration in the tree, so a stale number or a missing
;;; registration fails the run.
;;;
;;; It pins these groups:
;;;
;;;   S1 -- the re-measured surface of brief.org section 3: the base
;;;         commit 30213d139 is an ANCESTOR of HEAD; src/term.c (6,214
;;;         lines, 29 ^DEFUN (, 4 --tty-* leaf DEFUNs, 36
;;;         scm_c_public_ref sites); the 454 lines of
;;;         mod/emacs/tty-output.scm; the tree-wide scm_c_public_ref
;;;         count over src/*.[ch] (260); the 3 src/termchar.h FILE *
;;;         streams; and the test/pty-driver.py cases (24 at imp-1;
;;;         imp-2 adds one, so 25 now).  S1 holds 9 checks.
;;;   S2 -- the row map (brief.org section 4): the 3 C1 rows, their C
;;;         definitions, their src/term.c call sites, and the tracked C
;;;         evidence for each class.  Row 1 and row 3 STAYS C (C state
;;;         keyed on the descriptor / the termios read on the C
;;;         descriptor).  Row 2 keeps the C wrapper only: its DECISION
;;;         already moved to Scheme (`tty-size', M43 imp-5) and the
;;;         descriptor read stays C (a passthrough is not a port).  The
;;;         boundary rule is do-not-give-scheme-a-C-descriptor.  S2
;;;         holds 7 checks.
;;;   S3 -- the real tty init path: the built src/emacs runs on a real
;;;         PTY through test/pty-driver.py (a case that boots emacs and
;;;         drives the terminal, so init_tty runs the three rows).  A
;;;         missing built src/emacs or a missing PTY is an explicit
;;;         INFO skip, NEVER a pass.  S3 holds 2 checks.
;;;   S4 -- the registration: the corpus is registered in the (m56)
;;;         group of tool/run-tests.scm, after the (m55) group, and the
;;;         (m55) group stays present.  S4 holds 4 checks.
;;;   S5 -- the guards: 4 checks -- one per-group min-count guard for
;;;         each of S1 .. S4.  The in-process group-total `ert-deftest'
;;;         is a separate test in the same phase; it is NOT one of the 4
;;;         counted checks (the floor is 26 registered checks plus that
;;;         deftest = 27).
;;;
;;; This corpus reads TRACKED files only (src/, mod/, and the tracked
;;; runner tool/run-tests.scm, test/pty-driver.py).  It does NOT read
;;; docs/ (docs/kb.org test-must-not-read-docs): a gitignored record can
;;; only pass or skip, so a record check proves nothing.
;;;
;;; A read error is a real error, never a silent pass.  An absent
;;; TRACKED file is a real FAIL, not a pass (brief.org section 4).  A
;;; missing `git', `python3', `guile' binary or a missing PTY is an
;;; explicit INFO skip, never a pass.  Every check registers a real ERT
;;; test via imp-register-bool-as-ert-test, so the harness parses the
;;; ERT output and the exit code is correct.

(princ "=== m56 imp-1 deferred M54 input-stream descriptor audit suite ===\n")

(require 'imp-ert-report)

(defvar m56-imp1--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))
(defvar m56-imp1--registered 0
  "Total number of checks this corpus has registered.")
(defvar m56-imp1--group nil
  "The group that `m56-imp1--check' counts into: `s1' .. `s5', or nil.")
(defvar m56-imp1--counts nil
  "Alist of (GROUP . COUNT) for the registered checks.")

(defun m56-imp1--group-count (group)
  "Number of checks registered so far in GROUP."
  (or (cdr (assq group m56-imp1--counts)) 0))

(defun m56-imp1--bump-group ()
  "Count one check into `m56-imp1--group'."
  (when m56-imp1--group
    (let ((cell (assq m56-imp1--group m56-imp1--counts)))
      (if cell
          (setcdr cell (1+ (cdr cell)))
        (push (cons m56-imp1--group 1) m56-imp1--counts)))))

(defun m56-imp1--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
the symbol `m56-imp1-absent' when REL does not exist."
  (let ((path (expand-file-name rel m56-imp1--root)))
    (if (not (file-exists-p path))
        'm56-imp1-absent
      (with-temp-buffer
        (insert-file-contents path)
        (funcall fn)))))

(defun m56-imp1--contains-p (rel needle)
  "Non-nil when the TRACKED file REL contains NEEDLE.  An absent file
folds to nil, so a check prints FAIL: an absent TRACKED file is a real
error, not a pass (brief.org section 4)."
  (let ((hit (m56-imp1--with rel
               (lambda ()
                 (goto-char (point-min))
                 (search-forward needle nil t)))))
    (and (not (eq hit 'm56-imp1-absent)) (and hit t))))

(defun m56-imp1--holds-all (rel needles)
  "Non-nil when the TRACKED file REL holds every NEEDLE.  REL is read
once, so a multi-needle check does not re-read the file per needle."
  (m56-imp1--with rel
    (lambda ()
      (let ((all t))
        (dolist (needle needles)
          (goto-char (point-min))
          (unless (search-forward needle nil t) (setq all nil)))
        all))))

(defun m56-imp1--ordered-p (rel needles)
  "Non-nil when the TRACKED file REL holds every NEEDLE in the GIVEN
ORDER: each search starts after the previous match."
  (m56-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((all t))
        (dolist (needle needles)
          (when all
            (unless (search-forward needle nil t) (setq all nil))))
        all))))

(defun m56-imp1--exists-p (rel)
  "Non-nil when the TRACKED file REL (repo-root-relative) exists."
  (file-exists-p (expand-file-name rel m56-imp1--root)))

(defun m56-imp1--lines (rel)
  "Count the newlines of REL the way `wc -l' does."
  (m56-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (search-forward "\n" nil t) (setq n (1+ n)))
        n))))

(defun m56-imp1--count (rel regexp)
  "Count the matches of REGEXP in REL."
  (m56-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (re-search-forward regexp nil t) (setq n (1+ n)))
        n))))

(defun m56-imp1--line-of (rel regexp)
  "Return the 1-based line number of the first REGEXP match in REL, or
nil when REGEXP does not match.  The reader returns the symbol
`m56-imp1-absent' when REL does not exist, so the caller's `eql' folds
to nil and the check FAILS."
  (m56-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (when (re-search-forward regexp nil t)
        (let ((end (match-beginning 0)) (n 1))
          (goto-char (point-min))
          (while (search-forward "\n" end t) (setq n (1+ n)))
          n)))))

(defun m56-imp1--count-defun-leaf (rel)
  "Count the matches of `^DEFUN (\"--tty-' in REL.  Do NOT pin the leaves
with `grep -c -- '--tty-'': that count is higher, because each leaf name
also occurs in a sibling docstring (brief.org section 3)."
  (m56-imp1--count rel "^DEFUN (\"--tty-"))

(defun m56-imp1--count-scm-ref ()
  "Count scm_c_public_ref over src/*.[ch] (the brief.org section 3
tree-wide measure, `grep -rc scm_c_public_ref src/*.c src/*.h').  The
selector is .c and .h ONLY, to match the brief command; the .m files
(Objective-C, out of scope) are not read."
  (let ((total 0)
        (dir (expand-file-name "src" m56-imp1--root)))
    (dolist (f (directory-files dir t "\\.[ch]\\'"))
      (setq total (+ total (or (m56-imp1--count f "scm_c_public_ref") 0))))
    total))

(defun m56-imp1--run (prog args)
  "Run PROG with ARGS in a subprocess from the repo root and return its
stdout / stderr as a string, or the symbol `m56-imp1-prog-absent' when
PROG is not on PATH.  The default directory is the repo root, so a
relative ARGS stays repo-root-relative."
  (if (not (executable-find prog))
      'm56-imp1-prog-absent
    (let ((buf (get-buffer-create " *m56-imp1-run*"))
          (default-directory m56-imp1--root))
      (unwind-protect
          (progn
            (with-current-buffer buf (erase-buffer))
            (apply #'call-process prog nil buf nil args)
            (with-current-buffer buf
              (buffer-substring-no-properties (point-min) (point-max))))
        (kill-buffer buf)))))

(defun m56-imp1--ancestor-p (ancestor descendant)
  "Non-nil when ANCESTOR is an ancestor of DESCENDANT in the repo at
`m56-imp1--root'.  Return the symbol `m56-imp1-prog-absent' when the
`git' binary is not on PATH, and nil when `git' fails (for example an
unknown revision).  A committed corpus must NOT pin the running HEAD to
a literal base commit: when imp-1 is committed, HEAD moves to the imp
commit, so a hard equality check against the base always fails (cr.org
F1).  The ancestry relation stays true when the branch advances."
  (if (not (executable-find "git"))
      'm56-imp1-prog-absent
    (let ((default-directory m56-imp1--root))
      (zerop (call-process "git" nil nil nil
                           "merge-base" "--is-ancestor"
                           ancestor descendant)))))

(defun m56-imp1--check (name ok)
  "Report and register one check on a TRACKED file.  OK is a boolean.
The count callers pass `(eql N value)': when the source file is absent
the reader returns the symbol `m56-imp1-absent', so `eql' yields nil and
this prints FAIL.  When OK is the symbol `m56-imp1-absent' itself the
file is absent, and this prints FAIL too.  Either way this registers a
real FAILING ERT test, so an absent TRACKED file is a real error, not a
pass."
  (let* ((absent (eq ok 'm56-imp1-absent))
         (pass (and (not absent) (and ok t))))
    (if absent
        (princ (format "FAIL m56/imp1/%s (source file absent)\n" name))
      (princ (format "%s m56/imp1/%s\n" (if pass "PASS" "FAIL") name)))
    (setq m56-imp1--registered (1+ m56-imp1--registered))
    (m56-imp1--bump-group)
    (imp-register-bool-as-ert-test (format "m56-imp1/%s" name) pass)))

(defun m56-imp1--info-skip (name reason)
  "Register one explicit INFO skip, counted into the current group.  A
host limit is a skip, never a pass (brief.org section 11)."
  (princ (format "INFO m56/imp1/%s %s\n" name reason))
  (setq m56-imp1--registered (1+ m56-imp1--registered))
  (m56-imp1--bump-group)
  (imp-register-skip-as-ert-test (format "m56-imp1/%s" name) reason))

;;; --- S1. The measured surface (brief.org section 3) -----------------

;; One check per row of brief.org section 3.  Row 1 (HEAD) checks that
;; the base commit is an ANCESTOR of the running HEAD: a committed
;; corpus cannot pin HEAD to a literal, because HEAD moves to the imp
;; commit (cr.org F1).  A missing `git' is an explicit INFO skip, never
;; a pass.  The source rows re-measure the tree at HEAD; do NOT copy a
;; planning number.

(setq m56-imp1--group 's1)

(let ((ok (m56-imp1--ancestor-p "30213d139" "HEAD")))
  (if (eq ok 'm56-imp1-prog-absent)
      (m56-imp1--info-skip "head-30213d139" "no git binary on PATH")
    (m56-imp1--check "head-30213d139" ok)))

(m56-imp1--check "term.c-lines-6425"
                 (eql 6425 (m56-imp1--lines "src/term.c")))
(m56-imp1--check "term.c-defun-count-29"
                 (eql 29 (m56-imp1--count "src/term.c" "^DEFUN (")))
(m56-imp1--check "term.c-leaf-defun-count-4"
                 (eql 4 (m56-imp1--count-defun-leaf "src/term.c")))
(m56-imp1--check "term.c-scm-ref-41"
                 (eql 41 (m56-imp1--count "src/term.c" "scm_c_public_ref")))
(m56-imp1--check "tree-wide-scm-ref-265"
                 (eql 265 (m56-imp1--count-scm-ref)))
(m56-imp1--check "tty-output.scm-lines-682"
                 (eql 682 (m56-imp1--lines "mod/emacs/tty-output.scm")))
(m56-imp1--check "termchar-file-streams-3"
                 (and (eql 51 (m56-imp1--line-of "src/termchar.h" "FILE \\*input;"))
                      (eql 53 (m56-imp1--line-of "src/termchar.h" "FILE \\*output;"))
                      (eql 61 (m56-imp1--line-of "src/termchar.h" "FILE \\*termscript;"))))
(m56-imp1--check "pty-driver-cases-32"
                 (m56-imp1--contains-p
                  "test/pty-driver.py" "\"total-case-count\", len(CASES), 32"))

;;; --- S2. The row map (brief.org section 4) --------------------------

;; Row 1 -- add_keyboard_wait_descriptor.  C def src/process.c:8361.
;; It WRITES C state (`fd_callback_info[desc].flags', `max_desc') that
;; is keyed on the descriptor, so the class is STAYS C.

(setq m56-imp1--group 's2)

(m56-imp1--check "row1-c-def"
                 (m56-imp1--contains-p "src/process.c"
                                       "add_keyboard_wait_descriptor (int desc)"))
(m56-imp1--check "row1-stays-c-c-state"
                 (m56-imp1--holds-all "src/process.c"
                                      '("fd_callback_info[desc].flags"
                                        "max_desc = desc")))

;; Row 2 -- get_tty_size.  C def src/sysdep.c:1342, + the pure policy
;; helper `get_tty_size_policy' at :1293.  The policy helper already
;; dispatches into Scheme (`(emacs tty-modes) tty-size', M43 imp-5) over
;; a plain int fd and returns a plain (width . height) pair.  The C
;; wrapper keeps only the DESCRIPTOR read (`fileno'), so it STAYS C: a
;; passthrough is not a port (passthrough-leaf-is-not-a-port).

(m56-imp1--check "row2-c-def-and-delegate"
                 (m56-imp1--holds-all "src/sysdep.c"
                                      '("get_tty_size (int fd, int *widthp, int *heightp)"
                                        "get_tty_size_policy (fd, widthp, heightp);")))
(m56-imp1--check "row2-decision-moved-to-scheme"
                 (and (m56-imp1--contains-p
                       "src/sysdep.c"
                       "scm_c_public_ref (\"emacs tty-modes\", \"tty-size\")")
                      (m56-imp1--contains-p "mod/emacs/tty-modes.scm"
                                            "(define (tty-size fd)")))

;; Row 3 -- init_baud_rate.  C def src/sysdep.c:425.  It READS the
;; termios state through `tcgetattr' on the C descriptor and WRITES the
;; C global `baud_rate', so the class is STAYS C.

(m56-imp1--check "row3-c-def-termios"
                 (m56-imp1--holds-all "src/sysdep.c"
                                      '("init_baud_rate (int fd)"
                                        "tcgetattr (fd, &sg);")))
(m56-imp1--check "row3-stays-c-global"
                 (m56-imp1--contains-p "src/sysdep.c"
                                       "baud_rate = (emacs_ospeed"))

;; The three rows read the descriptor of the C FILE * stream in
;; src/term.c: `fileno' of the C stream stays C.  The rule
;; do-not-give-scheme-a-C-descriptor holds, and a passthrough wrapper is
;; not a port.  The sites are the real tty init path (init_tty at :4645
;; / :4930 / :5068, the resume path at :2842 / :2854).

(m56-imp1--check "sites-descriptor-stays-c"
                 (m56-imp1--holds-all
                  "src/term.c"
                  '("add_keyboard_wait_descriptor (fd);"
                    "add_keyboard_wait_descriptor (fileno (tty->input));"
                    "get_tty_size (fileno (tty->input), &width, &height);"
                    "init_baud_rate (fileno (tty->input));")))

;;; --- S3. The real tty init path (brief.org section 4.1 step 5) ------

;; The module-load probe is NOT proof.  The real path is the built
;; src/emacs on a real PTY: test/pty-driver.py boots the child emacs,
;; which runs init_tty and therefore the three C1 rows.  A missing
;; python3, a missing built src/emacs, or a missing PTY is an explicit
;; INFO skip, NEVER a pass.

(setq m56-imp1--group 's3)

(let ((out (m56-imp1--run "python3"
                          (list "test/pty-driver.py" "--selftest"))))
  (if (eq out 'm56-imp1-prog-absent)
      (m56-imp1--info-skip "pty-driver-selftest" "no python3 binary on PATH")
    (m56-imp1--check "pty-driver-selftest"
                     (and (string-match-p "SELFTEST OK" out) t))))

(let ((emacs (expand-file-name "src/emacs" m56-imp1--root)))
  (cond
   ((not (and (file-exists-p emacs) (file-executable-p emacs)))
    (m56-imp1--info-skip "pty-real-path-tty-init" "no built src/emacs"))
   (t
    (let ((out (m56-imp1--run
                "python3"
                (list "test/pty-driver.py" "--emacs" emacs
                      "--group" "m53-imp3"))))
      (cond
       ((eq out 'm56-imp1-prog-absent)
        (m56-imp1--info-skip "pty-real-path-tty-init" "no python3 binary on PATH"))
       ((string-match-p "PASS m53-imp3/vertical-slice-e2e" out)
        (m56-imp1--check "pty-real-path-tty-init" t))
       ((string-match-p "INFO m53-imp3/vertical-slice-e2e" out)
        (m56-imp1--info-skip "pty-real-path-tty-init" "no PTY on this host"))
       (t
        (m56-imp1--check "pty-real-path-tty-init" nil)))))))

;;; --- S4. The registration -------------------------------------------

(setq m56-imp1--group 's4)

(m56-imp1--check "run-tests-m56-imp1"
                 (m56-imp1--contains-p "tool/run-tests.scm"
                                       "test/m56/test-m56-imp1.el"))
(m56-imp1--check "run-tests-m56-group"
                 (m56-imp1--contains-p "tool/run-tests.scm" "(group (m56)"))
(m56-imp1--check "run-tests-m56-after-m55"
                 (m56-imp1--ordered-p "tool/run-tests.scm"
                                      '("(group (m55)" "(group (m56)")))
(m56-imp1--check "run-tests-m55-present"
                 (m56-imp1--contains-p "tool/run-tests.scm" "(group (m55)"))

;;; --- S5. The guards -------------------------------------------------

;; An --filter that matches no group already reports exit 0 with 0
;; tests, so a green m56 gate proves nothing until the corpus exists and
;; its checks really register.  These guards fail when the corpus body
;; is truncated or its core checks do not run.  The counts are stable
;; because every check is registered at load time.  S1 holds 9 checks,
;; S2 holds 7, S3 holds 2, and S4 holds 4.

(setq m56-imp1--group 's5)

(m56-imp1--check "reg/min-s1-checks-9" (>= (m56-imp1--group-count 's1) 9))
(m56-imp1--check "reg/min-s2-checks-7" (>= (m56-imp1--group-count 's2) 7))
(m56-imp1--check "reg/min-s3-checks-2" (>= (m56-imp1--group-count 's3) 2))
(m56-imp1--check "reg/min-s4-checks-4" (>= (m56-imp1--group-count 's4) 4))

;;; --- The group-total check ------------------------------------------

;; The measured count of m56-imp1 tests is 27: 26 registered checks
;; (S1 9, S2 7, S3 2, S4 4, S5 4) plus the group-total deftest itself.
;; The S3 checks may fold to a controlled INFO skip on a host with no
;; python3 / no built src/emacs / no PTY, and a controlled skip is still
;; a registered test, so the floor holds either way.

(defvar m56-imp1--min-gate-total 27
  "The exact number of m56-imp1 ERT tests: 26 registered checks (S1 9,
S2 7, S3 2, S4 4, S5 4) plus the group-total deftest itself.")

(ert-deftest m56-imp1/gate-m56-total ()
  "The m56-imp1 corpus registers at least its docs-independent floor."
  (should (>= (length (ert-select-tests "^m56-imp1" t))
              m56-imp1--min-gate-total)))

(princ (format "=== m56 imp-1 suite done (%d checks; s1 %d, s2 %d, s3 %d, s4 %d, s5 %d) ===\n"
               m56-imp1--registered
               (m56-imp1--group-count 's1)
               (m56-imp1--group-count 's2)
               (m56-imp1--group-count 's3)
               (m56-imp1--group-count 's4)
               (m56-imp1--group-count 's5)))
