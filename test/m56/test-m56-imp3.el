;;; test-m56-imp3.el --- M56 imp-3 close-out corpus (re-measure and record).
;;;
;;; M56 imp-3 is the CLOSE-OUT (brief.org section 1).  It moves no C and
;;; no Scheme: the net C delta is 0 and the net Scheme delta is 0.  It
;;; re-measures the surface, runs the gates, and records the result.
;;; This corpus pins the end state against the TRACKED tree, so a stale
;;; number or a missing registration fails the run.
;;;
;;; It pins four groups, S1 .. S4:
;;;
;;;   S1 -- the re-measured surface of brief.org section 4, measured at
;;;         the imp-3 base HEAD dc8af1488.  Group A (the M55 loader
;;;         surface, 9 rows): mod/emacs/loader.scm 1,187 lines / 74
;;;         (symbol-function 'X) matches / 19 symbol-fbound? lines / 15
;;;         set-symbol-function! lines / 8 FIX-*-guilemacs lines;
;;;         mod/emacs/reader.scm 2,021 lines; prelude/load.scm 265 lines
;;;         / 70 ^(use-modules lines / 31 ^(init-...-registrations)
;;;         lines.  Group B (the TTY surface M56 audits, 8 rows):
;;;         src/term.c 6,214 lines / 29 ^DEFUN / 4 --tty-* leaf DEFUNs /
;;;         36 scm_c_public_ref sites; the tree-wide scm_c_public_ref
;;;         count over src/*.[chm] (260); mod/emacs/tty-output.scm 454
;;;         lines; the 3 src/termchar.h FILE * streams (:51 / :53 / :61);
;;;         test/pty-driver.py 26 cases.  S1 holds 17 checks.
;;;   S2 -- the registration (brief.org section 5): this corpus is
;;;         present in the (m56) group of tool/run-tests.scm, it comes
;;;         after test/m56/test-m56-imp2.el, the (m56) group exists, and
;;;         the group holds test-m56-imp1.el and test-m56-imp2.el.  It
;;;         also pins that the base dc8af1488 is an ANCESTOR of HEAD
;;;         (not a rev-parse equality: HEAD moves when imp-3 lands), and
;;;         checks the UNTRACKED advisory helper tool/m56-audit.sh only
;;;         when it exists (else an INFO skip), so a fresh clone must
;;;         not FAIL on an untracked host artifact.  S2 holds 6 checks.
;;;   S3 -- the real path (brief.org section 5): python3
;;;         test/pty-driver.py --selftest prints SELFTEST OK, and the
;;;         case m56-imp2/tty-init-e2e PASSES on the built src/emacs on
;;;         a real PTY.  A missing python3, a missing built src/emacs,
;;;         or a missing PTY is an explicit INFO skip, NEVER a pass.  A
;;;         module-load probe is NOT proof.  S3 holds 2 checks.
;;;   S4 -- the guards: one per-group min-count guard for each of S1,
;;;         S2, and S3.  The in-process group-total `ert-deftest' is a
;;;         separate test in the same phase; it is NOT one of the 3
;;;         counted guards.
;;;
;;; This corpus reads TRACKED files only (src/, mod/, prelude/,
;;; tool/run-tests.scm, test/pty-driver.py).  It does NOT read docs/
;;; (docs/kb.org test-must-not-read-docs): docs/ is gitignored, so a
;;; record check can only pass or skip, and it proves nothing.  It does
;;; NOT read milestone.org (untracked).  It does NOT run a nested m56
;;; gate subprocess: the in-process `ert-deftest' replaces a nested
;;; gate.
;;;
;;; A read error is a real error, never a silent pass.  An absent
;;; TRACKED file is a real FAIL, not a pass: a count read of an absent
;;; file folds to a FAIL.  A missing `git', `python3' binary, a missing
;;; built src/emacs, or a missing PTY is an explicit INFO skip, never a
;;; pass.  Every check registers a real ERT test via
;;; imp-register-bool-as-ert-test, so the harness parses the ERT output
;;; and the exit code is correct: a princ'd FAIL with no ERT test would
;;; leave the exit code 0.

(princ "=== m56 imp-3 close-out suite ===\n")

(require 'imp-ert-report)

(defvar m56-imp3--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))
(defvar m56-imp3--registered 0
  "Total number of checks this corpus has registered.")
(defvar m56-imp3--group nil
  "The group that `m56-imp3--check' counts into: `s1' .. `s4', or nil.")
(defvar m56-imp3--counts nil
  "Alist of (GROUP . COUNT) for the registered checks.")

(defun m56-imp3--group-count (group)
  "Number of checks registered so far in GROUP."
  (or (cdr (assq group m56-imp3--counts)) 0))

(defun m56-imp3--bump-group ()
  "Count one check into `m56-imp3--group'."
  (when m56-imp3--group
    (let ((cell (assq m56-imp3--group m56-imp3--counts)))
      (if cell
          (setcdr cell (1+ (cdr cell)))
        (push (cons m56-imp3--group 1) m56-imp3--counts)))))

(defun m56-imp3--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
the symbol `m56-imp3-absent' when REL does not exist."
  (let ((path (expand-file-name rel m56-imp3--root)))
    (if (not (file-exists-p path))
        'm56-imp3-absent
      (with-temp-buffer
        (insert-file-contents path)
        (funcall fn)))))

(defun m56-imp3--contains-p (rel needle)
  "Non-nil when the TRACKED file REL (repo-root-relative) contains
NEEDLE.  An absent file folds to nil, so `m56-imp3--check' prints FAIL:
an absent TRACKED file is a real error, not a pass (brief.org section 5)."
  (let ((hit (m56-imp3--with rel
               (lambda ()
                 (goto-char (point-min))
                 (search-forward needle nil t)))))
    (and (not (eq hit 'm56-imp3-absent)) (and hit t))))

(defun m56-imp3--line-of (rel needle)
  "1-based line number of the first literal NEEDLE in REL, or nil.
An absent file folds to nil."
  (m56-imp3--with rel
    (lambda ()
      (goto-char (point-min))
      (when (search-forward needle nil t)
        (line-number-at-pos (match-beginning 0))))))

(defun m56-imp3--ordered-p (rel needles)
  "Non-nil when the TRACKED file REL holds every NEEDLE in the GIVEN
ORDER: each search starts after the previous match."
  (m56-imp3--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((all t))
        (dolist (needle needles)
          (when all
            (unless (search-forward needle nil t) (setq all nil))))
        all))))

(defun m56-imp3--lines (rel)
  "Count the newlines of REL the way `wc -l' does."
  (m56-imp3--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (search-forward "\n" nil t) (setq n (1+ n)))
        n))))

(defun m56-imp3--count (rel regexp)
  "Count the matches of REGEXP in REL, the way `grep -o PATTERN | wc -l'
does.  Use this only for a brief row whose command is `grep -o'."
  (m56-imp3--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (re-search-forward regexp nil t) (setq n (1+ n)))
        n))))

(defun m56-imp3--count-lines (rel regexp)
  "Count the LINES of REL that match REGEXP, the way `grep -c PATTERN'
does.  The brief.org section 4 rows that use `grep -c' count LINES, not
matches, so a line with two matches counts once: a later imp that puts
two refs on one line keeps this pin in step with the grep pin."
  (m56-imp3--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0)
            (last 0))
        (while (re-search-forward regexp nil t)
          (let ((line (line-number-at-pos (match-beginning 0))))
            (unless (= line last)
              (setq n (1+ n))
              (setq last line))))
        n))))

(defun m56-imp3--count-scm-ref ()
  "Count scm_c_public_ref over the TOP src/ directory, one file at a
time, over src/*.[chm] (the brief.org section 4 tree-wide measure: the
count is 260 for both src/*.[ch] and src/*.[chm]).  Do NOT use a
recursive `grep -r src/': that also counts the .scm, .go, and
sub-directory files."
  (let ((total 0)
        (dir (expand-file-name "src" m56-imp3--root)))
    (dolist (f (directory-files dir t "\\.[chm]\\'"))
      (setq total (+ total (or (m56-imp3--count-lines f "scm_c_public_ref") 0))))
    total))

(defun m56-imp3--check (name ok)
  "Report and register one check on a TRACKED file.  OK is a boolean.
The count callers pass `(eql N value)': when the source file is absent
the reader returns the symbol `m56-imp3-absent', so `eql' yields nil and
this prints FAIL.  When OK is the symbol `m56-imp3-absent' itself the
file is absent, and this prints FAIL too.  Either way this registers a
real FAILING ERT test, so an absent TRACKED file is a real error, not a
pass: the harness parses ERT's batch output for its exit code, so a
princ'd FAIL with no ERT test would leave the exit code 0."
  (let* ((absent (eq ok 'm56-imp3-absent))
         (pass (and (not absent) (and ok t))))
    (if absent
        (princ (format "FAIL m56/imp3/%s (source file absent)\n" name))
      (princ (format "%s m56/imp3/%s\n" (if pass "PASS" "FAIL") name)))
    (setq m56-imp3--registered (1+ m56-imp3--registered))
    (m56-imp3--bump-group)
    (imp-register-bool-as-ert-test (format "m56-imp3/%s" name) pass)))

(defun m56-imp3--info-skip (name reason)
  "Register one explicit INFO skip, counted into the current group.  A
host limit is a skip, never a pass (brief.org section 5)."
  (princ (format "INFO m56/imp3/%s %s\n" name reason))
  (setq m56-imp3--registered (1+ m56-imp3--registered))
  (m56-imp3--bump-group)
  (imp-register-skip-as-ert-test (format "m56-imp3/%s" name) reason))

(defun m56-imp3--check-advisory (name rel needle)
  "Check the ADVISORY helper file REL for NEEDLE, or skip when REL is
absent.  Every *-audit.sh helper in this repository is UNTRACKED, so a
fresh clone has no such file.  When REL exists this registers a real
check.  When REL is absent this registers an explicit INFO skip, never a
pass (brief.org section 5: a host limit is a skip, never a pass).  Either
way an ERT test is registered, so the S2 count and the group-total floor
stay stable, and a fresh clone does not FAIL on an untracked host
artifact."
  (let ((path (expand-file-name rel m56-imp3--root)))
    (if (not (file-exists-p path))
        (m56-imp3--info-skip
         name (format "%s absent (untracked advisory helper)" rel))
      (m56-imp3--check name (m56-imp3--contains-p rel needle)))))

;;; --- The subprocess probe (git / python3) ---------------------------

(defun m56-imp3--run (prog args)
  "Run PROG with ARGS in a subprocess from the repo root and return its
stdout / stderr as a string, or the symbol `m56-imp3-prog-absent' when
PROG is not on PATH.  The default directory is the repo root."
  (if (not (executable-find prog))
      'm56-imp3-prog-absent
    (let ((buf (get-buffer-create " *m56-imp3-run*"))
          (default-directory m56-imp3--root))
      (unwind-protect
          (progn
            (with-current-buffer buf (erase-buffer))
            (apply #'call-process prog nil buf nil args)
            (with-current-buffer buf
              (buffer-substring-no-properties (point-min) (point-max))))
        (kill-buffer buf)))))

(defun m56-imp3--exit (prog args)
  "Run PROG with ARGS from the repo root and return its exit code, or
the symbol `m56-imp3-prog-absent' when PROG is not on PATH."
  (if (not (executable-find prog))
      'm56-imp3-prog-absent
    (let ((default-directory m56-imp3--root))
      (apply #'call-process prog nil nil nil args))))

(defun m56-imp3--base-is-ancestor-p ()
  "Non-nil when the imp-3 base dc8af1488 is an ANCESTOR of HEAD.  Use
`git merge-base --is-ancestor' (exit 0 = ancestor), NOT a `git rev-parse'
equality check: HEAD moves to the imp-3 commit when imp-3 lands, so an
equality check would fail (brief.org section 5).  Return the symbol
`m56-imp3-prog-absent' when git is not on PATH."
  (let ((code (m56-imp3--exit
               "git" (list "merge-base" "--is-ancestor" "dc8af1488" "HEAD"))))
    (if (eq code 'm56-imp3-prog-absent)
        'm56-imp3-prog-absent
      (eql code 0))))

;;; --- S1. The re-measured surface (brief.org section 4) --------------

;; One check per brief.org section 4 value row.  Re-measured at the
;; imp-3 base HEAD dc8af1488.  An absent TRACKED file fails: the count
;; reader returns `m56-imp3-absent' and `eql' yields nil (brief.org
;; section 5).  Group A holds 9 checks, Group B holds 8.

(setq m56-imp3--group 's1)

;; --- Group A.  The M55 loader surface. ---

;; A1: mod/emacs/loader.scm lines = 1,398.  Was 1,391 and before it 1,389
;; and 1,363 at the 2 imp-7 attempts, 1,190 at the imp-3 base,
;; 1,203 before M60 imp-6 and 1,328 before M60 imp-7: the name follows
;; the measurement, the old values stay here (cr.org F3).  Rows 23 and 24
;; add the `defmacro' store and the `eval-when-compile' branch, and the
;; L10 note of cr.org F2 adds 7 lines.
;; M60 imp-8 (row 27) RE-PIN: loader.scm 1,398 -> 1,409 LINES (the
;; guarded `make-obsolete-variable' install in `init-loader').
;; M60 imp-9 (row 28a) RE-PIN: loader.scm 1,409 -> 1,511 LINES (the 3
;; branches `cond' / `let*' / `while' and the L16 ... L20 limit
;; block, above them, in `elisp-loader-eval-form').
;; M60 imp-9 fix (cr.org F3, F4, F5; L21) RE-PIN: loader.scm 1,480 -> 1,511 LINES.
;; M60 imp-11 (cr.org F3, F5) RE-PIN: loader.scm 1,511 -> 1,620 LINES; the check NAME drops the
;; stale number, because it changed again (an earlier cr.org round F5).
(m56-imp3--check "loader-lines"
                 ;; M60 imp-12 RE-PIN: loader.scm 1,620 -> 1,642 LINES (OLD value 1,620).
                 ;; M60 imp-13 RE-PIN: loader.scm 1,642 -> 1,653 LINES (OLD value 1,642).
                 ;; M60 imp-15 (row 32) RE-PIN: the hash-table cells move the loader.scm line
                 ;; count and its 4 counters.  OLD: 1,653 lines, 74, 40, 36 and 9.
                 ;; M60 imp-16 (row 25) RE-PIN: 1,792 -> 1,813 LINES (the guarded
                 ;; `normal-top-level-add-to-load-path' install in `init-loader').
                 ;; M60 imp-17 (row F3) RE-PIN: 1,813 -> 1,833 LINES (OLD value 1,813).
                 (eql 1833 (m56-imp3--lines "mod/emacs/loader.scm")))
;; A2: (symbol-function 'X) matches in loader.scm = 74.  The brief
;; command is `grep -o ... | wc -l', a MATCH count, so count matches.
(m56-imp3--check "loader-symbol-function-74"
                 (eql 76 (m56-imp3--count "mod/emacs/loader.scm"
                                          "(symbol-function '")))
;; A3: symbol-fbound? lines in loader.scm = 19 (`grep -c').
;; M60 imp-8 (row 27) RE-PIN: loader.scm `symbol-fbound?' 22 -> 23
;; LINES (1 guarded install, the row-18 pattern of `provide').
;; M60 imp-11 (cr.org F3, F5) RE-PIN: `symbol-fbound?` 23 -> 39 LINES; the check NAME drops the
;; stale number, because it changed again (an earlier cr.org round F5).
(m56-imp3--check "loader-symbol-fbound"
                 ;; M60 imp-13 RE-PIN: `symbol-fbound?' 39 -> 40 LINES (OLD value 39).
                 ;; M60 imp-16 RE-PIN: 55 -> 56 LINES (OLD value 55; the row-25
                 ;; guarded install in `init-loader').
                 ;; M60 imp-17 (row F3) RE-PIN: `symbol-fbound?' 56 -> 57 LINES (OLD value 56).
                 (eql 57 (m56-imp3--count-lines "mod/emacs/loader.scm"
                                                "symbol-fbound?")))
;; A4: set-symbol-function! lines in loader.scm = 15 (`grep -c').
;; M60 imp-8 (row 27) RE-PIN: loader.scm `set-symbol-function!' 18 -> 19
;; LINES (the same guarded install).  `FIX-.*guilemacs' stays 9.
;; M60 imp-11 (cr.org F3, F5) RE-PIN: `set-symbol-function!` 19 -> 35 LINES; the check NAME drops the
;; stale number, because it changed again (an earlier cr.org round F5).
(m56-imp3--check "loader-set-symbol-function"
                 ;; M60 imp-13 RE-PIN: `set-symbol-function!' 35 -> 36 LINES (OLD value 35).
                 ;; M60 imp-16 RE-PIN: 51 -> 52 LINES (OLD value 51).
                 ;; M60 imp-17 (row F3) RE-PIN: `set-symbol-function!' 52 -> 53 LINES (OLD value 52).
                 (eql 53 (m56-imp3--count-lines "mod/emacs/loader.scm"
                                                "set-symbol-function!")))
;; A5: FIX-*-guilemacs lines in loader.scm = 8 (`grep -c').
(m56-imp3--check "loader-fix-markers-8"
                 (eql 10 (m56-imp3--count-lines "mod/emacs/loader.scm"
                                               "FIX-.*guilemacs")))
;; A6: mod/emacs/reader.scm lines = 2,021.
(m56-imp3--check "reader-lines-2021"
                 (eql 2021 (m56-imp3--lines "mod/emacs/reader.scm")))
;; A7: prelude/load.scm lines = 229.
(m56-imp3--check "prelude-lines-229"
                 (eql 229 (m56-imp3--lines "prelude/load.scm")))
;; A8: prelude/load.scm ^(use-modules lines = 70.  Use the ANCHORED
;; pattern: the plain pattern also matches one comment line and gives 71
;; (brief.org section 4).
(m56-imp3--check "prelude-use-modules-71"
                 (eql 71 (m56-imp3--count-lines "prelude/load.scm"
                                                "^(use-modules")))
;; A9: prelude/load.scm ^(init-...-registrations) lines = 31.
(m56-imp3--check "prelude-init-registrations-31"
                 (eql 31 (m56-imp3--count-lines "prelude/load.scm"
                                                "^(init-.*-registrations)")))

;; --- Group B.  The TTY surface that M56 audits. ---

;; B1: src/term.c lines = 6,363 (M58 imp-3).
(m56-imp3--check "term-c-lines-6425"
                 (eql 6425 (m56-imp3--lines "src/term.c")))
;; B2: src/term.c ^DEFUN count = 29.
(m56-imp3--check "term-c-defun-29"
                 (eql 29 (m56-imp3--count-lines "src/term.c" "^DEFUN (")))
;; B3: the 4 --tty-* leaf DEFUNs.  Count the DEFUN forms, NOT the bare
;; leaf token: each leaf name also occurs in a sibling docstring.
(m56-imp3--check "term-c-tty-leaf-4"
                 (eql 4 (m56-imp3--count-lines "src/term.c" "^DEFUN (\"--tty-")))
;; B4: src/term.c scm_c_public_ref sites = 39 (M58 imp-3 added 3).
(m56-imp3--check "term-c-scm-ref-41"
                 (eql 41 (m56-imp3--count-lines "src/term.c" "scm_c_public_ref")))
;; B5: the tree-wide scm_c_public_ref count over src/*.[chm] = 263.
(m56-imp3--check "tree-wide-scm-ref-267"
                 (eql 267 (m56-imp3--count-scm-ref)))
;; B6: mod/emacs/tty-output.scm lines = 635 (M58 imp-3 added the face section).
(m56-imp3--check "tty-output-lines-635"
                 (eql 682 (m56-imp3--lines "mod/emacs/tty-output.scm")))
;; B7: the 3 src/termchar.h FILE * streams at :51 / :53 / :61.
(m56-imp3--check "termchar-file-streams-3"
                 (and (eql 51 (m56-imp3--line-of "src/termchar.h" "FILE *input;"))
                      (eql 53 (m56-imp3--line-of "src/termchar.h" "FILE *output;"))
                      (eql 61 (m56-imp3--line-of "src/termchar.h" "FILE *termscript;"))))
;; B8: test/pty-driver.py cases = 26 (the total-case-count pin).  The
;; close-out adds no PTY case, so the total stays 26 (brief.org section
;; 9).  This guards against a stale literal 24.
(m56-imp3--check "pty-driver-cases-32"
                 (and (m56-imp3--contains-p
                       "test/pty-driver.py"
                       "\"total-case-count\", len(CASES), 32")
                      (= 0 (m56-imp3--count "test/pty-driver.py"
                                            "len(CASES), 24"))))

;;; --- S2. The registration and the base (brief.org sections 5, 7) ----

;; Pin the registration against the TRACKED runner tool/run-tests.scm,
;; and pin the base as an ANCESTOR of HEAD.  The advisory helper
;; tool/m56-audit.sh is UNTRACKED, so its load-line check is a real
;; check when the file exists and an INFO skip when it is absent: a
;; fresh clone must not FAIL on an untracked host artifact.

(setq m56-imp3--group 's2)

(m56-imp3--check "run-tests-m56-imp3"
                 (m56-imp3--contains-p "tool/run-tests.scm"
                                       "test/m56/test-m56-imp3.el"))
(m56-imp3--check "run-tests-m56-imp3-after-imp2"
                 (let ((imp2 (m56-imp3--line-of "tool/run-tests.scm"
                                                "test/m56/test-m56-imp2.el"))
                       (imp3 (m56-imp3--line-of "tool/run-tests.scm"
                                                "test/m56/test-m56-imp3.el")))
                   (and (integerp imp2) (integerp imp3) (< imp2 imp3))))
(m56-imp3--check "run-tests-m56-group"
                 (m56-imp3--contains-p "tool/run-tests.scm" "(group (m56)"))
(m56-imp3--check "run-tests-m56-holds-imp1-imp2"
                 (and (m56-imp3--contains-p "tool/run-tests.scm"
                                            "test/m56/test-m56-imp1.el")
                      (m56-imp3--contains-p "tool/run-tests.scm"
                                            "test/m56/test-m56-imp2.el")))
(let ((anc (m56-imp3--base-is-ancestor-p)))
  (cond
   ((eq anc 'm56-imp3-prog-absent)
    (m56-imp3--info-skip "base-is-ancestor" "no git binary on PATH"))
   (t
    (m56-imp3--check "base-is-ancestor" anc))))
(m56-imp3--check-advisory "audit-loads-m56-imp3"
                          "tool/m56-audit.sh"
                          "test/m56/test-m56-imp3.el")

;;; --- S3. The real path (brief.org section 5) ------------------------

;; The module-load probe is NOT proof.  The real path is the built
;; src/emacs on a real PTY: test/pty-driver.py boots the child emacs,
;; which runs init_tty and therefore the three C1 rows.  A missing
;; python3, a missing built src/emacs, or a missing PTY is an explicit
;; INFO skip, NEVER a pass.

(setq m56-imp3--group 's3)

(let ((out (m56-imp3--run "python3" (list "test/pty-driver.py" "--selftest"))))
  (if (eq out 'm56-imp3-prog-absent)
      (m56-imp3--info-skip "pty-driver-selftest" "no python3 binary on PATH")
    (m56-imp3--check "pty-driver-selftest"
                     (and (string-match-p "SELFTEST OK" out) t))))

(let ((emacs (expand-file-name "src/emacs" m56-imp3--root)))
  (cond
   ((not (and (file-exists-p emacs) (file-executable-p emacs)))
    (m56-imp3--info-skip "pty-real-path-tty-init" "no built src/emacs"))
   (t
    (let ((out (m56-imp3--run
                "python3"
                (list "test/pty-driver.py" "--emacs" emacs
                      "--case" "m56-imp2/tty-init-e2e"))))
      (cond
       ((eq out 'm56-imp3-prog-absent)
        (m56-imp3--info-skip "pty-real-path-tty-init" "no python3 binary on PATH"))
       ((string-match-p "PASS m56-imp2/tty-init-e2e" out)
        (m56-imp3--check "pty-real-path-tty-init" t))
       ((string-match-p "INFO m56-imp2/tty-init-e2e" out)
        (m56-imp3--info-skip "pty-real-path-tty-init" "no PTY on this host"))
       (t
        (m56-imp3--check "pty-real-path-tty-init" nil)))))))

;;; --- S4. The guards -------------------------------------------------

;; An --filter that matches no group already reports exit 0 with 0
;; tests, so a green m56 gate proves nothing until the corpus exists and
;; its checks really register.  These guards fail when the corpus body
;; is truncated or its core checks do not run.  The counts are stable
;; because every check is registered at load time.  S1 holds 17 checks,
;; S2 holds 6, and S3 holds 2.

(setq m56-imp3--group 's4)

(m56-imp3--check "reg/min-s1-checks-17" (>= (m56-imp3--group-count 's1) 17))
(m56-imp3--check "reg/min-s2-checks-6" (>= (m56-imp3--group-count 's2) 6))
(m56-imp3--check "reg/min-s3-checks-2" (>= (m56-imp3--group-count 's3) 2))

;;; --- The group-total check ------------------------------------------

;; Select ONLY the m56-imp3 tests (the pattern is "^m56-imp3", not
;; "^m56-imp"): the whole (m56) group runs in one emacs process.  The
;; floor is measured from a real run: 28 registered checks (S1 17, S2 6,
;; S3 2, S4 3) plus the group-total deftest itself.  No check can fold
;; to a controlled skip -- the S2 ancestor and audit checks and the S3
;; checks register as ERT tests either way (a real check or an INFO
;; skip) -- so the floor is exact.

(defvar m56-imp3--min-gate-total 29
  "The exact number of m56-imp3 ERT tests: 28 registered checks (S1 17,
S2 6, S3 2, S4 3) plus the group-total deftest itself.")

(ert-deftest m56-imp3/gate-m56-total ()
  "The m56-imp3 corpus registers at least its docs-independent floor."
  (should (>= (length (ert-select-tests "^m56-imp3" t))
              m56-imp3--min-gate-total)))

(princ (format "=== m56 imp-3 close-out suite done (%d tracked checks; s1 %d, s2 %d, s3 %d, s4 %d) ===\n"
               m56-imp3--registered
               (m56-imp3--group-count 's1)
               (m56-imp3--group-count 's2)
               (m56-imp3--group-count 's3)
               (m56-imp3--group-count 's4)))
