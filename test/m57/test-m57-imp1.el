;;; test-m57-imp1.el --- M57 imp-1 C2 TTY FILE * stream ownership audit corpus.
;;;
;;; M57 imp-1 is the C2 TTY FILE * stream ownership AUDIT (brief.org
;;; section 1).  It is docs only: the C delta is 0 and the Scheme delta
;;; is 0.  It measures the three src/termchar.h FILE * streams of struct
;;; tty_display_info (input :51, output :53, termscript :61), answers the
;;; safe-handle question first, and records the A1 / A2 verdict
;;; (docs/m57-plan.org).
;;;
;;; This corpus pins the measured surface, the row map (the three stream
;;; paths and their src/term.c sites), the handle contract, the boundary
;;; rule, the real tty init path, and the registration in the tree, so a
;;; stale number or a missing registration fails the run.
;;;
;;; It pins these groups:
;;;
;;;   S1 -- the re-measured surface of brief.org section 3 (the base
;;;         e2423fcb0 as an ANCESTOR of HEAD, and the src/term.c /
;;;         src/termchar.h / mod/emacs/tty-output.scm / pty-driver.py
;;;         numbers).  S1 holds 9 checks.
;;;   S2 -- the row map of brief.org section 5: the OUTPUT, TERMSCRIPT,
;;;         and INPUT stream paths and their src/term.c sites, the
;;;         handle contract, and the boundary rule
;;;         do-not-give-scheme-a-C-descriptor.  S2 holds 13 checks.
;;;   S3 -- the real tty init path: the built src/emacs runs on a real
;;;         PTY through test/pty-driver.py, so init_tty runs the stream
;;;         sites.  On a result that is neither PASS nor INFO the check
;;;         RETRIES the driver once, then prints both runs when the
;;;         retry still fails (brief.org section 7).  A missing built
;;;         src/emacs or PTY is an explicit INFO skip.  S3 holds 2.
;;;   S4 -- the registration: the corpus is registered in the (m57)
;;;         group of tool/run-tests.scm, after the (m56) group, and the
;;;         (m56) group stays present.  S4 holds 4 checks.
;;;   S5 -- the guards: 4 checks -- one per-group min-count guard for
;;;         each of S1 .. S4.  The in-process group-total `ert-deftest'
;;;         is a separate test in the same phase; it is NOT one of the
;;;         4 counted checks (the floor is 32 checks plus that deftest
;;;         = 33).
;;;
;;; This corpus reads TRACKED files only (src/, mod/, and the tracked
;;; runner tool/run-tests.scm, test/pty-driver.py).  It does NOT read
;;; docs/ (docs/kb.org test-must-not-read-docs): a gitignored record can
;;; only pass or skip, so a record check proves nothing.
;;;
;;; A read error is a real error, never a silent pass.  An absent
;;; TRACKED file is a real FAIL, not a pass (brief.org section 8).  A
;;; missing `git', `python3', `guile' binary or a missing PTY is an
;;; explicit INFO skip, never a pass.  Every check registers a real ERT
;;; test via imp-register-bool-as-ert-test, so the harness parses the
;;; ERT output and the exit code is correct.

(princ "=== m57 imp-1 C2 TTY FILE * stream ownership audit suite ===\n")

(require 'imp-ert-report)

(defvar m57-imp1--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))
(defvar m57-imp1--registered 0
  "Total number of checks this corpus has registered.")
(defvar m57-imp1--group nil
  "The group that `m57-imp1--check' counts into: `s1' .. `s5', or nil.")
(defvar m57-imp1--counts nil
  "Alist of (GROUP . COUNT) for the registered checks.")

(defun m57-imp1--group-count (group)
  "Number of checks registered so far in GROUP."
  (or (cdr (assq group m57-imp1--counts)) 0))

(defun m57-imp1--bump-group ()
  "Count one check into `m57-imp1--group'."
  (when m57-imp1--group
    (let ((cell (assq m57-imp1--group m57-imp1--counts)))
      (if cell
          (setcdr cell (1+ (cdr cell)))
        (push (cons m57-imp1--group 1) m57-imp1--counts)))))

(defun m57-imp1--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
the symbol `m57-imp1-absent' when REL does not exist."
  (let ((path (expand-file-name rel m57-imp1--root)))
    (if (not (file-exists-p path))
        'm57-imp1-absent
      (with-temp-buffer
        (insert-file-contents path)
        (funcall fn)))))

(defun m57-imp1--contains-p (rel needle)
  "Non-nil when the TRACKED file REL contains NEEDLE.  An absent file
folds to nil, so a check prints FAIL: an absent TRACKED file is a real
error, not a pass (brief.org section 8)."
  (let ((hit (m57-imp1--with rel
               (lambda ()
                 (goto-char (point-min))
                 (search-forward needle nil t)))))
    (and (not (eq hit 'm57-imp1-absent)) (and hit t))))

(defun m57-imp1--holds-all (rel needles)
  "Non-nil when the TRACKED file REL holds every NEEDLE.  REL is read
once, so a multi-needle check does not re-read the file per needle."
  (m57-imp1--with rel
    (lambda ()
      (let ((all t))
        (dolist (needle needles)
          (goto-char (point-min))
          (unless (search-forward needle nil t) (setq all nil)))
        all))))

(defun m57-imp1--ordered-p (rel needles)
  "Non-nil when the TRACKED file REL holds every NEEDLE in the GIVEN
ORDER: each search starts after the previous match."
  (m57-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((all t))
        (dolist (needle needles)
          (when all
            (unless (search-forward needle nil t) (setq all nil))))
        all))))

(defun m57-imp1--exists-p (rel)
  "Non-nil when the TRACKED file REL (repo-root-relative) exists."
  (file-exists-p (expand-file-name rel m57-imp1--root)))

(defun m57-imp1--lines (rel)
  "Count the newlines of REL the way `wc -l' does."
  (m57-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (search-forward "\n" nil t) (setq n (1+ n)))
        n))))

(defun m57-imp1--count (rel regexp)
  "Count the matches of REGEXP in REL."
  (m57-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (re-search-forward regexp nil t) (setq n (1+ n)))
        n))))

(defun m57-imp1--line-of (rel regexp)
  "Return the 1-based line number of the first REGEXP match in REL, or
nil when REGEXP does not match.  The reader returns the symbol
`m57-imp1-absent' when REL does not exist, so the caller's `eql' folds
to nil and the check FAILS."
  (m57-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (when (re-search-forward regexp nil t)
        (let ((end (match-beginning 0)) (n 1))
          (goto-char (point-min))
          (while (search-forward "\n" end t) (setq n (1+ n)))
          n)))))

(defun m57-imp1--count-defun-leaf (rel)
  "Count the matches of `^DEFUN (\"--tty-' in REL.  Do NOT pin the leaves
with `grep -c -- '--tty-'': that count is higher, because each leaf name
also occurs in a sibling docstring (brief.org section 3)."
  (m57-imp1--count rel "^DEFUN (\"--tty-"))

(defun m57-imp1--count-scm-ref ()
  "Count scm_c_public_ref over src/*.[ch] (the brief.org section 3
tree-wide measure, `grep -rc scm_c_public_ref src/*.c src/*.h').  The
selector is .c and .h ONLY, to match the brief command; the .m files
(Objective-C, out of scope) are not read."
  (let ((total 0)
        (dir (expand-file-name "src" m57-imp1--root)))
    (dolist (f (directory-files dir t "\\.[ch]\\'"))
      (setq total (+ total (or (m57-imp1--count f "scm_c_public_ref") 0))))
    total))

(defun m57-imp1--run (prog args)
  "Run PROG with ARGS in a subprocess from the repo root and return its
stdout / stderr as a string, or the symbol `m57-imp1-prog-absent' when
PROG is not on PATH.  The default directory is the repo root, so a
relative ARGS stays repo-root-relative."
  (if (not (executable-find prog))
      'm57-imp1-prog-absent
    (let ((buf (get-buffer-create " *m57-imp1-run*"))
          (default-directory m57-imp1--root))
      (unwind-protect
          (progn
            (with-current-buffer buf (erase-buffer))
            (apply #'call-process prog nil buf nil args)
            (with-current-buffer buf
              (buffer-substring-no-properties (point-min) (point-max))))
        (kill-buffer buf)))))

(defun m57-imp1--ancestor-p (ancestor descendant)
  "Non-nil when ANCESTOR is an ancestor of DESCENDANT in the repo at
`m57-imp1--root'.  Return the symbol `m57-imp1-prog-absent' when the
`git' binary is not on PATH, and nil when `git' fails (for example an
unknown revision).  A committed corpus must NOT pin the running HEAD to
a literal base commit: when imp-1 is committed, HEAD moves to the imp
commit, so a hard equality check against the base always fails.  The
ancestry relation stays true when the branch advances."
  (if (not (executable-find "git"))
      'm57-imp1-prog-absent
    (let ((default-directory m57-imp1--root))
      (zerop (call-process "git" nil nil nil
                           "merge-base" "--is-ancestor"
                           ancestor descendant)))))

(defun m57-imp1--check (name ok)
  "Report and register one check on a TRACKED file.  OK is a boolean.
The count callers pass `(eql N value)': when the source file is absent
the reader returns the symbol `m57-imp1-absent', so `eql' yields nil and
this prints FAIL.  When OK is the symbol `m57-imp1-absent' itself the
file is absent, and this prints FAIL too.  Either way this registers a
real FAILING ERT test, so an absent TRACKED file is a real error, not a
pass."
  (let* ((absent (eq ok 'm57-imp1-absent))
         (pass (and (not absent) (and ok t))))
    (if absent
        (princ (format "FAIL m57/imp1/%s (source file absent)\n" name))
      (princ (format "%s m57/imp1/%s\n" (if pass "PASS" "FAIL") name)))
    (setq m57-imp1--registered (1+ m57-imp1--registered))
    (m57-imp1--bump-group)
    (imp-register-bool-as-ert-test (format "m57-imp1/%s" name) pass)))

(defun m57-imp1--info-skip (name reason)
  "Register one explicit INFO skip, counted into the current group.  A
host limit is a skip, never a pass (brief.org section 7)."
  (princ (format "INFO m57/imp1/%s %s\n" name reason))
  (setq m57-imp1--registered (1+ m57-imp1--registered))
  (m57-imp1--bump-group)
  (imp-register-skip-as-ert-test (format "m57-imp1/%s" name) reason))

;;; --- S1. The measured surface (brief.org section 3) -----------------

;; One check per row of brief.org section 3.  Row 1 (HEAD) checks that
;; the base commit is an ANCESTOR of the running HEAD: a committed
;; corpus cannot pin HEAD to a literal, because HEAD moves to the imp
;; commit.  A missing `git' is an explicit INFO skip, never a pass.  The
;; source rows re-measure the tree at HEAD; do NOT copy a planning
;; number.

(setq m57-imp1--group 's1)

(let ((ok (m57-imp1--ancestor-p "e2423fcb0" "HEAD")))
  (if (eq ok 'm57-imp1-prog-absent)
      (m57-imp1--info-skip "head-e2423fcb0" "no git binary on PATH")
    (m57-imp1--check "head-e2423fcb0" ok)))

(m57-imp1--check "term.c-lines-6214"
                 (eql 6214 (m57-imp1--lines "src/term.c")))
(m57-imp1--check "term.c-defun-count-29"
                 (eql 29 (m57-imp1--count "src/term.c" "^DEFUN (")))
(m57-imp1--check "term.c-leaf-defun-count-4"
                 (eql 4 (m57-imp1--count-defun-leaf "src/term.c")))
(m57-imp1--check "term.c-scm-ref-36"
                 (eql 36 (m57-imp1--count "src/term.c" "scm_c_public_ref")))
(m57-imp1--check "tree-wide-scm-ref-260"
                 (eql 260 (m57-imp1--count-scm-ref)))
(m57-imp1--check "tty-output.scm-lines-454"
                 (eql 454 (m57-imp1--lines "mod/emacs/tty-output.scm")))
(m57-imp1--check "termchar-file-streams-3"
                 (and (eql 51 (m57-imp1--line-of "src/termchar.h" "FILE \\*input;"))
                      (eql 53 (m57-imp1--line-of "src/termchar.h" "FILE \\*output;"))
                      (eql 61 (m57-imp1--line-of "src/termchar.h" "FILE \\*termscript;"))))
(m57-imp1--check "pty-driver-cases-26"
                 (m57-imp1--contains-p
                  "test/pty-driver.py" "\"total-case-count\", len(CASES), 26"))

;;; --- S2. The row map (brief.org section 5) --------------------------

;; The row map groups the stream paths by stream: the OUTPUT path
;; (=tty->output=), the TERMSCRIPT path (=tty->termscript=), and the
;; INPUT path (=tty->input=).  Every path READS or WRITES the C FILE *,
;; the C descriptor, or C state keyed on them, so the class is STAYS C.
;; The boundary rule do-not-give-scheme-a-C-descriptor holds: a Guile
;; port must NOT own a C FILE * stream, and a passthrough is not a port.
;; The sites are the real tty init path (init_tty, the suspend / resume
;; path, and the teardown).

(setq m57-imp1--group 's2)

;; The OUTPUT write path: the termcap fwrite sites, the space putc, and
;; the M52 leaf write.

(m57-imp1--check "output-write-sites"
                 (m57-imp1--holds-all
                  "src/term.c"
                  '("fwrite (SDATA (string), 1, SBYTES (string), tty->output);"
                    "fwrite (conversion_buffer, 1, coding->produced, tty->output);"
                    "putc (' ', tty->output);"
                    "size_t written = fwrite (str, 1, len, tty->output);")))

;; The OUTPUT flush and clearerr sites.

(m57-imp1--check "output-flush-sites"
                 (m57-imp1--holds-all
                  "src/term.c"
                  '("fflush (tty->output);"
                    "if (fflush (tty->output) != 0)")))
(m57-imp1--check "output-clearerr-sites"
                 (m57-imp1--contains-p "src/term.c" "clearerr (tty->output);"))

;; The TERMSCRIPT copy path: the copy fwrite / putc, the NULL guard, and
;; the M52 copy write.

(m57-imp1--check "termscript-write-sites"
                 (m57-imp1--holds-all
                  "src/term.c"
                  '("fwrite (SDATA (string), 1, SBYTES (string), tty->termscript);"
                    "fwrite (conversion_buffer, 1, coding->produced, tty->termscript);"
                    "putc (' ', tty->termscript);"
                    "size_t copied = fwrite (str, 1, len, tty->termscript);")))
(m57-imp1--check "termscript-guard-and-close"
                 (m57-imp1--holds-all
                  "src/term.c"
                  '("if (tty->termscript)"
                    "emacs_fclose (tty->termscript);")))

;; The short-write path of the M52 leaf write, which touches BOTH the
;; output and the termscript streams.

(m57-imp1--check "shortwrite-m52-writes"
                 (m57-imp1--holds-all
                  "src/term.c"
                  '("size_t written = fwrite (str, 1, len, tty->output);"
                    "size_t copied = fwrite (str, 1, len, tty->termscript);")))

;; The INPUT read handle (the C FILE * itself) and the descriptor reads.
;; The descriptor reads (add_keyboard_wait_descriptor, get_tty_size,
;; init_baud_rate, tabs_safe_p) all take fileno (tty->input), so the
;; descriptor stays C.

(m57-imp1--check "input-read-handle"
                 (m57-imp1--contains-p "src/term.c"
                                       "f = t->display_info.tty->input;"))
(m57-imp1--check "input-descriptor-sites"
                 (m57-imp1--holds-all
                  "src/term.c"
                  '("add_keyboard_wait_descriptor (fileno (tty->input));"
                    "get_tty_size (fileno (tty->input), &width, &height);"
                    "init_baud_rate (fileno (tty->input));"
                    "tabs_safe_p (fileno (tty->input));")))

;; The open sites: the tty init and the resume reopen.  The stream
;; pointer is set in C, so ownership cannot start in Scheme.

(m57-imp1--check "open-sites"
                 (m57-imp1--holds-all
                  "src/term.c"
                  '("tty->input = tty->output"
                    "emacs_fdopen (fd, \"w+\")")))

;; The close sites: the suspend close and the teardown close of the 3
;; streams once.

(m57-imp1--check "close-sites"
                 (m57-imp1--holds-all
                  "src/term.c"
                  '("emacs_fclose (t->display_info.tty->output);"
                    "emacs_fclose (f);"
                    "emacs_fclose (tty->input);"
                    "emacs_fclose (tty->output);"
                    "emacs_fclose (tty->termscript);")))

;; The GPM output descriptor read and the suspend NULL clears: both hold
;; the C stream pointer / descriptor, so they stay C.

(m57-imp1--check "output-gpm-and-null-clears"
                 (m57-imp1--holds-all
                  "src/term.c"
                  '("fileno (tty->output)"
                    "t->display_info.tty->input = 0;"
                    "t->display_info.tty->output = 0;")))

;; The boundary rule and the single-writer contract, pinned by name in
;; the TRACKED C source (the corpus must NOT read docs/).

(m57-imp1--check "boundary-rule"
                 (m57-imp1--contains-p "src/term.c"
                                       "no Guile port owns a FILE *"))

(m57-imp1--check "termchar-stream-decls"
                 (m57-imp1--holds-all
                  "src/termchar.h"
                  '("FILE *input;"
                    "FILE *output;"
                    "FILE *termscript;")))

;;; --- S3. The real tty init path (brief.org section 5) ---------------

;; The module-load probe is NOT proof.  The real path is the built
;; src/emacs on a real PTY: test/pty-driver.py boots the child emacs,
;; which runs init_tty and therefore the stream sites.  A missing
;; python3, a missing built src/emacs, or a missing PTY is an explicit
;; INFO skip, NEVER a pass.

(setq m57-imp1--group 's3)

(let ((out (m57-imp1--run "python3"
                          (list "test/pty-driver.py" "--selftest"))))
  (if (eq out 'm57-imp1-prog-absent)
      (m57-imp1--info-skip "pty-driver-selftest" "no python3 binary on PATH")
    (m57-imp1--check "pty-driver-selftest"
                     (and (string-match-p "SELFTEST OK" out) t))))

(let ((emacs (expand-file-name "src/emacs" m57-imp1--root)))
  (cond
   ((not (and (file-exists-p emacs) (file-executable-p emacs)))
    (m57-imp1--info-skip "pty-real-path-tty-init" "no built src/emacs"))
   (t
    (let* ((args (list "test/pty-driver.py" "--emacs" emacs "--group" "m56-imp2"))
           (out1 (m57-imp1--run "python3" args))
           (done (or (eq out1 'm57-imp1-prog-absent)
                     (string-match-p "PASS m56-imp2/tty-init-e2e" out1)
                     (string-match-p "INFO m56-imp2/tty-init-e2e" out1)))
           (out2 (unless done (m57-imp1--run "python3" args)))
           (out (or out2 out1)))
      (cond
       ((eq out1 'm57-imp1-prog-absent)
        (m57-imp1--info-skip "pty-real-path-tty-init" "no python3 binary on PATH"))
       ((string-match-p "PASS m56-imp2/tty-init-e2e" out)
        (m57-imp1--check "pty-real-path-tty-init" t))
       ((string-match-p "INFO m56-imp2/tty-init-e2e" out)
        (m57-imp1--info-skip "pty-real-path-tty-init" "no PTY on this host"))
       (t
        (princ (format "m57 imp1 PTY run 1 (neither PASS nor INFO):\n%s\n" out1))
        (princ (format "m57 imp1 PTY run 2 (retry):\n%s\n" out2))
        (m57-imp1--check "pty-real-path-tty-init" nil)))))))

;;; --- S4. The registration -------------------------------------------

(setq m57-imp1--group 's4)

(m57-imp1--check "run-tests-m57-imp1"
                 (m57-imp1--contains-p "tool/run-tests.scm"
                                       "test/m57/test-m57-imp1.el"))
(m57-imp1--check "run-tests-m57-group"
                 (m57-imp1--contains-p "tool/run-tests.scm" "(group (m57)"))
(m57-imp1--check "run-tests-m57-after-m56"
                 (m57-imp1--ordered-p "tool/run-tests.scm"
                                      '("(group (m56)" "(group (m57)")))
(m57-imp1--check "run-tests-m56-present"
                 (m57-imp1--contains-p "tool/run-tests.scm" "(group (m56)"))

;;; --- S5. The guards -------------------------------------------------

;; An --filter that matches no group already reports exit 0 with 0
;; tests, so a green m57 gate proves nothing until the corpus exists and
;; its checks really register.  These guards fail when the corpus body
;; is truncated or its core checks do not run.  The counts are stable
;; because every check is registered at load time.  S1 holds 9 checks,
;; S2 holds 13, S3 holds 2, and S4 holds 4.

(setq m57-imp1--group 's5)

(m57-imp1--check "reg/min-s1-checks-9" (>= (m57-imp1--group-count 's1) 9))
(m57-imp1--check "reg/min-s2-checks-13" (>= (m57-imp1--group-count 's2) 13))
(m57-imp1--check "reg/min-s3-checks-2" (>= (m57-imp1--group-count 's3) 2))
(m57-imp1--check "reg/min-s4-checks-4" (>= (m57-imp1--group-count 's4) 4))

;;; --- The group-total check ------------------------------------------

;; The measured count of m57-imp1 tests is 33: 32 registered checks
;; (S1 9, S2 13, S3 2, S4 4, S5 4) plus the group-total deftest itself.
;; The S3 checks may fold to a controlled INFO skip on a host with no
;; python3 / no built src/emacs / no PTY, and a controlled skip is still
;; a registered test, so the floor holds either way.

(defvar m57-imp1--min-gate-total 33
  "The exact number of m57-imp1 ERT tests: 32 registered checks (S1 9,
S2 13, S3 2, S4 4, S5 4) plus the group-total deftest itself.")

(ert-deftest m57-imp1/gate-m57-total ()
  "The m57-imp1 corpus registers at least its docs-independent floor."
  (should (>= (length (ert-select-tests "^m57-imp1" t))
              m57-imp1--min-gate-total)))

(princ (format "=== m57 imp-1 suite done (%d checks; s1 %d, s2 %d, s3 %d, s4 %d, s5 %d) ===\n"
               m57-imp1--registered
               (m57-imp1--group-count 's1)
               (m57-imp1--group-count 's2)
               (m57-imp1--group-count 's3)
               (m57-imp1--group-count 's4)
               (m57-imp1--group-count 's5)))
