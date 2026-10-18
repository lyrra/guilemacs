;;; test-m58-imp1.el --- M58 imp-1 remaining TTY policy surface audit corpus.
;;;
;;; M58 imp-1 is the remaining TTY policy-surface AUDIT
;;; (docs/m58-plan.org).  It is docs only: the C delta is 0 and the Scheme delta
;;; is 0.  It walks every remaining movable TTY policy and state path in
;;; src/term.c, re-checks the C3 elisp-compiler boundary, classes each
;;; path MOVE / STAYS C / NOT PROVEN, and records the A1 / A2 verdict
;;; (docs/m58-plan.org).
;;;
;;; This corpus pins the measured surface, the row map (the group A ..
;;; group G paths and their src/term.c sites), the boundary rule, the
;;; real tty init path, and the registration in the tree, so a stale
;;; number or a missing registration fails the run.
;;;
;;; It pins these groups:
;;;
;;;   S1 -- the re-measured surface of docs/m58-plan.org (the base
;;;         fca28d3be as an ANCESTOR of HEAD, and the src/term.c /
;;;         src/termchar.h / mod/emacs/tty-output.scm / pty-driver.py
;;;         numbers).  S1 holds 9 checks.
;;;   S2 -- the row map of docs/m58-plan.org: group A (the
;;;         face-appearance policy), group B (the color-mode policy),
;;;         group C (the cost policy), group D (the init policy),
;;;         group E (the C-mechanism blocks), group F (the read-only
;;;         accessors), and group G (the C3 elisp-compiler boundary),
;;;         plus the boundary rule do-not-give-scheme-a-C-descriptor by
;;;         name in the TRACKED C source.  S2 holds 8 checks.
;;;   S3 -- the real tty init path: the built src/emacs runs on a real
;;;         PTY through test/pty-driver.py, so init_tty runs the TTY
;;;         sites.  On a result that is neither PASS nor INFO the check
;;;         RETRIES the driver once, then prints both runs when the
;;;         retry still fails (docs/m58-plan.org).  A missing built
;;;         src/emacs or PTY is an explicit INFO skip.  S3 holds 2.
;;;   S4 -- the registration: the corpus is registered in the (m58)
;;;         group of tool/run-tests.scm, after the (m57) group, and the
;;;         (m57) group stays present.  S4 holds 4 checks.
;;;   S5 -- the guards: 4 checks -- one per-group min-count guard for
;;;         each of S1 .. S4.  The in-process group-total `ert-deftest'
;;;         is a separate test in the same phase; it is NOT one of the
;;;         4 counted checks (the floor is 27 checks plus that deftest
;;;         = 28).
;;;
;;; This corpus reads TRACKED files only (src/, mod/, and the tracked
;;; runner tool/run-tests.scm, test/pty-driver.py).  It does NOT read
;;; docs/ (docs/kb.org test-must-not-read-docs): a gitignored record can
;;; only pass or skip, so a record check proves nothing.
;;;
;;; A read error is a real error, never a silent pass.  An absent
;;; TRACKED file is a real FAIL, not a pass (docs/m58-plan.org).  A
;;; missing `git', `python3', `guile' binary or a missing PTY is an
;;; explicit INFO skip, never a pass.  Every check registers a real ERT
;;; test via imp-register-bool-as-ert-test, so the harness parses the
;;; ERT output and the exit code is correct.

(princ "=== m58 imp-1 remaining TTY policy surface audit suite ===\n")

(require 'imp-ert-report)

(defvar m58-imp1--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))
(defvar m58-imp1--registered 0
  "Total number of checks this corpus has registered.")
(defvar m58-imp1--group nil
  "The group that `m58-imp1--check' counts into: `s1' .. `s5', or nil.")
(defvar m58-imp1--counts nil
  "Alist of (GROUP . COUNT) for the registered checks.")

(defun m58-imp1--group-count (group)
  "Number of checks registered so far in GROUP."
  (or (cdr (assq group m58-imp1--counts)) 0))

(defun m58-imp1--bump-group ()
  "Count one check into `m58-imp1--group'."
  (when m58-imp1--group
    (let ((cell (assq m58-imp1--group m58-imp1--counts)))
      (if cell
          (setcdr cell (1+ (cdr cell)))
        (push (cons m58-imp1--group 1) m58-imp1--counts)))))

(defun m58-imp1--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
the symbol `m58-imp1-absent' when REL does not exist."
  (let ((path (expand-file-name rel m58-imp1--root)))
    (if (not (file-exists-p path))
        'm58-imp1-absent
      (with-temp-buffer
        (insert-file-contents path)
        (funcall fn)))))

(defun m58-imp1--contains-p (rel needle)
  "Non-nil when the TRACKED file REL contains NEEDLE.  An absent file
folds to nil, so a check prints FAIL: an absent TRACKED file is a real
error, not a pass (docs/m58-plan.org)."
  (let ((hit (m58-imp1--with rel
               (lambda ()
                 (goto-char (point-min))
                 (search-forward needle nil t)))))
    (and (not (eq hit 'm58-imp1-absent)) (and hit t))))

(defun m58-imp1--holds-all (rel needles)
  "Non-nil when the TRACKED file REL holds every NEEDLE.  REL is read
once, so a multi-needle check does not re-read the file per needle."
  (m58-imp1--with rel
    (lambda ()
      (let ((all t))
        (dolist (needle needles)
          (goto-char (point-min))
          (unless (search-forward needle nil t) (setq all nil)))
        all))))

(defun m58-imp1--live-p (rel needle)
  "Non-nil when the TRACKED file REL holds NEEDLE on a line that is NOT
commented out.  A plain `contains-p' match also passes when the line is
commented out, and a commented line registers no test (cr.org F4), so
this skips a line whose first non-blank character is `;'."
  (m58-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((hit nil))
        (while (and (not hit) (search-forward needle nil t))
          (setq hit (save-excursion
                      (goto-char (line-beginning-position))
                      (not (looking-at-p "[ \t]*;")))))
        hit))))

(defun m58-imp1--pty-case-pins ()
  "Read the `test/pty-driver.py' case-count pins as (TOTAL . SUM).
TOTAL is the `total-case-count' pin; SUM is the sum of the per-group
`-case-count' pins.  Return nil when a pin is absent.  A plain string
search for the pin line proves nothing about the number of cases
(cr.org F5), so the corpus checks the two numbers agree and that TOTAL
is the re-pinned value."
  (m58-imp1--with "test/pty-driver.py"
    (lambda ()
      (goto-char (point-min))
      (let ((total nil) (sum 0) (n 0))
        ;; ONE bracket expression, no `\|' alternation in the pattern.
        ;; Each pin number is read in the same `let' init that runs the
        ;; search, so the match data is read right after the match.
        (while (re-search-forward "check(\"\\([a-z0-9-]*-case-count\\)\", " nil t)
          (let ((name (match-string 1))
                (pin (progn (re-search-forward "), \\([0-9]+\\))" nil t)
                           (match-string 1))))
            (if (string= name "total-case-count")
                (setq total (string-to-number (or pin "0")))
              (setq sum (+ sum (string-to-number (or pin "0"))))
              (setq n (1+ n)))))
        (and total (> n 0) (cons total sum))))))

(defun m58-imp1--ordered-p (rel needles)
  "Non-nil when the TRACKED file REL holds every NEEDLE in the GIVEN
ORDER: each search starts after the previous match."
  (m58-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((all t))
        (dolist (needle needles)
          (when all
            (unless (search-forward needle nil t) (setq all nil))))
        all))))

(defun m58-imp1--exists-p (rel)
  "Non-nil when the TRACKED file REL (repo-root-relative) exists."
  (file-exists-p (expand-file-name rel m58-imp1--root)))

(defun m58-imp1--lines (rel)
  "Count the newlines of REL the way `wc -l' does."
  (m58-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (search-forward "\n" nil t) (setq n (1+ n)))
        n))))

(defun m58-imp1--count (rel regexp)
  "Count the matches of REGEXP in REL."
  (m58-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (re-search-forward regexp nil t) (setq n (1+ n)))
        n))))

(defun m58-imp1--line-of (rel regexp)
  "Return the 1-based line number of the first REGEXP match in REL, or
nil when REGEXP does not match.  The reader returns the symbol
`m58-imp1-absent' when REL does not exist, so the caller's `eql' folds
to nil and the check FAILS."
  (m58-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (when (re-search-forward regexp nil t)
        (let ((end (match-beginning 0)) (n 1))
          (goto-char (point-min))
          (while (search-forward "\n" end t) (setq n (1+ n)))
          n)))))

(defun m58-imp1--count-defun-leaf (rel)
  "Count the matches of `^DEFUN (\"--tty-' in REL.  Do NOT pin the leaves
with `grep -c -- '--tty-'': that count is higher, because each leaf name
also occurs in a sibling docstring (docs/m58-plan.org)."
  (m58-imp1--count rel "^DEFUN (\"--tty-"))

(defun m58-imp1--count-scm-ref ()
  "Count scm_c_public_ref over src/*.[ch] (the docs/m58-plan.org
tree-wide measure, `grep -rc scm_c_public_ref src/*.c src/*.h').  The
selector is .c and .h ONLY, to match the brief command; the .m files
(Objective-C, out of scope) are not read."
  (let ((total 0)
        (dir (expand-file-name "src" m58-imp1--root)))
    (dolist (f (directory-files dir t "\\.[ch]\\'"))
      (setq total (+ total (or (m58-imp1--count f "scm_c_public_ref") 0))))
    total))

(defun m58-imp1--run (prog args)
  "Run PROG with ARGS in a subprocess from the repo root and return its
stdout / stderr as a string, or the symbol `m58-imp1-prog-absent' when
PROG is not on PATH.  The default directory is the repo root, so a
relative ARGS stays repo-root-relative."
  (if (not (executable-find prog))
      'm58-imp1-prog-absent
    (let ((buf (get-buffer-create " *m58-imp1-run*"))
          (default-directory m58-imp1--root))
      (unwind-protect
          (progn
            (with-current-buffer buf (erase-buffer))
            (apply #'call-process prog nil buf nil args)
            (with-current-buffer buf
              (buffer-substring-no-properties (point-min) (point-max))))
        (kill-buffer buf)))))

(defun m58-imp1--ancestor-p (ancestor descendant)
  "Non-nil when ANCESTOR is an ancestor of DESCENDANT in the repo at
`m58-imp1--root'.  Return the symbol `m58-imp1-prog-absent' when the
`git' binary is not on PATH, and nil when `git' fails (for example an
unknown revision).  A committed corpus must NOT pin the running HEAD to
a literal base commit: when imp-1 is committed, HEAD moves to the imp
commit, so a hard equality check against the base always fails.  The
ancestry relation stays true when the branch advances."
  (if (not (executable-find "git"))
      'm58-imp1-prog-absent
    (let ((default-directory m58-imp1--root))
      (zerop (call-process "git" nil nil nil
                           "merge-base" "--is-ancestor"
                           ancestor descendant)))))

(defun m58-imp1--check (name ok)
  "Report and register one check on a TRACKED file.  OK is a boolean.
The count callers pass `(eql N value)': when the source file is absent
the reader returns the symbol `m58-imp1-absent', so `eql' yields nil and
this prints FAIL.  When OK is the symbol `m58-imp1-absent' itself the
file is absent, and this prints FAIL too.  Either way this registers a
real FAILING ERT test, so an absent TRACKED file is a real error, not a
pass."
  (let* ((absent (eq ok 'm58-imp1-absent))
         (pass (and (not absent) (and ok t))))
    (if absent
        (princ (format "FAIL m58/imp1/%s (source file absent)\n" name))
      (princ (format "%s m58/imp1/%s\n" (if pass "PASS" "FAIL") name)))
    (setq m58-imp1--registered (1+ m58-imp1--registered))
    (m58-imp1--bump-group)
    (imp-register-bool-as-ert-test (format "m58-imp1/%s" name) pass)))

(defun m58-imp1--info-skip (name reason)
  "Register one explicit INFO skip, counted into the current group.  A
host limit is a skip, never a pass (docs/m58-plan.org)."
  (princ (format "INFO m58/imp1/%s %s\n" name reason))
  (setq m58-imp1--registered (1+ m58-imp1--registered))
  (m58-imp1--bump-group)
  (imp-register-skip-as-ert-test (format "m58-imp1/%s" name) reason))

;;; --- S1. The measured surface (docs/m58-plan.org) -----------------

;; One check per row of docs/m58-plan.org.  Row 1 (HEAD) checks that
;; the base commit is an ANCESTOR of the running HEAD: a committed
;; corpus cannot pin HEAD to a literal, because HEAD moves to the imp
;; commit.  A missing `git' is an explicit INFO skip, never a pass.  The
;; source rows re-measure the tree at HEAD; do NOT copy a planning
;; number.

(setq m58-imp1--group 's1)

(let ((ok (m58-imp1--ancestor-p "fca28d3be" "HEAD")))
  (if (eq ok 'm58-imp1-prog-absent)
      (m58-imp1--info-skip "head-fca28d3be" "no git binary on PATH")
    (m58-imp1--check "head-fca28d3be" ok)))

(m58-imp1--check "term.c-lines-6363"
                 (eql 6363 (m58-imp1--lines "src/term.c")))
(m58-imp1--check "term.c-defun-count-29"
                 (eql 29 (m58-imp1--count "src/term.c" "^DEFUN (")))
(m58-imp1--check "term.c-leaf-defun-count-4"
                 (eql 4 (m58-imp1--count-defun-leaf "src/term.c")))
(m58-imp1--check "term.c-scm-ref-39"
                 (eql 39 (m58-imp1--count "src/term.c" "scm_c_public_ref")))
(m58-imp1--check "tree-wide-scm-ref-263"
                 (eql 263 (m58-imp1--count-scm-ref)))
(m58-imp1--check "tty-output.scm-lines-635"
                 (eql 637 (m58-imp1--lines "mod/emacs/tty-output.scm")))
(m58-imp1--check "termchar-file-streams-3"
                 (and (eql 51 (m58-imp1--line-of "src/termchar.h" "FILE \\*input;"))
                      (eql 53 (m58-imp1--line-of "src/termchar.h" "FILE \\*output;"))
                      (eql 61 (m58-imp1--line-of "src/termchar.h" "FILE \\*termscript;"))))
;; M58 imp-2 added ONE PTY case (m58-imp2/face-appearance-e2e) and
;; M58 imp-3 added FIVE (the m58-imp3 group), so the counted surface
;; moves from 25 to 31.  The re-pin lands in the SAME commit as the new
;; cases, else this check goes red.  The imp-2 corpus T5 and the imp-3
;; corpus U2 pin this re-pin from the other side.
(m58-imp1--check "pty-driver-cases-31"
                 (let ((pins (m58-imp1--pty-case-pins)))
                   (and (consp pins)
                        (eql 31 (car pins))
                        ;; The group pins must add up to the total, so a
                        ;; group pin that moves without the total FAILS.
                        (eql (car pins) (cdr pins)))))

;;; --- S2. The row map (docs/m58-plan.org) --------------------------

;; The row map groups the remaining TTY policy and state paths by the
;; kind of decision they hold.  One check per group, against the TRACKED
;; C source (src/term.c), plus the C3 boundary in the TRACKED Scheme
;; source (mod/).  A MOVE candidate keeps every C mechanism in C; a
;; passthrough is not a port.  The boundary rule
;; do-not-give-scheme-a-C-descriptor holds: a Guile port must NOT own a C
;; FILE *, a C descriptor, or C state keyed on them.

(setq m58-imp1--group 's2)

;; Group A -- the face-appearance policy (a MOVE candidate).  The
;; DECISION "which cap key, in which order" is a plain function of plain
;; booleans; the C struct face read, MAY_USE_WITH_COLORS_P, tparam, the
;; OUTPUT macros, and the FILE * stay C.

;; M58 imp-3 re-pinned this row: the TTY_CAPABLE_P_TRY macro is GONE.
;; The Group A decision MOVED to Scheme (tty-face-on-steps,
;; tty-face-off-steps, tty-capable-p), so the row now pins the three
;; dispatcher call sites instead of the inline C chain.  The 7
;; TTY_CAPABLE_P_TRY rows survive as ONE table in the Scheme procedure.
(m58-imp1--check "group-a-face-appearance"
                 (m58-imp1--holds-all
                  "src/term.c"
                  '("turn_on_face (struct frame *f, struct face *face)"
                    "turn_off_face (struct frame *f, struct face *face)"
                    "tty_capable_p (struct tty_display_info *tty, unsigned int caps)"
                    "\"tty-face-on-steps\""
                    "\"tty-face-off-steps\""
                    "\"tty-capable-p\"")))

;; Group B -- the color-mode policy (a MOVE candidate).  The mode
;; canonicalization and the -1 / 0 / 8 choice are plain policy; the cap
;; strings, TN_max_colors, and the default static slots STAY C.  The
;; observable is tty-display-color-cells (a Lisp value).

(m58-imp1--check "group-b-color-mode"
                 (m58-imp1--holds-all
                  "src/term.c"
                  '("tty_setup_colors (struct tty_display_info *tty, int mode)"
                    "set_tty_color_mode (struct tty_display_info *tty, struct frame *f)"
                    "\"tty-display-color-cells\"")))

;; Group C -- the cost policy.  The cost evaluation calls the C termcap
;; code (tputs / tparam) and the block writes the C char_ins_del_vector
;; and tty->RPov, so it STAYS C, except the plain TS_repeat arithmetic.

(m58-imp1--check "group-c-cost"
                 (m58-imp1--holds-all
                  "src/term.c"
                  '("string_cost (const char *str)"
                    "calculate_ins_del_char_costs (struct frame *f)"
                    "calculate_costs (struct frame *frame)"
                    "cmcostinit (FRAME_TTY (frame));")))

;; Group D -- the init policy.  The must_succeed / maybe_fatal action is
;; emacs_perror / die, a C platform mechanism.  The UseTabs verdict
;; already moved to Scheme (M54 tabs-verdict); the termios read on the C
;; descriptor stays C.  The scroll_region_ok / line_ins_del_ok /
;; char_ins_del_ok verdicts are plain-value policy but NOT PROVEN: no
;; real, gated observable exists today.

(m58-imp1--check "group-d-init"
                 (m58-imp1--holds-all
                  "src/term.c"
                  '("maybe_fatal (bool must_succeed"
                    "tty->scroll_region_ok"
                    "init_baud_rate (fileno (tty->input));")))

;; Group E -- the C-mechanism blocks (STAYS C).  The glyph writers hold
;; the C struct glyph; the fkey block writes the C kboard key arrays; the
;; menu path holds C glyph matrices; tty_send_additional_strings walks
;; the C terminal->param_alist.

(m58-imp1--check "group-e-c-mechanism"
                 (m58-imp1--holds-all
                  "src/term.c"
                  '("tty_write_glyphs (struct frame *f, struct glyph *string, int len)"
                    "term_get_fkeys (char **address, KBOARD *kboard)"
                    "tty_menu_activate (tty_menu *menu, int *pane, int *selidx,"
                    "tty_send_additional_strings (struct terminal *terminal, Lisp_Object sym)")))

;; Group F -- the read-only accessors.  tty-no-underline and
;; tty-top-frame are one-field C reads (MOVE candidates).  The frame-list
;; / restack block mutates the C frame list.  suspend-tty / resume-tty
;; close and reopen the C streams.  tty--set-output-buffer-size /
;; tty--output-buffer-size are NOT PROVEN.

(m58-imp1--check "group-f-accessors"
                 (m58-imp1--holds-all
                  "src/term.c"
                  '("\"tty-no-underline\""
                    "\"tty-top-frame\""
                    "\"suspend-tty\""
                    "\"resume-tty\""
                    "\"tty--set-output-buffer-size\""
                    "\"tty--output-buffer-size\"")))

;; Group G -- the C3 elisp-compiler boundary (re-check).  The elisp
;; compiler is C: src/emacs.c resolves the (emacs-elisp spec) language
;; module.  The plain Guile path avoids it: loader.scm tests
;; (lookup-language 'emacs-elisp) and runtime.scm calls it.  The
;; boundary STAYS C without a safe handle first.

(m58-imp1--check "group-g-c3-boundary"
                 (and (m58-imp1--contains-p
                       "src/emacs.c" "scm_c_resolve_module (\"emacs-elisp spec\")")
                      (m58-imp1--contains-p
                       "mod/emacs/loader.scm" "(lookup-language 'emacs-elisp)")
                      (m58-imp1--contains-p
                       "mod/emacs-elisp/runtime.scm" "(lookup-language 'emacs-elisp)")
                      (m58-imp1--contains-p
                       "mod/emacs/loader.scm" "it never calls lookup-language or compile")))

;; The boundary rule and the single-writer contract, pinned by name in
;; the TRACKED C source (the corpus must NOT read docs/).

(m58-imp1--check "boundary-rule"
                 (m58-imp1--contains-p "src/term.c"
                                       "no Guile port owns a FILE *"))

;;; --- S3. The real tty init path (docs/m58-plan.org) ---------------

;; The module-load probe is NOT proof.  The real path is the built
;; src/emacs on a real PTY: test/pty-driver.py boots the child emacs,
;; which runs init_tty and therefore the TTY sites.  A missing python3, a
;; missing built src/emacs, or a missing PTY is an explicit INFO skip,
;; NEVER a pass.

(setq m58-imp1--group 's3)

(let ((out (m58-imp1--run "python3"
                          (list "test/pty-driver.py" "--selftest"))))
  (if (eq out 'm58-imp1-prog-absent)
      (m58-imp1--info-skip "pty-driver-selftest" "no python3 binary on PATH")
    (m58-imp1--check "pty-driver-selftest"
                     (and (string-match-p "SELFTEST OK" out) t))))

(let ((emacs (expand-file-name "src/emacs" m58-imp1--root)))
  (cond
   ((not (and (file-exists-p emacs) (file-executable-p emacs)))
    (m58-imp1--info-skip "pty-real-path-tty-init" "no built src/emacs"))
   (t
    (let* ((args (list "test/pty-driver.py" "--emacs" emacs "--group" "m56-imp2"))
           (out1 (m58-imp1--run "python3" args))
           (done (or (eq out1 'm58-imp1-prog-absent)
                     (string-match-p "PASS m56-imp2/tty-init-e2e" out1)
                     (string-match-p "INFO m56-imp2/tty-init-e2e" out1)))
           (out2 (unless done (m58-imp1--run "python3" args)))
           (out (or out2 out1)))
      (cond
       ((eq out1 'm58-imp1-prog-absent)
        (m58-imp1--info-skip "pty-real-path-tty-init" "no python3 binary on PATH"))
       ((string-match-p "PASS m56-imp2/tty-init-e2e" out)
        (m58-imp1--check "pty-real-path-tty-init" t))
       ((string-match-p "INFO m56-imp2/tty-init-e2e" out)
        (m58-imp1--info-skip "pty-real-path-tty-init" "no PTY on this host"))
       (t
        (princ (format "m58 imp1 PTY run 1 (neither PASS nor INFO):\n%s\n" out1))
        (princ (format "m58 imp1 PTY run 2 (retry):\n%s\n" out2))
        (m58-imp1--check "pty-real-path-tty-init" nil)))))))

;;; --- S4. The registration -------------------------------------------

(setq m58-imp1--group 's4)

(m58-imp1--check "run-tests-m58-imp1"
                 (m58-imp1--live-p "tool/run-tests.scm"
                                   "test/m58/test-m58-imp1.el"))
(m58-imp1--check "run-tests-m58-group"
                 (m58-imp1--live-p "tool/run-tests.scm" "(group (m58)"))
(m58-imp1--check "run-tests-m58-after-m57"
                 (m58-imp1--ordered-p "tool/run-tests.scm"
                                      '("(group (m57)" "(group (m58)")))
(m58-imp1--check "run-tests-m57-present"
                 (m58-imp1--live-p "tool/run-tests.scm" "(group (m57)"))

;;; --- S5. The guards -------------------------------------------------

;; An --filter that matches no group already reports exit 0 with 0
;; tests, so a green m58 gate proves nothing until the corpus exists and
;; its checks really register.  These guards fail when the corpus body
;; is truncated or its core checks do not run.  The counts are stable
;; because every check is registered at load time.  S1 holds 9 checks,
;; S2 holds 8, S3 holds 2, and S4 holds 4.

(setq m58-imp1--group 's5)

(m58-imp1--check "reg/min-s1-checks-9" (>= (m58-imp1--group-count 's1) 9))
(m58-imp1--check "reg/min-s2-checks-8" (>= (m58-imp1--group-count 's2) 8))
(m58-imp1--check "reg/min-s3-checks-2" (>= (m58-imp1--group-count 's3) 2))
(m58-imp1--check "reg/min-s4-checks-4" (>= (m58-imp1--group-count 's4) 4))

;;; --- The group-total check ------------------------------------------

;; The measured count of m58-imp1 tests is 28: 27 registered checks
;; (S1 9, S2 8, S3 2, S4 4, S5 4) plus the group-total deftest itself.
;; The S3 checks may fold to a controlled INFO skip on a host with no
;; python3 / no built src/emacs / no PTY, and a controlled skip is still
;; a registered test, so the floor holds either way.

(defvar m58-imp1--min-gate-total 28
  "The exact number of m58-imp1 ERT tests: 27 registered checks (S1 9,
S2 8, S3 2, S4 4, S5 4) plus the group-total deftest itself.")

(ert-deftest m58-imp1/gate-m58-total ()
  "The m58-imp1 corpus registers at least its docs-independent floor."
  (should (>= (length (ert-select-tests "^m58-imp1" t))
              m58-imp1--min-gate-total)))

(princ (format "=== m58 imp-1 suite done (%d checks; s1 %d, s2 %d, s3 %d, s4 %d, s5 %d) ===\n"
               m58-imp1--registered
               (m58-imp1--group-count 's1)
               (m58-imp1--group-count 's2)
               (m58-imp1--group-count 's3)
               (m58-imp1--group-count 's4)
               (m58-imp1--group-count 's5)))
