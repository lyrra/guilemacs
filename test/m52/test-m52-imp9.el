;;; test-m52-imp9.el --- M52 imp-9 close-out corpus (re-measure and record).
;;;
;;; M52 imp-9 is the close-out (brief.org section 1).  It changes no C
;;; and no Scheme: the net C delta is 0 and the net Scheme delta is 0.
;;; It re-measures the surface, runs the gates, and records the result.
;;; This corpus pins the end state against the tree, so a stale number
;;; or a missing registration fails the run.
;;;
;;; It pins three groups, S1 .. S3:
;;;
;;;   S1 -- the surface of brief.org section 3.2, re-measured at HEAD
;;;         d3ea64d7c: src/term.c (6,214 lines, 29 ^DEFUN (, 4
;;;         --tty-* leaf DEFUNs, 10 fwrite ( sites, 36 scm_c_public_ref
;;;         sites); mod/emacs/tty-output.scm (454 lines and its 34
;;;         #:export names); prelude/load.scm holds (use-modules
;;;         (emacs tty-output)); the 30-key m52_caps table; and the
;;;         tree-wide scm_c_public_ref count over src/*.[chm] (260).
;;;         S1 holds 42 checks.
;;;   S2 -- the registration: the corpus is registered in the (m52)
;;;         group of tool/run-tests.scm after test-m52-imp8.el, and
;;;         test/pty-driver.py holds the m52-imp3 .. m52-imp8 groups and
;;;         the 25-case total pin.  Read tracked runner files only.  S2
;;;         holds 4 checks.
;;;   S3 -- the guards: a per-group min-count guard for S1 and one for
;;;         S2, and the group-total check.  The total check is an
;;;         `ert-deftest', so its body runs after every corpus of the
;;;         group has loaded and sees them all, whatever order
;;;         tool/run-tests.scm picked.
;;;
;;; This corpus reads TRACKED files only (src/, mod/, prelude/, and the
;;; two tracked runners tool/run-tests.scm and test/pty-driver.py).  It
;;; does NOT read docs/ (docs/kb.org test-must-not-read-docs): a
;;; gitignored record can only pass or skip, so a record check proves
;;; nothing.  It does NOT run a nested m52 gate subprocess.  The
;;; in-process `ert-deftest' replaces a nested gate.
;;;
;;; A read error is a real error, never a silent pass.  An absent src/
;;; file is a real FAIL, not a pass (brief.org section 2).  Every check
;;; registers a real ERT test via imp-register-bool-as-ert-test, so the
;;; harness parses the ERT output and the exit code is correct: a
;;; princ'd FAIL with no ERT test would leave the exit code 0.

(princ "=== m52 imp-9 close-out suite ===\n")

(require 'imp-ert-report)

(defvar m52-imp9--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))

(defvar m52-imp9--registered 0
  "Total number of tracked-file checks this corpus has registered.")

(defvar m52-imp9--group nil
  "The group that `m52-imp9--check' counts into: `s1', `s2', or nil.")

(defvar m52-imp9--counts nil
  "Alist of (GROUP . COUNT) for the registered tracked-file checks.")

(defun m52-imp9--group-count (group)
  "Number of tracked-file checks registered so far in GROUP."
  (or (cdr (assq group m52-imp9--counts)) 0))

(defun m52-imp9--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
the symbol `m52-imp9-absent' when REL does not exist."
  (let ((path (expand-file-name rel m52-imp9--root)))
    (if (not (file-exists-p path))
        'm52-imp9-absent
      (with-temp-buffer
        (insert-file-contents path)
        (funcall fn)))))

(defun m52-imp9--contains-p (rel needle)
  "Non-nil when the TRACKED file REL (repo-root-relative) contains NEEDLE.
An absent file folds to nil, so `m52-imp9--check' prints FAIL: an absent
src/ file is a real error, not a pass (brief.org section 2)."
  (let ((hit (m52-imp9--with rel
               (lambda ()
                 (goto-char (point-min))
                 (search-forward needle nil t)))))
    (and (not (eq hit 'm52-imp9-absent)) (and hit t))))

(defun m52-imp9--holds-all (rel needles)
  "Non-nil when the TRACKED file REL holds every NEEDLE.  REL is read
once, so a multi-needle check does not re-read the file per needle."
  (m52-imp9--with rel
    (lambda ()
      (let ((all t))
        (dolist (needle needles)
          (goto-char (point-min))
          (unless (search-forward needle nil t) (setq all nil)))
        all))))

(defun m52-imp9--token-absent (rel needle)
  "Return t when the TRACKED file REL exists and lacks NEEDLE.  Return
the symbol `m52-imp9-absent' when REL is absent, so `m52-imp9--check'
prints FAIL.  The distinction matters: an absent src/ file must not read
as a PASS for an absence check (brief.org section 2)."
  (m52-imp9--with rel
    (lambda ()
      (goto-char (point-min))
      (not (search-forward needle nil t)))))

(defun m52-imp9--export-p (rel name)
  "Non-nil when the `#:export' form of REL (repo-root-relative) names NAME.
The search is confined to the balanced `#:export' list, so a NAME that
only appears in a comment, a body, or a `defelisp' line does not count
(brief.org section 3.1).  An absent file folds to nil."
  (let ((hit (m52-imp9--with rel
               (lambda ()
                 (goto-char (point-min))
                 (when (search-forward "#:export" nil t)
                   (skip-chars-forward " \t\n")
                   (when (looking-at "(")
                     (let ((start (point)))
                       (forward-list)
                       (let ((limit (point)))
                         (goto-char start)
                         (search-forward name limit t)))))))))
    (and (not (eq hit 'm52-imp9-absent)) (and hit t))))

(defun m52-imp9--lines (rel)
  "Count the newlines of REL the way `wc -l' does."
  (m52-imp9--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (search-forward "\n" nil t) (setq n (1+ n)))
        n))))

(defun m52-imp9--count (rel regexp)
  "Count the matches of REGEXP in REL."
  (m52-imp9--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (re-search-forward regexp nil t) (setq n (1+ n)))
        n))))

(defun m52-imp9--line-of (rel needle)
  "1-based line number of the first literal NEEDLE in REL, or nil."
  (m52-imp9--with rel
    (lambda ()
      (goto-char (point-min))
      (when (search-forward needle nil t)
        (line-number-at-pos (match-beginning 0))))))

(defun m52-imp9--count-defun-leaf (rel)
  "Count the matches of `^DEFUN (\"--tty-' in REL.  Do NOT pin the leaves
with `grep -c -- '--tty-'': that count is higher, because each leaf name
also occurs in a sibling docstring (brief.org section 3.2 row 3)."
  (m52-imp9--count rel "^DEFUN (\"--tty-"))

(defun m52-imp9--caps-rows-in-buffer ()
  "Count the M52_CAP rows of a rendered m52_caps table in the current
buffer.  Slice the lines from the `m52_caps[] =' opening to the first
line that closes the table, that is a line whose only token is `};'
with any (including zero) leading indent: the real terminator in
src/term.c is `  };' with 2 spaces of indent.  Then count the lines
that hold a leading `M52_CAP (' token.

Return a cons (ROWS . TERMINATED): ROWS is the row count, TERMINATED is
non-nil when the closing `};' was found.  Return nil when the buffer
holds no m52_caps table.  Stopping at the close is what keeps a second
M52_CAP table elsewhere in the buffer from inflating the count
(cr.org F1).  Do NOT count a sibling docstring."
  (goto-char (point-min))
  (when (re-search-forward "m52_caps\\[\\] =" nil t)
    (forward-line 1)
    (let ((rows 0) (terminated nil))
      (while (and (not terminated) (not (eobp)))
        (if (looking-at-p "^[ \t]*};")
            (setq terminated t)
          (when (looking-at-p "^[ \t]*M52_CAP (")
            (setq rows (1+ rows)))
          (forward-line 1)))
      (cons rows terminated))))

(defun m52-imp9--caps-row-count ()
  "Count the row keys of the m52_caps table in src/term.c.  See
`m52-imp9--caps-rows-in-buffer' for the slice rule.  An absent file
folds to the symbol `m52-imp9-absent', so `m52-imp9--check' prints FAIL
(brief.org section 2)."
  (m52-imp9--with "src/term.c"
    (lambda ()
      (let ((res (m52-imp9--caps-rows-in-buffer)))
        (if res (car res) 'm52-imp9-absent)))))

(defun m52-imp9--count-scm-ref ()
  "Count scm_c_public_ref over src/*.[chm] (the brief.org section 3.2
row 10 measure)."
  (let ((total 0)
        (dir (expand-file-name "src" m52-imp9--root)))
    (dolist (f (directory-files dir t "\\.[chm]\\'"))
      (setq total (+ total (or (m52-imp9--count f "scm_c_public_ref") 0))))
    total))

(defun m52-imp9--check (name ok)
  "Report and register one check on a TRACKED file.  OK is a boolean.
The count callers pass `(eql N value)': when the source file is absent
the reader returns the symbol `m52-imp9-absent', so `eql' yields nil
and this prints FAIL.  When OK is the symbol `m52-imp9-absent' itself
the file is absent, and this prints FAIL too.  Either way this
registers a real FAILING ERT test, so an absent src/ file is a real
error, not a pass: the harness parses ERT's batch output for its exit
code, so a princ'd FAIL with no ERT test would leave the exit code 0
(brief.org section 2)."
  (let* ((absent (eq ok 'm52-imp9-absent))
         (pass (and (not absent) (and ok t))))
    (if absent
        (princ (format "FAIL m52/imp9/%s (source file absent)\n" name))
      (princ (format "%s m52/imp9/%s\n" (if pass "PASS" "FAIL") name)))
    (setq m52-imp9--registered (1+ m52-imp9--registered))
    (when m52-imp9--group
      (let ((cell (assq m52-imp9--group m52-imp9--counts)))
        (if cell
            (setcdr cell (1+ (cdr cell)))
          (push (cons m52-imp9--group 1) m52-imp9--counts))))
    (imp-register-bool-as-ert-test (format "m52-imp9/%s" name) pass)))

;;; --- S1. The re-measured surface (brief.org section 3.2) ------------

;; One check per brief.org section 3.2 value row (rows 1 .. 10).  Row 7
;; fans out to one check per exported name, so S1 holds 43 checks.

(setq m52-imp9--group 's1)

;; Row 1: src/term.c lines = 6,214.
(m52-imp9--check "term.c-lines-6214"
                 (eql 6214 (m52-imp9--lines "src/term.c")))
;; Row 2: src/term.c ^DEFUN ( count = 29.
(m52-imp9--check "term.c-defun-count-29"
                 (eql 29 (m52-imp9--count "src/term.c" "^DEFUN (")))
;; Row 3: the 4 --tty-* leaf DEFUNs.  Count the DEFUN forms, not the
;; leaf tokens (each name also occurs in a sibling docstring).
(m52-imp9--check "term.c-leaf-defun-count-4"
                 (eql 4 (m52-imp9--count-defun-leaf "src/term.c")))
;; Row 4: src/term.c fwrite ( count = 10.
(m52-imp9--check "term.c-fwrite-count-10"
                 (eql 10 (m52-imp9--count "src/term.c" "fwrite (")))
;; Row 5: src/term.c scm_c_public_ref sites = 36.
(m52-imp9--check "term.c-scm-ref-36"
                 (eql 36 (m52-imp9--count "src/term.c" "scm_c_public_ref")))
;; Row 6: mod/emacs/tty-output.scm lines = 454.
(m52-imp9--check "tty-output.scm-lines-454"
                 (eql 454 (m52-imp9--lines "mod/emacs/tty-output.scm")))
;; Row 7: the 34 #:export names of the module, one check per name.
;; The 8 M54 names (tty-write-verdict, tty-termscript-copy-handle,
;; tty-tab-verdict, and the tty-out-handle accessors) come first, then the
;; 26 M52 names.
(dolist (name '("tty-emit-cap" "tty-write-bytes" "tty-flush"
                "tty-emit-seq"
                "tty-write-verdict" "tty-termscript-copy-handle"
                "tty-tab-verdict"
                "make-tty-out-handle" "tty-out-handle?"
                "tty-out-handle-bytes" "tty-out-handle-short-writes"
                "tty-out-handle-hard-errors"
                "tty-turn-on-insert-cap" "tty-turn-off-insert-cap"
                "tty-turn-off-highlight-cap" "tty-turn-on-highlight-cap"
                "tty-toggle-highlight-cap"
                "tty-ring-bell-cap" "tty-hide-cursor-cap"
                "tty-show-cursor-cap"
                "tty-background-highlight-cap" "tty-highlight-if-desired-cap"
                "tty-update-end-steps"
                "tty-set-terminal-modes-steps" "tty-reset-terminal-modes-steps"
                "tty-cursor-to-steps" "tty-raw-cursor-to-steps"
                "tty-clear-to-end-steps" "tty-clear-frame-steps"
                "tty-clear-end-of-line-steps"
                "tty-set-terminal-window-steps" "tty-set-scroll-region-steps"
                "tty-delete-glyphs-steps" "tty-ins-del-lines-steps"))
  (m52-imp9--check (format "tty-output.scm-export-%s" name)
                   (m52-imp9--export-p "mod/emacs/tty-output.scm" name)))
;; Row 8: prelude/load.scm holds (use-modules (emacs tty-output)).  Pin
;; the FORM only; brief.org section 3.2 row 8 asks for no line pin.
(m52-imp9--check "load.scm-use-modules"
                 (m52-imp9--contains-p "prelude/load.scm"
                                       "(use-modules (emacs tty-output))"))
;; Row 9: the m52_caps table of src/term.c holds 30 keys.
(m52-imp9--check "m52-caps-rows-30"
                 (eql 30 (m52-imp9--caps-row-count)))
;; Row 10: the tree-wide scm_c_public_ref count over src/*.[chm] = 260.
(m52-imp9--check "tree-wide-scm-ref-260"
                 (eql 260 (m52-imp9--count-scm-ref)))

;;; --- S2. The registration (brief.org section 3.3) -------------------

;; test/pty-driver.py is a tracked file.  It holds the GROUPS tuple and
;; the case counts.  Read it once per check, not once per name.

(setq m52-imp9--group 's2)

(m52-imp9--check "run-tests-m52-imp9"
                 (m52-imp9--contains-p "tool/run-tests.scm"
                                       "test/m52/test-m52-imp9.el"))
(m52-imp9--check "run-tests-m52-imp9-after-imp8"
                 (let ((imp8 (m52-imp9--line-of "tool/run-tests.scm"
                                                "test/m52/test-m52-imp8.el"))
                       (imp9 (m52-imp9--line-of "tool/run-tests.scm"
                                                "test/m52/test-m52-imp9.el")))
                   (and (integerp imp8) (integerp imp9) (< imp8 imp9))))
(m52-imp9--check "pty-driver-groups-m52"
                 (m52-imp9--holds-all "test/pty-driver.py"
                                      '("\"m52-imp3\"" "\"m52-imp4\""
                                        "\"m52-imp5\"" "\"m52-imp6\""
                                        "\"m52-imp7\"" "\"m52-imp8\"")))
(m52-imp9--check "pty-driver-total-25"
                 (m52-imp9--contains-p
                  "test/pty-driver.py"
                  "\"total-case-count\", len(CASES), 25"))

;;; --- S3. The guards (brief.org section 3.4) -------------------------

;; An --filter that matches no group already reports exit 0 with 0
;; tests, so a green m52 gate proves nothing until the corpus exists and
;; its checks really register.  These guards fail when the corpus body
;; is truncated or its core checks do not run.  The counts are stable
;; because every check is registered at load time.  S1 holds 43 checks;
;; S2 holds 4 checks.

(setq m52-imp9--group nil)

(m52-imp9--check "reg/min-s1-checks-43"
                 (>= (m52-imp9--group-count 's1) 43))
(m52-imp9--check "reg/min-s2-checks-4"
                 (>= (m52-imp9--group-count 's2) 4))

;;; --- The group-total check (brief.org section 3.4) ------------------

;; A nested m52 gate subprocess is replaced by an in-process
;; `ert-deftest'.  ERT runs every test after all six m52 corpora have
;; loaded, so this body sees the whole group's registered tests whatever
;; order tool/run-tests.scm loaded the files in.
;;
;; The floor is measured from a real run, not from a stale per-corpus
;; minimum.  A real run of the m52 group selects 80 ERT tests at imp-9
;; (imp-3 .. imp-8 plus imp-9, including the imp-9 caps-slice regression
;; test).  The only tests that can legitimately drop are the 8 gated m52
;; pty cases; they INFO-skip on a host with no pty and register as
;; controlled ERT skips, so the floor is the measured total minus those
;; 8, and it holds whether or not a pty exists.  (brief.org section 3.4
;; states 6; the measured count of m52 pty cases is 8: imp-3 holds 3,
;; imp-4 .. imp-8 hold 1 each.)
;;
;; This is a coarse net, not a tight bound.  The per-corpus reg/min-*
;; guards are the tight per-corpus check; this deftest only catches a
;; whole-corpus or load-order loss.  The corpus reads no docs/, so the
;; total does not depend on docs/.

(defvar m52-imp9--min-gate-total 72
  "The minimum number of ERT tests the m52 group registers: the measured
total (80) minus the 8 gated m52 pty cases (imp-3 holds 3; imp-4 ..
imp-8 hold 1 each).")

(ert-deftest m52-imp9/gate-m52-total ()
  "The m52 group registers at least its docs-independent floor."
  (should (>= (length (ert-select-tests "^m52-imp" t))
              m52-imp9--min-gate-total)))

;;; --- The caps-slice regression test (cr.org F1) --------------------

(ert-deftest m52-imp9/caps-slice-stops-at-terminator ()
  "`m52-imp9--caps-rows-in-buffer' stops at the table's closing `};'.
The real terminator is `  };' with 2 spaces of indent (src/term.c), so
the slice must accept an indented close.  A second M52_CAP table after
the close must NOT inflate the count."
  (with-temp-buffer
    (insert "static const struct m52_cap_entry m52_caps[] =\n"
            "  {\n"
            "    M52_CAP (\"a\", 1),\n"
            "    M52_CAP (\"b\", 2),\n"
            "  };\n"
            "#undef M52_CAP\n"
            "/* a later table that must not count */\n"
            "    M52_CAP (\"c\", 3),\n")
    (let ((res (m52-imp9--caps-rows-in-buffer)))
      (should (consp res))
      (should (equal 2 (car res)))
      (should (cdr res)))))

(princ (format "=== m52 imp-9 close-out suite done (%d tracked checks; s1 %d, s2 %d) ===\n"
               m52-imp9--registered
               (m52-imp9--group-count 's1)
               (m52-imp9--group-count 's2)))
