;;; test-m48-imp5.el --- M48 imp-5 close-out corpus (re-measure and record).
;;;
;;; M48 imp-5 is the close-out (brief.org section 1).  It changes no C
;;; and no Scheme.  It re-measures the surface, runs the gates, and
;;; records.  This corpus pins the end state against the tree, so a
;;; stale number or a missing registration fails the run.
;;;
;;; It pins:
;;;   S1 -- the surface of brief.org section 4, re-measured at HEAD:
;;;         src/term.c (5,924 lines, 29 DEFUNs (25 M48 DEFUNs plus the
;;;         4 M52 imp-3 --tty-* leaves), 29 scm_c_public_ref sites, 6
;;;         --term-* leaves, 10 FIX-20261005-guilemacs marks, the guile.h
;;;         include at :48); mod/emacs/terminal.scm (266);
;;;         the tree-wide scm_c_public_ref over src/*.[chm] (253);
;;;         src/keyboard.c (11,233 lines / 447 DEFUNs);
;;;         src/keyboard-globals.c (490); the combined keyboard surface
;;;         (11,723); the margin (237 under the 11,960 M31 budget); and
;;;         the budget itself.  The 11 checks come from the 10 value
;;;         rows of brief.org section 4: the combined-surface/margin row
;;;         yields 2 checks (surface and margin), and every other row
;;;         yields 1, so 10 rows give 11 checks in total.
;;;   S2 -- the registration: the corpus is registered in the (m48)
;;;         group of tool/run-tests.scm after test-m48-imp4.el
;;;         (brief.org section 3).  Read tool/run-tests.scm only.
;;;   S3 -- the guards: the per-group min-count guard (one for S1, one
;;;         for S2), and the group-total check.  The total check is an
;;;         `ert-deftest', so its body runs after every corpus of the
;;;         group has loaded and sees them all, whatever order
;;;         tool/run-tests.scm picked.
;;;
;;; This corpus reads TRACKED files only (src/, mod/, tool/).  It does
;;; NOT read docs/ (docs/kb.org test-must-not-read-docs): a gitignored
;;; or untracked record can only pass or skip, so a record check proves
;;; nothing.  It does NOT run a nested m48 gate subprocess.  The
;;; in-process `ert-deftest' replaces a nested gate.
;;;
;;; A read error is a real error, never a silent pass.  An absent src/
;;; file is a real error.

(princ "=== m48 imp-5 close-out suite ===\n")

(require 'imp-ert-report)

(defvar m48-imp5--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))

(defvar m48-imp5--m31-budget 11960
  "The M31 keyboard-surface budget in lines (brief.org section 4).")

(defvar m48-imp5--registered 0
  "Total number of tracked-file checks this corpus has registered.")

(defvar m48-imp5--group nil
  "The group that `m48-imp5--check' counts into: `s1', `s2', or nil.")

(defvar m48-imp5--counts nil
  "Alist of (GROUP . COUNT) for the registered tracked-file checks.")

(defun m48-imp5--group-count (group)
  "Number of tracked-file checks registered so far in GROUP."
  (or (cdr (assq group m48-imp5--counts)) 0))

(defun m48-imp5--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
the symbol `m48-imp5-absent' when REL does not exist."
  (let ((path (expand-file-name rel m48-imp5--root)))
    (if (not (file-exists-p path))
        'm48-imp5-absent
      (with-temp-buffer
        (insert-file-contents path)
        (funcall fn)))))

(defun m48-imp5--contains-p (rel needle)
  "Non-nil when REL (repo-root-relative) contains NEEDLE."
  (m48-imp5--with rel
    (lambda ()
      (goto-char (point-min))
      (search-forward needle nil t))))

(defun m48-imp5--lines (rel)
  "Count the newlines of REL the way `wc -l' does."
  (m48-imp5--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (search-forward "\n" nil t) (setq n (1+ n)))
        n))))

(defun m48-imp5--count (rel regexp)
  "Count the matches of REGEXP in REL."
  (m48-imp5--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (re-search-forward regexp nil t) (setq n (1+ n)))
        n))))

(defun m48-imp5--line-of (rel needle)
  "1-based line number of the first literal NEEDLE in REL, or nil."
  (m48-imp5--with rel
    (lambda ()
      (goto-char (point-min))
      (when (search-forward needle nil t)
        (line-number-at-pos (match-beginning 0))))))

(defun m48-imp5--count-scm-ref ()
  "Count scm_c_public_ref over src/*.[chm] (the brief.org section 4 measure)."
  (let ((total 0)
        (dir (expand-file-name "src" m48-imp5--root)))
    (dolist (f (directory-files dir t "\\.[chm]\\'"))
      (setq total (+ total (or (m48-imp5--count f "scm_c_public_ref") 0))))
    total))

(defun m48-imp5--check (name ok)
  "Report and register one check on a TRACKED file.  OK is a boolean.
An absent src/ file makes the reader return the symbol
`m48-imp5-absent'.  The absent branch prints FAIL AND registers a real
FAILING ERT test, so an absent src/ file is a real error, not a pass:
the harness parses ERT's batch output for its exit code, so a princ'd
FAIL with no ERT test would leave the exit code 0."
  (if (eq ok 'm48-imp5-absent)
      (progn
        (princ (format "FAIL m48/imp5/%s (source file absent)\n" name))
        (imp-register-bool-as-ert-test (format "m48-imp5/%s" name) nil)
        (setq m48-imp5--registered (1+ m48-imp5--registered))
        (when m48-imp5--group
          (let ((cell (assq m48-imp5--group m48-imp5--counts)))
            (if cell
                (setcdr cell (1+ (cdr cell)))
              (push (cons m48-imp5--group 1) m48-imp5--counts)))))
    (progn
      (princ (format "%s m48/imp5/%s\n" (if ok "PASS" "FAIL") name))
      (setq m48-imp5--registered (1+ m48-imp5--registered))
      (when m48-imp5--group
        (let ((cell (assq m48-imp5--group m48-imp5--counts)))
          (if cell
              (setcdr cell (1+ (cdr cell)))
            (push (cons m48-imp5--group 1) m48-imp5--counts))))
      (imp-register-bool-as-ert-test (format "m48-imp5/%s" name) (and ok t)))))

;;; --- S1. The surface (brief.org section 4) --------------------------

;; The 11 checks come from the 10 value rows of the brief.org section 4
;; table.  A multi-value row (keyboard.c lines/DEFUNs) is one check that
;; asserts every value in the row, so one row == one check == one failure
;; line; the combined-surface/margin row is the exception and yields two
;; checks (surface and margin), for 11 checks over 10 rows.

(setq m48-imp5--group 's1)

(m48-imp5--check "term.c-lines-DEFUNs-refs"
                 (let ((lines (m48-imp5--lines "src/term.c"))
                       (defuns (m48-imp5--count "src/term.c" "^DEFUN (\""))
                       (refs (m48-imp5--count "src/term.c" "scm_c_public_ref")))
                   (and (integerp lines) (eql 5924 lines)
                        (integerp defuns) (eql 29 defuns)
                        (integerp refs) (eql 29 refs))))
(m48-imp5--check "term.c-guile.h-at-48"
                 (eql 48 (m48-imp5--line-of "src/term.c" "#include \"guile.h\"")))
(m48-imp5--check "term.c-leaves-6"
                 (eql 6 (m48-imp5--count "src/term.c" "^DEFUN (\"--term-")))
(m48-imp5--check "term.c-fix-marks-10"
                 (eql 10 (m48-imp5--count "src/term.c"
                                          "FIX-20261005-guilemacs")))
(m48-imp5--check "terminal.scm-lines-266"
                 (eql 266 (m48-imp5--lines "mod/emacs/terminal.scm")))
(m48-imp5--check "tree-wide-scm-public-ref-253"
                 (eql 253 (m48-imp5--count-scm-ref)))
(m48-imp5--check "keyboard.c-lines-DEFUNs"
                 (let ((lines (m48-imp5--lines "src/keyboard.c"))
                       (defuns (m48-imp5--count "src/keyboard.c" "^DEFUN (\"")))
                   (and (integerp lines) (eql 11233 lines)
                        (integerp defuns) (eql 447 defuns))))
(m48-imp5--check "keyboard-globals.c-lines-490"
                 (eql 490 (m48-imp5--lines "src/keyboard-globals.c")))
(m48-imp5--check "combined-keyboard-surface-11723"
                 (let ((kb (m48-imp5--lines "src/keyboard.c"))
                       (kg (m48-imp5--lines "src/keyboard-globals.c")))
                   (and (integerp kb) (integerp kg)
                        (eql 11723 (+ kb kg)))))
(m48-imp5--check "keyboard-margin-237-under-budget"
                 (let ((kb (m48-imp5--lines "src/keyboard.c"))
                       (kg (m48-imp5--lines "src/keyboard-globals.c")))
                   (and (integerp kb) (integerp kg)
                        (eql 237 (- 11960 (+ kb kg))))))
(m48-imp5--check "m31-budget-11960"
                 (eql 11960 m48-imp5--m31-budget))

;;; --- S2. The corpus is registered (brief.org section 3) -------------

(setq m48-imp5--group 's2)

(m48-imp5--check "run-tests-m48-imp5"
                 (m48-imp5--contains-p "tool/run-tests.scm"
                                       "test/m48/test-m48-imp5.el"))
(m48-imp5--check "run-tests-m48-imp5-after-imp4"
                 (let ((imp4 (m48-imp5--line-of "tool/run-tests.scm"
                                                "test/m48/test-m48-imp4.el"))
                       (imp5 (m48-imp5--line-of "tool/run-tests.scm"
                                                "test/m48/test-m48-imp5.el")))
                   (and (integerp imp4) (integerp imp5) (< imp4 imp5))))

;;; --- S3. The guards (brief.org section 6) ---------------------------

;; An --filter that matches no group already reports exit 0 with 0
;; tests, so a green m48 gate proves nothing until the corpus exists and
;; its checks really register.  These guards fail when the corpus body is
;; truncated or its core checks do not run.  The counts are stable
;; because every check is registered at load time.  S1 holds 11 checks;
;; S2 holds 2 checks.

(setq m48-imp5--group nil)

(m48-imp5--check "reg/min-s1-checks-11"
                 (>= (m48-imp5--group-count 's1) 11))
(m48-imp5--check "reg/min-s2-checks-2"
                 (>= (m48-imp5--group-count 's2) 2))

;;; --- The group-total check (brief.org section 6) --------------------

;; A nested m48 gate subprocess is replaced by an in-process
;; `ert-deftest'.  ERT runs every test after all five m48 corpora have
;; loaded, so this body sees the whole group's registered tests whatever
;; order tool/run-tests.scm loaded the files in -- it randomises them, so
;; a load-time count could not do this.
;;
;; The floor is measured from a real run, not from the stale per-corpus
;; minimums.  The m48 group registers N ERT tests at imp-5 (imp-1..imp-4
;; plus imp-5).  The only tests that can legitimately drop are the gated
;; runtime probes in imp-2, imp-3 and imp-4, which register nothing when
;; no built src/emacs exists.  The floor is the measured total minus
;; those probes, so it holds whether or not the probes run.
;;
;; This is a coarse net, not a tight bound.  When the probes run the
;; group holds 14 tests above the floor, so the loss of up to 14 static
;; checks would not fail here.  The per-corpus reg/min-* guards are the
;; tight per-corpus check; this deftest only catches a whole-corpus or
;; load-order loss.  The corpus reads no docs/, so the total does not
;; depend on docs/.

(defvar m48-imp5--min-gate-total 181
  "The minimum number of ERT tests the m48 group registers.")

(ert-deftest m48-imp5/gate-m48-total ()
  "The m48 group registers at least its docs-independent floor."
  (should (>= (length (ert-select-tests "^m48-imp" t))
              m48-imp5--min-gate-total)))

(princ (format "=== m48 imp-5 close-out suite done (%d tracked checks; s1 %d, s2 %d) ===\n"
               m48-imp5--registered
               (m48-imp5--group-count 's1)
               (m48-imp5--group-count 's2)))
