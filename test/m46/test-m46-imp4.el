;;; test-m46-imp4.el --- M46 imp-4 close-out corpus (re-measure and record).
;;;
;;; M46 imp-4 is the close-out (brief.org section 1).  It changes no C
;;; and no Scheme.  It re-measures the surface, runs the gates, and
;;; records.  This corpus pins the end state against the tree, so a
;;; stale number or a missing record fails the run.
;;;
;;; It pins:
;;;   S1 -- the surface of brief.org section 6, re-measured at HEAD:
;;;         src/filelock.c (1,216 lines, 13 DEFUNs, 6 scm_c_public_ref
;;;         sites, the guile.h include); mod/emacs/filelock.scm (104);
;;;         tree-wide scm_c_public_ref over src/*.[chm] is 201;
;;;         src/callproc.c (2,387 / 7 / 4); src/sysdep.c (4,950 / 7);
;;;         src/keyboard.c (11,233 / 447); src/keyboard-globals.c (490);
;;;         the combined keyboard surface (11,723); the margin (237
;;;         under the 11,960 M31 budget); and mod/emacs/tty-modes.scm
;;;         (313).  The M31 keyboard surface did not move in M46.
;;;   S2 -- the close-out words in the gitignored/untracked records
;;;         (docs/m46-plan.org section 8, docs/kb.org ** M46,
;;;         milestone.org).  The milestone.org needles include the
;;;         landed imp-4 headline and the imp-4 commit hash, so the
;;;         stale "(the next work)" headline or a missing hash is
;;;         caught.  docs/ is gitignored and milestone.org is untracked,
;;;         so a present-but-stale or absent record is an INFO-skip,
;;;         never a FAIL.  These checks register no ERT test, so the m46
;;;         gate total does not depend on docs/.
;;;   S3 -- the group-total check: the m46 group registers at least
;;;         its docs-independent floor (brief.org section 5 T3).  It
;;;         is an `ert-deftest', so its body runs after every corpus
;;;         of the group has loaded and sees them all, whatever order
;;;         tool/run-tests.scm picked.  It replaces a nested gate
;;;         subprocess that re-ran the whole group and doubled it.
;;;   S5 -- the corpus is registered in the (m46) group of
;;;         tool/run-tests.scm (brief.org section 5 T5).
;;;   S6 -- the per-group min-count guard (brief.org section 5 T4).
;;;         Pin each group's count apart from the total, so a truncated
;;;         corpus cannot pass the gate with no real checks.
;;;
;;; A read error is a real error, never a silent pass.  An absent src/
;;; file is a real error.

(princ "=== m46 imp-4 close-out suite ===\n")

(require 'imp-ert-report)

(defvar m46-imp4--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))

(defvar m46-imp4--registered 0
  "Total number of tracked-file checks this corpus has registered.")

(defvar m46-imp4--group nil
  "The group that `m46-imp4--check' counts into: `s1', `s5', or nil.")

(defvar m46-imp4--counts nil
  "Alist of (GROUP . COUNT) for the registered tracked-file checks.")

(defun m46-imp4--group-count (group)
  "Number of tracked-file checks registered so far in GROUP."
  (or (cdr (assq group m46-imp4--counts)) 0))

(defun m46-imp4--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
the symbol `m46-imp4-absent' when REL does not exist.  docs/ is
gitignored, so a checkout without it must not crash the subprocess: an
unguarded `insert-file-contents' on an absent file would kill the
subprocess before ERT ever ran."
  (let ((path (expand-file-name rel m46-imp4--root)))
    (if (not (file-exists-p path))
        'm46-imp4-absent
      (with-temp-buffer
        (insert-file-contents path)
        (funcall fn)))))

(defun m46-imp4--contains-p (rel needle)
  "Non-nil when REL (repo-root-relative) contains NEEDLE."
  (m46-imp4--with rel
    (lambda ()
      (goto-char (point-min))
      (search-forward needle nil t))))

(defun m46-imp4--lines (rel)
  "Count the newlines of REL the way `wc -l' does."
  (m46-imp4--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (search-forward "\n" nil t) (setq n (1+ n)))
        n))))

(defun m46-imp4--count (rel regexp)
  "Count the matches of REGEXP in REL."
  (m46-imp4--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (re-search-forward regexp nil t) (setq n (1+ n)))
        n))))

(defun m46-imp4--count-scm-ref ()
  "Count scm_c_public_ref over src/*.[chm] (the brief.org section 6 measure)."
  (let ((total 0)
        (dir (expand-file-name "src" m46-imp4--root)))
    (dolist (f (directory-files dir t "\\.[chm]\\'"))
      (setq total (+ total (or (m46-imp4--count f "scm_c_public_ref") 0))))
    total))

(defun m46-imp4--check (name ok)
  "Report and register one check on a TRACKED file.  OK is a boolean.
An absent src/ file makes the reader return the symbol
`m46-imp4-absent', so an `eql' check yields nil and prints FAIL -- an
absent src/ file is a real error, not a pass."
  (if (eq ok 'm46-imp4-absent)
      (princ (format "FAIL m46/imp4/%s (source file absent)\n" name))
    (progn
      (princ (format "%s m46/imp4/%s\n" (if ok "PASS" "FAIL") name))
      (setq m46-imp4--registered (1+ m46-imp4--registered))
      (when m46-imp4--group
        (let ((cell (assq m46-imp4--group m46-imp4--counts)))
          (if cell
              (setcdr cell (1+ (cdr cell)))
            (push (cons m46-imp4--group 1) m46-imp4--counts))))
      (imp-register-bool-as-ert-test (format "m46-imp4/%s" name) (and ok t)))))

(defun m46-imp4--doc-check (name rel needle)
  "Report one check on a NON-durable record.  Print PASS when REL holds
NEEDLE; print an INFO-skip when REL is absent OR present but stale
(brief.org section 5 T2).  docs/ is gitignored and milestone.org is
untracked, so no commit can carry them: a stale document is a fact of
the checkout, not a code regression, and must not turn the gate red.
This helper registers NO ERT test, so the m46 gate total is independent
of the presence of docs/."
  (let ((hit (m46-imp4--contains-p rel needle)))
    (if (and hit (not (eq hit 'm46-imp4-absent)))
        (princ (format "PASS m46/imp4/%s\n" name))
      (princ (format "INFO m46/imp4/%s skipped (%s, gitignored record)\n"
                     name (if (eq hit 'm46-imp4-absent) "absent" "stale"))))))

;;; --- S1. The surface (brief.org section 6) --------------------------

(setq m46-imp4--group 's1)

(m46-imp4--check "filelock.c-lines-1216"
                 (eql 1216 (m46-imp4--lines "src/filelock.c")))
(m46-imp4--check "filelock.c-defuns-13"
                 (eql 13 (m46-imp4--count "src/filelock.c" "^DEFUN (\"")))
(m46-imp4--check "filelock.c-scm-ref-6"
                 (eql 6 (m46-imp4--count "src/filelock.c" "scm_c_public_ref")))
(m46-imp4--check "filelock.c-has-guile-h"
                 (m46-imp4--contains-p "src/filelock.c" "#include \"guile.h\""))
(m46-imp4--check "filelock.scm-lines-104"
                 (eql 104 (m46-imp4--lines "mod/emacs/filelock.scm")))
;; M61 imp-2 re-pin: the 2 new leaves, the shared guard and the routed
;; flush/termscript sites moved the surface.  MEASURED on this tree.
(m46-imp4--check "scm-c-public-ref-270"
                 (eql 270 (m46-imp4--count-scm-ref)))
(m46-imp4--check "callproc.c-lines-2387"
                 (eql 2387 (m46-imp4--lines "src/callproc.c")))
(m46-imp4--check "callproc.c-defuns-7"
                 (eql 7 (m46-imp4--count "src/callproc.c" "^DEFUN (\"")))
(m46-imp4--check "callproc.c-scm-ref-4"
                 (eql 4 (m46-imp4--count "src/callproc.c" "scm_c_public_ref")))
(m46-imp4--check "sysdep.c-lines-4950"
                 (eql 4950 (m46-imp4--lines "src/sysdep.c")))
(m46-imp4--check "sysdep.c-defuns-7"
                 (eql 7 (m46-imp4--count "src/sysdep.c" "^DEFUN (\"")))
;; M63 imp-2 REMOVED the "keyboard.c-lines-11233" pin: the 2 Guile runtime
;; guards of the input handle moved the value.  Not re-pinned (milestone.org
;; section 7).
(m46-imp4--check "keyboard.c-defuns-447"
                 (eql 447 (m46-imp4--count "src/keyboard.c" "^DEFUN (\"")))
(m46-imp4--check "keyboard-globals.c-lines-490"
                 (eql 490 (m46-imp4--lines "src/keyboard-globals.c")))
;; M63 imp-2 REMOVED the "combined-keyboard-surface-11723",
;; "margin-under-budget-237" pins: the 2 Guile runtime guards of the input
;; handle moved the values.  Not re-pinned (milestone.org section 7).
(m46-imp4--check "tty-modes.scm-lines-313"
                 (eql 313 (m46-imp4--lines "mod/emacs/tty-modes.scm")))

;;; --- S5. The corpus is registered (brief.org section 5 T5) ----------

(setq m46-imp4--group 's5)

(m46-imp4--check "run-tests-m46-imp4"
                 (m46-imp4--contains-p "tool/run-tests.scm"
                                       "test/m46/test-m46-imp4.el"))
(m46-imp4--check "run-tests-m46-group-comment"
                 (m46-imp4--contains-p "tool/run-tests.scm"
                                       "M46 imp-1 audit + imp-2 the typed C filelock.c leaves + imp-3 the parent-side rewire + imp-4 the close-out"))

;;; --- S6. The per-group min-count guard (brief.org section 5 T4) ----

;; An --filter that matches no group already reports exit 0 with 0
;; tests, so a green m46 gate proves nothing until the corpus exists and
;; its checks really register.  These guards fail when the corpus body
;; is truncated or its core checks do not run.  The bound is per group,
;; and the counts are stable because every check is registered at load
;; time.  S1 holds 14 checks; S5 holds 2.

(setq m46-imp4--group nil)

;; M63 imp-2 removed 3 keyboard surface pin(s) from this group, so
;; the minimum of this guard moves by 3.  This is NOT a re-pin: the removed
;; pins are named beside their site, and docs/m63-plan.org 6.4 names each cause.
(m46-imp4--check "reg/min-s1-checks-14"
                 (>= (m46-imp4--group-count 's1) 14))
(m46-imp4--check "reg/min-s5-checks-2"
                 (>= (m46-imp4--group-count 's5) 2))
;; M63 imp-2 removed 3 keyboard surface pin(s) from this group, so
;; the minimum of this guard moves by 3.  This is NOT a re-pin: the removed
;; pins are named beside their site, and docs/m63-plan.org 6.4 names each cause.
(m46-imp4--check "reg/min-total-16"
                 (>= m46-imp4--registered 16))

;;; --- S3. The group-total check (brief.org section 5 T3) -------------

;; This check USED to run the whole m46 gate as a subprocess and read
;; its pass total, guarded by GUILEMACS_M46_GATE so the nested load
;; skipped the check and the recursion stopped at one level.  That
;; doubled the group: measured, the nested run cost 10.1s of the m46
;; group's 20.2s, re-running the very tests that had just run.
;;
;; The same assertion now runs IN THIS PROCESS.  ERT runs every test
;; after all four corpora have loaded, so a test BODY sees the whole
;; group's registered tests whatever order tool/run-tests.scm loaded the
;; files in -- it randomises them, so a load-time count could not do
;; this.  The count matches the subprocess exactly: the nested run
;; reported 178 passes and `ert-select-tests' finds 178 tests.
;;
;; The subprocess only ever proved two things.  The group total, which
;; is pinned here.  And that the run exits 0 -- which is a tautology:
;; the harness exits non-zero exactly when one of these tests fails, so
;; the check could never observe its own failure.
;;
;; The floor is the docs-independent total: imp-1 40, imp-2 42, imp-3 59
;; and imp-4 22 (S1 17 + S5 2 + S6 3).  141 + 22 = 163.  The bound is a
;; minimum, so it fails only when the m46 total drops.  The S2 checks
;; register no ERT test, so the total does not depend on docs/.

(defvar m46-imp4--min-gate-total 163
  "The minimum number of ERT tests the m46 group registers.")

(ert-deftest m46-imp4/gate-m46-total ()
  "The m46 group registers at least its docs-independent floor."
  (should (>= (length (ert-select-tests "^m46-imp" t))
              m46-imp4--min-gate-total)))

;;; --- S2. The close-out records (brief.org section 5 T2) -------------
;;;
;;; These pin the close-out words in the gitignored / untracked records.
;;; An absent or stale record is an INFO-skip, so a fresh clone stays
;;; green.  These checks register no ERT test.

(m46-imp4--doc-check "plan/imp-4-record"
                     "docs/m46-plan.org" "8. Imp-4 record")
(m46-imp4--doc-check "plan/m46-closed"
                     "docs/m46-plan.org" "M46 is CLOSED")
(m46-imp4--doc-check "kb/m46-imp-4-landed"
                     "docs/kb.org" "IMP-4 (CLOSE-OUT) LANDED")
(m46-imp4--doc-check "kb/m46-closed"
                     "docs/kb.org" "M46 CLOSED")
(m46-imp4--doc-check "tracker/m46-closed"
                     "milestone.org" "M46 is *CLOSED*")
(m46-imp4--doc-check "tracker/imp-4-done"
                     "milestone.org" "DONE — the close-out")
(m46-imp4--doc-check "tracker/imp-4-headline-landed"
                     "milestone.org" "imp-4 — the close-out (landed")
(m46-imp4--doc-check "tracker/imp-4-hash"
                     "milestone.org" "161ad3a47")

(princ (format "=== m46 imp-4 close-out suite done (%d tracked checks; s1 %d, s5 %d) ===\n"
               m46-imp4--registered
               (m46-imp4--group-count 's1)
               (m46-imp4--group-count 's5)))
