;;; test-m46-imp1.el --- M46 imp-1 audit corpus (src/filelock.c lockfile boundary).
;;;
;;; M46 imp-1 is the docs-only audit (brief.org, docs/m46-plan.org).  It
;;; changes no C and no Scheme.  It answers four questions with evidence
;;; -- the block map of the src/filelock.c OS surface, the class of each
;;; block, the module name and the leaf shape, and the A1 / A2 decision.
;;;
;;; This corpus reads files only.  It has no C dependency.  It pins:
;;;   D1 -- the base numbers of brief.org section 2, re-measured at the
;;;         M46 imp-1 base.  src/sysdep.c is 4,950 lines and 7 DEFUNs;
;;;         src/keyboard.c is 11,233 lines and 447 DEFUNs;
;;;         src/keyboard-globals.c is 490 lines; the combined keyboard
;;;         surface is 11,723 (margin 237 under the 11,960 M31 budget);
;;;         scm_c_public_ref over src/*.[chm] is 201;
;;;         mod/emacs/tty-modes.scm is 313 lines; src/callproc.c is
;;;         2,387 lines and 7 DEFUNs; and src/filelock.c is 1,216 lines
;;;         and 13 DEFUNs.  imp-2 added the eight lockfile leaves and the
;;;         guile.h include; imp-3 added the six dispatch helpers, so
;;;         the file moved from 1,171 lines / 13 DEFUNs.
;;;   D2 -- the block line facts of brief.org section 3 and the five
;;;         DEFUN lines.  These are facts in a tracked file, so a drift
;;;         is a real FAIL.  The corpus also pins the two file facts:
;;;         6 scm_c_public_ref sites and the guile.h include.
;;;   D3 -- the leaf-shape words of brief.org section 5 in
;;;         docs/m46-plan.org.
;;;   D4 -- the decision words in the gitignored records
;;;         docs/m46-plan.org and docs/kb.org.  docs/ is gitignored, so a
;;;         present-but-stale record is an INFO-skip, not a FAIL; an
;;;         absent record is also a skip.  Known limit: D3 and D4 are
;;;         advisory only -- on a fresh clone (no docs/) they register no
;;;         ERT test, so they cannot turn this gate red; the hard checks
;;;         D1, D2 and D5 do.
;;;   D5 -- the (m46) group is registered in tool/run-tests.scm, and this
;;;         corpus registers a minimum number of checks per group.  cr.org
;;;         F3: an --filter that matches no group already reports exit 0
;;;         and 0 tests, so the gate proves nothing until the corpus
;;;         exists and really runs.  A single total bound is too loose,
;;;         so the guard pins D1 and D2 separately and fails if either
;;;         group is truncated.
;;;   D6 -- the live tracker milestone.org carries no stale string: the
;;;         M46 base is 3644d4a55, imp-1 landed as d84c2498f, and the
;;;         orphaned draft hash c3da9abd3 is gone (cr.org V1 / V2).  The
;;;         tracker is untracked, so these are advisory only.
;;;
;;; Each tracked-file check is printed as a PASS/FAIL line and turned
;;; into an ERT test so the harness counts it.  A read error is a real
;;; error, never a silent pass.  The corpus holds its own copy of every
;;; number it pins (brief.org section 2 and section 3).

(princ "=== m46 imp-1 audit suite ===\n")

(require 'imp-ert-report)

(defvar m46-imp1--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))

(defvar m46-imp1--registered 0
  "Total number of tracked-file checks this corpus has registered.  D5
pins a per-group minimum, so a truncated load cannot pass the gate
with no real checks.")

(defvar m46-imp1--group nil
  "The group that `m46-imp1--check' counts into: `d1' or `d2', or nil.
D5 pins the D1 and D2 minima separately (cr.org F3).")

(defvar m46-imp1--registered-d1 0
  "Number of D1 base-number checks registered.  D5 pins a minimum.")

(defvar m46-imp1--registered-d2 0
  "Number of D2 line-fact checks registered.  D5 pins a minimum.")

(defun m46-imp1--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
the symbol `m46-imp1-absent' when REL does not exist.  docs/ is
gitignored, so a checkout without it must not crash the subprocess: an
unguarded `insert-file-contents' on an absent file would kill the
subprocess before ERT ever ran."
  (let ((path (expand-file-name rel m46-imp1--root)))
    (if (not (file-exists-p path))
        'm46-imp1-absent
      (with-temp-buffer
        (insert-file-contents path)
        (funcall fn)))))

(defun m46-imp1--contains-p (rel needle)
  "Non-nil when REL (repo-root-relative) contains NEEDLE."
  (m46-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (search-forward needle nil t))))

(defun m46-imp1--lines (rel)
  "Count the newlines of REL the way `wc -l' does."
  (m46-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (search-forward "\n" nil t) (setq n (1+ n)))
        n))))

(defun m46-imp1--count (rel regexp)
  "Count the matches of REGEXP in REL."
  (m46-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (re-search-forward regexp nil t) (setq n (1+ n)))
        n))))

(defun m46-imp1--line-of (rel needle)
  "1-based line number of the first literal NEEDLE in REL, or nil."
  (m46-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (when (search-forward needle nil t)
        (line-number-at-pos (match-beginning 0))))))

(defun m46-imp1--count-scm-ref ()
  "Count scm_c_public_ref over src/*.[chm] (the brief.org section 2 measure)."
  (let ((total 0)
        (dir (expand-file-name "src" m46-imp1--root)))
    (dolist (f (directory-files dir t "\\.[chm]\\'"))
      (setq total (+ total (or (m46-imp1--count f "scm_c_public_ref") 0))))
    total))

(defun m46-imp1--check (name ok)
  "Report and register one check on a TRACKED file.  OK is a boolean.
The D1/D2 callers pass `(eql N value)': when the source file is absent
the reader returns the symbol `m46-imp1-absent', so `eql' yields nil and
this prints FAIL.  That is intended -- an absent src/ file is a real
error, not a pass.  The `m46-imp1-absent' branch below only fires for a
caller that passes the symbol itself; D1 and D2 do not."
  (if (eq ok 'm46-imp1-absent)
      (princ (format "INFO m46/imp1/%s skipped (source file absent)\n" name))
    (progn
      (princ (format "%s m46/imp1/%s\n" (if ok "PASS" "FAIL") name))
      (setq m46-imp1--registered (1+ m46-imp1--registered))
      (cond ((eq m46-imp1--group 'd1)
             (setq m46-imp1--registered-d1 (1+ m46-imp1--registered-d1)))
            ((eq m46-imp1--group 'd2)
             (setq m46-imp1--registered-d2 (1+ m46-imp1--registered-d2))))
      (imp-register-bool-as-ert-test (format "m46-imp1/%s" name) (and ok t)))))

(defun m46-imp1--doc-check (name rel needle)
  "Report and register one check on a NON-durable record.  PASS and
register an ERT test when REL holds NEEDLE.  INFO-skip when REL is
absent OR present but stale.  docs/ is gitignored, so no commit can
carry it: a stale document is a fact of the checkout, not a code
regression, and must not turn the gate red."
  (let ((hit (m46-imp1--contains-p rel needle)))
    (if (and hit (not (eq hit 'm46-imp1-absent)))
        (progn (princ (format "PASS m46/imp1/%s\n" name))
               (imp-register-bool-as-ert-test (format "m46-imp1/%s" name) t))
      (princ (format "INFO m46/imp1/%s skipped (%s, gitignored record)\n"
                     name (if (eq hit 'm46-imp1-absent) "absent" "stale"))))))

(defun m46-imp1--doc-absent-check (name rel needle)
  "Report and register one check on a NON-durable record.  PASS and
register an ERT test when REL does NOT hold NEEDLE.  INFO-skip when REL
is absent.  This is the negative form of `m46-imp1--doc-check': it pins
that a stale string is GONE, not that a current string is present.  It is
used to guard cr.org V1 (the live tracker must not name the orphaned
draft hash)."
  (let ((hit (m46-imp1--contains-p rel needle)))
    (cond
     ((eq hit 'm46-imp1-absent)
      (princ (format "INFO m46/imp1/%s skipped (absent, gitignored record)\n" name)))
     ((not hit)
      (princ (format "PASS m46/imp1/%s\n" name))
      (imp-register-bool-as-ert-test (format "m46-imp1/%s" name) t))
     (t
      (princ (format "INFO m46/imp1/%s skipped (stale, gitignored record)\n" name))))))

;;; --- D1. The base numbers (brief.org section 2) -----------------------

(setq m46-imp1--group 'd1)

(m46-imp1--check "sysdep.c-lines-4950"
                 (eql 4950 (m46-imp1--lines "src/sysdep.c")))
(m46-imp1--check "sysdep.c-defuns-7"
                 (eql 7 (m46-imp1--count "src/sysdep.c" "^DEFUN (\"")))
(m46-imp1--check "keyboard.c-lines-11233"
                 (eql 11233 (m46-imp1--lines "src/keyboard.c")))
(m46-imp1--check "keyboard.c-defuns-447"
                 (eql 447 (m46-imp1--count "src/keyboard.c" "^DEFUN (\"")))
(m46-imp1--check "keyboard-globals.c-lines-490"
                 (eql 490 (m46-imp1--lines "src/keyboard-globals.c")))
(m46-imp1--check "combined-keyboard-surface-11723"
                 (let ((kb (m46-imp1--lines "src/keyboard.c"))
                       (kg (m46-imp1--lines "src/keyboard-globals.c")))
                   (and (eql 11233 kb)
                        (eql 490 kg)
                        (eql 11723 (+ kb kg)))))
(m46-imp1--check "margin-under-budget-237"
                 (let ((kb (m46-imp1--lines "src/keyboard.c"))
                       (kg (m46-imp1--lines "src/keyboard-globals.c")))
                   (and (integerp kb) (integerp kg)
                        (eql 237 (- 11960 (+ kb kg))))))
(m46-imp1--check "scm-c-public-ref-260"
                 (eql 260 (m46-imp1--count-scm-ref)))
(m46-imp1--check "tty-modes.scm-lines-313"
                 (eql 313 (m46-imp1--lines "mod/emacs/tty-modes.scm")))
(m46-imp1--check "callproc.c-lines-2387"
                 (eql 2387 (m46-imp1--lines "src/callproc.c")))
(m46-imp1--check "callproc.c-defuns-7"
                 (eql 7 (m46-imp1--count "src/callproc.c" "^DEFUN (\"")))
(m46-imp1--check "callproc.c-scm-ref-4"
                 (eql 4 (m46-imp1--count "src/callproc.c" "scm_c_public_ref")))
(m46-imp1--check "filelock.c-lines-1216"
                 (eql 1216 (m46-imp1--lines "src/filelock.c")))
(m46-imp1--check "filelock.c-defuns-13"
                 (eql 13 (m46-imp1--count "src/filelock.c" "^DEFUN (\"")))

;;; --- D2. The block line facts (brief.org section 3) ------------------
;;
;; The "guile.h" include (imp-2) moves every line below it by one; the
;; eight new leaves move the blocks below them by more.  imp-3 adds the
;; six dispatch helpers above lock_file_1 and deletes the lock_if_free
;; policy, so the map is not a uniform shift.  Re-measured at imp-3.

(setq m46-imp1--group 'd2)

;; the sixteen OS-surface blocks
(m46-imp1--check "get_boot_sec-def-116"
                 (eql 116 (m46-imp1--line-of
                           "src/filelock.c" "get_boot_sec (void)")))
(m46-imp1--check "rename_lock_file-def-155"
                 (eql 155 (m46-imp1--line-of
                           "src/filelock.c"
                           "rename_lock_file (char const *old, char const *new, bool force)")))
(m46-imp1--check "create_lock_file-def-198"
                 (eql 198 (m46-imp1--line-of
                           "src/filelock.c"
                           "create_lock_file (char *lfname, char *lock_info_str, bool force)")))
(m46-imp1--check "filelock_boot_sec-def-272"
                 (eql 272 (m46-imp1--line-of
                           "src/filelock.c"
                           "filelock_boot_sec (void)")))
(m46-imp1--check "lock_file_1-def-335"
                 (eql 335 (m46-imp1--line-of
                           "src/filelock.c"
                           "lock_file_1 (Lisp_Object lfname, bool force)")))
(m46-imp1--check "within_one_second-def-346"
                 (eql 346 (m46-imp1--line-of
                           "src/filelock.c"
                           "within_one_second (intmax_t a, time_t b)")))
(m46-imp1--check "read_lock_data-def-362"
                 (eql 362 (m46-imp1--line-of
                           "src/filelock.c"
                           "read_lock_data (char *lfname, char lfinfo[MAX_LFINFO + 1])")))
(m46-imp1--check "integer_prefixed-def-395"
                 (eql 395 (m46-imp1--line-of
                           "src/filelock.c"
                           "integer_prefixed (char const *s)")))
(m46-imp1--check "current_lock_owner-def-429"
                 (eql 429 (m46-imp1--line-of
                           "src/filelock.c"
                           "current_lock_owner (lock_info_type *owner, Lisp_Object lfname)")))
(m46-imp1--check "make_lock_file_name-def-554"
                 (eql 554 (m46-imp1--line-of
                           "src/filelock.c"
                           "make_lock_file_name (Lisp_Object fn)")))
(m46-imp1--check "lock_file-def-645"
                 (eql 645 (m46-imp1--line-of
                           "src/filelock.c"
                           "lock_file (Lisp_Object fn)")))
(m46-imp1--check "unlock_file-def-700"
                 (eql 700 (m46-imp1--line-of
                           "src/filelock.c"
                           "unlock_file (Lisp_Object fn)")))
(m46-imp1--check "unlock_file_handle_error-def-709"
                 (eql 709 (m46-imp1--line-of
                           "src/filelock.c"
                           "unlock_file_handle_error (Lisp_Object err)")))
(m46-imp1--check "unlock_all_files-def-1046"
                 (eql 1046 (m46-imp1--line-of
                           "src/filelock.c"
                           "unlock_all_files (void)")))
(m46-imp1--check "unlock_buffer-def-1146"
                 (eql 1146 (m46-imp1--line-of
                           "src/filelock.c"
                           "unlock_buffer (struct buffer *buffer)")))
(m46-imp1--check "syms_of_filelock-def-1196"
                 (eql 1196 (m46-imp1--line-of
                           "src/filelock.c"
                           "syms_of_filelock (void)")))

;; the five DEFUNs
(m46-imp1--check "defun-lock-file-1060"
                 (eql 1060 (m46-imp1--line-of
                           "src/filelock.c" "DEFUN (\"lock-file\"")))
(m46-imp1--check "defun-unlock-file-1083"
                 (eql 1083 (m46-imp1--line-of
                           "src/filelock.c" "DEFUN (\"unlock-file\"")))
(m46-imp1--check "defun-lock-buffer-1108"
                 (eql 1108 (m46-imp1--line-of
                           "src/filelock.c" "DEFUN (\"lock-buffer\"")))
(m46-imp1--check "defun-unlock-buffer-1127"
                 (eql 1127 (m46-imp1--line-of
                           "src/filelock.c" "DEFUN (\"unlock-buffer\"")))
(m46-imp1--check "defun-file-locked-p-1153"
                 (eql 1153 (m46-imp1--line-of
                           "src/filelock.c" "DEFUN (\"file-locked-p\"")))

;; the two file facts: eight scm_c_public_ref sites (imp-3) and the
;; guile.h include
(m46-imp1--check "filelock.c-scm-ref-6"
                 (eql 6 (m46-imp1--count "src/filelock.c" "scm_c_public_ref")))
(m46-imp1--check "filelock.c-has-guile.h"
                 (m46-imp1--contains-p "src/filelock.c" "#include \"guile.h\""))

;;; --- D3. The leaf-shape words (gitignored plan, brief.org section 5) --

;; doc-check does not register a tracked-file check, but close the D2
;; group so the D5 registration check and the guards count into no group.
(setq m46-imp1--group nil)

(m46-imp1--doc-check "plan-module-emacs-filelock"
                     "docs/m46-plan.org" "(emacs filelock)")
(m46-imp1--doc-check "plan-leaf-plain-values"
                     "docs/m46-plan.org" "plain values only")
(m46-imp1--doc-check "plan-no-struct-across"
                     "docs/m46-plan.org" "pass a struct across the OS layer")

;; cr.org F1: the class table must carry a per-block MOVES / STAYS C
;; verdict, so the movable list, the class table, and the decision agree.
(m46-imp1--doc-check "plan-verdict-moves"
                     "docs/m46-plan.org" "MOVES")
(m46-imp1--doc-check "plan-verdict-stays-c"
                     "docs/m46-plan.org" "STAYS C")

;;; --- D4. The decision words (gitignored records) ----------------------

(m46-imp1--doc-check "plan-base-3644d4a55"
                     "docs/m46-plan.org" "#+base: HEAD = 3644d4a55")
(m46-imp1--doc-check "plan-target-filelock.c"
                     "docs/m46-plan.org" "#+target: src/filelock.c")
(m46-imp1--doc-check "plan-decision-A1"
                     "docs/m46-plan.org" "Decision: A1")
(m46-imp1--doc-check "plan-parent-side-slice"
                     "docs/m46-plan.org" "parent-side")
;; cr.org F2: the kb needles must be M46-scoped.  A bare "IMP-1 LANDED"
;; and "DECISION A1" each occur 5 times in docs/kb.org (the M42 .. M46
;; nodes), so they pass while the M46 node is absent or stale.  Search
;; the M46 sentence instead.  "filelock-os-boundary" is already unique.
(m46-imp1--doc-check "kb-records-imp1-landed"
                     "docs/kb.org"
                     "IMP-1 LANDED (docs only, no C, no Scheme).  The audit is docs/m46-plan.org")
(m46-imp1--doc-check "kb-records-decision-A1"
                     "docs/kb.org"
                     "DECISION A1: the lockfile policy moves to Scheme in the new module (emacs filelock)")
(m46-imp1--doc-check "kb-layer-filelock-os-boundary"
                     "docs/kb.org" "filelock-os-boundary")
;; cr.org G1: the durable decision record needs the ** M46 node itself, so
;; pin the heading, not just its text.  An absent node is an INFO-skip.
(m46-imp1--doc-check "kb-node-M46-heading"
                     "docs/kb.org" "** M46\n  summary:")

;;; --- D6. The live tracker (milestone.org; cr.org V1 / V2) ------------
;;
;; cr.org V1: milestone.org named the orphaned draft hash c3da9abd3 (the
;; commit that the amend replaced).  cr.org V2: milestone.org carried a
;; stale base (the M45 imp-3, 1fc078fdc) while brief.org and this plan use
;; the M45 imp-4 close-out, 3644d4a55.  milestone.org is untracked, so
;; these are advisory (INFO-skip when the tracker is absent or stale), but
;; they guard the repair against a recurrence.

(m46-imp1--doc-check "tracker-base-3644d4a55"
                     "milestone.org" "#+base: HEAD = 3644d4a55")
(m46-imp1--doc-check "tracker-imp1-hash-d84c2498f"
                     "milestone.org" "landed as =d84c2498f=")
(m46-imp1--doc-absent-check "tracker-no-orphan-c3da9abd3"
                            "milestone.org" "c3da9abd3")

;;; --- D5. The group registration and the min-count guard (cr.org F3) --

(m46-imp1--check "reg/m46-group-present"
                 (m46-imp1--contains-p "tool/run-tests.scm"
                                       "test/m46/test-m46-imp1.el"))

;; cr.org F3: an --filter that matches no group already reports exit 0
;; with 0 tests, so a green m46 gate proves nothing until the corpus
;; exists and its checks really register.  These guards fail when the
;; corpus body is truncated or its core checks do not run.  The bound is
;; per group, and the counts are stable because every check is
;; registered at load time.  D1 holds 14 checks; D2 holds 23.
(m46-imp1--check "reg/min-d1-checks-14"
                 (>= m46-imp1--registered-d1 14))
(m46-imp1--check "reg/min-d2-checks-23"
                 (>= m46-imp1--registered-d2 23))

(princ (format "=== m46 imp-1 audit suite done (%d tracked checks: D1 %d, D2 %d) ===\n"
               m46-imp1--registered m46-imp1--registered-d1 m46-imp1--registered-d2))
