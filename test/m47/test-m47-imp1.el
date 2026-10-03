;;; test-m47-imp1.el --- M47 imp-1 audit corpus (src/fileio.c file-I/O boundary).
;;;
;;; M47 imp-1 is the docs-only audit (brief.org, docs/m47-plan.org).  It
;;; changes no C and no Scheme.  It answers four questions with evidence
;;; -- the block map of the src/fileio.c OS surface, the class of each
;;; block, the module name and the leaf shape, and the A1 / A2 decision.
;;;
;;; This corpus reads files only.  It has no C dependency.  It pins:
;;;   D1 -- the base numbers of brief.org section 3, re-measured at the
;;;         M47 imp-1 base abf26c469.  src/fileio.c is 6,484 lines, 52
;;;         DEFUNs, 1 scm_c_public_ref site, and includes guile.h;
;;;         mod/emacs/fileio.scm is 36 lines;
;;;         scm_c_public_ref over src/*.[chm] is 193; src/keyboard.c is
;;;         11,233 lines and 447 DEFUNs; src/keyboard-globals.c is 490
;;;         lines; the combined keyboard surface is 11,723 (margin 237
;;;         under the 11,960 M31 budget).
;;;   D2 -- the block line facts of brief.org section 4.1 (the 32 block
;;;         definitions) and the src/fileio.c ref site (:5796), 33 checks
;;;         in all.  These are facts in a tracked file, so a drift is a
;;;         real FAIL.
;;;   D3 -- the leaf-shape words of brief.org section 4.3 in
;;;         docs/m47-plan.org.
;;;   D4 -- the decision words in the gitignored records
;;;         docs/m47-plan.org and docs/kb.org.  docs/ is gitignored, so a
;;;         present-but-stale record is an INFO-skip, not a FAIL; an
;;;         absent record is also a skip.  Known limit: D3 and D4 are
;;;         advisory only -- on a fresh clone (no docs/) they register no
;;;         ERT test, so they cannot turn this gate red; the hard checks
;;;         D1, D2 and D5 do.
;;;   D5 -- the (m47) group is registered in tool/run-tests.scm, and this
;;;         corpus registers a minimum number of checks per group.  An
;;;         --filter that matches no group already reports exit 0 and 0
;;;         tests, so the gate proves nothing until the corpus exists and
;;;         really runs.  A single total bound is too loose, so the guard
;;;         pins D1 and D2 separately and fails if either group is
;;;         truncated.
;;;   D6 -- the live tracker milestone.org carries no stale string: the
;;;         M47 base is abf26c469 and imp-1 is marked DONE.  The tracker
;;;         is untracked, so these are advisory only.
;;;
;;; Each tracked-file check is printed as a PASS/FAIL line and turned
;;; into an ERT test so the harness counts it.  A read error is a real
;;; error, never a silent pass.  The corpus holds its own copy of every
;;; number it pins (brief.org section 3 and section 4.1).

(princ "=== m47 imp-1 audit suite ===\n")

(require 'imp-ert-report)

(defvar m47-imp1--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))

(defvar m47-imp1--registered 0
  "Total number of tracked-file checks this corpus has registered.  D5
pins a per-group minimum, so a truncated load cannot pass the gate
with no real checks.")

(defvar m47-imp1--group nil
  "The group that `m47-imp1--check' counts into: `d1' or `d2', or nil.
D5 pins the D1 and D2 minima separately.")

(defvar m47-imp1--registered-d1 0
  "Number of D1 base-number checks registered.  D5 pins a minimum.")

(defvar m47-imp1--registered-d2 0
  "Number of D2 line-fact checks registered.  D5 pins a minimum.")

(defun m47-imp1--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
the symbol `m47-imp1-absent' when REL does not exist.  docs/ is
gitignored, so a checkout without it must not crash the subprocess: an
unguarded `insert-file-contents' on an absent file would kill the
subprocess before ERT ever ran."
  (let ((path (expand-file-name rel m47-imp1--root)))
    (if (not (file-exists-p path))
        'm47-imp1-absent
      (with-temp-buffer
        (insert-file-contents path)
        (funcall fn)))))

(defun m47-imp1--contains-p (rel needle)
  "Non-nil when REL (repo-root-relative) contains NEEDLE."
  (m47-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (search-forward needle nil t))))

(defun m47-imp1--tracked-p (rel needle)
  "Non-nil when the TRACKED file REL contains NEEDLE.  A missing tracked
file yields nil, so `m47-imp1--check' prints FAIL: an absent src/ file
is a real error (brief.org section 5).  Contrast `m47-imp1--contains-p',
which returns `m47-imp1-absent' so a doc-check can tell absent from
stale for a gitignored record."
  (let ((hit (m47-imp1--contains-p rel needle)))
    (and (not (eq hit 'm47-imp1-absent)) (and hit t))))

(defun m47-imp1--lines (rel)
  "Count the newlines of REL the way `wc -l' does."
  (m47-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (search-forward "\n" nil t) (setq n (1+ n)))
        n))))

(defun m47-imp1--count (rel regexp)
  "Count the matches of REGEXP in REL."
  (m47-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (re-search-forward regexp nil t) (setq n (1+ n)))
        n))))

(defun m47-imp1--line-of (rel needle)
  "1-based line number of the first literal NEEDLE in REL, or nil."
  (m47-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (when (search-forward needle nil t)
        (line-number-at-pos (match-beginning 0))))))

(defun m47-imp1--count-scm-ref ()
  "Count scm_c_public_ref over src/*.[chm] (the brief.org section 3 measure)."
  (let ((total 0)
        (dir (expand-file-name "src" m47-imp1--root)))
    (dolist (f (directory-files dir t "\\.[chm]\\'"))
      (setq total (+ total (or (m47-imp1--count f "scm_c_public_ref") 0))))
    total))

(defun m47-imp1--check (name ok)
  "Report and register one check on a TRACKED file.  OK is a boolean.
The D1/D2 callers pass `(eql N value)': when the source file is absent
the reader returns the symbol `m47-imp1-absent', so `eql' yields nil and
this prints FAIL.  The string-test callers use `m47-imp1--tracked-p',
which folds an absent file to nil for the same reason, so this prints
FAIL too.  An absent src/ file is a real error, not a pass.  The
`m47-imp1-absent' branch below is thus a safety net: no tracked caller
passes the raw symbol to reach it."
  (if (eq ok 'm47-imp1-absent)
      (princ (format "INFO m47/imp1/%s skipped (source file absent)\n" name))
    (progn
      (princ (format "%s m47/imp1/%s\n" (if ok "PASS" "FAIL") name))
      (setq m47-imp1--registered (1+ m47-imp1--registered))
      (cond ((eq m47-imp1--group 'd1)
             (setq m47-imp1--registered-d1 (1+ m47-imp1--registered-d1)))
            ((eq m47-imp1--group 'd2)
             (setq m47-imp1--registered-d2 (1+ m47-imp1--registered-d2))))
      (imp-register-bool-as-ert-test (format "m47-imp1/%s" name) (and ok t)))))

(defun m47-imp1--doc-check (name rel needle)
  "Report and register one check on a NON-durable record.  PASS and
register an ERT test when REL holds NEEDLE.  INFO-skip when REL is
absent OR present but stale.  docs/ is gitignored, so no commit can
carry it: a stale document is a fact of the checkout, not a code
regression, and must not turn the gate red."
  (let ((hit (m47-imp1--contains-p rel needle)))
    (if (and hit (not (eq hit 'm47-imp1-absent)))
        (progn (princ (format "PASS m47/imp1/%s\n" name))
               (imp-register-bool-as-ert-test (format "m47-imp1/%s" name) t))
      (princ (format "INFO m47/imp1/%s skipped (%s, gitignored record)\n"
                     name (if (eq hit 'm47-imp1-absent) "absent" "stale"))))))

(defun m47-imp1--doc-absent-check (name rel needle)
  "Report and register one check on a NON-durable record.  PASS and
register an ERT test when REL does NOT hold NEEDLE.  INFO-skip when REL
is absent.  This is the negative form of `m47-imp1--doc-check': it pins
that a stale string is GONE, not that a current string is present."
  (let ((hit (m47-imp1--contains-p rel needle)))
    (cond
     ((eq hit 'm47-imp1-absent)
      (princ (format "INFO m47/imp1/%s skipped (absent, gitignored record)\n" name)))
     ((not hit)
      (princ (format "PASS m47/imp1/%s\n" name))
      (imp-register-bool-as-ert-test (format "m47-imp1/%s" name) t))
     (t
      (princ (format "INFO m47/imp1/%s skipped (stale, gitignored record)\n" name))))))

;;; --- D1. The base numbers (brief.org section 3) -----------------------

(setq m47-imp1--group 'd1)

(m47-imp1--check "fileio.c-lines-6484"
                 (eql 6484 (m47-imp1--lines "src/fileio.c")))
(m47-imp1--check "fileio.c-defuns-52"
                 (eql 52 (m47-imp1--count "src/fileio.c" "^DEFUN (\"")))
(m47-imp1--check "fileio.c-scm-ref-1"
                 (eql 1 (m47-imp1--count "src/fileio.c" "scm_c_public_ref")))
(m47-imp1--check "fileio.c-has-guile.h"
                 (m47-imp1--tracked-p "src/fileio.c" "#include \"guile.h\""))
(m47-imp1--check "fileio.scm-lines-36"
                 (eql 36 (m47-imp1--lines "mod/emacs/fileio.scm")))
(m47-imp1--check "scm-c-public-ref-193"
                 (eql 193 (m47-imp1--count-scm-ref)))
(m47-imp1--check "keyboard.c-lines-11233"
                 (eql 11233 (m47-imp1--lines "src/keyboard.c")))
(m47-imp1--check "keyboard.c-defuns-447"
                 (eql 447 (m47-imp1--count "src/keyboard.c" "^DEFUN (\"")))
(m47-imp1--check "keyboard-globals.c-lines-490"
                 (eql 490 (m47-imp1--lines "src/keyboard-globals.c")))
(m47-imp1--check "combined-keyboard-surface-11723"
                 (let ((kb (m47-imp1--lines "src/keyboard.c"))
                       (kg (m47-imp1--lines "src/keyboard-globals.c")))
                   (and (eql 11233 kb)
                        (eql 490 kg)
                        (eql 11723 (+ kb kg)))))
(m47-imp1--check "margin-under-budget-237"
                 (let ((kb (m47-imp1--lines "src/keyboard.c"))
                       (kg (m47-imp1--lines "src/keyboard-globals.c")))
                   (and (integerp kb) (integerp kg)
                        (eql 237 (- 11960 (+ kb kg))))))

;;; --- D2. The block line facts (brief.org section 4.1) ----------------
;;
;; The block definitions of src/fileio.c are the 52 DEFUN lines.  The
;; "guile.h" include and each new leaf move every line below them, so a
;; later imp re-pins this map.

(setq m47-imp1--group 'd2)

;; G1 -- the file-name / path policy
(m47-imp1--check "find-file-name-handler-def-391"
                 (eql 391 (m47-imp1--line-of
                           "src/fileio.c" "DEFUN (\"find-file-name-handler\"")))
(m47-imp1--check "file-name-directory-def-452"
                 (eql 452 (m47-imp1--line-of
                           "src/fileio.c" "DEFUN (\"file-name-directory\"")))
(m47-imp1--check "file-name-nondirectory-def-561"
                 (eql 561 (m47-imp1--line-of
                           "src/fileio.c" "DEFUN (\"file-name-nondirectory\"")))
(m47-imp1--check "file-name-as-directory-def-667"
                 (eql 667 (m47-imp1--line-of
                           "src/fileio.c" "DEFUN (\"file-name-as-directory\"")))
(m47-imp1--check "directory-file-name-def-760"
                 (eql 760 (m47-imp1--line-of
                           "src/fileio.c" "DEFUN (\"directory-file-name\"")))
(m47-imp1--check "file-name-concat-def-871"
                 (eql 871 (m47-imp1--line-of
                           "src/fileio.c" "DEFUN (\"file-name-concat\"")))
(m47-imp1--check "expand-file-name-def-1015"
                 (eql 1015 (m47-imp1--line-of
                            "src/fileio.c" "DEFUN (\"expand-file-name\"")))
(m47-imp1--check "substitute-in-file-name-def-1594"
                 (eql 1594 (m47-imp1--line-of
                            "src/fileio.c" "DEFUN (\"substitute-in-file-name\"")))

;; G2 -- the OS-query predicate policy
(m47-imp1--check "file-exists-p-def-2568"
                 (eql 2568 (m47-imp1--line-of
                            "src/fileio.c" "DEFUN (\"file-exists-p\"")))
(m47-imp1--check "file-executable-p-def-2580"
                 (eql 2580 (m47-imp1--line-of
                            "src/fileio.c" "DEFUN (\"file-executable-p\"")))
(m47-imp1--check "file-readable-p-def-2590"
                 (eql 2590 (m47-imp1--line-of
                            "src/fileio.c" "DEFUN (\"file-readable-p\"")))
(m47-imp1--check "file-writable-p-def-2598"
                 (eql 2598 (m47-imp1--line-of
                            "src/fileio.c" "DEFUN (\"file-writable-p\"")))
(m47-imp1--check "access-file-def-2636"
                 (eql 2636 (m47-imp1--line-of
                            "src/fileio.c" "DEFUN (\"access-file\"")))
(m47-imp1--check "file-symlink-p-def-2720"
                 (eql 2720 (m47-imp1--line-of
                            "src/fileio.c" "DEFUN (\"file-symlink-p\"")))
(m47-imp1--check "file-directory-p-def-2743"
                 (eql 2743 (m47-imp1--line-of
                            "src/fileio.c" "DEFUN (\"file-directory-p\"")))
(m47-imp1--check "file-regular-p-def-2917"
                 (eql 2917 (m47-imp1--line-of
                            "src/fileio.c" "DEFUN (\"file-regular-p\"")))
(m47-imp1--check "file-modes-def-3207"
                 (eql 3207 (m47-imp1--line-of
                            "src/fileio.c" "DEFUN (\"file-modes\"")))
(m47-imp1--check "file-newer-than-file-p-def-3356"
                 (eql 3356 (m47-imp1--line-of
                            "src/fileio.c" "DEFUN (\"file-newer-than-file-p\"")))
(m47-imp1--check "file-system-info-def-6119"
                 (eql 6119 (m47-imp1--line-of
                            "src/fileio.c" "DEFUN (\"file-system-info\"")))

;; G3 -- the copy / rename / link / delete policy
(m47-imp1--check "copy-file-def-1784"
                 (eql 1784 (m47-imp1--line-of
                            "src/fileio.c" "DEFUN (\"copy-file\"")))
(m47-imp1--check "make-directory-internal-def-2113"
                 (eql 2113 (m47-imp1--line-of
                            "src/fileio.c" "DEFUN (\"make-directory-internal\"")))
(m47-imp1--check "delete-directory-internal-def-2134"
                 (eql 2134 (m47-imp1--line-of
                            "src/fileio.c" "DEFUN (\"delete-directory-internal\"")))
(m47-imp1--check "delete-file-internal-def-2153"
                 (eql 2153 (m47-imp1--line-of
                            "src/fileio.c" "DEFUN (\"delete-file-internal\"")))
(m47-imp1--check "rename-file-def-2275"
                 (eql 2275 (m47-imp1--line-of
                            "src/fileio.c" "DEFUN (\"rename-file\"")))
(m47-imp1--check "add-name-to-file-def-2403"
                 (eql 2403 (m47-imp1--line-of
                            "src/fileio.c" "DEFUN (\"add-name-to-file\"")))
(m47-imp1--check "make-symbolic-link-def-2459"
                 (eql 2459 (m47-imp1--line-of
                            "src/fileio.c" "DEFUN (\"make-symbolic-link\"")))

;; the large blocks (STAYS C)
(m47-imp1--check "insert-file-contents-def-3602"
                 (eql 3602 (m47-imp1--line-of
                            "src/fileio.c" "DEFUN (\"insert-file-contents\"")))
(m47-imp1--check "write-region-def-4926"
                 (eql 4926 (m47-imp1--line-of
                            "src/fileio.c" "DEFUN (\"write-region\"")))
(m47-imp1--check "do-auto-save-def-5800"
                 (eql 5800 (m47-imp1--line-of
                            "src/fileio.c" "DEFUN (\"do-auto-save\"")))

;; the modtime group (STAYS C)
(m47-imp1--check "verify-visited-file-modtime-def-5592"
                 (eql 5592 (m47-imp1--line-of
                            "src/fileio.c" "DEFUN (\"verify-visited-file-modtime\"")))
(m47-imp1--check "visited-file-modtime-def-5636"
                 (eql 5636 (m47-imp1--line-of
                            "src/fileio.c" "DEFUN (\"visited-file-modtime\"")))
(m47-imp1--check "set-visited-file-modtime-def-5648"
                 (eql 5648 (m47-imp1--line-of
                            "src/fileio.c" "DEFUN (\"set-visited-file-modtime\"")))

;; the ref site: the one scm_c_public_ref site sits inside do-auto-save
(m47-imp1--check "fileio.c-ref-site-5796"
                 (eql 5796 (m47-imp1--line-of
                            "src/fileio.c" "scm_c_public_ref (\"emacs fileio\"")))

;;; --- D3. The leaf-shape words (gitignored plan, brief.org section 4.3) --

;; doc-check does not register a tracked-file check, but close the D2
;; group so the D5 registration check and the guards count into no group.
(setq m47-imp1--group nil)

(m47-imp1--doc-check "plan-module-emacs-fileio"
                     "docs/m47-plan.org" "(emacs fileio)")
(m47-imp1--doc-check "plan-leaf-plain-values"
                     "docs/m47-plan.org" "plain values only")
(m47-imp1--doc-check "plan-no-struct-across"
                     "docs/m47-plan.org" "Do not pass a struct across the OS")
;; the class table must carry a per-block MOVES / STAYS C verdict, so the
;; movable list, the class table, and the decision agree.
(m47-imp1--doc-check "plan-verdict-moves"
                     "docs/m47-plan.org" "MOVES")
(m47-imp1--doc-check "plan-verdict-stays-c"
                     "docs/m47-plan.org" "STAYS C")

;;; --- D4. The decision words (gitignored records) ----------------------

(m47-imp1--doc-check "plan-base-abf26c469"
                     "docs/m47-plan.org" "#+base: HEAD = abf26c469")
(m47-imp1--doc-check "plan-target-fileio.c"
                     "docs/m47-plan.org" "#+target: src/fileio.c")
(m47-imp1--doc-check "plan-decision-A1"
                     "docs/m47-plan.org" "Decision: A1")
(m47-imp1--doc-check "plan-parent-side-slice"
                     "docs/m47-plan.org" "parent-side")
;; the kb needles must be M47-scoped.  A bare "IMP-1 LANDED" and
;; "DECISION A1" each occur several times in docs/kb.org (the M42 .. M46
;; nodes), so they pass while the M47 node is absent or stale.  Search
;; the M47 sentence instead.  "fileio-os-boundary" is already unique.
(m47-imp1--doc-check "kb-records-imp1-landed"
                     "docs/kb.org"
                     "IMP-1 LANDED (docs only, no C, no Scheme).  The audit is docs/m47-plan.org")
(m47-imp1--doc-check "kb-records-decision-A1"
                     "docs/kb.org"
                     "DECISION A1: the src/fileio.c file-I/O policy moves to Scheme in the existing module (emacs fileio)")
(m47-imp1--doc-check "kb-layer-fileio-os-boundary"
                     "docs/kb.org" "fileio-os-boundary")
;; the durable decision record needs the ** M47 node itself, so pin the
;; heading, not just its text.  An absent node is an INFO-skip.
(m47-imp1--doc-check "kb-node-M47-heading"
                     "docs/kb.org" "** M47\n  summary:")

;;; --- D6. The live tracker (milestone.org) ----------------------------
;;
;; milestone.org is untracked, so these are advisory (INFO-skip when the
;; tracker is absent or stale), but they guard the repair against a
;; recurrence.

(m47-imp1--doc-check "tracker-base-abf26c469"
                     "milestone.org" "#+base: HEAD = abf26c469")
(m47-imp1--doc-check "tracker-imp1-done"
                     "milestone.org" "imp-1 is DONE")
(m47-imp1--doc-absent-check "tracker-no-stale-M46-open"
                            "milestone.org" "No imp has landed yet")

;;; --- D5. The group registration and the min-count guard --------------

(m47-imp1--check "reg/m47-group-present"
                 (m47-imp1--tracked-p "tool/run-tests.scm"
                                      "test/m47/test-m47-imp1.el"))
;; `m47-imp1--tracked-p' must fold an absent tracked file to nil, so that
;; `m47-imp1--check' prints FAIL for it (brief.org section 5: an absent
;; src/ file is a real error).  This pins the F3 repair: the string-test
;; callers must not leak the `m47-imp1-absent' symbol into the skip
;; branch.  A non-existent path stands in for an absent tracked file.
(m47-imp1--check "reg/absent-tracked-file-fails"
                 (null (m47-imp1--tracked-p "src/m47-imp1-no-such-file.c"
                                            "needle")))

;; An --filter that matches no group already reports exit 0 with 0 tests,
;; so a green m47 gate proves nothing until the corpus exists and its
;; checks really register.  These guards fail when the corpus body is
;; truncated or its core checks do not run.  The bound is per group, and
;; the counts are stable because every check is registered at load time.
;; D1 holds 11 checks; D2 holds 33.
(m47-imp1--check "reg/min-d1-checks-11"
                 (>= m47-imp1--registered-d1 11))
(m47-imp1--check "reg/min-d2-checks-33"
                 (>= m47-imp1--registered-d2 33))

(princ (format "=== m47 imp-1 audit suite done (%d tracked checks: D1 %d, D2 %d) ===\n"
               m47-imp1--registered m47-imp1--registered-d1 m47-imp1--registered-d2))
