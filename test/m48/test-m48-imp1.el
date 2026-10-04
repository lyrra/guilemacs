;;; test-m48-imp1.el --- M48 imp-1 audit corpus (src/term.c TTY terminal boundary).
;;;
;;; M48 imp-1 is the docs-only audit (brief.org, docs/m48-plan.org).  It
;;; changes no C and no Scheme.  It answers four questions with evidence
;;; -- the block map of the src/term.c TTY surface, the class of each
;;; block, the module name and the leaf shape, and the A1 / A2 decision.
;;;
;;; This corpus reads files only.  It has no C dependency.  It pins:
;;;   D1 -- the base numbers of brief.org section 3.  src/term.c is
;;;         5,059 lines, 19 DEFUNs, 3 scm_c_public_ref sites, and
;;;         includes guile.h; mod/emacs/terminal.scm is 134 lines;
;;;         scm_c_public_ref over src/*.[chm] is 219; src/keyboard.c is
;;;         11,233 lines and 447 DEFUNs; src/keyboard-globals.c is 490
;;;         lines; the combined keyboard surface is 11,723 (margin 237
;;;         under the 11,960 M31 budget).
;;;   D2 -- the block line facts of brief.org section 4 (the 19 block
;;;         definitions) and the three (emacs terminal) ref sites
;;;         (:3325, :3335, :3634), 22 checks in all.  These are facts in
;;;         a tracked file, so a drift is a real FAIL.
;;;   D3 -- the leaf-shape words of brief.org section 6 in
;;;         docs/m48-plan.org.
;;;   D4 -- the decision words in the gitignored records
;;;         docs/m48-plan.org and docs/kb.org.  docs/ is gitignored, so a
;;;         present-but-stale record is an INFO-skip, not a FAIL; an
;;;         absent record is also a skip.  Known limit: D3 and D4 are
;;;         advisory only -- on a fresh clone (no docs/) they register no
;;;         ERT test, so they cannot turn this gate red; the hard checks
;;;         D1, D2 and D5 do.
;;;   D5 -- the (m48) group is registered in tool/run-tests.scm, and this
;;;         corpus registers a minimum number of checks per group.  An
;;;         --filter that matches no group already reports exit 0 and 0
;;;         tests, so the gate proves nothing until the corpus exists and
;;;         really runs.  A single total bound is too loose, so the guard
;;;         pins D1 and D2 separately and fails if either group is
;;;         truncated.
;;;   D6 -- the live tracker milestone.org carries no stale string: the
;;;         M48 base is 18a7e3372 and imp-1 is marked DONE.  The tracker
;;;         is untracked, so these are advisory only.
;;;
;;; Each tracked-file check is printed as a PASS/FAIL line and turned
;;; into an ERT test so the harness counts it.  A read error is a real
;;; error, never a silent pass.  The corpus holds its own copy of every
;;; number it pins (brief.org section 3 and section 4).

(princ "=== m48 imp-1 audit suite ===\n")

(require 'imp-ert-report)

(defvar m48-imp1--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))

(defvar m48-imp1--registered 0
  "Total number of tracked-file checks this corpus has registered.  D5
pins a per-group minimum, so a truncated load cannot pass the gate
with no real checks.")

(defvar m48-imp1--group nil
  "The group that `m48-imp1--check' counts into: `d1' or `d2', or nil.
D5 pins the D1 and D2 minima separately.")

(defvar m48-imp1--registered-d1 0
  "Number of D1 base-number checks registered.  D5 pins a minimum.")

(defvar m48-imp1--registered-d2 0
  "Number of D2 line-fact checks registered.  D5 pins a minimum.")

(defun m48-imp1--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
the symbol `m48-imp1-absent' when REL does not exist.  docs/ is
gitignored, so a checkout without it must not crash the subprocess: an
unguarded `insert-file-contents' on an absent file would kill the
subprocess before ERT ever ran."
  (let ((path (expand-file-name rel m48-imp1--root)))
    (if (not (file-exists-p path))
        'm48-imp1-absent
      (with-temp-buffer
        (insert-file-contents path)
        (funcall fn)))))

(defun m48-imp1--contains-p (rel needle)
  "Non-nil when REL (repo-root-relative) contains NEEDLE."
  (m48-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (search-forward needle nil t))))

(defun m48-imp1--tracked-p (rel needle)
  "Non-nil when the TRACKED file REL contains NEEDLE.  A missing tracked
file yields nil, so `m48-imp1--check' prints FAIL: an absent src/ file
is a real error (brief.org section 12).  Contrast `m48-imp1--contains-p',
which returns `m48-imp1-absent' so a doc-check can tell absent from
stale for a gitignored record."
  (let ((hit (m48-imp1--contains-p rel needle)))
    (and (not (eq hit 'm48-imp1-absent)) (and hit t))))

(defun m48-imp1--lines (rel)
  "Count the newlines of REL the way `wc -l' does."
  (m48-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (search-forward "\n" nil t) (setq n (1+ n)))
        n))))

(defun m48-imp1--count (rel regexp)
  "Count the matches of REGEXP in REL."
  (m48-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (re-search-forward regexp nil t) (setq n (1+ n)))
        n))))

(defun m48-imp1--line-of (rel needle)
  "1-based line number of the first literal NEEDLE in REL, or nil."
  (m48-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (when (search-forward needle nil t)
        (line-number-at-pos (match-beginning 0))))))

(defun m48-imp1--count-scm-ref ()
  "Count scm_c_public_ref over src/*.[chm] (the brief.org section 3 measure)."
  (let ((total 0)
        (dir (expand-file-name "src" m48-imp1--root)))
    (dolist (f (directory-files dir t "\\.[chm]\\'"))
      (setq total (+ total (or (m48-imp1--count f "scm_c_public_ref") 0))))
    total))

(defun m48-imp1--check (name ok)
  "Report and register one check on a TRACKED file.  OK is a boolean.
The D1/D2 callers pass `(eql N value)': when the source file is absent
the reader returns the symbol `m48-imp1-absent', so `eql' yields nil and
this prints FAIL.  The string-test callers use `m48-imp1--tracked-p',
which folds an absent file to nil for the same reason, so this prints
FAIL too.  An absent src/ file is a real error, not a pass.  The
`m48-imp1-absent' branch below is thus a safety net: no tracked caller
passes the raw symbol to reach it."
  (if (eq ok 'm48-imp1-absent)
      (princ (format "INFO m48/imp1/%s skipped (source file absent)\n" name))
    (progn
      (princ (format "%s m48/imp1/%s\n" (if ok "PASS" "FAIL") name))
      (setq m48-imp1--registered (1+ m48-imp1--registered))
      (cond ((eq m48-imp1--group 'd1)
             (setq m48-imp1--registered-d1 (1+ m48-imp1--registered-d1)))
            ((eq m48-imp1--group 'd2)
             (setq m48-imp1--registered-d2 (1+ m48-imp1--registered-d2))))
      (imp-register-bool-as-ert-test (format "m48-imp1/%s" name) (and ok t)))))

(defun m48-imp1--doc-check (name rel needle)
  "Report and register one check on a NON-durable record.  PASS and
register an ERT test when REL holds NEEDLE.  INFO-skip when REL is
absent OR present but stale.  docs/ is gitignored, so no commit can
carry it: a stale document is a fact of the checkout, not a code
regression, and must not turn the gate red."
  (let ((hit (m48-imp1--contains-p rel needle)))
    (if (and hit (not (eq hit 'm48-imp1-absent)))
        (progn (princ (format "PASS m48/imp1/%s\n" name))
               (imp-register-bool-as-ert-test (format "m48-imp1/%s" name) t))
      (princ (format "INFO m48/imp1/%s skipped (%s, gitignored record)\n"
                     name (if (eq hit 'm48-imp1-absent) "absent" "stale"))))))

(defun m48-imp1--doc-absent-check (name rel needle)
  "Report and register one check on a NON-durable record.  PASS and
register an ERT test when REL does NOT hold NEEDLE.  INFO-skip when REL
is absent.  This is the negative form of `m48-imp1--doc-check': it pins
that a stale string is GONE, not that a current string is present."
  (let ((hit (m48-imp1--contains-p rel needle)))
    (cond
     ((eq hit 'm48-imp1-absent)
      (princ (format "INFO m48/imp1/%s skipped (absent, gitignored record)\n" name)))
     ((not hit)
      (princ (format "PASS m48/imp1/%s\n" name))
      (imp-register-bool-as-ert-test (format "m48-imp1/%s" name) t))
     (t
      (princ (format "INFO m48/imp1/%s skipped (stale, gitignored record)\n" name))))))

;;; --- D1. The base numbers (brief.org section 3) -----------------------

(setq m48-imp1--group 'd1)

(m48-imp1--check "term.c-lines-5059"
                 (eql 5059 (m48-imp1--lines "src/term.c")))
(m48-imp1--check "term.c-defuns-19"
                 (eql 19 (m48-imp1--count "src/term.c" "^DEFUN (\"")))
(m48-imp1--check "term.c-scm-ref-3"
                 (eql 3 (m48-imp1--count "src/term.c" "scm_c_public_ref")))
(m48-imp1--check "term.c-has-guile.h"
                 (m48-imp1--tracked-p "src/term.c" "#include \"guile.h\""))
(m48-imp1--check "terminal.scm-lines-134"
                 (eql 134 (m48-imp1--lines "mod/emacs/terminal.scm")))
(m48-imp1--check "scm-c-public-ref-219"
                 (eql 219 (m48-imp1--count-scm-ref)))
(m48-imp1--check "keyboard.c-lines-11233"
                 (eql 11233 (m48-imp1--lines "src/keyboard.c")))
(m48-imp1--check "keyboard.c-defuns-447"
                 (eql 447 (m48-imp1--count "src/keyboard.c" "^DEFUN (\"")))
(m48-imp1--check "keyboard-globals.c-lines-490"
                 (eql 490 (m48-imp1--lines "src/keyboard-globals.c")))
(m48-imp1--check "combined-keyboard-surface-11723"
                 (let ((kb (m48-imp1--lines "src/keyboard.c"))
                       (kg (m48-imp1--lines "src/keyboard-globals.c")))
                   (and (eql 11233 kb)
                        (eql 490 kg)
                        (eql 11723 (+ kb kg)))))
(m48-imp1--check "margin-under-budget-237"
                 (let ((kb (m48-imp1--lines "src/keyboard.c"))
                       (kg (m48-imp1--lines "src/keyboard-globals.c")))
                   (and (integerp kb) (integerp kg)
                        (eql 237 (- 11960 (+ kb kg))))))

;;; --- D2. The block line facts (brief.org section 4) ------------------
;;
;; The block definitions of src/term.c are the 19 DEFUN lines.  The
;; "guile.h" include and each new leaf move every line below them, so a
;; later imp re-pins this map.

(setq m48-imp1--group 'd2)

(m48-imp1--check "tty-display-color-p-def-2148"
                 (eql 2148 (m48-imp1--line-of
                 "src/term.c" "DEFUN (\"tty-display-color-p\"")))
(m48-imp1--check "tty-display-color-cells-def-2163"
                 (eql 2163 (m48-imp1--line-of
                 "src/term.c" "DEFUN (\"tty-display-color-cells\"")))
(m48-imp1--check "tty-type-def-2292"
                 (eql 2292 (m48-imp1--line-of
                 "src/term.c" "DEFUN (\"tty-type\"")))
(m48-imp1--check "controlling-tty-p-def-2305"
                 (eql 2305 (m48-imp1--line-of
                 "src/term.c" "DEFUN (\"controlling-tty-p\"")))
(m48-imp1--check "tty-no-underline-def-2318"
                 (eql 2318 (m48-imp1--line-of
                 "src/term.c" "DEFUN (\"tty-no-underline\"")))
(m48-imp1--check "tty-top-frame-def-2336"
                 (eql 2336 (m48-imp1--line-of
                 "src/term.c" "DEFUN (\"tty-top-frame\"")))
(m48-imp1--check "suspend-tty-def-2353"
                 (eql 2353 (m48-imp1--line-of
                 "src/term.c" "DEFUN (\"suspend-tty\"")))
(m48-imp1--check "resume-tty-def-2422"
                 (eql 2422 (m48-imp1--line-of
                 "src/term.c" "DEFUN (\"resume-tty\"")))
(m48-imp1--check "tty--set-output-buffer-size-def-2515"
                 (eql 2515 (m48-imp1--line-of
                 "src/term.c" "DEFUN (\"tty--set-output-buffer-size\"")))
(m48-imp1--check "tty--output-buffer-size-def-2537"
                 (eql 2537 (m48-imp1--line-of
                 "src/term.c" "DEFUN (\"tty--output-buffer-size\"")))
(m48-imp1--check "tty-frame-at-def-2616"
                 (eql 2616 (m48-imp1--line-of
                 "src/term.c" "DEFUN (\"tty-frame-at\"")))
(m48-imp1--check "gpm-mouse-start-def-2807"
                 (eql 2807 (m48-imp1--line-of
                 "src/term.c" "DEFUN (\"gpm-mouse-start\"")))
(m48-imp1--check "gpm-mouse-stop-def-2856"
                 (eql 2856 (m48-imp1--line-of
                 "src/term.c" "DEFUN (\"gpm-mouse-stop\"")))
(m48-imp1--check "tty-frame-geometry-def-4894"
                 (eql 4894 (m48-imp1--line-of
                 "src/term.c" "DEFUN (\"tty-frame-geometry\"")))
(m48-imp1--check "tty-frame-edges-def-4902"
                 (eql 4902 (m48-imp1--line-of
                 "src/term.c" "DEFUN (\"tty-frame-edges\"")))
(m48-imp1--check "tty-frame-list-z-order-def-4912"
                 (eql 4912 (m48-imp1--line-of
                 "src/term.c" "DEFUN (\"tty-frame-list-z-order\"")))
(m48-imp1--check "tty-frame-restack-def-4923"
                 (eql 4923 (m48-imp1--line-of
                 "src/term.c" "DEFUN (\"tty-frame-restack\"")))
(m48-imp1--check "tty-display-pixel-width-def-4963"
                 (eql 4963 (m48-imp1--line-of
                 "src/term.c" "DEFUN (\"tty-display-pixel-width\"")))
(m48-imp1--check "tty-display-pixel-height-def-4974"
                 (eql 4974 (m48-imp1--line-of
                 "src/term.c" "DEFUN (\"tty-display-pixel-height\"")))

;; the three ref sites: the M33 imp-1 (emacs terminal) consumers
(m48-imp1--check "term.c-ref-tty-menu-clear-help-3325"
                 (eql 3325 (m48-imp1--line-of
                 "src/term.c" "scm_c_public_ref (\"emacs terminal\", \"tty-menu-clear-help!\"")))
(m48-imp1--check "term.c-ref-tty-menu-discard-mouse-events-3335"
                 (eql 3335 (m48-imp1--line-of
                 "src/term.c" "scm_c_public_ref (\"emacs terminal\", \"tty-menu-discard-mouse-events!\"")))
(m48-imp1--check "term.c-ref-tty-menu-help-callback-3634"
                 (eql 3634 (m48-imp1--line-of
                 "src/term.c" "scm_c_public_ref (\"emacs terminal\", \"tty-menu-help-callback\"")))

;;; --- D3. The leaf-shape words (gitignored plan, brief.org section 6) --

;; doc-check does not register a tracked-file check, but close the D2
;; group so the D5 registration check and the guards count into no group.
(setq m48-imp1--group nil)

(m48-imp1--doc-check "plan-module-emacs-terminal"
                     "docs/m48-plan.org" "(emacs terminal)")
(m48-imp1--doc-check "plan-leaf-plain-values"
                     "docs/m48-plan.org" "plain values only")
(m48-imp1--doc-check "plan-no-struct-across"
                     "docs/m48-plan.org" "struct tty_display_info")
;; the class table must carry a per-block MOVES / STAYS C verdict, so the
;; movable list, the class table, and the decision agree.
(m48-imp1--doc-check "plan-verdict-moves"
                     "docs/m48-plan.org" "MOVES")
(m48-imp1--doc-check "plan-verdict-stays-c"
                     "docs/m48-plan.org" "STAYS C")

;;; --- D4. The decision words (gitignored records) ----------------------

(m48-imp1--doc-check "plan-base-18a7e3372"
                     "docs/m48-plan.org" "#+base: HEAD = 18a7e3372")
(m48-imp1--doc-check "plan-target-term.c"
                     "docs/m48-plan.org" "#+target: src/term.c")
(m48-imp1--doc-check "plan-decision-A1"
                     "docs/m48-plan.org" "Decision: A1")
(m48-imp1--doc-check "plan-normal-context-slice"
                     "docs/m48-plan.org" "normal context")
;; the kb needles must be M48-scoped.  A bare "IMP-1 LANDED" and
;; "DECISION A1" each occur several times in docs/kb.org (the M42 .. M47
;; nodes), so they pass while the M48 node is absent or stale.  Search
;; the M48 sentence instead.  "term-os-boundary" is already unique.
(m48-imp1--doc-check "kb-records-imp1-landed"
                     "docs/kb.org"
                     "IMP-1 LANDED (docs only, no C, no Scheme).  The audit is docs/m48-plan.org")
(m48-imp1--doc-check "kb-records-decision-A1"
                     "docs/kb.org"
                     "DECISION A1: the src/term.c TTY terminal policy moves to Scheme in the existing module (emacs terminal)")
(m48-imp1--doc-check "kb-layer-term-os-boundary"
                     "docs/kb.org" "term-os-boundary")
;; the durable decision record needs the ** M48 node itself, so pin the
;; heading, not just its text.  An absent node is an INFO-skip.
(m48-imp1--doc-check "kb-node-M48-heading"
                     "docs/kb.org" "** M48\n  summary:")

;;; --- D6. The live tracker (milestone.org) ----------------------------
;;
;; milestone.org is untracked, so these are advisory (INFO-skip when the
;; tracker is absent or stale), but they guard against a recurrence.

(m48-imp1--doc-check "tracker-base-18a7e3372"
                     "milestone.org" "#+base: HEAD = 18a7e3372")
(m48-imp1--doc-check "tracker-imp1-done"
                     "milestone.org" "imp-1 is DONE")
(m48-imp1--doc-absent-check "tracker-no-stale-M48-open"
                            "milestone.org" "No imp has landed yet")

;;; --- D5. The group registration and the min-count guard --------------

(m48-imp1--check "reg/m48-group-present"
                 (m48-imp1--tracked-p "tool/run-tests.scm"
                                      "test/m48/test-m48-imp1.el"))
;; `m48-imp1--tracked-p' must fold an absent tracked file to nil, so that
;; `m48-imp1--check' prints FAIL for it (brief.org section 12: an absent
;; src/ file is a real error).  A non-existent path stands in for an
;; absent tracked file.
(m48-imp1--check "reg/absent-tracked-file-fails"
                 (null (m48-imp1--tracked-p "src/m48-imp1-no-such-file.c"
                                            "needle")))

;; An --filter that matches no group already reports exit 0 with 0 tests,
;; so a green m48 gate proves nothing until the corpus exists and its
;; checks really register.  These guards fail when the corpus body is
;; truncated or its core checks do not run.  The bound is per group, and
;; the counts are stable because every check is registered at load time.
;; D1 holds 11 checks; D2 holds 22.
(m48-imp1--check "reg/min-d1-checks-11"
                 (>= m48-imp1--registered-d1 11))
(m48-imp1--check "reg/min-d2-checks-22"
                 (>= m48-imp1--registered-d2 22))

(princ (format "=== m48 imp-1 audit suite done (%d tracked checks: D1 %d, D2 %d) ===\n"
               m48-imp1--registered m48-imp1--registered-d1 m48-imp1--registered-d2))
