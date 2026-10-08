;;; test-m50-imp1.el --- M50 imp-1 audit corpus (the src/emacs.c invocation / daemon boundary).
;;;
;;; M50 imp-1 is the docs-only audit (brief.org, docs/m50-plan.org).  It
;;; changes no C and no Scheme.  It answers four questions with evidence
;;; -- the target choice over the three candidates (src/sysdep.c,
;;; src/emacs.c, src/coding.c), the block map, the class of each block,
;;; the module name and the leaf shape, and the A1 / A2 decision.
;;;
;;; This corpus reads TRACKED files only.  It has no C dependency.  A
;;; test does not read docs/: a docs needle is not a behaviour, and
;;; docs/ is gitignored, so such a check can never fail on a fresh
;;; clone.  The docs needles live in tool/m50-plan-lint.sh, which the
;;; (m50) group does not run.  This corpus pins:
;;;   D1 -- the base numbers of docs/m50-plan.org section 3.  Each
;;;         candidate is lines / DEFUNs / scm_c_public_ref sites:
;;;         src/sysdep.c 4,950 / 7 / 7; src/emacs.c 3,441 / 5 / 6 (at
;;;         the imp-1 audit it was 3,414 / 5 / 5; M50 imp-2 adds the
;;;         typed --emacs-daemon-state leaf and its helper, so it
;;;         re-pinned the line and DEFUN counts; M50 imp-3 deletes
;;;         the leaf and adds the daemonp bridge, so it re-pins them
;;;         again);
;;;         src/coding.c 12,284 / 34 / 0.  The tree-wide scm_c_public_ref
;;;         count over src/*.[chm] is 235.  Each of the three candidates
;;;         holds #include "guile.h" already (brief.org section 4).
;;;         mod/emacs/emacs.scm is present (M50 imp-2 creates it; it was
;;;         absent at the imp-1 audit).  14 checks.
;;;   D2 -- the block map of section 3.1 for the recommended target,
;;;         src/emacs.c, as the ORDERED DEFUN NAME LIST (the 5 block
;;;         names in file order).  6 checks in all.  These are facts in a
;;;         tracked file, so a drift is a real FAIL.
;;;
;;;         D2 pins NAMES, not line numbers.  The "guile.h" include and
;;;         each new leaf move every line below them, so a line constant
;;;         invalidates itself at the next imp.  The ordered name list
;;;         survives imp-2 and still catches a deletion or a re-order.
;;;   D5 -- the (m50) group is registered in tool/run-tests.scm, and this
;;;         corpus registers a minimum number of checks per group.  An
;;;         --filter that matches no group already reports exit 0 and 0
;;;         tests, so the gate proves nothing until the corpus exists and
;;;         really runs.  A single total bound is too loose, so the guard
;;;         pins D1 and D2 separately and fails if either group is
;;;         truncated.
;;;
;;; Each check is printed as a PASS/FAIL line and turned into an ERT
;;; test so the harness counts it.  A read error is a real error, never
;;; a silent pass.  The corpus holds its own copy of every fact it pins.

(princ "=== m50 imp-1 audit suite ===\n")

(require 'imp-ert-report)

(defvar m50-imp1--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))

(defvar m50-imp1--registered 0
  "Total number of tracked-file checks this corpus has registered.  D5
pins a per-group minimum, so a truncated load cannot pass the gate
with no real checks.")

(defvar m50-imp1--group nil
  "The group that `m50-imp1--check' counts into: `d1' or `d2', or nil.
D5 pins the D1 and D2 minima separately.")

(defvar m50-imp1--registered-d1 0
  "Number of D1 base-number checks registered.  D5 pins a minimum.")

(defvar m50-imp1--registered-d2 0
  "Number of D2 block-map checks registered.  D5 pins a minimum.")

(defun m50-imp1--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
the symbol `m50-imp1-absent' when REL does not exist.  docs/ is
gitignored, so a checkout without it must not crash the subprocess: an
unguarded `insert-file-contents' on an absent file would kill the
subprocess before ERT ever ran."
  (let ((path (expand-file-name rel m50-imp1--root)))
    (if (not (file-exists-p path))
        'm50-imp1-absent
      (with-temp-buffer
        (insert-file-contents path)
        (funcall fn)))))

(defun m50-imp1--contains-p (rel needle)
  "Non-nil when REL (repo-root-relative) contains NEEDLE."
  (m50-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (search-forward needle nil t))))

(defun m50-imp1--tracked-p (rel needle)
  "Non-nil when the TRACKED file REL contains NEEDLE.  A missing tracked
file yields nil, so `m50-imp1--check' prints FAIL: an absent src/ file
is a real error.  Contrast `m50-imp1--contains-p', which returns
`m50-imp1-absent' so a doc-check can tell absent from stale for a
gitignored record."
  (let ((hit (m50-imp1--contains-p rel needle)))
    (and (not (eq hit 'm50-imp1-absent)) (and hit t))))

(defun m50-imp1--exists-p (rel)
  "Non-nil when REL (repo-root-relative) exists as a file."
  (file-exists-p (expand-file-name rel m50-imp1--root)))

(defun m50-imp1--lines (rel)
  "Count the newlines of REL the way `wc -l' does."
  (m50-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (search-forward "\n" nil t) (setq n (1+ n)))
        n))))

(defun m50-imp1--count (rel regexp)
  "Count the matches of REGEXP in REL."
  (m50-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (re-search-forward regexp nil t) (setq n (1+ n)))
        n))))

(defun m50-imp1--defun-names (rel)
  "The DEFUN names of REL, in file order.  D2 pins this list instead of
a line constant: a new leaf moves every line below it, but it cannot
re-order or delete a block without this list changing.
A name that starts with two hyphens is a typed --emacs-* leaf (imp-2),
not one of the 5 policy blocks, so D2 skips it.  D2 then stays the 5
block names after imp-2 and still catches a deletion or a re-order."
  (m50-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((names '()))
        (while (re-search-forward "^DEFUN (\"\\([^\"]+\\)\"" nil t)
          (let ((name (match-string 1)))
            (unless (string-prefix-p "--" name)
              (push name names))))
        (nreverse names)))))

(defun m50-imp1--count-scm-ref ()
  "Count scm_c_public_ref over src/*.[chm] (the docs/m50-plan.org section 3 measure)."
  (let ((total 0)
        (dir (expand-file-name "src" m50-imp1--root)))
    (dolist (f (directory-files dir t "\\.[chm]\\'"))
      (setq total (+ total (or (m50-imp1--count f "scm_c_public_ref") 0))))
    total))

(defun m50-imp1--check (name ok)
  "Report and register one check on a TRACKED file.  OK is a boolean.
The D1/D2 callers pass `(eql N value)': when the source file is absent
the reader returns the symbol `m50-imp1-absent', so `eql' yields nil and
this prints FAIL.  The string-test callers use `m50-imp1--tracked-p',
which folds an absent file to nil for the same reason, so this prints
FAIL too.  An absent src/ file is a real error, not a pass.  The
`m50-imp1-absent' branch below is thus a safety net: no tracked caller
passes the raw symbol to reach it."
  (if (eq ok 'm50-imp1-absent)
      (princ (format "INFO m50/imp1/%s skipped (source file absent)\n" name))
    (progn
      (princ (format "%s m50/imp1/%s\n" (if ok "PASS" "FAIL") name))
      (setq m50-imp1--registered (1+ m50-imp1--registered))
      (cond ((eq m50-imp1--group 'd1)
             (setq m50-imp1--registered-d1 (1+ m50-imp1--registered-d1)))
            ((eq m50-imp1--group 'd2)
             (setq m50-imp1--registered-d2 (1+ m50-imp1--registered-d2))))
      (imp-register-bool-as-ert-test (format "m50-imp1/%s" name) (and ok t)))))

;;; --- D1. The base numbers (docs/m50-plan.org section 3) ---------------

(setq m50-imp1--group 'd1)

;;; imp-2 created the (emacs emacs) module and added the typed
;;; --emacs-* leaf to src/emacs.c.  M50 imp-3 deletes that leaf and
;;; adds the daemonp bridge, so it must re-pin these: the emacs.c line
;;; count, the DEFUN count, the guile.h fact, and the module fact.  A
;;; leaf that adds a scm_c_public_ref site moves the emacs.c ref count
;;; and the tree-wide count too; the bridge adds one ref site.
(m50-imp1--check "sysdep.c-lines-4950"
                 (eql 4950 (m50-imp1--lines "src/sysdep.c")))
(m50-imp1--check "sysdep.c-defuns-7"
                 (eql 7 (m50-imp1--count "src/sysdep.c" "^DEFUN (\"")))
(m50-imp1--check "sysdep.c-scm-ref-7"
                 (eql 7 (m50-imp1--count "src/sysdep.c" "scm_c_public_ref")))
(m50-imp1--check "emacs.c-lines-3441"
                 (eql 3441 (m50-imp1--lines "src/emacs.c")))
(m50-imp1--check "emacs.c-defuns-5"
                 (eql 5 (m50-imp1--count "src/emacs.c" "^DEFUN (\"")))
(m50-imp1--check "emacs.c-scm-ref-6"
                 (eql 6 (m50-imp1--count "src/emacs.c" "scm_c_public_ref")))
(m50-imp1--check "coding.c-lines-12284"
                 (eql 12284 (m50-imp1--lines "src/coding.c")))
(m50-imp1--check "coding.c-defuns-34"
                 (eql 34 (m50-imp1--count "src/coding.c" "^DEFUN (\"")))
(m50-imp1--check "coding.c-scm-ref-0"
                 (eql 0 (m50-imp1--count "src/coding.c" "scm_c_public_ref")))
(m50-imp1--check "scm-c-public-ref-235"
                 (eql 235 (m50-imp1--count-scm-ref)))
(m50-imp1--check "emacs-module-present"
                 (m50-imp1--exists-p "mod/emacs/emacs.scm"))
;; brief.org section 4 states that each candidate holds #include "guile.h"
;; already.  The M49 sibling corpus pinned its guile.h fact, so pin the
;; three M50 candidates too.  These are facts in tracked files, so a drift
;; is a real FAIL.  imp-2 keeps them: it adds leaves to src/emacs.c and
;; does not remove the include.
(m50-imp1--check "sysdep.c-has-guile.h"
                 (m50-imp1--tracked-p "src/sysdep.c" "#include \"guile.h\""))
(m50-imp1--check "emacs.c-has-guile.h"
                 (m50-imp1--tracked-p "src/emacs.c" "#include \"guile.h\""))
(m50-imp1--check "coding.c-has-guile.h"
                 (m50-imp1--tracked-p "src/coding.c" "#include \"guile.h\""))

;;; --- D2. The block map (docs/m50-plan.org section 3.1) ---------------
;;
;; The block definitions of src/emacs.c are the 5 DEFUN lines.  D2 pins
;; their NAMES in file order, not their line numbers: the "guile.h"
;; include and each new leaf move every line below them, so a line
;; constant invalidates itself at the next imp.

(setq m50-imp1--group 'd2)

(defconst m50-imp1--emacs-blocks
  '("invocation-name"
    "invocation-directory"
    "kill-emacs"
    "daemonp"
    "daemon-initialized")
  "The 5 src/emacs.c block names, in file order (section 3.1).")

(defvar m50-imp1--emacs-defuns
  (let ((found (m50-imp1--defun-names "src/emacs.c")))
    ;; An absent tracked file folds to the empty list, so every position
    ;; check below prints FAIL.  An absent src/ file is a real error.
    (if (listp found) found '()))
  "The DEFUN names read out of src/emacs.c, in file order.")

;; one check per block: the name AND its position must both hold.
(let ((i 0))
  (dolist (name m50-imp1--emacs-blocks)
    (m50-imp1--check (format "block-%02d-%s" (1+ i) name)
                     (equal name (nth i m50-imp1--emacs-defuns)))
    (setq i (1+ i))))

;; the whole list, so an EXTRA block is caught too.  A per-position
;; check alone passes when a 6th DEFUN is appended.
(m50-imp1--check "block-list-exact-5"
                 (equal m50-imp1--emacs-blocks m50-imp1--emacs-defuns))

;;; --- D5. The group registration and the min-count guard --------------

;; close the D2 group so the guards below count into no group.
(setq m50-imp1--group nil)

(m50-imp1--check "reg/m50-group-present"
                 (m50-imp1--tracked-p "tool/run-tests.scm"
                                      "test/m50/test-m50-imp1.el"))
;; `m50-imp1--tracked-p' must fold an absent tracked file to nil, so that
;; `m50-imp1--check' prints FAIL for it: an absent src/ file is a real
;; error.  A non-existent path stands in for an absent tracked file.
(m50-imp1--check "reg/absent-tracked-file-fails"
                 (null (m50-imp1--tracked-p "src/m50-imp1-no-such-file.c"
                                            "needle")))

;; An --filter that matches no group already reports exit 0 with 0 tests,
;; so a green m50 gate proves nothing until the corpus exists and its
;; checks really register.  These guards fail when the corpus body is
;; truncated or its core checks do not run.  The bound is per group, and
;; the counts are stable because every check is registered at load time.
;; D1 holds 14 checks; D2 holds 6 (5 block positions and the exact-list
;; check).
(m50-imp1--check "reg/min-d1-checks-14"
                 (>= m50-imp1--registered-d1 14))
(m50-imp1--check "reg/min-d2-checks-6"
                 (>= m50-imp1--registered-d2 6))

(princ (format "=== m50 imp-1 audit suite done (%d tracked checks: D1 %d, D2 %d) ===\n"
               m50-imp1--registered m50-imp1--registered-d1 m50-imp1--registered-d2))
