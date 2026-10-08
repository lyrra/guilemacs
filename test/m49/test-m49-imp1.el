;;; test-m49-imp1.el --- M49 imp-1 audit corpus (src/dired.c directory boundary).
;;;
;;; M49 imp-1 is the docs-only audit (brief.org, docs/m49-plan.org).  It
;;; changes no C and no Scheme.  It answers four questions with evidence
;;; -- the block map of the src/dired.c directory surface, the class of
;;; each block, the module name and the leaf shape, and the A1 / A2
;;; decision.
;;;
;;; This corpus reads TRACKED files only.  It has no C dependency.  A
;;; test does not read docs/: a docs needle is not a behaviour, and
;;; docs/ is gitignored, so such a check can never fail on a fresh
;;; clone.  The docs needles live in tool/m49-plan-lint.sh, which the
;;; (m49) group does not run.  This corpus pins:
;;;   D1 -- the base numbers of docs/m49-plan.org section 3.  src/dired.c
;;;         is 1,167 lines, 8 DEFUNs, 0 scm_c_public_ref sites, and
;;;         includes no guile.h; mod/emacs/dired.scm is absent; the
;;;         tree-wide scm_c_public_ref count over src/*.[chm] is 227.
;;;         6 checks.
;;;   D2 -- the block map of section 3.1 as the ORDERED DEFUN NAME LIST
;;;         (the 8 block names in file order).  9 checks in all.  These
;;;         are facts in a tracked file, so a drift is a real FAIL.
;;;
;;;         D2 pins NAMES, not line numbers.  The "guile.h" include and
;;;         each new leaf move every line below them, so a line constant
;;;         invalidates itself at the next imp.  The ordered name list
;;;         survives imp-2 and still catches a deletion or a re-order.
;;;   D5 -- the (m49) group is registered in tool/run-tests.scm, and this
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

(princ "=== m49 imp-1 audit suite ===\n")

(require 'imp-ert-report)

(defvar m49-imp1--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))

(defvar m49-imp1--registered 0
  "Total number of tracked-file checks this corpus has registered.  D5
pins a per-group minimum, so a truncated load cannot pass the gate
with no real checks.")

(defvar m49-imp1--group nil
  "The group that `m49-imp1--check' counts into: `d1' or `d2', or nil.
D5 pins the D1 and D2 minima separately.")

(defvar m49-imp1--registered-d1 0
  "Number of D1 base-number checks registered.  D5 pins a minimum.")

(defvar m49-imp1--registered-d2 0
  "Number of D2 block-map checks registered.  D5 pins a minimum.")

(defun m49-imp1--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
the symbol `m49-imp1-absent' when REL does not exist.  docs/ is
gitignored, so a checkout without it must not crash the subprocess: an
unguarded `insert-file-contents' on an absent file would kill the
subprocess before ERT ever ran."
  (let ((path (expand-file-name rel m49-imp1--root)))
    (if (not (file-exists-p path))
        'm49-imp1-absent
      (with-temp-buffer
        (insert-file-contents path)
        (funcall fn)))))

(defun m49-imp1--contains-p (rel needle)
  "Non-nil when REL (repo-root-relative) contains NEEDLE."
  (m49-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (search-forward needle nil t))))

(defun m49-imp1--tracked-p (rel needle)
  "Non-nil when the TRACKED file REL contains NEEDLE.  A missing tracked
file yields nil, so `m49-imp1--check' prints FAIL: an absent src/ file
is a real error.  Contrast `m49-imp1--contains-p', which returns
`m49-imp1-absent' so a doc-check can tell absent from stale for a
gitignored record."
  (let ((hit (m49-imp1--contains-p rel needle)))
    (and (not (eq hit 'm49-imp1-absent)) (and hit t))))

(defun m49-imp1--exists-p (rel)
  "Non-nil when REL (repo-root-relative) exists as a file."
  (file-exists-p (expand-file-name rel m49-imp1--root)))

(defun m49-imp1--lines (rel)
  "Count the newlines of REL the way `wc -l' does."
  (m49-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (search-forward "\n" nil t) (setq n (1+ n)))
        n))))

(defun m49-imp1--count (rel regexp)
  "Count the matches of REGEXP in REL."
  (m49-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (re-search-forward regexp nil t) (setq n (1+ n)))
        n))))

(defun m49-imp1--defun-names (rel)
  "The DEFUN names of REL, in file order.  D2 pins this list instead of
a line constant: a new leaf moves every line below it, but it cannot
re-order or delete a block without this list changing.
A name that starts with two hyphens is a typed --dired-* leaf (imp-2),
not one of the 8 policy blocks, so D2 skips it.  D2 then stays the 8
block names after imp-2 and still catches a deletion or a re-order."
  (m49-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((names '()))
        (while (re-search-forward "^DEFUN (\"\\([^\"]+\\)\"" nil t)
          (let ((name (match-string 1)))
            (unless (string-prefix-p "--" name)
              (push name names))))
        (nreverse names)))))

(defun m49-imp1--count-scm-ref ()
  "Count scm_c_public_ref over src/*.[chm] (the brief.org section 3 measure)."
  (let ((total 0)
        (dir (expand-file-name "src" m49-imp1--root)))
    (dolist (f (directory-files dir t "\\.[chm]\\'"))
      (setq total (+ total (or (m49-imp1--count f "scm_c_public_ref") 0))))
    total))

(defun m49-imp1--check (name ok)
  "Report and register one check on a TRACKED file.  OK is a boolean.
The D1/D2 callers pass `(eql N value)': when the source file is absent
the reader returns the symbol `m49-imp1-absent', so `eql' yields nil and
this prints FAIL.  The string-test callers use `m49-imp1--tracked-p',
which folds an absent file to nil for the same reason, so this prints
FAIL too.  An absent src/ file is a real error, not a pass.  The
`m49-imp1-absent' branch below is thus a safety net: no tracked caller
passes the raw symbol to reach it."
  (if (eq ok 'm49-imp1-absent)
      (princ (format "INFO m49/imp1/%s skipped (source file absent)\n" name))
    (progn
      (princ (format "%s m49/imp1/%s\n" (if ok "PASS" "FAIL") name))
      (setq m49-imp1--registered (1+ m49-imp1--registered))
      (cond ((eq m49-imp1--group 'd1)
             (setq m49-imp1--registered-d1 (1+ m49-imp1--registered-d1)))
            ((eq m49-imp1--group 'd2)
             (setq m49-imp1--registered-d2 (1+ m49-imp1--registered-d2))))
      (imp-register-bool-as-ert-test (format "m49-imp1/%s" name) (and ok t)))))

;;; --- D1. The base numbers (docs/m49-plan.org section 3) ---------------

(setq m49-imp1--group 'd1)

;;; imp-2 re-pins these: the guile.h include, the 4 --dired-* leaves, and
;;; the (emacs dired) module move the line count, the DEFUN count, the
;;; guile.h fact, and the module fact.  imp-2 adds no scm_c_public_ref
;;; site, so the two ref counts do not move.
;;;; imp-3 re-pins these again: the deleted G1 leaf, the new static
;;; helper dired_read_names_1, and the one new scm_c_public_ref site move
;;; the line count, the DEFUN count, and the dired.c ref count.
;;; imp-4 re-pins these again: the deleted G3 leaf and the new G3 dispatch
;;; helper move the line count, the DEFUN count, and the dired.c ref
;;; count (G2 stays in C, so no other site moves).
(m49-imp1--check "dired.c-lines-1346"
                 (eql 1346 (m49-imp1--lines "src/dired.c")))
(m49-imp1--check "dired.c-defuns-10"
                 (eql 10 (m49-imp1--count "src/dired.c" "^DEFUN (\"")))
(m49-imp1--check "dired.c-scm-ref-2"
                 (eql 2 (m49-imp1--count "src/dired.c" "scm_c_public_ref")))
(m49-imp1--check "dired.c-has-guile.h"
                 (m49-imp1--tracked-p "src/dired.c" "#include \"guile.h\""))
(m49-imp1--check "dired-module-present"
                 (m49-imp1--exists-p "mod/emacs/dired.scm"))
(m49-imp1--check "scm-c-public-ref-235"
                 (eql 235 (m49-imp1--count-scm-ref)))

;;; --- D2. The block map (docs/m49-plan.org section 3.1) ---------------
;;
;; The block definitions of src/dired.c are the 8 DEFUN lines.  D2 pins
;; their NAMES in file order, not their line numbers: the "guile.h"
;; include and each new leaf move every line below them, so a line
;; constant invalidates itself at the next imp.  The ordered name list
;; survives imp-2 and still catches a deletion or a re-order.

(setq m49-imp1--group 'd2)

(defconst m49-imp1--dired-blocks
  '("directory-files"
    "directory-files-and-attributes"
    "file-name-completion"
    "file-name-all-completions"
    "file-attributes"
    "file-attributes-lessp"
    "system-users"
    "system-groups")
  "The 8 src/dired.c block names, in file order (section 3.1).")

(defvar m49-imp1--dired-defuns
  (let ((found (m49-imp1--defun-names "src/dired.c")))
    ;; An absent tracked file folds to the empty list, so every position
    ;; check below prints FAIL.  An absent src/ file is a real error.
    (if (listp found) found '()))
  "The DEFUN names read out of src/dired.c, in file order.")

;; one check per block: the name AND its position must both hold.
(let ((i 0))
  (dolist (name m49-imp1--dired-blocks)
    (m49-imp1--check (format "block-%02d-%s" (1+ i) name)
                     (equal name (nth i m49-imp1--dired-defuns)))
    (setq i (1+ i))))

;; the whole list, so an EXTRA block is caught too.  A per-position
;; check alone passes when a 9th DEFUN is appended.
(m49-imp1--check "block-list-exact-8"
                 (equal m49-imp1--dired-blocks m49-imp1--dired-defuns))

;;; --- D5. The group registration and the min-count guard --------------

;; close the D2 group so the guards below count into no group.
(setq m49-imp1--group nil)

(m49-imp1--check "reg/m49-group-present"
                 (m49-imp1--tracked-p "tool/run-tests.scm"
                                      "test/m49/test-m49-imp1.el"))
;; `m49-imp1--tracked-p' must fold an absent tracked file to nil, so that
;; `m49-imp1--check' prints FAIL for it: an absent src/ file is a real
;; error.  A non-existent path stands in for an absent tracked file.
(m49-imp1--check "reg/absent-tracked-file-fails"
                 (null (m49-imp1--tracked-p "src/m49-imp1-no-such-file.c"
                                            "needle")))

;; An --filter that matches no group already reports exit 0 with 0 tests,
;; so a green m49 gate proves nothing until the corpus exists and its
;; checks really register.  These guards fail when the corpus body is
;; truncated or its core checks do not run.  The bound is per group, and
;; the counts are stable because every check is registered at load time.
;; D1 holds 6 checks; D2 holds 9 (8 block positions and the exact-list
;; check).
(m49-imp1--check "reg/min-d1-checks-6"
                 (>= m49-imp1--registered-d1 6))
(m49-imp1--check "reg/min-d2-checks-9"
                 (>= m49-imp1--registered-d2 9))

(princ (format "=== m49 imp-1 audit suite done (%d tracked checks: D1 %d, D2 %d) ===\n"
               m49-imp1--registered m49-imp1--registered-d1 m49-imp1--registered-d2))
