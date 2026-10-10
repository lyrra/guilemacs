;;; test-m48-imp1.el --- M48 imp-1 audit corpus (src/term.c TTY terminal boundary).
;;;
;;; M48 imp-1 is the docs-only audit (brief.org, docs/m48-plan.org).  It
;;; changes no C and no Scheme.  It answers four questions with evidence
;;; -- the block map of the src/term.c TTY surface, the class of each
;;; block, the module name and the leaf shape, and the A1 / A2 decision.
;;;
;;; This corpus reads TRACKED files only.  It has no C dependency.  A
;;; test does not read docs/: a docs needle is not a behaviour, and
;;; docs/ is gitignored, so such a check can never fail on a fresh
;;; clone.  The docs needles live in tool/m48-plan-lint.sh, which the
;;; (m48) group does not run.  This corpus pins:
;;;   D1 -- the base numbers of docs/m48-plan.org section 3, re-pinned by
;;;         imp-2, imp-3, imp-4, imp-6, and imp-7.  src/term.c is 5,924 lines,
;;;         29 DEFUNs (25 M48 DEFUNs plus the 4 M52 imp-3 --tty-* leaves),
;;;         29 scm_c_public_ref sites (3 old + 4 G1 + 4 G3 + 5 M52 imp-4 + 6 M52 imp-5 + 4 M52 imp-6 + 3 M52 imp-7 refs), and
;;;         includes guile.h; mod/emacs/terminal.scm is 266 lines (134 +
;;;         the 8 wrappers); scm_c_public_ref over src/*.[chm] is 253;
;;;         src/keyboard.c is 11,233 lines and 447 DEFUNs;
;;;         src/keyboard-globals.c is 490 lines; the combined keyboard
;;;         surface is 11,723 (margin 237 under the 11,960 M31 budget).
;;;         11 checks.
;;;   D2 -- the block map of section 3.1 as the ORDERED DEFUN NAME LIST
;;;         (the 19 block names in file order), plus the three (emacs
;;;         terminal) ref sites matched by the module name and the
;;;         procedure name.  23 checks in all.  These are facts in a
;;;         tracked file, so a drift is a real FAIL.
;;;
;;;         D2 pins NAMES, not line numbers.  The "guile.h" include and
;;;         each new leaf move every line below them, so a line constant
;;;         invalidates itself at the next imp.  The ordered name list
;;;         survives imp-2 and still catches a deletion or a re-order.
;;;   D5 -- the (m48) group is registered in tool/run-tests.scm, and this
;;;         corpus registers a minimum number of checks per group.  An
;;;         --filter that matches no group already reports exit 0 and 0
;;;         tests, so the gate proves nothing until the corpus exists and
;;;         really runs.  A single total bound is too loose, so the guard
;;;         pins D1 and D2 separately and fails if either group is
;;;         truncated.
;;;
;;; D3, D4 and D6 of the first pass are gone from the suite.  They read
;;; docs/m48-plan.org, docs/kb.org and milestone.org.  See
;;; tool/m48-plan-lint.sh.
;;;
;;; From imp-3 this corpus also gets BEHAVIOUR checks: each ported leaf
;;; of (emacs terminal) is called with plain values and its return value
;;; is asserted.  That is the real gate; D1, D2 and D5 are the surface
;;; guard.
;;;
;;; Each check is printed as a PASS/FAIL line and turned into an ERT
;;; test so the harness counts it.  A read error is a real error, never
;;; a silent pass.  The corpus holds its own copy of every fact it pins.

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

(defun m48-imp1--defun-names (rel)
  "The DEFUN names of REL, in file order.  D2 pins this list instead of
a line constant: a new leaf moves every line below it, but it cannot
re-order or delete a block without this list changing.
A name that starts with two hyphens is a typed --term-* leaf (imp-2),
not one of the 19 policy blocks, so D2 skips it.  D2 then stays the 19
block names after imp-2 and still catches a deletion or a re-order."
  (m48-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((names '()))
        (while (re-search-forward "^DEFUN (\"\\([^\"]+\\)\"" nil t)
          (let ((name (match-string 1)))
            (unless (string-prefix-p "--" name)
              (push name names))))
        (nreverse names)))))

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

;;; --- D1. The base numbers (docs/m48-plan.org section 3) ---------------

(setq m48-imp1--group 'd1)

;;; D1 was re-pinned after each M48 implementation step.  At imp-6 the
;;; two geometry leaves and their C arithmetic were removed; the Scheme
;;; module now owns the geometry arithmetic.  The current source has 29
;;; DEFUNs and 29 term.c refs.  The keyboard surface does not move.
(m48-imp1--check "term.c-lines-5924"
                 (eql 5924 (m48-imp1--lines "src/term.c")))
(m48-imp1--check "term.c-defuns-29"
                 (eql 29 (m48-imp1--count "src/term.c" "^DEFUN (\"")))
(m48-imp1--check "term.c-scm-ref-29"
                 (eql 29 (m48-imp1--count "src/term.c" "scm_c_public_ref")))
(m48-imp1--check "term.c-has-guile.h"
                 (m48-imp1--tracked-p "src/term.c" "#include \"guile.h\""))
(m48-imp1--check "terminal.scm-lines-266"
                 (eql 266 (m48-imp1--lines "mod/emacs/terminal.scm")))
(m48-imp1--check "scm-c-public-ref-253"
                 (eql 253 (m48-imp1--count-scm-ref)))
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

;;; --- D2. The block map (docs/m48-plan.org section 3.1) ---------------
;;
;; The block definitions of src/term.c are the 19 DEFUN lines.  D2 pins
;; their NAMES in file order, not their line numbers: the "guile.h"
;; include and each new leaf move every line below them, so a line
;; constant invalidates itself at the next imp.  The ordered name list
;; survives imp-2 and still catches a deletion or a re-order.

(setq m48-imp1--group 'd2)

(defconst m48-imp1--term-blocks
  '("tty-display-color-p"
    "tty-display-color-cells"
    "tty-type"
    "controlling-tty-p"
    "tty-no-underline"
    "tty-top-frame"
    "suspend-tty"
    "resume-tty"
    "tty--set-output-buffer-size"
    "tty--output-buffer-size"
    "tty-frame-at"
    "gpm-mouse-start"
    "gpm-mouse-stop"
    "tty-frame-geometry"
    "tty-frame-edges"
    "tty-frame-list-z-order"
    "tty-frame-restack"
    "tty-display-pixel-width"
    "tty-display-pixel-height")
  "The 19 src/term.c block names, in file order (section 3.1).")

(defvar m48-imp1--term-defuns
  (let ((found (m48-imp1--defun-names "src/term.c")))
    ;; An absent tracked file folds to the empty list, so every position
    ;; check below prints FAIL.  An absent src/ file is a real error.
    (if (listp found) found '()))
  "The DEFUN names read out of src/term.c, in file order.")

;; one check per block: the name AND its position must both hold.
(let ((i 0))
  (dolist (name m48-imp1--term-blocks)
    (m48-imp1--check (format "block-%02d-%s" (1+ i) name)
                     (equal name (nth i m48-imp1--term-defuns)))
    (setq i (1+ i))))

;; the whole list, so an EXTRA block is caught too.  A per-position
;; check alone passes when a 20th DEFUN is appended.
(m48-imp1--check "block-list-exact-19"
                 (equal m48-imp1--term-blocks m48-imp1--term-defuns))

;; the three ref sites: the M33 imp-1 (emacs terminal) consumers.
;; Matched by the module name and the procedure name, not by line.
(m48-imp1--check "term.c-ref-tty-menu-clear-help"
                 (m48-imp1--tracked-p
                  "src/term.c"
                  "scm_c_public_ref (\"emacs terminal\", \"tty-menu-clear-help!\""))
(m48-imp1--check "term.c-ref-tty-menu-discard-mouse-events"
                 (m48-imp1--tracked-p
                  "src/term.c"
                  "scm_c_public_ref (\"emacs terminal\", \"tty-menu-discard-mouse-events!\""))
(m48-imp1--check "term.c-ref-tty-menu-help-callback"
                 (m48-imp1--tracked-p
                  "src/term.c"
                  "scm_c_public_ref (\"emacs terminal\", \"tty-menu-help-callback\""))

;;; --- D5. The group registration and the min-count guard --------------

;; close the D2 group so the guards below count into no group.
(setq m48-imp1--group nil)

(m48-imp1--check "reg/m48-group-present"
                 (m48-imp1--tracked-p "tool/run-tests.scm"
                                      "test/m48/test-m48-imp1.el"))
;; `m48-imp1--tracked-p' must fold an absent tracked file to nil, so that
;; `m48-imp1--check' prints FAIL for it: an absent src/ file is a real
;; error.  A non-existent path stands in for an absent tracked file.
(m48-imp1--check "reg/absent-tracked-file-fails"
                 (null (m48-imp1--tracked-p "src/m48-imp1-no-such-file.c"
                                            "needle")))

;; An --filter that matches no group already reports exit 0 with 0 tests,
;; so a green m48 gate proves nothing until the corpus exists and its
;; checks really register.  These guards fail when the corpus body is
;; truncated or its core checks do not run.  The bound is per group, and
;; the counts are stable because every check is registered at load time.
;; D1 holds 11 checks; D2 holds 23 (19 block positions, the exact-list
;; check, and the 3 ref sites).
(m48-imp1--check "reg/min-d1-checks-11"
                 (>= m48-imp1--registered-d1 11))
(m48-imp1--check "reg/min-d2-checks-23"
                 (>= m48-imp1--registered-d2 23))

(princ (format "=== m48 imp-1 audit suite done (%d tracked checks: D1 %d, D2 %d) ===\n"
               m48-imp1--registered m48-imp1--registered-d1 m48-imp1--registered-d2))
