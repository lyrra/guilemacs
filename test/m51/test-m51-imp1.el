;;; test-m51-imp1.el --- M51 imp-1 audit corpus (the src/image.c image file hop boundary).
;;;
;;; M51 imp-1 is the docs-only audit (brief.org, docs/m51-plan.org).  It
;;; changes no C and no Scheme.  It answers four questions with evidence
;;; -- the target choice over the six candidates (src/xterm.c,
;;; src/image.c, src/xfns.c, src/pgtkterm.c, src/sysdep.c, src/lread.c),
;;; the block map, the class of each block, the module name and the leaf
;;; shape, and the A1 / A2 decision.
;;;
;;; This corpus reads TRACKED files only.  It has no C dependency.  A
;;; test does not read docs/: a docs needle is not a behaviour, and
;;; docs/ is gitignored, so such a check can never fail on a fresh
;;; clone.  The docs needles live in tool/m51-plan-lint.sh, which the
;;; (m51) group does not run.  This corpus pins:
;;;   D1 -- the base numbers of docs/m51-plan.org section 3.  Each of the
;;;         six candidates is lines / DEFUNs / scm_c_public_ref sites /
;;;         the #include "guile.h" count: src/xterm.c 33,110 / 0 / 5 / 1;
;;;         src/image.c 13,207 / 11 / 0 / 1; src/xfns.c 10,546 / 54 /
;;;         0 / 0; src/pgtkterm.c 7,774 / 0 / 4 / 1; src/sysdep.c 4,950 /
;;;         7 / 7 / 1; src/lread.c 3,561 / 19 / 2 / 1.  The tree-wide
;;;         scm_c_public_ref count over src/*.[chm] is 230.  mod/emacs/
;;;         image.scm is ABSENT at the audit (the module does not exist
;;;         yet).  26 checks.
;;;   D2 -- the block map of section 3.1 for the recommended target,
;;;         src/image.c, as the ORDERED DEFUN NAME LIST (the 11 block
;;;         names in file order).  12 checks in all.  These are facts in
;;;         a tracked file, so a drift is a real FAIL.
;;;
;;;         D2 pins NAMES, not line numbers.  The "guile.h" include and
;;;         each new leaf move every line below them, so a line constant
;;;         invalidates itself at the next imp.  The ordered name list
;;;         survives imp-2 (a "--image-*" leaf name is skipped, see
;;;         below) and still catches a deletion or a re-order.
;;;   D5 -- the (m51) group is registered in tool/run-tests.scm, and this
;;;         corpus registers a minimum number of checks per group.  The
;;;         guard pins the group NAME, "(group (m51)", and its position
;;;         after "(group (m50)" -- a bare path needle proves only that
;;;         some group loads the file, not that the (m51) name or its
;;;         order holds (brief.org section 12.4).  An --filter that
;;;         matches no group already reports exit 0 and 0 tests, so the
;;;         gate proves nothing until the corpus exists and really runs.
;;;         A single total bound is too loose, so the guard pins D1 and
;;;         D2 separately and fails if either group is truncated.
;;;
;;; Each check is printed as a PASS/FAIL line and turned into an ERT
;;; test so the harness counts it.  A read error is a real error, never
;;; a silent pass.  The corpus holds its own copy of every fact it pins.

(princ "=== m51 imp-1 audit suite ===\n")

(require 'imp-ert-report)

(defvar m51-imp1--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))

(defvar m51-imp1--registered 0
  "Total number of tracked-file checks this corpus has registered.  D5
pins a per-group minimum, so a truncated load cannot pass the gate
with no real checks.")

(defvar m51-imp1--group nil
  "The group that `m51-imp1--check' counts into: `d1' or `d2', or nil.
D5 pins the D1 and D2 minima separately.")

(defvar m51-imp1--registered-d1 0
  "Number of D1 base-number checks registered.  D5 pins a minimum.")

(defvar m51-imp1--registered-d2 0
  "Number of D2 block-map checks registered.  D5 pins a minimum.")

(defun m51-imp1--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
the symbol `m51-imp1-absent' when REL does not exist.  docs/ is
gitignored, so a checkout without it must not crash the subprocess: an
unguarded `insert-file-contents' on an absent file would kill the
subprocess before ERT ever ran."
  (let ((path (expand-file-name rel m51-imp1--root)))
    (if (not (file-exists-p path))
        'm51-imp1-absent
      (with-temp-buffer
        (insert-file-contents path)
        (funcall fn)))))

(defun m51-imp1--contains-p (rel needle)
  "Non-nil when REL (repo-root-relative) contains NEEDLE."
  (m51-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (search-forward needle nil t))))

(defun m51-imp1--tracked-p (rel needle)
  "Non-nil when the TRACKED file REL contains NEEDLE.  A missing tracked
file yields nil, so `m51-imp1--check' prints FAIL: an absent src/ file
is a real error.  Contrast `m51-imp1--contains-p', which returns
`m51-imp1-absent' so a doc-check can tell absent from stale for a
gitignored record."
  (let ((hit (m51-imp1--contains-p rel needle)))
    (and (not (eq hit 'm51-imp1-absent)) (and hit t))))

(defun m51-imp1--exists-p (rel)
  "Non-nil when REL (repo-root-relative) exists as a file."
  (file-exists-p (expand-file-name rel m51-imp1--root)))

(defun m51-imp1--lines (rel)
  "Count the newlines of REL the way `wc -l' does."
  (m51-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (search-forward "\n" nil t) (setq n (1+ n)))
        n))))

(defun m51-imp1--count (rel regexp)
  "Count the matches of REGEXP in REL."
  (m51-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (re-search-forward regexp nil t) (setq n (1+ n)))
        n))))

(defun m51-imp1--count-literal (rel needle)
  "Count the matches of the LITERAL NEEDLE in REL.
`m51-imp1--count' takes a regexp, so a needle that holds a `.` (such as
`#include \"guile.h\"') would also match `#include \"guileXh\"'.  Quote
the needle so the count is exact."
  (m51-imp1--count rel (regexp-quote needle)))

(defun m51-imp1--defun-count (rel)
  "Count the `^DEFUN (' lines of REL.
The `^' anchor stays a regexp, but the rest of the needle is quoted, so
the `(' and `\"' are not treated as regexp syntax."
  (m51-imp1--count rel (concat "^" (regexp-quote "DEFUN (\""))))

(defun m51-imp1--line-of (rel needle)
  "1-based line number of the first LITERAL NEEDLE in REL, or nil.
An absent REL, or an absent needle, yields nil, so the caller prints a
real FAIL (m4x-probe-failure-must-not-read-as-a-skip)."
  (m51-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (when (search-forward needle nil t)
        (line-number-at-pos (match-beginning 0))))))

(defun m51-imp1--defun-names (rel)
  "The DEFUN names of REL, in file order.  D2 pins this list instead of
a line constant: a new leaf moves every line below it, but it cannot
re-order or delete a block without this list changing.
A name that starts with two hyphens is a typed --image-* leaf (imp-2),
not one of the 11 policy blocks, so D2 skips it.  D2 then stays the 11
block names after imp-2 and still catches a deletion or a re-order."
  (m51-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((names '()))
        (while (re-search-forward "^DEFUN (\"\\([^\"]+\\)\"" nil t)
          (let ((name (match-string 1)))
            (unless (string-prefix-p "--" name)
              (push name names))))
        (nreverse names)))))

(defun m51-imp1--count-scm-ref ()
  "Count scm_c_public_ref over src/*.[chm] (the docs/m51-plan.org section 3 measure)."
  (let ((total 0)
        (dir (expand-file-name "src" m51-imp1--root)))
    (dolist (f (directory-files dir t "\\.[chm]\\'"))
      (setq total (+ total (or (m51-imp1--count-literal f "scm_c_public_ref") 0))))
    total))

(defun m51-imp1--check (name ok)
  "Report and register one check on a TRACKED file.  OK is a boolean.
The D1/D2 callers pass `(eql N value)': when the source file is absent
the reader returns the symbol `m51-imp1-absent', so `eql' yields nil and
this prints FAIL.  The string-test callers use `m51-imp1--tracked-p',
which folds an absent file to nil for the same reason, so this prints
FAIL too.  An absent src/ file is a real error, not a pass.  The
`m51-imp1-absent' branch below is thus a safety net: no tracked caller
passes the raw symbol to reach it."
  (if (eq ok 'm51-imp1-absent)
      (princ (format "INFO m51/imp1/%s skipped (source file absent)\n" name))
    (progn
      (princ (format "%s m51/imp1/%s\n" (if ok "PASS" "FAIL") name))
      (setq m51-imp1--registered (1+ m51-imp1--registered))
      (cond ((eq m51-imp1--group 'd1)
             (setq m51-imp1--registered-d1 (1+ m51-imp1--registered-d1)))
            ((eq m51-imp1--group 'd2)
             (setq m51-imp1--registered-d2 (1+ m51-imp1--registered-d2))))
      (imp-register-bool-as-ert-test (format "m51-imp1/%s" name) (and ok t)))))

;;; --- D1. The base numbers (docs/m51-plan.org section 3) ---------------

(setq m51-imp1--group 'd1)

;; The six candidates of section 3.  Each is lines / DEFUNs /
;; scm_c_public_ref sites / the guile.h count.  The count form (rather
;; than `m51-imp1--tracked-p') keeps the guile.h fact absent-safe: an
;; absent file folds to the symbol, so `eql' fails and the check prints
;; FAIL.  imp-2 adds the (emacs image) module and the typed --image-*
;; leaf to src/image.c, so it must re-pin FOUR drifting facts:
;;   - image.c-lines-13207, image.c-defuns-11, and image.c-guile.h-1
;;     (the new leaf, its declaration, and the guile.h include);
;;   - image.c-scm-ref-0, which drifts from 0 to >=1 (the new typed leaf
;;     calls scm_c_public_ref);
;;   - scm-c-public-ref-230, the tree-wide src/*.[chm] count, which
;;     drifts from 230 to 231 (the same new include site).
;; imp-2 or imp-5 must re-pin all of them, or the D1 check FAILs.
(m51-imp1--check "xterm.c-lines-33110"
                 (eql 33110 (m51-imp1--lines "src/xterm.c")))
(m51-imp1--check "xterm.c-defuns-0"
                 (eql 0 (m51-imp1--defun-count "src/xterm.c")))
(m51-imp1--check "xterm.c-scm-ref-5"
                 (eql 5 (m51-imp1--count-literal "src/xterm.c" "scm_c_public_ref")))
(m51-imp1--check "xterm.c-guile.h-1"
                 (eql 1 (m51-imp1--count-literal "src/xterm.c" "#include \"guile.h\"")))
(m51-imp1--check "image.c-lines-13207"
                 (eql 13207 (m51-imp1--lines "src/image.c")))
(m51-imp1--check "image.c-defuns-11"
                 (eql 11 (m51-imp1--defun-count "src/image.c")))
(m51-imp1--check "image.c-scm-ref-0"
                 (eql 0 (m51-imp1--count-literal "src/image.c" "scm_c_public_ref")))
(m51-imp1--check "image.c-guile.h-1"
                 (eql 1 (m51-imp1--count-literal "src/image.c" "#include \"guile.h\"")))
(m51-imp1--check "xfns.c-lines-10546"
                 (eql 10546 (m51-imp1--lines "src/xfns.c")))
(m51-imp1--check "xfns.c-defuns-54"
                 (eql 54 (m51-imp1--defun-count "src/xfns.c")))
(m51-imp1--check "xfns.c-scm-ref-0"
                 (eql 0 (m51-imp1--count-literal "src/xfns.c" "scm_c_public_ref")))
(m51-imp1--check "xfns.c-guile.h-0"
                 (eql 0 (m51-imp1--count-literal "src/xfns.c" "#include \"guile.h\"")))
(m51-imp1--check "pgtkterm.c-lines-7774"
                 (eql 7774 (m51-imp1--lines "src/pgtkterm.c")))
(m51-imp1--check "pgtkterm.c-defuns-0"
                 (eql 0 (m51-imp1--defun-count "src/pgtkterm.c")))
(m51-imp1--check "pgtkterm.c-scm-ref-4"
                 (eql 4 (m51-imp1--count-literal "src/pgtkterm.c" "scm_c_public_ref")))
(m51-imp1--check "pgtkterm.c-guile.h-1"
                 (eql 1 (m51-imp1--count-literal "src/pgtkterm.c" "#include \"guile.h\"")))
(m51-imp1--check "sysdep.c-lines-4950"
                 (eql 4950 (m51-imp1--lines "src/sysdep.c")))
(m51-imp1--check "sysdep.c-defuns-7"
                 (eql 7 (m51-imp1--defun-count "src/sysdep.c")))
(m51-imp1--check "sysdep.c-scm-ref-7"
                 (eql 7 (m51-imp1--count-literal "src/sysdep.c" "scm_c_public_ref")))
(m51-imp1--check "sysdep.c-guile.h-1"
                 (eql 1 (m51-imp1--count-literal "src/sysdep.c" "#include \"guile.h\"")))
(m51-imp1--check "lread.c-lines-3561"
                 (eql 3561 (m51-imp1--lines "src/lread.c")))
(m51-imp1--check "lread.c-defuns-19"
                 (eql 19 (m51-imp1--defun-count "src/lread.c")))
(m51-imp1--check "lread.c-scm-ref-2"
                 (eql 2 (m51-imp1--count-literal "src/lread.c" "scm_c_public_ref")))
(m51-imp1--check "lread.c-guile.h-1"
                 (eql 1 (m51-imp1--count-literal "src/lread.c" "#include \"guile.h\"")))
(m51-imp1--check "scm-c-public-ref-230"
                 (eql 230 (m51-imp1--count-scm-ref)))
;; The recommended target's new module does not exist yet (imp-2 creates
;; it).  Pin the absence so a stray mod/emacs/image.scm fails here.
(m51-imp1--check "image-module-absent"
                 (null (m51-imp1--exists-p "mod/emacs/image.scm")))

;;; --- D2. The block map (docs/m51-plan.org section 3.1) ---------------
;;
;; The block definitions of src/image.c are the 11 DEFUN lines.  D2 pins
;; their NAMES in file order, not their line numbers: the "guile.h"
;; include and each new leaf move every line below them, so a line
;; constant invalidates itself at the next imp.

(setq m51-imp1--group 'd2)

(defconst m51-imp1--image-blocks
  '("image-size"
    "image-mask-p"
    "image-metadata"
    "clear-image-cache"
    "image-flush"
    "imagemagick-types"
    "imagep"
    "lookup-image"
    "image-transforms-p"
    "image-cache-size"
    "init-image-library")
  "The 11 src/image.c block names, in file order (section 3.1).")

(defvar m51-imp1--image-defuns
  (let ((found (m51-imp1--defun-names "src/image.c")))
    ;; An absent tracked file folds to the empty list, so every position
    ;; check below prints FAIL.  An absent src/ file is a real error.
    (if (listp found) found '()))
  "The DEFUN names read out of src/image.c, in file order.")

;; one check per block: the name AND its position must both hold.
(let ((i 0))
  (dolist (name m51-imp1--image-blocks)
    (m51-imp1--check (format "block-%02d-%s" (1+ i) name)
                     (equal name (nth i m51-imp1--image-defuns)))
    (setq i (1+ i))))

;; the whole list, so an EXTRA block is caught too.  A per-position
;; check alone passes when a 12th DEFUN is appended.
(m51-imp1--check "block-list-exact-11"
                 (equal m51-imp1--image-blocks m51-imp1--image-defuns))

;;; --- D5. The group registration and the min-count guard --------------

;; close the D2 group so the guards below count into no group.
(setq m51-imp1--group nil)

(m51-imp1--check "reg/m51-group-present"
                 (m51-imp1--tracked-p "tool/run-tests.scm"
                                      "test/m51/test-m51-imp1.el"))
;; The path needle above is weak: it proves only that SOME group loads
;; the file.  Pin the group NAME and its order too (brief.org section
;; 12.4): the corpus must register under the (m51) name, and that group
;; must follow the (m50) group.
(m51-imp1--check "reg/m51-group-name"
                 (m51-imp1--tracked-p "tool/run-tests.scm" "(group (m51)"))
(m51-imp1--check "reg/m51-group-after-m50"
                 (let ((m50 (m51-imp1--line-of "tool/run-tests.scm"
                                               "(group (m50)"))
                       (m51 (m51-imp1--line-of "tool/run-tests.scm"
                                               "(group (m51)")))
                   (and (integerp m50) (integerp m51) (< m50 m51))))
;; `m51-imp1--tracked-p' must fold an absent tracked file to nil, so that
;; `m51-imp1--check' prints FAIL for it: an absent src/ file is a real
;; error.  A non-existent path stands in for an absent tracked file.
(m51-imp1--check "reg/absent-tracked-file-fails"
                 (null (m51-imp1--tracked-p "src/m51-imp1-no-such-file.c"
                                            "needle")))

;; An --filter that matches no group already reports exit 0 with 0 tests,
;; so a green m51 gate proves nothing until the corpus exists and its
;; checks really register.  These guards fail when the corpus body is
;; truncated or its core checks do not run.  The bound is per group, and
;; the counts are stable because every check is registered at load time.
;; D1 holds 26 checks; D2 holds 12 (11 block positions and the
;; exact-list check).
(m51-imp1--check "reg/min-d1-checks-26"
                 (>= m51-imp1--registered-d1 26))
(m51-imp1--check "reg/min-d2-checks-12"
                 (>= m51-imp1--registered-d2 12))

(princ (format "=== m51 imp-1 audit suite done (%d tracked checks: D1 %d, D2 %d) ===\n"
               m51-imp1--registered m51-imp1--registered-d1 m51-imp1--registered-d2))
