;;; test-m52-imp1.el --- M52 imp-1 audit corpus (the candidate OS boundaries).
;;;
;;; M52 imp-1 is the docs-only evidence audit (brief.org, docs/m52-plan.org).
;;; It changes no C and no Scheme.  It answers the brief.org section 6
;;; questions with evidence: it re-measures the five candidates, maps the
;;; block of each candidate, and returns the A1 / A2 verdict.
;;;
;;; The M52 target is a USER SCOPE DECISION (brief.org section 2).  No
;;; candidate passes the brief.org section 2 rule, so the verdict is A2:
;;; no recommended file, no module.  This corpus pins the evidence for
;;; that verdict.
;;;
;;; This corpus reads TRACKED files only.  It has no C dependency.  A test
;;; does not read docs/: a docs needle is not a behaviour, and docs/ is
;;; gitignored, so such a check can never fail on a fresh clone.  The docs
;;; needles live in tool/m52-plan-lint.sh, which no group runs.  This
;;; corpus pins:
;;;   D1 -- the base numbers of docs/m52-plan.org section 3.  Each of the
;;;         five candidates is lines / DEFUNs / scm_c_public_ref sites /
;;;         the #include "guile.h" count: src/xterm.c 33,110 / 0 / 5 / 1;
;;;         src/xfns.c 10,546 / 54 / 0 / 0; src/pgtkterm.c 7,774 / 0 / 4 /
;;;         1; src/sysdep.c 4,950 / 7 / 7 / 1; src/lread.c 3,561 / 19 / 2 /
;;;         1.  The tree-wide scm_c_public_ref count over src/*.[chm] is
;;;         235.  21 checks.
;;;   D2 -- the block map of section 3.1 for the two candidates whose
;;;         blocks carry the A2 argument: src/sysdep.c (the 7-name ordered
;;;         DEFUN list) and src/lread.c (the 19-name ordered DEFUN list).
;;;         The other three candidates have 0 DEFUNs (src/xterm.c,
;;;         src/pgtkterm.c) or are not OS-facing (src/xfns.c, pinned by
;;;         count in D1).  28 checks in all.  These are facts in a tracked
;;;         file, so a drift is a real FAIL.
;;;
;;;         D2 pins NAMES, not line numbers: a new leaf moves every line
;;;         below it, so a line constant invalidates itself at the next
;;;         imp.  The ordered name list survives imp-2 and still catches a
;;;         deletion or a re-order.
;;;   D5 -- the (m52) group is ABSENT from tool/run-tests.scm.  imp-1 adds
;;;         no behaviour, so brief.org section 5 says create the (m52)
;;;         group only when the first behaviour corpus lands (imp-2).  A
;;;         group that exists early is a real FAIL.  This corpus registers
;;;         a per-group minimum count.  That guard only proves the file
;;;         loaded past the guard line: it cannot catch a truncation that
;;;         removes a D1 or D2 check, because the guard sits below those
;;;         blocks (cr.org D4).  The advisory runner prints the real test
;;;         count, so a caller can still see a low count.
;;;
;;; The D1 tree-wide scm_c_public_ref measure counts LINES, not
;;; occurrences, so it matches a hand run of `grep -rc' (brief.org
;;; section 3; cr.org D5).
;;;
;;; Each check is printed as a PASS/FAIL line and turned into an ERT test
;;; so the harness counts it.  A read error is a real error, never a
;;; silent pass.  The corpus holds its own copy of every fact it pins.

(princ "=== m52 imp-1 audit suite ===\n")

(require 'imp-ert-report)

(defvar m52-imp1--root
  (file-name-as-directory
   (expand-file-name ".." (file-name-directory (or load-file-name
                                                       default-directory)))))

(defvar m52-imp1--registered 0
  "Total number of tracked-file checks this corpus has registered.  D5
pins a per-group minimum, so a truncated load cannot pass the gate with
no real checks.")

(defvar m52-imp1--group nil
  "The group that `m52-imp1--check' counts into: `d1', `d2', or nil.
D5 pins the D1 and D2 minima separately.")

(defvar m52-imp1--registered-d1 0
  "Number of D1 base-number checks registered.  D5 pins a minimum.")

(defvar m52-imp1--registered-d2 0
  "Number of D2 block-map checks registered.  D5 pins a minimum.")

(defun m52-imp1--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
the symbol `m52-imp1-absent' when REL does not exist.  docs/ is
gitignored, so a checkout without it must not crash the subprocess: an
unguarded `insert-file-contents' on an absent file would kill the
subprocess before ERT ever ran."
  (let ((path (expand-file-name rel m52-imp1--root)))
    (if (not (file-exists-p path))
        'm52-imp1-absent
      (with-temp-buffer
        (insert-file-contents path)
        (funcall fn)))))

(defun m52-imp1--contains-p (rel needle)
  "Non-nil when REL (repo-root-relative) contains NEEDLE."
  (m52-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (search-forward needle nil t))))

(defun m52-imp1--tracked-p (rel needle)
  "Non-nil when the TRACKED file REL contains NEEDLE.
A missing tracked file folds to nil, so `m52-imp1--check' prints FAIL:
an absent tracked file is a real error.  Contrast `m52-imp1--contains-p',
which returns `m52-imp1-absent' so a doc-check can tell absent from stale
for a gitignored record."
  (let ((hit (m52-imp1--contains-p rel needle)))
    (and (not (eq hit 'm52-imp1-absent)) (and hit t))))

(defun m52-imp1--lines (rel)
  "Count the newlines of REL the way `wc -l' does."
  (m52-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (search-forward "\n" nil t) (setq n (1+ n)))
        n))))

(defun m52-imp1--count (rel regexp)
  "Count the matches of REGEXP in REL."
  (m52-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (re-search-forward regexp nil t) (setq n (1+ n)))
        n))))

(defun m52-imp1--count-literal (rel needle)
  "Count the matches of the LITERAL NEEDLE in REL.
`m52-imp1--count' takes a regexp, so a needle that holds a `.` (such as
`#include \"guile.h\"') would also match `#include \"guileXh\"'.  Quote
the needle so the count is exact."
  (m52-imp1--count rel (regexp-quote needle)))

(defun m52-imp1--count-lines (rel needle)
  "Count the lines of REL that contain the LITERAL NEEDLE (`grep -c' style).
The brief.org section 3 measure is `grep -c', which counts matching
LINES, not occurrences.  A line that holds two occurrences counts once.
`m52-imp1--count-literal' counts occurrences instead, so the two methods
agree only while no line holds two occurrences."
  (m52-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (not (eobp))
          (when (save-excursion
                  (beginning-of-line)
                  (search-forward needle (line-end-position) t))
            (setq n (1+ n)))
          (forward-line 1))
        n))))

(defun m52-imp1--defun-count (rel)
  "Count the `^DEFUN (' lines of REL.
The `^' anchor stays a regexp, but the rest of the needle is quoted, so
the `(' and `\"' are not treated as regexp syntax."
  (m52-imp1--count rel (concat "^" (regexp-quote "DEFUN (\""))))

(defun m52-imp1--line-of (rel needle)
  "1-based line number of the first LITERAL NEEDLE in REL, or nil.
An absent REL, or an absent needle, yields nil, so the caller prints a
real FAIL (m4x-probe-failure-must-not-read-as-a-skip)."
  (m52-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (when (search-forward needle nil t)
        (line-number-at-pos (match-beginning 0))))))

(defun m52-imp1--defun-names (rel)
  "The DEFUN names of REL, in file order.  D2 pins this list instead of
a line constant: a new leaf moves every line below it, but it cannot
re-order or delete a block without this list changing."
  (m52-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((names '()))
        (while (re-search-forward "^DEFUN (\"\\([^\"]+\\)\"" nil t)
          (push (match-string 1) names))
        (nreverse names)))))

(defun m52-imp1--count-scm-ref ()
  "Count the lines with scm_c_public_ref over src/*.[chm].
This is the docs/m52-plan.org section 3 measure, `grep -rc
scm_c_public_ref src/*.[chm]' summed.  The count is of LINES, not
occurrences, so it matches a hand run of the brief.org section 3
command."
  (let ((total 0)
        (dir (expand-file-name "src" m52-imp1--root)))
    (dolist (f (directory-files dir t "\\.[chm]\\'"))
      (setq total (+ total (or (m52-imp1--count-lines f "scm_c_public_ref") 0))))
    total))

(defun m52-imp1--check (name ok)
  "Report and register one check on a TRACKED file.  OK is a boolean.
The D1/D2 callers pass `(eql N value)': when the source file is absent
the reader returns the symbol `m52-imp1-absent', so `eql' yields nil and
this prints FAIL.  The string-test callers use a fold-to-nil helper for
the same reason.  An absent src/ file is a real error, not a pass."
  (if (eq ok 'm52-imp1-absent)
      (princ (format "INFO m52/imp1/%s skipped (source file absent)\n" name))
    (progn
      (princ (format "%s m52/imp1/%s\n" (if ok "PASS" "FAIL") name))
      (setq m52-imp1--registered (1+ m52-imp1--registered))
      (cond ((eq m52-imp1--group 'd1)
             (setq m52-imp1--registered-d1 (1+ m52-imp1--registered-d1)))
            ((eq m52-imp1--group 'd2)
             (setq m52-imp1--registered-d2 (1+ m52-imp1--registered-d2))))
      (imp-register-bool-as-ert-test (format "m52-imp1/%s" name) (and ok t)))))

;;; --- D1. The base numbers (docs/m52-plan.org section 3) ---------------

(setq m52-imp1--group 'd1)

;; The five candidates of section 3.  Each is lines / DEFUNs /
;; scm_c_public_ref sites / the guile.h count.
(m52-imp1--check "xterm.c-lines-33110"
                 (eql 33110 (m52-imp1--lines "src/xterm.c")))
(m52-imp1--check "xterm.c-defuns-0"
                 (eql 0 (m52-imp1--defun-count "src/xterm.c")))
(m52-imp1--check "xterm.c-scm-ref-5"
                 (eql 5 (m52-imp1--count-literal "src/xterm.c" "scm_c_public_ref")))
(m52-imp1--check "xterm.c-guile.h-1"
                 (eql 1 (m52-imp1--count-literal "src/xterm.c" "#include \"guile.h\"")))
(m52-imp1--check "xfns.c-lines-10546"
                 (eql 10546 (m52-imp1--lines "src/xfns.c")))
(m52-imp1--check "xfns.c-defuns-54"
                 (eql 54 (m52-imp1--defun-count "src/xfns.c")))
(m52-imp1--check "xfns.c-scm-ref-0"
                 (eql 0 (m52-imp1--count-literal "src/xfns.c" "scm_c_public_ref")))
(m52-imp1--check "xfns.c-guile.h-0"
                 (eql 0 (m52-imp1--count-literal "src/xfns.c" "#include \"guile.h\"")))
(m52-imp1--check "pgtkterm.c-lines-7774"
                 (eql 7774 (m52-imp1--lines "src/pgtkterm.c")))
(m52-imp1--check "pgtkterm.c-defuns-0"
                 (eql 0 (m52-imp1--defun-count "src/pgtkterm.c")))
(m52-imp1--check "pgtkterm.c-scm-ref-4"
                 (eql 4 (m52-imp1--count-literal "src/pgtkterm.c" "scm_c_public_ref")))
(m52-imp1--check "pgtkterm.c-guile.h-1"
                 (eql 1 (m52-imp1--count-literal "src/pgtkterm.c" "#include \"guile.h\"")))
(m52-imp1--check "sysdep.c-lines-4950"
                 (eql 4950 (m52-imp1--lines "src/sysdep.c")))
(m52-imp1--check "sysdep.c-defuns-7"
                 (eql 7 (m52-imp1--defun-count "src/sysdep.c")))
(m52-imp1--check "sysdep.c-scm-ref-7"
                 (eql 7 (m52-imp1--count-literal "src/sysdep.c" "scm_c_public_ref")))
(m52-imp1--check "sysdep.c-guile.h-1"
                 (eql 1 (m52-imp1--count-literal "src/sysdep.c" "#include \"guile.h\"")))
(m52-imp1--check "lread.c-lines-3561"
                 (eql 3561 (m52-imp1--lines "src/lread.c")))
(m52-imp1--check "lread.c-defuns-19"
                 (eql 19 (m52-imp1--defun-count "src/lread.c")))
(m52-imp1--check "lread.c-scm-ref-2"
                 (eql 2 (m52-imp1--count-literal "src/lread.c" "scm_c_public_ref")))
(m52-imp1--check "lread.c-guile.h-1"
                 (eql 1 (m52-imp1--count-literal "src/lread.c" "#include \"guile.h\"")))
(m52-imp1--check "scm-c-public-ref-235"
                 (eql 235 (m52-imp1--count-scm-ref)))

;;; --- D2. The block map (docs/m52-plan.org section 3.1) ---------------
;;
;; The block definitions of a candidate are its ^DEFUN lines.  D2 pins
;; the NAMES in file order, not the line numbers.  The two candidates
;; that carry the A2 argument are src/sysdep.c (the M43 sibling
;; mechanism plus one thin time policy) and src/lread.c (the reader
;; already reads a Guile port).  src/xterm.c and src/pgtkterm.c have 0
;; DEFUNs (pinned by count in D1); src/xfns.c is not OS-facing (pinned
;; by count in D1).

(setq m52-imp1--group 'd2)

(defconst m52-imp1--sysdep-blocks
  '("get-internal-run-time"
    "--tty-get-mode"
    "--tty-set-mode"
    "--tty-flow-unlock"
    "--tty-get-size"
    "--tty-set-size"
    "--tty-mode-constants")
  "The 7 src/sysdep.c block names, in file order (section 3.1).")

(defconst m52-imp1--lread-blocks
  '("read-char"
    "read-event"
    "read-char-exclusive"
    "get-load-suffixes"
    "locate-file-internal"
    "eval-buffer"
    "eval-region"
    "elisp-loadhist-initialize"
    "read-from-buffer-guile"
    "lread--substitute-object-in-subtree"
    "find-symbol"
    "intern"
    "intern-soft"
    "unintern"
    "mapatoms"
    "obarray-make"
    "obarrayp"
    "obarray-clear"
    "internal--obarray-buckets")
  "The 19 src/lread.c block names, in file order (section 3.1).")

(defun m52-imp1--defuns-or-nil (rel)
  "The DEFUN names of REL, or nil when REL is absent.
An absent tracked file folds to nil, so every position check below
prints FAIL.  An absent src/ file is a real error."
  (let ((found (m52-imp1--defun-names rel)))
    (if (listp found) found '())))

;; one check per src/sysdep.c block: the name AND its position must hold.
(let ((i 0)
      (found (m52-imp1--defuns-or-nil "src/sysdep.c")))
  (dolist (name m52-imp1--sysdep-blocks)
    (m52-imp1--check (format "sysdep-block-%02d-%s" (1+ i) name)
                     (equal name (nth i found)))
    (setq i (1+ i))))
;; the whole list, so an EXTRA block is caught too.
(m52-imp1--check "sysdep-block-list-exact-7"
                 (equal m52-imp1--sysdep-blocks
                        (m52-imp1--defuns-or-nil "src/sysdep.c")))

;; one check per src/lread.c block: the name AND its position must hold.
(let ((i 0)
      (found (m52-imp1--defuns-or-nil "src/lread.c")))
  (dolist (name m52-imp1--lread-blocks)
    (m52-imp1--check (format "lread-block-%02d-%s" (1+ i) name)
                     (equal name (nth i found)))
    (setq i (1+ i))))
;; the whole list, so an EXTRA block is caught too.
(m52-imp1--check "lread-block-list-exact-19"
                 (equal m52-imp1--lread-blocks
                        (m52-imp1--defuns-or-nil "src/lread.c")))

;;; --- D5. The group state and the min-count guard ---------------------

;; close the D2 group so the guards below count into no group.
(setq m52-imp1--group nil)

;; imp-1 adds no behaviour, so brief.org section 5 says do NOT create the
;; (m52) group yet.  A group that exists at imp-1 is a real FAIL.
(m52-imp1--check "reg/m52-group-absent"
                 (null (m52-imp1--contains-p "tool/run-tests.scm"
                                             "(group (m52)")))
;; The (m51) group is the last milestone group and stays present.
;; `m52-imp1--tracked-p' folds an absent tracked file to nil, so this
;; prints FAIL (not the INFO of an absent file) if tool/run-tests.scm
;; disappears (cr.org D3).
(m52-imp1--check "reg/m51-group-present"
                 (m52-imp1--tracked-p "tool/run-tests.scm"
                                      "(group (m51)"))
;; the fold-to-nil helper itself: a non-existent path stands in for an
;; absent tracked file, so the check must print FAIL, not INFO.
(m52-imp1--check "reg/absent-tracked-file-fails"
                 (null (m52-imp1--tracked-p "src/m52-imp1-no-such-file.c"
                                            "needle")))

;; An --filter that matches no group already reports exit 0 with 0 tests,
;; so a green m52 gate proves nothing until the corpus exists and its
;; checks really register.  These guards only prove the file loaded past
;; this line.  They CANNOT catch a truncation that removes D1 or D2: the
;; guards sit below those blocks, so a truncation that drops a D1/D2
;; check also drops the guard (cr.org D4).  The advisory runner prints
;; the real test count, so a caller can still see a low count.  The
;; counts are stable because every check is registered at load time.
;; D1 holds 21 checks; D2 holds 28 (7 sysdep positions + the exact-7 list
;; + 19 lread positions + the exact-19 list).
(m52-imp1--check "reg/min-d1-checks-21"
                 (>= m52-imp1--registered-d1 21))
(m52-imp1--check "reg/min-d2-checks-28"
                 (>= m52-imp1--registered-d2 28))

(princ (format "=== m52 imp-1 audit suite done (%d tracked checks: D1 %d, D2 %d) ===\n"
               m52-imp1--registered m52-imp1--registered-d1 m52-imp1--registered-d2))
