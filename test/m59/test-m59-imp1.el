;;; test-m59-imp1.el --- M59 imp-1 src/xfaces.c face surface audit corpus.
;;;
;;; M59 imp-1 is the src/xfaces.c face-surface AUDIT (docs/m59-plan.org).
;;; It is docs only: the C delta is 0 and the Scheme delta is 0.  It
;;; measures the surface at HEAD, classes every DEFUN of src/xfaces.c
;;; MOVE / STAYS C / NOT PROVEN, and records the A1 verdict with ONE
;;; named candidate (face-attribute-relative-p, :4173 at imp-1) and ONE
;;; runner-up (bitmap-spec-p, :813 at imp-1).
;;;
;;; M59 imp-3 LANDED the named candidate and re-pinned the surface rows
;;; of S1 and S2: the DEFUN was at :4197, the file was 7,708 lines,
;;; src/xfaces.c held 1 scm_c_public_ref LINE and the tree-wide count was
;;; 266 OCCURRENCES.  M59 imp-4 LANDED the RUNNER-UP and re-pinned the
;;; same rows again: the file is 7,741 lines, src/xfaces.c holds 2
;;; scm_c_public_ref LINES (2 dispatchers) and 21 direct scm_* LINES, the
;;; tree-wide count is 267 OCCURRENCES, and the inline decision of
;;; bitmap-spec-p is GONE too (the type tests stay C).
;;;
;;; It pins these groups:
;;;
;;;   S1 -- the re-measured surface of docs/m59-plan.org section 2 (the
;;;         base e9f87b051 as an ANCESTOR of HEAD, the src/xfaces.c
;;;         numbers, the 16 direct scm_* lines, the tree-wide
;;;         scm_c_public_ref count, the pty-driver.py case pin, and the
;;;         corpus directory).  S1 holds 9 checks.  The (m59) group
;;;         registration is pinned by S4 and NOT here: a duplicate
;;;         needle inflates a count floor and proves nothing new.
;;;   S2 -- the row map: the named candidate and its C site count, the
;;;         runner-up and its 5 call sites, the 5 MOVE rows, the class
;;;         counts (MOVE 5, STAYS C 26, NOT PROVEN 2, total 33), the 2
;;;         NOT PROVEN blockers, one STAYS C witness per class reason (a
;;;         face-cache read, a C static, a C FILE *, a C hook), the
;;;         already-landed color-spec row, and the boundary rule
;;;         do-not-give-scheme-a-C-descriptor by name in the TRACKED C
;;;         source.  S2 holds 9 checks.
;;;   S3 -- the real path: test/pty-driver.py --selftest and the built
;;;         src/emacs on a real PTY through the EXISTING case
;;;         m56-imp2/tty-init-e2e.  NO new PTY case in imp-1.  A
;;;         missing python3, a missing built src/emacs, or no PTY is an
;;;         explicit INFO skip, never a pass.  On a result that is
;;;         neither PASS nor INFO the check RETRIES once, then prints
;;;         both runs.  S3 holds 2 checks.
;;;   S4 -- the registration: the corpus is in the (m59) group of
;;;         tool/run-tests.scm, after the (m58) group, and the (m58)
;;;         group stays present.  S4 holds 4 checks.
;;;   S5 -- the guards: 4 checks -- one per-group min-count guard for
;;;         each of S1 .. S4.  The in-process group-total
;;;         `ert-deftest' is a separate test in the same phase; it is
;;;         NOT one of the 4 counted checks (the floor is 28 checks plus
;;;         that deftest = 29).
;;;
;;; This corpus reads TRACKED files only (src/, tool/run-tests.scm,
;;; test/pty-driver.py).  It does NOT read docs/
;;; (docs/kb.org test-must-not-read-docs): a gitignored record can only
;;; pass or skip, so a record check proves nothing.
;;;
;;; A read error is a real error, never a silent pass.  An absent
;;; TRACKED file is a real FAIL, not a pass (docs/m59-plan.org).  A
;;; missing `git', `python3' binary or a missing PTY is an explicit INFO
;;; skip, never a pass.  Every check registers a real ERT test via
;;; imp-register-bool-as-ert-test, so the harness parses the ERT output
;;; and the exit code is correct.
;;;
;;; Every pin states its MEASURE UNIT: `m59-imp1--grep-c' counts LINES
;;; (the unit of `grep -c'), `m59-imp1--count' counts OCCURRENCES (the
;;; unit of `grep -o | wc -l'), and `m59-imp1--lines' counts NEWLINES
;;; (the unit of `wc -l').  MEASURED after M59 imp-3: the token `guile'
;;; matches 8 OCCURRENCES and 8 LINES in src/xfaces.c.

(princ "=== m59 imp-1 src/xfaces.c face surface audit suite ===\n")

(require 'imp-ert-report)

(defvar m59-imp1--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))
(defvar m59-imp1--registered 0
  "Total number of checks this corpus has registered.")
(defvar m59-imp1--group nil
  "The group that `m59-imp1--check' counts into: `s1' .. `s5', or nil.")
(defvar m59-imp1--counts nil
  "Alist of (GROUP . COUNT) for the registered checks.")

(defun m59-imp1--group-count (group)
  "Number of checks registered so far in GROUP."
  (or (cdr (assq group m59-imp1--counts)) 0))

(defun m59-imp1--bump-group ()
  "Count one check into `m59-imp1--group'."
  (when m59-imp1--group
    (let ((cell (assq m59-imp1--group m59-imp1--counts)))
      (if cell
          (setcdr cell (1+ (cdr cell)))
        (push (cons m59-imp1--group 1) m59-imp1--counts)))))

(defun m59-imp1--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
the symbol `m59-imp1-absent' when REL does not exist.  `case-fold-search'
is bound to nil: the elisp default is t, which folds `Guile' into
`guile'.  MEASURED: with the default, a count of `guile' in
src/xfaces.c gives 13 matches, but `grep -c guile' gives 7 lines.  Every
pin in this corpus is case-SENSITIVE, like its grep command."
  (let ((path (expand-file-name rel m59-imp1--root)))
    (if (not (file-exists-p path))
        'm59-imp1-absent
      (with-temp-buffer
        (insert-file-contents path)
        (let ((case-fold-search nil))
          (funcall fn))))))

(defun m59-imp1--contains-p (rel needle)
  "Non-nil when the TRACKED file REL contains NEEDLE.  An absent file
folds to nil, so the check prints FAIL: an absent TRACKED file is a real
error, not a pass (docs/m59-plan.org)."
  (let ((hit (m59-imp1--with rel
               (lambda ()
                 (goto-char (point-min))
                 (search-forward needle nil t)))))
    (and (not (eq hit 'm59-imp1-absent)) (and hit t))))

(defun m59-imp1--holds-none (rel needles)
  "Non-nil when the TRACKED file REL holds NO needle of NEEDLES.  An
absent file returns the symbol `m59-imp1-absent', which fails the check."
  (let ((res (m59-imp1--with rel
               (lambda ()
                 (let ((none t))
                   (dolist (needle needles)
                     (goto-char (point-min))
                     (when (search-forward needle nil t) (setq none nil)))
                   none)))))
    (if (eq res 'm59-imp1-absent) res res)))

(defun m59-imp1--holds-all (rel needles)
  "Non-nil when the TRACKED file REL holds every NEEDLE.  REL is read
once, so a multi-needle check does not re-read the file per needle."
  (m59-imp1--with rel
    (lambda ()
      (let ((all t))
        (dolist (needle needles)
          (goto-char (point-min))
          (unless (search-forward needle nil t) (setq all nil)))
        all))))

(defun m59-imp1--live-p (rel needle)
  "Non-nil when the TRACKED file REL holds NEEDLE on a line that is NOT
commented out.  A needle that sits only on a comment registers no test,
so this skips a line whose first non-blank character is `;'."
  (m59-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((hit nil))
        (while (and (not hit) (search-forward needle nil t))
          (setq hit (save-excursion
                      (goto-char (line-beginning-position))
                      (not (looking-at-p "[ \t]*;")))))
        hit))))

(defun m59-imp1--pty-case-pins ()
  "Read the `test/pty-driver.py' case-count pins as (TOTAL . SUM).
TOTAL is the `total-case-count' pin; SUM is the sum of the per-group
`-case-count' pins.  Return nil when a pin is absent.  A plain string
search for the pin line proves nothing about the number of cases, so the
corpus checks that the two numbers agree."
  (m59-imp1--with "test/pty-driver.py"
    (lambda ()
      (goto-char (point-min))
      (let ((total nil) (sum 0) (n 0))
        (while (re-search-forward "check(\"\\([a-z0-9-]*-case-count\\)\", " nil t)
          (let ((name (match-string 1))
                (pin (progn (re-search-forward "), \\([0-9]+\\))" nil t)
                           (match-string 1))))
            (if (string= name "total-case-count")
                (setq total (string-to-number (or pin "0")))
              (setq sum (+ sum (string-to-number (or pin "0"))))
              (setq n (1+ n)))))
        (and total (> n 0) (cons total sum))))))

(defun m59-imp1--ordered-p (rel needles)
  "Non-nil when the TRACKED file REL holds every NEEDLE in the GIVEN
ORDER: each search starts after the previous match."
  (m59-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((all t))
        (dolist (needle needles)
          (when all
            (unless (search-forward needle nil t) (setq all nil))))
        all))))

(defun m59-imp1--exists-p (rel)
  "Non-nil when the TRACKED file REL (repo-root-relative) exists."
  (file-exists-p (expand-file-name rel m59-imp1--root)))

(defun m59-imp1--grep-c (rel regexp)
  "Count the LINES of REL that match REGEXP, the unit of `grep -c'.
A line with 3 matches counts 1, not 3.  MEASURED on src/xfaces.c:
`scm_' has 33 occurrences but only 11 lines."
  (m59-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (not (eobp))
          (when (re-search-forward regexp (line-end-position) t)
            (setq n (1+ n)))
          (forward-line 1))
        n))))

(defun m59-imp1--count (rel regexp)
  "Count the OCCURRENCES of REGEXP in REL, the unit of `grep -o | wc -l'.
This is NOT the unit of `grep -c': use `m59-imp1--grep-c' for a pin
whose brief command is `grep -c'."
  (m59-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (re-search-forward regexp nil t) (setq n (1+ n)))
        n))))

(defun m59-imp1--lines (rel)
  "Count the NEWLINES of REL, the unit of `wc -l'."
  (m59-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (search-forward "\n" nil t) (setq n (1+ n)))
        n))))

(defun m59-imp1--line-of (rel regexp)
  "Return the 1-based line number of the first REGEXP match in REL, or
nil when REGEXP does not match.  The reader returns the symbol
`m59-imp1-absent' when REL does not exist, so the caller's `eql' folds
to nil and the check FAILS."
  (m59-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (when (re-search-forward regexp nil t)
        (let ((end (match-beginning 0)) (n 1))
          (goto-char (point-min))
          (while (search-forward "\n" end t) (setq n (1+ n)))
          n)))))

(defun m59-imp1--line-number-here ()
  "Return the 1-based line number of point in the current buffer."
  (let ((target (point)))
    (save-excursion
      (goto-char (point-min))
      (let ((n 1))
        (while (search-forward "\n" target t) (setq n (1+ n)))
        n))))

(defun m59-imp1--sites (rel regexp)
  "Return the 1-based line numbers of the matches of REGEXP in REL,
EXCEPT a line whose first non-blank text is `DEFUN ('.  So the result is
the caller map of a subr, not its own definition.  A symbol (an absent
file) is returned unchanged, so the caller's `equal' folds to nil."
  (m59-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((sites nil))
        (while (re-search-forward regexp nil t)
          (let ((line (m59-imp1--line-number-here))
                (defun-line-p (save-excursion
                                (goto-char (line-beginning-position))
                                (looking-at-p "[ \t]*DEFUN ("))))
            (unless (or defun-line-p (memq line sites))
              (push line sites))))
        (nreverse sites)))))

(defun m59-imp1--count-scm-ref ()
  "Count scm_c_public_ref over src/*.[ch] (the docs/m59-plan.org
tree-wide measure, `grep -h scm_c_public_ref src/*.c src/*.h | wc -l').
The selector is .c and .h ONLY, to match the brief command; the .m files
(Objective-C, out of scope) are not read.  Unit: OCCURRENCES, which is
the unit of the `grep -h ... | wc -l' pipeline."
  (let ((total 0)
        (dir (expand-file-name "src" m59-imp1--root)))
    (dolist (f (directory-files dir t "\\.[ch]\\'"))
      (setq total (+ total (or (m59-imp1--count f "scm_c_public_ref") 0))))
    total))

(defun m59-imp1--run (prog args)
  "Run PROG with ARGS in a subprocess from the repo root and return its
stdout / stderr as a string, or the symbol `m59-imp1-prog-absent' when
PROG is not on PATH."
  (if (not (executable-find prog))
      'm59-imp1-prog-absent
    (let ((buf (get-buffer-create " *m59-imp1-run*"))
          (default-directory m59-imp1--root))
      (unwind-protect
          (progn
            (with-current-buffer buf (erase-buffer))
            (apply #'call-process prog nil buf nil args)
            (with-current-buffer buf
              (buffer-substring-no-properties (point-min) (point-max))))
        (kill-buffer buf)))))

(defun m59-imp1--ancestor-p (ancestor descendant)
  "Non-nil when ANCESTOR is an ancestor of DESCENDANT in the repo at
`m59-imp1--root'.  Return the symbol `m59-imp1-prog-absent' when the
`git' binary is not on PATH, and nil when `git' fails.  A committed
corpus must NOT pin the running HEAD to a literal base commit: when
imp-1 is committed, HEAD moves to the imp commit, so a hard equality
check against the base always fails.  The ancestry relation stays true
when the branch advances."
  (if (not (executable-find "git"))
      'm59-imp1-prog-absent
    (let ((default-directory m59-imp1--root))
      (zerop (call-process "git" nil nil nil
                           "merge-base" "--is-ancestor"
                           ancestor descendant)))))

(defun m59-imp1--move-row-regexp ()
  "The regexp that matches the 5 MOVE rows of the row map.  The set is
measured in docs/m59-plan.org section 4: 4 fresh candidates plus the 1
row that ALREADY LANDED (color-values-from-color-spec).
merge-face-attribute and color-distance are NOT in this set: the first
calls the Lisp engine (safe_calln at :2280), the second reads a struct
frame and a C hook and calls the metric (:4777, :4782, :4801).  Rule 5.6
of brief.org classes both NOT PROVEN."
  (concat "^DEFUN (\""
          "\\(bitmap-spec-p"
          "\\|color-values-from-color-spec"
          "\\|internal-set-lisp-face-attribute-from-resource"
          "\\|face-attribute-relative-p"
          "\\|internal-lisp-face-attribute-values"
          "\\)\""))

(defun m59-imp1--check (name ok)
  "Report and register one check on a TRACKED file.  OK is a boolean.
When the source file is absent the reader returns the symbol
`m59-imp1-absent', so `eql' yields nil and this prints FAIL.  Either way
this registers a real FAILING ERT test, so an absent TRACKED file is a
real error, not a pass."
  (let* ((absent (eq ok 'm59-imp1-absent))
         (pass (and (not absent) (and ok t))))
    (if absent
        (princ (format "FAIL m59/imp1/%s (source file absent)\n" name))
      (princ (format "%s m59/imp1/%s\n" (if pass "PASS" "FAIL") name)))
    (setq m59-imp1--registered (1+ m59-imp1--registered))
    (m59-imp1--bump-group)
    (imp-register-bool-as-ert-test (format "m59-imp1/%s" name) pass)))

(defun m59-imp1--info-skip (name reason)
  "Register one explicit INFO skip, counted into the current group.  A
host limit is a skip, never a pass (docs/m59-plan.org)."
  (princ (format "INFO m59/imp1/%s %s\n" name reason))
  (setq m59-imp1--registered (1+ m59-imp1--registered))
  (m59-imp1--bump-group)
  (imp-register-skip-as-ert-test (format "m59-imp1/%s" name) reason))

;;; --- S1. The measured surface (docs/m59-plan.org section 2) -------

;; One check per row of the surface table.  Row 1 (HEAD) checks that the
;; base commit is an ANCESTOR of the running HEAD: a committed corpus
;; cannot pin HEAD to a literal, because HEAD moves to the imp commit.  A
;; missing `git' is an explicit INFO skip, never a pass.  The source rows
;; re-measure the tree at HEAD; do NOT copy a planning number.

(setq m59-imp1--group 's1)

(let ((ok (m59-imp1--ancestor-p "e9f87b051" "HEAD")))
  (if (eq ok 'm59-imp1-prog-absent)
      (m59-imp1--info-skip "head-e9f87b051" "no git binary on PATH")
    (m59-imp1--check "head-e9f87b051" ok)))

;; Unit: LINES (`wc -l').  M59 imp-3 adds 23 net lines (the dispatcher,
;; the include, and the shorter body); M59 imp-4 adds 33 net lines (the
;; second dispatcher and its comment).
(m59-imp1--check "xfaces.c-lines-7741"
                 (eql 7741 (m59-imp1--lines "src/xfaces.c")))
;; Unit: LINES (`grep -c "^DEFUN ("').
;; M61 imp-2 re-pin: the 2 new leaves, the shared guard and the routed
;; flush/termscript sites moved the surface.  MEASURED on this tree.
(m59-imp1--check "xfaces.c-defun-count-33"
                 (eql 33 (m59-imp1--grep-c "src/xfaces.c" "^DEFUN (")))
;; Unit: LINES (`grep -c scm_c_public_ref').  2 after the M59 imp-4 MOVE:
;; each of the 2 dispatchers resolves (emacs faces) one time.
(m59-imp1--check "xfaces.c-scm-ref-2"
                 (eql 2 (m59-imp1--grep-c "src/xfaces.c" "scm_c_public_ref")))
;; Unit: OCCURRENCES (`grep -h ... | wc -l').
(m59-imp1--check "tree-wide-scm-ref-270"
                 (eql 270 (m59-imp1--count-scm-ref)))
;; Unit: LINES (`grep -c guile' = 8).  The lines of Guile coupling: the
;; 2 includes (:229, :230), the 2 real seams (:1047
;; guile_parse_color_spec, :3995 guile_parse_face_bool_attribute), and 4
;; support lines.  The 2 seams are pinned by name too.
(m59-imp1--check "xfaces.c-guile-lines-8"
                 (and (eql 8 (m59-imp1--grep-c "src/xfaces.c" "guile"))
                      (m59-imp1--contains-p "src/xfaces.c"
                                            "guile_parse_color_spec (spec)")
                      (m59-imp1--contains-p "src/xfaces.c"
                                            "guile_parse_face_bool_attribute")))
;; Unit: LINES (`grep -c scm_ src/xfaces.c' = 21).  The file holds 21
;; lines with a DIRECT scm_* call: the 11 old sites, the 5 lines of the
;; M59 imp-3 dispatcher (scm_c_public_ref, scm_is_true / SCM_CALL_3, and
;; the 3 scm_from_bool arguments), and the 5 lines of the M59 imp-4
;; dispatcher (scm_c_public_ref, scm_is_true / SCM_CALL_4, and the 4
;; scm_from_bool / scm_from_ptrdiff_t arguments).  So "2
;; scm_c_public_ref" does not state the full size of the Guile coupling.
(m59-imp1--check "xfaces.c-scm-lines-21"
                 (eql 21 (m59-imp1--grep-c "src/xfaces.c" "scm_")))
;; M59 imp-1 adds NO PTY case.  The counted surface stays 32.  The group
;; pins must add up to the total, so a group pin that moves without the
;; total FAILS.
(m59-imp1--check "pty-driver-cases-42"
                 (let ((pins (m59-imp1--pty-case-pins)))
                   (and (consp pins)
                        (eql 42 (car pins))
                        (eql (car pins) (cdr pins)))))
(m59-imp1--check "corpus-dir-present"
                 (and (m59-imp1--exists-p "test/m59")
                      (m59-imp1--exists-p "test/m59/test-m59-imp1.el")))

;;; --- S2. The row map (docs/m59-plan.org section 3 and 4) ----------

;; The row map classes all 33 DEFUN of src/xfaces.c.  A MOVE row holds a
;; plain-value decision AND a batch-mode observable.  A STAYS C row must
;; read C state to decide.  A row whose decision needs the Lisp engine or
;; a C hook is NOT PROVEN.  A passthrough is not a port
;; (passthrough-leaf-is-not-a-port).

(setq m59-imp1--group 's2)

;; The NAMED candidate face-attribute-relative-p is now the FIRST LANDED
;; MOVE row.  M59 imp-3 landed it: the DEFUN moved to :4197 (:4230
;; after the M59 imp-4 MOVE), C keeps the
;; 3 type tests, and the combine is in Scheme ((emacs faces),
;; face-attribute-relative-verdict).  The inline decision is GONE.
(m59-imp1--check "candidate-face-attribute-relative-p"
                 (and (eql 4230 (m59-imp1--line-of
                                 "src/xfaces.c"
                                 "^DEFUN (\"face-attribute-relative-p\""))
                      (m59-imp1--holds-all
                       "src/xfaces.c"
                       '("bool a = EQ (value, Qunspecified) || EQ (value, QCignore_defface);"
                         "bool b = EQ (attribute, QCheight);"
                         "bool c = FIXNUMP (value);"
                         "return m59_face_attribute_relative_p_scheme (a, b, c);"
                         "scm_c_public_ref (\"emacs faces\","
                         "\"face-attribute-relative-verdict\");"))
                      (m59-imp1--holds-none
                       "src/xfaces.c"
                       '("return FIXNUMP (value) ? Qnil : Qt;"
                         "if (EQ (value, Qunspecified) || (EQ (value, QCignore_defface)))"))))

;; The candidate has 0 internal C callers: src/xfaces.c holds only the
;; DEFUN, and src/globals.h holds only the EXFUN.  So a port adds no
;; crossing on a C path.  Unit: OCCURRENCES.
(m59-imp1--check "candidate-no-C-caller"
                 (and (null (m59-imp1--sites "src/xfaces.c"
                                             "Fface_attribute_relative_p"))
                      (eql 1 (m59-imp1--count "src/globals.h"
                                              "Fface_attribute_relative_p"))))

;; The RUNNER-UP bitmap-spec-p (:843 ... :893 after the M59 imp-4 MOVE,
;; :813 ... :860 at imp-1) has 5 internal C callers,
;; so it ranks second.  The 5 caller lines are measured.
(m59-imp1--check "runner-up-bitmap-spec-p"
                 (and (eql 843 (m59-imp1--line-of
                                "src/xfaces.c" "^DEFUN (\"bitmap-spec-p\""))
                      (equal '(911 1434 1948 2918 3617)
                             (m59-imp1--sites "src/xfaces.c"
                                              "Fbitmap_spec_p"))))

;; The 5 MOVE rows, by name, in src/xfaces.c.  Unit: OCCURRENCES.
(m59-imp1--check "move-rows-5"
                 (eql 5 (m59-imp1--count "src/xfaces.c"
                                         (m59-imp1--move-row-regexp))))

;; The class counts sum to 33: MOVE 5 (4 fresh + 1 landed), STAYS C 26,
;; NOT PROVEN 2.  The class of a row is a judgement from the C text, so
;; the corpus pins the DEFUN total and the MOVE set; the 2 NOT PROVEN
;; rows are pinned by name and by their blocker.  Unit: LINES for the
;; DEFUN total, OCCURRENCES for the MOVE set.
(m59-imp1--check "class-counts-sum-33"
                 (let ((total (m59-imp1--grep-c "src/xfaces.c" "^DEFUN ("))
                       (move (m59-imp1--count "src/xfaces.c"
                                              (m59-imp1--move-row-regexp)))
                       (not-proven 2))
                   (and (eql 33 total)
                        (eql 5 move)
                        (eql 2 not-proven)
                        (eql 26 (- total move not-proven)))))

;; The 2 NOT PROVEN rows of the row map, with their blocker in the
;; TRACKED C source.  Rule 5.6 of brief.org: a row is MOVE only if a
;; plain value crosses the seam AND an observable exists.  Row 16
;; merge-face-attribute (:4251 after the M59 imp-4 MOVE) calls the Lisp
;; engine at :2314 (safe_calln); row 24 color-distance (:4821) reads a
;; struct frame, a C hook, and calls the metric (:4834).
(m59-imp1--check "not-proven-rows-2"
                 (and (eql 4251 (m59-imp1--line-of
                                 "src/xfaces.c"
                                 "^DEFUN (\"merge-face-attribute\""))
                      (eql 4821 (m59-imp1--line-of
                                 "src/xfaces.c" "^DEFUN (\"color-distance\""))
                      (eql 2314 (m59-imp1--line-of
                                 "src/xfaces.c" "result = safe_calln (from, to)"))
                      (m59-imp1--holds-all
                       "src/xfaces.c"
                       '("struct frame *f = decode_live_frame (frame);"
                         "return call2 (metric,"))))

;; One STAYS C witness per class reason, in the TRACKED C source: a face
;; cache read (rows 10, 17, 21, 22, 23), a C static (rows 9, 27, 30), a
;; C FILE * (row 31), and a C hook (rows 5, 6).
(m59-imp1--check "stays-c-witnesses"
                 (m59-imp1--holds-all
                  "src/xfaces.c"
                  '("lface_equal_p (XVECTOR (lface1)->contents,"
                    "static int next_lface_id;"
                    "static int font_sort_order[4];"
                    "FILE *fp;"
                    "FRAME_TERMINAL (f)->defined_color_hook")))

;; The color-spec row ALREADY LANDED: the body returns the Guile parser.
;; Do not port it again.
(m59-imp1--check "already-landed-color-spec"
                 (eql 1080 (m59-imp1--line-of
                            "src/xfaces.c" "guile_parse_color_spec (spec)")))

;; The boundary rule do-not-give-scheme-a-C-descriptor, by name in the
;; TRACKED C source.  M61 imp-2b (milestone.org findings F2): the
;; measured LINE NUMBER is REMOVED, not re-pinned.  The token presence
;; check stays: it is a real runtime token, not a source-text line pin.
(m59-imp1--check "boundary-rule-token"
                 (m59-imp1--contains-p "src/term.c"
                                       "no Guile port owns a FILE *"))

;;; --- S3. The real path (docs/m59-plan.org section 7) --------------

;; The module-load probe is NOT proof.  The real path is the built
;; src/emacs on a real PTY: test/pty-driver.py boots the child emacs,
;; which runs init_tty.  Imp-1 adds NO new PTY case; it reuses
;; m56-imp2/tty-init-e2e.  A missing python3, a missing built src/emacs,
;; or a missing PTY is an explicit INFO skip, NEVER a pass.

(setq m59-imp1--group 's3)

(let ((out (m59-imp1--run "python3"
                          (list "test/pty-driver.py" "--selftest"))))
  (if (eq out 'm59-imp1-prog-absent)
      (m59-imp1--info-skip "pty-driver-selftest" "no python3 binary on PATH")
    (m59-imp1--check "pty-driver-selftest"
                     (and (string-match-p "SELFTEST OK" out) t))))

(let ((emacs (expand-file-name "src/emacs" m59-imp1--root)))
  (cond
   ((not (and (file-exists-p emacs) (file-executable-p emacs)))
    (m59-imp1--info-skip "pty-real-path-tty-init" "no built src/emacs"))
   (t
    (let* ((args (list "test/pty-driver.py" "--emacs" emacs "--group" "m56-imp2"))
           (out1 (m59-imp1--run "python3" args))
           (done (or (eq out1 'm59-imp1-prog-absent)
                     (string-match-p "PASS m56-imp2/tty-init-e2e" out1)
                     (string-match-p "INFO m56-imp2/tty-init-e2e" out1)))
           (out2 (unless done (m59-imp1--run "python3" args)))
           (out (or out2 out1)))
      (cond
       ((eq out1 'm59-imp1-prog-absent)
        (m59-imp1--info-skip "pty-real-path-tty-init" "no python3 binary on PATH"))
       ((string-match-p "PASS m56-imp2/tty-init-e2e" out)
        (m59-imp1--check "pty-real-path-tty-init" t))
       ((string-match-p "INFO m56-imp2/tty-init-e2e" out)
        (m59-imp1--info-skip "pty-real-path-tty-init" "no PTY on this host"))
       (t
        (princ (format "m59 imp1 PTY run 1 (neither PASS nor INFO):\n%s\n" out1))
        (princ (format "m59 imp1 PTY run 2 (retry):\n%s\n" out2))
        (m59-imp1--check "pty-real-path-tty-init" nil)))))))

;;; --- S4. The registration -------------------------------------------

(setq m59-imp1--group 's4)

(m59-imp1--check "run-tests-m59-imp1"
                 (m59-imp1--live-p "tool/run-tests.scm"
                                   "test/m59/test-m59-imp1.el"))
(m59-imp1--check "run-tests-m59-group"
                 (m59-imp1--live-p "tool/run-tests.scm" "(group (m59)"))
(m59-imp1--check "run-tests-m59-after-m58"
                 (m59-imp1--ordered-p "tool/run-tests.scm"
                                      '("(group (m58)" "(group (m59)")))
(m59-imp1--check "run-tests-m58-present"
                 (m59-imp1--live-p "tool/run-tests.scm" "(group (m58)"))

;;; --- S5. The guards -------------------------------------------------

;; An --filter that matches no group already reports exit 0 with 0
;; tests, so a green m59 gate proves nothing until the corpus exists and
;; its checks really register.  These guards fail when the corpus body
;; is truncated or its core checks do not run.  S1 holds 9 checks, S2
;; holds 9, S3 holds 2, and S4 holds 4.

(setq m59-imp1--group 's5)

(m59-imp1--check "reg/min-s1-checks-9" (>= (m59-imp1--group-count 's1) 9))
(m59-imp1--check "reg/min-s2-checks-9" (>= (m59-imp1--group-count 's2) 9))
(m59-imp1--check "reg/min-s3-checks-2" (>= (m59-imp1--group-count 's3) 2))
(m59-imp1--check "reg/min-s4-checks-4" (>= (m59-imp1--group-count 's4) 4))

;;; --- The group-total check ------------------------------------------

;; The measured count of m59-imp1 tests is 29: 28 registered checks
;; (S1 9, S2 9, S3 2, S4 4, S5 4) plus the group-total deftest itself.
;; The S3 checks may fold to a controlled INFO skip on a host with no
;; python3 / no built src/emacs / no PTY, and a controlled skip is still
;; a registered test, so the floor holds either way.

(defvar m59-imp1--min-gate-total 29
  "The exact number of m59-imp1 ERT tests: 28 registered checks (S1 9,
S2 9, S3 2, S4 4, S5 4) plus the group-total deftest itself.")

(ert-deftest m59-imp1/gate-m59-total ()
  "The m59-imp1 corpus registers at least its docs-independent floor."
  (should (>= (length (ert-select-tests "^m59-imp1" t))
              m59-imp1--min-gate-total)))

(princ (format "=== m59 imp-1 suite done (%d checks; s1 %d, s2 %d, s3 %d, s4 %d, s5 %d) ===\n"
               m59-imp1--registered
               (m59-imp1--group-count 's1)
               (m59-imp1--group-count 's2)
               (m59-imp1--group-count 's3)
               (m59-imp1--group-count 's4)
               (m59-imp1--group-count 's5)))
