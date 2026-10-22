;;; test-m60-imp1.el --- M60 imp-1 standalone-load boundary audit corpus.
;;;
;;; M60 imp-1 is the standalone-load boundary AUDIT (docs/m60-plan.org).
;;; It is docs only: the C delta is 0 and the Scheme delta is 0.  It
;;; measures 3 subjects on the real plain-`guile' path -- the ordered
;;; empty cells, the `(language emacs-elisp)' registration, and the C
;;; bootstrap cells -- and records the verdict with ONE named candidate
;;; (the (language emacs-elisp spec) registration) and ONE runner-up
;;; (the `provide' cell with the `features' variable).
;;;
;;; It pins these groups:
;;;
;;;   S1 -- the re-measured surface of docs/m60-plan.org section 2 (the
;;;         base 3603a6795 as an ANCESTOR of HEAD, the 6 line counts,
;;;         the 3 loader.scm grep LINE counts, the tree-wide
;;;         scm_c_public_ref OCCURRENCE count, the test/mod file count,
;;;;         and the mod/emacs-elisp ENTRY count).  S1 holds 11 checks.
;;;         The (m60) group registration is pinned by S5 and NOT here:
;;;         a duplicate needle inflates a count floor.
;;;   S2 -- the ordered cell list: the 11 guarded installs in call
;;;         order, the 2 unguarded installs, the 4 variable binds, the
;;;         measured stop point cell (`provide'), the measured
;;;         provide/require asymmetry, the `features' DEFVAR, and the 2
;;;;         evaluator cells that a pure stub can not pass.  S2 holds 6
;;;         checks.
;;;   S3 -- the registration: the 6 `lookup-language' sites, the prelude
;;;         monkey-patch range and its 2 patched modules, the C
;;;         scm_c_resolve_module ("emacs-elisp spec"), the circularity
;;;         of mod/emacs-elisp/spec.scm that makes the verdict A2, and
;;;         the narrow catch at loader.scm :1086.  S3 holds 5 checks.
;;;   S4 -- the C bootstrap rows: the module resolution sequence, the 2
;;;         Scheme accessor refs, the SCM_CALL_7 `emacs!' call with its
;;;         6 accessor names, and the defsubr wave.  S4 holds 4 checks.
;;;   S5 -- the registration: the corpus is in the (m60) group of
;;;         tool/run-tests.scm, AFTER the (m59) group, the (m59) group
;;;         stays present, and the group holds NO prelude key.  S5 holds
;;;         4 checks.
;;;   S6 -- the guards: 5 checks -- one per-group min-count guard for
;;;         each of S1 ... S5.  The in-process group-total
;;;         `ert-deftest' is a separate test in the same phase; it is
;;;         NOT one of the 5 counted checks.
;;;
;;; This corpus reads TRACKED files only (src/, mod/, prelude/,
;;; tool/run-tests.scm).  It does NOT read docs/
;;; (docs/kb.org test-must-not-read-docs): a gitignored record can only
;;; pass or skip, so a record check proves nothing.
;;;
;;; A read error is a real error, never a silent pass.  An absent
;;; TRACKED file is a real FAIL, not a pass (docs/m60-plan.org).  A
;;; missing `git' binary is an explicit INFO skip, never a pass.  Every
;;; check registers a real ERT test via imp-register-bool-as-ert-test,
;;; so the harness parses the ERT output and the exit code is correct.
;;;
;;; Every pin states its MEASURE UNIT: `m60-imp1--grep-c' counts LINES
;;; (the unit of `grep -c'), `m60-imp1--count' counts OCCURRENCES (the
;;; unit of `grep -o | wc -l'), and `m60-imp1--lines' counts NEWLINES
;;; (the unit of `wc -l').

(princ "=== m60 imp-1 standalone-load boundary audit suite ===\n")

(require 'imp-ert-report)

(defvar m60-imp1--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))
(defvar m60-imp1--registered 0
  "Total number of checks this corpus has registered.")
(defvar m60-imp1--group nil
  "The group that `m60-imp1--check' counts into: `s1' .. `s6', or nil.")
(defvar m60-imp1--counts nil
  "Alist of (GROUP . COUNT) for the registered checks.")

(defun m60-imp1--group-count (group)
  "Number of checks registered so far in GROUP."
  (or (cdr (assq group m60-imp1--counts)) 0))

(defun m60-imp1--bump-group ()
  "Count one check into `m60-imp1--group'."
  (when m60-imp1--group
    (let ((cell (assq m60-imp1--group m60-imp1--counts)))
      (if cell
          (setcdr cell (1+ (cdr cell)))
        (push (cons m60-imp1--group 1) m60-imp1--counts)))))

(defun m60-imp1--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
the symbol `m60-imp1-absent' when REL does not exist.  `case-fold-search'
is bound to nil: the elisp default folds case and inflates a count."
  (let ((path (expand-file-name rel m60-imp1--root)))
    (if (not (file-exists-p path))
        'm60-imp1-absent
      (with-temp-buffer
        (insert-file-contents path)
        (let ((case-fold-search nil))
          (funcall fn))))))

(defun m60-imp1--contains-p (rel needle)
  "Non-nil when the TRACKED file REL contains NEEDLE.  An absent file
folds to nil, so the check prints FAIL."
  (let ((hit (m60-imp1--with rel
               (lambda ()
                 (goto-char (point-min))
                 (search-forward needle nil t)))))
    (and (not (eq hit 'm60-imp1-absent)) (and hit t))))

(defun m60-imp1--holds-all (rel needles)
  "Non-nil when the TRACKED file REL holds every NEEDLE.  REL is read
once, so a multi-needle check does not re-read the file per needle."
  (m60-imp1--with rel
    (lambda ()
      (let ((all t))
        (dolist (needle needles)
          (goto-char (point-min))
          (unless (search-forward needle nil t) (setq all nil)))
        all))))

(defun m60-imp1--holds-none (rel needles)
  "Non-nil when the TRACKED file REL holds NO needle of NEEDLES.  An
absent file returns the symbol `m60-imp1-absent', which fails the check."
  (m60-imp1--with rel
    (lambda ()
      (let ((none t))
        (dolist (needle needles)
          (goto-char (point-min))
          (when (search-forward needle nil t) (setq none nil)))
        none))))

(defun m60-imp1--live-p (rel needle)
  "Non-nil when the TRACKED file REL holds NEEDLE on a line that is NOT
commented out."
  (m60-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((hit nil))
        (while (and (not hit) (search-forward needle nil t))
          (setq hit (save-excursion
                      (goto-char (line-beginning-position))
                      (not (looking-at-p "[ \t]*;")))))
        hit))))

(defun m60-imp1--ordered-p (rel needles)
  "Non-nil when the TRACKED file REL holds every NEEDLE in the GIVEN
ORDER: each search starts after the previous match."
  (m60-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((all t))
        (dolist (needle needles)
          (when all
            (unless (search-forward needle nil t) (setq all nil))))
        all))))

(defun m60-imp1--exists-p (rel)
  "Non-nil when REL exists in the tree at `m60-imp1--root'."
  (file-exists-p (expand-file-name rel m60-imp1--root)))

(defun m60-imp1--dir-entries (rel)
  "Count the entries of the directory REL, the unit of `ls | wc -l'.
Return the symbol `m60-imp1-absent' when REL does not exist."
  (let ((path (expand-file-name rel m60-imp1--root)))
    (if (not (file-directory-p path))
        'm60-imp1-absent
      (length (directory-files path nil "\\`[^.]")))))

(defun m60-imp1--lines (rel)
  "Count the NEWLINES of REL, the unit of `wc -l'."
  (m60-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (search-forward "\n" nil t) (setq n (1+ n)))
        n))))

(defun m60-imp1--grep-c (rel regexp)
  "Count the LINES of REL that match REGEXP, the unit of `grep -c'."
  (m60-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (not (eobp))
          (when (re-search-forward regexp (line-end-position) t)
            (setq n (1+ n)))
          (forward-line 1))
        n))))

(defun m60-imp1--count (rel regexp)
  "Count the OCCURRENCES of REGEXP in REL, the unit of
`grep -o | wc -l'.  This is NOT the unit of `grep -c'."
  (m60-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (re-search-forward regexp nil t) (setq n (1+ n)))
        n))))

(defun m60-imp1--lines-of (rel regexp)
  "Return the 1-based line numbers of the matches of REGEXP in REL.
An absent file returns the symbol `m60-imp1-absent', so the caller's
`equal' folds to nil and the check FAILS."
  (m60-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((sites nil))
        (while (re-search-forward regexp nil t)
          (let ((end (match-beginning 0)) (n 1))
            (save-excursion
              (goto-char (point-min))
              (while (search-forward "\n" end t) (setq n (1+ n)))
              (unless (memq n sites) (push n sites)))))
        (nreverse sites)))))

(defun m60-imp1--line-of (rel regexp)
  "Return the 1-based line number of the first REGEXP match in REL, or
nil when REGEXP does not match."
  (let ((sites (m60-imp1--lines-of rel regexp)))
    (and (listp sites) (car sites))))

(defun m60-imp1--count-scm-ref ()
  "Count scm_c_public_ref over src/*.[ch], the unit of
`grep -h scm_c_public_ref src/*.c src/*.h | wc -l'.  Unit: OCCURRENCES."
  (let ((total 0)
        (dir (expand-file-name "src" m60-imp1--root)))
    (dolist (f (directory-files dir t "\\.[ch]\\'"))
      (setq total (+ total (or (m60-imp1--count f "scm_c_public_ref") 0))))
    total))

(defun m60-imp1--text-of (rel regexp)
  "Return the last match of REGEXP in REL as a string, or nil."
  (m60-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((last nil))
        (while (re-search-forward regexp nil t) (setq last (match-string 0)))
        last))))

(defun m60-imp1--run (prog args)
  "Run PROG with ARGS from the repo root and return its stdout / stderr
as a string, or the symbol `m60-imp1-prog-absent' when PROG is absent."
  (if (not (executable-find prog))
      'm60-imp1-prog-absent
    (let ((buf (get-buffer-create " *m60-imp1-run*"))
          (default-directory m60-imp1--root))
      (unwind-protect
          (progn
            (with-current-buffer buf (erase-buffer))
            (apply #'call-process prog nil buf nil args)
            (with-current-buffer buf
              (buffer-substring-no-properties (point-min) (point-max))))
        (kill-buffer buf)))))

(defun m60-imp1--ancestor-p (ancestor descendant)
  "Non-nil when ANCESTOR is an ancestor of DESCENDANT in this repo.
Return the symbol `m60-imp1-prog-absent' when the `git' binary is not
on PATH.  A committed corpus must NOT pin HEAD to a literal base
commit: when imp-1 is committed, HEAD moves to the imp commit."
  (if (not (executable-find "git"))
      'm60-imp1-prog-absent
    (let ((default-directory m60-imp1--root))
      (zerop (call-process "git" nil nil nil
                           "merge-base" "--is-ancestor"
                           ancestor descendant)))))

(defun m60-imp1--check (name ok)
  "Report and register one check on a TRACKED file.  An absent source
file folds to nil, so the check prints FAIL: an absent TRACKED file is a
real error, not a pass."
  (let* ((absent (eq ok 'm60-imp1-absent))
         (pass (and (not absent) (and ok t))))
    (if absent
        (princ (format "FAIL m60/imp1/%s (source file absent)\n" name))
      (princ (format "%s m60/imp1/%s\n" (if pass "PASS" "FAIL") name)))
    (setq m60-imp1--registered (1+ m60-imp1--registered))
    (m60-imp1--bump-group)
    (imp-register-bool-as-ert-test (format "m60-imp1/%s" name) pass)))

(defun m60-imp1--info-skip (name reason)
  "Register one explicit INFO skip, counted into the current group.  A
host limit is a skip, never a pass (docs/m60-plan.org section 12)."
  (princ (format "INFO m60/imp1/%s %s\n" name reason))
  (setq m60-imp1--registered (1+ m60-imp1--registered))
  (m60-imp1--bump-group)
  (imp-register-skip-as-ert-test (format "m60-imp1/%s" name) reason))

;;; --- S1. The measured surface (docs/m60-plan.org section 2) -------

;; One check per row of the surface table.  Row 1 (HEAD) checks that the
;; base commit is an ANCESTOR of the running HEAD.  The source rows
;; re-measure the tree at HEAD; do NOT copy a planning number.

(setq m60-imp1--group 's1)

(let ((ok (m60-imp1--ancestor-p "3603a6795" "HEAD")))
  (if (eq ok 'm60-imp1-prog-absent)
      (m60-imp1--info-skip "head-3603a6795" "no git binary on PATH")
    (m60-imp1--check "head-3603a6795" ok)))

;; Unit: LINES (`wc -l').  Measured 2026-10-20 at HEAD 3603a6795.
;; RE-PINNED at M60 imp-7: loader.scm 1,328 -> 1,363 -> 1,389 -> 1,391 ->
;; 1,398 LINES (rows 23 and 24: the `defmacro' store and the
;; `eval-when-compile' branch, and the L10 note of cr.org F2).
(m60-imp1--check "xfaces.c-lines"
                 (eql 7741 (m60-imp1--lines "src/xfaces.c")))
;; M60 imp-8 (row 27) RE-PIN: loader.scm 1,398 -> 1,409 LINES (the
;; guarded `make-obsolete-variable' install in `init-loader').
;; M60 imp-9 (row 28a) RE-PIN: loader.scm 1,409 -> 1,511 LINES (the 3
;; branches `cond' / `let*' / `while' and the L16 ... L20 limit
;; block, above them, in `elisp-loader-eval-form').
;; M60 imp-9 fix (cr.org F3, F4, F5; L21) RE-PIN: loader.scm 1,480 -> 1,511 LINES.
;; M60 imp-10 RE-PIN: row 29 adds 2 `#:use-module' forms and 15
;; guarded installs to loader.scm -- 1,511 -> 1,588 LINES (wc -l) and
;; 23 / 19 -> 38 / 34 LINES (grep -c) -- and mode `arith' to
;; test/m60/probe-imp3.scm (591 -> 691 LINES).  OLD VALUES are the
;; cells that the numbers above replace.
(m60-imp1--check "loader.scm-lines"
;; M60 imp-11 RE-PIN: loader.scm 1,588 -> 1,620 LINES (OLD value 1,588).
                 ;; M60 imp-12 RE-PIN: loader.scm 1,620 -> 1,642 LINES (OLD value 1,620).
                 (eql 1642 (m60-imp1--lines "mod/emacs/loader.scm")))
(m60-imp1--check "reader.scm-lines"
                 (eql 2021 (m60-imp1--lines "mod/emacs/reader.scm")))
(m60-imp1--check "prelude-load.scm-lines"
                 (eql 229 (m60-imp1--lines "prelude/load.scm")))
(m60-imp1--check "faces.scm-and-spec.scm-lines"
                 (and (eql 70 (m60-imp1--lines "mod/emacs/faces.scm"))
                      (eql 32 (m60-imp1--lines "mod/emacs-elisp/spec.scm"))))

;; Unit: LINES (`grep -c').  7 + 4 guarded installs plus 2 unguarded
;; installs and the `defun' branch of the minimal evaluator made 14.
;; RE-MEASURED at M60 imp-4: the guarded `provide' install adds 1 to
;; each count -> 19 / 15 / 8.
;; M60 imp-8 (row 27) RE-PIN: loader.scm `symbol-fbound?' 22 -> 23
;; LINES (1 guarded install, the row-18 pattern of `provide').
;; M60 imp-8 (row 27) RE-PIN: loader.scm `set-symbol-function!' 18 -> 19
;; LINES (the same guarded install).  `FIX-.*guilemacs' stays 9.
;; M60 imp-10 RE-PIN: row 29 adds 2 `#:use-module' forms and 15
;; guarded installs to loader.scm -- 1,511 -> 1,588 LINES (wc -l) and
;; 23 / 19 -> 38 / 34 LINES (grep -c) -- and mode `arith' to
;; test/m60/probe-imp3.scm (591 -> 691 LINES).  OLD VALUES are the
;; cells that the numbers above replace.
(m60-imp1--check "loader.scm-grep-c-counts"
;; M60 imp-11 RE-PIN: `symbol-fbound?` 38 -> 39 LINES (OLD value 38).
                 (and (eql 39 (m60-imp1--grep-c "mod/emacs/loader.scm"
                                                "symbol-fbound?"))
;; M60 imp-11 RE-PIN: `set-symbol-function!` 34 -> 35 LINES (OLD value 34).
                      (eql 35 (m60-imp1--grep-c "mod/emacs/loader.scm"
                                                "set-symbol-function!"))
                      (eql 9 (m60-imp1--grep-c "mod/emacs/loader.scm"
                                               "FIX-.*guilemacs"))))
;; Unit: OCCURRENCES over src/*.[ch].
(m60-imp1--check "tree-wide-scm-ref-267"
                 (eql 267 (m60-imp1--count-scm-ref)))
;; Unit: FILES under test/mod (3 suites, 1 runner, 2 fixtures).
(m60-imp1--check "test-mod-files-6"
                 (eql 6 (m60-imp1--dir-entries "test/mod")))
;; Unit: ENTRIES of mod/emacs-elisp.  9, because `runtime/' is one entry.
(m60-imp1--check "emacs-elisp-entries-9"
                 (eql 9 (m60-imp1--dir-entries "mod/emacs-elisp")))
(m60-imp1--check "corpus-dir-present"
                 (and (m60-imp1--exists-p "test/m60")
                      (m60-imp1--exists-p "test/m60/test-m60-imp1.el")))

;;; --- S2. The ordered cell list (docs/m60-plan.org section 3) ------

;; The 11 GUARDED names are all bound after `init-loader' (MEASURED:
;; EMPTY-CELLS is the empty list).  The real path stops on cells that
;; this list does not hold.  The measured FIRST stop that a pure stub
;; can not pass is `defvar', not `require'.

(setq m60-imp1--group 's2)

;; The 11 guarded installs, in call order (7 runtime cells then 4 reader
;; / eval cells), and the 2 unguarded installs BEFORE them.
(m60-imp1--check "guarded-install-order-11"
                 (and (m60-imp1--ordered-p
                       "mod/emacs/loader.scm"
                       '("(unless (symbol-fbound? 'get-load-suffixes)"
                         "(unless (symbol-fbound? 'append)"
                         "(unless (symbol-fbound? 'symbol-value)"
                         "(unless (symbol-fbound? 'car)"
                         "(unless (symbol-fbound? 'expand-file-name)"
                         "(unless (symbol-fbound? 'file-directory-p)"
                         "(unless (symbol-fbound? 'cdr)"
                         "(unless (symbol-fbound? 'intern)"
                         "(unless (symbol-fbound? 'concat)"
                         "(unless (symbol-fbound? 'substring)"
                         "(unless (symbol-fbound? 'eval)"))
                      (m60-imp1--ordered-p
                       "mod/emacs/loader.scm"
                       '("(set-symbol-function! 'load elisp-load)"
                         "(set-symbol-function! 'autoload-do-load"
                         "(unless (symbol-fbound? 'get-load-suffixes)"))))

;; The 4 variable binds, in call order.  `init-loader' binds them only
;; when absent, so the full-Emacs values stay.
(m60-imp1--check "variable-binds-4"
                 (m60-imp1--ordered-p
                  "mod/emacs/loader.scm"
                  '("(unless (symbol-bound? 'load-path)"
                    "(unless (symbol-bound? 'load-suffixes)"
                    "(unless (symbol-bound? 'load-file-rep-suffixes)"
                    "(unless (symbol-bound? 'load-read-function)")))

;; The measured stop point cell: `provide' is a C DEFUN at src/fns.c
;; :3450 and `require' at :3496.  The Scheme `provide' exists, the
;; Scheme `require' does NOT.
(m60-imp1--check "provide-cell-sites"
                 (and (eql 3450 (m60-imp1--line-of
                                 "src/fns.c" "^DEFUN (\"provide\""))
                      (eql 3496 (m60-imp1--line-of
                                 "src/fns.c" "^DEFUN (\"require\""))
                      ;; M60 imp-8 (row 27) RE-PIN: 211 -> 212.  The
                      ;; export NAME of `elisp-make-obsolete-variable'
                      ;; is 1 line above `elisp-provide'.
                      (eql 212 (m60-imp1--line-of
                                "mod/emacs/utils.scm"
                                "^(define elisp-provide"))
                      ;; RE-PINNED at M60 imp-4: the install LEFT
                      ;; `init-utils-registrations'.  The pin follows the
                      ;; install and also pins that `utils.scm' holds
                      ;; NONE: ONE home only.
                      (eql 0 (m60-imp1--grep-c
                              "mod/emacs/utils.scm"
                              "set-symbol-function! 'provide"))
                      (m60-imp1--holds-all
                       "mod/emacs/loader.scm"
                       '("(unless (symbol-fbound? 'provide)"
                         "(set-symbol-function! 'provide elisp-provide)"))))

;; MEASURED ASYMMETRY, CLOSED at M60 imp-5.  At imp-1 `elisp-require'
;; appeared ONCE in the tree -- the #:export list at utils.scm :26 -- and
;; was never defined and never installed.  imp-5 gives the name ONE home:
;; 2 OCCURRENCES in loader.scm (the definition and the install), 0 in
;; utils.scm, 0 in the prelude.  RE-PINNED: the utils.scm export is gone.
(m60-imp1--check "require-asymmetry"
                 (and (eql 0 (m60-imp1--count "mod/emacs/utils.scm"
                                              "elisp-require"))
                      (eql 2 (m60-imp1--count "mod/emacs/loader.scm"
                                              "elisp-require"))
                      (eql 0 (m60-imp1--count "prelude/load.scm"
                                              "elisp-require"))
                      ;; RE-PINNED at M60 imp-3: the prelude lost the 36
                      ;; patch lines, so this site moved 236 -> 200.
                      (eql 200 (m60-imp1--line-of
                                "prelude/load.scm"
                                "(init-utils-registrations)"))
                      (m60-imp1--holds-none
                       "mod/emacs/utils.scm"
                       '("(define (elisp-require"
                         "(set-symbol-function! 'require"))))

;; The `features' variable is a C DEFVAR_LISP.  MEASURED: unbound in a
;; plain `guile' process, and `elisp-provide' raises on it.
(m60-imp1--check "features-defvar-6372"
                 (and (eql 6372 (m60-imp1--line-of
                                 "src/fns.c"
                                 "DEFVAR_LISP (\"features\""))
                      (m60-imp1--contains-p
                       "mod/emacs/utils.scm"
                       "(set-symbol-value! 'features (cons feature current-features))")))

;; The minimal evaluator `elisp-loader-eval' has a branch for `quote',
;; `setq', `if', `progn', `let', `lambda', `defun' and -- since M60
;; imp-6 (rows 21 and 22) -- for `defvar' and `defconst'.  `defmacro'
;; still has NO branch (row 23, imp-7).
;;
;; RE-PINNED at M60 imp-6: the check was named
;; `evaluator-has-no-defvar' and pinned the ABSENCE of both branches.
;; That was the pre-imp-6 measurement: the load of lisp/obarray.el
;; stopped at (void-function defconst), because the `defvar' of
;; `obarray-default-size' was never evaluated.  The stop was then
;; (void-function make-obsolete-variable) -- row 27.
;;
;; RE-PINNED at M60 imp-8: row 27 lands, so lisp/obarray.el loads to the
;; END in a plain `guile -L mod' process.  The old stop was
;; `LOAD lisp/obarray.el: ERROR void-function (make-obsolete-variable)'.
(m60-imp1--check "evaluator-has-defvar-and-defconst"
                 (and (m60-imp1--contains-p "mod/emacs/loader.scm"
                                            "((eq? head 'defun)")
                      (m60-imp1--contains-p "mod/emacs/loader.scm"
                                            "((eq? head 'defvar)")
                      (m60-imp1--contains-p "mod/emacs/loader.scm"
                                            "((eq? head 'defconst)")
                      ;; RE-PINNED at M60 imp-7: the ABSENCE pin of the
                      ;; `defmacro' branch (row 23) flips to PRESENCE.
                      (m60-imp1--contains-p "mod/emacs/loader.scm"
                                            "((eq? head 'defmacro)")))

;;; --- S3. The registration (docs/m60-plan.org section 4) -----------

;; Guile's `lookup-language' reads the binding NAME in the module
;; `(language NAME spec)' and raises "no such language NAME" when that
;; module does not bind it.  `define-language' alone does NOT register a
;; language (MEASURED control: module-bound? gives #f).  The tree does 2
;; things instead: it defines the language in `(emacs-elisp spec)' and
;; monkey-patches `lookup-language' from the prelude.

(setq m60-imp1--group 's3)

;; The `lookup-language' sites in the TRACKED Scheme.  M60 imp-3 RE-PINS
;; this check: the split moved the loader guard to :1099 (it now also
;; tests `c-runtime-installed?') and the `emacs!' row of runtime.scm to
;; :788, and it DELETED the prelude read, so 0 sites stay there.
;; M60 imp-5 RE-PINS the loader site again: the require cell and its 2
;; `load' protocol cells add 77 lines ABOVE it, so it moves 1099 -> 1176.
;; M60 imp-6 RE-PINS it one more time: the 2 evaluator branches of rows
;; 21 and 22 add 20 lines ABOVE it, so it moves 1176 -> 1196.
;; M60 imp-7 RE-PINS it: rows 23 and 24 add 35 lines ABOVE it, so the
;; site moves 1196 -> 1231.  The imp-7 fix RE-PINS it once more: the
;; L2 ... L6 limits block and the macro-drop helper add 26 lines ABOVE
;; it, so the site moves 1231 -> 1257 -> 1259.  The cr.org F2 fix of
;; L10 adds 7 more lines ABOVE it, so it moves 1259 -> 1266.
;; M60 imp-9 RE-PINS it: the 3 branches of row 28a and the L16 ... L20
;; limit block add lines ABOVE it, and the cr.org fix of imp-9 adds 31
;; more, so it moves 1266 -> 1337 -> 1368 (old
;; values 1231, 1257, 1259 and 1266).
;; M60 imp-10 RE-PIN: row 29 adds 2 `#:use-module' forms and 15
;; guarded installs to loader.scm -- 1,511 -> 1,588 LINES (wc -l) and
;; 23 / 19 -> 38 / 34 LINES (grep -c) -- and mode `arith' to
;; test/m60/probe-imp3.scm (591 -> 691 LINES).  OLD VALUES are the
;; cells that the numbers above replace.
;; M60 imp-12 RE-PIN: the `eval-and-compile' branch of row 31 and its
;; L27 ... L30 limit block add 22 lines ABOVE the site, so it moves
;; 1,385 -> 1,407.  The runtime.scm site stays at 788.
(m60-imp1--check "lookup-language-sites"
                 (and (eql 1407 (m60-imp1--line-of
                                 "mod/emacs/loader.scm"
                                 "(lookup-language 'emacs-elisp)"))
                      (eql 788 (m60-imp1--line-of
                                "mod/emacs-elisp/runtime.scm"
                                "(lookup-language 'emacs-elisp)"))
                      (eql 0 (m60-imp1--grep-c
                              "prelude/load.scm"
                              "lookup-language"))))

;; M60 imp-3 RE-PINS this check.  It pinned an ABSENT thing ("the
;; monkey patch of 4 `module-set!' sites is live"), and the patch is now
;; DELETED.  The check pins the PRESENT new thing instead: ONE mechanism,
;; the module `(language emacs-elisp spec)', and ZERO patch lines in the
;; prelude.  It does NOT get weaker: the 4 old sites are named as the
;; needles that must be gone, and the new module must exist.
(m60-imp1--check "prelude-patch-2-modules"
                 (and (eql 0 (m60-imp1--grep-c
                              "prelude/load.scm"
                              "module-set!"))
                      (eql 0 (m60-imp1--grep-c
                              "prelude/load.scm"
                              "patched-lookup"))
                      (eql 0 (m60-imp1--grep-c
                              "prelude/load.scm"
                              "bad language"))
                      (m60-imp1--holds-none
                       "prelude/load.scm"
                       '("(module-set! lang-module 'lookup-language patched-lookup)"
                         "(module-set! compile-module 'lookup-language patched-lookup)"
                         "(module-set! lang-module 'default-environment patched-default-env)"
                         "(resolve-module '(emacs-elisp spec))"))
                      (m60-imp1--exists-p
                       "mod/language/emacs-elisp/spec.scm")))

;; The C core loads the language module itself, so the language exists
;; in a full Emacs and not in a plain `guile' process.
(m60-imp1--check "c-resolve-emacs-elisp-spec"
                 (eql 1639 (m60-imp1--line-of
                            "src/emacs.c"
                            "scm_c_resolve_module (\"emacs-elisp spec\")")))

;; M60 imp-3 RE-PINS this check.  The circularity that makes the move
;; verdict A2 is GONE: the language object lives in
;; mod/language/emacs-elisp/spec.scm, and (emacs-elisp spec) imports it
;; and re-exports it, so it keeps `compile-and-load' and holds no
;; `define-language'.  32 lines is the MEASURED value after the split.
(m60-imp1--check "spec.scm-circularity"
                 (and (eql 32 (m60-imp1--lines "mod/emacs-elisp/spec.scm"))
                      (m60-imp1--ordered-p
                       "mod/emacs-elisp/spec.scm"
                       '("(define-module (emacs-elisp spec)"
                         "#:use-module (language emacs-elisp spec)"
                         "#:re-export (emacs-elisp)"
                         "(compile-and-load"))
                      (eql 0 (m60-imp1--grep-c
                              "mod/emacs-elisp/spec.scm"
                              "define-language"))
                      (eql 1 (m60-imp1--grep-c
                              "mod/language/emacs-elisp/spec.scm"
                              "^(define-language emacs-elisp"))))

;; The guard at loader.scm :1086 catches ONLY the "no such language"
;; message and re-raises any other misc-error.
(m60-imp1--check "narrow-catch-1086"
                 (m60-imp1--holds-all
                  "mod/emacs/loader.scm"
                  '("(string-contains arg \"no such language\")"
                    "(apply throw key args)")))

;;; --- S4. The C bootstrap rows (docs/m60-plan.org section 5) -------

;; The C core owns a sequence that a plain `guile' process does not run.
;; The symbol machinery is ALREADY Scheme; the missing parts are the
;; registration (S3) and the elisp primitives of the defsubr wave.

(setq m60-imp1--group 's4)

(m60-imp1--check "bootstrap-module-sequence"
                 (m60-imp1--ordered-p
                  "src/emacs.c"
                  '("scm_c_resolve_module (\"emacs-elisp spec\")"
                    "scm_c_resolve_module (\"elisp-symbols\")"
                    "scm_c_resolve_module (\"elisp-functions\")"
                    "scm_c_resolve_module (\"elisp-plists\")"
                    "scm_set_current_module (scm_c_resolve_module (\"guile-user\"))")))

(m60-imp1--check "bootstrap-symbol-accessors"
                 (and (eql 1647 (m60-imp1--line-of
                                 "src/emacs.c"
                                 "\"symbol-desc\""))
                      (eql 1648 (m60-imp1--line-of
                                 "src/emacs.c"
                                 "\"symbol-function\""))))

;; The SCM_CALL_7 of `emacs!': 7 arguments -- the 6 C accessor handles
;; and Qnil.
(m60-imp1--check "bootstrap-emacs-bang-7"
                 (and (eql 1672 (m60-imp1--line-of
                                 "src/emacs.c"
                                 "SCM_CALL_7 (scm_c_public_ref (\"emacs-elisp runtime\", \"emacs!\")"))
                      (m60-imp1--holds-all
                       "src/emacs.c"
                       '("SYMBOL_FUNCTION (intern (\"symbol-value\"))"
                         "SYMBOL_FUNCTION (intern (\"set\"))"
                         "SYMBOL_FUNCTION (intern (\"boundp\"))"
                         "SYMBOL_FUNCTION (intern (\"default-value\"))"
                         "SYMBOL_FUNCTION (intern (\"set-default\"))"
                         "SYMBOL_FUNCTION (intern (\"default-boundp\"))"))))

;; The defsubr wave, in call order.  Only `provide' and `require' are
;; classed in the row map; the rest is out of the imp-1 scope (Rule C).
(m60-imp1--check "bootstrap-defsubr-wave"
                 (m60-imp1--ordered-p
                  "src/emacs.c"
                  '("syms_of_fns ();"
                    "syms_of_xfaces ();"
                    "syms_of_keyboard ();")))

;;; --- S5. The registration -------------------------------------------

(setq m60-imp1--group 's5)

(m60-imp1--check "run-tests-m60-imp1"
                 (m60-imp1--live-p "tool/run-tests.scm"
                                   "test/m60/test-m60-imp1.el"))
(m60-imp1--check "run-tests-m60-group"
                 (m60-imp1--live-p "tool/run-tests.scm" "(group (m60)"))
(m60-imp1--check "run-tests-m60-after-m59"
                 (and (m60-imp1--ordered-p "tool/run-tests.scm"
                                           '("(group (m59)" "(group (m60)"))
                      (m60-imp1--live-p "tool/run-tests.scm"
                                        "(group (m59)")))
(m60-imp1--check "run-tests-m60-no-prelude"
                 (let ((text (m60-imp1--text-of
                              "tool/run-tests.scm"
                              "(group (m60)[^)]*)")))
                   (and (stringp text)
                        (not (string-match-p "prelude" text)))))

;;; --- S6. The guards -------------------------------------------------

;; An --filter that matches no group already reports exit 0 with 0
;; tests, so a green m60 gate proves nothing until the corpus exists and
;; its checks really register.  S1 holds 11 checks, S2 holds 6, S3 holds
;; 5, S4 holds 4, and S5 holds 4.

(setq m60-imp1--group 's6)

(m60-imp1--check "reg/min-s1-checks-11" (>= (m60-imp1--group-count 's1) 11))
(m60-imp1--check "reg/min-s2-checks-6" (>= (m60-imp1--group-count 's2) 6))
(m60-imp1--check "reg/min-s3-checks-5" (>= (m60-imp1--group-count 's3) 5))
(m60-imp1--check "reg/min-s4-checks-4" (>= (m60-imp1--group-count 's4) 4))
(m60-imp1--check "reg/min-s5-checks-4" (>= (m60-imp1--group-count 's5) 4))

;;; --- The group-total check ------------------------------------------

;; The measured count of m60-imp1 tests is 36: 35 registered checks
;; (S1 11, S2 6, S3 5, S4 4, S5 4, S6 5) plus this deftest itself.

(defvar m60-imp1--min-gate-total 36
  "The exact number of m60-imp1 ERT tests: 35 registered checks (S1 11,
S2 6, S3 5, S4 4, S5 4, S6 5) plus the group-total deftest itself.")

(ert-deftest m60-imp1/gate-m60-total ()
  "The m60-imp1 corpus registers at least its docs-independent floor."
  (should (>= (length (ert-select-tests "^m60-imp1" t))
              m60-imp1--min-gate-total)))

(princ (format "=== m60 imp-1 suite done (%d checks; s1 %d, s2 %d, s3 %d, s4 %d, s5 %d, s6 %d) ===\n"
               m60-imp1--registered
               (m60-imp1--group-count 's1)
               (m60-imp1--group-count 's2)
               (m60-imp1--group-count 's3)
               (m60-imp1--group-count 's4)
               (m60-imp1--group-count 's5)
               (m60-imp1--group-count 's6)))
