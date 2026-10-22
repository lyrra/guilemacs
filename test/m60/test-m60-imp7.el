;;; test-m60-imp7.el --- M60 imp-7 `defmacro' / `eval-when-compile' corpus.
;;;
;;; M60 imp-7 lands rows 23 and 24 of the row map of docs/m60-plan.org
;;; section 6: the `defmacro' store and the `eval-when-compile' branch,
;;; so that lisp/hex-util.el loads to the END in a plain `guile -L mod'
;;; process.  Both names are SPECIAL FORMS, so `init-loader' gets NO new
;;; install site and the C delta is 0.
;;;
;;; Row 24 (`eval-when-compile'): it is a MACRO in Emacs, but a
;;; source-reading loader has no compile phase.  At LOAD time its body
;;; must RUN, so the branch is `(elisp-loader-eval-seq (cdr form))' and
;;; it returns the value of its LAST body form.  This is a DECISION for
;;; the INTERPRETER, not a port: a compiler drops the body.
;;;
;;; Row 23 (`defmacro'): it must STORE an expander and must NOT evaluate
;;; the argument forms.  The expander is a Scheme PROCEDURE built with
;;; the same call that `defun' makes, and it lives in a Scheme alist of
;;; (emacs loader): `elisp-loader-macro-table'.  The elisp FUNCTION cell
;;; is NOT touched, because `symbol-function' and the `fbound?' predicate
;;; read that cell and a full Emacs owns it in C.  The evaluator looks
;;; the table up BEFORE the function cell of the final `else'.
;;;
;;; Row 28 (the macro EXPANSION path: backquote, ,@, `cond', `let*',
;;; `while') stays OPEN.  lisp/hex-util.el expands NO macro when it
;;; loads, so a `LOAD ... done' line is NOT expansion proof.
;;;
;;; cr.org raised 3 corrections after the first imp-7 commit.  F1 is a
;;; commit-message record and is NOT in this tree.  F2 (limits L2 ...
;;; L6 are NAMED in the source above the 2 branches) and F3 (a `defun'
;;; now SHADOWS a macro of the same name, because Emacs keeps the 2
;;; forms in ONE cell) are pinned here: S1 `macro-drop-source', S2
;;; `defun-shadows-macro' and S3 `defun-shadows-macro'.
;;;
;;; The (m60) group has NO prelude key, so this corpus runs INSIDE the
;;; built src/emacs.  Every plain-guile value is measured by
;;; test/m60/probe-imp3.scm as a `guile -L mod' child process with
;;; GUILE_AUTO_COMPILE=0 -- one MODE per child, so a stub of one mode
;;; can not hide the next result.  Mode `macros' is NEW here, and it is
;;; named in the `cells|provide|...' list of the mode error message.
;;; `elisp-loader-eval' and `elisp-loader-macro-ref' are NOT in the
;;; #:export list of (emacs loader), so the fixture gets them with
;;; `module-ref'.
;;;
;;; It pins these groups:
;;;
;;;   S1 -- the 3 sources: the macro table, `elisp-loader-macro-ref',
;;;         and the 2 branches; the return values (the SYMBOL, and the
;;;         last body value); 1 store call; 0 new install sites.
;;;   S2 -- the branch ORDER of brief.org section 4: both new branches
;;;         after `defvar' and before the final `else'; the neighbours
;;;         untouched; the `else' call unchanged; the table lookup BEFORE
;;;         `elisp-loader-apply'.
;;;   S3 -- the observables of brief.org section 6 through a live
;;;         `guile' child, mode `macros'.
;;;   S4 -- no regression: modes `cells', `provide', `stubs',
;;;         `negative', `noboot', `require', `defs', `registration' and
;;;         `language' keep their values.
;;;   S5 -- the re-measured surface: the LINE counts, the 3 `grep -c'
;;;         counts, and the NAMED limits of brief.org section 5.
;;;   S6 -- the registration: the imp-7 line AFTER the imp-6 line,
;;;         imp-1 ... imp-6 kept, (m60) with no prelude key.
;;;   S7 -- the guards: the per-group min counts, the marker-routing
;;;         self-check of the skip path, and the group-total deftest.
;;;
;;; This corpus reads TRACKED files only.  It does NOT read docs/.
;;; A read error is a real error, never a silent pass.  An absent TRACKED
;;; file is a real FAIL.  A missing `guile' binary is an explicit INFO
;;; skip, never a pass: `m60-imp7--check' routes the marker
;;; `m60-imp7-prog-absent' to `m60-imp7--info-skip', and `m60-imp7--all'
;;; carries that marker through a composite check.
;;;
;;; Every value below was MEASURED on this host on 2026-10-21 by running
;;; the fixture and the commands named in the comment of each check.
;;; MEASURED total: 43 registered checks (S1 7, S2 6, S3 7, S4 9, S5 4,
;;; S6 3, S7 7) plus the group-total deftest = 44 ERT tests.  The imp-7
;;; commit had 39 + 1 = 40; the 3 cr.org F3 checks and the L10 check of
;;; the second cr.org review follow.

(princ "=== m60 imp-7 defmacro/eval-when-compile suite ===\n")

(require 'imp-ert-report)

(defvar m60-imp7--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))
(defvar m60-imp7--registered 0
  "Total number of checks this corpus has registered.")
(defvar m60-imp7--group nil
  "The group that `m60-imp7--check' counts into: `s1' .. `s7', or nil.")
(defvar m60-imp7--counts nil
  "Alist of (GROUP . COUNT) for the registered checks.")
(defvar m60-imp7--probe-cache nil
  "Alist of (MODE . RESULT) of the plain-guile probe runs of this corpus.
A mode is measured once per corpus run, so a group starts one child
process, not one per check.")

(defun m60-imp7--group-count (group)
  "Number of checks registered so far in GROUP."
  (or (cdr (assq group m60-imp7--counts)) 0))

(defun m60-imp7--bump-group ()
  "Count one check into `m60-imp7--group'."
  (when m60-imp7--group
    (let ((cell (assq m60-imp7--group m60-imp7--counts)))
      (if cell
          (setcdr cell (1+ (cdr cell)))
        (push (cons m60-imp7--group 1) m60-imp7--counts)))))

;;; --- tracked-file helpers (the imp-1 / imp-4 / imp-6 idioms) --------

(defun m60-imp7--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
the symbol `m60-imp7-absent' when REL does not exist.  `case-fold-search'
is bound to nil: the elisp default folds case and inflates a count."
  (let ((path (expand-file-name rel m60-imp7--root)))
    (if (not (file-exists-p path))
        'm60-imp7-absent
      (with-temp-buffer
        (insert-file-contents path)
        (let ((case-fold-search nil))
          (funcall fn))))))

(defun m60-imp7--holds-all (rel needles)
  "Non-nil when the TRACKED file REL holds every NEEDLE.  An absent file
fails the check."
  (m60-imp7--with rel
    (lambda ()
      (let ((all t))
        (dolist (needle needles)
          (goto-char (point-min))
          (unless (search-forward needle nil t) (setq all nil)))
        all))))

(defun m60-imp7--holds-none (rel needles)
  "Non-nil when the TRACKED file REL holds NO needle of NEEDLES."
  (m60-imp7--with rel
    (lambda ()
      (let ((none t))
        (dolist (needle needles)
          (goto-char (point-min))
          (when (search-forward needle nil t) (setq none nil)))
        none))))

(defun m60-imp7--ordered-p (rel needles)
  "Non-nil when the TRACKED file REL holds every NEEDLE in the GIVEN
ORDER: each search starts after the previous match."
  (m60-imp7--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((all t))
        (dolist (needle needles)
          (when all
            (unless (search-forward needle nil t) (setq all nil))))
        all))))

(defun m60-imp7--lines (rel)
  "Count the NEWLINES of REL, the unit of `wc -l'."
  (m60-imp7--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (search-forward "\n" nil t) (setq n (1+ n)))
        n))))

(defun m60-imp7--grep-c (rel regexp)
  "Count the LINES of REL that match REGEXP, the unit of `grep -c'."
  (m60-imp7--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (not (eobp))
          (when (re-search-forward regexp (line-end-position) t)
            (setq n (1+ n)))
          (forward-line 1))
        n))))

(defun m60-imp7--literal-lines (rel needle)
  "Count the LINES of REL that hold NEEDLE as a LITERAL substring.  Use
this helper and not `m60-imp7--grep-c' where NEEDLE holds a regexp
metacharacter: `?' is the `optional' operator of the search syntax."
  (m60-imp7--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (not (eobp))
          (when (search-forward needle (line-end-position) t)
            (setq n (1+ n)))
          (forward-line 1))
        n))))

(defun m60-imp7--literal-lines-in-eval-form (needle)
  "Count the LINES of `elisp-loader-eval-form' that hold NEEDLE as a
LITERAL substring, or return the symbol `m60-imp7-absent'.  The region
is SCOPED: a file-wide pin turns a check of rows 23 and 24 red when an
UNRELATED row adds the same text, and the red check then names the wrong
cause.  The form starts at `(define (elisp-loader-eval-form form)' and
ends at the next top-level `(define'."
  (m60-imp7--with "mod/emacs/loader.scm"
    (lambda ()
      (goto-char (point-min))
      (if (not (search-forward "(define (elisp-loader-eval-form form)" nil t))
          nil
        (let ((start (line-beginning-position)))
          (if (re-search-forward "^(define " nil t)
              (narrow-to-region start (line-beginning-position))
            (narrow-to-region start (point-max)))
          (goto-char (point-min))
          (let ((n 0))
            (while (not (eobp))
              (when (search-forward needle (line-end-position) t)
                (setq n (1+ n)))
              (forward-line 1))
            n))))))

;;; --- the plain-guile probe runner -----------------------------------

(defun m60-imp7--probe-1 (mode)
  "Run test/m60/probe-imp3.scm in MODE as a `guile -L mod' child
process, with GUILE_AUTO_COMPILE=0 and GUILEMACS_ROOT set, and with
`default-directory' at the repo root.  Return (EXIT . OUTPUT), where
OUTPUT holds stdout AND stderr, or the symbol `m60-imp7-prog-absent'
when the `guile' binary is not on PATH."
  (if (not (executable-find "guile"))
      'm60-imp7-prog-absent
    (let ((buf (get-buffer-create " *m60-imp7-probe*"))
          (default-directory m60-imp7--root)
          (process-environment
           (append (list (concat "GUILEMACS_ROOT=" m60-imp7--root)
                         "GUILE_AUTO_COMPILE=0")
                   process-environment)))
      (unwind-protect
          (progn
            (with-current-buffer buf (erase-buffer))
            (let ((exit (apply #'call-process
                               "guile" nil buf nil
                               (list "-L" "mod"
                                     "test/m60/probe-imp3.scm"
                                     mode))))
              (cons exit (with-current-buffer buf
                           (buffer-substring-no-properties
                            (point-min) (point-max))))))
        (kill-buffer buf)))))

(defun m60-imp7--probe (mode)
  "The cached result of `m60-imp7--probe-1' for MODE."
  (let ((cell (assoc mode m60-imp7--probe-cache)))
    (if cell
        (cdr cell)
      (let ((result (m60-imp7--probe-1 mode)))
        (push (cons mode result) m60-imp7--probe-cache)
        result))))

(defun m60-imp7--probe-raw (mode)
  "The OUTPUT of the probe MODE whatever the exit status is, or the
marker `m60-imp7-prog-absent'.  Mode `registration' raises on purpose,
so its output is only readable this way."
  (let ((result (m60-imp7--probe mode)))
    (cond
     ((eq result 'm60-imp7-prog-absent) result)
     ((consp result) (cdr result))
     (t nil))))

(defun m60-imp7--probe-output (mode)
  "The OUTPUT of the probe MODE when the child exited 0, else nil.  A
crash mid-mode printed a partial output, so the exit status is part of
every output check.  When the `guile' binary is absent, the marker
`m60-imp7-prog-absent' is returned instead of nil, so the caller can
SKIP and not pass or fail."
  (let ((result (m60-imp7--probe mode)))
    (cond
     ((eq result 'm60-imp7-prog-absent) result)
     ((and (consp result) (eql 0 (car result))) (cdr result))
     (t nil))))

(defun m60-imp7--probe-line (mode line)
  "Non-nil when the probe MODE printed LINE as one WHOLE line and the
child exited 0.  A substring match is NOT enough: a line pin holds the
whole line, so a changed value can not hide inside it."
  (let ((out (m60-imp7--probe-output mode)))
    (cond
     ((eq out 'm60-imp7-prog-absent) out)
     ((not (stringp out)) nil)
     (t (with-temp-buffer
          (insert "\n" out "\n")
          (goto-char (point-min))
          (and (search-forward (concat "\n" line "\n") nil t) t))))))

(defun m60-imp7--probe-holds (mode needle)
  "Non-nil when the OUTPUT of the probe MODE holds NEEDLE (a substring
pin; use it only where an address sits in the text)."
  (let ((out (m60-imp7--probe-output mode)))
    (cond
     ((eq out 'm60-imp7-prog-absent) out)
     ((not (stringp out)) nil)
     (t (with-temp-buffer
          (insert out)
          (goto-char (point-min))
          (and (search-forward needle nil t) t))))))

(defun m60-imp7--probe-holds-none (mode needle)
  "Non-nil when the OUTPUT of the probe MODE holds NO NEEDLE."
  (let ((out (m60-imp7--probe-output mode)))
    (cond
     ((eq out 'm60-imp7-prog-absent) out)
     ((not (stringp out)) nil)
     (t (with-temp-buffer
          (insert out)
          (goto-char (point-min))
          (not (search-forward needle nil t)))))))

(defun m60-imp7--probe-raw-holds (mode needle)
  "Non-nil when the RAW output of the probe MODE holds NEEDLE, whatever
the exit status is."
  (let ((out (m60-imp7--probe-raw mode)))
    (cond
     ((eq out 'm60-imp7-prog-absent) out)
     ((not (stringp out)) nil)
     (t (with-temp-buffer
          (insert out)
          (goto-char (point-min))
          (and (search-forward needle nil t) t))))))

(defun m60-imp7--all (&rest values)
  "`and' over the ALREADY-EVALUATED VALUES, with one difference: a
MARKER wins over a nil.  Both markers are truthy, so a plain `and'
returns the value of a LATER form and the check reads as a PASS.  The
verdict order matches `m60-imp7--verdict': the absent FILE marker first
(a real FAIL), then the absent `guile' marker (a skip), then nil (a
FAIL), then t (a PASS)."
  (cond
   ((memq 'm60-imp7-absent values) 'm60-imp7-absent)
   ((memq 'm60-imp7-prog-absent values) 'm60-imp7-prog-absent)
   ((memq nil values) nil)
   (t t)))

;;; --- report helpers -------------------------------------------------

(defun m60-imp7--verdict (ok)
  "Classify the value OK of one check: `pass', `fail', `absent' (the
TRACKED file is missing -- a real FAIL), or `skip' (the `guile' binary is
not on PATH, so the probe could not run -- never a pass)."
  (cond
   ((eq ok 'm60-imp7-prog-absent) 'skip)
   ((eq ok 'm60-imp7-absent) 'absent)
   (ok 'pass)
   (t 'fail)))

(defun m60-imp7--check (name ok)
  "Report and register one check.  The 4 outcomes come from
`m60-imp7--verdict': an absent TRACKED file prints FAIL (a real error,
not a pass), and an absent `guile' binary prints INFO and registers a
controlled ERT skip -- never a pass."
  (let ((verdict (m60-imp7--verdict ok)))
    (cond
     ((eq verdict 'skip)
      (m60-imp7--info-skip name "no guile binary on PATH"))
     ((eq verdict 'absent)
      (princ (format "FAIL m60/imp7/%s (source file absent)\n" name))
      (setq m60-imp7--registered (1+ m60-imp7--registered))
      (m60-imp7--bump-group)
      (imp-register-bool-as-ert-test (format "m60-imp7/%s" name) nil))
     (t
      (princ (format "%s m60/imp7/%s\n"
                     (if (eq verdict 'pass) "PASS" "FAIL") name))
      (setq m60-imp7--registered (1+ m60-imp7--registered))
      (m60-imp7--bump-group)
      (imp-register-bool-as-ert-test (format "m60-imp7/%s" name)
                                     (eq verdict 'pass))))))

(defun m60-imp7--info-skip (name reason)
  "Register one explicit INFO skip, counted into the current group.  A
host limit is a skip, never a pass."
  (princ (format "INFO m60/imp7/%s %s\n" name reason))
  (setq m60-imp7--registered (1+ m60-imp7--registered))
  (m60-imp7--bump-group)
  (imp-register-skip-as-ert-test (format "m60-imp7/%s" name) reason))

;;; --- S1. The 3 sources ----------------------------------------------

;; Row 23 needs a STORE that is not the elisp function cell.  MEASURED
;; 2026-10-21 (`grep -c', unit LINES): 1 `(define elisp-loader-macro-table
;; '())', 1 `(define (elisp-loader-macro-ref name)', and 1 `assq' against
;; that table.
(setq m60-imp7--group 's1)

(m60-imp7--check "s1/macro-table-source"
                 (m60-imp7--all
                  (eql 1 (m60-imp7--literal-lines
                          "mod/emacs/loader.scm"
                          "(define elisp-loader-macro-table '())"))
                  (eql 1 (m60-imp7--literal-lines
                          "mod/emacs/loader.scm"
                          "(define (elisp-loader-macro-ref name)"))
                  (eql 1 (m60-imp7--literal-lines
                          "mod/emacs/loader.scm"
                          "(hit (assq name elisp-loader-macro-table))"))))

;; ONE branch per name, and MEASURED: 1 `eval-when-compile' branch and 1
;; `defmacro' branch in mod/emacs/loader.scm.
(m60-imp7--check "s1/one-branch-each"
                 (m60-imp7--all
                  (eql 1 (m60-imp7--literal-lines
                          "mod/emacs/loader.scm"
                          "((eq? head 'eval-when-compile)"))
                  (eql 1 (m60-imp7--literal-lines
                          "mod/emacs/loader.scm"
                          "((eq? head 'defmacro)"))))

;; Row 24 runs the BODY at load time and returns its LAST value.  The
;; DECISION words name the interpreter behaviour, so a later reader can
;; not mistake the branch for a port of the compiler.
(m60-imp7--check "s1/eval-when-compile-runs-the-body"
                 (m60-imp7--all
                  (m60-imp7--ordered-p
                   "mod/emacs/loader.scm"
                   '("((eq? head 'eval-when-compile)"
                     "(elisp-loader-eval-seq (cdr form))"))
                  (m60-imp7--holds-all
                   "mod/emacs/loader.scm"
                   '("DECISION, not a port" "INTERPRETER behaviour"))))

;; Row 23 builds the expander with the SAME call that `defun' makes, and
;; the branch returns the SYMBOL `(cadr form)'.  `set!' returns an
;; unspecified value, so a branch that ENDED with the store would hand a
;; loaded file that value, not the symbol.
(m60-imp7--check "s1/defmacro-returns-the-symbol"
                 (m60-imp7--ordered-p
                  "mod/emacs/loader.scm"
                  '("((eq? head 'defmacro)"
                    "(set! elisp-loader-macro-table"
                    "(acons (cadr form)"
                    "(elisp-loader-make-procedure (caddr form) (cdddr form))"
                    "(cadr form))")))

;; ONE store call INSIDE the evaluator: the alist is extended in exactly
;; one place of `elisp-loader-eval-form', so a 2nd mechanism can not
;; appear beside it.  RE-PINNED at the imp-7 fix (cr.org F3): the 2nd
;; LITERAL LINE of the file is `elisp-loader-macro-drop!', the helper
;; that REMOVES an entry.  Total 1 -> 2 (old value 1), still 1 inside
;; `elisp-loader-eval-form'.
(m60-imp7--check "s1/one-store-call"
                 (m60-imp7--all
                  (eql 2 (m60-imp7--literal-lines
                          "mod/emacs/loader.scm"
                          "(set! elisp-loader-macro-table"))
                  (eql 1 (m60-imp7--literal-lines-in-eval-form
                          "(set! elisp-loader-macro-table"))))

;; cr.org F3 / limit L8: a `defun' SHADOWS a macro of the same name.
;; Emacs keeps the 2 forms in ONE cell, so the table entry must be
;; DROPPED.  The helper is defined ABOVE `elisp-loader-eval-form', like
;; the table and the lookup.
(m60-imp7--check "s1/macro-drop-source"
                 (m60-imp7--all
                  (eql 1 (m60-imp7--literal-lines
                          "mod/emacs/loader.scm"
                          "(define (elisp-loader-macro-drop! name)"))
                  (eql 1 (m60-imp7--literal-lines
                          "mod/emacs/loader.scm"
                          "(remove (lambda (entry) (eq? (car entry) name))"))
                  (m60-imp7--ordered-p
                   "mod/emacs/loader.scm"
                   '("(define (elisp-loader-macro-ref name)"
                     "(define (elisp-loader-macro-drop! name)"
                     "(define (elisp-loader-eval-form form)"))))

;; The 2 names are SPECIAL FORMS, not function cells: `init-loader' must
;; get NO new install site.  MEASURED: 0 sites in loader.scm and 0 in the
;; prelude.  This check keeps `symbol-function' and the `fbound?'
;; predicate unaware of a macro.
(m60-imp7--check "s1/zero-install-sites"
                 (m60-imp7--all
                  (m60-imp7--holds-none
                   "mod/emacs/loader.scm"
                   '("(set-symbol-function! 'defmacro"
                     "(set-symbol-function! 'eval-when-compile"))
                  (m60-imp7--holds-none
                   "prelude/load.scm"
                   '("set-symbol-function! 'defmacro"
                     "set-symbol-function! 'eval-when-compile"))))

;;; --- S2. The branch order and the neighbours -------------------------

;; MEASURED order (brief.org section 4): quote, progn, defun, defconst,
;; defvar, then the 2 NEW branches, then the final `else'.  No existing
;; branch moved: a move breaks the order pins of rows 21 and 22.
(setq m60-imp7--group 's2)

(m60-imp7--check "s2/ordered-after-defvar-before-else"
                 (m60-imp7--ordered-p
                  "mod/emacs/loader.scm"
                  '("((eq? head 'defvar)"
                    "((eq? head 'eval-when-compile)"
                    "((eq? head 'defmacro)"
                    "(else"
                    "(throw 'void-function head)")))

;; The neighbours of the new code are UNTOUCHED: the `defvar' guard
;; above, and the `elisp-loader-make-procedure' call that the `defun'
;; branch and the new `defmacro' branch share.
(m60-imp7--check "s2/neighbours-untouched"
                 (m60-imp7--all
                  (eql 1 (m60-imp7--literal-lines
                          "mod/emacs/loader.scm"
                          "(and (pair? (cddr form)) (not (symbol-bound? name)))"))
                  (eql 2 (m60-imp7--literal-lines
                          "mod/emacs/loader.scm"
                          "(elisp-loader-make-procedure (caddr form)"))))

;; `eval-when-compile' adds a SECOND LITERAL LINE of the sequence call:
;; the `progn' branch and the new branch.  1 -> 2 is the re-pin of
;; brief.org section 9.  The dispatcher itself is unchanged.
(m60-imp7--check "s2/eval-unchanged"
                 (m60-imp7--all
                  (eql 1 (m60-imp7--literal-lines
                          "mod/emacs/loader.scm"
                          "(define (elisp-loader-eval form)"))
                  (eql 1 (m60-imp7--literal-lines
                          "mod/emacs/loader.scm"
                          "((pair? form) (elisp-loader-eval-form form))"))
                  ;; M60 imp-12 RE-PIN: 2 -> 3 LITERAL LINES.  The
                  ;; `eval-and-compile' branch of row 31 adds the 3rd.
                  (eql 3 (m60-imp7--literal-lines
                          "mod/emacs/loader.scm"
                          "(elisp-loader-eval-seq (cdr form))"))))

;; The `else' body still calls `elisp-loader-apply' on the FUNCTION cell.
;; The 3 counts are SCOPED to that one form, so an unrelated row can not
;; turn this check red.
(m60-imp7--check "s2/apply-unchanged"
                 (m60-imp7--all
                  (eql 1 (m60-imp7--literal-lines
                          "mod/emacs/loader.scm"
                          "(define (elisp-loader-apply fn args)"))
                  (eql 1 (m60-imp7--literal-lines-in-eval-form
                          "(elisp-loader-apply (symbol-function head)"))
                  (eql 2 (m60-imp7--literal-lines-in-eval-form
                          "(map elisp-loader-eval (cdr form))"))))

;; The table lookup comes BEFORE the function cell.  A macro call must
;; never reach `symbol-function': the reverse order would expand nothing
;; and would raise `void-function' on a macro name.
(m60-imp7--check "s2/macro-lookup-before-apply"
                 (m60-imp7--all
                  (m60-imp7--ordered-p
                   "mod/emacs/loader.scm"
                   '("(else"
                     "(let ((expander (elisp-loader-macro-ref head)))"
                     "(apply expander (cdr form))"
                     "(symbol-fbound? head)"
                     "(elisp-loader-apply (symbol-function head)"))
                  (eql 1 (m60-imp7--literal-lines-in-eval-form
                          "(elisp-loader-macro-ref head)"))))

;; cr.org F3 / limit L8: the `defun' branch DROPS the table entry BEFORE
;; it writes the function cell.  The reverse order would leave a window
;; where the call reaches neither of the 2 stores of Emacs.
(m60-imp7--check "s2/defun-shadows-macro"
                 (m60-imp7--all
                  (eql 1 (m60-imp7--literal-lines
                          "mod/emacs/loader.scm"
                          "(elisp-loader-macro-drop! (cadr form))"))
                  (m60-imp7--ordered-p
                   "mod/emacs/loader.scm"
                   '("((eq? head 'defun)"
                     "(elisp-loader-macro-drop! (cadr form))"
                     "(set-symbol-function! (cadr form)"))))

;;; --- S3. The observables (mode `macros') -----------------------------

;; A plain `guile -L mod' process, ONE child for this group.  The elisp
;; FUNCTION cell of a macro name stays EMPTY; the expander is a Scheme
;; procedure in the table.
(setq m60-imp7--group 's3)

(m60-imp7--check "s3/defmacro-returns-the-symbol"
                 (m60-imp7--all
                  (m60-imp7--probe-line "macros" "defmacro ret: m60-probe-m")
                  (m60-imp7--probe-holds-none "macros" "defmacro ret: (")
                  (m60-imp7--probe-holds-none "macros" "defmacro ret: #t")))

(m60-imp7--check "s3/defmacro-fbound-false"
                 (m60-imp7--probe-line "macros" "defmacro fbound: #f"))

;; The expander is a PROCEDURE.  The line holds the stable token only,
;; never the printed address of the object.
(m60-imp7--check "s3/expander-is-a-procedure"
                 (m60-imp7--all
                  (m60-imp7--probe-line "macros"
                                        "defmacro expander: procedure=#t")
                  (m60-imp7--probe-line
                   "macros"
                   "stored expanders: hex-char-to-num=#t num-to-hex-char=#t")))

;; `7' proves that the argument did NOT run: `(m60-probe-missing-fn)'
;; would raise `void-function' if it did.
(m60-imp7--check "s3/call-does-not-evaluate-argument"
                 (m60-imp7--probe-line "macros" "defmacro call noeval: 7"))

;; cr.org F3 / limit L8: after `(defun m60-probe-m (x) 9)' the table entry
;; is GONE, the function cell answers, and the call gives `9'.  In Emacs
;; the 2 forms share ONE cell, so the `defun' wins there too.
(m60-imp7--check "s3/defun-shadows-macro"
                 (m60-imp7--all
                  (m60-imp7--probe-line "macros" "defun shadow expander: #f")
                  (m60-imp7--probe-line "macros" "defun shadow fbound: #t")
                  (m60-imp7--probe-line "macros" "defun shadow call: 9")))

;; Row 24 on the REAL file: form 1 of lisp/hex-util.el, read with the
;; elisp reader, returns the value of its LAST body form, that is the
;; SYMBOL `num-to-hex-char'.
(m60-imp7--check "s3/eval-when-compile-form1"
                 (m60-imp7--probe-line
                  "macros"
                  "eval-when-compile form1 ret: num-to-hex-char"))

;; The whole file on the real load path, and its `provide'.
(m60-imp7--check "s3/hex-util-loads-to-the-end"
                 (m60-imp7--all
                  (m60-imp7--probe-line "macros" "LOAD lisp/hex-util.el: done")
                  (m60-imp7--probe-line "macros" "featurep hex-util: #t")))

;;; --- S4. No regression on the 9 older modes --------------------------

(setq m60-imp7--group 's4)

;; RE-PINNED at imp-7: `LOAD lisp/hex-util.el' is now `done`, not
;; `ERROR void-function (eval-when-compile)`.  The imp-2 R3 and imp-3 S5
;; lines follow this one.
(m60-imp7--check "s4/cells-unchanged"
                 (m60-imp7--all
                  (m60-imp7--probe-line "cells" "EMPTY-CELLS: ()")
                  (m60-imp7--probe-line
                   "cells" "UNGUARDED: load=#t autoload-do-load=#t")
                  (m60-imp7--probe-line
                   "cells"
                   (concat "VARS: load-path=#t load-suffixes=#t"
                           " load-file-rep-suffixes=#t load-read-function=#t"))
                  (m60-imp7--probe-line "cells" "ASYM: require=#t provide=#t")
                  (m60-imp7--probe-line "cells" "LOAD lisp/cdl.el: done")
                  (m60-imp7--probe-line "cells" "features: (cdl)")
                  (m60-imp7--probe-line "cells" "FEATURES-BOUND: #t")))

;; RE-PINNED at imp-7: the FIRST stop moved from form 1 of hex-util.el
;; to the row-27 call in obarray.el, and hex-util.el now reaches the END.
;; M60 imp-8 (row 27) RE-PIN: this line is `done' now; the old pin was
;; the `ERROR void-function (make-obsolete-variable)' line of row 27.
(m60-imp7--check "s4/cells-stops"
                 (m60-imp7--all
                  (m60-imp7--probe-line
                   "cells"
                   "LOAD lisp/obarray.el: done")
                  (m60-imp7--probe-line "cells" "LOAD lisp/hex-util.el: done")
                  (m60-imp7--probe-holds-none "cells" "(eval-when-compile)")))

(m60-imp7--check "s4/provide-unchanged"
                 (m60-imp7--all
                  (m60-imp7--probe-line "provide" "features-bound-at-start: #t")
                  (m60-imp7--probe-line "provide" "provide-fbound-at-start: #t")
                  (m60-imp7--probe-line "provide" "LOAD cdl: done")
                  (m60-imp7--probe-line "provide" "require-fbound: #t")))

;; RE-PINNED at imp-7: the real `eval-when-compile' branch matches FIRST,
;; so the pure stub of that name is DEAD.  The stub STAYS in the fixture,
;; like the `defconst' stub of imp-6, because the mode records the chain.
;; The stop is no longer `(defmacro)'.
;; M60 imp-8 (row 27) RE-PIN: this line is `done' now; the old pin was
;; the `ERROR void-function (make-obsolete-variable)' line of row 27.
(m60-imp7--check "s4/stubs-blockers"
                 (m60-imp7--all
                  (m60-imp7--probe-line "stubs" "stub-provide / cdl: done")
                  (m60-imp7--probe-line
                   "stubs"
                   "stub-defconst / obarray: done")
                  (m60-imp7--probe-line "stubs"
                                        "stub-eval-when-compile / hex-util: done")
                  (m60-imp7--probe-line "stubs" "stub-ntl / subdirs: done")))

;; The imp-4 negative control still names the unbound sentinel.  The
;; address changes per run, so the pin holds WORDS, not a LINE.
(m60-imp7--check "s4/negative-control"
                 (m60-imp7--all
                  (m60-imp7--probe-line "negative" "features-bound: #f")
                  (m60-imp7--probe-line "negative" "provide-fbound: #t")
                  (m60-imp7--probe-holds "negative" "LOAD cdl: ERROR wrong-type-arg")
                  (m60-imp7--probe-holds "negative" "\"memq\"")
                  (m60-imp7--probe-holds "negative" "uninterned-symbol unbound")
                  (m60-imp7--probe-holds-none "negative" "void-function")))

(m60-imp7--check "s4/noboot-unchanged"
                 (m60-imp7--all
                  (m60-imp7--probe-line "noboot" "features-bound: #f")
                  (m60-imp7--probe-holds "noboot" "Wrong type to apply")))

(m60-imp7--check "s4/require-unchanged"
                 (m60-imp7--all
                  (m60-imp7--probe-line "require" "REQUIRE-FBOUND: #t")
                  (m60-imp7--probe-line "require" "features-at-start: ()")
                  (m60-imp7--probe-line "require" "REQUIRE cdl: cdl")
                  (m60-imp7--probe-line "require" "features: (cdl)")
                  (m60-imp7--probe-line "require" "REQUIRE-AGAIN: cdl")))

;; Mode `defs' is the imp-6 record of rows 21 and 22.  The 2 new branches
;; are AFTER the `defvar' branch, so those values must not move.
(m60-imp7--check "s4/defs-unchanged"
                 (m60-imp7--all
                  (m60-imp7--probe-line "defs"
                                        "defconst ret: m60-probe-c / m60-probe-c")
                  (m60-imp7--probe-line "defs" "defconst value: 2")
                  (m60-imp7--probe-line "defs"
                                        "defvar ret: m60-probe-v / m60-probe-v")
                  (m60-imp7--probe-line "defs" "defvar value: 1")
                  (m60-imp7--probe-line "defs" "defvar no-init bound: #f")
                  (m60-imp7--probe-line
                   "defs" "defconst no-init bound (lenient): #t")))

;; The registration row keeps its NEXT blocker (row 26), and the language
;; object still resolves.  Mode `registration' raises on purpose, so its
;; output is read raw.
(m60-imp7--check "s4/registration-and-language"
                 (m60-imp7--all
                  (m60-imp7--probe-raw-holds "registration"
                                             "Unbound variable: mapcar")
                  (m60-imp7--probe-line "language" "LANGUAGE?: #t")
                  (m60-imp7--probe-line "language"
                                        "LANGUAGE-TITLE: \"Modern Emacs Lisp\"")
                  (m60-imp7--probe-line "language" "LANGUAGE-NAME: emacs-elisp")))

;;; --- S5. The re-measured surface ------------------------------------

;; Unit: NEWLINES (`wc -l'), MEASURED 2026-10-21 after the imp-7 fix:
;; loader.scm 1328 -> 1363 -> 1389 -> 1391 -> 1398 (old imp-7 values
;; 1363, 1389 and 1391: the limits block L1 ... L9 (the L9 note of the
;; process-global table is the last 2 lines), the `elisp-loader-macro-drop!'
;; helper and its call in the `defun' branch, and the L10 note of the
;; `defmacro' branch, which is 7 lines); utils.scm 606 UNCHANGED;
;; prelude/load.scm 229 UNCHANGED; probe-imp3.scm 384 -> 437 -> 444 (old
;; imp-7 value 437: the 3 `defun shadow' lines of mode `macros').  Only
;; the loader.scm count moves here; the 3 unchanged counts prove that no
;; OTHER file was touched.
(setq m60-imp7--group 's5)

;; M60 imp-8 (row 27) RE-PIN: loader.scm 1,398 -> 1,409 LINES (the
;; guarded `make-obsolete-variable' install in `init-loader').
;; M60 imp-8 (row 27) RE-PIN: utils.scm 606 -> 640 LINES (the
;; `elisp-make-obsolete-variable' procedure, 1 export NAME and the
;; L11 ... L15 limit block).  The old value was 606.
;; M60 imp-8 (row 27) RE-PIN: probe-imp3.scm 444 -> 471 LINES (mode
;; `obsolete', its comment block, 1 dispatch clause, 1 mode name).
;; M60 imp-9 (row 28a) RE-PIN: loader.scm 1,409 -> 1,511 LINES (the 3
;; branches `cond' / `let*' / `while' and the L16 ... L20 limit
;; block, above them, in `elisp-loader-eval-form').  probe-imp3.scm
;; 471 -> 535 LINES (mode `control') -> 584 LINES (the cr.org fix
;; observables and the REAL path fixture of mode `control').
;; M60 imp-9 fix (cr.org F3, F4, F5; L21) RE-PIN: loader.scm 1,480 -> 1,511 LINES.
;; M60 imp-9 review fix (cr.org F4) RE-PIN: probe-imp3.scm 584 -> 591 LINES
;; (the `let parallel-init' observable of mode `control').
;; M60 imp-10 RE-PIN: row 29 adds 2 `#:use-module' forms and 15
;; guarded installs to loader.scm -- 1,511 -> 1,588 LINES (wc -l) and
;; 23 / 19 -> 38 / 34 LINES (grep -c) -- and mode `arith' to
;; test/m60/probe-imp3.scm (591 -> 691 LINES).  OLD VALUES are the
;; cells that the numbers above replace.
(m60-imp7--check "s5/line-counts"
                 (m60-imp7--all
;; M60 imp-11 RE-PIN: loader.scm 1,588 -> 1,620 LINES (OLD value 1,588).
                  ;; M60 imp-12 RE-PIN: loader.scm 1,620 -> 1,642 LINES (OLD value 1,620).
                  (eql 1642 (m60-imp7--lines "mod/emacs/loader.scm"))
                  (eql 640 (m60-imp7--lines "mod/emacs/utils.scm"))
                  (eql 229 (m60-imp7--lines "prelude/load.scm"))
;; M60 imp-11 RE-PIN: probe-imp3.scm 691 -> 789 LINES (OLD value 691).
                  ;; M60 imp-12 RE-PIN: probe-imp3.scm 789 -> 825 LINES (OLD value 789).
                  (eql 825 (m60-imp7--lines "test/m60/probe-imp3.scm"))))

;; Unit: LINES (`grep -c'), MEASURED 2026-10-21: 22 / 18 / 9, the imp-5
;; values, UNCHANGED.  A macro object in the elisp function cell would
;; move the first two, so these 3 counts are the DESIGN GUARD of row 23.
;; M60 imp-8 (row 27) RE-PIN: loader.scm `symbol-fbound?' 22 -> 23
;; LINES (1 guarded install, the row-18 pattern of `provide').
;; M60 imp-8 (row 27) RE-PIN: loader.scm `set-symbol-function!' 18 -> 19
;; LINES (the same guarded install).  `FIX-.*guilemacs' stays 9.
;; M60 imp-10 RE-PIN: row 29 adds 2 `#:use-module' forms and 15
;; guarded installs to loader.scm -- 1,511 -> 1,588 LINES (wc -l) and
;; 23 / 19 -> 38 / 34 LINES (grep -c) -- and mode `arith' to
;; test/m60/probe-imp3.scm (591 -> 691 LINES).  OLD VALUES are the
;; cells that the numbers above replace.
(m60-imp7--check "s5/grep-c-counts"
;; M60 imp-11 RE-PIN: `symbol-fbound?` 38 -> 39 LINES (OLD value 38).
                 (and (eql 39 (m60-imp7--grep-c "mod/emacs/loader.scm"
                                                "symbol-fbound?"))
;; M60 imp-11 RE-PIN: `set-symbol-function!` 34 -> 35 LINES (OLD value 34).
                      (eql 35 (m60-imp7--grep-c "mod/emacs/loader.scm"
                                                "set-symbol-function!"))
                      (eql 9 (m60-imp7--grep-c "mod/emacs/loader.scm"
                                               "FIX-.*guilemacs"))))

;; The limits of brief.org section 5 are NAMED in the source: L1 (the
;; DECISION of row 24), the L2 ... L6 block of cr.org F2, L7 Row 28 as
;; OPEN, L8 (cr.org F3) and L9 (the process-global macro table with no
;; reset).  A reader who finds a limit here must not read it as a claim.
(m60-imp7--check "s5/limits-named"
                 (m60-imp7--all
                  (m60-imp7--holds-all
                   "mod/emacs/loader.scm"
                   '("DECISION, not a port"
                     "INTERPRETER behaviour"
                     "a compiler drops the body"
                     "row 24 (L1)"
                     "L7 Row 28"))
                  (m60-imp7--holds-all
                   "mod/emacs/loader.scm"
                   '("expansion path: backquote, ,@, cond, let*, while) stays OPEN"))
                  (m60-imp7--holds-all
                   "mod/emacs/loader.scm"
                   '("M60 imp-7 LIMITS of rows 23 and 24"
                     "L9: the table is process-GLOBAL and has no reset"
                     "L2 a macro call expands when the evaluator EVALUATES"
                     "L3 the expander runs on the DYNAMIC binding model"
                     "L4 no `&rest' / `&optional' parameter support"
                     "L5 a DOC element is not stripped"
                     "L6 the table lookup adds 1 `assq'"))
                  (m60-imp7--holds-all
                   "mod/emacs/loader.scm"
                   '("L8 (cr.org F3)"))))

;; L10 (cr.org F2): the asymmetry of the 2 stores is NAMED in the source,
;; and so is the reason why the cell is NOT cleared.  A limit that is
;; named is not a claim, so no call behaviour is promised here.
(m60-imp7--check "s5/l10-named"
                 (m60-imp7--holds-all
                  "mod/emacs/loader.scm"
                  '("L10 (cr.org F2): the drop is ONE-WAY"
                    "leaves the OLD procedure in the"
                    "`else' tests the table FIRST"
                    "design counter 18 of brief.org section 9")))

;;; --- S6. The registration of THIS corpus ----------------------------

(setq m60-imp7--group 's6)

(m60-imp7--check "s6/run-tests-m60-imp7"
                 (m60-imp7--holds-all "tool/run-tests.scm"
                                      '("test/m60/test-m60-imp7.el")))

(m60-imp7--check "s6/imp7-after-imp6"
                 (m60-imp7--ordered-p
                  "tool/run-tests.scm"
                  '("test/m60/test-m60-imp1.el"
                    "test/m60/test-m60-imp2.el"
                    "test/m60/test-m60-imp3.el"
                    "test/m60/test-m60-imp4.el"
                    "test/m60/test-m60-imp5.el"
                    "test/m60/test-m60-imp6.el"
                    "test/m60/test-m60-imp7.el")))

;; The (m60) group must not take the prelude key: a prelude run would
;; load the prelude BEFORE the corpus and hide a missing boot.
(m60-imp7--check "s6/m60-group-no-prelude"
                 (m60-imp7--all
                  (m60-imp7--holds-all "tool/run-tests.scm" '("(group (m60)"))
                  (m60-imp7--holds-none "tool/run-tests.scm"
                                        '("(group (m60 "))))

;;; --- S7. The guards -------------------------------------------------

;; Per-group floors stop a silent loss of a group: S1 7 (old 6), S2 6
;; (old 5), S3 7 (old 6), S4 9, S5 4 (old 3), S6 3 -- the 3 raises are
;; the cr.org F3 checks, the last is the L10 check.
(setq m60-imp7--group 's7)

(m60-imp7--check "s7/min-s1-checks-7" (>= (m60-imp7--group-count 's1) 7))
(m60-imp7--check "s7/min-s2-checks-6" (>= (m60-imp7--group-count 's2) 6))
(m60-imp7--check "s7/min-s3-checks-7" (>= (m60-imp7--group-count 's3) 7))
(m60-imp7--check "s7/min-s4-checks-9" (>= (m60-imp7--group-count 's4) 9))
(m60-imp7--check "s7/min-s5-checks-4" (>= (m60-imp7--group-count 's5) 4))
(m60-imp7--check "s7/min-s6-checks-3" (>= (m60-imp7--group-count 's6) 3))

(m60-imp7--check "s7/prog-absent-routes-to-skip"
                 (and (eq 'skip (m60-imp7--verdict 'm60-imp7-prog-absent))
                      (eq 'skip (m60-imp7--verdict
                                 (m60-imp7--all
                                  'm60-imp7-prog-absent
                                  (m60-imp7--probe-line "macros"
                                                        "defmacro fbound: #f"))))
                      (eq 'absent (m60-imp7--verdict 'm60-imp7-absent))
                      (eq 'absent (m60-imp7--verdict
                                   (m60-imp7--all 'm60-imp7-absent t)))
                      (eq 'pass (m60-imp7--verdict t))
                      (eq 'fail (m60-imp7--verdict nil))
                      (eq 'fail (m60-imp7--verdict (m60-imp7--all t nil)))))

;;; --- The group-total check ------------------------------------------

;; MEASURED: 43 registered checks (S1 7, S2 6, S3 7, S4 9, S5 4, S6 3,
;; S7 7) plus this deftest itself = 44 ERT tests.  Old total at imp-7 was
;; 40; the 3 cr.org F3 checks and the L10 check follow.

(defvar m60-imp7--min-gate-total 44
  "The exact number of m60-imp7 ERT tests: 43 registered checks (S1 7,
S2 6, S3 7, S4 9, S5 4, S6 3, S7 7) plus the group-total deftest
itself.")

(ert-deftest m60-imp7/gate-m60-total ()
  "The m60-imp7 corpus registers at least its docs-independent floor."
  (should (>= (length (ert-select-tests "^m60-imp7" t))
              m60-imp7--min-gate-total)))

(princ (format "=== m60 imp-7 suite done (%d checks; s1 %d, s2 %d, s3 %d, s4 %d, s5 %d, s6 %d, s7 %d) ===\n"
               m60-imp7--registered
               (m60-imp7--group-count 's1)
               (m60-imp7--group-count 's2)
               (m60-imp7--group-count 's3)
               (m60-imp7--group-count 's4)
               (m60-imp7--group-count 's5)
               (m60-imp7--group-count 's6)
               (m60-imp7--group-count 's7)))
