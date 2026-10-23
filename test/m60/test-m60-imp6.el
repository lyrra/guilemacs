;;; test-m60-imp6.el --- M60 imp-6 `defconst' / `defvar' corpus.
;;;
;;; M60 imp-6 lands rows 21 and 22 of the row map of docs/m60-plan.org
;;; section 6: the 2 value-definition special forms, `defconst' and
;;; `defvar'.  They are 2 BRANCHES of `elisp-loader-eval-form'
;;; (mod/emacs/loader.scm :1110), not cells: the names are special
;;; forms, so `init-loader' gets NO new install site.
;;;
;;; Row 21 (`defconst'): evaluate INIT, store it in the value cell
;;; ALWAYS, return the SYMBOL.  Row 22 (`defvar'): store INIT ONLY when
;;; the value cell is EMPTY, and return the SYMBOL.  The `symbol-bound?'
;;; test comes FIRST, because `symbol-value' raises on an empty cell.  A
;;; `defvar' with no INIT leaves the cell EMPTY.  That difference is the
;;; observable that separates the 2 rows.
;;;
;;; Both names are special in elisp.  The minimal evaluator binds
;;; dynamically already (`elisp-loader-bind-thunk'), so the branch adds
;;; no code for that.  A 3rd element (DOC) is IGNORED and NOT evaluated:
;;; `(defconst SYMBOL INIT DOC)' is a declaration, not a call.
;;;
;;; The (m60) group has NO prelude key, so this corpus runs INSIDE the
;;; built src/emacs.  Every plain-guile value is measured by
;;; test/m60/probe-imp3.scm as a `guile -L mod' child process with
;;; GUILE_AUTO_COMPILE=0 -- one MODE per child, so a stub of one mode
;;; can not hide the next result.  Mode `defs' is NEW here.  The 2 forms
;;; change neither `features' nor `load-path', so mode `defs' shares the
;;; boot of the other modes.  `elisp-loader-eval' is NOT in the #:export
;;; list of (emacs loader), so the fixture gets it with `module-ref'.
;;;
;;; It pins these groups:
;;;
;;;   S1 -- the 2 branch sources: 1 `defconst' branch, 1 `defvar'
;;;         branch, the `symbol-bound?' guard, the `#nil' default, the 2
;;;         return values, 0 new install sites, and 1 `cadddr' in
;;;         `elisp-loader-eval-form' (the `if' branch, not the 2 new
;;;         branches).  The 2 counts that name a form are SCOPED to that
;;;         one form (cr.org F4), so a later row can not turn them red.
;;;   S2 -- the branch ORDER and the 2 untouched neighbours: both
;;;         branches after `defun' and before the final `else',
;;;         `elisp-loader-eval' and `elisp-loader-apply' unchanged, no
;;;         `defmacro' branch (row 23 stays open).
;;;   S3 -- the 3 observables and the 3 return values through a live
;;;         `guile' child, mode `defs'.
;;;   S4 -- no regression: modes `cells', `provide', `stubs',
;;;         `negative', `noboot', `require', `registration' and
;;;         `language' keep their values.
;;;   S5 -- the re-measured surface: the 3 LINE counts and the 3
;;;         loader.scm `grep -c' counts.
;;;   S6 -- the registration: the imp-6 line AFTER the imp-5 line,
;;;         imp-1 ... imp-5 kept, (m60) with no prelude key.
;;;   S7 -- the guards: the per-group min counts, the marker-routing
;;;         self-check of the skip path, and the group-total deftest.
;;;
;;; This corpus reads TRACKED files only.  It does NOT read docs/.
;;; A read error is a real error, never a silent pass.  An absent TRACKED
;;; file is a real FAIL.  A missing `guile' binary is an explicit INFO
;;; skip, never a pass: `m60-imp6--check' routes the marker
;;; `m60-imp6-prog-absent' to `m60-imp6--info-skip', and `m60-imp6--all'
;;; carries that marker through a composite check.
;;;
(princ "=== m60 imp-6 defconst/defvar suite ===\n")

(require 'imp-ert-report)

(defvar m60-imp6--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))
(defvar m60-imp6--registered 0
  "Total number of checks this corpus has registered.")
(defvar m60-imp6--group nil
  "The group that `m60-imp6--check' counts into: `s1' .. `s7', or nil.")
(defvar m60-imp6--counts nil
  "Alist of (GROUP . COUNT) for the registered checks.")
(defvar m60-imp6--probe-cache nil
  "Alist of (MODE . RESULT) of the plain-guile probe runs of this corpus.
A mode is measured once per corpus run, so a group starts one child
process, not one per check.")

(defun m60-imp6--group-count (group)
  "Number of checks registered so far in GROUP."
  (or (cdr (assq group m60-imp6--counts)) 0))

(defun m60-imp6--bump-group ()
  "Count one check into `m60-imp6--group'."
  (when m60-imp6--group
    (let ((cell (assq m60-imp6--group m60-imp6--counts)))
      (if cell
          (setcdr cell (1+ (cdr cell)))
        (push (cons m60-imp6--group 1) m60-imp6--counts)))))

;;; --- tracked-file helpers (the imp-1 / imp-4 idioms) ----------------

(defun m60-imp6--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
the symbol `m60-imp6-absent' when REL does not exist.  `case-fold-search'
is bound to nil: the elisp default folds case and inflates a count."
  (let ((path (expand-file-name rel m60-imp6--root)))
    (if (not (file-exists-p path))
        'm60-imp6-absent
      (with-temp-buffer
        (insert-file-contents path)
        (let ((case-fold-search nil))
          (funcall fn))))))

(defun m60-imp6--holds-all (rel needles)
  "Non-nil when the TRACKED file REL holds every NEEDLE.  An absent file
fails the check."
  (m60-imp6--with rel
    (lambda ()
      (let ((all t))
        (dolist (needle needles)
          (goto-char (point-min))
          (unless (search-forward needle nil t) (setq all nil)))
        all))))

(defun m60-imp6--holds-none (rel needles)
  "Non-nil when the TRACKED file REL holds NO needle of NEEDLES."
  (m60-imp6--with rel
    (lambda ()
      (let ((none t))
        (dolist (needle needles)
          (goto-char (point-min))
          (when (search-forward needle nil t) (setq none nil)))
        none))))

(defun m60-imp6--ordered-p (rel needles)
  "Non-nil when the TRACKED file REL holds every NEEDLE in the GIVEN
ORDER: each search starts after the previous match."
  (m60-imp6--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((all t))
        (dolist (needle needles)
          (when all
            (unless (search-forward needle nil t) (setq all nil))))
        all))))

(defun m60-imp6--lines (rel)
  "Count the NEWLINES of REL, the unit of `wc -l'."
  (m60-imp6--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (search-forward "\n" nil t) (setq n (1+ n)))
        n))))

(defun m60-imp6--grep-c (rel regexp)
  "Count the LINES of REL that match REGEXP, the unit of `grep -c'."
  (m60-imp6--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (not (eobp))
          (when (re-search-forward regexp (line-end-position) t)
            (setq n (1+ n)))
          (forward-line 1))
        n))))

(defun m60-imp6--literal-lines (rel needle)
  "Count the LINES of REL that hold NEEDLE as a LITERAL substring.  Use
this helper and not `m60-imp6--grep-c' where NEEDLE holds a regexp
metacharacter: `?' is the `optional' operator of the search syntax, so
the guard pattern never matches the source line that it names (MEASURED
2026-10-21)."
  (m60-imp6--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (not (eobp))
          (when (search-forward needle (line-end-position) t)
            (setq n (1+ n)))
          (forward-line 1))
        n))))

(defun m60-imp6--literal-lines-in-eval-form (needle)
  "Count the LINES of `elisp-loader-eval-form' that hold NEEDLE as a
LITERAL substring, or return the symbol `m60-imp6-absent'.  The region
is SCOPED: a file-wide pin turns a check of rows 21 and 22 red when an
UNRELATED row adds the same text, and the red check then names the wrong
cause (cr.org F4).  The form starts at
`(define (elisp-loader-eval-form form)' (:1110) and ends at the next
top-level `(define' (:1194)."
  (m60-imp6--with "mod/emacs/loader.scm"
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

(defun m60-imp6--probe-1 (mode)
  "Run test/m60/probe-imp3.scm in MODE as a `guile -L mod' child
process, with GUILE_AUTO_COMPILE=0 and GUILEMACS_ROOT set, and with
`default-directory' at the repo root.  Return (EXIT . OUTPUT), where
OUTPUT holds stdout AND stderr, or the symbol `m60-imp6-prog-absent'
when the `guile' binary is not on PATH."
  (if (not (executable-find "guile"))
      'm60-imp6-prog-absent
    (let ((buf (get-buffer-create " *m60-imp6-probe*"))
          (default-directory m60-imp6--root)
          (process-environment
           (append (list (concat "GUILEMACS_ROOT=" m60-imp6--root)
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

(defun m60-imp6--probe (mode)
  "The cached result of `m60-imp6--probe-1' for MODE."
  (let ((cell (assoc mode m60-imp6--probe-cache)))
    (if cell
        (cdr cell)
      (let ((result (m60-imp6--probe-1 mode)))
        (push (cons mode result) m60-imp6--probe-cache)
        result))))

(defun m60-imp6--probe-raw (mode)
  "The OUTPUT of the probe MODE whatever the exit status is, or the
marker `m60-imp6-prog-absent'.  Mode `registration' raises on purpose,
so its output is only readable this way."
  (let ((result (m60-imp6--probe mode)))
    (cond
     ((eq result 'm60-imp6-prog-absent) result)
     ((consp result) (cdr result))
     (t nil))))

(defun m60-imp6--probe-output (mode)
  "The OUTPUT of the probe MODE when the child exited 0, else nil.  A
crash mid-mode printed a partial output, so the exit status is part of
every output check.  When the `guile' binary is absent, the marker
`m60-imp6-prog-absent' is returned instead of nil, so the caller can
SKIP and not pass or fail."
  (let ((result (m60-imp6--probe mode)))
    (cond
     ((eq result 'm60-imp6-prog-absent) result)
     ((and (consp result) (eql 0 (car result))) (cdr result))
     (t nil))))

(defun m60-imp6--probe-line (mode line)
  "Non-nil when the probe MODE printed LINE as one WHOLE line and the
child exited 0.  A substring match is NOT enough: a line pin holds the
whole line, so a changed value can not hide inside it."
  (let ((out (m60-imp6--probe-output mode)))
    (cond
     ((eq out 'm60-imp6-prog-absent) out)
     ((not (stringp out)) nil)
     (t (with-temp-buffer
          (insert "\n" out "\n")
          (goto-char (point-min))
          (and (search-forward (concat "\n" line "\n") nil t) t))))))

(defun m60-imp6--probe-holds (mode needle)
  "Non-nil when the OUTPUT of the probe MODE holds NEEDLE (a substring
pin; use it only where an address sits in the text)."
  (let ((out (m60-imp6--probe-output mode)))
    (cond
     ((eq out 'm60-imp6-prog-absent) out)
     ((not (stringp out)) nil)
     (t (with-temp-buffer
          (insert out)
          (goto-char (point-min))
          (and (search-forward needle nil t) t))))))

(defun m60-imp6--probe-holds-none (mode needle)
  "Non-nil when the OUTPUT of the probe MODE holds NO NEEDLE."
  (let ((out (m60-imp6--probe-output mode)))
    (cond
     ((eq out 'm60-imp6-prog-absent) out)
     ((not (stringp out)) nil)
     (t (with-temp-buffer
          (insert out)
          (goto-char (point-min))
          (not (search-forward needle nil t)))))))

(defun m60-imp6--probe-raw-holds (mode needle)
  "Non-nil when the RAW output of the probe MODE holds NEEDLE, whatever
the exit status is."
  (let ((out (m60-imp6--probe-raw mode)))
    (cond
     ((eq out 'm60-imp6-prog-absent) out)
     ((not (stringp out)) nil)
     (t (with-temp-buffer
          (insert out)
          (goto-char (point-min))
          (and (search-forward needle nil t) t))))))

(defun m60-imp6--all (&rest values)
  "`and' over the ALREADY-EVALUATED VALUES, with one difference: a
MARKER wins over a nil.  Both markers are truthy, so a plain `and'
returns the value of a LATER form and the check reads as a PASS.  The
verdict order matches `m60-imp6--verdict': the absent FILE marker first
(a real FAIL), then the absent `guile' marker (a skip), then nil (a
FAIL), then t (a PASS)."
  (cond
   ((memq 'm60-imp6-absent values) 'm60-imp6-absent)
   ((memq 'm60-imp6-prog-absent values) 'm60-imp6-prog-absent)
   ((memq nil values) nil)
   (t t)))

;;; --- report helpers -------------------------------------------------

(defun m60-imp6--verdict (ok)
  "Classify the value OK of one check: `pass', `fail', `absent' (the
TRACKED file is missing -- a real FAIL), or `skip' (the `guile' binary is
not on PATH, so the probe could not run -- never a pass)."
  (cond
   ((eq ok 'm60-imp6-prog-absent) 'skip)
   ((eq ok 'm60-imp6-absent) 'absent)
   (ok 'pass)
   (t 'fail)))

(defun m60-imp6--check (name ok)
  "Report and register one check.  The 4 outcomes come from
`m60-imp6--verdict': an absent TRACKED file prints FAIL (a real error,
not a pass), and an absent `guile' binary prints INFO and registers a
controlled ERT skip -- never a pass."
  (let ((verdict (m60-imp6--verdict ok)))
    (cond
     ((eq verdict 'skip)
      (m60-imp6--info-skip name "no guile binary on PATH"))
     ((eq verdict 'absent)
      (princ (format "FAIL m60/imp6/%s (source file absent)\n" name))
      (setq m60-imp6--registered (1+ m60-imp6--registered))
      (m60-imp6--bump-group)
      (imp-register-bool-as-ert-test (format "m60-imp6/%s" name) nil))
     (t
      (princ (format "%s m60/imp6/%s\n"
                     (if (eq verdict 'pass) "PASS" "FAIL") name))
      (setq m60-imp6--registered (1+ m60-imp6--registered))
      (m60-imp6--bump-group)
      (imp-register-bool-as-ert-test (format "m60-imp6/%s" name)
                                     (eq verdict 'pass))))))

(defun m60-imp6--info-skip (name reason)
  "Register one explicit INFO skip, counted into the current group.  A
host limit is a skip, never a pass."
  (princ (format "INFO m60/imp6/%s %s\n" name reason))
  (setq m60-imp6--registered (1+ m60-imp6--registered))
  (m60-imp6--bump-group)
  (imp-register-skip-as-ert-test (format "m60-imp6/%s" name) reason))

;;; --- S1. The 2 branch sources ----------------------------------------

;; ONE branch per name.  MEASURED 2026-10-21: 1 `defconst' branch and 1
;; `defvar' branch in mod/emacs/loader.scm (`grep -c').  Unit: LINES.
(setq m60-imp6--group 's1)

(m60-imp6--check "s1/one-branch-each"
                 (m60-imp6--all
                  (eql 1 (m60-imp6--literal-lines
                          "mod/emacs/loader.scm" "((eq? head 'defconst)"))
                  (eql 1 (m60-imp6--literal-lines
                          "mod/emacs/loader.scm" "((eq? head 'defvar)"))))

;; Row 22 stores ONLY into an empty cell, so the `symbol-bound?' test
;; must come FIRST: `symbol-value' raises on an empty cell.  A branch
;; that read the cell directly would break `(defvar NAME)'.
(m60-imp6--check "s1/defvar-guard-first"
                 (m60-imp6--all
                  (eql 1 (m60-imp6--literal-lines
                          "mod/emacs/loader.scm"
                          "(and (pair? (cddr form)) (not (symbol-bound? name)))"))
                  ;; The guard runs BEFORE the store.  (A file-wide
                  ;; `holds-none "(symbol-value name)"' would fail:
                  ;; `elisp-loader-bind-thunk' reads that cell too.)
                  (m60-imp6--ordered-p
                   "mod/emacs/loader.scm"
                   '("((eq? head 'defvar)"
                     "(not (symbol-bound? name))"
                     "(set-symbol-value! name"))))

;; Row 21 stores ALWAYS.  With no INIT the branch still BINDS the cell,
;; to the elisp nil: that is the observable that separates the 2 rows.
(m60-imp6--check "s1/defconst-nil-default"
                 (m60-imp6--ordered-p
                  "mod/emacs/loader.scm"
                  '("((eq? head 'defconst)"
                    "(if (pair? (cddr form))"
                    "#nil))"
                    "((eq? head 'defvar)")))

;; RISK A5 of the review: `set-symbol-value!' returns the VALUE, so a
;; branch that ENDS with that call hands a loaded file the value, not
;; the symbol.  Both branches return the SYMBOL: `(cadr form)' and
;; `name'.  Unit: the ORDER of the branch text, so a value-only pin can
;; not pass here.
(m60-imp6--check "s1/both-branches-return-the-symbol"
                 (m60-imp6--ordered-p
                  "mod/emacs/loader.scm"
                  '("((eq? head 'defconst)"
                    "(elisp-loader-eval (caddr form))"
                    "#nil))"
                    "(cadr form))"
                    "((eq? head 'defvar)"
                    "(not (symbol-bound? name))"
                    "(set-symbol-value! name (elisp-loader-eval (caddr form))))"
                    "name))")))

;; The 2 names are SPECIAL FORMS, not function cells: `init-loader' must
;; get NO new install site (`brief.org' section 4).  MEASURED: 0 sites in
;; loader.scm and 0 in the prelude.
(m60-imp6--check "s1/zero-install-sites"
                 (m60-imp6--all
                  (m60-imp6--holds-none
                   "mod/emacs/loader.scm"
                   '("(set-symbol-function! 'defconst"
                     "(set-symbol-function! 'defvar"))
                  (m60-imp6--holds-none
                   "prelude/load.scm"
                   '("set-symbol-function! 'defconst"
                     "set-symbol-function! 'defvar"))))

;; The DOC element is ignored and NOT evaluated.  MEASURED: the whole
;; `elisp-loader-eval-form' form holds ONE `(cadddr form)', and it is the
;; `if' branch (:1128), not the 2 new branches.  The count is SCOPED to
;; that one form (cr.org F4), so a later row that reads a 4th element can
;; not turn this check red.  The live pin of this property is
;; `s3/defconst-doc-not-evaluated'.  NOTE: DOC is not STORED for
;; `documentation' either: this evaluator has no docstring slot, so a
;; later `documentation' port must add it (cr.org F5).
(m60-imp6--check "s1/doc-is-not-read"
                 (m60-imp6--all
                  (eql 1 (m60-imp6--literal-lines-in-eval-form
                          "(cadddr form)"))))

;;; --- S2. The branch order and the 2 untouched neighbours -------------

;; MEASURED order: after the `defun' branch (:1148) and before the final
;; `else'.  The last needle is the body of that `else'.
(setq m60-imp6--group 's2)

(m60-imp6--check "s2/ordered-after-defun-before-else"
                 (m60-imp6--ordered-p
                  "mod/emacs/loader.scm"
                  '("((eq? head 'defun)"
                    "(elisp-loader-make-procedure (caddr form)"
                    "((eq? head 'defconst)"
                    "((eq? head 'defvar)"
                    "(throw 'void-function head)")))

;; The dispatcher and the apply entry are NOT changed: the same 2
;; branches, the same pair forms, the same `progn' branch.
(m60-imp6--check "s2/eval-unchanged"
                 (m60-imp6--all
                  (eql 1 (m60-imp6--literal-lines
                          "mod/emacs/loader.scm"
                          "(define (elisp-loader-eval form)"))
                  (eql 1 (m60-imp6--literal-lines
                          "mod/emacs/loader.scm"
                          "((pair? form) (elisp-loader-eval-form form))"))
                  ;; RE-PINNED at M60 imp-7: 1 -> 2 LITERAL LINES.  The
                  ;; `eval-when-compile' branch of row 24 adds the 2nd.
                  ;; M60 imp-12 RE-PIN: 2 -> 3 LITERAL LINES.  The
                  ;; `eval-and-compile' branch of row 31 adds the 3rd.
                  (eql 3 (m60-imp6--literal-lines
                          "mod/emacs/loader.scm"
                          "(elisp-loader-eval-seq (cdr form))"))))


;; RE-PINNED at M60 imp-7: row 23 CLOSED, so the pin flips from ABSENCE
;; to PRESENCE.  RENAMED with the assertion: the old name
;; `s2/no-defmacro-branch' named the ABSENCE that no longer holds, so it
;; is `s2/defmacro-branch' now.  The old check was a `holds-none' of
;; `((eq? head 'defmacro)'.
(m60-imp6--check "s2/defmacro-branch"
                 (m60-imp6--holds-all "mod/emacs/loader.scm"
                                      '("((eq? head 'defmacro)")))

;;; --- S3. The observables (mode `defs') -------------------------------

;; A plain `guile -L mod' process, one child for this group.  MEASURED
;; 2026-10-21: `defconst' stores TWICE, `defvar' stores ONCE.
(setq m60-imp6--group 's3)

(m60-imp6--check "s3/defconst-stores-twice"
                 (m60-imp6--all
                  (m60-imp6--probe-line "defs"
                                        "defconst ret: m60-probe-c / m60-probe-c")
                  (m60-imp6--probe-line "defs" "defconst value: 2")))

;; The DOC element of the form is `(/ 1 0)'.  A branch that evaluated it
;; would raise, so the line proves that DOC is NOT evaluated.
(m60-imp6--check "s3/defconst-doc-not-evaluated"
                 (m60-imp6--all
                  (m60-imp6--probe-line "defs" "defconst doc ret: m60-probe-d")
                  (m60-imp6--probe-line "defs" "defconst doc value: 1")))

(m60-imp6--check "s3/defvar-stores-once"
                 (m60-imp6--all
                  (m60-imp6--probe-line "defs"
                                        "defvar ret: m60-probe-v / m60-probe-v")
                  (m60-imp6--probe-line "defs" "defvar value: 1")))

;; The observable that separates the 2 rows: a `defvar' with no INIT
;; leaves the cell EMPTY, so the symbol stays UNBOUND.
(m60-imp6--check "s3/defvar-no-init-stays-unbound"
                 (m60-imp6--all
                  (m60-imp6--probe-line "defs" "defvar no-init ret: m60-probe-w")
                  (m60-imp6--probe-line "defs" "defvar no-init bound: #f")))

;; A1 of the review: `(defconst SYMBOL)' is NOT legal elisp (INIT is
;; required).  The branch is LENIENT and BINDS the cell to #nil.  This is
;; a DEVIATION, pinned as such -- not as elisp behaviour.
(m60-imp6--check "s3/defconst-no-init-lenient"
                 (m60-imp6--probe-line
                  "defs" "defconst no-init bound (lenient): #t"))

;;; --- S4. No regression on the 8 older modes --------------------------

(setq m60-imp6--group 's4)

;; Mode `cells' installs neither branch itself, so these words come from
;; the loader source only.  RE-PINNED: the obarray stop is now the
;; `make-obsolete-variable' call (row 27), not `(defconst)'.
(m60-imp6--check "s4/cells-unchanged"
                 (m60-imp6--all
                  (m60-imp6--probe-line "cells" "EMPTY-CELLS: ()")
                  (m60-imp6--probe-line
                   "cells" "UNGUARDED: load=#t autoload-do-load=#t")
                  (m60-imp6--probe-line
                   "cells"
                   (concat "VARS: load-path=#t load-suffixes=#t"
                           " load-file-rep-suffixes=#t load-read-function=#t"))
                  (m60-imp6--probe-line "cells" "ASYM: require=#t provide=#t")
                  (m60-imp6--probe-line "cells" "LOAD lisp/cdl.el: done")
                  (m60-imp6--probe-line "cells" "features: (cdl)")
                  (m60-imp6--probe-line "cells" "FEATURES-BOUND: #t")))

;; The 2 stops that rows 21 and 22 close, and the 2 that stay open.
;; RE-PINNED at M60 imp-7: rows 23 and 24 close the hex-util stop, so
;; the file loads to the END.  The old line was `LOAD lisp/hex-util.el:
;; ERROR void-function (eval-when-compile)'.
;; M60 imp-8 (row 27) RE-PIN: this line is `done' now; the old pin was
;; the `ERROR void-function (make-obsolete-variable)' line of row 27.
(m60-imp6--check "s4/cells-stops"
                 (m60-imp6--all
                  (m60-imp6--probe-line
                   "cells"
                   "LOAD lisp/obarray.el: done")
                  (m60-imp6--probe-line "cells" "LOAD lisp/hex-util.el: done")))

(m60-imp6--check "s4/provide-unchanged"
                 (m60-imp6--all
                  (m60-imp6--probe-line "provide" "features-bound-at-start: #t")
                  (m60-imp6--probe-line "provide" "provide-fbound-at-start: #t")
                  (m60-imp6--probe-line "provide" "LOAD cdl: done")
                  (m60-imp6--probe-line "provide" "require-fbound: #t")))

;; RE-PINNED at imp-6: the real `defconst' branch matches FIRST, so the
;; pure `defconst' stub is DEAD and the obarray stop is now a FUNCTION.
;; M60 imp-8 (row 27) RE-PIN: this line is `done' now; the old pin was
;; the `ERROR void-function (make-obsolete-variable)' line of row 27.
(m60-imp6--check "s4/stubs-blockers"
                 (m60-imp6--all
                  (m60-imp6--probe-line "stubs" "stub-provide / cdl: done")
                  (m60-imp6--probe-line
                   "stubs"
                   "stub-defconst / obarray: done")
                  ;; RE-PINNED at M60 imp-7: the real `eval-when-compile'
                  ;; branch matches FIRST, so that stub is DEAD and the
                  ;; file loads to the END.  The old line was
                  ;; `stub-eval-when-compile / hex-util: ERROR
                  ;; void-function (defmacro)'.
                  (m60-imp6--probe-line "stubs"
                                        "stub-eval-when-compile / hex-util: done")
                  (m60-imp6--probe-line "stubs" "stub-ntl / subdirs: done")))

;; The imp-4 negative control still names the unbound sentinel.  The
;; address changes per run, so the pin holds WORDS, not a LINE.
(m60-imp6--check "s4/negative-control"
                 (m60-imp6--all
                  (m60-imp6--probe-line "negative" "features-bound: #f")
                  (m60-imp6--probe-line "negative" "provide-fbound: #t")
                  (m60-imp6--probe-holds "negative" "LOAD cdl: ERROR wrong-type-arg")
                  (m60-imp6--probe-holds "negative" "\"memq\"")
                  (m60-imp6--probe-holds "negative" "uninterned-symbol unbound")
                  (m60-imp6--probe-holds-none "negative" "void-function")))

(m60-imp6--check "s4/noboot-unchanged"
                 (m60-imp6--all
                  (m60-imp6--probe-line "noboot" "features-bound: #f")
                  (m60-imp6--probe-holds "noboot" "Wrong type to apply")))

(m60-imp6--check "s4/require-unchanged"
                 (m60-imp6--all
                  (m60-imp6--probe-line "require" "REQUIRE-FBOUND: #t")
                  (m60-imp6--probe-line "require" "features-at-start: ()")
                  (m60-imp6--probe-line "require" "REQUIRE cdl: cdl")
                  (m60-imp6--probe-line "require" "features: (cdl)")
                  (m60-imp6--probe-line "require" "REQUIRE-AGAIN: cdl")))

;; The registration row keeps its NEXT blocker (row 26), and the language
;; object still resolves.  Mode `registration' raises on purpose, so its
;; output is read raw.
(m60-imp6--check "s4/registration-and-language"
                 (m60-imp6--all
                  (m60-imp6--probe-raw-holds "registration"
                                             "Unbound variable: mapcar")
                  (m60-imp6--probe-line "language" "LANGUAGE?: #t")
                  (m60-imp6--probe-line "language"
                                        "LANGUAGE-TITLE: \"Modern Emacs Lisp\"")
                  (m60-imp6--probe-line "language" "LANGUAGE-NAME: emacs-elisp")))

;;; --- S5. The re-measured surface ------------------------------------

;; Unit: NEWLINES (`wc -l'), MEASURED 2026-10-21 after the change:
;; loader.scm 1308 + 20, utils.scm 606, prelude/load.scm 229.  The 2
;; branches add LINES to the FIRST count only.
(setq m60-imp6--group 's5)



;;; --- S6. The registration of THIS corpus ----------------------------

(setq m60-imp6--group 's6)

(m60-imp6--check "s6/run-tests-m60-imp6"
                 (m60-imp6--holds-all "tool/run-tests.scm"
                                      '("test/m60/test-m60-imp6.el")))

(m60-imp6--check "s6/imp6-after-imp5"
                 (m60-imp6--ordered-p
                  "tool/run-tests.scm"
                  '("test/m60/test-m60-imp1.el"
                    "test/m60/test-m60-imp2.el"
                    "test/m60/test-m60-imp3.el"
                    "test/m60/test-m60-imp4.el"
                    "test/m60/test-m60-imp5.el"
                    "test/m60/test-m60-imp6.el")))

;; The (m60) group must not take the prelude key: a prelude run would
;; load the prelude BEFORE the corpus and hide a missing boot.
(m60-imp6--check "s6/m60-group-no-prelude"
                 (m60-imp6--all
                  (m60-imp6--holds-all "tool/run-tests.scm" '("(group (m60)"))
                  (m60-imp6--holds-none "tool/run-tests.scm"
                                        '("(group (m60 "))))

;;; --- S7. The guards -------------------------------------------------

;; Per-group floors stop a silent loss of a group: S1 6, S2 4, S3 5,
;; S4 8, S5 2, S6 3.
(setq m60-imp6--group 's7)

(m60-imp6--check "s7/min-s1-checks-6" (>= (m60-imp6--group-count 's1) 6))
(m60-imp6--check "s7/min-s2-checks-3" (>= (m60-imp6--group-count 's2) 3))
(m60-imp6--check "s7/min-s3-checks-5" (>= (m60-imp6--group-count 's3) 5))
(m60-imp6--check "s7/min-s4-checks-8" (>= (m60-imp6--group-count 's4) 8))
(m60-imp6--check "s7/min-s6-checks-3" (>= (m60-imp6--group-count 's6) 3))

(m60-imp6--check "s7/prog-absent-routes-to-skip"
                 (and (eq 'skip (m60-imp6--verdict 'm60-imp6-prog-absent))
                      (eq 'skip (m60-imp6--verdict
                                 (m60-imp6--all
                                  'm60-imp6-prog-absent
                                  (m60-imp6--probe-line "defs"
                                                        "defconst value: 2"))))
                      (eq 'absent (m60-imp6--verdict 'm60-imp6-absent))
                      (eq 'absent (m60-imp6--verdict
                                   (m60-imp6--all 'm60-imp6-absent t)))
                      (eq 'pass (m60-imp6--verdict t))
                      (eq 'fail (m60-imp6--verdict nil))
                      (eq 'fail (m60-imp6--verdict (m60-imp6--all t nil)))))

;;; --- The group-total check ------------------------------------------

(defvar m60-imp6--min-gate-total 32
  "Minimum registered ERT test count for this corpus.")

(ert-deftest m60-imp6/gate-m60-total ()
  "The m60-imp6 corpus registers at least its docs-independent floor."
  (should (>= (length (ert-select-tests "^m60-imp6" t))
              m60-imp6--min-gate-total)))

(princ (format "=== m60 imp-6 suite done (%d checks; s1 %d, s2 %d, s3 %d, s4 %d, s5 %d, s6 %d, s7 %d) ===\n"
               m60-imp6--registered
               (m60-imp6--group-count 's1)
               (m60-imp6--group-count 's2)
               (m60-imp6--group-count 's3)
               (m60-imp6--group-count 's4)
               (m60-imp6--group-count 's5)
               (m60-imp6--group-count 's6)
               (m60-imp6--group-count 's7)))
