;;; test-m60-imp2.el --- M60 imp-2 standalone-load boundary MEASUREMENT.
;;;
;;; M60 imp-1 wrote the audit.  M60 imp-2 is the MEASUREMENT step: it
;;; re-runs the probes of docs/m60-plan.org section 3 in a plain `guile'
;;; subprocess and pins what it measures.  C delta 0.  Scheme delta 0.
;;;
;;; The (m60) group has NO prelude key, so this corpus runs INSIDE the
;;; built src/emacs (run-tests-loadup-emacs).  Every measurement is taken
;;; by test/m60/probe-imp2.scm, which this corpus runs as a `guile -L
;;; mod' child process with GUILE_AUTO_COMPILE=0 -- the real plain-guile
;;; path, not an Emacs internals shim.  One MODE per child process, so a
;;; stub of one mode can not hide the next result (limit L3).
;;;
;;; It pins these groups:
;;;
;;;   R1 -- the surface, re-measured: the 6 line counts, the 3
;;;         loader.scm grep LINE counts, the tree-wide scm_c_public_ref
;;;         OCCURRENCE count, the test/mod FILES, the mod/emacs-elisp
;;;         ENTRIES, and the 2 fixture files of this imp.
;;;   R2 -- the ordered cell list: the 11 guarded installs in call
;;;         order, the 2 unguarded cells, the 4 variable binds,
;;;         EMPTY-CELLS = () (MEASURED), and the provide / require
;;;         asymmetry.
;;;   R3 -- the 4 first stops, one check per lisp/ file, plus the
;;;         unbound `features' variable.
;;;   R4 -- the ordered stub chain, the `defvar' stop, the last good
;;;         point ((featurep 'cdl) = #t), and the negative control in
;;;         its own process.
;;;   R5 -- the registration: the exit status, the exact error text, the
;;;         2 spec.scm sites, the live prelude patch, and the C site.
;;;   R6 -- the registration of THIS corpus: the imp-2 line AFTER the
;;;         imp-1 line, imp-1 kept, (m60) after (m59), no prelude key.
;;;   R7 -- the per-group min-count guards, the marker-routing
;;;         self-check of the skip path, plus the in-process
;;;         group-total `ert-deftest' selecting ^m60-imp2.
;;;
;;; This corpus reads TRACKED files only (src/, mod/, prelude/,
;;; tool/run-tests.scm, test/m60/).  It does NOT read docs/
;;; (docs/kb.org test-must-not-read-docs).
;;;
;;; A read error is a real error, never a silent pass.  An absent
;;; TRACKED file is a real FAIL.  A missing `guile' binary is an explicit
;;; INFO skip, never a pass: `m60-imp2--check' routes the marker
;;; `m60-imp2-prog-absent' to `m60-imp2--info-skip', and
;;; `m60-imp2--all' carries that marker through a composite check, so no
;;; probe check can print PASS on a host without `guile'
;;; (cr.org F4).  Every pin names its MEASURE UNIT:
;;; `m60-imp2--grep-c' counts LINES (the unit of `grep -c'),
;;; `m60-imp2--count' counts OCCURRENCES (the unit of
;;; `grep -o | wc -l'), `m60-imp2--lines' counts NEWLINES (the unit of
;;; `wc -l'), and `m60-imp2--dir-entries' counts directory ENTRIES.
;;;
;;; Every value below was MEASURED on this host on 2026-10-20 by running
;;; the fixture and the commands that are named in the comment of each
;;; check.  No value is copied from brief.org or from
;;; docs/m60-plan.org.
;;;
;;; BASE CITE (cr.org F1): the measured base is 3603a6795, an ANCESTOR of
;;; HEAD.  No file of src/, mod/, or prelude/ differs between 3603a6795
;;; and the commit that adds this corpus, so a pin of those files is
;;; true at the ancestor.  The imp-1 corpus and its 1-line count fix
;;; arrived in the SAME commit as this corpus, so a cite of a separate
;;; imp-1 commit would name a commit that is NOT an ancestor
;;; (=draft-commit-versus-landed-commit=).

(princ "=== m60 imp-2 standalone-load boundary measurement suite ===\n")

(require 'imp-ert-report)

(defvar m60-imp2--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))
(defvar m60-imp2--registered 0
  "Total number of checks this corpus has registered.")
(defvar m60-imp2--group nil
  "The group that `m60-imp2--check' counts into: `r1' .. `r7', or nil.")
(defvar m60-imp2--counts nil
  "Alist of (GROUP . COUNT) for the registered checks.")
(defvar m60-imp2--probe-cache nil
  "Alist of (MODE . RESULT) of the plain-guile probe runs of this corpus.
A mode is measured once per corpus run, so a 5-check group starts one
child process, not 5.")

(defun m60-imp2--group-count (group)
  "Number of checks registered so far in GROUP."
  (or (cdr (assq group m60-imp2--counts)) 0))

(defun m60-imp2--bump-group ()
  "Count one check into `m60-imp2--group'."
  (when m60-imp2--group
    (let ((cell (assq m60-imp2--group m60-imp2--counts)))
      (if cell
          (setcdr cell (1+ (cdr cell)))
        (push (cons m60-imp2--group 1) m60-imp2--counts)))))

;;; --- tracked-file helpers (the imp-1 idioms) -------------------------

(defun m60-imp2--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
the symbol `m60-imp2-absent' when REL does not exist.  `case-fold-search'
is bound to nil: the elisp default folds case and inflates a count."
  (let ((path (expand-file-name rel m60-imp2--root)))
    (if (not (file-exists-p path))
        'm60-imp2-absent
      (with-temp-buffer
        (insert-file-contents path)
        (let ((case-fold-search nil))
          (funcall fn))))))

(defun m60-imp2--text-of (rel)
  "The contents of REL as a string, or the symbol `m60-imp2-absent'."
  (m60-imp2--with rel
    (lambda ()
      (buffer-substring-no-properties (point-min) (point-max)))))

(defun m60-imp2--holds-all (rel needles)
  "Non-nil when the TRACKED file REL holds every NEEDLE.  An absent file
fails the check."
  (m60-imp2--with rel
    (lambda ()
      (let ((all t))
        (dolist (needle needles)
          (goto-char (point-min))
          (unless (search-forward needle nil t) (setq all nil)))
        all))))

(defun m60-imp2--holds-none (rel needles)
  "Non-nil when the TRACKED file REL holds NO needle of NEEDLES."
  (m60-imp2--with rel
    (lambda ()
      (let ((none t))
        (dolist (needle needles)
          (goto-char (point-min))
          (when (search-forward needle nil t) (setq none nil)))
        none))))

(defun m60-imp2--live-p (rel needle)
  "Non-nil when the TRACKED file REL holds NEEDLE on a line that is NOT
commented out."
  (m60-imp2--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((hit nil))
        (while (and (not hit) (search-forward needle nil t))
          (setq hit (save-excursion
                      (goto-char (line-beginning-position))
                      (not (looking-at-p "[ \t]*;")))))
        hit))))

(defun m60-imp2--ordered-p (rel needles)
  "Non-nil when the TRACKED file REL holds every NEEDLE in the GIVEN
ORDER: each search starts after the previous match."
  (m60-imp2--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((all t))
        (dolist (needle needles)
          (when all
            (unless (search-forward needle nil t) (setq all nil))))
        all))))

(defun m60-imp2--exists-p (rel)
  "Non-nil when REL exists in the tree at `m60-imp2--root'."
  (file-exists-p (expand-file-name rel m60-imp2--root)))

(defun m60-imp2--dir-entries (rel)
  "Count the entries of the directory REL, the unit of `ls | wc -l'."
  (let ((path (expand-file-name rel m60-imp2--root)))
    (if (not (file-directory-p path))
        'm60-imp2-absent
      (length (directory-files path nil "\\`[^.]")))))

(defun m60-imp2--lines (rel)
  "Count the NEWLINES of REL, the unit of `wc -l'."
  (m60-imp2--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (search-forward "\n" nil t) (setq n (1+ n)))
        n))))

(defun m60-imp2--grep-c (rel regexp)
  "Count the LINES of REL that match REGEXP, the unit of `grep -c'."
  (m60-imp2--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (not (eobp))
          (when (re-search-forward regexp (line-end-position) t)
            (setq n (1+ n)))
          (forward-line 1))
        n))))

(defun m60-imp2--count (rel regexp)
  "Count the OCCURRENCES of REGEXP in REL, the unit of
`grep -o | wc -l'.  This is NOT the unit of `grep -c'."
  (m60-imp2--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (re-search-forward regexp nil t) (setq n (1+ n)))
        n))))

(defun m60-imp2--line-of (rel regexp)
  "Return the 1-based line number of the first REGEXP match in REL, or
nil when REGEXP does not match.  The match END is read into a variable
BEFORE the newline loop: a loop that re-reads `(match-beginning 0)' takes
the match data of its own `search-forward' and raises
`Invalid search bound (wrong side of point)' (MEASURED)."
  (m60-imp2--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n nil))
        (when (re-search-forward regexp nil t)
          (let ((end (match-beginning 0)))
            (save-excursion
              (goto-char (point-min))
              (let ((line 1))
                (while (search-forward "\n" end t)
                  (setq line (1+ line)))
                (setq n line)))))
        n))))

(defun m60-imp2--count-scm-ref ()
  "Count scm_c_public_ref over src/*.[ch], the unit of
`grep -h scm_c_public_ref src/*.c src/*.h | wc -l'.  Unit: OCCURRENCES."
  (let ((total 0)
        (dir (expand-file-name "src" m60-imp2--root)))
    (dolist (f (directory-files dir t "\\.[ch]\\'"))
      (setq total (+ total (or (m60-imp2--count f "scm_c_public_ref") 0))))
    total))

;;; --- the plain-guile probe runner -----------------------------------

(defun m60-imp2--probe-1 (mode)
  "Run test/m60/probe-imp2.scm in MODE as a `guile -L mod' child
process, with GUILE_AUTO_COMPILE=0 and GUILEMACS_ROOT set, and with
`default-directory' at the repo root.  Return (EXIT . OUTPUT), where
OUTPUT holds stdout AND stderr, or the symbol `m60-imp2-prog-absent'
when the `guile' binary is not on PATH."
  (if (not (executable-find "guile"))
      'm60-imp2-prog-absent
    (let ((buf (get-buffer-create " *m60-imp2-probe*"))
          (default-directory m60-imp2--root)
          (process-environment
           (append (list (concat "GUILEMACS_ROOT=" m60-imp2--root)
                         "GUILE_AUTO_COMPILE=0")
                   process-environment)))
      (unwind-protect
          (progn
            (with-current-buffer buf (erase-buffer))
            (let ((exit (apply #'call-process
                               "guile" nil buf nil
                               (list "-L" "mod"
                                     "test/m60/probe-imp2.scm"
                                     mode))))
              (cons exit (with-current-buffer buf
                           (buffer-substring-no-properties
                            (point-min) (point-max))))))
        (kill-buffer buf)))))

(defun m60-imp2--probe (mode)
  "The cached result of `m60-imp2--probe-1' for MODE."
  (let ((cell (assoc mode m60-imp2--probe-cache)))
    (if cell
        (cdr cell)
      (let ((result (m60-imp2--probe-1 mode)))
        (push (cons mode result) m60-imp2--probe-cache)
        result))))

(defun m60-imp2--probe-output (mode)
  "The OUTPUT of the probe MODE when the child exited 0, else nil.  A
crash mid-mode printed a partial output, so the exit status is part of
every output check: a partial output can not pass.  When the `guile'
binary is absent, the marker `m60-imp2-prog-absent' is returned instead
of nil, so the caller can SKIP and not pass or fail (cr.org F4)."
  (let ((result (m60-imp2--probe mode)))
    (cond
     ((eq result 'm60-imp2-prog-absent) result)
     ((and (consp result) (eql 0 (car result))) (cdr result))
     (t nil))))

(defun m60-imp2--probe-exit (mode)
  "The exit status of the probe MODE, or the symbol
`m60-imp2-prog-absent'."
  (let ((result (m60-imp2--probe mode)))
    (if (consp result) (car result) result)))

(defun m60-imp2--probe-raw-output (mode)
  "The OUTPUT of the probe MODE for ANY exit status, or the marker
`m60-imp2-prog-absent'.  Use this only for a mode that MUST fail: the
registration mode of M60 imp-2 raises on purpose, so its output is
valuable at a non-zero exit.  Every other check goes through
`m60-imp2--probe-output', which requires exit 0."
  (let ((result (m60-imp2--probe mode)))
    (cond
     ((eq result 'm60-imp2-prog-absent) result)
     ((consp result) (cdr result))
     (t nil))))

(defun m60-imp2--probe-raw-holds (mode needle)
  "Non-nil when the OUTPUT of the probe MODE holds NEEDLE, at ANY exit
status."
  (let ((out (m60-imp2--probe-raw-output mode)))
    (cond
     ((eq out 'm60-imp2-prog-absent) out)
     ((not (stringp out)) nil)
     (t (with-temp-buffer
          (insert out)
          (goto-char (point-min))
          (and (search-forward needle nil t) t))))))

(defun m60-imp2--probe-raw-holds-none (mode needle)
  "Non-nil when the OUTPUT of the probe MODE holds NO NEEDLE, at ANY exit
status.  Use it for a mode that must fail: the imp-3 re-pin of R5 pins
the ABSENT old error of the `registration' mode."
  (let ((out (m60-imp2--probe-raw-output mode)))
    (cond
     ((eq out 'm60-imp2-prog-absent) out)
     ((not (stringp out)) nil)
     (t (with-temp-buffer
          (insert out)
          (goto-char (point-min))
          (not (search-forward needle nil t)))))))

(defun m60-imp2--probe-line (mode line)
  "Non-nil when the probe MODE printed LINE as one WHOLE line and the
child exited 0.  A substring match is NOT enough: a line pin holds the
whole line, so a changed value can not hide inside it."
  (let ((out (m60-imp2--probe-output mode)))
    (cond
     ((eq out 'm60-imp2-prog-absent) out)
     ((not (stringp out)) nil)
     (t (with-temp-buffer
          (insert "\n" out "\n")
          (goto-char (point-min))
          (and (search-forward (concat "\n" line "\n") nil t) t))))))

(defun m60-imp2--probe-holds (mode needle)
  "Non-nil when the OUTPUT of the probe MODE holds NEEDLE (a substring
pin; use it only where a run-dependent address sits in the text)."
  (let ((out (m60-imp2--probe-output mode)))
    (cond
     ((eq out 'm60-imp2-prog-absent) out)
     ((not (stringp out)) nil)
     (t (with-temp-buffer
          (insert out)
          (goto-char (point-min))
          (and (search-forward needle nil t) t))))))

(defun m60-imp2--probe-holds-none (mode needle)
  "Non-nil when the OUTPUT of the probe MODE holds NO NEEDLE."
  (let ((out (m60-imp2--probe-output mode)))
    (cond
     ((eq out 'm60-imp2-prog-absent) out)
     ((not (stringp out)) nil)
     (t (with-temp-buffer
          (insert out)
          (goto-char (point-min))
          (not (search-forward needle nil t)))))))

(defun m60-imp2--probe-ordered (mode needles)
  "Non-nil when the OUTPUT of the probe MODE holds every NEEDLE in the
GIVEN ORDER, and the child exited 0."
  (let ((out (m60-imp2--probe-output mode)))
    (cond
     ((eq out 'm60-imp2-prog-absent) out)
     ((not (stringp out)) nil)
     (t (with-temp-buffer
          (insert out)
          (goto-char (point-min))
          (let ((all t))
            (dolist (needle needles)
              (when all
                (unless (search-forward needle nil t) (setq all nil))))
            all))))))

(defun m60-imp2--all (&rest values)
  "`and' over the ALREADY-EVALUATED VALUES, with one difference: a
MARKER wins over a nil.  Both markers are truthy, so a plain `and'
returns the value of a LATER form and the check reads as a PASS
(cr.org F4).  The verdict order matches `m60-imp2--verdict': the absent
FILE marker first (a real FAIL), then the absent `guile' marker (a
skip), then nil (a FAIL), then t (a PASS).  Use this wherever a check
combines a probe result or a file-helper result with a second result."
  (cond
   ((memq 'm60-imp2-absent values) 'm60-imp2-absent)
   ((memq 'm60-imp2-prog-absent values) 'm60-imp2-prog-absent)
   ((memq nil values) nil)
   (t t)))

;;; --- report helpers -------------------------------------------------

(defun m60-imp2--verdict (ok)
  "Classify the value OK of one check: `pass', `fail', `absent' (the
TRACKED file is missing -- a real FAIL), or `skip' (the `guile' binary is
not on PATH, so the probe could not run -- never a pass)."
  (cond
   ((eq ok 'm60-imp2-prog-absent) 'skip)
   ((eq ok 'm60-imp2-absent) 'absent)
   (ok 'pass)
   (t 'fail)))

(defun m60-imp2--check (name ok)
  "Report and register one check.  The 4 outcomes come from
`m60-imp2--verdict': an absent TRACKED file prints FAIL (a real error,
not a pass), and an absent `guile' binary prints INFO and registers a
controlled ERT skip -- never a pass."
  (let ((verdict (m60-imp2--verdict ok)))
    (cond
     ((eq verdict 'skip)
      (m60-imp2--info-skip name "no guile binary on PATH"))
     ((eq verdict 'absent)
      (princ (format "FAIL m60/imp2/%s (source file absent)\n" name))
      (setq m60-imp2--registered (1+ m60-imp2--registered))
      (m60-imp2--bump-group)
      (imp-register-bool-as-ert-test (format "m60-imp2/%s" name) nil))
     (t
      (princ (format "%s m60/imp2/%s\n"
                     (if (eq verdict 'pass) "PASS" "FAIL") name))
      (setq m60-imp2--registered (1+ m60-imp2--registered))
      (m60-imp2--bump-group)
      (imp-register-bool-as-ert-test (format "m60-imp2/%s" name)
                                     (eq verdict 'pass))))))

(defun m60-imp2--info-skip (name reason)
  "Register one explicit INFO skip, counted into the current group.  A
host limit is a skip, never a pass."
  (princ (format "INFO m60/imp2/%s %s\n" name reason))
  (setq m60-imp2--registered (1+ m60-imp2--registered))
  (m60-imp2--bump-group)
  (imp-register-skip-as-ert-test (format "m60-imp2/%s" name) reason))

;;; --- R1. The surface, re-measured -----------------------------------

;; MEASURED 2026-10-20 at base 3603a6795, an ANCESTOR of HEAD (cr.org
;; F1: no src/, mod/, or prelude/ file differs between that commit and
;; the one that adds this corpus).  Unit: NEWLINES (`wc -l').
;; The tree of imp-1 carried the same values: imp-1 changed no source
;; file.  Brief.org section 7 asks for a RE-measurement, so these are
;; measured again and pinned here, not copied from the imp-1 corpus.

(setq m60-imp2--group 'r1)

(m60-imp2--check "r1/xfaces.c-lines"
                 (eql 7741 (m60-imp2--lines "src/xfaces.c")))
;; RE-PINNED at M60 imp-7: loader.scm 1,328 -> 1,363 -> 1,389 -> 1,391 -> 1,398 LINES
;; (rows 23 and 24; the old imp-7 value was 1,363).  reader.scm does
;; not move.
(m60-imp2--check "r1/loader-and-reader-lines"
                 (and (eql 1398 (m60-imp2--lines "mod/emacs/loader.scm"))
                      (eql 2021 (m60-imp2--lines "mod/emacs/reader.scm"))))
(m60-imp2--check "r1/prelude-load-lines"
                 (eql 229 (m60-imp2--lines "prelude/load.scm")))
(m60-imp2--check "r1/faces-and-spec-lines"
                 (and (eql 70 (m60-imp2--lines "mod/emacs/faces.scm"))
                      (eql 32 (m60-imp2--lines "mod/emacs-elisp/spec.scm"))))

;; Unit: LINES (`grep -c').  RE-MEASURED at M60 imp-5: 22 / 18 / 9.
(m60-imp2--check "r1/loader.scm-grep-c-counts"
                 (and (eql 22 (m60-imp2--grep-c "mod/emacs/loader.scm"
                                                "symbol-fbound?"))
                      (eql 18 (m60-imp2--grep-c "mod/emacs/loader.scm"
                                                "set-symbol-function!"))
                      (eql 9 (m60-imp2--grep-c "mod/emacs/loader.scm"
                                               "FIX-.*guilemacs"))))

;; Unit: OCCURRENCES over src/*.[ch].  MEASURED: 267.
(m60-imp2--check "r1/tree-wide-scm-ref"
                 (eql 267 (m60-imp2--count-scm-ref)))

;; Unit: FILES under test/mod (MEASURED 6: 3 suites, 1 runner, 2
;; fixtures) and ENTRIES of mod/emacs-elisp (MEASURED 9: `runtime/' is
;; ONE entry).
(m60-imp2--check "r1/test-mod-files-and-emacs-elisp-entries"
                 (and (eql 6 (m60-imp2--dir-entries "test/mod"))
                      (eql 9 (m60-imp2--dir-entries "mod/emacs-elisp"))))

;; The 2 fixtures of this imp.  An absent fixture must FAIL here, not be
;; reported as an INFO skip: the measurement of every later group would
;; be a false green.
(m60-imp2--check "r1/fixtures-present"
                 (and (m60-imp2--exists-p "test/m60/probe-imp2.scm")
                      (m60-imp2--exists-p "test/m60/test-m60-imp2.el")))

;;; --- R2. The ordered cell list --------------------------------------

;; The 11 GUARDED installs, in call order (MEASURED on the TRACKED
;; source), and the 2 UNGUARDED installs BEFORE them.
(setq m60-imp2--group 'r2)

(m60-imp2--check "r2/guarded-install-order-11"
                 (m60-imp2--all (m60-imp2--ordered-p
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
                                (m60-imp2--ordered-p
                                 "mod/emacs/loader.scm"
                                 '("(set-symbol-function! 'load elisp-load)"
                                   "(set-symbol-function! 'autoload-do-load"
                                   "(unless (symbol-fbound? 'get-load-suffixes)"))))

;; MEASURED (probe mode `cells'): after `init-loader' not one of the 11
;; guarded cells is empty.  The M55 imp-3 result HOLDS.
(m60-imp2--check "r2/empty-cells-nil"
                 (m60-imp2--probe-line "cells" "EMPTY-CELLS: ()"))

;; MEASURED (probe mode `cells'): the 2 unguarded installs are bound.
(m60-imp2--check "r2/unguarded-cells-2"
                 (m60-imp2--probe-line
                  "cells" "UNGUARDED: load=#t autoload-do-load=#t"))

;; MEASURED (probe mode `cells'): the 4 variable binds of `init-loader'.
(m60-imp2--check "r2/variable-binds-4"
                 (m60-imp2--probe-line
                  "cells"
                  (concat "VARS: load-path=#t load-suffixes=#t"
                          " load-file-rep-suffixes=#t load-read-function=#t")))

;; MEASURED (probe mode `cells'): provide / require is NO LONGER
;; asymmetric.  RE-PINNED at M60 imp-5: `init-loader' installs `require'
;; (row 20) as well as `provide' (row 18), so BOTH cells report #t.  The
;; utils.scm install count is still 0: the cell has ONE home.
(m60-imp2--check "r2/provide-require-asymmetry"
                 (m60-imp2--all (m60-imp2--probe-line
                                 "cells" "ASYM: require=#t provide=#t")
                                (eql 0 (m60-imp2--count "mod/emacs/utils.scm"
                                                        "set-symbol-function! 'require"))))

;;; --- R3. The 4 first stops ------------------------------------------

;; One REAL lisp/ file per check.  MEASURED (probe mode `cells'): each
;; file stops on a cell that the 11-name list does not hold.  So the
;; list is INCOMPLETE for a real file, and the M55 imp-3 result does not
;; cover the whole boundary.
(setq m60-imp2--group 'r3)

(m60-imp2--check "r3/subdirs-first-stop"
                 (m60-imp2--probe-line
                  "cells"
                  (concat "LOAD lisp/subdirs.el: ERROR void-function"
                          " (normal-top-level-add-to-load-path)")))
;; RE-PINNED at M60 imp-4: `provide' landed (row 18), so lisp/cdl.el
;; is NO stop of mode `cells' any more: it loads to the END.  The old
;; pin is not deleted; it follows the measured value.
(m60-imp2--check "r3/cdl-first-stop"
                 (m60-imp2--probe-line "cells" "LOAD lisp/cdl.el: done"))
;; RE-PINNED at M60 imp-6: rows 21 and 22 close the `defconst' stop.
;; The old pin was `LOAD lisp/obarray.el: ERROR void-function
;; (defconst)'.  The load now reaches the `make-obsolete-variable' call
;; of lisp/obarray.el :31 -- that is row 27, NOT PROVEN.
(m60-imp2--check "r3/obarray-first-stop"
                 (m60-imp2--probe-line
                  "cells"
                  (concat "LOAD lisp/obarray.el: ERROR void-function"
                          " (make-obsolete-variable)")))
;; RE-PINNED at M60 imp-7: row 24 closes the `eval-when-compile' stop
;; and row 23 the `defmacro' stop, so lisp/hex-util.el loads to the END.
;; The old pin was `LOAD lisp/hex-util.el: ERROR void-function
;; (eval-when-compile)'.  Row 28 (the expansion path) STAYS OPEN.
(m60-imp2--check "r3/hex-util-first-stop"
                 (m60-imp2--probe-line "cells" "LOAD lisp/hex-util.el: done"))

;; MEASURED: `features' is a C DEFVAR_LISP (src/fns.c :6372).
;; RE-PINNED at M60 imp-4: `init-loader' binds it (row 19), so the
;; variable cell is BOUND in a plain `guile' process.
(m60-imp2--check "r3/features-bound"
                 (m60-imp2--all (m60-imp2--probe-line "cells" "FEATURES-BOUND: #t")
                                (eql 6372 (m60-imp2--line-of
                                           "src/fns.c"
                                           "DEFVAR_LISP (\"features\""))))

;;; --- R4. The stub chain, the last good point, the control -----------

;; One pure stub at a time, in this ORDER (probe mode `stubs').  A pure
;; stub passes the first 3 stops; the 4th file needs the same stub set.
(setq m60-imp2--group 'r4)

;; RE-PINNED at M60 imp-6: the real `defconst' branch now matches
;; FIRST, so the pure `defconst' stub is DEAD and the obarray stop moves
;; from `void-variable (obarray-default-size)' to
;; `void-function (make-obsolete-variable)'.  The stub stays: this mode
;; records the chain.
;; RE-PINNED at M60 imp-7: the real `eval-when-compile' branch matches
;; FIRST, so that pure stub is DEAD (it STAYS in the fixture, because
;; this mode records the chain) and the chain step is `done'.  The old
;; step was `stub-eval-when-compile / hex-util: ERROR void-function
;; (defmacro)'.
(m60-imp2--check "r4/stub-chain-order"
                 (m60-imp2--probe-ordered
                  "stubs"
                  '("stub-provide / cdl: done"
                    "stub-defconst / obarray: ERROR void-function (make-obsolete-variable)"
                    "stub-eval-when-compile / hex-util: done"
                    "stub-ntl / subdirs: done")))

;; The FIRST stop that a pure stub can NOT pass was a VARIABLE, not a
;; function: the minimal evaluator `elisp-loader-eval'
;; (mod/emacs/loader.scm) had no `defvar' branch, so the variable cell
;; stayed unbound.
;;
;; RE-PINNED at M60 imp-6: rows 21 and 22 add the 2 branches, so
;; `obarray-default-size' is bound and the pure `defconst' stub is dead.
;; The first stop that a stub can not pass is now the
;; `make-obsolete-variable' FUNCTION call (row 27).  The old check was
;; named `r4/defvar-stop' and pinned `void-variable
;; (obarray-default-size)'.
;;
;; RE-PINNED at M60 imp-7: row 23 adds the `defmacro' branch, so the
;; ABSENCE pin flips to PRESENCE.
(m60-imp2--check "r4/defvar-and-defconst-branches"
                 (m60-imp2--all (m60-imp2--probe-line
                                 "stubs"
                                 (concat "stub-defconst / obarray: ERROR void-function"
                                         " (make-obsolete-variable)"))
                                (m60-imp2--holds-all
                                 "mod/emacs/loader.scm"
                                 '("((eq? head 'defun)"
                                   "((eq? head 'defvar)"
                                   "((eq? head 'defconst)"))
                                (m60-imp2--holds-all
                                 "mod/emacs/loader.scm"
                                 '("((eq? head 'defmacro)"))))

;; The LAST GOOD POINT: with the faithful `provide' cell and the
;; `features' variable bound, lisp/cdl.el loads to the END, the elisp
;; `featurep' of `cdl' is #t, and `features' is (cdl).  (`featurep'
;; itself is a C DEFUN, so its own cell is empty here; the fixture uses
;; the elisp definition, a `memq' over `features'.)
(m60-imp2--check "r4/last-good-point"
                 (m60-imp2--all (m60-imp2--probe-line "stubs" "faithful-provide / cdl: done")
                                (m60-imp2--probe-line "stubs" "featurep-fbound: #f")
                                (m60-imp2--probe-line "stubs" "featurep cdl: #t")
                                (m60-imp2--probe-line "stubs" "features: (cdl)")))

;; The NEGATIVE CONTROL, in its OWN process (probe mode `negative'):
;; the faithful `provide' cell WITHOUT the `features' bind.  MEASURED:
;; the load raises a TYPE error on the unbound sentinel, so the bind is
;; load-bearing and the error is NOT a void-function stop.  The address
;; inside the sentinel changes between runs, so this check pins the 3
;; stable words and not the whole line.
(m60-imp2--check "r4/negative-control"
                 (m60-imp2--all (m60-imp2--probe-line "negative" "features-bound: #f")
                                (m60-imp2--probe-line "negative" "provide-fbound: #t")
                                (m60-imp2--probe-holds "negative" "LOAD cdl: ERROR wrong-type-arg")
                                (m60-imp2--probe-holds "negative" "\"memq\"")
                                (m60-imp2--probe-holds "negative" "uninterned-symbol unbound")
                                (m60-imp2--probe-holds-none "negative" "void-function")))

;;; --- R5. The registration -------------------------------------------

;; R5 re-pinned at M60 imp-3 (brief.org F2).  The named blocker of imp-2
;; ("no such language emacs-elisp") is CLOSED: the split registers the
;; language in (language emacs-elisp spec), the name Guile resolves.
;; MEASURED now: the fixture still exits 1, but it stops at the NEXT
;; blocker inside `compile-and-load' -- the Scheme elisp compiler
;; resolves `mapcar' at compile time and only the C runtime binds it.
;; So no check here claims a module load; the language object itself is
;; pinned by test-m60-imp3.el (mode `language').
(setq m60-imp2--group 'r5)

;; cr.org F4: `m60-imp2--probe-exit' returns the marker
;; `m60-imp2-prog-absent' when no `guile' binary is on PATH, and the
;; marker is returned AS IS, so `m60-imp2--check' reports a controlled
;; INFO skip and never a PASS.
(m60-imp2--check "r5/registration-exit-status"
                 (let ((exit (m60-imp2--probe-exit "registration")))
                   (if (eq exit 'm60-imp2-prog-absent)
                       exit
                     (and (integerp exit) (/= 0 exit)))))

;; RE-PINNED at imp-3 (brief.org F2): "no such language emacs-elisp" is
;; GONE from the output (the blocker is closed) and the stop is the next
;; one.  The check keeps its strength: it pins the ABSENT old error, the
;; PRESENT new error, and the site that reports it.
(m60-imp2--check "r5/registration-error-text"
                 (m60-imp2--all
                  (m60-imp2--probe-raw-holds-none "registration"
                                                  "no such language emacs-elisp")
                  (m60-imp2--probe-raw-holds "registration"
                                             "Unbound variable: mapcar")
                  (m60-imp2--probe-raw-holds "registration"
                                             "ERROR: In procedure %resolve-variable")))

;; RE-PINNED at imp-3 (brief.org F2): (emacs-elisp spec) now IMPORTS the
;; language module at :8 and calls `compile-and-load' at :31.  The
;; `define-language' form is no longer in this file; it is at :15 of
;; mod/language/emacs-elisp/spec.scm.
(m60-imp2--check "r5/spec.scm-sites"
                 (and (eql 8 (m60-imp2--line-of
                              "mod/emacs-elisp/spec.scm"
                              "#:use-module (language emacs-elisp spec)"))
                      (eql 31 (m60-imp2--line-of
                               "mod/emacs-elisp/spec.scm"
                               "(compile-and-load (%search-load-path"))
                      (eql 0 (m60-imp2--grep-c
                              "mod/emacs-elisp/spec.scm"
                              "define-language"))
                      (eql 15 (m60-imp2--line-of
                               "mod/language/emacs-elisp/spec.scm"
                               "(define-language emacs-elisp"))))

;; RE-PINNED at imp-3 (brief.org F2).  This check pinned the ABSENT
;; state ("the patch is live").  The patch is DELETED, so the check pins
;; the PRESENT new thing: ZERO patch lines, and `<prelude>/../mod' still
;; on %load-path -- that path is what lets a FULL Emacs find the new
;; module without any patch.
(m60-imp2--check "r5/prelude-patch-live"
                 (m60-imp2--all
                  (eql 0 (m60-imp2--grep-c "prelude/load.scm" "patched-lookup"))
                  (eql 0 (m60-imp2--grep-c "prelude/load.scm" "module-set!"))
                  (eql 0 (m60-imp2--grep-c "prelude/load.scm" "bad language"))
                  (m60-imp2--live-p "prelude/load.scm" "/../mod")))

;; The C core resolves the language module itself, so the language
;; exists in a full Emacs and NOT in a plain `guile' process.
(m60-imp2--check "r5/c-resolve-emacs-elisp-spec"
                 (eql 1639 (m60-imp2--line-of
                            "src/emacs.c"
                            "scm_c_resolve_module (\"emacs-elisp spec\")")))

;;; --- R6. The registration of THIS corpus ----------------------------

(setq m60-imp2--group 'r6)

(m60-imp2--check "r6/run-tests-m60-imp2"
                 (m60-imp2--live-p "tool/run-tests.scm"
                                   "test/m60/test-m60-imp2.el"))
(m60-imp2--check "r6/run-tests-imp2-after-imp1"
                 (m60-imp2--ordered-p
                  "tool/run-tests.scm"
                  '("test/m60/test-m60-imp1.el" "test/m60/test-m60-imp2.el")))
(m60-imp2--check "r6/run-tests-m60-after-m59"
                 (m60-imp2--all (m60-imp2--live-p "tool/run-tests.scm" "(group (m59)")
                                (m60-imp2--ordered-p "tool/run-tests.scm"
                                                     '("(group (m59)" "(group (m60)"))))
;; A group KEY is an extra symbol in the key list: `(group (m60 prelude)
;; ...)' would run through run-tests-bare-emacs.  So the group key list
;; must be exactly `(m60)' -- that is what the corpus needs, because the
;; group must run through run-tests-loadup-emacs, INSIDE the built
;; src/emacs.  Do NOT scan the group BODY for the word "prelude": the
;; comment prose of the group names prelude/load.scm, and a substring
;; scan would report a false FAIL (MEASURED).
(m60-imp2--check "r6/run-tests-m60-no-prelude"
                 (m60-imp2--all (m60-imp2--live-p "tool/run-tests.scm" "(group (m60)")
                                (m60-imp2--holds-none "tool/run-tests.scm"
                                                      '("(group (m60 "))))

;;; --- R7. The guards -------------------------------------------------

;; S1 of the imp-1 corpus warns that an --filter which matches no group
;; reports exit 0 with 0 tests.  The per-group floors below stop a silent
;; loss of a group: R1 8, R2 5, R3 5, R4 4, R5 5, R6 4.

(setq m60-imp2--group 'r7)

(m60-imp2--check "r7/min-r1-checks-8" (>= (m60-imp2--group-count 'r1) 8))
(m60-imp2--check "r7/min-r2-checks-5" (>= (m60-imp2--group-count 'r2) 5))
(m60-imp2--check "r7/min-r3-checks-5" (>= (m60-imp2--group-count 'r3) 5))
(m60-imp2--check "r7/min-r4-checks-4" (>= (m60-imp2--group-count 'r4) 4))
(m60-imp2--check "r7/min-r5-checks-5" (>= (m60-imp2--group-count 'r5) 5))
(m60-imp2--check "r7/min-r6-checks-4" (>= (m60-imp2--group-count 'r6) 4))

;; cr.org F4: the skip path must be LIVE.  This self-check exercises the
;; 2 pure helpers that route a missing `guile' binary: `m60-imp2--verdict'
;; classifies a check value, and `m60-imp2--all' keeps a marker through a
;; composite check.  An edit that folds the marker into a truthy value
;; reads as a false PASS, and it FAILs HERE instead.  The 2nd `all' call
;; holds a real probe result, so the check also pins that the marker wins
;; over a probe result.
(m60-imp2--check "r7/prog-absent-routes-to-skip"
                 (and (eq 'skip (m60-imp2--verdict 'm60-imp2-prog-absent))
                      (eq 'skip (m60-imp2--verdict
                                 (m60-imp2--all
                                  'm60-imp2-prog-absent
                                  (m60-imp2--probe-line "cells"
                                                        "EMPTY-CELLS: ()"))))
                      (eq 'absent (m60-imp2--verdict 'm60-imp2-absent))
                      (eq 'absent (m60-imp2--verdict
                                   (m60-imp2--all 'm60-imp2-absent t)))
                      (eq 'pass (m60-imp2--verdict t))
                      (eq 'fail (m60-imp2--verdict nil))
                      (eq 'fail (m60-imp2--verdict (m60-imp2--all t nil)))))

;;; --- The group-total check ------------------------------------------

;; MEASURED count of m60-imp2 tests: 38 registered checks (R1 8, R2 5,
;; R3 5, R4 4, R5 5, R6 4, R7 7) plus this deftest itself.

(defvar m60-imp2--min-gate-total 39
  "The exact number of m60-imp2 ERT tests: 38 registered checks (R1 8,
R2 5, R3 5, R4 4, R5 5, R6 4, R7 7) plus the group-total deftest
itself.")

(ert-deftest m60-imp2/gate-m60-total ()
  "The m60-imp2 corpus registers at least its docs-independent floor."
  (should (>= (length (ert-select-tests "^m60-imp2" t))
              m60-imp2--min-gate-total)))

(princ (format "=== m60 imp-2 suite done (%d checks; r1 %d, r2 %d, r3 %d, r4 %d, r5 %d, r6 %d, r7 %d) ===\n"
               m60-imp2--registered
               (m60-imp2--group-count 'r1)
               (m60-imp2--group-count 'r2)
               (m60-imp2--group-count 'r3)
               (m60-imp2--group-count 'r4)
               (m60-imp2--group-count 'r5)
               (m60-imp2--group-count 'r6)
               (m60-imp2--group-count 'r7)))
