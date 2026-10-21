;;; test-m60-imp5.el --- M60 imp-5 REQUIRE CELL corpus.
;;;
;;; M60 imp-5 lands row 20 of the row map of docs/m60-plan.org section 6:
;;; `require', the C DEFUN of src/fns.c :3496.  The cell gets ONE home,
;;; `init-loader' (mod/emacs/loader.scm), and the stale `elisp-require'
;;; name is DELETED from the #:export list of (emacs utils) in the same
;;; commit: `(emacs loader)' uses `(emacs utils)' (loader.scm :18), so a
;;; definition in utils.scm that calls the loader is a module cycle.
;;;
;;; Reach: a plain `guile -L mod' process never loads the prelude, it
;;; calls `init-loader' only.  A full Emacs calls `init-loader' before the
;;; prelude.  So the cell is installed in the guarded block of
;;; `init-loader', only when the function cell is EMPTY, and a full Emacs
;;; keeps the C DEFUN.
;;;
;;; MEASURED PRECONDITION (this is the new fact of imp-5): the elisp
;;; `load' protocol that `Frequire' calls is `elisp-load'
;;; (loader.scm :725), and it applies 2 function cells that `init-loader'
;;; did not install -- `string-suffix-p' and `file-name-directory'
;;; (loader.scm :257, :259).  Both are EMPTY in a plain `guile' process,
;;; so `elisp-load' raised `wrong-type-arg "Wrong type to apply: #nil"'
;;; BEFORE the load started (recorded by the probe run of 2026-10-21).
;;; imp-5 therefore installs those 2 cells too, guarded, and reuses the
;;; pure-Scheme `string-suffix-p' of (emacs strings) :336.
;;;
;;; The (m60) group has NO prelude key, so this corpus runs INSIDE the
;;; built src/emacs.  Every plain-guile value is measured by
;;; test/m60/probe-imp3.scm as a `guile -L mod' child process with
;;; GUILE_AUTO_COMPILE=0 -- one MODE per child, so a stub of one mode can
;;; not hide the next result.  Mode `require' is NEW here: it changes
;;; `features' and the elisp `load-path' variable, so it needs its own
;;; process.
;;;
;;; It pins these groups:
;;;
;;;   S1 -- the cell source: 1 definition in loader.scm, 0 names in
;;;         utils.scm and in the prelude, the FIX marker, the
;;;         `elisp-load' call, and the `elisp-loader-truthy?' test (R1).
;;;   S2 -- the install: the `symbol-fbound?' guard, 1 site, the ORDER
;;;         after the `provide' install and before
;;;         `(set! %load-extensions ...)', and the 2 `load' protocol
;;;         cells.
;;;   S3 -- the observable through a live `guile' child, mode `require':
;;;         the symbol, the `features' list, the silent second `require',
;;;         the "Required feature" error, the missing-file error, and the
;;;         NOERROR nil.
;;;   S4 -- no regression: modes `cells', `provide', `stubs', `negative',
;;;         `noboot', `registration' and `language' keep their values.
;;;   S5 -- the re-measured surface: the 3 LINE counts and the 3
;;;         loader.scm `grep -c' counts.
;;;   S6 -- the registration: the imp-5 line AFTER the imp-4 line,
;;;         imp-1 ... imp-4 kept, (m60) with no prelude key.
;;;   S7 -- the guards: the per-group min counts, the marker-routing
;;;         self-check of the skip path, and the group-total deftest.
;;;
;;; This corpus reads TRACKED files only.  It does NOT read docs/.
;;; A read error is a real error, never a silent pass.  An absent TRACKED
;;; file is a real FAIL.  A missing `guile' binary is an explicit INFO
;;; skip, never a pass: `m60-imp5--check' routes the marker
;;; `m60-imp5-prog-absent' to `m60-imp5--info-skip', and `m60-imp5--all'
;;; carries that marker through a composite check.
;;;
;;; Every value below was MEASURED on this host on 2026-10-21 by running
;;; the fixture and the commands named in the comment of each check.
;;; MEASURED total: 35 registered checks (S1 5, S2 4, S3 8, S4 6, S5 2,
;;; S6 3, S7 7) plus the group-total deftest = 36 ERT tests.

(princ "=== m60 imp-5 require-cell suite ===\n")

(require 'imp-ert-report)

(defvar m60-imp5--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))
(defvar m60-imp5--registered 0
  "Total number of checks this corpus has registered.")
(defvar m60-imp5--group nil
  "The group that `m60-imp5--check' counts into: `s1' .. `s7', or nil.")
(defvar m60-imp5--counts nil
  "Alist of (GROUP . COUNT) for the registered checks.")
(defvar m60-imp5--probe-cache nil
  "Alist of (MODE . RESULT) of the plain-guile probe runs of this corpus.
A mode is measured once per corpus run, so a group starts one child
process, not one per check.")

(defun m60-imp5--group-count (group)
  "Number of checks registered so far in GROUP."
  (or (cdr (assq group m60-imp5--counts)) 0))

(defun m60-imp5--bump-group ()
  "Count one check into `m60-imp5--group'."
  (when m60-imp5--group
    (let ((cell (assq m60-imp5--group m60-imp5--counts)))
      (if cell
          (setcdr cell (1+ (cdr cell)))
        (push (cons m60-imp5--group 1) m60-imp5--counts)))))

;;; --- tracked-file helpers (the imp-1 / imp-4 idioms) ----------------

(defun m60-imp5--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
the symbol `m60-imp5-absent' when REL does not exist.  `case-fold-search'
is bound to nil: the elisp default folds case and inflates a count."
  (let ((path (expand-file-name rel m60-imp5--root)))
    (if (not (file-exists-p path))
        'm60-imp5-absent
      (with-temp-buffer
        (insert-file-contents path)
        (let ((case-fold-search nil))
          (funcall fn))))))

(defun m60-imp5--holds-all (rel needles)
  "Non-nil when the TRACKED file REL holds every NEEDLE.  An absent file
fails the check."
  (m60-imp5--with rel
    (lambda ()
      (let ((all t))
        (dolist (needle needles)
          (goto-char (point-min))
          (unless (search-forward needle nil t) (setq all nil)))
        all))))

(defun m60-imp5--holds-none (rel needles)
  "Non-nil when the TRACKED file REL holds NO needle of NEEDLES."
  (m60-imp5--with rel
    (lambda ()
      (let ((none t))
        (dolist (needle needles)
          (goto-char (point-min))
          (when (search-forward needle nil t) (setq none nil)))
        none))))

(defun m60-imp5--ordered-p (rel needles)
  "Non-nil when the TRACKED file REL holds every NEEDLE in the GIVEN
ORDER: each search starts after the previous match."
  (m60-imp5--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((all t))
        (dolist (needle needles)
          (when all
            (unless (search-forward needle nil t) (setq all nil))))
        all))))

(defun m60-imp5--lines (rel)
  "Count the NEWLINES of REL, the unit of `wc -l'."
  (m60-imp5--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (search-forward "\n" nil t) (setq n (1+ n)))
        n))))

(defun m60-imp5--grep-c (rel regexp)
  "Count the LINES of REL that match REGEXP, the unit of `grep -c'."
  (m60-imp5--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (not (eobp))
          (when (re-search-forward regexp (line-end-position) t)
            (setq n (1+ n)))
          (forward-line 1))
        n))))

(defun m60-imp5--literal-lines (rel needle)
  "Count the LINES of REL that hold NEEDLE as a LITERAL substring.  Use
this helper and not `m60-imp5--grep-c' where NEEDLE holds a regexp
metacharacter: `?' is the `optional' operator of the search syntax, so
the guard pattern never matches the source line that it names (MEASURED
2026-10-21)."
  (m60-imp5--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (not (eobp))
          (when (search-forward needle (line-end-position) t)
            (setq n (1+ n)))
          (forward-line 1))
        n))))

;;; --- the plain-guile probe runner -----------------------------------

(defun m60-imp5--probe-1 (mode)
  "Run test/m60/probe-imp3.scm in MODE as a `guile -L mod' child
process, with GUILE_AUTO_COMPILE=0 and GUILEMACS_ROOT set, and with
`default-directory' at the repo root.  Return (EXIT . OUTPUT), where
OUTPUT holds stdout AND stderr, or the symbol `m60-imp5-prog-absent'
when the `guile' binary is not on PATH."
  (if (not (executable-find "guile"))
      'm60-imp5-prog-absent
    (let ((buf (get-buffer-create " *m60-imp5-probe*"))
          (default-directory m60-imp5--root)
          (process-environment
           (append (list (concat "GUILEMACS_ROOT=" m60-imp5--root)
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

(defun m60-imp5--probe (mode)
  "The cached result of `m60-imp5--probe-1' for MODE."
  (let ((cell (assoc mode m60-imp5--probe-cache)))
    (if cell
        (cdr cell)
      (let ((result (m60-imp5--probe-1 mode)))
        (push (cons mode result) m60-imp5--probe-cache)
        result))))

(defun m60-imp5--probe-raw (mode)
  "The OUTPUT of the probe MODE whatever the exit status is, or the
marker `m60-imp5-prog-absent'.  Mode `registration' raises on purpose, so
its output is only readable this way."
  (let ((result (m60-imp5--probe mode)))
    (cond
     ((eq result 'm60-imp5-prog-absent) result)
     ((consp result) (cdr result))
     (t nil))))

(defun m60-imp5--probe-output (mode)
  "The OUTPUT of the probe MODE when the child exited 0, else nil.  A
crash mid-mode printed a partial output, so the exit status is part of
every output check.  When the `guile' binary is absent, the marker
`m60-imp5-prog-absent' is returned instead of nil, so the caller can
SKIP and not pass or fail."
  (let ((result (m60-imp5--probe mode)))
    (cond
     ((eq result 'm60-imp5-prog-absent) result)
     ((and (consp result) (eql 0 (car result))) (cdr result))
     (t nil))))

(defun m60-imp5--probe-line (mode line)
  "Non-nil when the probe MODE printed LINE as one WHOLE line and the
child exited 0.  A substring match is NOT enough: a line pin holds the
whole line, so a changed value can not hide inside it."
  (let ((out (m60-imp5--probe-output mode)))
    (cond
     ((eq out 'm60-imp5-prog-absent) out)
     ((not (stringp out)) nil)
     (t (with-temp-buffer
          (insert "\n" out "\n")
          (goto-char (point-min))
          (and (search-forward (concat "\n" line "\n") nil t) t))))))

(defun m60-imp5--probe-line-count (mode line)
  "Number of WHOLE lines LINE in the OUTPUT of the probe MODE, or nil
when the mode did not exit 0.  Unit: LINES, not occurrences, so the
`loading NAME' debug line of `elisp-load' is countable."
  (let ((out (m60-imp5--probe-output mode)))
    (cond
     ((eq out 'm60-imp5-prog-absent) out)
     ((not (stringp out)) nil)
     (t (with-temp-buffer
          (insert "\n" out "\n")
          (goto-char (point-min))
          (let ((n 0))
            (while (search-forward (concat "\n" line "\n") nil t)
              (setq n (1+ n)))
            n))))))

(defun m60-imp5--probe-holds (mode needle)
  "Non-nil when the OUTPUT of the probe MODE holds NEEDLE (a substring
pin; use it only where an address sits in the text)."
  (let ((out (m60-imp5--probe-output mode)))
    (cond
     ((eq out 'm60-imp5-prog-absent) out)
     ((not (stringp out)) nil)
     (t (with-temp-buffer
          (insert out)
          (goto-char (point-min))
          (and (search-forward needle nil t) t))))))

(defun m60-imp5--probe-holds-none (mode needle)
  "Non-nil when the OUTPUT of the probe MODE holds NO NEEDLE."
  (let ((out (m60-imp5--probe-output mode)))
    (cond
     ((eq out 'm60-imp5-prog-absent) out)
     ((not (stringp out)) nil)
     (t (with-temp-buffer
          (insert out)
          (goto-char (point-min))
          (not (search-forward needle nil t)))))))

(defun m60-imp5--probe-raw-holds (mode needle)
  "Non-nil when the RAW output of the probe MODE holds NEEDLE, whatever
the exit status is."
  (let ((out (m60-imp5--probe-raw mode)))
    (cond
     ((eq out 'm60-imp5-prog-absent) out)
     ((not (stringp out)) nil)
     (t (with-temp-buffer
          (insert out)
          (goto-char (point-min))
          (and (search-forward needle nil t) t))))))

(defun m60-imp5--all (&rest values)
  "`and' over the ALREADY-EVALUATED VALUES, with one difference: a
MARKER wins over a nil.  Both markers are truthy, so a plain `and'
returns the value of a LATER form and the check reads as a PASS.  The
verdict order matches `m60-imp5--verdict': the absent FILE marker first
(a real FAIL), then the absent `guile' marker (a skip), then nil (a
FAIL), then t (a PASS)."
  (cond
   ((memq 'm60-imp5-absent values) 'm60-imp5-absent)
   ((memq 'm60-imp5-prog-absent values) 'm60-imp5-prog-absent)
   ((memq nil values) nil)
   (t t)))

;;; --- report helpers -------------------------------------------------

(defun m60-imp5--verdict (ok)
  "Classify the value OK of one check: `pass', `fail', `absent' (the
TRACKED file is missing -- a real FAIL), or `skip' (the `guile' binary is
not on PATH, so the probe could not run -- never a pass)."
  (cond
   ((eq ok 'm60-imp5-prog-absent) 'skip)
   ((eq ok 'm60-imp5-absent) 'absent)
   (ok 'pass)
   (t 'fail)))

(defun m60-imp5--check (name ok)
  "Report and register one check.  The 4 outcomes come from
`m60-imp5--verdict': an absent TRACKED file prints FAIL (a real error,
not a pass), and an absent `guile' binary prints INFO and registers a
controlled ERT skip -- never a pass."
  (let ((verdict (m60-imp5--verdict ok)))
    (cond
     ((eq verdict 'skip)
      (m60-imp5--info-skip name "no guile binary on PATH"))
     ((eq verdict 'absent)
      (princ (format "FAIL m60/imp5/%s (source file absent)\n" name))
      (setq m60-imp5--registered (1+ m60-imp5--registered))
      (m60-imp5--bump-group)
      (imp-register-bool-as-ert-test (format "m60-imp5/%s" name) nil))
     (t
      (princ (format "%s m60/imp5/%s\n"
                     (if (eq verdict 'pass) "PASS" "FAIL") name))
      (setq m60-imp5--registered (1+ m60-imp5--registered))
      (m60-imp5--bump-group)
      (imp-register-bool-as-ert-test (format "m60-imp5/%s" name)
                                     (eq verdict 'pass))))))

(defun m60-imp5--info-skip (name reason)
  "Register one explicit INFO skip, counted into the current group.  A
host limit is a skip, never a pass."
  (princ (format "INFO m60/imp5/%s %s\n" name reason))
  (setq m60-imp5--registered (1+ m60-imp5--registered))
  (m60-imp5--bump-group)
  (imp-register-skip-as-ert-test (format "m60-imp5/%s" name) reason))

;;; --- S1. The cell source --------------------------------------------

;; ONE home.  MEASURED 2026-10-21: 1 definition in loader.scm
;; (`define* (elisp-require'), 0 NAMES in utils.scm (the stale export is
;; deleted), 0 in prelude/load.scm.  Unit: LINES (`grep -c').
(setq m60-imp5--group 's1)

(m60-imp5--check "s1/one-definition-in-loader"
                 (eql 1 (m60-imp5--literal-lines "mod/emacs/loader.scm"
                                                 "(define* (elisp-require")))

(m60-imp5--check "s1/zero-names-in-utils-and-prelude"
                 (m60-imp5--all
                  (eql 0 (m60-imp5--grep-c "mod/emacs/utils.scm"
                                           "elisp-require"))
                  (eql 0 (m60-imp5--grep-c "prelude/load.scm"
                                           "elisp-require"))))

;; The cell is a standalone-load cell, so it carries a FIX marker in the
;; =FIX-YYYYMMDD-guilemacs= form of the project rules.
(m60-imp5--check "s1/fix-marker-20261021"
                 (m60-imp5--holds-all "mod/emacs/loader.scm"
                                      '("FIX-20261021-guilemacs")))

;; The cell calls the ELISP `load' protocol, `elisp-load' (:725), and not
;; the lower entry `load-elisp' (:831).
(m60-imp5--check "s1/cell-calls-elisp-load"
                 (m60-imp5--all
                  (m60-imp5--holds-all
                   "mod/emacs/loader.scm"
                   '("(elisp-load name noerror #t #nil from-feature?)"))
                  (m60-imp5--holds-none "mod/emacs/loader.scm"
                                        '("(load-elisp name"))))

;; RISK R1: a NOERROR failure of `elisp-load' returns Scheme #f (:785),
;; and `(eq? #f #nil)' is false, so the cell must test the load value
;; with `elisp-loader-truthy?' and NEVER with a plain nil test.
(m60-imp5--check "s1/truth-test-not-plain-nil"
                 (m60-imp5--all
                  (m60-imp5--holds-all
                   "mod/emacs/loader.scm"
                   '("(if (not (elisp-loader-truthy? result))"))
                  (m60-imp5--holds-none "mod/emacs/loader.scm"
                                        '("(eq? result #nil)"))))

;;; --- S2. The install ------------------------------------------------

(setq m60-imp5--group 's2)

(m60-imp5--check "s2/guard-and-one-install"
                 (m60-imp5--all
                  (eql 1 (m60-imp5--literal-lines
                          "mod/emacs/loader.scm"
                          "(unless (symbol-fbound? 'require)"))
                  (eql 1 (m60-imp5--literal-lines
                          "mod/emacs/loader.scm"
                          "(set-symbol-function! 'require elisp-require)"))))

;; MEASURED order in `init-loader': AFTER the `provide' install (row 18)
;; and BEFORE `(set! %load-extensions ...)'.
(m60-imp5--check "s2/ordered-after-provide-before-load-extensions"
                 (m60-imp5--ordered-p
                  "mod/emacs/loader.scm"
                  '("(set-symbol-function! 'provide elisp-provide)"
                    "(unless (symbol-fbound? 'require)"
                    "(set-symbol-function! 'require elisp-require)"
                    "(set! %load-extensions (cons \".el\" %load-extensions))")))

;; The 2 cells of the elisp `load' protocol that the cell applies.  Both
;; are GUARDED, and each has EXACTLY ONE install site.
(m60-imp5--check "s2/load-protocol-cells-installed"
                 (m60-imp5--all
                  (eql 1 (m60-imp5--grep-c
                          "mod/emacs/loader.scm"
                          "(set-symbol-function! 'string-suffix-p"))
                  (eql 1 (m60-imp5--grep-c
                          "mod/emacs/loader.scm"
                          "(set-symbol-function! 'file-name-directory"))))

(m60-imp5--check "s2/ordered-require-then-the-2-cells"
                 (m60-imp5--ordered-p
                  "mod/emacs/loader.scm"
                  '("(set-symbol-function! 'require elisp-require)"
                    "(unless (symbol-fbound? 'string-suffix-p)"
                    "(set-symbol-function! 'string-suffix-p elisp-string-suffix-p)"
                    "(unless (symbol-fbound? 'file-name-directory)"
                    "(set-symbol-function! 'file-name-directory")))

;;; --- S3. The acceptance observable (mode `require') -----------------

;; A plain `guile -L mod' process.  MEASURED 2026-10-21: the cell loads
;; lisp/cdl.el, returns the symbol, and leaves `features' = (cdl).
(setq m60-imp5--group 's3)

(m60-imp5--check "s3/require-fbound"
                 (m60-imp5--probe-line "require" "REQUIRE-FBOUND: #t"))

(m60-imp5--check "s3/features-at-start-empty"
                 (m60-imp5--probe-line "require" "features-at-start: ()"))

(m60-imp5--check "s3/require-cdl-returns-symbol"
                 (m60-imp5--probe-line "require" "REQUIRE cdl: cdl"))

(m60-imp5--check "s3/features-is-cdl"
                 (m60-imp5--probe-line "require" "features: (cdl)"))

;; The mode empties the ELISP `load-path' variable before this line, so a
;; real load would fail on the missing file: no error proves that the
;; SECOND require does not load again.  The `loading cdl' debug line of
;; `elisp-load' (:730) appears ONCE in the whole mode.
(m60-imp5--check "s3/require-again-no-second-load"
                 (m60-imp5--all
                  (m60-imp5--probe-line "require" "REQUIRE-AGAIN: cdl")
                  (eql 1 (m60-imp5--probe-line-count "require" "loading cdl"))))

;; Step 6 of the cell: a file that loads to the END and provides ANOTHER
;; feature still raises the C message (src/fns.c :3604).
(m60-imp5--check "s3/require-not-provided-message"
                 (m60-imp5--probe-line
                  "require"
                  (concat "REQUIRE-NOT-PROVIDED: ERROR misc-error"
                          " Required feature `no-such-feature' was not provided")))

(m60-imp5--check "s3/require-missing-error"
                 (m60-imp5--probe-line
                  "require"
                  "REQUIRE-MISSING: ERROR misc-error Cannot open load file"))

;; Step 5: NOERROR returns the ELISP nil, never #t.  `~s' of the nil value
;; prints `#nil' in this Guile.
(m60-imp5--check "s3/require-noerror-nil"
                 (m60-imp5--probe-line "require" "REQUIRE-NOERROR: #nil"))

;;; --- S4. No regression on the 7 older modes -------------------------

;; Mode `cells' installs neither the require cell nor the 2 `load' cells
;; itself, so these words come from `init-loader' only.  RE-PINNED: the
;; `require' half of the old asymmetry is now `#t'.
(setq m60-imp5--group 's4)

(m60-imp5--check "s4/cells-unchanged"
                 (m60-imp5--all
                  (m60-imp5--probe-line "cells" "EMPTY-CELLS: ()")
                  (m60-imp5--probe-line
                   "cells" "UNGUARDED: load=#t autoload-do-load=#t")
                  (m60-imp5--probe-line
                   "cells"
                   (concat "VARS: load-path=#t load-suffixes=#t"
                           " load-file-rep-suffixes=#t load-read-function=#t"))
                  (m60-imp5--probe-line "cells" "LOAD lisp/cdl.el: done")
                  (m60-imp5--probe-line "cells" "features: (cdl)")
                  (m60-imp5--probe-line "cells" "FEATURES-BOUND: #t")
                  (m60-imp5--probe-line "cells" "ASYM: require=#t provide=#t")))

;; RE-PINNED at imp-5: mode `provide' reported `require-fbound: #f' while
;; row 20 was open.
(m60-imp5--check "s4/provide-require-fbound"
                 (m60-imp5--all
                  (m60-imp5--probe-line "provide" "require-fbound: #t")
                  (m60-imp5--probe-line "provide" "features: (cdl)")))

;; The ordered blocker list of the minimal evaluator moves at ONE
;; point: the pure stub passes `provide' and
;; `normal-top-level-add-to-load-path', and the load stops on
;; `void-function' only.  RE-PINNED at M60 imp-6: the real `defconst'
;; branch matches FIRST, so the stub is dead and the obarray stop is the
;; `make-obsolete-variable' call (row 27); the old pin was
;; `void-variable (obarray-default-size)'.
;; RE-PINNED at M60 imp-7: the real `eval-when-compile' branch matches
;; FIRST, so that pure stub is DEAD and hex-util.el loads to the END.  The
;; stub STAYS in the fixture: the mode records the chain.
(m60-imp5--check "s4/stubs-blockers"
                 (m60-imp5--all
                  (m60-imp5--probe-line "stubs" "stub-provide / cdl: done")
                  (m60-imp5--probe-line
                   "stubs"
                   (concat "stub-defconst / obarray: ERROR void-function"
                           " (make-obsolete-variable)"))
                  (m60-imp5--probe-line
                   "stubs" "stub-eval-when-compile / hex-util: done")
                  (m60-imp5--probe-line "stubs" "stub-ntl / subdirs: done")))

;; The imp-4 negative control still names the unbound sentinel.  The
;; address changes per run, so the pin holds WORDS, not a LINE.
(m60-imp5--check "s4/negative-control"
                 (m60-imp5--all
                  (m60-imp5--probe-line "negative" "features-bound: #f")
                  (m60-imp5--probe-line "negative" "provide-fbound: #t")
                  (m60-imp5--probe-holds "negative" "LOAD cdl: ERROR wrong-type-arg")
                  (m60-imp5--probe-holds "negative" "\"memq\"")
                  (m60-imp5--probe-holds "negative" "uninterned-symbol unbound")
                  (m60-imp5--probe-holds-none "negative" "void-function")))

(m60-imp5--check "s4/noboot-unchanged"
                 (m60-imp5--all
                  (m60-imp5--probe-line "noboot" "features-bound: #f")
                  (m60-imp5--probe-holds "noboot" "Wrong type to apply")))

;; The registration row keeps its NEXT blocker (row 26), and the language
;; object still resolves.  Mode `registration' raises on purpose, so its
;; output is read raw.
(m60-imp5--check "s4/registration-and-language"
                 (m60-imp5--all
                  (m60-imp5--probe-raw-holds "registration"
                                             "Unbound variable: mapcar")
                  (m60-imp5--probe-line "language" "LANGUAGE?: #t")
                  (m60-imp5--probe-line "language"
                                        "LANGUAGE-TITLE: \"Modern Emacs Lisp\"")
                  (m60-imp5--probe-line "language" "LANGUAGE-NAME: emacs-elisp")))

;;; --- S5. The re-measured surface ------------------------------------

;; Unit: NEWLINES (`wc -l'), MEASURED 2026-10-21 after the change:
;; loader.scm 1214 + 94, utils.scm 606 (an export NAME was removed, not a
;; line), prelude/load.scm 229.
;; RE-MEASURED at M60 imp-6: loader.scm 1308 -> 1328 (+20 lines: the 2
;; evaluator branches of rows 21 and 22).  The other 2 counts stand.
(setq m60-imp5--group 's5)

;; RE-PINNED at M60 imp-7: 1,328 -> 1,363 -> 1,389 -> 1,391 -> 1,398 LINES (rows 23 and 24).
(m60-imp5--check "s5/line-counts"
                 (m60-imp5--all
                  (eql 1398 (m60-imp5--lines "mod/emacs/loader.scm"))
                  (eql 606 (m60-imp5--lines "mod/emacs/utils.scm"))
                  (eql 229 (m60-imp5--lines "prelude/load.scm"))))

;; Unit: LINES (`grep -c'), MEASURED 2026-10-21: 19/15/8 before the
;; change, 22/18/9 after it (+3 `symbol-fbound?' guards, +3
;; `set-symbol-function!' installs, +1 FIX marker).
(m60-imp5--check "s5/grep-c-counts"
                 (and (eql 22 (m60-imp5--grep-c "mod/emacs/loader.scm"
                                                "symbol-fbound?"))
                      (eql 18 (m60-imp5--grep-c "mod/emacs/loader.scm"
                                                "set-symbol-function!"))
                      (eql 9 (m60-imp5--grep-c "mod/emacs/loader.scm"
                                               "FIX-.*guilemacs"))))

;;; --- S6. The registration of THIS corpus ----------------------------

(setq m60-imp5--group 's6)

(m60-imp5--check "s6/run-tests-m60-imp5"
                 (m60-imp5--holds-all "tool/run-tests.scm"
                                      '("test/m60/test-m60-imp5.el")))

(m60-imp5--check "s6/imp5-after-imp4"
                 (m60-imp5--ordered-p
                  "tool/run-tests.scm"
                  '("test/m60/test-m60-imp1.el"
                    "test/m60/test-m60-imp2.el"
                    "test/m60/test-m60-imp3.el"
                    "test/m60/test-m60-imp4.el"
                    "test/m60/test-m60-imp5.el")))

;; The (m60) group must not take the prelude key: a prelude run would
;; load the prelude BEFORE the corpus and hide a missing boot.
(m60-imp5--check "s6/m60-group-no-prelude"
                 (m60-imp5--all
                  (m60-imp5--holds-all "tool/run-tests.scm" '("(group (m60)"))
                  (m60-imp5--holds-none "tool/run-tests.scm"
                                        '("(group (m60 "))))

;;; --- S7. The guards -------------------------------------------------

;; Per-group floors stop a silent loss of a group: S1 5, S2 4, S3 8,
;; S4 6, S5 2, S6 3.
(setq m60-imp5--group 's7)

(m60-imp5--check "s7/min-s1-checks-5" (>= (m60-imp5--group-count 's1) 5))
(m60-imp5--check "s7/min-s2-checks-4" (>= (m60-imp5--group-count 's2) 4))
(m60-imp5--check "s7/min-s3-checks-8" (>= (m60-imp5--group-count 's3) 8))
(m60-imp5--check "s7/min-s4-checks-6" (>= (m60-imp5--group-count 's4) 6))
(m60-imp5--check "s7/min-s5-checks-2" (>= (m60-imp5--group-count 's5) 2))
(m60-imp5--check "s7/min-s6-checks-3" (>= (m60-imp5--group-count 's6) 3))

(m60-imp5--check "s7/prog-absent-routes-to-skip"
                 (and (eq 'skip (m60-imp5--verdict 'm60-imp5-prog-absent))
                      (eq 'skip (m60-imp5--verdict
                                 (m60-imp5--all
                                  'm60-imp5-prog-absent
                                  (m60-imp5--probe-line "require"
                                                        "REQUIRE cdl: cdl"))))
                      (eq 'absent (m60-imp5--verdict 'm60-imp5-absent))
                      (eq 'absent (m60-imp5--verdict
                                   (m60-imp5--all 'm60-imp5-absent t)))
                      (eq 'pass (m60-imp5--verdict t))
                      (eq 'fail (m60-imp5--verdict nil))
                      (eq 'fail (m60-imp5--verdict (m60-imp5--all t nil)))))

;;; --- The group-total check ------------------------------------------

;; MEASURED: 35 registered checks (S1 5, S2 4, S3 8, S4 6, S5 2, S6 3,
;; S7 7) plus this deftest itself = 36 ERT tests.

(defvar m60-imp5--min-gate-total 36
  "The exact number of m60-imp5 ERT tests: 35 registered checks (S1 5,
S2 4, S3 8, S4 6, S5 2, S6 3, S7 7) plus the group-total deftest
itself.")

(ert-deftest m60-imp5/gate-m60-total ()
  "The m60-imp5 corpus registers at least its docs-independent floor."
  (should (>= (length (ert-select-tests "^m60-imp5" t))
              m60-imp5--min-gate-total)))

(princ (format "=== m60 imp-5 suite done (%d checks; s1 %d, s2 %d, s3 %d, s4 %d, s5 %d, s6 %d, s7 %d) ===\n"
               m60-imp5--registered
               (m60-imp5--group-count 's1)
               (m60-imp5--group-count 's2)
               (m60-imp5--group-count 's3)
               (m60-imp5--group-count 's4)
               (m60-imp5--group-count 's5)
               (m60-imp5--group-count 's6)
               (m60-imp5--group-count 's7)))
