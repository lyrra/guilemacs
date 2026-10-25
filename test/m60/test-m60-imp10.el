;;; test-m60-imp10.el --- M60 imp-10 comparison/arithmetic cells corpus.
;;;
;;; M60 imp-10 lands row 29 of the row map of docs/m60-plan.org section
;;; 6: the function cells of `eq', `eql', `equal', `null', `+', `-',
;;; `*', `/', `=', `<', `>', `1+', `1-', `length' and `nreverse'.
;;; MEASURED 2026-10-22 with mode `arith' of test/m60/probe-imp3.scm:
;;; all 15 names are EMPTY in a plain `guile -L mod' process, and
;;; `lisp/color.el' stops at `void-function (/)'.
;;;
;;; Every name already had a pure-Scheme definition, so this corpus pins
;;; IMPORTS and GUARDED INSTALLS only -- NO new procedure is written, and
;;; the C delta is 0:
;;;   (emacs types)     elisp-null :147, elisp-eq :174, elisp-eql :178,
;;;                     elisp-equal :209
;;;   (emacs numbers)   elisp-+ :76, elisp-- :79, elisp-* :82,
;;;                     elisp-/ :91, elisp-1+ :104, elisp-1- :107, and
;;;                     the `let-syntax' block at :126 for elisp-=,
;;;                     elisp-< and elisp->
;;;   (emacs sequences) elisp-length :297
;;;   (emacs utils)     elisp-nreverse :264
;;;
;;; The guard is the row-18 pattern `(unless (symbol-fbound? 'NAME)
;;; (set-symbol-function! 'NAME PROC))': a full Emacs already owns the C
;;; DEFUN (src/data.c, src/fns.c) in that cell, so an UNGUARDED install
;;; would replace the C cell for EVERY elisp caller.
;;;
;;; The 3 bulk installers are NOT called: `init-types-registrations',
;;; `init-numbers-registrations' (numbers.scm :290) and
;;; `init-utils-registrations' (utils.scm :594) install with no guard.
;;; utils.scm :610 is the UNGUARDED `nreverse' install; it does not run on
;;; this path, and this row does not call it.
;;;
;;; Truth values: elisp-eq, elisp-eql, elisp-equal, elisp-null and the 5
;;; comparison procedures return #t or #nil, and (eq? '#nil #f) is
;;; FALSE.  A condition from one of these cells MUST pass through
;;; `elisp-loader-truthy?' (loader.scm :1062).  Group S2 pins that rule
;;; with the 2 TRUTHY lines of mode `arith' (cr.org F6).
;;;
;;; LIMITS, named in the source and NOT claimed here:
;;;   L15 `EMPTY-CELLS' is a FIXED 11-name list, so it stays () and is
;;;       NOT the proof of row 29; the proof is the `CELLS' line.
;;;   L22 `check-number-coerce-marker' (numbers.scm :56) tests a marker
;;;       through the `markerp' cell, and that cell is EMPTY here, so
;;;       these cells are correct for NUMBERS only.
;;;   L23 `elisp-/` with 0 arguments (numbers.scm :93) calls the
;;;       `signal' cell, and that cell is EMPTY here too.
;;;   L24 `<=' and `>=' are NOT in the row-29 name list of
;;;       milestone.org section 3.  Their definitions exist
;;;       (numbers.scm :126) and they stay EMPTY; a later row owns them.
;;;
;;; This corpus reads TRACKED files only and does NOT read docs/.  A read
;;; error is a real error, never a silent pass.  An absent TRACKED file
;;; is a real FAIL.  A missing `guile' binary is an explicit INFO skip,
;;; never a pass.
;;;
;;; Groups: S1 the install sources, S2 the observables of the live
;;; `guile' child (mode `arith'), S3 the re-measured surface, S4 this
;;; registration, S5 the guards.

(princ "=== m60 imp-10 comparison/arithmetic suite ===\n")

(require 'imp-ert-report)

(defvar m60-imp10--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))
(defvar m60-imp10--registered 0
  "Total number of checks this corpus has registered.")
(defvar m60-imp10--group nil
  "The group that `m60-imp10--check' counts into: `s1' .. `s5', or nil.")
(defvar m60-imp10--counts nil
  "Alist of (GROUP . COUNT) for the registered checks.")
(defvar m60-imp10--probe-cache nil
  "Alist of (MODE . RESULT) of the plain-guile probe runs of this corpus.")

(defun m60-imp10--group-count (group)
  "Number of checks registered so far in GROUP."
  (or (cdr (assq group m60-imp10--counts)) 0))

(defun m60-imp10--bump-group ()
  "Count one check into `m60-imp10--group'."
  (when m60-imp10--group
    (let ((cell (assq m60-imp10--group m60-imp10--counts)))
      (if cell
          (setcdr cell (1+ (cdr cell)))
        (push (cons m60-imp10--group 1) m60-imp10--counts)))))

;;; --- tracked-file helpers (the imp-1 / imp-6 / imp-9 idioms) --------

(defun m60-imp10--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
the symbol `m60-imp10-absent' when REL does not exist."
  (let ((path (expand-file-name rel m60-imp10--root)))
    (if (not (file-exists-p path))
        'm60-imp10-absent
      (with-temp-buffer
        (insert-file-contents path)
        (let ((case-fold-search nil))
          (funcall fn))))))

(defun m60-imp10--holds-all (rel needles)
  "Non-nil when the TRACKED file REL holds every NEEDLE."
  (m60-imp10--with rel
    (lambda ()
      (let ((all t))
        (dolist (needle needles)
          (goto-char (point-min))
          (unless (search-forward needle nil t) (setq all nil)))
        all))))

(defun m60-imp10--holds-none (rel needles)
  "Non-nil when the TRACKED file REL holds NO needle of NEEDLES."
  (m60-imp10--with rel
    (lambda ()
      (let ((none t))
        (dolist (needle needles)
          (goto-char (point-min))
          (when (search-forward needle nil t) (setq none nil)))
        none))))

(defun m60-imp10--literal-lines (rel needle)
  "Count the LINES of REL that hold NEEDLE as a LITERAL substring.  Use
this helper and not a regexp search where NEEDLE holds a metacharacter:
`+', `*', `?', `=' and `/' are operators of the search syntax."
  (m60-imp10--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (not (eobp))
          (when (search-forward needle (line-end-position) t)
            (setq n (1+ n)))
          (forward-line 1))
        n))))

(defun m60-imp10--lines (rel)
  "Count the NEWLINES of REL, the unit of `wc -l'."
  (m60-imp10--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (search-forward "\n" nil t) (setq n (1+ n)))
        n))))

(defun m60-imp10--grep-c (rel regexp)
  "Count the LINES of REL that match REGEXP, the unit of `grep -c'."
  (m60-imp10--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (not (eobp))
          (when (re-search-forward regexp (line-end-position) t)
            (setq n (1+ n)))
          (forward-line 1))
        n))))

(defun m60-imp10--ordered-p (rel needles)
  "Non-nil when the TRACKED file REL holds every NEEDLE in the GIVEN
ORDER."
  (m60-imp10--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((all t))
        (dolist (needle needles)
          (when all
            (unless (search-forward needle nil t) (setq all nil))))
        all))))

;;; --- the plain-guile probe runner -----------------------------------

(defun m60-imp10--probe-1 (mode)
  "Run test/m60/probe-imp3.scm in MODE as a `guile -L mod' child, with
GUILE_AUTO_COMPILE=0 and GUILEMACS_ROOT set.  Return (EXIT . OUTPUT) or
the symbol `m60-imp10-prog-absent'."
  (if (not (executable-find "guile"))
      'm60-imp10-prog-absent
    (let ((buf (get-buffer-create " *m60-imp10-probe*"))
          (default-directory m60-imp10--root)
          (process-environment
           (append (list (concat "GUILEMACS_ROOT=" m60-imp10--root)
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

(defun m60-imp10--probe (mode)
  "The cached result of `m60-imp10--probe-1' for MODE."
  (let ((cell (assoc mode m60-imp10--probe-cache)))
    (if cell
        (cdr cell)
      (let ((result (m60-imp10--probe-1 mode)))
        (push (cons mode result) m60-imp10--probe-cache)
        result))))

(defun m60-imp10--probe-output (mode)
  "The OUTPUT of the probe MODE when the child exited 0, else nil.  A
missing `guile' binary returns the marker `m60-imp10-prog-absent', so
the caller can SKIP and not pass or fail."
  (let ((result (m60-imp10--probe mode)))
    (cond
     ((eq result 'm60-imp10-prog-absent) result)
     ((and (consp result) (eql 0 (car result))) (cdr result))
     (t nil))))

(defun m60-imp10--probe-line (mode line)
  "Non-nil when the probe MODE printed LINE as one WHOLE line and the
child exited 0."
  (let ((out (m60-imp10--probe-output mode)))
    (cond
     ((eq out 'm60-imp10-prog-absent) out)
     ((not (stringp out)) nil)
     (t (with-temp-buffer
          (insert "\n" out "\n")
          (goto-char (point-min))
          (and (search-forward (concat "\n" line "\n") nil t) t))))))

(defun m60-imp10--all (&rest values)
  "`and' over the ALREADY-EVALUATED VALUES, where a MARKER wins over a
nil: the absent FILE marker first (a real FAIL), then the absent `guile'
marker (a skip)."
  (cond
   ((memq 'm60-imp10-absent values) 'm60-imp10-absent)
   ((memq 'm60-imp10-prog-absent values) 'm60-imp10-prog-absent)
   ((memq nil values) nil)
   (t t)))

(defun m60-imp10--verdict (ok)
  "Classify the value OK of one check: `pass', `fail', `absent' (a
TRACKED file is missing) or `skip' (no `guile' binary)."
  (cond
   ((eq ok 'm60-imp10-prog-absent) 'skip)
   ((eq ok 'm60-imp10-absent) 'absent)
   (ok 'pass)
   (t 'fail)))

(defun m60-imp10--check (name ok)
  "Report and register one check.  An absent `guile' binary registers a
controlled ERT skip -- never a pass."
  (let ((verdict (m60-imp10--verdict ok)))
    (cond
     ((eq verdict 'skip)
      (princ (format "INFO m60/imp10/%s no guile binary on PATH\n" name))
      (setq m60-imp10--registered (1+ m60-imp10--registered))
      (m60-imp10--bump-group)
      (imp-register-skip-as-ert-test (format "m60-imp10/%s" name)
                                     "no guile binary on PATH"))
     ((eq verdict 'absent)
      (princ (format "FAIL m60/imp10/%s (source file absent)\n" name))
      (setq m60-imp10--registered (1+ m60-imp10--registered))
      (m60-imp10--bump-group)
      (imp-register-bool-as-ert-test (format "m60-imp10/%s" name) nil))
     (t
      (princ (format "%s m60/imp10/%s\n"
                     (if (eq verdict 'pass) "PASS" "FAIL") name))
      (setq m60-imp10--registered (1+ m60-imp10--registered))
      (m60-imp10--bump-group)
      (imp-register-bool-as-ert-test (format "m60-imp10/%s" name)
                                     (eq verdict 'pass))))))

;;; --- S1. The install sources ----------------------------------------

(setq m60-imp10--group 's1)

(defvar m60-imp10--names
  '(eq eql equal null + - * / = < > 1+ 1- length nreverse)
  "The 15 row-29 names.  The unit is NAMES, and the count is MEASURED
with mode `arith', not copied from milestone.org section 4 (which says
14).")

(defconst m60-imp10--installs
  '(("eq" "elisp-eq") ("eql" "elisp-eql") ("equal" "elisp-equal")
    ("null" "elisp-null")
    ("+" "elisp-+") ("-" "elisp--") ("*" "elisp-*") ("/" "elisp-/")
    ("=" "elisp-=") ("<" "elisp-<") (">" "elisp->")
    ("1+" "elisp-1+") ("1-" "elisp-1-")
    ("length" "elisp-length") ("nreverse" "elisp-nreverse"))
  "The 15 (ELISP-NAME SCHEME-PROCEDURE) pairs of row 29.  Every
PROCEDURE already existed before this row.")

;; 15 names, 1 guarded install each, and no 16th name.
(m60-imp10--check "s1/one-guarded-install-per-name"
                 (m60-imp10--all
                  (eql 15 (length m60-imp10--installs))
                  (let ((all t))
                    (dolist (pair m60-imp10--installs)
                      (let ((form (format "(unless (symbol-fbound? '%s)"
                                          (car pair))))
                        (unless (eql 1 (m60-imp10--literal-lines
                                        "mod/emacs/loader.scm" form))
                          (setq all nil))
                        (unless (eql 1 (m60-imp10--literal-lines
                                        "mod/emacs/loader.scm"
                                        (format "(set-symbol-function! '%s %s)"
                                                (car pair) (cadr pair))))
                          (setq all nil))))
                    all)))

;; The 3 module imports: 2 new `#:use-module' forms and the extended
;; `#:select' list of (emacs sequences).
(m60-imp10--check "s1/module-imports"
                 (m60-imp10--all
                  (m60-imp10--holds-all
                   "mod/emacs/loader.scm"
                   '("#:use-module ((emacs types)"
                     ;; M60 imp-15 RE-PIN: the OLD pin was
                     ;; "#:select (elisp-eq elisp-eql elisp-equal elisp-null))".
                     ;; Row 32 imports the hash-table predicate from the
                     ;; same module, so the select list is longer and it
                     ;; spans 2 lines.
                     "#:select (elisp-eq elisp-eql elisp-equal elisp-null"
                     "elisp-hash-table-p))"
                     "#:use-module ((emacs numbers)"
                     "#:use-module ((emacs sequences) #:select (elisp-append elisp-length))"))))

;; Every installed PROCEDURE is defined in its owner module and exported,
;; so `#:select' resolves.  No new procedure is written by this row.
(m60-imp10--check "s1/owners-export-the-procedures"
                 (m60-imp10--all
                  (m60-imp10--holds-all
                   "mod/emacs/types.scm"
                   '("elisp-null" "elisp-eq" "elisp-eql" "elisp-equal"))
                  (m60-imp10--holds-all
                   "mod/emacs/numbers.scm"
                   '("elisp-+" "elisp--" "elisp-*" "elisp-/"))
                  (m60-imp10--holds-all
                   "mod/emacs/sequences.scm" '("elisp-length"))
                  (m60-imp10--holds-all
                   "mod/emacs/utils.scm" '("elisp-nreverse"))))

;; The comparison procedures are built by 1 `let-syntax' block and return
;; #t or #nil.  The block is at numbers.scm :126 (the brief said :117 ..
;; :136; an earlier cr.org round F3 corrected it).
(m60-imp10--check "s1/comparison-truth-values"
                 (m60-imp10--all
                  (m60-imp10--ordered-p
                   "mod/emacs/numbers.scm"
                   '("(let-syntax"
                     "(frob = elisp-=)"
                     "(frob < elisp-<)"
                     "(frob > elisp->)"))))

;; The 3 bulk installers stay UNCALLED: they install with no guard, so
;; they would replace the C cell of a full Emacs.
(m60-imp10--check "s1/no-bulk-installer"
                 (m60-imp10--holds-none
                  "mod/emacs/loader.scm"
                  '("(init-types-registrations)"
                    "(init-numbers-registrations)"
                    "(init-utils-registrations)")))


;; L24: `<=' and `>=' are not in the row-29 list and stay EMPTY, so this
;; row adds no install for them.
(m60-imp10--check "s1/no-extra-names-installed"
                 (m60-imp10--holds-none
                  "mod/emacs/loader.scm"
                  '("(symbol-fbound? '<=)" "(symbol-fbound? '>=)")))

;;; --- S2. The observables (live `guile' child, mode `arith') ---------

(setq m60-imp10--group 's2)

;; The CELLS line is the proof of row 29: no name of the row stays EMPTY.
;; F4 of the imp-10 cr.org review: the format is `NAME -> VALUE' with
;; the name written by `~s', so no name can absorb the separator.  The
;; old `~a=~s' format printed the `< #t' pair as `<==#t', which reads as
;; "the cell of `=' is bound to #t".
(m60-imp10--check "s2/cells-bound"
                 (m60-imp10--all
                  (m60-imp10--probe-line
                   "arith"
                   (concat "CELLS: eq -> #t eql -> #t equal -> #t null -> #t"
                           " + -> #t - -> #t * -> #t / -> #t = -> #t < -> #t"
                           " > -> #t #{1+}# -> #t #{1-}# -> #t length -> #t"
                           " nreverse -> #t"))
                  (m60-imp10--probe-line "arith" "COUNT: 0")))

;; The installed cell is a real elisp primitive, not only a bound cell.
(m60-imp10--check "s2/non-numeric-calls"
                 (m60-imp10--all
                  (m60-imp10--probe-line "arith" "CALL eq: #t")
                  (m60-imp10--probe-line "arith" "CALL eq-miss: #nil")
                  (m60-imp10--probe-line "arith" "CALL eql: #t")
                  (m60-imp10--probe-line "arith" "CALL equal: #t")
                  (m60-imp10--probe-line "arith" "CALL null: #t")
                  (m60-imp10--probe-line "arith" "CALL null-false: #nil")
                  (m60-imp10--probe-line "arith" "CALL length: 3")
                  (m60-imp10--probe-line "arith" "CALL nreverse: (3 2 1)")))

(m60-imp10--check "s2/numeric-calls"
                 (m60-imp10--all
                  (m60-imp10--probe-line "arith" "CALL +: 6")
                  (m60-imp10--probe-line "arith" "CALL -: 6")
                  (m60-imp10--probe-line "arith" "CALL *: 6")
                  (m60-imp10--probe-line "arith" "CALL /: 4")
                  (m60-imp10--probe-line "arith" "CALL 1+: 42")
                  (m60-imp10--probe-line "arith" "CALL 1-: 42")))

;; A comparison returns #t or #nil, and #nil is NOT #f, so the caller
;; must use `elisp-loader-truthy?' (:1062).
(m60-imp10--check "s2/comparison-calls"
                 (m60-imp10--all
                  (m60-imp10--probe-line "arith" "CALL = : #t")
                  (m60-imp10--probe-line "arith" "CALL <: #t")
                  (m60-imp10--probe-line "arith" "CALL >: #t")
                  (m60-imp10--probe-line "arith" "CALL >-false: #nil")))

;; F6 of the imp-10 cr.org review: the rule above is now PINNED, not
;; only written.  A FALSE comparison gives `#nil', `(eq? '#nil #f)' is
;; false, and `elisp-loader-truthy?' maps it to #f.  Without these 2
;; lines a caller could test the raw cell value against #f and be wrong.
(m60-imp10--check "s2/truth-value-rule"
                 (m60-imp10--all
                  (m60-imp10--probe-line "arith" "TRUTHY #nil-is-not-#f: #f")
                  (m60-imp10--probe-line
                   "arith" "TRUTHY elisp-loader-truthy?: #f")))

;; The 3 recorded FIRST STOPS after this row: color.el moves past `/',
;; the other 2 stop on rows 30 and 31.
(m60-imp10--check "s2/recorded-first-stops"
                 (m60-imp10--all
                  (m60-imp10--probe-line "arith" "LOAD lisp/color.el: done")
                  ;; M60 imp-11 RE-PIN: the OLD line was
                  ;; `LOAD lisp/calendar/time-date.el: ERROR void-function
                  ;; (put)'.  Row 30 installs the `put' cell, so the load
                  ;; moves past it to the NEXT empty cell of the same
                  ;; require chain (`make-hash-table', macroexp.el :165).
                  ;; M60 imp-13 RE-PIN: the OLD line was
                  ;; `LOAD lisp/calendar/time-date.el: ERROR wrong-type-arg
                  ;; (#f "Wrong type to apply: ~S" (#nil) (#nil))'.  Row 33
                  ;; installs the `set' cell, so the load moves to the NEXT
                  ;; wall, `make-hash-table' (row 32, macroexp.el :165).
                  (m60-imp10--probe-line
                   "arith"
                  ;; M60 imp-15 RE-PIN: row 32 installs the
                  ;; `make-hash-table' family, so this wall MOVED.
                   "LOAD lisp/calendar/time-date.el: ERROR void-function (define-obsolete-function-alias)")
                  (m60-imp10--probe-line
                   "arith"
                   ;; M60 imp-12 RE-PIN: the OLD line was
                   ;; `LOAD lisp/subr.el: ERROR void-function (eval-and-compile)'.
                   ;; Row 31 adds the branch, so the load moves PAST form 1 to the
                   ;; NEXT wall, `defalias' at subr.el :29.  `subr.el' does NOT
                   ;; load: a `done' value is a FAIL.
                   "LOAD lisp/subr.el: ERROR void-function (defsubst)")))

;; L15: the FIXED 11-name list is not the proof of this row.
(m60-imp10--check "s2/l15-empty-cells-stays"
                 (m60-imp10--probe-line "arith" "EMPTY-CELLS: ()"))

;; L22 and L23 are RECORDED, not fixed: the `signal' cell and the
;; `markerp' cell are still EMPTY on the plain path.
(m60-imp10--check "s2/l22-l23-recorded"
                 (m60-imp10--all
                  (m60-imp10--probe-line "arith" "signal-fbound: #f")
                  (m60-imp10--probe-line "arith" "markerp-fbound: #f")))

;; No regression: the 12 older modes still run, and mode `cells' prints
;; the state of the 11 guarded names.
(m60-imp10--check "s2/no-regression-on-older-modes"
                 (m60-imp10--all
                  (m60-imp10--probe-line "cells" "EMPTY-CELLS: ()")
                  ;; M60 imp-16 (row 25) RE-PIN: OLD value "LOAD
                  ;; lisp/subdirs.el: ERROR void-function
                  ;; (normal-top-level-add-to-load-path)".
                  (m60-imp10--probe-line
                   "cells"
                   "LOAD lisp/subdirs.el: done")
                  (m60-imp10--probe-line "control" "cond empty: #nil")
                  (m60-imp10--probe-line "defs" "defconst value: 2")
                  (m60-imp10--probe-line "obsolete" "LOAD lisp/obarray.el: done")))

;;; --- S3. The re-measured surface ------------------------------------

(setq m60-imp10--group 's3)


;;; --- S4. The registration of THIS corpus ----------------------------

(setq m60-imp10--group 's4)

(m60-imp10--check "s4/run-tests-m60-imp10"
                 (m60-imp10--holds-all "tool/run-tests.scm"
                                       '("test/m60/test-m60-imp10.el")))

;; The imp-10 line sits AFTER the imp-9 line, and imp-1 ... imp-9 stand.
(m60-imp10--check "s4/registered-after-imp9"
                 (m60-imp10--all
                  (m60-imp10--ordered-p
                   "tool/run-tests.scm"
                   '("test/m60/test-m60-imp9.el"
                     "test/m60/test-m60-imp10.el"))))

;; The (m60) group carries no prelude key: a prelude run would load the
;; prelude BEFORE the corpus and hide a missing boot.
(m60-imp10--check "s4/m60-group-no-prelude"
                 (m60-imp10--all
                  (m60-imp10--holds-all "tool/run-tests.scm" '("(group (m60)"))
                  (m60-imp10--holds-none "tool/run-tests.scm"
                                         '("(group (m60 "))))

;;; --- S5. The guards -------------------------------------------------

(setq m60-imp10--group 's5)

(m60-imp10--check "s5/min-s1-checks-6" (>= (m60-imp10--group-count 's1) 6))
(m60-imp10--check "s5/min-s2-checks-9" (>= (m60-imp10--group-count 's2) 9))
(m60-imp10--check "s5/min-s4-checks-3" (>= (m60-imp10--group-count 's4) 3))

(m60-imp10--check "s5/prog-absent-routes-to-skip"
                 (and (eq 'skip (m60-imp10--verdict 'm60-imp10-prog-absent))
                      (eq 'skip (m60-imp10--verdict
                                 (m60-imp10--all
                                  'm60-imp10-prog-absent
                                  (m60-imp10--probe-line "arith" "COUNT: 0"))))
                      (eq 'absent (m60-imp10--verdict 'm60-imp10-absent))
                      (eq 'pass (m60-imp10--verdict t))
                      (eq 'fail (m60-imp10--verdict nil))
                      (eq 'fail (m60-imp10--verdict
                                 (m60-imp10--all t nil)))))

;;; --- The group-total check ------------------------------------------

(defvar m60-imp10--min-gate-total 23
  "Minimum registered ERT test count for this corpus.")

(ert-deftest m60-imp10/gate-m60-total ()
  "The m60-imp10 corpus registers at least its own floor, so a silent
registration loss is a FAIL."
  (should (>= (length (ert-select-tests "^m60-imp10" t))
              m60-imp10--min-gate-total)))

(princ (format "=== m60 imp-10 suite done (%d checks; s1 %d, s2 %d, s3 %d, s4 %d, s5 %d) ===\n"
               m60-imp10--registered
               (m60-imp10--group-count 's1)
               (m60-imp10--group-count 's2)
               (m60-imp10--group-count 's3)
               (m60-imp10--group-count 's4)
               (m60-imp10--group-count 's5)))
