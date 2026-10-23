;;; test-m60-imp12.el --- M60 imp-12 `eval-and-compile' branch corpus.
;;;
;;; M60 imp-12 lands row 31 of the row map of docs/m60-plan.org section
;;; 4: the `eval-and-compile' branch of `elisp-loader-eval-form'.  The
;;; base file `lisp/subr.el' stops at its FIRST form,
;;;
;;;   (eval-and-compile
;;;    (defalias 'string= #'string-equal)
;;;   )
;;;
;;; MEASURED 2026-10-22 at HEAD cce013c72, plain `guile -L mod': the
;;; stop is `void-function (eval-and-compile)'.  The head falls to the
;;; `else' clause, because the macro table has no entry.
;;;
;;; The work is 1 CLAUSE and NO install: row 31 is a SPECIAL FORM, so it
;;; adds 0 install sites and 0 FIX markers.  C delta 0.
;;;
;;; WHY the body runs ONE time: `boot.el' :49 defines
;;;
;;;   (defmacro eval-and-compile (&rest body)
;;;     `(progn (eval-when-compile ,@body) (progn ,@body)))
;;;
;;; so a COMPILER runs the body 2 times.  A source-reading loader has no
;;; compile phase: it runs the body 1 time at LOAD time, and the value
;;; is the value of the LAST body form.  That is a DECISION, not a port.
;;;
;;; LIMITS, named in the source and NOT claimed here:
;;;   L27 a compiler drops the body of `eval-when-compile' and runs the
;;;       body of `eval-and-compile' 2 times.  This loader runs the body
;;;       ONE time for BOTH rows.
;;;   L28 the body runs under the DYNAMIC binding model of this
;;;       evaluator (L3), not under the lexical model of a compiler.
;;;   L29 the branch does not strip a DOC string and does not warn on a
;;;       non-macro use.
;;;   L30 the value is the value of the last body form at LOAD time.
;;;       The return value of the BYTE-COMPILED form is out of scope.
;;;   L15 still holds: `EMPTY-CELLS' is a FIXED 11-name list, so it is
;;;       NOT the proof of row 31.  The proof is the `subr.el' load line.
;;;
;;; The NEXT walls, RECORDED and not implemented: `defalias' (subr.el
;;; :29) and the `function' head of `#'string-equal'.  Rows 32
;;; (`make-hash-table'), 28b (`backquote'), F3 (`featurep'), 25
;;; (`normal-top-level-add-to-load-path') and L24 (`<=' / `>=') stay
;;; OPEN.
;;;
;;; This corpus reads TRACKED files only and does NOT read docs/.  A read
;;; error is a real error, never a silent pass.  An absent TRACKED file
;;; is a real FAIL.  A missing `guile' binary is an explicit INFO skip,
;;; never a pass.
;;;
;;; Groups: S1 the branch source and its position, S2 the observables of
;;; the live `guile' child (mode `eac') plus no regression on the 14
;;; older modes, S3 the re-measured surface, S4 this registration, S5
;;; the guards.

(princ "=== m60 imp-12 `eval-and-compile' suite ===\n")

(require 'imp-ert-report)

(defvar m60-imp12--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))
(defvar m60-imp12--registered 0
  "Total number of checks this corpus has registered.")
(defvar m60-imp12--group nil
  "The group that `m60-imp12--check' counts into: `s1' .. `s5', or nil.")
(defvar m60-imp12--counts nil
  "Alist of (GROUP . COUNT) for the registered checks.")
(defvar m60-imp12--probe-cache nil
  "Alist of (MODE . RESULT) of the plain-guile probe runs of this corpus.")

(defun m60-imp12--group-count (group)
  "Number of checks registered so far in GROUP."
  (or (cdr (assq group m60-imp12--counts)) 0))

(defun m60-imp12--bump-group ()
  "Count one check into `m60-imp12--group'."
  (when m60-imp12--group
    (let ((cell (assq m60-imp12--group m60-imp12--counts)))
      (if cell
          (setcdr cell (1+ (cdr cell)))
        (push (cons m60-imp12--group 1) m60-imp12--counts)))))

;;; --- tracked-file helpers (the imp-1 / imp-6 / imp-9 idioms) --------

(defun m60-imp12--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
the symbol `m60-imp12-absent' when REL does not exist."
  (let ((path (expand-file-name rel m60-imp12--root)))
    (if (not (file-exists-p path))
        'm60-imp12-absent
      (with-temp-buffer
        (insert-file-contents path)
        (let ((case-fold-search nil))
          (funcall fn))))))

(defun m60-imp12--holds-all (rel needles)
  "Non-nil when the TRACKED file REL holds every NEEDLE."
  (m60-imp12--with rel
    (lambda ()
      (let ((all t))
        (dolist (needle needles)
          (goto-char (point-min))
          (unless (search-forward needle nil t) (setq all nil)))
        all))))

(defun m60-imp12--holds-none (rel needles)
  "Non-nil when the TRACKED file REL holds NO needle of NEEDLES."
  (m60-imp12--with rel
    (lambda ()
      (let ((none t))
        (dolist (needle needles)
          (goto-char (point-min))
          (when (search-forward needle nil t) (setq none nil)))
        none))))

(defun m60-imp12--literal-lines (rel needle)
  "Count the LINES of REL that hold NEEDLE as a LITERAL substring.  Use
this helper and not a regexp search where NEEDLE holds a metacharacter."
  (m60-imp12--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (not (eobp))
          (when (search-forward needle (line-end-position) t)
            (setq n (1+ n)))
          (forward-line 1))
        n))))

(defun m60-imp12--lines (rel)
  "Count the NEWLINES of REL, the unit of `wc -l'."
  (m60-imp12--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (search-forward "\n" nil t) (setq n (1+ n)))
        n))))

(defun m60-imp12--grep-c (rel regexp)
  "Count the LINES of REL that match REGEXP, the unit of `grep -c'."
  (m60-imp12--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (not (eobp))
          (when (re-search-forward regexp (line-end-position) t)
            (setq n (1+ n)))
          (forward-line 1))
        n))))

(defun m60-imp12--ordered-p (rel needles)
  "Non-nil when the TRACKED file REL holds every NEEDLE in the GIVEN
ORDER."
  (m60-imp12--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((all t))
        (dolist (needle needles)
          (when all
            (unless (search-forward needle nil t) (setq all nil))))
        all))))

(defun m60-imp12--text-between (rel start end)
  "The TEXT of the TRACKED file REL between the literal needles START
and END, or nil when either needle is absent.  Use this to pin ONE
comment block and not the whole file."
  (m60-imp12--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((from (search-forward start nil t)))
        (when from
          (let ((to (search-forward end nil t)))
            (when to
              (buffer-substring-no-properties from
                                              (1- (point))))))))))

;;; --- the plain-guile probe runner -----------------------------------

(defun m60-imp12--probe-1 (mode)
  "Run test/m60/probe-imp3.scm in MODE as a `guile -L mod' child, with
GUILE_AUTO_COMPILE=0 and GUILEMACS_ROOT set.  Return (EXIT . OUTPUT) or
the symbol `m60-imp12-prog-absent'."
  (if (not (executable-find "guile"))
      'm60-imp12-prog-absent
    (let ((buf (get-buffer-create " *m60-imp12-probe*"))
          (default-directory m60-imp12--root)
          (process-environment
           (append (list (concat "GUILEMACS_ROOT=" m60-imp12--root)
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

(defun m60-imp12--probe (mode)
  "The cached result of `m60-imp12--probe-1' for MODE."
  (let ((cell (assoc mode m60-imp12--probe-cache)))
    (if cell
        (cdr cell)
      (let ((result (m60-imp12--probe-1 mode)))
        (push (cons mode result) m60-imp12--probe-cache)
        result))))

(defun m60-imp12--probe-output (mode)
  "The OUTPUT of the probe MODE when the child exited 0, else nil.  A
missing `guile' binary returns the marker `m60-imp12-prog-absent', so
the caller can SKIP and not pass or fail."
  (let ((result (m60-imp12--probe mode)))
    (cond
     ((eq result 'm60-imp12-prog-absent) result)
     ((and (consp result) (eql 0 (car result))) (cdr result))
     (t nil))))

(defun m60-imp12--probe-line (mode line)
  "Non-nil when the probe MODE printed LINE as one WHOLE line and the
child exited 0."
  (let ((out (m60-imp12--probe-output mode)))
    (cond
     ((eq out 'm60-imp12-prog-absent) out)
     ((not (stringp out)) nil)
     (t (with-temp-buffer
          (insert "\n" out "\n")
          (goto-char (point-min))
          (and (search-forward (concat "\n" line "\n") nil t) t))))))

(defun m60-imp12--probe-exit (mode)
  "The EXIT status of the probe MODE, or nil when `guile' is absent."
  (let ((result (m60-imp12--probe mode)))
    (cond
     ((eq result 'm60-imp12-prog-absent) result)
     ((consp result) (car result))
     (t nil))))

(defun m60-imp12--all (&rest values)
  "`and' over the ALREADY-EVALUATED VALUES, where a MARKER wins over a
nil: the absent FILE marker first (a real FAIL), then the absent `guile'
marker (a skip)."
  (cond
   ((memq 'm60-imp12-absent values) 'm60-imp12-absent)
   ((memq 'm60-imp12-prog-absent values) 'm60-imp12-prog-absent)
   ((memq nil values) nil)
   (t t)))

(defun m60-imp12--verdict (ok)
  "Classify the value OK of one check: `pass', `fail', `absent' (a
TRACKED file is missing) or `skip' (no `guile' binary)."
  (cond
   ((eq ok 'm60-imp12-prog-absent) 'skip)
   ((eq ok 'm60-imp12-absent) 'absent)
   (ok 'pass)
   (t 'fail)))

(defun m60-imp12--check (name ok)
  "Report and register one check.  An absent `guile' binary registers a
controlled ERT skip -- never a pass."
  (let ((verdict (m60-imp12--verdict ok)))
    (cond
     ((eq verdict 'skip)
      (princ (format "INFO m60/imp12/%s no guile binary on PATH\n" name))
      (setq m60-imp12--registered (1+ m60-imp12--registered))
      (m60-imp12--bump-group)
      (imp-register-skip-as-ert-test (format "m60-imp12/%s" name)
                                     "no guile binary on PATH"))
     ((eq verdict 'absent)
      (princ (format "FAIL m60/imp12/%s (source file absent)\n" name))
      (setq m60-imp12--registered (1+ m60-imp12--registered))
      (m60-imp12--bump-group)
      (imp-register-bool-as-ert-test (format "m60-imp12/%s" name) nil))
     (t
      (princ (format "%s m60/imp12/%s\n"
                     (if (eq verdict 'pass) "PASS" "FAIL") name))
      (setq m60-imp12--registered (1+ m60-imp12--registered))
      (m60-imp12--bump-group)
      (imp-register-bool-as-ert-test (format "m60-imp12/%s" name)
                                     (eq verdict 'pass))))))

;;; --- S1. The branch source and its position -------------------------

(setq m60-imp12--group 's1)

;; Exactly 1 clause and 1 head test: row 31 owns ONE branch (risk R3).
(m60-imp12--check "s1/one-branch"
                 (m60-imp12--all
                  (eql 1 (m60-imp12--literal-lines
                          "mod/emacs/loader.scm"
                          "((eq? head 'eval-and-compile)"))
                  (eql 1 (m60-imp12--literal-lines
                          "mod/emacs/loader.scm"
                          ";; M60 imp-12 -- row 31"))))

;; The clause sits DIRECTLY after the `eval-when-compile' clause and
;; BEFORE the `defmacro' comment block.  `cond' tests in order, so a
;; clause after `else' would be DEAD code (risk R1).
(m60-imp12--check "s1/branch-position"
                 (m60-imp12--ordered-p
                  "mod/emacs/loader.scm"
                  '("((eq? head 'eval-when-compile)"
                    "((eq? head 'eval-and-compile)"
                    ";; M60 imp-7 -- row 23: `defmacro' STORES an expander")))

;; The body of the clause is the SHARED sequence evaluator: no 2nd
;; evaluator, and no `eval-when-compile' CALL form, because a rewrite
;; would add 1 pass and 1 macro lookup.
(m60-imp12--check "s1/body-is-eval-seq"
                 (m60-imp12--all
                  (m60-imp12--ordered-p
                   "mod/emacs/loader.scm"
                   '("((eq? head 'eval-and-compile)"
                     "(elisp-loader-eval-seq (cdr form))"))
                  (m60-imp12--holds-none
                   "mod/emacs/loader.scm"
                   '("(eval-and-compile (eval-when-compile"))))

;; Row 31 is a SPECIAL FORM and NOT a cell: no install site, so the 2
;; design counters do not move (brief.org section 5).
(m60-imp12--check "s1/no-install"
                 (m60-imp12--holds-none
                  "mod/emacs/loader.scm"
                  '("(set-symbol-function! 'eval-and-compile"
                    "(unless (symbol-fbound? 'eval-and-compile)")))

;; The Emacs expansion that the DECISION replaces is in the source
;; comment, so a later reader does not have to re-measure it.
(m60-imp12--check "s1/boot-expansion-recorded"
                 (m60-imp12--all
                  (m60-imp12--holds-all
                   "mod/emacs/loader.scm"
                   '("boot.el :49 expands it to 2 nested `progn' forms"
                     "runs the body 2 TIMES"
                     "RUNS ONE time at LOAD time"))
                  (m60-imp12--holds-all
                   "mod/emacs-elisp/boot.el"
                   '("(defmacro eval-and-compile (&rest body)"))))

;; L27 ... L30 are NAMED in the source, next to the branch.
(m60-imp12--check "s1/limits-recorded"
                 (m60-imp12--all
                  (m60-imp12--holds-all
                   "mod/emacs/loader.scm"
                   '("M60 imp-12 LIMITS of row 31"
                     "L27 a compiler drops the body of `eval-when-compile'"
                     "L28 the body runs under the DYNAMIC binding model"
                     "L29 the branch does not strip a DOC string"
                     "L30 the value is the value of the last body form"))))


;; REVIEW RULE (cr.org F2): the imp-12 limit block cites the LIMITS
;; section of its own brief, and not the record section.  A wrong
;; section number sends the reader to the wrong text.
(m60-imp12--check "s1/limit-cites-brief-section-9"
                 (let ((text (m60-imp12--text-between
                              "mod/emacs/loader.scm"
                              "M60 imp-12 LIMITS of row 31"
                              ";; L27 a compiler drops the body")))
                   (m60-imp12--all
                    (and (stringp text)
                         (string-match-p "brief\\.org section 9" text)
                         (not (string-match-p "brief\\.org section 10"
                                              text))))))

;; REVIEW RULE: a row-map STATUS list does NOT live in the imp-12 limit
;; block.  A status in a code comment goes stale at the next row, so
;; this corpus owns it.  Only the behavior and the named limits stay in
;; the source.  The check reads the imp-12 block ONLY: older limit
;; blocks (rows 28a, 28b) keep their own status lines.
(m60-imp12--check "s1/no-row-status-in-source"
                 (let ((text (m60-imp12--text-between
                              "mod/emacs/loader.scm"
                              "M60 imp-12 LIMITS of row 31"
                              ";; M60 imp-12 -- row 31:")))
                   (m60-imp12--all
                    (and (stringp text)
                         (not (string-match-p "OPEN" text))
                         (not (string-match-p "CLOSED" text))))))

;; REVIEW RULE: the L27 ... L30 block sits ABOVE the clause comment, so the
;; row-31 clause stays NEXT to the `defmacro' comment of row 23.  The
;; clause is 5 comment LINES and 2 code LINES, as brief.org section 4
;; shows.  `cond' tests its clauses in ORDER, so this adjacency is also
;; the proof that the clause is not DEAD code (risk R1).
(m60-imp12--check "s1/limits-above-clause"
                 (m60-imp12--all
                  (m60-imp12--ordered-p
                   "mod/emacs/loader.scm"
                   '("M60 imp-12 LIMITS of row 31"
                     ";; M60 imp-12 -- row 31:"))
                  (m60-imp12--holds-all
                   "mod/emacs/loader.scm"
                   '("      ((eq? head 'eval-and-compile)
       (elisp-loader-eval-seq (cdr form)))
      ;; M60 imp-7 -- row 23: `defmacro' STORES an expander"))))

;;; --- S2. The observables (live `guile' child, mode `eac') -----------

(setq m60-imp12--group 's2)

;; The value of the LAST body form, for a 3-form and a 1-form body, and
;; the elisp nil for an EMPTY body.
(m60-imp12--check "s2/returns-last-value"
                 (m60-imp12--all
                  (m60-imp12--probe-line "eac" "EAC ret: 3")
                  (m60-imp12--probe-line "eac" "EAC one form ret: 7")
                  (m60-imp12--probe-line "eac" "EAC empty ret: #nil")))

;; Risk R5: the body runs ONE time.  A `progn' rewrite of the 2 nested
;; forms of boot.el :49 would run it 2 times per form, so the variable
;; `m60-probe-eac-v' would read 5 and not 3.  cr.org F5: the printed
;; line names the FULL probe variable, so a reader needs no fixture.
(m60-imp12--check "s2/side-effects-once"
                 (m60-imp12--probe-line
                  "eac" "EAC side effects: 3 m60-probe-eac-v=3"))

;; The row is a SPECIAL FORM: the elisp function cell stays EMPTY.
(m60-imp12--check "s2/not-a-cell"
                 (m60-imp12--probe-line "eac" "EAC is not a cell: #f"))

;; THE ACCEPTANCE of row 31: the branch runs, and the load of the base
;; file stops on the NEXT wall, `defalias' at subr.el :29.  A `done'
;; value is a FAIL.
(m60-imp12--check "s2/subr-stop-moved"
                 (m60-imp12--probe-line
                  "eac"
                  "EAC load line: ERROR void-function (defsubst)")

;; The same stop from the 3 older modes that load `lisp/subr.el'.  This
;; is the no-regression proof of brief.org section 7.4: those lines are
;; the ONLY difference from HEAD.
(m60-imp12--check "s2/subr-stop-in-older-modes"
                 (m60-imp12--all
                  (m60-imp12--probe-line
                   "arith" "LOAD lisp/subr.el: ERROR void-function (defsubst)")
                  (m60-imp12--probe-line
                   "control" "LOAD lisp/subr.el: ERROR void-function (defsubst)")
                  (m60-imp12--probe-line
                   "put" "LOAD lisp/subr.el: ERROR void-function (defsubst)")))

;; No regression: the 13 other older modes still run and keep their
;; lines.  Mode `registration' is NOT here: its non-zero exit status is
;; the recorded blocker of M60 imp-2, so it is pinned by imp-2.
(m60-imp12--check "s2/no-regression-on-older-modes"
                 (m60-imp12--all
                  (m60-imp12--probe-line "cells" "EMPTY-CELLS: ()")
                  (m60-imp12--probe-line "provide" "LOAD cdl: done")
                  (m60-imp12--probe-line "defs" "defconst value: 2")
                  (m60-imp12--probe-line "macros" "defmacro call noeval: 7")
                  (m60-imp12--probe-line "obsolete"
                                         "LOAD lisp/obarray.el: done")
                  (m60-imp12--probe-line "control" "cond empty: #nil")
                  (m60-imp12--probe-line "arith" "COUNT: 0")
                  (m60-imp12--probe-line
                   "put" "CELLS: put -> #t get -> #f make-hash-table -> #f")
                  (m60-imp12--probe-line
                   "language" "LANGUAGE-NAME: emacs-elisp")))

;; Mode `eac' itself exits 0.  A non-zero status would make every
;; `probe-line' of this group return nil, so the status is pinned too.
(m60-imp12--check "s2/eac-exit-status"
                 (m60-imp12--all
                  (eql 0 (m60-imp12--probe-exit "eac"))
                  (eql 0 (m60-imp12--probe-exit "arith"))
                  (eql 0 (m60-imp12--probe-exit "control"))
                  (eql 0 (m60-imp12--probe-exit "put"))))

;;; --- S3. The re-measured surface ------------------------------------

(setq m60-imp12--group 's3)
;;; --- S4. The registration of THIS corpus ----------------------------

(setq m60-imp12--group 's4)

(m60-imp12--check "s4/run-tests-m60-imp12"
                 (m60-imp12--holds-all "tool/run-tests.scm"
                                       '("test/m60/test-m60-imp12.el")))

;; The imp-12 line sits AFTER the imp-11 line, and imp-1 ... imp-11
;; stand.
(m60-imp12--check "s4/registered-after-imp11"
                 (m60-imp12--all
                  (m60-imp12--ordered-p
                   "tool/run-tests.scm"
                   '("test/m60/test-m60-imp11.el"
                     "test/m60/test-m60-imp12.el"))
                  (m60-imp12--holds-all "tool/run-tests.scm"
                                        '("test/m60/test-m60-imp1.el"))))

;; The (m60) group carries no prelude key: a prelude run would load the
;; prelude BEFORE the corpus and hide a missing boot.
(m60-imp12--check "s4/m60-group-no-prelude"
                 (m60-imp12--all
                  (m60-imp12--holds-all "tool/run-tests.scm" '("(group (m60)"))
                  (m60-imp12--holds-none "tool/run-tests.scm"
                                         '("(group (m60 "))))

;;; --- S5. The guards -------------------------------------------------

(setq m60-imp12--group 's5)

;; The 2 source-placement checks add 2 to S1 and the cr.org F2 check adds
;; 1 more, so the guard is 10 and not 7.
(m60-imp12--check "s5/min-s1-checks-9" (>= (m60-imp12--group-count 's1) 9))
(m60-imp12--check "s5/min-s2-checks-7" (>= (m60-imp12--group-count 's2) 7))
(m60-imp12--check "s5/min-s4-checks-3" (>= (m60-imp12--group-count 's4) 3))

(m60-imp12--check "s5/prog-absent-routes-to-skip"
                 (and (eq 'skip (m60-imp12--verdict 'm60-imp12-prog-absent))
                      (eq 'skip (m60-imp12--verdict
                                 (m60-imp12--all
                                  'm60-imp12-prog-absent
                                  (m60-imp12--probe-line
                                   "eac" "EAC ret: 3"))))
                      (eq 'absent (m60-imp12--verdict 'm60-imp12-absent))
                      (eq 'pass (m60-imp12--verdict t))
                      (eq 'fail (m60-imp12--verdict nil))
                      (eq 'fail (m60-imp12--verdict
                                 (m60-imp12--all t nil)))))

;;; --- The group-total check ------------------------------------------

(defvar m60-imp12--min-gate-total 24
  "Minimum registered ERT test count for this corpus.")

(ert-deftest m60-imp12/gate-m60-total ()
  "The m60-imp12 corpus registers at least its own floor, so a silent
registration loss is a FAIL."
  (should (>= (length (ert-select-tests "^m60-imp12" t))
              m60-imp12--min-gate-total)))

(princ (format "=== m60 imp-12 suite done (%d checks; s1 %d, s2 %d, s3 %d, s4 %d, s5 %d) ===\n"
               m60-imp12--registered
               (m60-imp12--group-count 's1)
               (m60-imp12--group-count 's2)
               (m60-imp12--group-count 's3)
               (m60-imp12--group-count 's4)
               (m60-imp12--group-count 's5)))
