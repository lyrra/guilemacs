;;; test-m60-imp11.el --- M60 imp-11 `put' function cell corpus.
;;;
;;; M60 imp-11 lands row 30 of the row map of docs/m60-plan.org section
;;; 6: the function cell of `put'.  MEASURED 2026-10-22 with mode `put'
;;; of test/m60/probe-imp3.scm: the cell is EMPTY in a plain
;;; `guile -L mod' process, and `lisp/calendar/time-date.el' stops at
;;; `void-function (put)'.
;;;
;;; WHY `put' and not `get': `put' is the FIRST stop of a real file.
;;; `lisp/calendar/time-date.el' itself calls no `put' (measured: no
;;; match for `(put ').  The caller is lisp/emacs-lisp/macroexp.el :137,
;;;
;;;   (put 'macroexp--funcall-if-compiled 'byte-compile (lambda ...))
;;;
;;; reached through `(require 'cl-lib)' at time-date.el :39, because
;;; cl-lib.el :87 does `(require 'macroexp)'.  The stop is 2 requires
;;; below time-date.el, so it is RECORDED here and not guessed.
;;;
;;; The work is 1 GUARDED install and NO new procedure and NO import:
;;; `elisp-put' already exists (mod/emacs/utils.scm :164), it is exported
;;; at :24, and loader.scm imports (emacs utils) as a WHOLE module at
;;; :20.
;;;
;;; The guard is the row-18 pattern `(unless (symbol-fbound? 'put)
;;; (set-symbol-function! 'put elisp-put))': a full Emacs already owns
;;; the C DEFUN (src/fns.c, Fput) in that cell, so an UNGUARDED install
;;; would replace the C cell for EVERY elisp caller.
;;;
;;; The bulk installer `init-utils-registrations' (utils.scm :594) also
;;; writes `put' at :606, but with NO guard, and `init-loader' does not
;;; call it.  This row names that installer (the F3 class) and does not
;;; call it.
;;;
;;; LIMITS, named in the source and NOT claimed here:
;;;   L15 `EMPTY-CELLS' is a FIXED 11-name list, so it does not hold
;;;       `put'.  It is NOT the proof of row 30; the proof is the
;;;       `CELLS' line of mode `put'.
;;;   L26 (CLOSED by row 32) the NEXT stop after row 30 was
;;;       `make-hash-table' (lisp/emacs-lisp/macroexp.el :165).
;;;       M60 imp-15: row 32 wrote the family and installed its 14 cells,
;;;       so the stop MOVED.  The check `s1/next-stop-named' and the 2
;;;       observable pins name the NEXT wall,
;;;       `void-function (define-obsolete-function-alias)'.
;;;   A `put' on a STRING or a NUMBER first argument raises `Wrong type
;;;       argument: symbolp'.  That is elisp behaviour, so it is pinned
;;;       as CORRECT.
;;;   Row 30 moves 1 cell.  The load stops at the NEXT empty cell of the
;;;       same require chain; this row records it and does not fix it.
;;;
;;; This corpus reads TRACKED files only and does NOT read docs/.  A read
;;; error is a real error, never a silent pass.  An absent TRACKED file
;;; is a real FAIL.  A missing `guile' binary is an explicit INFO skip,
;;; never a pass.
;;;
;;; Groups: S1 the install source, S2 the observables of the live
;;; `guile' child (mode `put') plus no regression on the 12 older modes,
;;; S3 the re-measured surface, S4 this registration, S5 the guards.

(princ "=== m60 imp-11 `put' cell suite ===\n")

(require 'imp-ert-report)

(defvar m60-imp11--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))
(defvar m60-imp11--registered 0
  "Total number of checks this corpus has registered.")
(defvar m60-imp11--group nil
  "The group that `m60-imp11--check' counts into: `s1' .. `s5', or nil.")
(defvar m60-imp11--counts nil
  "Alist of (GROUP . COUNT) for the registered checks.")
(defvar m60-imp11--probe-cache nil
  "Alist of (MODE . RESULT) of the plain-guile probe runs of this corpus.")

(defun m60-imp11--group-count (group)
  "Number of checks registered so far in GROUP."
  (or (cdr (assq group m60-imp11--counts)) 0))

(defun m60-imp11--bump-group ()
  "Count one check into `m60-imp11--group'."
  (when m60-imp11--group
    (let ((cell (assq m60-imp11--group m60-imp11--counts)))
      (if cell
          (setcdr cell (1+ (cdr cell)))
        (push (cons m60-imp11--group 1) m60-imp11--counts)))))

;;; --- tracked-file helpers (the imp-1 / imp-6 / imp-9 idioms) --------

(defun m60-imp11--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
the symbol `m60-imp11-absent' when REL does not exist."
  (let ((path (expand-file-name rel m60-imp11--root)))
    (if (not (file-exists-p path))
        'm60-imp11-absent
      (with-temp-buffer
        (insert-file-contents path)
        (let ((case-fold-search nil))
          (funcall fn))))))

(defun m60-imp11--holds-all (rel needles)
  "Non-nil when the TRACKED file REL holds every NEEDLE."
  (m60-imp11--with rel
    (lambda ()
      (let ((all t))
        (dolist (needle needles)
          (goto-char (point-min))
          (unless (search-forward needle nil t) (setq all nil)))
        all))))

(defun m60-imp11--holds-none (rel needles)
  "Non-nil when the TRACKED file REL holds NO needle of NEEDLES."
  (m60-imp11--with rel
    (lambda ()
      (let ((none t))
        (dolist (needle needles)
          (goto-char (point-min))
          (when (search-forward needle nil t) (setq none nil)))
        none))))

(defun m60-imp11--literal-lines (rel needle)
  "Count the LINES of REL that hold NEEDLE as a LITERAL substring.  Use
this helper and not a regexp search where NEEDLE holds a metacharacter:
`+', `*', `?', `=' and `/' are operators of the search syntax."
  (m60-imp11--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (not (eobp))
          (when (search-forward needle (line-end-position) t)
            (setq n (1+ n)))
          (forward-line 1))
        n))))

(defun m60-imp11--lines (rel)
  "Count the NEWLINES of REL, the unit of `wc -l'."
  (m60-imp11--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (search-forward "\n" nil t) (setq n (1+ n)))
        n))))

(defun m60-imp11--grep-c (rel regexp)
  "Count the LINES of REL that match REGEXP, the unit of `grep -c'."
  (m60-imp11--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (not (eobp))
          (when (re-search-forward regexp (line-end-position) t)
            (setq n (1+ n)))
          (forward-line 1))
        n))))

(defun m60-imp11--ordered-p (rel needles)
  "Non-nil when the TRACKED file REL holds every NEEDLE in the GIVEN
ORDER."
  (m60-imp11--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((all t))
        (dolist (needle needles)
          (when all
            (unless (search-forward needle nil t) (setq all nil))))
        all))))

;;; --- the plain-guile probe runner -----------------------------------

(defun m60-imp11--probe-1 (mode)
  "Run test/m60/probe-imp3.scm in MODE as a `guile -L mod' child, with
GUILE_AUTO_COMPILE=0 and GUILEMACS_ROOT set.  Return (EXIT . OUTPUT) or
the symbol `m60-imp11-prog-absent'."
  (if (not (executable-find "guile"))
      'm60-imp11-prog-absent
    (let ((buf (get-buffer-create " *m60-imp11-probe*"))
          (default-directory m60-imp11--root)
          (process-environment
           (append (list (concat "GUILEMACS_ROOT=" m60-imp11--root)
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

(defun m60-imp11--probe (mode)
  "The cached result of `m60-imp11--probe-1' for MODE."
  (let ((cell (assoc mode m60-imp11--probe-cache)))
    (if cell
        (cdr cell)
      (let ((result (m60-imp11--probe-1 mode)))
        (push (cons mode result) m60-imp11--probe-cache)
        result))))

(defun m60-imp11--probe-output (mode)
  "The OUTPUT of the probe MODE when the child exited 0, else nil.  A
missing `guile' binary returns the marker `m60-imp11-prog-absent', so
the caller can SKIP and not pass or fail."
  (let ((result (m60-imp11--probe mode)))
    (cond
     ((eq result 'm60-imp11-prog-absent) result)
     ((and (consp result) (eql 0 (car result))) (cdr result))
     (t nil))))

(defun m60-imp11--probe-line (mode line)
  "Non-nil when the probe MODE printed LINE as one WHOLE line and the
child exited 0."
  (let ((out (m60-imp11--probe-output mode)))
    (cond
     ((eq out 'm60-imp11-prog-absent) out)
     ((not (stringp out)) nil)
     (t (with-temp-buffer
          (insert "\n" out "\n")
          (goto-char (point-min))
          (and (search-forward (concat "\n" line "\n") nil t) t))))))

(defun m60-imp11--all (&rest values)
  "`and' over the ALREADY-EVALUATED VALUES, where a MARKER wins over a
nil: the absent FILE marker first (a real FAIL), then the absent `guile'
marker (a skip)."
  (cond
   ((memq 'm60-imp11-absent values) 'm60-imp11-absent)
   ((memq 'm60-imp11-prog-absent values) 'm60-imp11-prog-absent)
   ((memq nil values) nil)
   (t t)))

(defun m60-imp11--verdict (ok)
  "Classify the value OK of one check: `pass', `fail', `absent' (a
TRACKED file is missing) or `skip' (no `guile' binary)."
  (cond
   ((eq ok 'm60-imp11-prog-absent) 'skip)
   ((eq ok 'm60-imp11-absent) 'absent)
   (ok 'pass)
   (t 'fail)))

(defun m60-imp11--check (name ok)
  "Report and register one check.  An absent `guile' binary registers a
controlled ERT skip -- never a pass."
  (let ((verdict (m60-imp11--verdict ok)))
    (cond
     ((eq verdict 'skip)
      (princ (format "INFO m60/imp11/%s no guile binary on PATH\n" name))
      (setq m60-imp11--registered (1+ m60-imp11--registered))
      (m60-imp11--bump-group)
      (imp-register-skip-as-ert-test (format "m60-imp11/%s" name)
                                     "no guile binary on PATH"))
     ((eq verdict 'absent)
      (princ (format "FAIL m60/imp11/%s (source file absent)\n" name))
      (setq m60-imp11--registered (1+ m60-imp11--registered))
      (m60-imp11--bump-group)
      (imp-register-bool-as-ert-test (format "m60-imp11/%s" name) nil))
     (t
      (princ (format "%s m60/imp11/%s\n"
                     (if (eq verdict 'pass) "PASS" "FAIL") name))
      (setq m60-imp11--registered (1+ m60-imp11--registered))
      (m60-imp11--bump-group)
      (imp-register-bool-as-ert-test (format "m60-imp11/%s" name)
                                     (eq verdict 'pass))))))

;;; --- S1. The install source -----------------------------------------

(setq m60-imp11--group 's1)

;; Exactly 1 guarded install, and no 2nd site: the cell is written once,
;; in the guarded block of `init-loader'.
(m60-imp11--check "s1/one-guarded-install"
                 (m60-imp11--all
                  (eql 1 (m60-imp11--literal-lines
                          "mod/emacs/loader.scm"
                          "(unless (symbol-fbound? 'put)"))
                  (eql 1 (m60-imp11--literal-lines
                          "mod/emacs/loader.scm"
                          "(set-symbol-function! 'put elisp-put)"))))

;; The guard is the row-18 pattern, so a full Emacs keeps its C cell.
(m60-imp11--check "s1/row-18-guard"
                 (m60-imp11--ordered-p
                  "mod/emacs/loader.scm"
                  '("(unless (symbol-fbound? 'put)"
                    "(set-symbol-function! 'put elisp-put)")))

;; The install is the LAST form of the guarded block: it comes AFTER the
;; `nreverse' install of row 29 and BEFORE the closing paren of
;; `init-loader'.
(m60-imp11--check "s1/install-order"
                 (m60-imp11--ordered-p
                  "mod/emacs/loader.scm"
                  '("(set-symbol-function! 'nreverse elisp-nreverse)"
                    "(unless (symbol-fbound? 'put)"
                    "(set-symbol-function! 'put elisp-put)")))

;; The procedure already exists and is exported, so this row writes no
;; procedure and adds no import.  A missing export would make the install
;; unbound, so pin the export.
(m60-imp11--check "s1/definition-and-export"
                 (m60-imp11--all
                  (m60-imp11--holds-all
                   "mod/emacs/utils.scm"
                   '("(define (elisp-put symbol propname value)"
                     "elisp-get elisp-put elisp-symbol-plist elisp-setplist"))
                  (m60-imp11--holds-all
                   "mod/emacs/loader.scm"
                   '("#:use-module (emacs utils)"))))

;; The bulk installer stays UNCALLED: it installs with no guard.
(m60-imp11--check "s1/no-bulk-installer"
                 (m60-imp11--holds-none
                  "mod/emacs/loader.scm"
                  '("(init-utils-registrations)")))

;; The require chain of the recorded stop is in the source comment, so a
;; later reader does not have to re-measure it.
(m60-imp11--check "s1/require-chain-recorded"
                 (m60-imp11--all
                  (m60-imp11--holds-all
                   "mod/emacs/loader.scm"
                   '("lisp/emacs-lisp/macroexp.el :137"
                     "cl-lib.el :87 requires macroexp"))))

;; The NEXT stop and its named blocker are in the source comment.
;; M60 imp-15 RE-PIN: L26 (`make-hash-table') is CLOSED by row 32, so
;; this check now names the wall that row 32 exposes, and the old pin
;; named the exported-but-empty trap.
(m60-imp11--check "s1/next-stop-named"
                 (m60-imp11--all
                  (m60-imp11--holds-all
                   "mod/emacs/loader.scm"
                   '("lisp/emacs-lisp/macroexp.el :165"
                     "void-function (define-obsolete-function-alias)"))))

;;; --- S2. The observables (live `guile' child, mode `put') -----------

(setq m60-imp11--group 's2)

;; The CELLS line is the proof of row 30: `put' is BOUND, and the 2
;; neighbour cells are still EMPTY.  `get' and `featurep' belong to F3
;; and `make-hash-table' to L26, so this row does NOT bind them.
(m60-imp11--check "s2/cell-bound"
                 (m60-imp11--probe-line
                  "put"
                  ;; M60 imp-15 RE-PIN: row 32 installs the
                  ;; `make-hash-table' family, so this wall MOVED.
                  "CELLS: put -> #t get -> #f make-hash-table -> #t"))

;; The installed cell stores a property and RETURNS the VALUE, not the
;; plist, and `get' reads the same property back.
(m60-imp11--check "s2/property-and-return"
                 (m60-imp11--all
                  (m60-imp11--probe-line "put" "CALL put symbol-property: 42")
                  (m60-imp11--probe-line "put" "CALL get after put: 42")))

;; The elisp nil value is `#nil', not `#f', and 2 properties on 1 symbol
;; are both kept.
(m60-imp11--check "s2/nil-value-and-two-properties"
                 (m60-imp11--all
                  (m60-imp11--probe-line "put" "CALL put nil value: #nil")
                  (m60-imp11--probe-line "put" "CALL get nil value: #nil")
                  (m60-imp11--probe-line "put" "CALL 2 properties: 42 second")))

;; A non-symbol first argument raises `symbolp'.  That is elisp
;; behaviour, so it is pinned as CORRECT, not as a defect.
(m60-imp11--check "s2/symbolp-error"
                 (m60-imp11--all
                  (m60-imp11--probe-line
                   "put"
                   "CALL string first arg: ERROR misc-error Wrong type argument: symbolp \"m60-probe-str\"")
                  (m60-imp11--probe-line
                   "put"
                   "CALL number first arg: ERROR misc-error Wrong type argument: symbolp 7")))

;; The 3 recorded FIRST STOPS after this row: color.el is done,
;; time-date.el moves PAST `put' to the next empty cell, and the subr.el
;; stop MOVED at row 31 (M60 imp-12) to the next wall, `defalias'.
(m60-imp11--check "s2/recorded-first-stops"
                 (m60-imp11--all
                  (m60-imp11--probe-line "put" "LOAD lisp/color.el: done")
                  ;; M60 imp-13 RE-PIN: the OLD line was
                  ;; `LOAD lisp/calendar/time-date.el: ERROR wrong-type-arg
                  ;; (#f "Wrong type to apply: ~S" (#nil) (#nil))'.  Row 33
                  ;; installs the `set' cell, so the load moves to the NEXT
                  ;; wall, `make-hash-table' (row 32, macroexp.el
                  ;; :165); row 32 CLOSED that stop.
                  (m60-imp11--probe-line
                   "put"
                  ;; M60 imp-15 RE-PIN: row 32 installs the
                  ;; `make-hash-table' family, so this wall MOVED.
                   "LOAD lisp/calendar/time-date.el: ERROR void-function (define-obsolete-function-alias)")
                  (m60-imp11--probe-line
                   "put"
                   ;; M60 imp-12 RE-PIN: the OLD line was
                   ;; `LOAD lisp/subr.el: ERROR void-function (eval-and-compile)'.
                   ;; Row 31 adds the branch, so the load moves PAST form 1 to the
                   ;; NEXT wall, `defalias' at subr.el :29.  `subr.el' does NOT
                   ;; load: a `done' value is a FAIL.
                   "LOAD lisp/subr.el: ERROR void-function (defsubst)")))

;; No regression: the older modes still run.  Mode `arith' keeps
;; `COUNT: 0' (row 29), mode `cells' keeps the FIXED 11-name list, and
;; the F3 stop of mode `arith' is unchanged.  The row-31 stop of modes
;; `arith', `control' and `put' MOVED at M60 imp-12.
(m60-imp11--check "s2/no-regression-on-older-modes"
                 (m60-imp11--all
                  (m60-imp11--probe-line "arith" "COUNT: 0")
                  (m60-imp11--probe-line "arith" "EMPTY-CELLS: ()")
                  (m60-imp11--probe-line "cells" "EMPTY-CELLS: ()")
                  (m60-imp11--probe-line "control" "cond empty: #nil")
                  (m60-imp11--probe-line "defs" "defconst value: 2")
                  (m60-imp11--probe-line "obsolete" "LOAD lisp/obarray.el: done")))

;;; --- S3. The re-measured surface ------------------------------------

(setq m60-imp11--group 's3)


;;; --- S4. The registration of THIS corpus ----------------------------

(setq m60-imp11--group 's4)

(m60-imp11--check "s4/run-tests-m60-imp11"
                 (m60-imp11--holds-all "tool/run-tests.scm"
                                       '("test/m60/test-m60-imp11.el")))

;; The imp-11 line sits AFTER the imp-10 line, and imp-1 ... imp-10 stand.
(m60-imp11--check "s4/registered-after-imp10"
                 (m60-imp11--all
                  (m60-imp11--ordered-p
                   "tool/run-tests.scm"
                   '("test/m60/test-m60-imp10.el"
                     "test/m60/test-m60-imp11.el"))
                  (m60-imp11--holds-all "tool/run-tests.scm"
                                        '("test/m60/test-m60-imp1.el"))))

;; The (m60) group carries no prelude key: a prelude run would load the
;; prelude BEFORE the corpus and hide a missing boot.
(m60-imp11--check "s4/m60-group-no-prelude"
                 (m60-imp11--all
                  (m60-imp11--holds-all "tool/run-tests.scm" '("(group (m60)"))
                  (m60-imp11--holds-none "tool/run-tests.scm"
                                         '("(group (m60 "))))

;;; --- S5. The guards -------------------------------------------------

(setq m60-imp11--group 's5)

(m60-imp11--check "s5/min-s1-checks-7" (>= (m60-imp11--group-count 's1) 7))
(m60-imp11--check "s5/min-s2-checks-6" (>= (m60-imp11--group-count 's2) 6))
(m60-imp11--check "s5/min-s4-checks-3" (>= (m60-imp11--group-count 's4) 3))

(m60-imp11--check "s5/prog-absent-routes-to-skip"
                 (and (eq 'skip (m60-imp11--verdict 'm60-imp11-prog-absent))
                      (eq 'skip (m60-imp11--verdict
                                 (m60-imp11--all
                                  'm60-imp11-prog-absent
                  ;; M60 imp-15 RE-PIN: row 32 installs the
                  ;; `make-hash-table' family, so this wall MOVED.
                                  (m60-imp11--probe-line "put" "CELLS: put -> #t get -> #f make-hash-table -> #t"))))
                      (eq 'absent (m60-imp11--verdict 'm60-imp11-absent))
                      (eq 'pass (m60-imp11--verdict t))
                      (eq 'fail (m60-imp11--verdict nil))
                      (eq 'fail (m60-imp11--verdict
                                 (m60-imp11--all t nil)))))

;;; --- The group-total check ------------------------------------------

(defvar m60-imp11--min-gate-total 21
  "Minimum registered ERT test count for this corpus.")

(ert-deftest m60-imp11/gate-m60-total ()
  "The m60-imp11 corpus registers at least its own floor, so a silent
registration loss is a FAIL."
  (should (>= (length (ert-select-tests "^m60-imp11" t))
              m60-imp11--min-gate-total)))

(princ (format "=== m60 imp-11 suite done (%d checks; s1 %d, s2 %d, s3 %d, s4 %d, s5 %d) ===\n"
               m60-imp11--registered
               (m60-imp11--group-count 's1)
               (m60-imp11--group-count 's2)
               (m60-imp11--group-count 's3)
               (m60-imp11--group-count 's4)
               (m60-imp11--group-count 's5)))
