;;; test-m60-imp8.el --- M60 imp-8 `make-obsolete-variable' corpus.
;;;
;;; M60 imp-8 lands row 27 of the row map of docs/m60-plan.org section 6:
;;; the `make-obsolete-variable' FUNCTION cell, so that
;;; lisp/obarray.el loads to the END in a plain `guile -L mod' process.
;;; The name is a Lisp function in lisp/emacs-lisp/byte-run.el :564, not
;;; a C DEFUN (`rg -c make-obsolete-variable src/' gives 0 hits), so the
;;; row takes the row-18 pattern of `provide': ONE guarded install site
;;; and 0 new evaluator branches.  C delta 0.
;;;
;;; The mark is DATA only, in the SOURCE order of byte-run.el :576:
;;; (CURRENT-NAME ACCESS-TYPE WHEN).  The 3-arity form passes #nil for
;;; ACCESS-TYPE, because (equal? #nil '()) is #f.  The procedure returns
;;; the SYMBOL; `elisp-put' returns the VALUE, so the return expression
;;; is written out.
;;;
;;; LIMITS, named in the source and NOT claimed here: L11 no
;;; `purecopy', L12 no warning channel, L13 no
;;; `byte-run--constant-obsolete-warning' and no `nil' / `t' guard, L14
;;; `(declare (obsolete ...))' stays in the BODY of `obarray-size' at
;;; lisp/obarray.el :35 -- the LOAD passes, a CALL would raise
;;; `void-function declare', L15 `EMPTY-CELLS' is a FIXED 11-name list
;;; and is NOT the proof of row 27.
;;;
;;; The probe runs as a plain `guile -L mod' child process with
;;; GUILE_AUTO_COMPILE=0 -- one MODE per child.  Mode `obsolete' is NEW
;;; here and it is named in the `cells|provide|...' list of the mode
;;; error message.  `elisp-loader-eval' is NOT in the #:export list of
;;; (emacs loader), so the fixture gets it with `module-ref'.
;;;
;;; It checks the observable behavior of M60 imp-8 and regression
;;; behavior in the existing plain-Guile probe modes. It does not inspect
;;; source text or enforce implementation shape.
;;;
;;; A missing `guile' binary is an explicit INFO skip, never a pass:
;;; `m60-imp8--check' routes the marker
;;; `m60-imp8-prog-absent' to `m60-imp8--info-skip', and `m60-imp8--all'
;;; carries that marker through a composite check.
;;;
;;; The checks compare values printed by the fixture.

(princ "=== m60 imp-8 make-obsolete-variable suite ===\n")

(require 'imp-ert-report)

(defvar m60-imp8--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))
(defvar m60-imp8--registered 0
  "Total number of checks this corpus has registered.")
(defvar m60-imp8--group nil
  "The group that `m60-imp8--check' counts into: `s3', `s4', `s7', or nil.")
(defvar m60-imp8--counts nil
  "Alist of (GROUP . COUNT) for the registered checks.")
(defvar m60-imp8--probe-cache nil
  "Alist of (MODE . RESULT) of the plain-guile probe runs of this corpus.
A mode is measured once per corpus run, so a group starts one child
process, not one per check.")

(defun m60-imp8--group-count (group)
  "Number of checks registered so far in GROUP."
  (or (cdr (assq group m60-imp8--counts)) 0))

(defun m60-imp8--bump-group ()
  "Count one check into `m60-imp8--group'."
  (when m60-imp8--group
    (let ((cell (assq m60-imp8--group m60-imp8--counts)))
      (if cell
          (setcdr cell (1+ (cdr cell)))
        (push (cons m60-imp8--group 1) m60-imp8--counts)))))

;;; --- the plain-guile probe runner -----------------------------------

(defun m60-imp8--probe-1 (mode)
  "Run test/m60/probe-imp3.scm in MODE as a `guile -L mod' child
process, with GUILE_AUTO_COMPILE=0 and GUILEMACS_ROOT set, and with
`default-directory' at the repo root.  Return (EXIT . OUTPUT), where
OUTPUT holds stdout AND stderr, or the symbol `m60-imp8-prog-absent'
when the `guile' binary is not on PATH."
  (if (not (executable-find "guile"))
      'm60-imp8-prog-absent
    (let ((buf (get-buffer-create " *m60-imp8-probe*"))
          (default-directory m60-imp8--root)
          (process-environment
           (append (list (concat "GUILEMACS_ROOT=" m60-imp8--root)
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

(defun m60-imp8--probe (mode)
  "The cached result of `m60-imp8--probe-1' for MODE."
  (let ((cell (assoc mode m60-imp8--probe-cache)))
    (if cell
        (cdr cell)
      (let ((result (m60-imp8--probe-1 mode)))
        (push (cons mode result) m60-imp8--probe-cache)
        result))))

(defun m60-imp8--probe-output (mode)
  "The OUTPUT of the probe MODE when the child exited 0, else nil.  When
the `guile' binary is absent, the marker `m60-imp8-prog-absent' is
returned instead of nil, so the caller can SKIP and not pass or fail."
  (let ((result (m60-imp8--probe mode)))
    (cond
     ((eq result 'm60-imp8-prog-absent) result)
     ((and (consp result) (eql 0 (car result))) (cdr result))
     (t nil))))

(defun m60-imp8--probe-line (mode line)
  "Non-nil when the probe MODE printed LINE as one WHOLE line and the
child exited 0.  A substring match is NOT enough: a line pin holds the
whole line, so a changed value can not hide inside it."
  (let ((out (m60-imp8--probe-output mode)))
    (cond
     ((eq out 'm60-imp8-prog-absent) out)
     ((not (stringp out)) nil)
     (t (with-temp-buffer
          (insert "\n" out "\n")
          (goto-char (point-min))
          (and (search-forward (concat "\n" line "\n") nil t) t))))))

(defun m60-imp8--probe-holds (mode needle)
  "Non-nil when the OUTPUT of the probe MODE holds NEEDLE (a substring
pin; use it only where an address sits in the text)."
  (let ((out (m60-imp8--probe-output mode)))
    (cond
     ((eq out 'm60-imp8-prog-absent) out)
     ((not (stringp out)) nil)
     (t (with-temp-buffer
          (insert out)
          (goto-char (point-min))
          (and (search-forward needle nil t) t))))))

(defun m60-imp8--probe-holds-none (mode needle)
  "Non-nil when the OUTPUT of the probe MODE holds NO NEEDLE."
  (let ((out (m60-imp8--probe-output mode)))
    (cond
     ((eq out 'm60-imp8-prog-absent) out)
     ((not (stringp out)) nil)
     (t (with-temp-buffer
          (insert out)
          (goto-char (point-min))
          (not (search-forward needle nil t)))))))

(defun m60-imp8--all (&rest values)
  "`and' over ALREADY-EVALUATED VALUES, preserving a missing-guile marker."
  (cond
   ((memq 'm60-imp8-prog-absent values) 'm60-imp8-prog-absent)
   ((memq nil values) nil)
   (t t)))

;;; --- report helpers -------------------------------------------------

(defun m60-imp8--verdict (ok)
  "Classify check value OK as `pass', `fail', or `skip'."
  (cond
   ((eq ok 'm60-imp8-prog-absent) 'skip)
   (ok 'pass)
   (t 'fail)))

(defun m60-imp8--check (name ok)
  "Report and register one check; a missing `guile' binary is a skip."
  (let ((verdict (m60-imp8--verdict ok)))
    (cond
     ((eq verdict 'skip)
      (m60-imp8--info-skip name "no guile binary on PATH"))
     (t
      (princ (format "%s m60/imp8/%s\n"
                     (if (eq verdict 'pass) "PASS" "FAIL") name))
      (setq m60-imp8--registered (1+ m60-imp8--registered))
      (m60-imp8--bump-group)
      (imp-register-bool-as-ert-test (format "m60-imp8/%s" name)
                                     (eq verdict 'pass))))))

(defun m60-imp8--info-skip (name reason)
  "Register one explicit INFO skip, counted into the current group.  A
host limit is a skip, never a pass."
  (princ (format "INFO m60/imp8/%s %s\n" name reason))
  (setq m60-imp8--registered (1+ m60-imp8--registered))
  (m60-imp8--bump-group)
  (imp-register-skip-as-ert-test (format "m60-imp8/%s" name) reason))

;;; --- S3. The observables (modes `obsolete' and `cells') -------------

(setq m60-imp8--group 's3)

;; The 5 observations of brief.org section 5.  Mode `obsolete' prints
;; the 2 observables that mode `cells' does not: the RETURN value and
;; the MARK.
(m60-imp8--check "s3/obarray-loads-to-the-end"
                 (m60-imp8--all
                  (m60-imp8--probe-line "obsolete"
                                        "LOAD lisp/obarray.el: done")
                  (m60-imp8--probe-line "cells"
                                        "LOAD lisp/obarray.el: done")))

(m60-imp8--check "s3/return-value-is-the-symbol"
                 (m60-imp8--all
                  (m60-imp8--probe-line "obsolete"
                                        "RETURN: obarray-default-size")
                  (m60-imp8--probe-holds-none "obsolete" "RETURN: (")))

;; The exact 3-element mark, in the SOURCE order.  Field 2 is #nil,
;; because lisp/obarray.el :31 calls the 3-arity form.
(m60-imp8--check "s3/mark-in-source-order"
                 (m60-imp8--probe-line
                  "obsolete"
                  (concat "MARK: (\"obarrays now grow automatically.\""
                          " #nil \"30.1\")")))

;; EMPTY-CELLS is NOT the proof of this row (L15): the probe builds it
;; from a FIXED 11-name list that does not hold `make-obsolete-variable'.
;; The line is pinned as a NO-REGRESSION value only.
(m60-imp8--check "s3/empty-cells-unchanged"
                 (m60-imp8--all
                  (m60-imp8--probe-line "cells" "EMPTY-CELLS: ()")
                  (m60-imp8--probe-line "cells"
                                        "ASYM: require=#t provide=#t")
                  (m60-imp8--probe-line "cells" "FEATURES-BOUND: #t")))

;;; --- S4. No regression on the older probe modes ---------------------

(setq m60-imp8--group 's4)

(m60-imp8--check "s4/cells-unchanged"
                 (m60-imp8--all
                  (m60-imp8--probe-line
                   "cells" "UNGUARDED: load=#t autoload-do-load=#t")
                  (m60-imp8--probe-line "cells" "LOAD lisp/cdl.el: done")
                  (m60-imp8--probe-line "cells" "features: (cdl)")
                  (m60-imp8--probe-line "cells" "LOAD lisp/hex-util.el: done")))

;; The stub chain of mode `stubs': the real cell now answers, so the
;; obarray step is `done' (it was `ERROR void-function
;; (make-obsolete-variable)').  The stub STAYS in the fixture, because
;; that mode records the chain.
(m60-imp8--check "s4/stubs-blockers"
                 (m60-imp8--all
                  (m60-imp8--probe-line "stubs" "stub-provide / cdl: done")
                  (m60-imp8--probe-line "stubs" "stub-defconst / obarray: done")
                  (m60-imp8--probe-line "stubs"
                                        "stub-eval-when-compile / hex-util: done")
                  (m60-imp8--probe-line "stubs" "stub-ntl / subdirs: done")))

(m60-imp8--check "s4/provide-and-require-unchanged"
                 (m60-imp8--all
                  (m60-imp8--probe-line "provide" "LOAD cdl: done")
                  (m60-imp8--probe-line "provide" "require-fbound: #t")
                  (m60-imp8--probe-line "require" "REQUIRE cdl: cdl")
                  (m60-imp8--probe-line "require" "REQUIRE-NOERROR: #nil")))

;; The negative control and the no-boot control still stop before
;; `provide' runs.  The address changes per run, so the pin holds WORDS.
(m60-imp8--check "s4/controls-unchanged"
                 (m60-imp8--all
                  (m60-imp8--probe-line "negative" "features-bound: #f")
                  (m60-imp8--probe-holds "negative" "LOAD cdl: ERROR wrong-type-arg")
                  (m60-imp8--probe-holds-none "negative" "void-function")
                  (m60-imp8--probe-line "noboot" "features-bound: #f")
                  (m60-imp8--probe-holds "noboot" "Wrong type to apply")))

(m60-imp8--check "s4/defs-macros-and-language-unchanged"
                 (m60-imp8--all
                  (m60-imp8--probe-line "defs" "defconst value: 2")
                  (m60-imp8--probe-line "defs" "defvar no-init bound: #f")
                  (m60-imp8--probe-line "macros" "defmacro fbound: #f")
                  (m60-imp8--probe-line "macros"
                                        "eval-when-compile form1 ret: num-to-hex-char")
                  (m60-imp8--probe-line "language" "LANGUAGE-NAME: emacs-elisp")))

;;; --- S7. The guards -------------------------------------------------

(setq m60-imp8--group 's7)

(m60-imp8--check "s7/min-s3-checks-4" (>= (m60-imp8--group-count 's3) 4))
(m60-imp8--check "s7/min-s4-checks-5" (>= (m60-imp8--group-count 's4) 5))

(m60-imp8--check "s7/prog-absent-routes-to-skip"
                 (and (eq 'skip (m60-imp8--verdict 'm60-imp8-prog-absent))
                      (eq 'skip (m60-imp8--verdict
                                 (m60-imp8--all
                                  'm60-imp8-prog-absent
                                  (m60-imp8--probe-line
                                   "obsolete" "RETURN: obarray-default-size"))))
                      (eq 'pass (m60-imp8--verdict t))
                      (eq 'fail (m60-imp8--verdict nil))
                      (eq 'fail (m60-imp8--verdict (m60-imp8--all t nil)))))

;;; --- The group-total check ------------------------------------------

;; 12 registered checks (S3 4, S4 5, S7 3) plus this deftest = 13 ERT tests.

(defvar m60-imp8--min-gate-total 13
  "The m60-imp8 ERT floor: 12 registered checks plus the group-total test.")

(ert-deftest m60-imp8/gate-m60-total ()
  "The m60-imp8 corpus registers at least its docs-independent floor."
  (should (>= (length (ert-select-tests "^m60-imp8" t))
              m60-imp8--min-gate-total)))

(princ (format "=== m60 imp-8 suite done (%d checks; s3 %d, s4 %d, s7 %d) ===\n"
               m60-imp8--registered
               (m60-imp8--group-count 's3)
               (m60-imp8--group-count 's4)
               (m60-imp8--group-count 's7)))
