;;; test-m60-imp4.el --- M60 imp-4 PROVIDE CELL AND FEATURES BIND corpus.
;;;
;;; M60 imp-4 lands rows 18 (`provide') and 19 (`features') of the row
;;; map of docs/m60-plan.org section 6.  Both cells get ONE home,
;;; `init-loader' (mod/emacs/loader.scm), and the 2 old homes are
;;; deleted in the same commit: the bare `features' bind of
;;; prelude/load.scm:227 and the `provide' install of
;;; `init-utils-registrations' (mod/emacs/utils.scm:576).
;;;
;;; Reach: a plain `guile -L mod' process never loads the prelude, it
;;; calls `init-loader' only.  A full Emacs calls `init-loader' before
;;; the prelude.  So `init-loader' is the home that both paths run, and
;;; each cell is installed only when it is EMPTY: `symbol-bound?' for
;;; the variable, `symbol-fbound?' for the function cell.  A full Emacs
;;; therefore keeps the C DEFUN (src/fns.c:3450) and the C DEFVAR_LISP
;;; (src/fns.c:6372).
;;;
;;; The (m60) group has NO prelude key, so this corpus runs INSIDE the
;;; built src/emacs.  Every plain-guile value is measured by
;;; test/m60/probe-imp3.scm as a `guile -L mod' child process with
;;; GUILE_AUTO_COMPILE=0 -- the real plain-guile path, one MODE per
;;; child, so a stub of one mode can not hide the next result.
;;;
;;; It pins these groups:
;;;
;;;   S1 -- the 2 new forms of `init-loader': the guard of each form
;;;         (`symbol-bound?' / `symbol-fbound?'), their ORDER after the
;;;         `%load-path' append, and the FIX marker of the bind.
;;;   S2 -- ONE home: 0 `set-symbol-value! 'features' sites in
;;;         prelude/load.scm, 0 `set-symbol-function! 'provide' sites
;;;         in utils.scm, 1 of each in loader.scm.
;;;   S3 -- the acceptance observable through a live `guile' child, from
;;;         mode `cells' (which never installs the 2 cells):
;;;         `LOAD cdl: done', `featurep cdl: #t', `features: (cdl)',
;;;         and the asymmetry `require=#f provide=#t'.
;;;   S4 -- the negative control: `provide' installed, `features'
;;;         UNBOUND, and the load still raises `wrong-type-arg' on the
;;;         unbound sentinel (the 2 pinned words, not the address); plus
;;;         mode `noboot', the record of why the control keeps the boot.
;;;   S5 -- the re-measured surface: the 3 LINE counts and the 3
;;;         loader.scm `grep -c' counts.
;;;   S6 -- the registration: the imp-4 line AFTER the imp-3 line,
;;;         imp-1 ... imp-3 kept, (m60) with no prelude key.
;;;   S7 -- the guards: the per-group min counts, the marker-routing
;;;         self-check of the skip path, and the group-total deftest.
;;;
;;; This corpus reads TRACKED files only.  It does NOT read docs/.
;;; A read error is a real error, never a silent pass.  An absent
;;; TRACKED file is a real FAIL.  A missing `guile' binary is an explicit
;;; INFO skip, never a pass: `m60-imp4--check' routes the marker
;;; `m60-imp4-prog-absent' to `m60-imp4--info-skip', and `m60-imp4--all'
;;; carries that marker through a composite check.
;;;
;;; Every value below was MEASURED on this host on 2026-10-20 by running
;;; the fixture and the commands named in the comment of each check.
;;; MEASURED total: 29 registered checks (S1 4, S2 3, S3 4, S4 4, S5 4,
;;; S6 3, S7 7) plus the group-total deftest = 30 ERT tests.

(princ "=== m60 imp-4 provide-cell and features-bind suite ===\n")

(require 'imp-ert-report)

(defvar m60-imp4--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))
(defvar m60-imp4--registered 0
  "Total number of checks this corpus has registered.")
(defvar m60-imp4--group nil
  "The group that `m60-imp4--check' counts into: `s1' .. `s7', or nil.")
(defvar m60-imp4--counts nil
  "Alist of (GROUP . COUNT) for the registered checks.")
(defvar m60-imp4--probe-cache nil
  "Alist of (MODE . RESULT) of the plain-guile probe runs of this corpus.
A mode is measured once per corpus run, so a group starts one child
process, not one per check.")

(defun m60-imp4--group-count (group)
  "Number of checks registered so far in GROUP."
  (or (cdr (assq group m60-imp4--counts)) 0))

(defun m60-imp4--bump-group ()
  "Count one check into `m60-imp4--group'."
  (when m60-imp4--group
    (let ((cell (assq m60-imp4--group m60-imp4--counts)))
      (if cell
          (setcdr cell (1+ (cdr cell)))
        (push (cons m60-imp4--group 1) m60-imp4--counts)))))

;;; --- tracked-file helpers (the imp-1 idioms) -------------------------

(defun m60-imp4--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
the symbol `m60-imp4-absent' when REL does not exist.  `case-fold-search'
is bound to nil: the elisp default folds case and inflates a count."
  (let ((path (expand-file-name rel m60-imp4--root)))
    (if (not (file-exists-p path))
        'm60-imp4-absent
      (with-temp-buffer
        (insert-file-contents path)
        (let ((case-fold-search nil))
          (funcall fn))))))

(defun m60-imp4--holds-all (rel needles)
  "Non-nil when the TRACKED file REL holds every NEEDLE.  An absent file
fails the check."
  (m60-imp4--with rel
    (lambda ()
      (let ((all t))
        (dolist (needle needles)
          (goto-char (point-min))
          (unless (search-forward needle nil t) (setq all nil)))
        all))))

(defun m60-imp4--holds-none (rel needles)
  "Non-nil when the TRACKED file REL holds NO needle of NEEDLES."
  (m60-imp4--with rel
    (lambda ()
      (let ((none t))
        (dolist (needle needles)
          (goto-char (point-min))
          (when (search-forward needle nil t) (setq none nil)))
        none))))

(defun m60-imp4--ordered-p (rel needles)
  "Non-nil when the TRACKED file REL holds every NEEDLE in the GIVEN
ORDER: each search starts after the previous match."
  (m60-imp4--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((all t))
        (dolist (needle needles)
          (when all
            (unless (search-forward needle nil t) (setq all nil))))
        all))))

(defun m60-imp4--lines (rel)
  "Count the NEWLINES of REL, the unit of `wc -l'."
  (m60-imp4--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (search-forward "\n" nil t) (setq n (1+ n)))
        n))))

(defun m60-imp4--grep-c (rel regexp)
  "Count the LINES of REL that match REGEXP, the unit of `grep -c'."
  (m60-imp4--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (not (eobp))
          (when (re-search-forward regexp (line-end-position) t)
            (setq n (1+ n)))
          (forward-line 1))
        n))))

;;; --- the plain-guile probe runner -----------------------------------

(defun m60-imp4--probe-1 (mode)
  "Run test/m60/probe-imp3.scm in MODE as a `guile -L mod' child
process, with GUILE_AUTO_COMPILE=0 and GUILEMACS_ROOT set, and with
`default-directory' at the repo root.  Return (EXIT . OUTPUT), where
OUTPUT holds stdout AND stderr, or the symbol `m60-imp4-prog-absent'
when the `guile' binary is not on PATH."
  (if (not (executable-find "guile"))
      'm60-imp4-prog-absent
    (let ((buf (get-buffer-create " *m60-imp4-probe*"))
          (default-directory m60-imp4--root)
          (process-environment
           (append (list (concat "GUILEMACS_ROOT=" m60-imp4--root)
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

(defun m60-imp4--probe (mode)
  "The cached result of `m60-imp4--probe-1' for MODE."
  (let ((cell (assoc mode m60-imp4--probe-cache)))
    (if cell
        (cdr cell)
      (let ((result (m60-imp4--probe-1 mode)))
        (push (cons mode result) m60-imp4--probe-cache)
        result))))

(defun m60-imp4--probe-output (mode)
  "The OUTPUT of the probe MODE when the child exited 0, else nil.  A
crash mid-mode printed a partial output, so the exit status is part of
every output check.  When the `guile' binary is absent, the marker
`m60-imp4-prog-absent' is returned instead of nil, so the caller can
SKIP and not pass or fail."
  (let ((result (m60-imp4--probe mode)))
    (cond
     ((eq result 'm60-imp4-prog-absent) result)
     ((and (consp result) (eql 0 (car result))) (cdr result))
     (t nil))))

(defun m60-imp4--probe-line (mode line)
  "Non-nil when the probe MODE printed LINE as one WHOLE line and the
child exited 0.  A substring match is NOT enough: a line pin holds the
whole line, so a changed value can not hide inside it."
  (let ((out (m60-imp4--probe-output mode)))
    (cond
     ((eq out 'm60-imp4-prog-absent) out)
     ((not (stringp out)) nil)
     (t (with-temp-buffer
          (insert "\n" out "\n")
          (goto-char (point-min))
          (and (search-forward (concat "\n" line "\n") nil t) t))))))

(defun m60-imp4--probe-holds (mode needle)
  "Non-nil when the OUTPUT of the probe MODE holds NEEDLE (a substring
pin; use it only where a run-dependent address sits in the text)."
  (let ((out (m60-imp4--probe-output mode)))
    (cond
     ((eq out 'm60-imp4-prog-absent) out)
     ((not (stringp out)) nil)
     (t (with-temp-buffer
          (insert out)
          (goto-char (point-min))
          (and (search-forward needle nil t) t))))))

(defun m60-imp4--probe-holds-none (mode needle)
  "Non-nil when the OUTPUT of the probe MODE holds NO NEEDLE."
  (let ((out (m60-imp4--probe-output mode)))
    (cond
     ((eq out 'm60-imp4-prog-absent) out)
     ((not (stringp out)) nil)
     (t (with-temp-buffer
          (insert out)
          (goto-char (point-min))
          (not (search-forward needle nil t)))))))

(defun m60-imp4--all (&rest values)
  "`and' over the ALREADY-EVALUATED VALUES, with one difference: a
MARKER wins over a nil.  Both markers are truthy, so a plain `and'
returns the value of a LATER form and the check reads as a PASS.  The
verdict order matches `m60-imp4--verdict': the absent FILE marker first
(a real FAIL), then the absent `guile' marker (a skip), then nil (a
FAIL), then t (a PASS)."
  (cond
   ((memq 'm60-imp4-absent values) 'm60-imp4-absent)
   ((memq 'm60-imp4-prog-absent values) 'm60-imp4-prog-absent)
   ((memq nil values) nil)
   (t t)))

;;; --- report helpers -------------------------------------------------

(defun m60-imp4--verdict (ok)
  "Classify the value OK of one check: `pass', `fail', `absent' (the
TRACKED file is missing -- a real FAIL), or `skip' (the `guile' binary is
not on PATH, so the probe could not run -- never a pass)."
  (cond
   ((eq ok 'm60-imp4-prog-absent) 'skip)
   ((eq ok 'm60-imp4-absent) 'absent)
   (ok 'pass)
   (t 'fail)))

(defun m60-imp4--check (name ok)
  "Report and register one check.  The 4 outcomes come from
`m60-imp4--verdict': an absent TRACKED file prints FAIL (a real error,
not a pass), and an absent `guile' binary prints INFO and registers a
controlled ERT skip -- never a pass."
  (let ((verdict (m60-imp4--verdict ok)))
    (cond
     ((eq verdict 'skip)
      (m60-imp4--info-skip name "no guile binary on PATH"))
     ((eq verdict 'absent)
      (princ (format "FAIL m60/imp4/%s (source file absent)\n" name))
      (setq m60-imp4--registered (1+ m60-imp4--registered))
      (m60-imp4--bump-group)
      (imp-register-bool-as-ert-test (format "m60-imp4/%s" name) nil))
     (t
      (princ (format "%s m60/imp4/%s\n"
                     (if (eq verdict 'pass) "PASS" "FAIL") name))
      (setq m60-imp4--registered (1+ m60-imp4--registered))
      (m60-imp4--bump-group)
      (imp-register-bool-as-ert-test (format "m60-imp4/%s" name)
                                     (eq verdict 'pass))))))

(defun m60-imp4--info-skip (name reason)
  "Register one explicit INFO skip, counted into the current group.  A
host limit is a skip, never a pass."
  (princ (format "INFO m60/imp4/%s %s\n" name reason))
  (setq m60-imp4--registered (1+ m60-imp4--registered))
  (m60-imp4--bump-group)
  (imp-register-skip-as-ert-test (format "m60-imp4/%s" name) reason))

;;; --- S1. The 2 new forms of init-loader -----------------------------

;; Row 19 uses `symbol-bound?' (a VARIABLE cell), row 18 uses
;; `symbol-fbound?' (a FUNCTION cell).  This is the shape of rows
;; 14 ... 17 of the same guarded bind block.
(setq m60-imp4--group 's1)

(m60-imp4--check "s1/features-form-guarded"
                 (m60-imp4--ordered-p
                  "mod/emacs/loader.scm"
                  '("(unless (symbol-bound? 'features)"
                    "(set-symbol-value! 'features '())")))

(m60-imp4--check "s1/provide-form-guarded"
                 (m60-imp4--ordered-p
                  "mod/emacs/loader.scm"
                  '("(unless (symbol-fbound? 'provide)"
                    "(set-symbol-function! 'provide elisp-provide)")))

;; The 2 forms sit AFTER the `%load-path' append, next to the guarded
;; binds of rows 14 ... 17: MEASURED order in `init-loader'.
(m60-imp4--check "s1/order-after-load-path-append"
                 (m60-imp4--ordered-p
                  "mod/emacs/loader.scm"
                  '("(set! %load-path (append dirs %load-path))"
                    "(unless (symbol-bound? 'features)"
                    "(set-symbol-value! 'features '())"
                    "(unless (symbol-fbound? 'provide)"
                    "(set-symbol-function! 'provide elisp-provide)")))

;; The bind is a standalone-load default, so it carries a FIX marker in
;; the =FIX-YYYYMMDD-guilemacs:= form of the project rules.
(m60-imp4--check "s1/fix-marker-20261020"
                 (m60-imp4--holds-all "mod/emacs/loader.scm"
                                      '("FIX-20261020-guilemacs")))

;;; --- S2. ONE home only ----------------------------------------------

;; Two live mechanisms are not permitted.  The prelude and
;; `init-utils-registrations' hold NEITHER cell after the delete.
(setq m60-imp4--group 's2)

(m60-imp4--check "s2/zero-features-binds-in-prelude"
                 (eql 0 (m60-imp4--grep-c "prelude/load.scm"
                                          "set-symbol-value! 'features")))

(m60-imp4--check "s2/zero-provide-installs-in-utils"
                 (eql 0 (m60-imp4--grep-c "mod/emacs/utils.scm"
                                          "set-symbol-function! 'provide")))

(m60-imp4--check "s2/one-home-of-each-in-loader"
                 (m60-imp4--all
                  (eql 1 (m60-imp4--grep-c "mod/emacs/loader.scm"
                                           "set-symbol-value! 'features"))
                  (eql 1 (m60-imp4--grep-c "mod/emacs/loader.scm"
                                           "set-symbol-function! 'provide"))))

;;; --- S3. The acceptance observable ----------------------------------

;; A plain `guile -L mod' process, mode `cells', which NEVER installs the
;; 2 cells: it prints `LOAD lisp/cdl.el: done' and the 3 acceptance words
;; of brief.org section 11.  MEASURED 2026-10-20.  The words come from the
;; 2 guarded forms of `init-loader' and from nowhere else, so these checks
;; go RED when a form is deleted (cr.org F2 of the review of 174f0d2db).
(setq m60-imp4--group 's3)

(m60-imp4--check "s3/cdl-loads-to-end"
                 (m60-imp4--probe-line "cells" "LOAD lisp/cdl.el: done"))

(m60-imp4--check "s3/featurep-cdl"
                 (m60-imp4--probe-line "cells" "featurep cdl: #t"))

(m60-imp4--check "s3/features-is-cdl"
                 (m60-imp4--probe-line "cells" "features: (cdl)"))

;; `require' was NOT part of imp-4 (row 20 is a separate commit).
;; RE-PINNED at M60 imp-5: row 20 installs the cell, so the imp-4
;; asymmetry `require=#f' is gone and BOTH cells report #t.
(m60-imp4--check "s3/asymmetry-and-features-bound"
                 (m60-imp4--all
                  (m60-imp4--probe-line "cells"
                                        "ASYM: require=#t provide=#t")
                  (m60-imp4--probe-line "cells" "FEATURES-BOUND: #t")))

;;; --- S4. The negative control ---------------------------------------

;; Mode `negative' takes the SAME boot as every other mode and then
;; UNBINDS the value cell of `features' again with the exported
;; `makunbound!' helper, so the variable is UNBOUND and not #nil.
;; MEASURED: the load still raises `wrong-type-arg' with the words `memq'
;; and `uninterned-symbol unbound'.  The address in the sentinel changes
;; per run, so the pin holds 2 WORDS, not 1 LINE.
(setq m60-imp4--group 's4)

(m60-imp4--check "s4/control-cells"
                 (m60-imp4--all
                  (m60-imp4--probe-line "negative" "features-bound: #f")
                  (m60-imp4--probe-line "negative" "provide-fbound: #t")))

(m60-imp4--check "s4/control-wrong-type-arg"
                 (m60-imp4--all
                  (m60-imp4--probe-holds "negative"
                                         "LOAD cdl: ERROR wrong-type-arg")
                  (m60-imp4--probe-holds "negative" "\"memq\"")
                  (m60-imp4--probe-holds "negative" "uninterned-symbol unbound")
                  (m60-imp4--probe-holds-none "negative" "void-function")))

;; The control must prove the UNBOUND state without a second mechanism:
;; the boot is NOT skipped, and the unbind uses the EXPORTED helper
;; `makunbound!' of (emacs-elisp runtime), not a private binding.
(m60-imp4--check "s4/control-shape"
                 (m60-imp4--all
                  (m60-imp4--holds-all
                   "test/m60/probe-imp3.scm"
                   '("(makunbound! 'features)"))
                  (m60-imp4--holds-none "test/m60/probe-imp3.scm"
                                        '("value-slot-module"))
                  (m60-imp4--holds-none "test/m60/probe-imp3.scm"
                                        '("(unless (string=? mode \"negative\")"))))

;; The MEASUREMENT behind that shape, repeatable in its own process: mode
;; `noboot' takes NO boot and stops with `Wrong type to apply: #nil', so
;; it does NOT name the unbound sentinel.  This is the record of why mode
;; `negative' keeps the boot (cr.org F3 of the review of 174f0d2db).
(m60-imp4--check "s4/no-boot-stops-earlier"
                 (m60-imp4--all
                  (m60-imp4--probe-line "noboot" "features-bound: #f")
                  (m60-imp4--probe-line "noboot" "provide-fbound: #t")
                  (m60-imp4--probe-holds "noboot"
                                         "LOAD cdl: ERROR wrong-type-arg")
                  (m60-imp4--probe-holds "noboot" "Wrong type to apply")
                  (m60-imp4--probe-holds-none "noboot"
                                              "uninterned-symbol unbound")))

;;; --- S5. The re-measured surface ------------------------------------

;; Unit: NEWLINES (`wc -l'), MEASURED 2026-10-20 after the change:
;; loader.scm 1203 + 11 (2 guarded forms, 9 comment lines),
;; prelude/load.scm 230 - 1, mod/emacs/utils.scm 607 - 1.
;; RE-MEASURED at M60 imp-6: loader.scm 1308 -> 1328 (+20 lines: the 2
;; evaluator branches of rows 21 and 22).  The other 2 counts stand.
;; The check name follows the measurement: it said 1214 until now, and
;; the old value 1214 stays in this comment (cr.org F3).
(setq m60-imp4--group 's5)

;; RE-PINNED at M60 imp-7: 1,328 -> 1,363 -> 1,389 -> 1,391 -> 1,398 LINES (rows 23 and 24).
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
;; M60 imp-11 (cr.org F5) RE-PIN: loader.scm 1,588 -> 1,620 LINES (OLD
;; value 1,588), and the check NAME drops the stale number 1511.
(m60-imp4--check "s5/loader-lines"
                 ;; M60 imp-12 RE-PIN: loader.scm 1,620 -> 1,642 LINES (OLD value 1,620).
                 ;; M60 imp-13 RE-PIN: loader.scm 1,642 -> 1,653 LINES (OLD value 1,642).
                 (eql 1653 (m60-imp4--lines "mod/emacs/loader.scm")))
(m60-imp4--check "s5/prelude-load-lines-229"
                 (eql 229 (m60-imp4--lines "prelude/load.scm")))
;; M60 imp-8 (row 27) RE-PIN: utils.scm 606 -> 640 LINES (the
;; `elisp-make-obsolete-variable' procedure, 1 export NAME and the
;; L11 ... L15 limit block).  The old value was 606.
(m60-imp4--check "s5/utils-lines-606"
                 ;; M60 imp-13 RE-PIN: utils.scm 640 -> 662 LINES (OLD value 640).
                 (eql 662 (m60-imp4--lines "mod/emacs/utils.scm")))

;; Unit: LINES (`grep -c'), MEASURED 2026-10-20: 18/14/7 before the
;; change, 19/15/8 after it.  Each count moves by 1, the 3 new lines of
;; the 2 forms.
;; M60 imp-8 (row 27) RE-PIN: loader.scm `symbol-fbound?' 22 -> 23
;; LINES (1 guarded install, the row-18 pattern of `provide').
;; M60 imp-8 (row 27) RE-PIN: loader.scm `set-symbol-function!' 18 -> 19
;; LINES (the same guarded install).  `FIX-.*guilemacs' stays 9.
;; M60 imp-10 RE-PIN: row 29 adds 2 `#:use-module' forms and 15
;; guarded installs to loader.scm -- 1,511 -> 1,588 LINES (wc -l) and
;; 23 / 19 -> 38 / 34 LINES (grep -c) -- and mode `arith' to
;; test/m60/probe-imp3.scm (591 -> 691 LINES).  OLD VALUES are the
;; cells that the numbers above replace.
(m60-imp4--check "s5/loader-grep-c-counts"
;; M60 imp-11 RE-PIN: `symbol-fbound?` 38 -> 39 LINES (OLD value 38).
                 ;; M60 imp-13 RE-PIN: `symbol-fbound?' 39 -> 40 LINES (OLD value 39).
                 (and (eql 40 (m60-imp4--grep-c "mod/emacs/loader.scm"
                                                "symbol-fbound?"))
;; M60 imp-11 RE-PIN: `set-symbol-function!` 34 -> 35 LINES (OLD value 34).
                      ;; M60 imp-13 RE-PIN: `set-symbol-function!' 35 -> 36 LINES (OLD value 35).
                      (eql 36 (m60-imp4--grep-c "mod/emacs/loader.scm"
                                                "set-symbol-function!"))
                      (eql 9 (m60-imp4--grep-c "mod/emacs/loader.scm"
                                               "FIX-.*guilemacs"))))

;;; --- S6. The registration of THIS corpus ----------------------------

(setq m60-imp4--group 's6)

(m60-imp4--check "s6/run-tests-m60-imp4"
                 (m60-imp4--holds-all "tool/run-tests.scm"
                                      '("test/m60/test-m60-imp4.el")))

(m60-imp4--check "s6/imp4-after-imp3"
                 (m60-imp4--ordered-p
                  "tool/run-tests.scm"
                  '("test/m60/test-m60-imp1.el"
                    "test/m60/test-m60-imp2.el"
                    "test/m60/test-m60-imp3.el"
                    "test/m60/test-m60-imp4.el")))

;; The (m60) group must not take the prelude key: a prelude run would
;; load the prelude BEFORE the corpus and hide a missing boot.
(m60-imp4--check "s6/m60-group-no-prelude"
                 (m60-imp4--all
                  (m60-imp4--holds-all "tool/run-tests.scm" '("(group (m60)"))
                  (m60-imp4--holds-none "tool/run-tests.scm"
                                        '("(group (m60 "))))

;;; --- S7. The guards -------------------------------------------------

;; Per-group floors stop a silent loss of a group: S1 4, S2 3, S3 4,
;; S4 4, S5 4, S6 3.
(setq m60-imp4--group 's7)

(m60-imp4--check "s7/min-s1-checks-4" (>= (m60-imp4--group-count 's1) 4))
(m60-imp4--check "s7/min-s2-checks-3" (>= (m60-imp4--group-count 's2) 3))
(m60-imp4--check "s7/min-s3-checks-4" (>= (m60-imp4--group-count 's3) 4))
(m60-imp4--check "s7/min-s4-checks-4" (>= (m60-imp4--group-count 's4) 4))
(m60-imp4--check "s7/min-s5-checks-4" (>= (m60-imp4--group-count 's5) 4))
(m60-imp4--check "s7/min-s6-checks-3" (>= (m60-imp4--group-count 's6) 3))

(m60-imp4--check "s7/prog-absent-routes-to-skip"
                 (and (eq 'skip (m60-imp4--verdict 'm60-imp4-prog-absent))
                      (eq 'skip (m60-imp4--verdict
                                 (m60-imp4--all
                                  'm60-imp4-prog-absent
                                  (m60-imp4--probe-line "cells"
                                                        "LOAD lisp/cdl.el: done"))))
                      (eq 'absent (m60-imp4--verdict 'm60-imp4-absent))
                      (eq 'absent (m60-imp4--verdict
                                   (m60-imp4--all 'm60-imp4-absent t)))
                      (eq 'pass (m60-imp4--verdict t))
                      (eq 'fail (m60-imp4--verdict nil))
                      (eq 'fail (m60-imp4--verdict (m60-imp4--all t nil)))))

;;; --- The group-total check ------------------------------------------

;; MEASURED: 29 registered checks (S1 4, S2 3, S3 4, S4 4, S5 4, S6 3,
;; S7 7) plus this deftest itself = 30 ERT tests.

(defvar m60-imp4--min-gate-total 30
  "The exact number of m60-imp4 ERT tests: 29 registered checks (S1 4,
S2 3, S3 4, S4 4, S5 4, S6 3, S7 7) plus the group-total deftest
itself.")

(ert-deftest m60-imp4/gate-m60-total ()
  "The m60-imp4 corpus registers at least its docs-independent floor."
  (should (>= (length (ert-select-tests "^m60-imp4" t))
              m60-imp4--min-gate-total)))

(princ (format "=== m60 imp-4 suite done (%d checks; s1 %d, s2 %d, s3 %d, s4 %d, s5 %d, s6 %d, s7 %d) ===\n"
               m60-imp4--registered
               (m60-imp4--group-count 's1)
               (m60-imp4--group-count 's2)
               (m60-imp4--group-count 's3)
               (m60-imp4--group-count 's4)
               (m60-imp4--group-count 's5)
               (m60-imp4--group-count 's6)
               (m60-imp4--group-count 's7)))
