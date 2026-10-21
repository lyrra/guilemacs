;;; test-m60-imp3.el --- M60 imp-3 SPLIT REGISTRATION corpus.
;;;
;;; M60 imp-1 wrote the audit, imp-2 measured the standalone-load
;;; boundary, and imp-3 SPLITS the language registration: the
;;; `define-language emacs-elisp' form moves from (emacs-elisp spec) to
;;; the new module (language emacs-elisp spec), and the monkey patch of
;;; prelude/load.scm is DELETED in the same commit.  Reason: Guile
;;; `lookup-language' resolves `(language NAME spec)' and reads the
;;; binding NAME in that module (system/base/language.scm:62 ... :66).
;;; (emacs-elisp spec) keeps `compile-and-load' and RE-EXPORTS the
;;; language object, so src/emacs.c:1639 still resolves its module.
;;;
;;; The (m60) group has NO prelude key, so this corpus runs INSIDE the
;;; built src/emacs (run-tests-loadup-emacs).  Every plain-guile value is
;;; measured by test/m60/probe-imp3.scm as a `guile -L mod' child process
;;; with GUILE_AUTO_COMPILE=0 -- the real plain-guile path, one MODE per
;;; child, so a stub of one mode can not hide the next result.
;;;
;;; It pins these groups:
;;;
;;;   S1 -- the surface, re-measured: 4 LINE counts, the 3 loader.scm
;;;         grep LINE counts, the mod/emacs-elisp ENTRIES (9, NOT 10:
;;;         brief.org F1), the 1 ENTRY of mod/language/emacs-elisp, the
;;;         2 fixtures of this imp, the imp-3 word of the fixture header
;;;         (cr.org F4), and the `.gitignore' rule that keeps the
;;;         generated `*.el.go' files out of the index (cr.org F3).
;;;   S2 -- the new module: its name, its `define-language' form, and
;;;         the things it must NOT hold (`compile-and-load',
;;;         `set-vm-engine!').
;;;   S3 -- the observable: mode `language' returns the language OBJECT
;;;         with the title "Modern Emacs Lisp".  A module load is NOT
;;;         proof (brief.org limit).
;;;   S4 -- ONE mechanism only: 0 patch lines in the prelude, the C
;;;         resolve of src/emacs.c:1639 kept, `compile-and-load' kept in
;;;         (emacs-elisp spec), and exactly 1 `define-language' site.
;;;         Plus the loader gate of cr.org F2: the compiled branch needs
;;;         the C runtime handoff, so a plain `guile' keeps the source
;;;         branch.
;;;   S5 -- no regression: the 5 probe modes reproduce the imp-2 values,
;;;         and the pure-guile gate stays 35 cases.
;;;   S6 -- the registration of THIS corpus: the imp-3 line AFTER the
;;;         imp-2 line, imp-1 and imp-2 kept, (m60) after (m59), no
;;;         prelude key.
;;;   S7 -- the guards: the per-group min counts, the marker-routing
;;;         self-check of the skip path, and the group-total deftest.
;;;
;;; This corpus reads TRACKED files only.  It does NOT read docs/.
;;; A read error is a real error, never a silent pass.  An absent
;;; TRACKED file is a real FAIL.  A missing `guile' binary is an explicit
;;; INFO skip, never a pass: `m60-imp3--check' routes the marker
;;; `m60-imp3-prog-absent' to `m60-imp3--info-skip', and `m60-imp3--all'
;;; carries that marker through a composite check.
;;;
;;; Every value below was MEASURED on this host on 2026-10-20 by running
;;; the fixture and the commands named in the comment of each check.
;;; MEASURED total: 46 registered checks (S1 9, S2 7, S3 4, S4 7, S5 8,
;;; S6 4, S7 7) plus the group-total deftest = 47 ERT tests.

(princ "=== m60 imp-3 split-registration measurement suite ===\n")

(require 'imp-ert-report)

(defvar m60-imp3--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))
(defvar m60-imp3--registered 0
  "Total number of checks this corpus has registered.")
(defvar m60-imp3--group nil
  "The group that `m60-imp3--check' counts into: `r1' .. `r7', or nil.")
(defvar m60-imp3--counts nil
  "Alist of (GROUP . COUNT) for the registered checks.")
(defvar m60-imp3--probe-cache nil
  "Alist of (MODE . RESULT) of the plain-guile probe runs of this corpus.
A mode is measured once per corpus run, so a 5-check group starts one
child process, not 5.")

(defun m60-imp3--group-count (group)
  "Number of checks registered so far in GROUP."
  (or (cdr (assq group m60-imp3--counts)) 0))

(defun m60-imp3--bump-group ()
  "Count one check into `m60-imp3--group'."
  (when m60-imp3--group
    (let ((cell (assq m60-imp3--group m60-imp3--counts)))
      (if cell
          (setcdr cell (1+ (cdr cell)))
        (push (cons m60-imp3--group 1) m60-imp3--counts)))))

;;; --- tracked-file helpers (the imp-1 idioms) -------------------------

(defun m60-imp3--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
the symbol `m60-imp3-absent' when REL does not exist.  `case-fold-search'
is bound to nil: the elisp default folds case and inflates a count."
  (let ((path (expand-file-name rel m60-imp3--root)))
    (if (not (file-exists-p path))
        'm60-imp3-absent
      (with-temp-buffer
        (insert-file-contents path)
        (let ((case-fold-search nil))
          (funcall fn))))))

(defun m60-imp3--text-of (rel)
  "The contents of REL as a string, or the symbol `m60-imp3-absent'."
  (m60-imp3--with rel
    (lambda ()
      (buffer-substring-no-properties (point-min) (point-max)))))

(defun m60-imp3--holds-all (rel needles)
  "Non-nil when the TRACKED file REL holds every NEEDLE.  An absent file
fails the check."
  (m60-imp3--with rel
    (lambda ()
      (let ((all t))
        (dolist (needle needles)
          (goto-char (point-min))
          (unless (search-forward needle nil t) (setq all nil)))
        all))))

(defun m60-imp3--holds-none (rel needles)
  "Non-nil when the TRACKED file REL holds NO needle of NEEDLES."
  (m60-imp3--with rel
    (lambda ()
      (let ((none t))
        (dolist (needle needles)
          (goto-char (point-min))
          (when (search-forward needle nil t) (setq none nil)))
        none))))

(defun m60-imp3--live-p (rel needle)
  "Non-nil when the TRACKED file REL holds NEEDLE on a line that is NOT
commented out."
  (m60-imp3--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((hit nil))
        (while (and (not hit) (search-forward needle nil t))
          (setq hit (save-excursion
                      (goto-char (line-beginning-position))
                      (not (looking-at-p "[ \t]*;")))))
        hit))))

(defun m60-imp3--ordered-p (rel needles)
  "Non-nil when the TRACKED file REL holds every NEEDLE in the GIVEN
ORDER: each search starts after the previous match."
  (m60-imp3--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((all t))
        (dolist (needle needles)
          (when all
            (unless (search-forward needle nil t) (setq all nil))))
        all))))

(defun m60-imp3--exists-p (rel)
  "Non-nil when REL exists in the tree at `m60-imp3--root'."
  (file-exists-p (expand-file-name rel m60-imp3--root)))

(defun m60-imp3--dir-entries (rel)
  "Count the entries of the directory REL, the unit of `ls | wc -l'."
  (let ((path (expand-file-name rel m60-imp3--root)))
    (if (not (file-directory-p path))
        'm60-imp3-absent
      (length (directory-files path nil "\\`[^.]")))))

(defun m60-imp3--lines (rel)
  "Count the NEWLINES of REL, the unit of `wc -l'."
  (m60-imp3--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (search-forward "\n" nil t) (setq n (1+ n)))
        n))))

(defun m60-imp3--grep-c (rel regexp)
  "Count the LINES of REL that match REGEXP, the unit of `grep -c'."
  (m60-imp3--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (not (eobp))
          (when (re-search-forward regexp (line-end-position) t)
            (setq n (1+ n)))
          (forward-line 1))
        n))))

(defun m60-imp3--count (rel regexp)
  "Count the OCCURRENCES of REGEXP in REL, the unit of
`grep -o | wc -l'.  This is NOT the unit of `grep -c'."
  (m60-imp3--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (re-search-forward regexp nil t) (setq n (1+ n)))
        n))))

(defun m60-imp3--line-of (rel regexp)
  "Return the 1-based line number of the first REGEXP match in REL, or
nil when REGEXP does not match.  The match END is read into a variable
BEFORE the newline loop: a loop that re-reads `(match-beginning 0)' takes
the match data of its own `search-forward' and raises
`Invalid search bound (wrong side of point)' (MEASURED)."
  (m60-imp3--with rel
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

(defun m60-imp3--count-scm-ref ()
  "Count scm_c_public_ref over src/*.[ch], the unit of
`grep -h scm_c_public_ref src/*.c src/*.h | wc -l'.  Unit: OCCURRENCES."
  (let ((total 0)
        (dir (expand-file-name "src" m60-imp3--root)))
    (dolist (f (directory-files dir t "\\.[ch]\\'"))
      (setq total (+ total (or (m60-imp3--count f "scm_c_public_ref") 0))))
    total))

;;; --- the plain-guile probe runner -----------------------------------

(defun m60-imp3--probe-1 (mode)
  "Run test/m60/probe-imp3.scm in MODE as a `guile -L mod' child
process, with GUILE_AUTO_COMPILE=0 and GUILEMACS_ROOT set, and with
`default-directory' at the repo root.  Return (EXIT . OUTPUT), where
OUTPUT holds stdout AND stderr, or the symbol `m60-imp3-prog-absent'
when the `guile' binary is not on PATH."
  (if (not (executable-find "guile"))
      'm60-imp3-prog-absent
    (let ((buf (get-buffer-create " *m60-imp3-probe*"))
          (default-directory m60-imp3--root)
          (process-environment
           (append (list (concat "GUILEMACS_ROOT=" m60-imp3--root)
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

(defun m60-imp3--probe (mode)
  "The cached result of `m60-imp3--probe-1' for MODE."
  (let ((cell (assoc mode m60-imp3--probe-cache)))
    (if cell
        (cdr cell)
      (let ((result (m60-imp3--probe-1 mode)))
        (push (cons mode result) m60-imp3--probe-cache)
        result))))

(defun m60-imp3--probe-output (mode)
  "The OUTPUT of the probe MODE when the child exited 0, else nil.  A
crash mid-mode printed a partial output, so the exit status is part of
every output check: a partial output can not pass.  When the `guile'
binary is absent, the marker `m60-imp3-prog-absent' is returned instead
of nil, so the caller can SKIP and not pass or fail (cr.org F4)."
  (let ((result (m60-imp3--probe mode)))
    (cond
     ((eq result 'm60-imp3-prog-absent) result)
     ((and (consp result) (eql 0 (car result))) (cdr result))
     (t nil))))

(defun m60-imp3--probe-exit (mode)
  "The exit status of the probe MODE, or the symbol
`m60-imp3-prog-absent'."
  (let ((result (m60-imp3--probe mode)))
    (if (consp result) (car result) result)))

(defun m60-imp3--probe-raw-output (mode)
  "The OUTPUT of the probe MODE for ANY exit status, or the marker
`m60-imp3-prog-absent'.  Use this only for a mode that MUST fail: the
registration mode of M60 imp-2 raises on purpose, so its output is
valuable at a non-zero exit.  Every other check goes through
`m60-imp3--probe-output', which requires exit 0."
  (let ((result (m60-imp3--probe mode)))
    (cond
     ((eq result 'm60-imp3-prog-absent) result)
     ((consp result) (cdr result))
     (t nil))))

(defun m60-imp3--probe-raw-holds (mode needle)
  "Non-nil when the OUTPUT of the probe MODE holds NEEDLE, at ANY exit
status."
  (let ((out (m60-imp3--probe-raw-output mode)))
    (cond
     ((eq out 'm60-imp3-prog-absent) out)
     ((not (stringp out)) nil)
     (t (with-temp-buffer
          (insert out)
          (goto-char (point-min))
          (and (search-forward needle nil t) t))))))

(defun m60-imp3--probe-line (mode line)
  "Non-nil when the probe MODE printed LINE as one WHOLE line and the
child exited 0.  A substring match is NOT enough: a line pin holds the
whole line, so a changed value can not hide inside it."
  (let ((out (m60-imp3--probe-output mode)))
    (cond
     ((eq out 'm60-imp3-prog-absent) out)
     ((not (stringp out)) nil)
     (t (with-temp-buffer
          (insert "\n" out "\n")
          (goto-char (point-min))
          (and (search-forward (concat "\n" line "\n") nil t) t))))))

(defun m60-imp3--probe-holds (mode needle)
  "Non-nil when the OUTPUT of the probe MODE holds NEEDLE (a substring
pin; use it only where a run-dependent address sits in the text)."
  (let ((out (m60-imp3--probe-output mode)))
    (cond
     ((eq out 'm60-imp3-prog-absent) out)
     ((not (stringp out)) nil)
     (t (with-temp-buffer
          (insert out)
          (goto-char (point-min))
          (and (search-forward needle nil t) t))))))

(defun m60-imp3--probe-holds-none (mode needle)
  "Non-nil when the OUTPUT of the probe MODE holds NO NEEDLE."
  (let ((out (m60-imp3--probe-output mode)))
    (cond
     ((eq out 'm60-imp3-prog-absent) out)
     ((not (stringp out)) nil)
     (t (with-temp-buffer
          (insert out)
          (goto-char (point-min))
          (not (search-forward needle nil t)))))))

(defun m60-imp3--probe-ordered (mode needles)
  "Non-nil when the OUTPUT of the probe MODE holds every NEEDLE in the
GIVEN ORDER, and the child exited 0."
  (let ((out (m60-imp3--probe-output mode)))
    (cond
     ((eq out 'm60-imp3-prog-absent) out)
     ((not (stringp out)) nil)
     (t (with-temp-buffer
          (insert out)
          (goto-char (point-min))
          (let ((all t))
            (dolist (needle needles)
              (when all
                (unless (search-forward needle nil t) (setq all nil))))
            all))))))

(defun m60-imp3--all (&rest values)
  "`and' over the ALREADY-EVALUATED VALUES, with one difference: a
MARKER wins over a nil.  Both markers are truthy, so a plain `and'
returns the value of a LATER form and the check reads as a PASS
(cr.org F4).  The verdict order matches `m60-imp3--verdict': the absent
FILE marker first (a real FAIL), then the absent `guile' marker (a
skip), then nil (a FAIL), then t (a PASS).  Use this wherever a check
combines a probe result or a file-helper result with a second result."
  (cond
   ((memq 'm60-imp3-absent values) 'm60-imp3-absent)
   ((memq 'm60-imp3-prog-absent values) 'm60-imp3-prog-absent)
   ((memq nil values) nil)
   (t t)))

;;; --- report helpers -------------------------------------------------

(defun m60-imp3--verdict (ok)
  "Classify the value OK of one check: `pass', `fail', `absent' (the
TRACKED file is missing -- a real FAIL), or `skip' (the `guile' binary is
not on PATH, so the probe could not run -- never a pass)."
  (cond
   ((eq ok 'm60-imp3-prog-absent) 'skip)
   ((eq ok 'm60-imp3-absent) 'absent)
   (ok 'pass)
   (t 'fail)))

(defun m60-imp3--check (name ok)
  "Report and register one check.  The 4 outcomes come from
`m60-imp3--verdict': an absent TRACKED file prints FAIL (a real error,
not a pass), and an absent `guile' binary prints INFO and registers a
controlled ERT skip -- never a pass."
  (let ((verdict (m60-imp3--verdict ok)))
    (cond
     ((eq verdict 'skip)
      (m60-imp3--info-skip name "no guile binary on PATH"))
     ((eq verdict 'absent)
      (princ (format "FAIL m60/imp3/%s (source file absent)\n" name))
      (setq m60-imp3--registered (1+ m60-imp3--registered))
      (m60-imp3--bump-group)
      (imp-register-bool-as-ert-test (format "m60-imp3/%s" name) nil))
     (t
      (princ (format "%s m60/imp3/%s\n"
                     (if (eq verdict 'pass) "PASS" "FAIL") name))
      (setq m60-imp3--registered (1+ m60-imp3--registered))
      (m60-imp3--bump-group)
      (imp-register-bool-as-ert-test (format "m60-imp3/%s" name)
                                     (eq verdict 'pass))))))

(defun m60-imp3--info-skip (name reason)
  "Register one explicit INFO skip, counted into the current group.  A
host limit is a skip, never a pass."
  (princ (format "INFO m60/imp3/%s %s\n" name reason))
  (setq m60-imp3--registered (1+ m60-imp3--registered))
  (m60-imp3--bump-group)
  (imp-register-skip-as-ert-test (format "m60-imp3/%s" name) reason))

;;; --- S1. The surface, re-measured -----------------------------------

;; Unit: NEWLINES (`wc -l').  MEASURED 2026-10-20 after the split:
;; prelude/load.scm lost the 36 patch lines (266 -> 230) and the bare
;; `features' bind (-1), and mod/emacs-elisp/spec.scm lost the language
;; form (38 -> 32).
(setq m60-imp3--group 's1)

(m60-imp3--check "s1/prelude-load-lines"
                 (eql 229 (m60-imp3--lines "prelude/load.scm")))
(m60-imp3--check "s1/spec-and-language-spec-lines"
                 (and (eql 32 (m60-imp3--lines "mod/emacs-elisp/spec.scm"))
                      (eql 20 (m60-imp3--lines
                               "mod/language/emacs-elisp/spec.scm"))))

;; MEASURED 1214: the imp-3 value 1203 plus the 11 lines of the 2
;; guarded forms of M60 imp-4 (2 forms, 9 lines of comment).
;; RE-MEASURED at M60 imp-6: 1214 -> 1308 at imp-5, then 1308 -> 1328.
;; The 2 evaluator branches of rows 21 and 22 add 20 lines (5 comment
;; lines each, and 5 code lines each).
(m60-imp3--check "s1/loader-lines"
                 (eql 1328 (m60-imp3--lines "mod/emacs/loader.scm")))

;; Unit: LINES (`grep -c').  RE-MEASURED at M60 imp-5: 22 / 18 / 9.
;; The 2 landed cells add 1 guarded install, 1 install and 1 FIX line.
(m60-imp3--check "s1/loader.scm-grep-c-counts"
                 (and (eql 22 (m60-imp3--grep-c "mod/emacs/loader.scm"
                                                "symbol-fbound?"))
                      (eql 18 (m60-imp3--grep-c "mod/emacs/loader.scm"
                                                "set-symbol-function!"))
                      (eql 9 (m60-imp3--grep-c "mod/emacs/loader.scm"
                                               "FIX-.*guilemacs"))))

;; brief.org F1: mod/emacs-elisp KEEPS 9 ENTRIES (`runtime/' is ONE
;; entry).  The new module is NOT inside it, so a count of 10 here would
;; be a false pin.  mod/language/emacs-elisp is 1 ENTRY.
(m60-imp3--check "s1/emacs-elisp-entries-9"
                 (eql 9 (m60-imp3--dir-entries "mod/emacs-elisp")))
(m60-imp3--check "s1/language-emacs-elisp-entries-1"
                 (eql 1 (m60-imp3--dir-entries "mod/language/emacs-elisp")))

;; The 2 fixtures of this imp.  An absent fixture must FAIL here, never
;; read as an INFO skip.
(m60-imp3--check "s1/fixtures-present"
                 (and (m60-imp3--exists-p "test/m60/probe-imp3.scm")
                      (m60-imp3--exists-p "test/m60/test-m60-imp3.el")))

;;; cr.org F4: the header of the fixture names the imp that owns it.  A
;;; copy of the imp-2 header would send a reader to the wrong file.
(m60-imp3--check "s1/probe-header-names-imp3"
                 (m60-imp3--holds-all "test/m60/probe-imp3.scm"
                                      '(";;; probe-imp3.scm --- M60 imp-3")))

;; cr.org F3: the first imp-3 attempt left 154 untracked `*.el.go'
;; files in the tree.  MEASURED: the FULL-Emacs test run writes them
;; again, because the compiled loader branch calls `compile-file' and
;; that call puts the GO file NEXT TO the source.  They are a build
;; artifact, like the `.elc' files that .gitignore :194 already
;; holds, so the fix is the SAME rule one line below it -- not a scan
;; that any ERT run would break.  The 154 files were deleted.
(m60-imp3--check "s1/generated-go-ignored"
                 (m60-imp3--holds-all ".gitignore" '("*.elc" "*.el.go")))

;;; --- S2. The new module ---------------------------------------------

;; The module NAME is the contract: `lookup-language' resolves exactly
;; `(language emacs-elisp spec)'.
(setq m60-imp3--group 's2)

(m60-imp3--check "s2/module-name"
                 (m60-imp3--live-p "mod/language/emacs-elisp/spec.scm"
                                   "(define-module (language emacs-elisp spec)"))
(m60-imp3--check "s2/holds-define-language"
                 (and (eql 1 (m60-imp3--grep-c
                              "mod/language/emacs-elisp/spec.scm"
                              "^(define-language emacs-elisp"))
                      (m60-imp3--live-p "mod/language/emacs-elisp/spec.scm"
                                        "#:title     \"Modern Emacs Lisp\"")))
(m60-imp3--check "s2/exports-the-language"
                 (m60-imp3--live-p "mod/language/emacs-elisp/spec.scm"
                                   "#:export (emacs-elisp)"))

;; The module holds the language object and NOTHING else: the boot
;; compile and the VM engine stay in (emacs-elisp spec), so the 2 modules
;; have no cycle.
(m60-imp3--check "s2/holds-no-compile-and-load"
                 (eql 0 (m60-imp3--grep-c
                         "mod/language/emacs-elisp/spec.scm"
                         "compile-and-load")))
(m60-imp3--check "s2/holds-no-vm-engine"
                 (eql 0 (m60-imp3--grep-c
                         "mod/language/emacs-elisp/spec.scm"
                         "set-vm-engine!")))

;; (emacs-elisp spec) imports the new module and RE-EXPORTS the binding,
;; so the C resolve of its own module name still finds the language.
(m60-imp3--check "s2/spec-imports-and-re-exports"
                 (and (m60-imp3--live-p "mod/emacs-elisp/spec.scm"
                                        "#:use-module (language emacs-elisp spec)")
                      (m60-imp3--live-p "mod/emacs-elisp/spec.scm"
                                        "#:re-export (emacs-elisp)")))
(m60-imp3--check "s2/spec-keeps-compile-and-load"
                 (eql 1 (m60-imp3--grep-c "mod/emacs-elisp/spec.scm"
                                          "(compile-and-load")))

;;; --- S3. The observable ---------------------------------------------

;; The acceptance observable of the brief: a PLAIN `guile -L mod'
;; process.  MEASURED: LANGUAGE? #t, title "Modern Emacs Lisp", name
;; emacs-elisp, exit 0.
(setq m60-imp3--group 's3)

(m60-imp3--check "s3/language-object"
                 (m60-imp3--probe-line "language" "LANGUAGE?: #t"))
(m60-imp3--check "s3/language-title"
                 (m60-imp3--probe-line "language"
                                       "LANGUAGE-TITLE: \"Modern Emacs Lisp\""))
(m60-imp3--check "s3/language-name"
                 (m60-imp3--probe-line "language" "LANGUAGE-NAME: emacs-elisp"))
(m60-imp3--check "s3/language-mode-exits-0"
                 (let ((exit (m60-imp3--probe-exit "language")))
                   (if (eq exit 'm60-imp3-prog-absent)
                       exit
                     (eql 0 exit))))

;;; --- S4. One mechanism only -----------------------------------------

;; Two live mechanisms are not permitted (brief.org limit N1).  The
;; prelude patch is GONE; the C resolve and `compile-and-load' stay.
(setq m60-imp3--group 's4)

(m60-imp3--check "s4/prelude-no-patched-lookup"
                 (eql 0 (m60-imp3--grep-c "prelude/load.scm"
                                          "patched-lookup")))
(m60-imp3--check "s4/prelude-no-module-set"
                 (m60-imp3--all
                  (eql 0 (m60-imp3--grep-c "prelude/load.scm" "module-set!"))
                  (eql 0 (m60-imp3--grep-c "prelude/load.scm" "bad language"))))
(m60-imp3--check "s4/c-resolve-kept"
                 (eql 1639 (m60-imp3--line-of
                            "src/emacs.c"
                            "scm_c_resolve_module (\"emacs-elisp spec\")")))
(m60-imp3--check "s4/prelude-keeps-mod-on-load-path"
                 (m60-imp3--live-p "prelude/load.scm" "/../mod"))
;; Exactly ONE `define-language emacs-elisp' site in the whole tree of
;; TRACKED Scheme sources of the language.
(m60-imp3--check "s4/one-define-language-site"
                 (and (eql 0 (m60-imp3--grep-c "mod/emacs-elisp/spec.scm"
                                               "define-language"))
                      (eql 1 (m60-imp3--grep-c
                              "mod/language/emacs-elisp/spec.scm"
                              "define-language"))))

;; cr.org F2: the loader takes the COMPILED branch only when the C core
;; has handed the runtime over.  The presence of the language object is
;; not enough: the bytecode resolves its variables in the
;; `elisp-symbols' module, and only the C core fills that module.
;; MEASURED: a plain `guile' keeps the SOURCE branch, so the 5 imp-2
;; probe values do not move.
(m60-imp3--check "s4/loader-requires-c-runtime"
                 (m60-imp3--all
                  (m60-imp3--live-p
                   "mod/emacs/loader.scm"
                   "(if (c-runtime-installed?) (lookup-language 'emacs-elisp) #f)")
                  ;; `compiled-file-name' was UNBOUND in this module.  The
                  ;; compiled branch needs it, so its import is part of
                  ;; the same contract.
                  (m60-imp3--live-p
                   "mod/emacs/loader.scm"
                   "#:select (compile compile-file compiled-file-name)")))
;; The 4 needles are LITERAL (`m60-imp3--live-p' runs `search-forward'),
;; so a `?' and a `(' need no regexp escape: MEASURED, this Emacs engine
;; does NOT treat `(' as a literal in a regexp the way GNU Emacs does.
(m60-imp3--check "s4/runtime-c-runtime-flag"
                 (m60-imp3--all
                  (m60-imp3--live-p "mod/emacs-elisp/runtime.scm"
                                    "(define %c-runtime-installed? #f)")
                  (m60-imp3--live-p "mod/emacs-elisp/runtime.scm"
                                    "(define (c-runtime-installed?)")
                  ;; The export must be there, or (emacs loader) can not
                  ;; see the binding at all.
                  (m60-imp3--holds-all "mod/emacs-elisp/runtime.scm"
                                       '("            c-runtime-installed?"))
                  (m60-imp3--live-p "mod/emacs-elisp/runtime.scm"
                                    "(set! %c-runtime-installed? #t)")))

;;; --- S5. No regression ----------------------------------------------

;; The 5 probe modes of imp-2, re-measured at imp-3: EVERY value is the
;; imp-2 value, so no R2/R3/R4 re-pin is needed (brief.org F5 measured:
;; the loader keeps the source-reading branch, because
;; `elisp-loader-compiler-available?' now also requires the C runtime
;; handoff of `emacs!', which a plain `guile' process never sees).
(setq m60-imp3--group 's5)

(m60-imp3--check "s5/cells-and-binds"
                 (m60-imp3--all
                  (m60-imp3--probe-line "cells" "EMPTY-CELLS: ()")
                  (m60-imp3--probe-line
                   "cells" "UNGUARDED: load=#t autoload-do-load=#t")
                  (m60-imp3--probe-line
                   "cells"
                   (concat "VARS: load-path=#t load-suffixes=#t"
                           " load-file-rep-suffixes=#t load-read-function=#t"))
                  ;; RE-PINNED at M60 imp-5: row 20 installs `require'.
                  (m60-imp3--probe-line "cells" "ASYM: require=#t provide=#t")))
;; RE-PINNED at M60 imp-4: lisp/cdl.el is no stop any more, it loads
;; to the END (`provide' and `features' landed).
;; RE-PINNED at M60 imp-6: the obarray stop moves from `(defconst)' to
;; `(make-obsolete-variable)' (row 27).  The other 2 stops keep their
;; text.
(m60-imp3--check "s5/four-first-stops"
                 (m60-imp3--probe-ordered
                  "cells"
                  '("LOAD lisp/subdirs.el: ERROR void-function"
                    "LOAD lisp/cdl.el: done"
                    "LOAD lisp/obarray.el: ERROR void-function (make-obsolete-variable)"
                    "LOAD lisp/hex-util.el: ERROR void-function (eval-when-compile)")))
(m60-imp3--check "s5/features-bound"
                 (m60-imp3--probe-line "cells" "FEATURES-BOUND: #t"))
(m60-imp3--check "s5/provide-then-cdl"
                 (m60-imp3--all
                  (m60-imp3--probe-line "provide" "LOAD cdl: done")
                  (m60-imp3--probe-line "provide" "featurep cdl: #t")
                  (m60-imp3--probe-line "provide" "features: (cdl)")))
(m60-imp3--check "s5/stub-chain"
                 (m60-imp3--probe-ordered
                  "stubs"
                  '("stub-provide / cdl: done"
                    "stub-defconst / obarray: ERROR void-function (make-obsolete-variable)"
                    "stub-eval-when-compile / hex-util: ERROR void-function (defmacro)"
                    "stub-ntl / subdirs: done")))
(m60-imp3--check "s5/last-good-point"
                 (m60-imp3--all
                  (m60-imp3--probe-line "stubs" "faithful-provide / cdl: done")
                  (m60-imp3--probe-line "stubs" "featurep cdl: #t")
                  (m60-imp3--probe-line "stubs" "features: (cdl)")))
(m60-imp3--check "s5/negative-control"
                 (m60-imp3--all
                  (m60-imp3--probe-line "negative" "features-bound: #f")
                  (m60-imp3--probe-line "negative" "provide-fbound: #t")
                  (m60-imp3--probe-holds "negative" "LOAD cdl: ERROR wrong-type-arg")
                  (m60-imp3--probe-holds-none "negative" "void-function")))

;; The pure-guile gate stays 35 cases: 3 + 4 + 28.  The 3 suites pin
;; their own case count, so this check pins the SUM of the 3 constants.
(m60-imp3--check "s5/mod-suites-pin-35"
                 (and (m60-imp3--holds-all
                       "test/mod/sequences-tests.scm" '("expected-passes 3"))
                      (m60-imp3--holds-all
                       "test/mod/standalone-tests.scm" '("expected-passes 4"))
                      (m60-imp3--holds-all
                       "test/mod/faces-tests.scm" '("expected-passes 28"))))

;;; --- S6. The registration of THIS corpus ----------------------------

(setq m60-imp3--group 's6)

(m60-imp3--check "s6/run-tests-m60-imp3"
                 (m60-imp3--live-p "tool/run-tests.scm"
                                   "test/m60/test-m60-imp3.el"))
(m60-imp3--check "s6/run-tests-imp3-after-imp2"
                 (m60-imp3--ordered-p
                  "tool/run-tests.scm"
                  '("test/m60/test-m60-imp1.el"
                    "test/m60/test-m60-imp2.el"
                    "test/m60/test-m60-imp3.el")))
(m60-imp3--check "s6/run-tests-m60-after-m59"
                 (m60-imp3--all (m60-imp3--live-p "tool/run-tests.scm"
                                                  "(group (m59)")
                                (m60-imp3--ordered-p "tool/run-tests.scm"
                                                     '("(group (m59)"
                                                       "(group (m60)"))))
(m60-imp3--check "s6/run-tests-m60-no-prelude"
                 (m60-imp3--all (m60-imp3--live-p "tool/run-tests.scm"
                                                  "(group (m60)")
                                (m60-imp3--holds-none "tool/run-tests.scm"
                                                      '("(group (m60 "))))

;;; --- S7. The guards -------------------------------------------------

;; Per-group floors stop a silent loss of a group: S1 9, S2 7, S3 4,
;; S4 7, S5 8, S6 4.
(setq m60-imp3--group 's7)

(m60-imp3--check "s7/min-s1-checks-9" (>= (m60-imp3--group-count 's1) 9))
(m60-imp3--check "s7/min-s2-checks-7" (>= (m60-imp3--group-count 's2) 7))
(m60-imp3--check "s7/min-s3-checks-4" (>= (m60-imp3--group-count 's3) 4))
(m60-imp3--check "s7/min-s4-checks-7" (>= (m60-imp3--group-count 's4) 7))
(m60-imp3--check "s7/min-s5-checks-8" (>= (m60-imp3--group-count 's5) 8))
(m60-imp3--check "s7/min-s6-checks-4" (>= (m60-imp3--group-count 's6) 4))

(m60-imp3--check "s7/prog-absent-routes-to-skip"
                 (and (eq 'skip (m60-imp3--verdict 'm60-imp3-prog-absent))
                      (eq 'skip (m60-imp3--verdict
                                 (m60-imp3--all
                                  'm60-imp3-prog-absent
                                  (m60-imp3--probe-line "language"
                                                        "LANGUAGE?: #t"))))
                      (eq 'absent (m60-imp3--verdict 'm60-imp3-absent))
                      (eq 'absent (m60-imp3--verdict
                                   (m60-imp3--all 'm60-imp3-absent t)))
                      (eq 'pass (m60-imp3--verdict t))
                      (eq 'fail (m60-imp3--verdict nil))
                      (eq 'fail (m60-imp3--verdict (m60-imp3--all t nil)))))

;;; --- The group-total check ------------------------------------------

;; MEASURED: 46 registered checks (S1 9, S2 7, S3 4, S4 7, S5 8, S6 4,
;; S7 7) plus this deftest itself = 47 ERT tests.

(defvar m60-imp3--min-gate-total 47
  "The exact number of m60-imp3 ERT tests: 46 registered checks (S1 9,
S2 7, S3 4, S4 7, S5 8, S6 4, S7 7) plus the group-total deftest
itself.")

(ert-deftest m60-imp3/gate-m60-total ()
  "The m60-imp3 corpus registers at least its docs-independent floor."
  (should (>= (length (ert-select-tests "^m60-imp3" t))
              m60-imp3--min-gate-total)))

(princ (format "=== m60 imp-3 suite done (%d checks; s1 %d, s2 %d, s3 %d, s4 %d, s5 %d, s6 %d, s7 %d) ===\n"
               m60-imp3--registered
               (m60-imp3--group-count 's1)
               (m60-imp3--group-count 's2)
               (m60-imp3--group-count 's3)
               (m60-imp3--group-count 's4)
               (m60-imp3--group-count 's5)
               (m60-imp3--group-count 's6)
               (m60-imp3--group-count 's7)))
