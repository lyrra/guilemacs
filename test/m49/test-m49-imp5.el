;;; test-m49-imp5.el --- M49 imp-5 close-out corpus (re-measure and record).
;;;
;;; M49 imp-5 is the close-out (brief.org section 1).  It changes no C
;;; and no Scheme.  It re-measures the surface, runs the gates, and
;;; records the result.  This corpus pins the end state against the tree,
;;; so a stale number or a missing registration fails the run.
;;;
;;; It pins:
;;;   S1 -- the surface of brief.org section 4, re-measured at HEAD:
;;;         src/dired.c (1,346 lines, 10 DEFUNs, 2 scm_c_public_ref
;;;         sites, 2 --dired-* leaves at :1262 and :1290 (both G2), the
;;;         guile.h include at :45, 5 FIX-20261006-guilemacs marks);
;;;         mod/emacs/dired.scm (156 lines, 2 defelisp %--dired-* lines);
;;;         the 4 public wrappers of the module (dired-listing-names,
;;;         dired-file-name-completion, dired-file-name-all-completions,
;;;         dired-file-attributes-lessp); and the tree-wide
;;;         scm_c_public_ref count over src/*.[chm] (240).  The 14 checks
;;;         come from the 10 value rows of brief.org section 4: row 4
;;;         pins the 2 G2 leaves by name and line (2 checks), row 9 pins
;;;         the 4 public wrapper names (4 checks), and every other row
;;;         yields 1, so 8 + 2 + 4 == 14 checks in total.
;;;   S2 -- the registration: the corpus is registered in the (m49)
;;;         group of tool/run-tests.scm after test-m49-imp4.el
;;;         (brief.org section 6).  Read tool/run-tests.scm only.
;;;   S3 -- the guards: the per-group min-count guard (one for S1, one
;;;         for S2), and the group-total check.  The total check is an
;;;         `ert-deftest', so its body runs after every corpus of the
;;;         group has loaded and sees them all, whatever order
;;;         tool/run-tests.scm picked.
;;;
;;; The G2 decision (brief.org section 5) is Option B: an accepted A2
;;; that names the duplication.  The 2 G2 leaves each repeat the body of
;;; their own hub (Fexpand_file_name, both Ffind_file_name_handler calls,
;;; the handler call4 / call3) and then call the engine
;;; file_name_completion.  A Shape A rewire cannot keep the exit
;;; criterion true at an acceptable delta, because the C loop decides the
;;; prefix match on ENCODED names with scmp (:900) before DECODE_FILE,
;;; while Scheme holds DECODED names (imp-4).  imp-5 changes no C, so it
;;; records the A2 and pins the 2 G2 leaves here.
;;;
;;; This corpus reads TRACKED files only (src/, mod/, tool/).  It does
;;; NOT read docs/ (docs/kb.org test-must-not-read-docs): a gitignored
;;; or untracked record can only pass or skip, so a record check proves
;;; nothing.  It does NOT run a nested m49 gate subprocess.  The
;;; in-process `ert-deftest' replaces a nested gate.
;;;
;;; A read error is a real error, never a silent pass.  An absent src/
;;; file is a real error.

(princ "=== m49 imp-5 close-out suite ===\n")

(require 'imp-ert-report)

(defvar m49-imp5--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))

(defvar m49-imp5--registered 0
  "Total number of tracked-file checks this corpus has registered.")

(defvar m49-imp5--group nil
  "The group that `m49-imp5--check' counts into: `s1', `s2', or nil.")

(defvar m49-imp5--counts nil
  "Alist of (GROUP . COUNT) for the registered tracked-file checks.")

(defun m49-imp5--group-count (group)
  "Number of tracked-file checks registered so far in GROUP."
  (or (cdr (assq group m49-imp5--counts)) 0))

(defun m49-imp5--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
the symbol `m49-imp5-absent' when REL does not exist."
  (let ((path (expand-file-name rel m49-imp5--root)))
    (if (not (file-exists-p path))
        'm49-imp5-absent
      (with-temp-buffer
        (insert-file-contents path)
        (funcall fn)))))

(defun m49-imp5--contains-p (rel needle)
  "Non-nil when REL (repo-root-relative) contains NEEDLE."
  (m49-imp5--with rel
    (lambda ()
      (goto-char (point-min))
      (search-forward needle nil t))))

(defun m49-imp5--export-p (rel name)
  "Non-nil when the `#:export' form of REL (repo-root-relative) names NAME.
The search is confined to the balanced `#:export' list, so a NAME that
only appears in a comment, a body, or a `defelisp' line does not count.
This is the brief.org section 4 row 9 measure: \"the 4 `#:export' names
of the module\"."
  (m49-imp5--with rel
    (lambda ()
      (goto-char (point-min))
      (when (search-forward "#:export" nil t)
        (skip-chars-forward " \t\n")
        (when (looking-at "(")
          (let ((start (point)))
            (forward-list)
            (let ((limit (point)))
              (goto-char start)
              (search-forward name limit t))))))))

(defun m49-imp5--lines (rel)
  "Count the newlines of REL the way `wc -l' does."
  (m49-imp5--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (search-forward "\n" nil t) (setq n (1+ n)))
        n))))

(defun m49-imp5--count (rel regexp)
  "Count the matches of REGEXP in REL."
  (m49-imp5--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (re-search-forward regexp nil t) (setq n (1+ n)))
        n))))

(defun m49-imp5--line-of (rel needle)
  "1-based line number of the first literal NEEDLE in REL, or nil."
  (m49-imp5--with rel
    (lambda ()
      (goto-char (point-min))
      (when (search-forward needle nil t)
        (line-number-at-pos (match-beginning 0))))))

(defun m49-imp5--count-scm-ref ()
  "Count scm_c_public_ref over src/*.[chm] (the brief.org section 4 measure)."
  (let ((total 0)
        (dir (expand-file-name "src" m49-imp5--root)))
    (dolist (f (directory-files dir t "\\.[chm]\\'"))
      (setq total (+ total (or (m49-imp5--count f "scm_c_public_ref") 0))))
    total))

(defun m49-imp5--check (name ok)
  "Report and register one check on a TRACKED file.  OK is a boolean.
An absent src/ file makes the reader return the symbol
`m49-imp5-absent'.  The absent branch prints FAIL AND registers a real
FAILING ERT test, so an absent src/ file is a real error, not a pass:
the harness parses ERT's batch output for its exit code, so a princ'd
FAIL with no ERT test would leave the exit code 0."
  (if (eq ok 'm49-imp5-absent)
      (progn
        (princ (format "FAIL m49/imp5/%s (source file absent)\n" name))
        (imp-register-bool-as-ert-test (format "m49-imp5/%s" name) nil)
        (setq m49-imp5--registered (1+ m49-imp5--registered))
        (when m49-imp5--group
          (let ((cell (assq m49-imp5--group m49-imp5--counts)))
            (if cell
                (setcdr cell (1+ (cdr cell)))
              (push (cons m49-imp5--group 1) m49-imp5--counts)))))
    (progn
      (princ (format "%s m49/imp5/%s\n" (if ok "PASS" "FAIL") name))
      (setq m49-imp5--registered (1+ m49-imp5--registered))
      (when m49-imp5--group
        (let ((cell (assq m49-imp5--group m49-imp5--counts)))
          (if cell
              (setcdr cell (1+ (cdr cell)))
            (push (cons m49-imp5--group 1) m49-imp5--counts))))
      (imp-register-bool-as-ert-test (format "m49-imp5/%s" name) (and ok t)))))

;;; --- S1. The surface (brief.org section 4) --------------------------

;; The 14 checks come from the 10 value rows of the brief.org section 4
;; table.  Rows 1, 2, 3, 5, 6, 7, 8, and 10 yield one check each; row 4
;; pins the 2 G2 leaves by name and line (2 checks); row 9 pins the 4
;; public wrapper names (4 checks).  So 8 + 2 + 4 == 14.

(setq m49-imp5--group 's1)

;; Row 1: src/dired.c lines = 1,346.
(m49-imp5--check "dired.c-lines-1346"
                 (eql 1346 (m49-imp5--lines "src/dired.c")))
;; Row 2: src/dired.c ^DEFUN (" count = 10.
(m49-imp5--check "dired.c-defun-count-10"
                 (eql 10 (m49-imp5--count "src/dired.c" "^DEFUN (\"")))
;; Row 3: src/dired.c scm_c_public_ref sites = 2.
(m49-imp5--check "dired.c-scm-ref-2"
                 (eql 2 (m49-imp5--count "src/dired.c" "scm_c_public_ref")))
;; Row 4: the 2 G2 leaves by name and line (:1262, :1290).
(m49-imp5--check "g2-leaf-completion-at-1262"
                 (eql 1262 (m49-imp5--line-of
                            "src/dired.c"
                            "DEFUN (\"--dired-file-name-completion\"")))
(m49-imp5--check "g2-leaf-all-completions-at-1290"
                 (eql 1290 (m49-imp5--line-of
                            "src/dired.c"
                            "DEFUN (\"--dired-file-name-all-completions\"")))
;; Row 5: the guile.h include at :45.
(m49-imp5--check "dired.c-guile.h-at-45"
                 (eql 45 (m49-imp5--line-of "src/dired.c" "#include \"guile.h\"")))
;; Row 6: the FIX-20261006-guilemacs marks = 5.
(m49-imp5--check "dired.c-fix-marks-5"
                 (eql 5 (m49-imp5--count "src/dired.c"
                                         "FIX-20261006-guilemacs")))
;; Row 7: mod/emacs/dired.scm lines = 156.
(m49-imp5--check "dired.scm-lines-156"
                 (eql 156 (m49-imp5--lines "mod/emacs/dired.scm")))
;; Row 8: the defelisp %--dired-* lines = 2 (both G2).
(m49-imp5--check "dired.scm-defelisp-2"
                 (eql 2 (m49-imp5--count "mod/emacs/dired.scm"
                                         "^(defelisp %--dired-")))
;; Row 9: the 4 public wrapper names of the module's #:export.  `export-p'
;; confines the search to the #:export form, so a name that appears only
;; in a comment or a body does not pass.
(m49-imp5--check "export-dired-listing-names"
                 (m49-imp5--export-p "mod/emacs/dired.scm"
                                     "dired-listing-names"))
(m49-imp5--check "export-dired-file-name-completion"
                 (m49-imp5--export-p "mod/emacs/dired.scm"
                                     "dired-file-name-completion"))
(m49-imp5--check "export-dired-file-name-all-completions"
                 (m49-imp5--export-p "mod/emacs/dired.scm"
                                     "dired-file-name-all-completions"))
(m49-imp5--check "export-dired-file-attributes-lessp"
                 (m49-imp5--export-p "mod/emacs/dired.scm"
                                     "dired-file-attributes-lessp"))
;; Row 10: the tree-wide scm_c_public_ref count over src/*.[chm] = 240.
(m49-imp5--check "tree-wide-scm-public-ref-240"
                 (eql 240 (m49-imp5--count-scm-ref)))

;;; --- S2. The corpus is registered (brief.org section 6) -------------

(setq m49-imp5--group 's2)

(m49-imp5--check "run-tests-m49-imp5"
                 (m49-imp5--contains-p "tool/run-tests.scm"
                                       "test/m49/test-m49-imp5.el"))
(m49-imp5--check "run-tests-m49-imp5-after-imp4"
                 (let ((imp4 (m49-imp5--line-of "tool/run-tests.scm"
                                                "test/m49/test-m49-imp4.el"))
                       (imp5 (m49-imp5--line-of "tool/run-tests.scm"
                                                "test/m49/test-m49-imp5.el")))
                   (and (integerp imp4) (integerp imp5) (< imp4 imp5))))

;;; --- S3. The guards (brief.org section 3.3) -------------------------

;; An --filter that matches no group already reports exit 0 with 0
;; tests, so a green m49 gate proves nothing until the corpus exists and
;; its checks really register.  These guards fail when the corpus body is
;; truncated or its core checks do not run.  The counts are stable because
;; every check is registered at load time.  S1 holds 14 checks; S2 holds
;; 2 checks.

(setq m49-imp5--group nil)

(m49-imp5--check "reg/min-s1-checks-14"
                 (>= (m49-imp5--group-count 's1) 14))
(m49-imp5--check "reg/min-s2-checks-2"
                 (>= (m49-imp5--group-count 's2) 2))

;;; --- The group-total check (brief.org section 3.3) ------------------

;; A nested m49 gate subprocess is replaced by an in-process
;; `ert-deftest'.  ERT runs every test after all five m49 corpora have
;; loaded, so this body sees the whole group's registered tests whatever
;; order tool/run-tests.scm loaded the files in -- it randomises them, so
;; a load-time count could not do this.
;;
;; The floor is measured from a real run, not from the stale per-corpus
;; minimums.  The m49 group registers N ERT tests at imp-5 (imp-1..imp-4
;; plus imp-5).  The only tests that can legitimately drop are the gated
;; runtime probes in imp-2, imp-3 and imp-4, which register nothing when
;; no built src/emacs exists.  The floor is the measured total minus
;; those probes, so it holds whether or not the probes run.
;;
;; This is a coarse net, not a tight bound.  The per-corpus reg/min-*
;; guards are the tight per-corpus check; this deftest only catches a
;; whole-corpus or load-order loss.  The corpus reads no docs/, so the
;; total does not depend on docs/.

(defvar m49-imp5--min-gate-total 143
  "The minimum number of ERT tests the m49 group registers.")

(ert-deftest m49-imp5/gate-m49-total ()
  "The m49 group registers at least its docs-independent floor."
  (should (>= (length (ert-select-tests "^m49-imp" t))
              m49-imp5--min-gate-total)))

(princ (format "=== m49 imp-5 close-out suite done (%d tracked checks; s1 %d, s2 %d) ===\n"
               m49-imp5--registered
               (m49-imp5--group-count 's1)
               (m49-imp5--group-count 's2)))
