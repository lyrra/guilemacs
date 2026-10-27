;;; test-m47-imp6.el --- M47 imp-6 close-out corpus (re-measure and record).
;;;
;;; M47 imp-6 is the close-out (brief.org section 1).  It changes no C
;;; and no Scheme.  It re-measures the surface, runs the gates, and
;;; records.  This corpus pins the end state against the tree, so a
;;; stale number or a missing registration fails the run.
;;;
;;; It pins:
;;;   S1 -- the surface of brief.org section 4, re-measured at HEAD:
;;;         src/fileio.c (7,575 lines, 78 DEFUNs, 27 scm_c_public_ref
;;;         sites, 26 --fileio-* leaves, 0 OPEN markers);
;;;         mod/emacs/fileio.scm (370); the tree-wide scm_c_public_ref
;;;         over src/*.[chm] (227 after M48 imp-4); src/keyboard.c (11,233 / 447);
;;;         src/keyboard-globals.c (490); the combined keyboard surface
;;;         (11,723); the margin (237 under the 11,960 M31 budget);
;;;         and the budget itself.  The M31 keyboard surface did not
;;;         move in M47.
;;;   S2 -- the registration: the corpus is registered in the (m47)
;;;         group of tool/run-tests.scm after test-m47-imp5.el
;;;         (brief.org section 5).  Read tool/run-tests.scm only.
;;;   S3 -- the guards: the per-group min-count guard, and the
;;;         group-total check.  The total check is an `ert-deftest', so
;;;         its body runs after every corpus of the group has loaded and
;;;         sees them all, whatever order tool/run-tests.scm picked.
;;;
;;; This corpus reads TRACKED files only (src/, mod/, tool/).  It does
;;; NOT read docs/ (docs/kb.org test-must-not-read-docs): a gitignored
;;; or untracked record can only pass or skip, so a record check proves
;;; nothing.  It does NOT run a nested m47 gate subprocess (the M46
;;; corpus explains why; the in-process `ert-deftest' replaces it).
;;;
;;; A read error is a real error, never a silent pass.  An absent src/
;;; file is a real error.

(princ "=== m47 imp-6 close-out suite ===\n")

(require 'imp-ert-report)

(defvar m47-imp6--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))

(defvar m47-imp6--m31-budget 11960
  "The M31 keyboard-surface budget in lines (brief.org section 4).")

(defvar m47-imp6--registered 0
  "Total number of tracked-file checks this corpus has registered.")

(defvar m47-imp6--group nil
  "The group that `m47-imp6--check' counts into: `s1', `s2', or nil.")

(defvar m47-imp6--counts nil
  "Alist of (GROUP . COUNT) for the registered tracked-file checks.")

(defun m47-imp6--group-count (group)
  "Number of tracked-file checks registered so far in GROUP."
  (or (cdr (assq group m47-imp6--counts)) 0))

(defun m47-imp6--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
the symbol `m47-imp6-absent' when REL does not exist."
  (let ((path (expand-file-name rel m47-imp6--root)))
    (if (not (file-exists-p path))
        'm47-imp6-absent
      (with-temp-buffer
        (insert-file-contents path)
        (funcall fn)))))

(defun m47-imp6--contains-p (rel needle)
  "Non-nil when REL (repo-root-relative) contains NEEDLE."
  (m47-imp6--with rel
    (lambda ()
      (goto-char (point-min))
      (search-forward needle nil t))))

(defun m47-imp6--lines (rel)
  "Count the newlines of REL the way `wc -l' does."
  (m47-imp6--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (search-forward "\n" nil t) (setq n (1+ n)))
        n))))

(defun m47-imp6--count (rel regexp)
  "Count the matches of REGEXP in REL."
  (m47-imp6--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (re-search-forward regexp nil t) (setq n (1+ n)))
        n))))

(defun m47-imp6--line-of (rel needle)
  "1-based line number of the first literal NEEDLE in REL, or nil."
  (m47-imp6--with rel
    (lambda ()
      (goto-char (point-min))
      (when (search-forward needle nil t)
        (line-number-at-pos (match-beginning 0))))))

(defun m47-imp6--count-scm-ref ()
  "Count scm_c_public_ref over src/*.[chm] (the brief.org section 4 measure)."
  (let ((total 0)
        (dir (expand-file-name "src" m47-imp6--root)))
    (dolist (f (directory-files dir t "\\.[chm]\\'"))
      (setq total (+ total (or (m47-imp6--count f "scm_c_public_ref") 0))))
    total))

(defun m47-imp6--check (name ok)
  "Report and register one check on a TRACKED file.  OK is a boolean.
An absent src/ file makes the reader return the symbol
`m47-imp6-absent'.  The absent branch prints FAIL AND registers a real
FAILING ERT test, so an absent src/ file is a real error, not a pass:
the harness parses ERT's batch output for its exit code, so a princ'd
FAIL with no ERT test would leave the exit code 0 (cr.org finding
4.2.5)."
  (if (eq ok 'm47-imp6-absent)
      (progn
        (princ (format "FAIL m47/imp6/%s (source file absent)\n" name))
        (imp-register-bool-as-ert-test (format "m47-imp6/%s" name) nil)
        (setq m47-imp6--registered (1+ m47-imp6--registered))
        (when m47-imp6--group
          (let ((cell (assq m47-imp6--group m47-imp6--counts)))
            (if cell
                (setcdr cell (1+ (cdr cell)))
              (push (cons m47-imp6--group 1) m47-imp6--counts)))))
    (progn
      (princ (format "%s m47/imp6/%s\n" (if ok "PASS" "FAIL") name))
      (setq m47-imp6--registered (1+ m47-imp6--registered))
      (when m47-imp6--group
        (let ((cell (assq m47-imp6--group m47-imp6--counts)))
          (if cell
              (setcdr cell (1+ (cdr cell)))
            (push (cons m47-imp6--group 1) m47-imp6--counts))))
      (imp-register-bool-as-ert-test (format "m47-imp6/%s" name) (and ok t)))))

;;; --- S1. The surface (brief.org section 4) --------------------------

(setq m47-imp6--group 's1)

(m47-imp6--check "fileio.c-lines-7575"
                 (eql 7575 (m47-imp6--lines "src/fileio.c")))
(m47-imp6--check "fileio.c-defuns-78"
                 (eql 78 (m47-imp6--count "src/fileio.c" "^DEFUN (\"")))
(m47-imp6--check "fileio.c-refs-27"
                 (eql 27 (m47-imp6--count "src/fileio.c" "scm_c_public_ref")))
(m47-imp6--check "fileio.c-leaves-26"
                 (eql 26 (m47-imp6--count "src/fileio.c" "^DEFUN (\"--fileio-")))
;; The G1 / G2 / G3 OPEN-leaf value is 0 / 0 / 0.  All three groups'
;; leaves live in src/fileio.c, so a zero marker count in that file is
;; exactly 0 / 0 / 0.  The pattern matches ANY `OPEN (cr.org <tag>)'
;; marker, not one tag: a future marker with a different F tag must also
;; fail this check (cr.org finding 4.2.4).
(m47-imp6--check "fileio.c-open-leaves-0-0-0"
                 (eql 0 (m47-imp6--count "src/fileio.c" "OPEN (cr\\.org")))
(m47-imp6--check "fileio.scm-lines-370"
                 (eql 370 (m47-imp6--lines "mod/emacs/fileio.scm")))
(m47-imp6--check "tree-wide-scm-public-ref-268"
                 (eql 268 (m47-imp6--count-scm-ref)))
(m47-imp6--check "keyboard.c-lines-11233"
                 (eql 11233 (m47-imp6--lines "src/keyboard.c")))
(m47-imp6--check "keyboard.c-defuns-447"
                 (eql 447 (m47-imp6--count "src/keyboard.c" "^DEFUN (\"")))
(m47-imp6--check "keyboard-globals.c-lines-490"
                 (eql 490 (m47-imp6--lines "src/keyboard-globals.c")))
(m47-imp6--check "combined-keyboard-surface-11723"
                 (let ((kb (m47-imp6--lines "src/keyboard.c"))
                       (kg (m47-imp6--lines "src/keyboard-globals.c")))
                   (and (integerp kb) (integerp kg)
                        (eql 11723 (+ kb kg)))))
(m47-imp6--check "keyboard-margin-237-under-budget"
                 (let ((kb (m47-imp6--lines "src/keyboard.c"))
                       (kg (m47-imp6--lines "src/keyboard-globals.c")))
                   (and (integerp kb) (integerp kg)
                        (eql 237 (- 11960 (+ kb kg))))))
(m47-imp6--check "m31-budget-11960"
                 (eql 11960 m47-imp6--m31-budget))

;;; --- S2. The corpus is registered (brief.org section 5) -------------

(setq m47-imp6--group 's2)

(m47-imp6--check "run-tests-m47-imp6"
                 (m47-imp6--contains-p "tool/run-tests.scm"
                                       "test/m47/test-m47-imp6.el"))
(m47-imp6--check "run-tests-m47-imp6-after-imp5"
                 (let ((imp5 (m47-imp6--line-of "tool/run-tests.scm"
                                                "test/m47/test-m47-imp5.el"))
                       (imp6 (m47-imp6--line-of "tool/run-tests.scm"
                                                "test/m47/test-m47-imp6.el")))
                   (and (integerp imp5) (integerp imp6) (< imp5 imp6))))

;;; --- S3. The per-group min-count guard (brief.org section 5) --------

;; An --filter that matches no group already reports exit 0 with 0
;; tests, so a green m47 gate proves nothing until the corpus exists and
;; its checks really register.  These guards fail when the corpus body is
;; truncated or its core checks do not run.  The counts are stable
;; because every check is registered at load time.  S1 holds 13 checks;
;; S2 holds 2.

(setq m47-imp6--group nil)

(m47-imp6--check "reg/min-s1-checks-13"
                 (>= (m47-imp6--group-count 's1) 13))
(m47-imp6--check "reg/min-s2-checks-2"
                 (>= (m47-imp6--group-count 's2) 2))
(m47-imp6--check "reg/min-total-18"
                 (>= (1+ m47-imp6--registered) 18))

;; A read error must be a real FAIL, not a printed one (cr.org finding
;; 4.2.5).  Drive the read-error branch of `m47-imp6--check' with the
;; absent sentinel under a throwaway name, then assert the branch
;; registered a REAL ERT test whose body FAILS.  This is what makes the
;; harness exit non-zero on an absent src/ file; a princ'd FAIL alone
;; would leave the exit code 0.  `ert-make-test-unbound' removes the
;; throwaway so it never runs in the gate, and the `let' restores the
;; `m47-imp6--registered' total so the min-count guards above stay exact.
(m47-imp6--check "reg/absent-path-registers-failing-ert"
                 (let* ((m47-imp6--registered m47-imp6--registered)
                        (probe "reg/absent-registration-probe")
                        (sym (intern (format "m47-imp6/%s" probe))))
                   (prog1
                       (progn
                         (m47-imp6--check probe 'm47-imp6-absent)
                         (and (ert-test-boundp sym)
                              (condition-case nil
                                  (progn (funcall (ert-test-body
                                                   (ert-get-test sym)))
                                         nil)
                                (error t))))
                     (ert-make-test-unbound sym))))

;;; --- The group-total check (brief.org section 5) --------------------

;; The M46 S3 subprocess was replaced by an in-process `ert-deftest' (the
;; M46 corpus explains why: a nested run doubled the group).  ERT runs
;; every test after all six m47 corpora have loaded, so a test BODY sees
;; the whole group's registered tests whatever order tool/run-tests.scm
;; loaded the files in -- it randomises them, so a load-time count could
;; not do this.
;;
;; The floor is measured from a real run, not from the stale per-corpus
;; minimums of brief.org section 5.  The m47 group registers 560 ERT
;; tests at imp-6 (imp-1 62, imp-2 129, imp-3 95, imp-4 143, imp-5 111,
;; imp-6 20; cr.org section 3).  The only tests that can legitimately
;; drop are the gated runtime probes, which register nothing under
;; GUILEMACS_M47_GATE: imp-2 3, imp-3 8, imp-4 11, imp-5 8 -- 30 in all.
;; 560 - 30 = 530.  The floor is the measured total minus the skippable
;; probes, so it holds whether or not the probes run, yet it is tight:
;; the loss of any static check now fails (cr.org finding 4.2.2).  The
;; corpus reads no docs/, so the total does not depend on docs/.

(defvar m47-imp6--min-gate-total 530
  "The minimum number of ERT tests the m47 group registers.")

(ert-deftest m47-imp6/gate-m47-total ()
  "The m47 group registers at least its docs-independent floor."
  (should (>= (length (ert-select-tests "^m47-imp" t))
              m47-imp6--min-gate-total)))

(princ (format "=== m47 imp-6 close-out suite done (%d tracked checks; s1 %d, s2 %d) ===\n"
               m47-imp6--registered
               (m47-imp6--group-count 's1)
               (m47-imp6--group-count 's2)))
