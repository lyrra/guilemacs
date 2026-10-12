;;; test-m50-imp5.el --- M50 imp-5 close-out corpus (re-measure and record).
;;;
;;; M50 imp-5 is the close-out (brief.org section 1).  It changes no C
;;; and no Scheme: the net C delta is 0 and the net Scheme delta is 0.
;;; It re-measures the surface, runs the gates, and records the result.
;;; This corpus pins the end state against the tree, so a stale number
;;; or a missing registration fails the run.
;;;
;;; It pins three groups, S1 .. S3:
;;;
;;;   S1 -- the surface of brief.org section 3, re-measured at HEAD:
;;;         src/emacs.c (3,441 lines, 5 ^DEFUN (" blocks, 6
;;;         scm_c_public_ref sites, 3 FIX-20261006-guilemacs marks, the
;;;         guile.h include at :37 -- the one DELIBERATE line-number pin
;;;         in S1 (brief.org section 3 row 5; see the row-5 note) -- and
;;;         the two deleted imp-3 leaf
;;;         tokens absent); mod/emacs/emacs.scm (47 lines and the one
;;;         #:export name (emacs-daemonp)); prelude/load.scm holds
;;;         (use-modules (emacs emacs)); the ordered 5-block name list
;;;         (invocation-name, invocation-directory, kill-emacs, daemonp,
;;;         daemon-initialized); and the tree-wide scm_c_public_ref
;;;         count over src/*.[chm] (260).  S1 holds 12 checks.
;;;   S2 -- the registration: the corpus is registered in the (m50)
;;;         group of tool/run-tests.scm after test-m50-imp4.el
;;;         (brief.org section 6).  Read tool/run-tests.scm only.  S2
;;;         holds 2 checks.
;;;   S3 -- the guards: a per-group min-count guard for S1 and one for
;;;         S2, and the group-total check.  The total check is an
;;;         `ert-deftest', so its body runs after every corpus of the
;;;         group has loaded and sees them all, whatever order
;;;         tool/run-tests.scm picked.
;;;
;;; This corpus reads TRACKED files only (src/, mod/, prelude/, tool/).
;;; It does NOT read docs/ (docs/kb.org test-must-not-read-docs): a
;;; gitignored or untracked record can only pass or skip, so a record
;;; check proves nothing.  It does NOT run a nested m50 gate subprocess.
;;; The in-process `ert-deftest' replaces a nested gate.
;;;
;;; A read error is a real error, never a silent pass.  An absent src/
;;; file is a real FAIL, not a pass (brief.org section 4).  Every check
;;; registers a real ERT test via imp-register-bool-as-ert-test, so the
;;; harness parses the ERT output and the exit code is correct: a
;;; princ'd FAIL with no ERT test would leave the exit code 0.
;;;
;;; The runtime probe (brief.org section 5) is gated on a built
;;; src/emacs: an absent binary is an INFO skip, and a probe error is a
;;; FAIL, never a silent pass
;;; (m4x-probe-failure-must-not-read-as-a-skip).  The probe asserts
;;; (eq (daemonp) nil) and (not (eq (daemonp) t)) in a --batch run: the
;;; result is the elisp nil (#nil), not the Scheme #f.

(princ "=== m50 imp-5 close-out suite ===\n")

(require 'imp-ert-report)

(defvar m50-imp5--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))

(defvar m50-imp5--registered 0
  "Total number of tracked-file checks this corpus has registered.")

(defvar m50-imp5--group nil
  "The group that `m50-imp5--check' counts into: `s1', `s2', or nil.")

(defvar m50-imp5--counts nil
  "Alist of (GROUP . COUNT) for the registered tracked-file checks.")

(defun m50-imp5--group-count (group)
  "Number of tracked-file checks registered so far in GROUP."
  (or (cdr (assq group m50-imp5--counts)) 0))

(defun m50-imp5--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
the symbol `m50-imp5-absent' when REL does not exist."
  (let ((path (expand-file-name rel m50-imp5--root)))
    (if (not (file-exists-p path))
        'm50-imp5-absent
      (with-temp-buffer
        (insert-file-contents path)
        (funcall fn)))))

(defun m50-imp5--contains-p (rel needle)
  "Non-nil when the TRACKED file REL (repo-root-relative) contains NEEDLE.
An absent file folds to nil, so `m50-imp5--check' prints FAIL: an absent
src/ file is a real error, not a pass (brief.org section 4)."
  (let ((hit (m50-imp5--with rel
               (lambda ()
                 (goto-char (point-min))
                 (search-forward needle nil t)))))
    (and (not (eq hit 'm50-imp5-absent)) (and hit t))))

(defun m50-imp5--token-absent (rel needle)
  "Return t when the TRACKED file REL exists and lacks NEEDLE.  Return
the symbol `m50-imp5-absent' when REL is absent, so `m50-imp5--check'
prints FAIL.  The distinction matters: an absent src/ file must not read
as a PASS for an absence check (brief.org section 4)."
  (m50-imp5--with rel
    (lambda ()
      (goto-char (point-min))
      (not (search-forward needle nil t)))))

(defun m50-imp5--export-p (rel name)
  "Non-nil when the `#:export' form of REL (repo-root-relative) names NAME.
The search is confined to the balanced `#:export' list, so a NAME that
only appears in a comment, a body, or a `defelisp' line does not count
(brief.org section 4.1).  An absent file folds to nil."
  (let ((hit (m50-imp5--with rel
               (lambda ()
                 (goto-char (point-min))
                 (when (search-forward "#:export" nil t)
                   (skip-chars-forward " \t\n")
                   (when (looking-at "(")
                     (let ((start (point)))
                       (forward-list)
                       (let ((limit (point)))
                         (goto-char start)
                         (search-forward name limit t)))))))))
    (and (not (eq hit 'm50-imp5-absent)) (and hit t))))

(defun m50-imp5--lines (rel)
  "Count the newlines of REL the way `wc -l' does."
  (m50-imp5--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (search-forward "\n" nil t) (setq n (1+ n)))
        n))))

(defun m50-imp5--count (rel regexp)
  "Count the matches of REGEXP in REL."
  (m50-imp5--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (re-search-forward regexp nil t) (setq n (1+ n)))
        n))))

(defun m50-imp5--line-of (rel needle)
  "1-based line number of the first literal NEEDLE in REL, or nil."
  (m50-imp5--with rel
    (lambda ()
      (goto-char (point-min))
      (when (search-forward needle nil t)
        (line-number-at-pos (match-beginning 0))))))

(defun m50-imp5--count-scm-ref ()
  "Count scm_c_public_ref over src/*.[chm] (the brief.org section 3 measure)."
  (let ((total 0)
        (dir (expand-file-name "src" m50-imp5--root)))
    (dolist (f (directory-files dir t "\\.[chm]\\'"))
      (setq total (+ total (or (m50-imp5--count f "scm_c_public_ref") 0))))
    total))

(defun m50-imp5--defun-names (rel)
  "The DEFUN names of REL, in file order.  A name that starts with two
hyphens is a typed --emacs-* leaf, not one of the 5 policy blocks, so
it is skipped.  No typed leaf remains at imp-5, so the list is the 5
block names.  An absent file folds to the `absent' symbol, so the
`equal' check FAILs."
  (m50-imp5--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((names '()))
        (while (re-search-forward "^DEFUN (\"\\([^\"]+\\)\"" nil t)
          (let ((name (match-string 1)))
            (unless (string-prefix-p "--" name)
              (push name names))))
        (nreverse names)))))

(defun m50-imp5--check (name ok)
  "Report and register one check on a TRACKED file.  OK is a boolean.
The count callers pass `(eql N value)': when the source file is absent
the reader returns the symbol `m50-imp5-absent', so `eql' yields nil
and this prints FAIL.  When OK is the symbol `m50-imp5-absent' itself
the file is absent, and this prints FAIL too.  Either way this
registers a real FAILING ERT test, so an absent src/ file is a real
error, not a pass: the harness parses ERT's batch output for its exit
code, so a princ'd FAIL with no ERT test would leave the exit code 0
(brief.org section 4)."
  (let* ((absent (eq ok 'm50-imp5-absent))
         (pass (and (not absent) (and ok t))))
    (if absent
        (princ (format "FAIL m50/imp5/%s (source file absent)\n" name))
      (princ (format "%s m50/imp5/%s\n" (if pass "PASS" "FAIL") name)))
    (setq m50-imp5--registered (1+ m50-imp5--registered))
    (when m50-imp5--group
      (let ((cell (assq m50-imp5--group m50-imp5--counts)))
        (if cell
            (setcdr cell (1+ (cdr cell)))
          (push (cons m50-imp5--group 1) m50-imp5--counts))))
    (imp-register-bool-as-ert-test (format "m50-imp5/%s" name) pass)))

;;; --- S1. The surface (brief.org section 3) --------------------------

;; One check per brief.org section 3 value row (rows 1 .. 11), plus the
;; ordered 5-block name list.  So S1 holds 12 checks.

(setq m50-imp5--group 's1)

;; Row 1: src/emacs.c lines = 3,441.
(m50-imp5--check "emacs.c-lines-3441"
                 (eql 3441 (m50-imp5--lines "src/emacs.c")))
;; Row 2: src/emacs.c ^DEFUN (" count = 5.
(m50-imp5--check "emacs.c-defun-count-5"
                 (eql 5 (m50-imp5--count "src/emacs.c" "^DEFUN (\"")))
;; Row 3: src/emacs.c scm_c_public_ref sites = 6.
(m50-imp5--check "emacs.c-scm-ref-6"
                 (eql 6 (m50-imp5--count "src/emacs.c" "scm_c_public_ref")))
;; Row 4: the FIX-20261006-guilemacs marks = 3.
(m50-imp5--check "emacs.c-fix-marks-3"
                 (eql 3 (m50-imp5--count "src/emacs.c"
                                         "FIX-20261006-guilemacs")))
;; Row 5: the guile.h include at :37.  This is the ONE line-number pin
;; in S1, and it is DELIBERATE: the value reproduces brief.org section
;; 3 row 5, and the M48 / M49 close-out corpora pin their include line
;; the same way (a close-out is a snapshot at a fixed base).  The
;; brief's "pin names, not line numbers" rule governs the block list
;; (row 12), which pins the ordered names instead.  A later imp that
;; adds a line above :37 must re-measure this deliberate pin: a stale
;; value is a real FAIL, and this check does not widen or drop.
(m50-imp5--check "emacs.c-guile.h-at-37"
                 (eql 37 (m50-imp5--line-of "src/emacs.c"
                                            "#include \"guile.h\"")))
;; Row 6: the token --emacs-daemon-state is absent (the imp-3 deleted leaf).
(m50-imp5--check "leaf-token-absent"
                 (m50-imp5--token-absent "src/emacs.c"
                                         "--emacs-daemon-state"))
;; Row 7: the token Femacs_daemon_state is absent (the imp-3 deleted leaf).
(m50-imp5--check "leaf-fname-token-absent"
                 (m50-imp5--token-absent "src/emacs.c"
                                         "Femacs_daemon_state"))
;; Row 8: mod/emacs/emacs.scm lines = 47.
(m50-imp5--check "emacs.scm-lines-47"
                 (eql 47 (m50-imp5--lines "mod/emacs/emacs.scm")))
;; Row 9: the one #:export name of the boundary module.
(m50-imp5--check "emacs.scm-export-daemonp"
                 (m50-imp5--export-p "mod/emacs/emacs.scm" "emacs-daemonp"))
;; Row 10: prelude/load.scm holds (use-modules (emacs emacs)).
(m50-imp5--check "load.scm-use-modules"
                 (m50-imp5--contains-p "prelude/load.scm"
                                       "(use-modules (emacs emacs))"))
;; Row 11: the tree-wide scm_c_public_ref count over src/*.[chm] = 260.
(m50-imp5--check "tree-wide-scm-public-ref-260"
                 (eql 260 (m50-imp5--count-scm-ref)))
;; The ordered 5-block name list equals the src/emacs.c DEFUN names.
(m50-imp5--check "block-list-exact-5"
                 (equal '("invocation-name"
                          "invocation-directory"
                          "kill-emacs"
                          "daemonp"
                          "daemon-initialized")
                        (m50-imp5--defun-names "src/emacs.c")))

;;; --- S2. The corpus is registered (brief.org section 6) -------------

(setq m50-imp5--group 's2)

(m50-imp5--check "run-tests-m50-imp5"
                 (m50-imp5--contains-p "tool/run-tests.scm"
                                       "test/m50/test-m50-imp5.el"))
(m50-imp5--check "run-tests-m50-imp5-after-imp4"
                 (let ((imp4 (m50-imp5--line-of "tool/run-tests.scm"
                                                "test/m50/test-m50-imp4.el"))
                       (imp5 (m50-imp5--line-of "tool/run-tests.scm"
                                                "test/m50/test-m50-imp5.el")))
                   (and (integerp imp4) (integerp imp5) (< imp4 imp5))))

;;; --- S3. The guards (brief.org section 4.3) -------------------------

;; An --filter that matches no group already reports exit 0 with 0
;; tests, so a green m50 gate proves nothing until the corpus exists and
;; its checks really register.  These guards fail when the corpus body
;; is truncated or its core checks do not run.  The counts are stable
;; because every check is registered at load time.  S1 holds 12 checks;
;; S2 holds 2 checks.

(setq m50-imp5--group nil)

(m50-imp5--check "reg/min-s1-checks-12"
                 (>= (m50-imp5--group-count 's1) 12))
(m50-imp5--check "reg/min-s2-checks-2"
                 (>= (m50-imp5--group-count 's2) 2))

;;; --- The group-total check (brief.org section 4.3) ------------------

;; A nested m50 gate subprocess is replaced by an in-process
;; `ert-deftest'.  ERT runs every test after all five m50 corpora have
;; loaded, so this body sees the whole group's registered tests whatever
;; order tool/run-tests.scm loaded the files in.
;;
;; The floor is measured from a real run, not from the stale per-corpus
;; minimums.  The m50 group registers N ERT tests at imp-5 (imp-1 ..
;; imp-4 plus imp-5).  The only tests that can legitimately drop are the
;; gated runtime probes in imp-3, imp-4, and imp-5, which register
;; nothing when no built src/emacs exists.  The floor is the measured
;; total minus those 6 probes, so it holds whether or not the probes
;; run.
;;
;; This is a coarse net, not a tight bound.  The per-corpus reg/min-*
;; guards are the tight per-corpus check; this deftest only catches a
;; whole-corpus or load-order loss.  The corpus reads no docs/, so the
;; total does not depend on docs/.

(defvar m50-imp5--min-gate-total 119
  "The minimum number of ERT tests the m50 group registers: the measured
total (125) minus the 6 gated runtime probes of imp-3, imp-4, and imp-5.")

(ert-deftest m50-imp5/gate-m50-total ()
  "The m50 group registers at least its docs-independent floor."
  (should (>= (length (ert-select-tests "^m50-imp" t))
              m50-imp5--min-gate-total)))

;;; --- The gated runtime probe (brief.org section 5) ------------------

;; The (m50) group carries no `prelude' key, so tool/run-tests.scm loads
;; these files with run-tests-loadup-emacs, which is "../src/emacs ...
;; -l <file> --batch".  A probe therefore calls the hub `daemonp'
;; DIRECTLY, in this process.
;;
;; An absent built binary is an INFO-skip.  A signalled error is a FAIL,
;; never a silent pass; the error is printed so the cause is visible.

(defun m50-imp5--probe (tag thunk)
  "Register the probe TAG from the value of THUNK, which calls `daemonp'.
A non-nil value is a PASS.  A signalled error is a FAIL, never a silent
pass; the error is printed so the cause is visible."
  (m50-imp5--check
   (format "probe/%s" tag)
   (condition-case err
       (and (funcall thunk) t)
     (error (princ (format "INFO m50/imp5/%s error=%S\n" tag err))
            nil))))

(if (not (file-exists-p (expand-file-name "src/emacs" m50-imp5--root)))
    (princ "INFO m50/imp5/runtime-probes skipped (no built src/emacs)\n")
  (m50-imp5--probe
   "daemonp-nondaemon-nil"
   (lambda ()
     ;; A --batch run is not a daemon, so `daemonp' returns nil.
     (eq (daemonp) nil)))
  (m50-imp5--probe
   "daemonp-nondaemon-not-false"
   (lambda ()
     ;; The result is the elisp nil (#nil), not the Scheme #f, and it is
     ;; not t.  A #f slip in the policy would cross back as a non-nil
     ;; value, so assert the exact nil (brief.org section 5).
     (and (eq (daemonp) nil)
          (not (eq (daemonp) t))))))

(princ (format "=== m50 imp-5 close-out suite done (%d tracked checks; s1 %d, s2 %d) ===\n"
               m50-imp5--registered
               (m50-imp5--group-count 's1)
               (m50-imp5--group-count 's2)))
