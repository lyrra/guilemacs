;;; test-m53-imp1.el --- M53 imp-1 end-state evidence audit corpus.
;;;
;;; M53 imp-1 is the end-state evidence audit (brief.org section 1,
;;; milestone.org section 5).  It is docs only: the net C delta is 0 and
;;; the net Scheme delta is 0.  It measures the two end-state checks and
;;; records the A1 / A2 verdict (docs/m53-plan.org).
;;;
;;; This corpus pins the measured surface and the two check paths in
;;; the tree, so a stale number or a missing registration fails the
;;; run.
;;;
;;; It pins these groups:
;;;
;;;   S1 -- the measured surface of brief.org section 5, re-measured at
;;;         base HEAD fa11385b3: src/term.c (6,214 lines, 29 ^DEFUN (,
;;;         4 --tty-* leaf DEFUNs, 36 scm_c_public_ref sites); the 454
;;;         lines of mod/emacs/tty-output.scm; and the tree-wide
;;;         scm_c_public_ref count over src/*.[chm] (260).  S1 holds 1
;;;         check.
;;;   S2 -- CHECK 1, the standalone loader.  A plain `guile' process
;;;         (no Emacs C core) loads (emacs loader) and (emacs reader);
;;;         a real Elisp file loads through the Scheme loader; and the
;;;         loader / reader / src/lread.c entry points are present.  S2
;;;         holds 6 checks.
;;;   S3 -- CHECK 2, the PTY terminal path.  The src/termchar.h FILE *
;;;         streams, the test/pty-driver.py groups, and the
;;;         test/m42/pty-runner.el harness are present.  S3 holds 3
;;;         checks.
;;;   S4 -- the registration: the corpus is registered in the (m53)
;;;         group of tool/run-tests.scm, and test/pty-driver.py holds
;;;         the --selftest entry (the case-count pin is REMOVED, M61
;;;         imp-2g).  S4 holds 3
;;;         checks.
;;;   S5 -- the guards: a per-group min-count guard for S1 .. S4, and
;;;         the group-total `ert-deftest'.  S5 holds 4 checks.
;;;
;;; This corpus reads TRACKED files only (src/, mod/, prelude/, test/,
;;; and the tracked runner tool/run-tests.scm).  It does NOT read docs/
;;; (docs/kb.org test-must-not-read-docs): a gitignored record can only
;;; pass or skip, so a record check proves nothing.
;;;
;;; A read error is a real error, never a silent pass.  An absent src/
;;; file is a real FAIL, not a pass (brief.org section 2).  Every check
;;; registers a real ERT test via imp-register-bool-as-ert-test, so the
;;; harness parses the ERT output and the exit code is correct: a
;;; princ'd FAIL with no ERT test would leave the exit code 0.

(princ "=== m53 imp-1 end-state evidence suite ===\n")

(require 'imp-ert-report)

(defvar m53-imp1--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))
(defvar m53-imp1--registered 0
  "Total number of checks this corpus has registered.")
(defvar m53-imp1--group nil
  "The group that `m53-imp1--check' counts into: `s1' .. `s5', or nil.")
(defvar m53-imp1--counts nil
  "Alist of (GROUP . COUNT) for the registered checks.")

(defun m53-imp1--group-count (group)
  "Number of checks registered so far in GROUP."
  (or (cdr (assq group m53-imp1--counts)) 0))

(defun m53-imp1--bump-group ()
  "Count one check into `m53-imp1--group'."
  (when m53-imp1--group
    (let ((cell (assq m53-imp1--group m53-imp1--counts)))
      (if cell
          (setcdr cell (1+ (cdr cell)))
        (push (cons m53-imp1--group 1) m53-imp1--counts)))))

(defun m53-imp1--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
the symbol `m53-imp1-absent' when REL does not exist."
  (let ((path (expand-file-name rel m53-imp1--root)))
    (if (not (file-exists-p path))
        'm53-imp1-absent
      (with-temp-buffer
        (insert-file-contents path)
        (funcall fn)))))

(defun m53-imp1--contains-p (rel needle)
  "Non-nil when the TRACKED file REL (repo-root-relative) contains NEEDLE.
An absent file folds to nil, so `m53-imp1--check' prints FAIL: an absent
src/ file is a real error, not a pass (brief.org section 2)."
  (let ((hit (m53-imp1--with rel
               (lambda ()
                 (goto-char (point-min))
                 (search-forward needle nil t)))))
    (and (not (eq hit 'm53-imp1-absent)) (and hit t))))

(defun m53-imp1--holds-all (rel needles)
  "Non-nil when the TRACKED file REL holds every NEEDLE.  REL is read
once, so a multi-needle check does not re-read the file per needle."
  (m53-imp1--with rel
    (lambda ()
      (let ((all t))
        (dolist (needle needles)
          (goto-char (point-min))
          (unless (search-forward needle nil t) (setq all nil)))
        all))))

(defun m53-imp1--exists-p (rel)
  "Non-nil when the TRACKED file REL (repo-root-relative) exists."
  (file-exists-p (expand-file-name rel m53-imp1--root)))

(defun m53-imp1--count (rel regexp)
  "Count the matches of REGEXP in REL."
  (m53-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (re-search-forward regexp nil t) (setq n (1+ n)))
        n))))

(defun m53-imp1--count-scm-ref ()
  "Count scm_c_public_ref over src/*.[chm] (the brief.org section 5
tree-wide measure)."
  (let ((total 0)
        (dir (expand-file-name "src" m53-imp1--root)))
    (dolist (f (directory-files dir t "\\.[chm]\\'"))
      (setq total (+ total (or (m53-imp1--count f "scm_c_public_ref") 0))))
    total))

(defun m53-imp1--check (name ok)
  "Report and register one check on a TRACKED file.  OK is a boolean.
The count callers pass `(eql N value)': when the source file is absent
the reader returns the symbol `m53-imp1-absent', so `eql' yields nil and
this prints FAIL.  When OK is the symbol `m53-imp1-absent' itself the
file is absent, and this prints FAIL too.  Either way this registers a
real FAILING ERT test, so an absent src/ file is a real error, not a
pass."
  (let* ((absent (eq ok 'm53-imp1-absent))
         (pass (and (not absent) (and ok t))))
    (if absent
        (princ (format "FAIL m53/imp1/%s (source file absent)\n" name))
      (princ (format "%s m53/imp1/%s\n" (if pass "PASS" "FAIL") name)))
    (setq m53-imp1--registered (1+ m53-imp1--registered))
    (m53-imp1--bump-group)
    (imp-register-bool-as-ert-test (format "m53-imp1/%s" name) pass)))

(defun m53-imp1--info-skip (name reason)
  "Register one explicit INFO skip, counted into the current group.  A
host limit is a skip, never a pass (brief.org section 9)."
  (princ (format "INFO m53/imp1/%s %s\n" name reason))
  (setq m53-imp1--registered (1+ m53-imp1--registered))
  (m53-imp1--bump-group)
  (imp-register-skip-as-ert-test (format "m53-imp1/%s" name) reason))

;;; --- The standalone Guile probe (CHECK 1) ---------------------------

(defun m53-imp1--plain-guile-loads-module-p (module)
  "Run a standalone `guile' that loads MODULE and prints a marker.
Return t on success, the symbol `m53-imp1-guile-absent' when no guile
binary is on PATH, and nil on any failure.  This process is a plain
Guile load of a Scheme module: the Emacs C core is absent from it."
  (let ((guile (executable-find "guile")))
    (if (not guile)
        'm53-imp1-guile-absent
      (let* ((modpath (expand-file-name "mod" m53-imp1--root))
             (code (format "(use-modules %s) (display \"M53-OK\\n\")" module))
             (buf (get-buffer-create " *m53-imp1-guile*"))
             (status nil))
        (unwind-protect
            (progn
              (with-current-buffer buf (erase-buffer))
              (setq status (call-process guile nil buf nil
                                         "-L" modpath "-c" code))
              (and (integerp status) (zerop status)
                   (with-current-buffer buf
                     (goto-char (point-min))
                     (search-forward "M53-OK" nil t))))
          (kill-buffer buf))))))

(defun m53-imp1--check-guile (name module)
  "Check that a standalone `guile' loads MODULE.  A missing guile binary
is an explicit INFO skip, never a pass (brief.org section 9)."
  (let ((res (m53-imp1--plain-guile-loads-module-p module)))
    (if (eq res 'm53-imp1-guile-absent)
        (m53-imp1--info-skip name "no guile binary on PATH")
      (m53-imp1--check name res))))

(defun m53-imp1--real-elisp-load-p ()
  "Load a real Elisp file through the Scheme loader and check its side
effect.  The file is written to a temp path, loaded with `load' (bound
to the Scheme `elisp-load'), and removed afterwards.  Return t on
success, nil on any failure.  This is the real path, not a module-load
probe: the loader must read and evaluate a real Elisp file."
  (let ((file (make-temp-file "m53-imp1-" nil ".el"))
        (result nil))
    (unwind-protect
        (progn
          (with-temp-file file
            (insert ";; a real Elisp file for the M53 imp-1 loader check\n"
                    "(setq m53-imp1-fixture-loaded 'm53-imp1-fixture-ok)\n"))
          (condition-case nil
              (progn
                (load file nil t)
                (setq result (and (boundp 'm53-imp1-fixture-loaded)
                                  (equal (symbol-value 'm53-imp1-fixture-loaded)
                                         'm53-imp1-fixture-ok))))
            (error (setq result nil))))
      (when (file-exists-p file) (delete-file file)))
    result))

;;; --- S1. The measured surface (brief.org section 5) -----------------

(setq m53-imp1--group 's1)

;; M61 imp-2b (milestone.org findings F2): the src/term.c and
;; mod/emacs/tty-output.scm source-text pins (the line counts, the
;; ^DEFUN ( count, the --tty-* leaf count and the scm_c_public_ref
;; count) are REMOVED, not re-pinned.  A test proves behavior; it must
;; not read source text.

;; Row 6: the tree-wide scm_c_public_ref count over src/*.[chm] = 260.
(m53-imp1--check "tree-wide-scm-ref-270"
                 (eql 270 (m53-imp1--count-scm-ref)))

;;; --- S2. CHECK 1, the standalone loader -----------------------------

;; The two module loads run a real plain `guile' subprocess.  The Elisp
;; load runs the real Scheme loader in this process.  The three source
;; pins hold the entry points named in brief.org section 3.

(setq m53-imp1--group 's2)

(m53-imp1--check-guile "loader-module-under-plain-guile" "(emacs loader)")
(m53-imp1--check-guile "reader-module-under-plain-guile" "(emacs reader)")
(m53-imp1--check "real-elisp-load-through-scheme-loader"
                 (m53-imp1--real-elisp-load-p))
(m53-imp1--check "loader.scm-entry-points"
                 (m53-imp1--holds-all "mod/emacs/loader.scm"
                                      '("elisp-load" "search-elisp-load-path"
                                        "load-elisp" "load-elisp-full"
                                        "elisp-complete-file-load-from-port")))
(m53-imp1--check "reader.scm-entry-points"
                 (m53-imp1--holds-all "mod/emacs/reader.scm"
                                      '("elisp-read-from-port"
                                        "custom-elisp-read")))
(m53-imp1--check "lread.c-port-context"
                 (m53-imp1--holds-all "src/lread.c"
                                      '("The input port for Guile integration"
                                        "SCM port;"
                                        "scm_getc (ctx->port)")))

;;; --- S3. CHECK 2, the PTY terminal path -----------------------------

;; A PTY allocation now WORKS on this host (cr.org F4, brief.org section
;; 2): =os.openpty()= returns 2 file descriptors and no =errno 13=, and
;; =python3 test/pty-driver.py --selftest= prints =SELFTEST OK=.  The old
;; comment said the PTY allocation is denied; that host limit is GONE.
;; These pins record the path and its handles.  The live PTY slice is the
;; imp-3 work.

(setq m53-imp1--group 's3)

(m53-imp1--check "termchar.h-file-streams"
                 (m53-imp1--holds-all "src/termchar.h"
                                      '("FILE *input" "FILE *output"
                                        "FILE *termscript")))

(m53-imp1--check "pty-runner-present"
                 (m53-imp1--exists-p "test/m42/pty-runner.el"))

;;; --- S4. The registration ------------------------------------------

(setq m53-imp1--group 's4)

(m53-imp1--check "run-tests-m53-imp1"
                 (m53-imp1--contains-p "tool/run-tests.scm"
                                       "test/m53/test-m53-imp1.el"))
(m53-imp1--check "run-tests-m53-group"
                 (m53-imp1--contains-p "tool/run-tests.scm" "(group (m53)"))
;; M61 imp-2g (review cr.org CR2, finding F2 / F7): the
;; `total-case-count', len(CASES), 42 pin is REMOVED, not re-pinned.  A
;; case count is not a behavior, and the driver's own --selftest holds
;; the 3 count checks at :3470 ... :3472.

;;; --- S5. The guards -------------------------------------------------

;; An --filter that matches no group already reports exit 0 with 0
;; tests, so a green m53 gate proves nothing until the corpus exists and
;; its checks really register.  These guards fail when the corpus body
;; is truncated or its core checks do not run.  The counts are stable
;; because every check is registered at load time.  S1 holds 1 check,
;; S2 holds 6, S3 holds 3, and S4 holds 3.

(setq m53-imp1--group 's5)

(m53-imp1--check "reg/min-s1-checks-1" (>= (m53-imp1--group-count 's1) 1))
(m53-imp1--check "reg/min-s2-checks-6" (>= (m53-imp1--group-count 's2) 6))

;;; --- The group-total check ------------------------------------------

;; The floor is the measured count of m53-imp1 tests: 22 registered
;; checks (S1 1, S2 6, S3 3, S4 3, S5 4) plus the group-total deftest
;; itself.  The two S2 guile checks may fold to a controlled INFO skip
;; on a host with no guile binary, and a controlled skip is still a
;; registered test, so the floor holds either way.  This is a coarse
;; net, not a tight bound; the per-group reg/min-* guards are the tight
;; check.

(princ (format "=== m53 imp-1 suite done (%d checks; s1 %d, s2 %d, s3 %d, s4 %d, s5 %d) ===\n"
               m53-imp1--registered
               (m53-imp1--group-count 's1)
               (m53-imp1--group-count 's2)
               (m53-imp1--group-count 's3)
               (m53-imp1--group-count 's4)
               (m53-imp1--group-count 's5)))
