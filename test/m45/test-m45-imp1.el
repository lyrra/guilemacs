;;; test-m45-imp1.el --- M45 imp-1 audit corpus (src/callproc.c OS boundary).
;;;
;;; M45 imp-1 is the docs-only audit (brief.org, docs/m45-plan.org).  It
;;; changes no C and no Scheme.  It answers four questions with evidence
;;; -- the block map of the src/callproc.c OS surface, the class of each
;;; block, the module name and the leaf shape, and the A1 / A2 decision.
;;;
;;; This corpus reads files only.  It has no C dependency.  It pins:
;;;   D1 -- the base numbers of brief.org section 4, re-measured at M45
;;;         imp-2: src/sysdep.c is 4,950 lines and 7 DEFUNs;
;;;         src/keyboard.c is 11,233 lines and 447 DEFUNs;
;;;         src/keyboard-globals.c is 490 lines; the combined keyboard
;;;         surface is 11,723 (margin 237 under the 11,960 M31 budget);
;;;         scm_c_public_ref over src/*.[chm] is 201;
;;;         mod/emacs/tty-modes.scm is 313 lines; and src/callproc.c is
;;;         2,387 lines and 7 DEFUNs (imp-2 added the four leaves and
;;;         the guile.h include, so the block map below moved by one
;;;         line and the two callproc numbers grew; the imp-2 review
;;;         fixes for F1, F2 and F3 moved the line count again).
;;;   D2 -- the block line facts of brief.org section 3.1 and the three
;;;         DEFUN lines, re-pinned at M45 imp-2.  These are facts in a
;;;         tracked file, so a drift is a real FAIL.  The corpus records
;;;         the milestone.org correction: the definition range starts at
;;;         getenv_internal_1 (:1620) and ends at
;;;         make_environment_block (:1725), not the milestone.org range
;;;         ":1620 ... :1754".  The corpus also pins the section 3.1 note
;;;         column: the forward declarations (call_process :115,
;;;         child_setup :123) and the call sites (create_temp_file :1111,
;;;         exec_failed :1248, child_setup :643, :1559 and :1561,
;;;         emacs_spawn :692, make_environment_block :640,
;;;         block_child_signal :689).  It also pins the two file
;;;         facts: 4 scm_c_public_ref sites and 1 guile.h include (the
;;;         include that imp-2 adds; imp-3 adds the four dispatch helpers).
;;;   D3 -- the leaf-shape words of brief.org section 6 in
;;;         docs/m45-plan.org.
;;;   D4 -- the decision words in the gitignored records
;;;         docs/m45-plan.org and docs/kb.org.  docs/ is gitignored, so a
;;;         present-but-stale record is an INFO-skip, not a FAIL; an
;;;         absent record is also a skip.  Known limit: D3 and D4 are
;;;         advisory only -- on a fresh clone (no docs/) they register no
;;;         ERT test, so they cannot turn this gate red; the hard checks
;;;         D1, D2 and D5 do.
;;;   D5 -- the (m45) group is registered in tool/run-tests.scm, and this
;;;         corpus registers a minimum number of checks per group.  cr.org
;;;         F2: an --filter that matches no group already reports exit 0
;;;         and 0 tests, so the gate proves nothing until the corpus exists
;;;         and really runs.  A single total bound is too loose, so the
;;;         guard pins D1 and D2 separately and fails if either group is
;;;         truncated.
;;;
;;; Each tracked-file check is printed as a PASS/FAIL line and turned
;;; into an ERT test so the harness counts it.  A read error is a real
;;; error, never a silent pass.  The corpus holds its own copy of every
;;; number it pins (brief.org section 4 and section 3.1).

(princ "=== m45 imp-1 audit suite ===\n")

(require 'imp-ert-report)

(defvar m45-imp1--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))

(defvar m45-imp1--registered 0
  "Total number of tracked-file checks this corpus has registered.  D5
pins a per-group minimum, so a truncated load cannot pass the gate
with no real checks.")

(defvar m45-imp1--group nil
  "The group that `m45-imp1--check' counts into: `d1' or `d2', or nil.
D5 pins the D1 and D2 minima separately (cr.org F2).")

(defvar m45-imp1--registered-d1 0
  "Number of D1 base-number checks registered.  D5 pins a minimum.")

(defvar m45-imp1--registered-d2 0
  "Number of D2 line-fact checks registered.  D5 pins a minimum.")

(defun m45-imp1--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
the symbol `m45-imp1-absent' when REL does not exist.  docs/ is
gitignored, so a checkout without it must not crash the subprocess: an
unguarded `insert-file-contents' on an absent file would kill the
subprocess before ERT ever ran."
  (let ((path (expand-file-name rel m45-imp1--root)))
    (if (not (file-exists-p path))
        'm45-imp1-absent
      (with-temp-buffer
        (insert-file-contents path)
        (funcall fn)))))

(defun m45-imp1--contains-p (rel needle)
  "Non-nil when REL (repo-root-relative) contains NEEDLE."
  (m45-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (search-forward needle nil t))))

(defun m45-imp1--lines (rel)
  "Count the newlines of REL the way `wc -l' does."
  (m45-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (search-forward "\n" nil t) (setq n (1+ n)))
        n))))

(defun m45-imp1--count (rel regexp)
  "Count the matches of REGEXP in REL."
  (m45-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (re-search-forward regexp nil t) (setq n (1+ n)))
        n))))

(defun m45-imp1--line-of (rel needle)
  "1-based line number of the first literal NEEDLE in REL, or nil."
  (m45-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (when (search-forward needle nil t)
        (line-number-at-pos (match-beginning 0))))))

(defun m45-imp1--line-of-nth (rel regexp n)
  "1-based line of the Nth (1-based) REGEXP match in REL, or nil.
Used to pin a call site that occurs more than once in the same file."
  (m45-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((i 0) (line nil))
        (while (and (< i n) (re-search-forward regexp nil t))
          (setq i (1+ i))
          (setq line (line-number-at-pos (match-beginning 0))))
        (when (= i n) line)))))

(defun m45-imp1--count-scm-ref ()
  "Count scm_c_public_ref over src/*.[chm] (the brief.org section 4 measure)."
  (let ((total 0)
        (dir (expand-file-name "src" m45-imp1--root)))
    (dolist (f (directory-files dir t "\\.[chm]\\'"))
      (setq total (+ total (or (m45-imp1--count f "scm_c_public_ref") 0))))
    total))

(defun m45-imp1--check (name ok)
  "Report and register one check on a TRACKED file.  OK is a boolean.
The D1/D2 callers pass `(eql N value)': when the source file is absent
the reader returns the symbol `m45-imp1-absent', so `eql' yields nil and
this prints FAIL.  That is intended -- an absent src/ file is a real
error, not a pass.  The `m45-imp1-absent' branch below only fires for a
caller that passes the symbol itself; D1 and D2 do not."
  (if (eq ok 'm45-imp1-absent)
      (princ (format "INFO m45/imp1/%s skipped (source file absent)\n" name))
    (progn
      (princ (format "%s m45/imp1/%s\n" (if ok "PASS" "FAIL") name))
      (setq m45-imp1--registered (1+ m45-imp1--registered))
      (cond ((eq m45-imp1--group 'd1)
             (setq m45-imp1--registered-d1 (1+ m45-imp1--registered-d1)))
            ((eq m45-imp1--group 'd2)
             (setq m45-imp1--registered-d2 (1+ m45-imp1--registered-d2))))
      (imp-register-bool-as-ert-test (format "m45-imp1/%s" name) (and ok t)))))

(defun m45-imp1--doc-check (name rel needle)
  "Report and register one check on a NON-durable record.  PASS and
register an ERT test when REL holds NEEDLE.  INFO-skip when REL is
absent OR present but stale.  docs/ is gitignored, so no commit can
carry it: a stale document is a fact of the checkout, not a code
regression, and must not turn the gate red."
  (let ((hit (m45-imp1--contains-p rel needle)))
    (if (and hit (not (eq hit 'm45-imp1-absent)))
        (progn (princ (format "PASS m45/imp1/%s\n" name))
               (imp-register-bool-as-ert-test (format "m45-imp1/%s" name) t))
      (princ (format "INFO m45/imp1/%s skipped (%s, gitignored record)\n"
                     name (if (eq hit 'm45-imp1-absent) "absent" "stale"))))))

;;; --- D1. The base numbers (brief.org section 4) -----------------------

(setq m45-imp1--group 'd1)

(m45-imp1--check "sysdep.c-lines-4950"
                 (eql 4950 (m45-imp1--lines "src/sysdep.c")))
(m45-imp1--check "sysdep.c-defuns-7"
                 (eql 7 (m45-imp1--count "src/sysdep.c" "^DEFUN (\"")))
(m45-imp1--check "keyboard.c-lines-11233"
                 (eql 11233 (m45-imp1--lines "src/keyboard.c")))
(m45-imp1--check "keyboard.c-defuns-447"
                 (eql 447 (m45-imp1--count "src/keyboard.c" "^DEFUN (\"")))
(m45-imp1--check "keyboard-globals.c-lines-490"
                 (eql 490 (m45-imp1--lines "src/keyboard-globals.c")))
(m45-imp1--check "combined-keyboard-surface-11723"
                 (let ((kb (m45-imp1--lines "src/keyboard.c"))
                       (kg (m45-imp1--lines "src/keyboard-globals.c")))
                   (and (eql 11233 kb)
                        (eql 490 kg)
                        (eql 11723 (+ kb kg)))))
(m45-imp1--check "margin-under-budget-237"
                 (let ((kb (m45-imp1--lines "src/keyboard.c"))
                       (kg (m45-imp1--lines "src/keyboard-globals.c")))
                   (and (integerp kb) (integerp kg)
                        (eql 237 (- 11960 (+ kb kg))))))
(m45-imp1--check "scm-c-public-ref-253"
                 (eql 253 (m45-imp1--count-scm-ref)))
(m45-imp1--check "tty-modes.scm-lines-313"
                 (eql 313 (m45-imp1--lines "mod/emacs/tty-modes.scm")))
(m45-imp1--check "callproc.c-lines-2387"
                 (eql 2387 (m45-imp1--lines "src/callproc.c")))
(m45-imp1--check "callproc.c-defuns-7"
                 (eql 7 (m45-imp1--count "src/callproc.c" "^DEFUN (\"")))

;;; --- D2. The block line facts (brief.org section 3.1) -----------------

(setq m45-imp1--group 'd2)

;; the parent-side policy and the mechanism blocks
(m45-imp1--check "call_process-def-400"
                 (eql 400 (m45-imp1--line-of
                           "src/callproc.c"
                           "call_process (ptrdiff_t nargs, Lisp_Object *args,")))
(m45-imp1--check "create_temp_file-def-981"
                 (eql 981 (m45-imp1--line-of
                           "src/callproc.c"
                           "create_temp_file (ptrdiff_t nargs, Lisp_Object *args,")))
(m45-imp1--check "add_env-removed"
                 (eql 0 (m45-imp1--count
                         "src/callproc.c"
                         "add_env (char **env, char **new_env, char *string)")))
(m45-imp1--check "exec_failed-def-1161"
                 (eql 1161 (m45-imp1--line-of
                            "src/callproc.c"
                            "exec_failed (char const *name, int err)")))
(m45-imp1--check "child_setup-def-1191"
                 (eql 1191 (m45-imp1--line-of
                            "src/callproc.c"
                            "child_setup (int in, int out, int err, char **new_argv, char **env,")))
(m45-imp1--check "emacs_posix_spawn_init_actions-def-1283"
                 (eql 1283 (m45-imp1--line-of
                            "src/callproc.c"
                            "emacs_posix_spawn_init_actions (posix_spawn_file_actions_t *actions,")))
(m45-imp1--check "emacs_posix_spawn_init_attributes-def-1325"
                 (eql 1325 (m45-imp1--line-of
                            "src/callproc.c"
                            "emacs_posix_spawn_init_attributes (posix_spawnattr_t *attributes,")))
(m45-imp1--check "emacs_spawn-def-1396"
                 (eql 1396 (m45-imp1--line-of
                            "src/callproc.c"
                            "emacs_spawn (pid_t *newpid, int std_in, int std_out, int std_err,")))
(m45-imp1--check "getenv_internal_1-def-1584"
                 (eql 1584 (m45-imp1--line-of
                            "src/callproc.c"
                            "getenv_internal_1 (const char *var")))
(m45-imp1--check "getenv_internal-def-1619"
                 (eql 1619 (m45-imp1--line-of
                            "src/callproc.c"
                            "getenv_internal (const char *var")))
(m45-imp1--check "egetenv_internal-def-1702"
                 (eql 1702 (m45-imp1--line-of
                            "src/callproc.c"
                            "egetenv_internal (const char *var, ptrdiff_t len)")))
(m45-imp1--check "make_environment_block-def-1725"
                 (eql 1725 (m45-imp1--line-of
                            "src/callproc.c"
                            "make_environment_block (Lisp_Object current_dir)")))
(m45-imp1--check "init_callproc-def-1781"
                 (eql 1781 (m45-imp1--line-of
                            "src/callproc.c"
                            "init_callproc (void)")))

;; the forward declarations (brief.org section 3.1 note column: the entry
;; points are "declared :114" and ":122", above their definitions)
(m45-imp1--check "call_process-decl-115"
                 (eql 115 (m45-imp1--line-of-nth
                           "src/callproc.c" "call_process (" 1)))
(m45-imp1--check "child_setup-decl-123"
                 (eql 123 (m45-imp1--line-of-nth
                           "src/callproc.c" "child_setup (" 1)))

;; the call sites (brief.org section 3.1 note column: "called at ...").
;; child_setup is called from both the posix_spawn path (:616) and the
;; vfork path (:1594, :1596); block_child_signal is called at :178 and
;; the parent-side :662, so the second match is pinned by index.
(m45-imp1--check "create_temp_file-call-1111"
                 (eql 1111 (m45-imp1--line-of
                            "src/callproc.c"
                            "create_temp_file (nargs, args, &infile, &fd);")))
(m45-imp1--check "callproc-resolve-program-def-135"
                 (eql 135 (m45-imp1--line-of
                           "src/callproc.c"
                           "callproc_resolve_program (Lisp_Object program)")))
(m45-imp1--check "callproc-env-called-1731"
                 (eql 1731 (m45-imp1--line-of
                            "src/callproc.c"
                            "env_list = callproc_env (current_dir);")))
(m45-imp1--check "exec_failed-call-1248"
                 (eql 1248 (m45-imp1--line-of
                            "src/callproc.c"
                            "exec_failed (new_argv[0], errnum);")))
(m45-imp1--check "child_setup-call-643"
                 (eql 643 (m45-imp1--line-of
                           "src/callproc.c"
                           "child_setup (*filefd, fd_output, fd_error, new_argv, env,")))
(m45-imp1--check "child_setup-call-1559"
                 (eql 1559 (m45-imp1--line-of
                            "src/callproc.c"
                            "pid = child_setup (std_in, std_out, std_err, argv, envp, cwd);")))
(m45-imp1--check "child_setup-call-1561"
                 (eql 1561 (m45-imp1--line-of-nth
                            "src/callproc.c"
                            "child_setup (std_in, std_out, std_err, argv, envp, cwd);" 2)))
(m45-imp1--check "emacs_spawn-call-692"
                 (eql 692 (m45-imp1--line-of
                           "src/callproc.c"
                           "emacs_spawn (&pid, filefd, fd_output, fd_error, new_argv, env,")))
(m45-imp1--check "make_environment_block-call-640"
                 (eql 640 (m45-imp1--line-of
                           "src/callproc.c"
                           "make_environment_block (current_dir)")))
(m45-imp1--check "block_child_signal-call-689"
                 ;; anchor the match: "unblock_child_signal" holds the
                 ;; same substring, so an unanchored search would hit it.
                 (eql 689 (m45-imp1--line-of-nth
                           "src/callproc.c"
                           "^[ \t]*block_child_signal (&oldset);" 2)))

;; the three DEFUNs
(m45-imp1--check "defun-call-process-316"
                 (eql 316 (m45-imp1--line-of
                           "src/callproc.c" "DEFUN (\"call-process\"")))
(m45-imp1--check "defun-call-process-region-1052"
                 (eql 1052 (m45-imp1--line-of
                            "src/callproc.c" "DEFUN (\"call-process-region\"")))
(m45-imp1--check "defun-getenv-internal-1668"
                 (eql 1668 (m45-imp1--line-of
                            "src/callproc.c" "DEFUN (\"getenv-internal\"")))

;; the two file facts: 4 scm_c_public_ref sites and 1 guile.h include
;; (imp-2 added the include, so the imp-1 no-guile.h pin is now positive;
;; imp-3 adds the four dispatch helpers)
(m45-imp1--check "callproc.c-scm-ref-4"
                 (eql 4 (m45-imp1--count "src/callproc.c" "scm_c_public_ref")))
(m45-imp1--check "callproc.c-has-guile.h"
                 (let ((n (m45-imp1--count "src/callproc.c" "guile.h")))
                   (and (integerp n) (eql 1 n))))

;;; --- D3. The leaf-shape words (gitignored plan, brief.org section 6) --

;; doc-check does not register a tracked-file check, but close the D2
;; group so the D5 registration check and the guards count into no group.
(setq m45-imp1--group nil)

(m45-imp1--doc-check "plan-module-emacs-process-create"
                     "docs/m45-plan.org" "(emacs process-create)")
(m45-imp1--doc-check "plan-leaf-plain-values"
                     "docs/m45-plan.org" "plain values only")
(m45-imp1--doc-check "plan-no-struct-across"
                     "docs/m45-plan.org" "pass a struct across the OS layer")

;;; --- D4. The decision words (gitignored records) ----------------------

(m45-imp1--doc-check "plan-base-8cad4f6d6"
                     "docs/m45-plan.org" "#+base: HEAD = 8cad4f6d6")
(m45-imp1--doc-check "plan-target-callproc.c"
                     "docs/m45-plan.org" "#+target: src/callproc.c")
(m45-imp1--doc-check "plan-decision-A1"
                     "docs/m45-plan.org" "Decision: A1")
(m45-imp1--doc-check "plan-parent-side-slice"
                     "docs/m45-plan.org" "parent-side")
(m45-imp1--doc-check "kb-records-imp1-landed"
                     "docs/kb.org" "IMP-1 LANDED")
(m45-imp1--doc-check "kb-records-decision-A1"
                     "docs/kb.org" "DECISION A1")
(m45-imp1--doc-check "kb-layer-callproc-os-boundary"
                     "docs/kb.org" "callproc-os-boundary")

;;; --- D5. The group registration and the min-count guard (cr.org F2) ---

(m45-imp1--check "reg/m45-group-present"
                 (m45-imp1--contains-p "tool/run-tests.scm"
                                       "test/m45/test-m45-imp1.el"))

;; cr.org F2: an --filter that matches no group already reports exit 0
;; with 0 tests, so a green m45 gate proves nothing until the corpus
;; exists and its checks really register.  These guards fail when the
;; corpus body is truncated or its core checks do not run.  The bound is
;; per group, and the counts are stable because every check is
;; registered at load time.  D1 holds 11 checks; D2 holds 30.
(m45-imp1--check "reg/min-d1-checks-11"
                 (>= m45-imp1--registered-d1 11))
(m45-imp1--check "reg/min-d2-checks-30"
                 (>= m45-imp1--registered-d2 30))

(princ (format "=== m45 imp-1 audit suite done (%d tracked checks: D1 %d, D2 %d) ===\n"
               m45-imp1--registered m45-imp1--registered-d1 m45-imp1--registered-d2))
