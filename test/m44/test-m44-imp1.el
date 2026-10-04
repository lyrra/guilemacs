;;; test-m44-imp1.el --- M44 imp-1 audit corpus (src/sysdep.c signal / suspend).
;;;
;;; M44 imp-1 is the docs-only audit (brief.org, docs/m44-plan.org).  It
;;; changes no C and no Scheme.  It answers four questions with evidence
;;; -- the block map of the signal / suspend surface, the class of each
;;; block, the module name and the leaf shape, and the A1 / A2 decision.
;;;
;;; This corpus reads files only.  It has no C dependency.  It pins:
;;;   D1 -- the base numbers of brief.org section 3, re-measured at HEAD
;;;         (the M43 close-out, 0e226bd05): src/sysdep.c is 4,950 lines
;;;         and 7 DEFUNs; src/keyboard.c is 11,233 lines and 447 DEFUNs;
;;;         src/keyboard-globals.c is 490 lines; the combined keyboard
;;;         surface is 11,723 (margin 237 under the 11,960 M31 budget);
;;;         scm_c_public_ref over src/*.[chm] is 201; and
;;;         mod/emacs/tty-modes.scm is 313 lines.
;;;   D2 -- the signal / suspend line facts of brief.org section 2 and
;;;         section 4.  These are facts in tracked files, so a drift is a
;;;         real FAIL.  The corpus records the milestone.org handler-site
;;;         correction: handle_child_signal is defined at src/process.c:7913
;;;         and handle_window_change_signal at src/dispnew.c:6489; the
;;;         milestone cites the delivery lines (:8002 and :6532).
;;;   D3 -- the leaf-shape words of brief.org section 5.3 in
;;;         docs/m44-plan.org.
;;;   D4 -- the decision words in the gitignored records
;;;         docs/m44-plan.org and docs/kb.org.  docs/ is gitignored, so a
;;;         present-but-stale record is an INFO-skip, not a FAIL; an
;;;         absent record is also a skip.  Known limit: D3 and D4 are
;;;         advisory only -- on a fresh clone (no docs/) they register no
;;;         ERT test, so they cannot turn this gate red; the hard checks
;;;         D1, D2 and D5 do.
;;;   D5 -- the (m44) group is registered in tool/run-tests.scm, and this
;;;         corpus registers a minimum number of checks per group.  cr.org
;;;         F2: an --filter that matches no group already reports exit 0
;;;         and 0 tests, so the gate proves nothing until the corpus exists
;;;         and really runs.  A single total bound is too loose (30 accepted
;;;         a loss of up to six checks), so the guard pins D1 and D2
;;;         separately and fails if either group is truncated.
;;;
;;; Each tracked-file check is printed as a PASS/FAIL line and turned
;;; into an ERT test so the harness counts it.  A read error is a real
;;; error, never a silent pass.  The corpus holds its own copy of every
;;; number it pins (brief.org section 3 and section 4).

(princ "=== m44 imp-1 audit suite ===\n")

(require 'imp-ert-report)

(defvar m44-imp1--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))

(defvar m44-imp1--registered 0
  "Total number of tracked-file checks this corpus has registered.  D5
pins a per-group minimum, so a truncated load cannot pass the gate
with no real checks.")

(defvar m44-imp1--group nil
  "The group that `m44-imp1--check' counts into: `d1' or `d2', or nil.
D5 pins the D1 and D2 minima separately (cr.org F2).")

(defvar m44-imp1--registered-d1 0
  "Number of D1 base-number checks registered.  D5 pins a minimum.
cr.org F2: a single loose total bound hid a truncation of up to six
checks, so each group carries its own bound.")

(defvar m44-imp1--registered-d2 0
  "Number of D2 line-fact checks registered.  D5 pins a minimum.")

(defun m44-imp1--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
the symbol `m44-imp1-absent' when REL does not exist.  docs/ is
gitignored, so a checkout without it must not crash the subprocess: an
unguarded `insert-file-contents' on an absent file would kill the
subprocess before ERT ever ran."
  (let ((path (expand-file-name rel m44-imp1--root)))
    (if (not (file-exists-p path))
        'm44-imp1-absent
      (with-temp-buffer
        (insert-file-contents path)
        (funcall fn)))))

(defun m44-imp1--contains-p (rel needle)
  "Non-nil when REL (repo-root-relative) contains NEEDLE."
  (m44-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (search-forward needle nil t))))

(defun m44-imp1--lines (rel)
  "Count the newlines of REL the way `wc -l' does."
  (m44-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (search-forward "\n" nil t) (setq n (1+ n)))
        n))))

(defun m44-imp1--count (rel regexp)
  "Count the matches of REGEXP in REL."
  (m44-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (re-search-forward regexp nil t) (setq n (1+ n)))
        n))))

(defun m44-imp1--line-of (rel needle)
  "1-based line number of the first literal NEEDLE in REL, or nil."
  (m44-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (when (search-forward needle nil t)
        (line-number-at-pos (match-beginning 0))))))

(defun m44-imp1--line-of-nth (rel regexp n)
  "1-based line of the Nth (1-based) REGEXP match in REL, or nil."
  (m44-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((i 0) (line nil))
        (while (and (< i n) (re-search-forward regexp nil t))
          (setq i (1+ i))
          (setq line (line-number-at-pos (match-beginning 0))))
        (when (= i n) line)))))

(defun m44-imp1--count-scm-ref ()
  "Count scm_c_public_ref over src/*.[chm] (the brief.org section 3 measure)."
  (let ((total 0)
        (dir (expand-file-name "src" m44-imp1--root)))
    (dolist (f (directory-files dir t "\\.[chm]\\'"))
      (setq total (+ total (or (m44-imp1--count f "scm_c_public_ref") 0))))
    total))

(defun m44-imp1--check (name ok)
  "Report and register one check on a TRACKED file.  OK is a boolean.
The D1/D2 callers pass `(eql N value)': when the source file is absent
the reader returns the symbol `m44-imp1-absent', so `eql' yields nil and
this prints FAIL.  That is intended -- an absent src/ file is a real
error, not a pass.  The `m44-imp1-absent' branch below only fires for a
caller that passes the symbol itself; D1 and D2 do not."
  (if (eq ok 'm44-imp1-absent)
      (princ (format "INFO m44/imp1/%s skipped (source file absent)\n" name))
    (progn
      (princ (format "%s m44/imp1/%s\n" (if ok "PASS" "FAIL") name))
      (setq m44-imp1--registered (1+ m44-imp1--registered))
      (cond ((eq m44-imp1--group 'd1)
             (setq m44-imp1--registered-d1 (1+ m44-imp1--registered-d1)))
            ((eq m44-imp1--group 'd2)
             (setq m44-imp1--registered-d2 (1+ m44-imp1--registered-d2))))
      (imp-register-bool-as-ert-test (format "m44-imp1/%s" name) (and ok t)))))

(defun m44-imp1--doc-check (name rel needle)
  "Report and register one check on a NON-durable record.  PASS and
register an ERT test when REL holds NEEDLE.  INFO-skip when REL is
absent OR present but stale.  docs/ is gitignored, so no commit can
carry it: a stale document is a fact of the checkout, not a code
regression, and must not turn the gate red."
  (let ((hit (m44-imp1--contains-p rel needle)))
    (if (and hit (not (eq hit 'm44-imp1-absent)))
        (progn (princ (format "PASS m44/imp1/%s\n" name))
               (imp-register-bool-as-ert-test (format "m44-imp1/%s" name) t))
      (princ (format "INFO m44/imp1/%s skipped (%s, gitignored record)\n"
                     name (if (eq hit 'm44-imp1-absent) "absent" "stale"))))))

;;; --- D1. The base numbers (brief.org section 3) -----------------------

(setq m44-imp1--group 'd1)

(m44-imp1--check "sysdep.c-lines-4950"
                 (eql 4950 (m44-imp1--lines "src/sysdep.c")))
(m44-imp1--check "sysdep.c-defuns-7"
                 (eql 7 (m44-imp1--count "src/sysdep.c" "^DEFUN (\"")))
(m44-imp1--check "keyboard.c-lines-11233"
                 (eql 11233 (m44-imp1--lines "src/keyboard.c")))
(m44-imp1--check "keyboard.c-defuns-447"
                 (eql 447 (m44-imp1--count "src/keyboard.c" "^DEFUN (\"")))
(m44-imp1--check "keyboard-globals.c-lines-490"
                 (eql 490 (m44-imp1--lines "src/keyboard-globals.c")))
(m44-imp1--check "combined-keyboard-surface-11723"
                 (let ((kb (m44-imp1--lines "src/keyboard.c"))
                       (kg (m44-imp1--lines "src/keyboard-globals.c")))
                   (and (eql 11233 kb)
                        (eql 490 kg)
                        (eql 11723 (+ kb kg)))))
(m44-imp1--check "margin-under-budget-237"
                 (let ((kb (m44-imp1--lines "src/keyboard.c"))
                       (kg (m44-imp1--lines "src/keyboard-globals.c")))
                   (and (integerp kb) (integerp kg)
                        (eql 237 (- 11960 (+ kb kg))))))
(m44-imp1--check "scm-c-public-ref-219"
                 (eql 219 (m44-imp1--count-scm-ref)))
(m44-imp1--check "tty-modes.scm-lines-313"
                 (eql 313 (m44-imp1--lines "mod/emacs/tty-modes.scm")))

;;; --- D2. The signal / suspend line facts (brief.org section 2 and 4) --

(setq m44-imp1--group 'd2)

;; suspend / resume in src/sysdep.c
(m44-imp1--check "sys_suspend-def-640"
                 (eql 640 (m44-imp1--line-of "src/sysdep.c" "sys_suspend (void)")))
(m44-imp1--check "kill-SIGTSTP-643"
                 (eql 643 (m44-imp1--line-of "src/sysdep.c" "kill (0, SIGTSTP);")))
(m44-imp1--check "sys_subshell-def-656"
                 (eql 656 (m44-imp1--line-of "src/sysdep.c" "sys_subshell (void)")))

;; signal delivery funnel in src/sysdep.c
(m44-imp1--check "emacs_sigaction_init-def-1601"
                 (eql 1601 (m44-imp1--line-of
                            "src/sysdep.c"
                            "emacs_sigaction_init (struct sigaction *action, signal_handler_t handler)")))
(m44-imp1--check "deliver_process_signal-def-1649"
                 (eql 1649 (m44-imp1--line-of
                            "src/sysdep.c"
                            "deliver_process_signal (int sig, signal_handler_t handler)")))
(m44-imp1--check "deliver_thread_signal-def-1684"
                 (eql 1684 (m44-imp1--line-of
                            "src/sysdep.c"
                            "deliver_thread_signal (int sig, signal_handler_t handler)")))
(m44-imp1--check "handle_fatal_signal-def-1708"
                 (eql 1708 (m44-imp1--line-of
                            "src/sysdep.c" "handle_fatal_signal (int sig)")))
(m44-imp1--check "handle_fatal_signal-call-1743"
                 (eql 1743 (m44-imp1--line-of
                            "src/sysdep.c" "handle_fatal_signal (sig);")))
(m44-imp1--check "deliver_arith_signal-accept-1970"
                 (eql 1970 (m44-imp1--line-of
                            "src/sysdep.c"
                            "emacs_sigaction_init (&action, deliver_arith_signal);")))
(m44-imp1--check "deliver_thread_signal-call-1902"
                 (eql 1902 (m44-imp1--line-of
                            "src/sysdep.c"
                            "deliver_thread_signal (sig, handle_arith_signal);")))

;; the declarations in src/syssignal.h
(m44-imp1--check "syssignal-sigaction-decl-61"
                 (eql 61 (m44-imp1--line-of
                          "src/syssignal.h"
                          "emacs_sigaction_init (struct sigaction *, signal_handler_t);")))
(m44-imp1--check "syssignal-deliver-decl-81"
                 (eql 81 (m44-imp1--line-of
                          "src/syssignal.h"
                          "deliver_process_signal (int, signal_handler_t);")))

;; the handlers in src/keyboard.c
(m44-imp1--check "handle_input_available-def-6888"
                 (eql 6888 (m44-imp1--line-of
                            "src/keyboard.c" "handle_input_available_signal (int sig)")))
(m44-imp1--check "handle_input_available-deliver-6899"
                 (eql 6899 (m44-imp1--line-of
                            "src/keyboard.c"
                            "deliver_process_signal (sig, handle_input_available_signal);")))
(m44-imp1--check "handle_user_signal-def-6954"
                 (eql 6954 (m44-imp1--line-of
                            "src/keyboard.c" "handle_user_signal (int sig)")))
(m44-imp1--check "handle_user_signal-deliver-6997"
                 (eql 6997 (m44-imp1--line-of
                            "src/keyboard.c"
                            "deliver_process_signal (sig, handle_user_signal);")))
(m44-imp1--check "handle_interrupt_signal-def-9851"
                 (eql 9851 (m44-imp1--line-of
                            "src/keyboard.c" "handle_interrupt_signal (int sig)")))
(m44-imp1--check "handle_interrupt_signal-deliver-9880"
                 (eql 9880 (m44-imp1--line-of
                            "src/keyboard.c"
                            "deliver_process_signal (sig, handle_interrupt_signal);")))

;; the suspend / subshell shims in src/keyboard.c
(m44-imp1--check "shim-sys-suspend-4121"
                 (eql 4121 (m44-imp1--line-of
                            "src/keyboard.c" "DEFUN (\"--sys-suspend\"")))
(m44-imp1--check "sys_suspend-call-4128"
                 (eql 4128 (m44-imp1--line-of-nth
                            "src/keyboard.c" "^[ \t]*sys_suspend ();" 1)))
(m44-imp1--check "sys_suspend-call-9967"
                 (eql 9967 (m44-imp1--line-of-nth
                            "src/keyboard.c" "^[ \t]*sys_suspend ();" 2)))
(m44-imp1--check "shim-sys-subshell-10522"
                 (eql 10522 (m44-imp1--line-of
                             "src/keyboard.c" "DEFUN (\"--sys-subshell\"")))

;; the handler definitions in the other files (the milestone sites are the
;; delivery lines; these are the true definition lines)
(m44-imp1--check "handle_child_signal-def-7913"
                 (eql 7913 (m44-imp1--line-of
                            "src/process.c" "handle_child_signal (int sig)")))
(m44-imp1--check "handle_child_signal-deliver-8002"
                 (eql 8002 (m44-imp1--line-of
                            "src/process.c"
                            "deliver_process_signal (sig, handle_child_signal);")))
(m44-imp1--check "handle_window_change-def-6489"
                 (eql 6489 (m44-imp1--line-of
                            "src/dispnew.c" "handle_window_change_signal (int sig)")))
(m44-imp1--check "handle_window_change-deliver-6532"
                 (eql 6532 (m44-imp1--line-of
                            "src/dispnew.c"
                            "deliver_process_signal (sig, handle_window_change_signal);")))

;;; --- D3. The leaf-shape words (gitignored plan, brief.org section 5.3) -

;; doc-check does not register a tracked-file check, but close the D2
;; group so the D5 registration check and the guards count into no group.
(setq m44-imp1--group nil)

(m44-imp1--doc-check "plan-module-emacs-interrupt"
                     "docs/m44-plan.org" "(emacs interrupt)")
(m44-imp1--doc-check "plan-leaf-plain-values"
                     "docs/m44-plan.org" "plain values only")
(m44-imp1--doc-check "plan-no-struct-across"
                     "docs/m44-plan.org" "Do not pass a struct")

;;; --- D4. The decision words (gitignored records) ----------------------

(m44-imp1--doc-check "plan-base-0e226bd05"
                     "docs/m44-plan.org" "#+base: HEAD = 0e226bd05")
(m44-imp1--doc-check "plan-target-sysdep.c"
                     "docs/m44-plan.org" "#+target: src/sysdep.c")
(m44-imp1--doc-check "plan-decision-A2"
                     "docs/m44-plan.org" "Decision: A2")
(m44-imp1--doc-check "plan-verdict-stays-C"
                     "docs/m44-plan.org" "STAYS C")
(m44-imp1--doc-check "kb-records-imp1-landed"
                     "docs/kb.org" "IMP-1 LANDED")
(m44-imp1--doc-check "kb-records-decision-A2"
                     "docs/kb.org" "DECISION A2")
(m44-imp1--doc-check "kb-signal-delivery-verdict"
                     "docs/kb.org" "sysdep-signal-delivery")
(m44-imp1--doc-check "kb-suspend-resume-verdict"
                     "docs/kb.org" "sysdep-suspend-resume")

;;; --- D5. The group registration and the min-count guard (cr.org F2) ---

(m44-imp1--check "reg/m44-group-present"
                 (m44-imp1--contains-p "tool/run-tests.scm"
                                       "test/m44/test-m44-imp1.el"))

;; cr.org F2: an --filter that matches no group already reports exit 0
;; with 0 tests, so a green m44 gate proves nothing until the corpus
;; exists and its checks really register.  These guards fail when the
;; corpus body is truncated or its core checks do not run.  The bound is
;; per group (cr.org F2: a single total bound of 30 accepted a loss of
;; up to six checks), and the counts are stable because every check is
;; registered at load time.  D1 holds 9 checks; D2 holds 26.
(m44-imp1--check "reg/min-d1-checks-9"
                 (>= m44-imp1--registered-d1 9))
(m44-imp1--check "reg/min-d2-checks-26"
                 (>= m44-imp1--registered-d2 26))

(princ (format "=== m44 imp-1 audit suite done (%d tracked checks: D1 %d, D2 %d) ===\n"
               m44-imp1--registered m44-imp1--registered-d1 m44-imp1--registered-d2))
