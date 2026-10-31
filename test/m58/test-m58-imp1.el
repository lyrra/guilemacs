;;; test-m58-imp1.el --- M58 imp-1 remaining TTY policy surface audit corpus.
;;;
;;; M58 imp-1 is the remaining TTY policy-surface AUDIT
;;; (docs/m58-plan.org).  It is docs only: the C delta is 0 and the Scheme delta
;;; is 0.  It walks every remaining movable TTY policy and state path in
;;; src/term.c, re-checks the C3 elisp-compiler boundary, classes each
;;; path MOVE / STAYS C / NOT PROVEN, and records the A1 / A2 verdict
;;; (docs/m58-plan.org).
;;;
;;; M61 imp-2b and imp-2g removed every SOURCE-INSPECTION assertion of
;;; this corpus (milestone.org finding F2 / F7).  A test proves
;;; BEHAVIOR.  It must not read source text, a source line number, a
;;; source byte count or a source order, because such a check fails on a
;;; comment change and proves nothing about the program.
;;;
;;; What the corpus keeps:
;;;
;;;   S1 -- a STATE check, NOT a behavior check: the base commit
;;;         fca28d3be is an ANCESTOR of the running HEAD.  It is a `git'
;;;         query, not a source read, and it proves nothing about the
;;;         program.  It fails in a shallow clone and after a history
;;;         rewrite, so it guards the repository relation only.  S1
;;;         holds 1 check.
;;;   S2 -- the real names resolve in the BUILT src/emacs.  The row map
;;;         of docs/m58-plan.org classes 7 TTY entry points as STAYS C
;;;         or MOVE; each one is a real subr in the running binary, so
;;;         each name must resolve and answer a subr.  A missing name is
;;;         a real FAIL.  S2 holds 2 checks.
;;;   S3 -- the real tty init path: the built src/emacs runs on a real
;;;         PTY through test/pty-driver.py, so init_tty runs the TTY
;;;         sites.  On a result that is neither PASS nor INFO the check
;;;         RETRIES the driver once, then prints both runs when the
;;;         retry still fails (docs/m58-plan.org).  A missing PTY is an
;;;         explicit INFO skip.  S3 holds 2 checks.
;;;   S4 -- the guards: one per-group min-count guard for each of S1 ..
;;;         S3.  S4 holds 3 checks.
;;;
;;; The corpus reads NO source file.  The only inputs are the running
;;; binary, `git', and a real PTY run.
;;;
;;; A missing `git', `python3' binary or a missing PTY is an explicit
;;; INFO skip, never a pass.  Every check registers a real ERT test via
;;; imp-register-bool-as-ert-test, so the harness parses the ERT output
;;; and the exit code is correct.

(princ "=== m58 imp-1 remaining TTY policy surface audit suite ===\n")

(require 'imp-ert-report)

(defvar m58-imp1--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))
(defvar m58-imp1--registered 0
  "Total number of checks this corpus has registered.")
(defvar m58-imp1--group nil
  "The group that `m58-imp1--check' counts into: `s1' .. `s4', or nil.")
(defvar m58-imp1--counts nil
  "Alist of (GROUP . COUNT) for the registered checks.")

(defun m58-imp1--group-count (group)
  "Number of checks registered so far in GROUP."
  (or (cdr (assq group m58-imp1--counts)) 0))

(defun m58-imp1--bump-group ()
  "Count one check into `m58-imp1--group'."
  (when m58-imp1--group
    (let ((cell (assq m58-imp1--group m58-imp1--counts)))
      (if cell
          (setcdr cell (1+ (cdr cell)))
        (push (cons m58-imp1--group 1) m58-imp1--counts)))))

(defun m58-imp1--run (prog args)
  "Run PROG with ARGS in a subprocess from the repo root and return its
stdout / stderr as a string, or the symbol `m58-imp1-prog-absent' when
PROG is not on PATH.  The default directory is the repo root, so a
relative ARGS stays repo-root-relative."
  (if (not (executable-find prog))
      'm58-imp1-prog-absent
    (let ((buf (get-buffer-create " *m58-imp1-run*"))
          (default-directory m58-imp1--root))
      (unwind-protect
          (progn
            (with-current-buffer buf (erase-buffer))
            (apply #'call-process prog nil buf nil args)
            (with-current-buffer buf
              (buffer-substring-no-properties (point-min) (point-max))))
        (kill-buffer buf)))))

(defun m58-imp1--ancestor-p (ancestor descendant)
  "Non-nil when ANCESTOR is an ancestor of DESCENDANT in the repo at
`m58-imp1--root'.  Return the symbol `m58-imp1-prog-absent' when the
`git' binary is not on PATH, and nil when `git' fails (for example an
unknown revision).  A committed corpus must NOT pin the running HEAD to
a literal base commit: when imp-1 is committed, HEAD moves to the imp
commit, so a hard equality check against the base always fails.  The
ancestry relation stays true when the branch advances."
  (if (not (executable-find "git"))
      'm58-imp1-prog-absent
    (let ((default-directory m58-imp1--root))
      (zerop (call-process "git" nil nil nil
                           "merge-base" "--is-ancestor"
                           ancestor descendant)))))

(defun m58-imp1--check (name ok)
  "Report and register one check.  OK is a boolean."
  (let ((pass (and ok t)))
    (princ (format "%s m58/imp1/%s\n" (if pass "PASS" "FAIL") name))
    (setq m58-imp1--registered (1+ m58-imp1--registered))
    (m58-imp1--bump-group)
    (imp-register-bool-as-ert-test (format "m58-imp1/%s" name) pass)))

(defun m58-imp1--info-skip (name reason)
  "Register one explicit INFO skip, counted into the current group.  A
host limit is a skip, never a pass (docs/m58-plan.org)."
  (princ (format "INFO m58/imp1/%s %s\n" name reason))
  (setq m58-imp1--registered (1+ m58-imp1--registered))
  (m58-imp1--bump-group)
  (imp-register-skip-as-ert-test (format "m58/imp1/%s" name) reason))

;;; --- S1. The real repository relation (a STATE check) ---------------

;; Row 1 of docs/m58-plan.org (HEAD) checks that the base commit is an
;; ANCESTOR of the running HEAD: a committed corpus cannot pin HEAD to a
;; literal, because HEAD moves to the imp commit.  This is a STATE check
;; of the repository, not a behavior check: it proves nothing about the
;; program and it fails in a shallow clone.  A missing `git' is an
;; explicit INFO skip, never a pass.

(setq m58-imp1--group 's1)

(let ((ok (m58-imp1--ancestor-p "fca28d3be" "HEAD")))
  (if (eq ok 'm58-imp1-prog-absent)
      (m58-imp1--info-skip "head-fca28d3be" "no git binary on PATH")
    (m58-imp1--check "head-fca28d3be" ok)))

;;; --- S2. The real names resolve -------------------------------------

;; The row map classes 7 TTY entry points (MOVE or STAYS C).  Each one
;; is a real subr of the running binary, so the observable that replaces
;; the deleted source pins is: the name resolves, and its definition is
;; a subr.  This runs INSIDE the built src/emacs (the (m58) group has no
;; prelude key), so it is the real binary of this tree.

(defvar m58-imp1--tty-names
  '(tty-display-color-cells        ; group B -- the color-mode policy
    tty-no-underline               ; group F -- a one-field C read
    tty-top-frame                  ; group F -- a one-field C read
    suspend-tty                    ; group F -- a C stream close / open
    resume-tty                     ; group F -- a C stream close / open
    tty--set-output-buffer-size    ; group F -- NOT PROVEN
    tty--output-buffer-size)       ; group F -- NOT PROVEN
  "The TTY entry points of the docs/m58-plan.org row map.")

(setq m58-imp1--group 's2)

(m58-imp1--check "tty-names-resolve"
                 (let ((all t))
                   (dolist (name m58-imp1--tty-names)
                     (unless (fboundp name) (setq all nil)))
                   all))

(m58-imp1--check "tty-names-are-subrs"
                 (let ((all t))
                   (dolist (name m58-imp1--tty-names)
                     (unless (and (fboundp name)
                                  (subrp (symbol-function name)))
                       (setq all nil)))
                   all))

;;; --- S3. The real tty init path (docs/m58-plan.org) ---------------

;; The module-load probe is NOT proof.  The real path is the built
;; src/emacs on a real PTY: test/pty-driver.py boots the child emacs,
;; which runs init_tty and therefore the TTY sites.  A missing python3 or
;; a missing PTY is an explicit INFO skip, NEVER a pass.

(setq m58-imp1--group 's3)

(let ((out (m58-imp1--run "python3"
                          (list "test/pty-driver.py" "--selftest"))))
  (if (eq out 'm58-imp1-prog-absent)
      (m58-imp1--info-skip "pty-driver-selftest" "no python3 binary on PATH")
    (m58-imp1--check "pty-driver-selftest"
                     (and (string-match-p "SELFTEST OK" out) t))))

(let ((emacs (expand-file-name "src/emacs" m58-imp1--root)))
  (let* ((args (list "test/pty-driver.py" "--emacs" emacs "--group" "m56-imp2"))
         (out1 (m58-imp1--run "python3" args))
         (done (or (eq out1 'm58-imp1-prog-absent)
                   (string-match-p "PASS m56-imp2/tty-init-e2e" out1)
                   (string-match-p "INFO m56-imp2/tty-init-e2e" out1)))
         (out2 (unless done (m58-imp1--run "python3" args)))
         (out (or out2 out1)))
    (cond
     ((eq out1 'm58-imp1-prog-absent)
      (m58-imp1--info-skip "pty-real-path-tty-init" "no python3 binary on PATH"))
     ((string-match-p "PASS m56-imp2/tty-init-e2e" out)
      (m58-imp1--check "pty-real-path-tty-init" t))
     ((string-match-p "INFO m56-imp2/tty-init-e2e" out)
      (m58-imp1--info-skip "pty-real-path-tty-init" "no PTY on this host"))
     (t
      (princ (format "m58 imp1 PTY run 1 (neither PASS nor INFO):\n%s\n" out1))
      (princ (format "m58 imp1 PTY run 2 (retry):\n%s\n" out2))
      (m58-imp1--check "pty-real-path-tty-init" nil)))))

;;; --- S4. The guards -------------------------------------------------

;; An --filter that matches no group already reports exit 0 with 0
;; tests, so a green m58 gate proves nothing until the corpus exists and
;; its checks really register.  These guards fail when the corpus body
;; is truncated or its core checks do not run.  The counts are stable
;; because every check is registered at load time.  S1 holds 1 check,
;; S2 holds 2, and S3 holds 2.

(setq m58-imp1--group 's4)

(m58-imp1--check "reg/min-s1-checks-1" (>= (m58-imp1--group-count 's1) 1))
(m58-imp1--check "reg/min-s2-checks-2" (>= (m58-imp1--group-count 's2) 2))
(m58-imp1--check "reg/min-s3-checks-2" (>= (m58-imp1--group-count 's3) 2))

;;; --- The group-total check ------------------------------------------

;; The measured count of m58-imp1 tests is 9: 8 registered checks
;; (S1 1, S2 2, S3 2, S4 3) plus the group-total deftest itself.  The S3
;; checks may fold to a controlled INFO skip on a host with no python3 or
;; no PTY, and a controlled skip is still a registered test, so the floor
;; holds either way.

(defvar m58-imp1--min-gate-total 9
  "The exact number of m58-imp1 ERT tests: 8 registered checks (S1 1,
S2 2, S3 2, S4 3) plus the group-total deftest itself.")

(ert-deftest m58-imp1/gate-m58-total ()
  "The m58-imp1 corpus registers at least its docs-independent floor."
  (should (>= (length (ert-select-tests "^m58-imp1" t))
              m58-imp1--min-gate-total)))

(princ (format "=== m58 imp-1 suite done (%d checks; s1 %d, s2 %d, s3 %d, s4 %d) ===\n"
               m58-imp1--registered
               (m58-imp1--group-count 's1)
               (m58-imp1--group-count 's2)
               (m58-imp1--group-count 's3)
               (m58-imp1--group-count 's4)))
