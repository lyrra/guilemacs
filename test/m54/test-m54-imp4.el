;;; test-m54-imp4.el --- M54 imp-4 input stream TAB policy corpus.
;;;
;;; M54 imp-4 moves ONE decision of the src/termchar.h INPUT stream
;;; (src/termchar.h :51) into the module (emacs tty-output): the terminal
;;; TAB policy UseTabs of ONE tty init (src/term.c :5030, brief.org
;;; section 3).  C keeps the mechanism: it calls
;;; tabs_safe_p (fileno (tty->input)) (the termios read on the C
;;; descriptor) and it reads TabWidth (tty) (a plain fixnum).  It passes
;;; the two PLAIN values to Scheme; Scheme owns the pure DECISION and
;;; returns the plain string "tabs" or "spaces".  C stores the result in
;;; UseTabs (tty).  No FILE * and no port crosses the seam.
;;;
;;; This corpus pins these groups:
;;;
;;;   S1 -- the pure table.  It resolves (emacs tty-output) through
;;;         `eval-scheme' and calls tty-tab-verdict for each plain pair:
;;;         (#t 8) -> "tabs", (#t 7) -> "spaces", (#f 8) -> "spaces",
;;;         (#f 7) -> "spaces".  It checks the plain string return and
;;;         that NO twin procedure exists.  S1 holds 2 checks.
;;;   S2 -- the seam by name.  The dispatcher m54_tty_tabs_verdict_scheme,
;;;         the ONE call site in init_tty, the scm_c_public_ref site, and
;;;         the anchors tabs_safe_p, fileno (tty->input), TabWidth, and
;;;         UseTabs (tty) (name checks, not line numbers), plus the nil
;;;         fallback that keeps the present C behavior.  S2 holds 5
;;;         checks.
;;;   S3 -- the registration: the corpus is in the (m54) group of
;;;         tool/run-tests.scm, after test-m54-imp3.el, and the (m52) and
;;;         (m53) groups stay present.  S3 holds 3 checks.
;;;   S4 -- the pty driver pins: the m54-imp4 group, the case
;;;         m54-imp4/tab-policy-e2e, and the case-count pins.  S4 holds 3
;;;         checks.
;;;   S5 -- the guards: a per-group min-count guard for S1 .. S4, and the
;;;         in-process group-total `ert-deftest'.  S5 holds 4 checks.
;;;
;;; This corpus reads TRACKED files only (src/, mod/, and the tracked
;;; runner tool/run-tests.scm and test/pty-driver.py).  It does NOT read
;;; docs/ (docs/kb.org test-must-not-read-docs): a gitignored record can
;;; only pass or skip, so a record check proves nothing.
;;;
;;; The pure DECISION is proven by the S1 headless table (the M52
;;; imp-4 .. imp-8 idiom).  The real path is proven by the separate pty
;;; case m54-imp4/tab-policy-e2e in test/pty-driver.py: it runs the built
;;; src/emacs on a real PTY with a tab-capable TERM and checks that the
;;; terminal path emits a hard-tab byte (0x09) when the decision is
;;; "tabs".  A host that cannot produce that byte is an explicit INFO
;;; skip with its evidence, never a pass.

(princ "=== m54 imp-4 input stream TAB policy suite ===\n")

(require 'imp-ert-report)

(defvar m54-imp4--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))
(defvar m54-imp4--registered 0
  "Total number of checks this corpus has registered.")
(defvar m54-imp4--group nil
  "The group that `m54-imp4--check' counts into: `s1' .. `s5', or nil.")
(defvar m54-imp4--counts nil
  "Alist of (GROUP . COUNT) for the registered checks.")

(defun m54-imp4--group-count (group)
  "Number of checks registered so far in GROUP."
  (or (cdr (assq group m54-imp4--counts)) 0))

(defun m54-imp4--bump-group ()
  "Count one check into `m54-imp4--group'."
  (when m54-imp4--group
    (let ((cell (assq m54-imp4--group m54-imp4--counts)))
      (if cell
          (setcdr cell (1+ (cdr cell)))
        (push (cons m54-imp4--group 1) m54-imp4--counts)))))

(defun m54-imp4--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
the symbol `m54-imp4-absent' when REL does not exist."
  (let ((path (expand-file-name rel m54-imp4--root)))
    (if (not (file-exists-p path))
        'm54-imp4-absent
      (with-temp-buffer
        (insert-file-contents path)
        (funcall fn)))))

(defun m54-imp4--contains-p (rel needle)
  "Non-nil when the TRACKED file REL contains NEEDLE.  An absent file
folds to nil, so a check prints FAIL: an absent src/ file is a real
error, not a pass (brief.org section 2)."
  (let ((hit (m54-imp4--with rel
               (lambda ()
                 (goto-char (point-min))
                 (search-forward needle nil t)))))
    (and (not (eq hit 'm54-imp4-absent)) (and hit t))))

(defun m54-imp4--count (rel needle)
  "Count the literal occurrences of NEEDLE in REL, or the symbol
`m54-imp4-absent' when REL does not exist.  This is a literal count, so
a call site that appears twice is caught."
  (m54-imp4--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (search-forward needle nil t) (setq n (1+ n)))
        n))))

(defun m54-imp4--ordered-p (rel needles)
  "Non-nil when the TRACKED file REL holds every NEEDLE in the GIVEN
ORDER: each search starts after the previous match."
  (m54-imp4--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((all t))
        (dolist (needle needles)
          (when all
            (unless (search-forward needle nil t) (setq all nil))))
        all))))

(defun m54-imp4--eval-scheme-int (expr)
  "Evaluate the plain Scheme EXPRESSION in the built Emacs and return
its integer value, or nil on any error.  The corpus calls the module
procedures through `resolve-module' / `module-ref': it does not use a
module-load probe as the proof of behaviour."
  (condition-case nil
      (eval-scheme expr)
    (error nil)))

(defun m54-imp4--check (name ok)
  "Report and register one check.  OK is a boolean.  When the source
file is absent the reader returns the symbol `m54-imp4-absent', so the
caller's test folds to nil and this prints FAIL.  Either way this
registers a real FAILING ERT test, so an absent src/ file is a real
error, not a pass."
  (let* ((absent (eq ok 'm54-imp4-absent))
         (pass (and (not absent) (and ok t))))
    (if absent
        (princ (format "FAIL m54/imp4/%s (source file absent)\n" name))
      (princ (format "%s m54/imp4/%s\n" (if pass "PASS" "FAIL") name)))
    (setq m54-imp4--registered (1+ m54-imp4--registered))
    (m54-imp4--bump-group)
    (imp-register-bool-as-ert-test (format "m54-imp4/%s" name) pass)))

;;; --- S1. The pure table (brief.org section 4) -----------------------

;; The procedure takes the plain C values (TABS-SAFE? a boolean,
;; TAB-WIDTH a fixnum) and returns the plain string "tabs" (the tty may
;; use hard tabs) or "spaces".  A plain string, not a Scheme boolean,
;; removes the #f / elisp nil ambiguity of a nil verdict.

(setq m54-imp4--group 's1)

(m54-imp4--check "tab-verdict-table"
                 (eql 1 (m54-imp4--eval-scheme-int
                         (concat
                          "(let ((m (resolve-module '(emacs tty-output))))"
                          " (if (and"
                          "  (equal? ((module-ref m 'tty-tab-verdict) #t 8) \"tabs\")"
                          "  (equal? ((module-ref m 'tty-tab-verdict) #t 7) \"spaces\")"
                          "  (equal? ((module-ref m 'tty-tab-verdict) #f 8) \"spaces\")"
                          "  (equal? ((module-ref m 'tty-tab-verdict) #f 7) \"spaces\"))"
                          " 1 0))"))))

;; The decision must be ONE procedure: a second definition would be a
;; twin.  The shared tty-write-verdict (imp-2 / imp-3) is untouched.
(m54-imp4--check "tab-no-twin-procedure"
                 (and (eql 1 (m54-imp4--count
                              "mod/emacs/tty-output.scm"
                              "(define (tty-tab-verdict tabs-safe? tab-width)"))
                      (eql 1 (m54-imp4--count
                              "mod/emacs/tty-output.scm"
                              "(define (tty-write-verdict written len err)"))))

;;; --- S2. The seam (brief.org section 5) -----------------------------

;; Name checks, not line pins.  The dispatcher resolves ONE module
;; procedure and passes plain values only.  C keeps the termios query,
;; the TabWidth read, and the UseTabs (tty) state write.  A nil verdict
;; MUST keep the present C behavior.

(setq m54-imp4--group 's2)

(m54-imp4--check "seam-dispatcher"
                 (m54-imp4--contains-p
                  "src/term.c"
                  "m54_tty_tabs_verdict_scheme (Lisp_Object tabs_safe, Lisp_Object tab_width)"))
(m54-imp4--check "seam-single-call-site"
                 (eql 1 (m54-imp4--count
                         "src/term.c"
                         "m54_tty_tabs_verdict_scheme (tabs_safe ? Qt : Qnil,")))
(m54-imp4--check "seam-scm-ref-site"
                 (m54-imp4--contains-p
                  "src/term.c"
                  "scm_c_public_ref (\"emacs tty-output\", \"tty-tab-verdict\")"))
(m54-imp4--check "seam-c-anchors"
                 (and (m54-imp4--contains-p "src/term.c" "tabs_safe_p (fileno (tty->input))")
                      (m54-imp4--contains-p "src/term.c" "make_fixnum (TabWidth (tty))")
                      (m54-imp4--contains-p "src/term.c" "UseTabs (tty)")))
;; The nil fallback: read the plain C value FIRST, call the dispatcher,
;; then keep the C result on nil.  A nil verdict must NOT force UseTabs
;; to 0.
(m54-imp4--check "seam-nil-fallback"
                 (and (m54-imp4--ordered-p
                       "src/term.c"
                       '("bool tabs_safe = tabs_safe_p (fileno (tty->input));"
                         "m54_tty_tabs_verdict_scheme (tabs_safe ? Qt : Qnil,"
                         "NILP (verdict)"
                         "? (tabs_safe && TabWidth (tty) == 8)"))))

;;; --- S3. The registration (brief.org section 8) ---------------------

(setq m54-imp4--group 's3)

(m54-imp4--check "run-tests-m54-imp4"
                 (m54-imp4--contains-p "tool/run-tests.scm"
                                       "test/m54/test-m54-imp4.el"))
(m54-imp4--check "run-tests-imp4-after-imp3"
                 (m54-imp4--ordered-p "tool/run-tests.scm"
                                      '("test/m54/test-m54-imp3.el"
                                        "test/m54/test-m54-imp4.el")))
(m54-imp4--check "run-tests-m52-m53-present"
                 (and (m54-imp4--contains-p "tool/run-tests.scm" "(group (m52)")
                      (m54-imp4--contains-p "tool/run-tests.scm" "(group (m53)")))

;;; --- S4. The pty driver pins (brief.org section 8) ------------------

(setq m54-imp4--group 's4)

(m54-imp4--check "pty-driver-group-m54-imp4"
                 (m54-imp4--contains-p "test/pty-driver.py" "\"m54-imp4\""))
(m54-imp4--check "pty-driver-case-name"
                 (m54-imp4--contains-p
                  "test/pty-driver.py" "m54-imp4/tab-policy-e2e"))
(m54-imp4--check "pty-driver-case-count-pins"
                 (and (m54-imp4--contains-p
                       "test/pty-driver.py"
                       "\"m54-imp4-case-count\", len(group_cases(\"m54-imp4\")), 1")
                      (m54-imp4--contains-p
                       "test/pty-driver.py"
                       "\"total-case-count\", len(CASES), 24")))

;;; --- S5. The guards -------------------------------------------------

;; An --filter that matches no group already reports exit 0 with 0
;; tests, so a green m54 gate proves nothing until the corpus exists and
;; its checks really register.  These guards fail when the corpus body
;; is truncated or its core checks do not run.  S1 holds 2 checks, S2
;; holds 5, S3 holds 3, and S4 holds 3.

(setq m54-imp4--group 's5)

(m54-imp4--check "reg/min-s1-checks-2" (>= (m54-imp4--group-count 's1) 2))
(m54-imp4--check "reg/min-s2-checks-5" (>= (m54-imp4--group-count 's2) 5))
(m54-imp4--check "reg/min-s3-checks-3" (>= (m54-imp4--group-count 's3) 3))
(m54-imp4--check "reg/min-s4-checks-3" (>= (m54-imp4--group-count 's4) 3))

;;; --- The group-total check ------------------------------------------

;; The floor is the measured count of m54-imp4 tests: 17 registered
;; checks (S1 2, S2 5, S3 3, S4 3, S5 4) plus the group-total deftest,
;; allowing one slack.

(defvar m54-imp4--min-gate-total 17
  "The minimum number of m54-imp4 ERT tests: 17 registered checks plus
the group-total deftest, allowing one slack.")

(ert-deftest m54-imp4/gate-m54-imp4-total ()
  "The m54-imp4 corpus registers at least its floor."
  (should (>= (length (ert-select-tests "^m54-imp4" t))
              m54-imp4--min-gate-total)))

(princ (format "=== m54 imp-4 suite done (%d checks; s1 %d, s2 %d, s3 %d, s4 %d, s5 %d) ===\n"
               m54-imp4--registered
               (m54-imp4--group-count 's1)
               (m54-imp4--group-count 's2)
               (m54-imp4--group-count 's3)
               (m54-imp4--group-count 's4)
               (m54-imp4--group-count 's5)))
