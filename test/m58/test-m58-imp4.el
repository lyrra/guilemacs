;;; test-m58-imp4.el --- M58 imp-4 the Group B color-mode MOVE.
;;;
;;; imp-4 MOVES the 2 plain color-mode decisions of src/term.c to
;;; (emacs tty-output) (brief.org sections 1, 5, and 6):
;;;
;;;   tty_setup_colors     the mode canonicalization and the
;;;                        -1 / 0 / 8 scheme choice.  They are now the
;;;                        pure procedure tty-color-mode-tag.
;;;   set_tty_color_mode   the change gate.  It is now the pure
;;;                        procedure tty-color-mode-changed-p, which
;;;                        compares the RAW modes.
;;;
;;; C keeps every mechanism: the 3 cap strings (with the TERMINFO
;;; variants of the 8-color scheme), every TN_* and TS_* write, the
;;; static default slots, tty_default_color_capabilities save /
;;; restore, the f->param_alist and tty-color-mode-alist resolve, the
;;; TYPE_RANGED_FIXNUMP narrowing, the RAW previous_color_mode store,
;;; safe_calln (Qtty_set_up_initial_frame_faces), and the FILE *
;;; streams.  No Lisp_Object, struct frame *, or
;;; struct tty_display_info * crosses the seam.
;;;
;;; This corpus pins:
;;;
;;;   T1 -- the C sites that stay C, the 2 DELETED inline decisions,
;;;         the gate and the raw store, the ONE caller (the frame
;;;         switch), and the boundary rule "no Scheme port owns a C
;;;         FILE *".  T1 holds 5 checks.
;;;   T2 -- the PTY case in test/pty-driver.py: its name, its group,
;;;         the M58_IMP4_CASES tuple, the CASES and GROUPS entries,
;;;         the expectation "8 0 8", the frame switch, the NARROW
;;;         info_report_prefix skip, and the case-count pins (TOTAL 32
;;;         = the SUM of the 19 group pins).  T2 holds 6 checks.
;;;   T3 -- the REAL path: run the case on the built src/emacs through
;;;         a real PTY.  A PASS or an explicit INFO skip, never a pass
;;;         on a skip.  A bad run retries once.  T3 holds 1 check.
;;;   T4 -- the (m58) registration in tool/run-tests.scm: this file
;;;         comes after test-m58-imp3.el and the older lines stay.  T4
;;;         holds 2 checks.
;;;   T5 -- the cross-corpus re-pins: the PTY case total moves from 31
;;;         to 32, so every older pin must hold 32 in the SAME commit.
;;;         T5 holds 5 checks (the last one scans EVERY corpus file);
;;;         the fifth pins the MEASURED delta of the (m58-imp4) group
;;;         comment, so a stale number fails a check.
;;;   T6 -- the guards: 9 per-group min-count guards, plus the
;;;         in-process group-total `ert-deftest' selecting ^m58-imp4.
;;;   T7 -- theme 2, the 2 pure procedures: their `define' forms, their
;;;         #:export entries, their purity (no leaf call, no emit, no
;;;         set!), their semantics through a `guile -L mod'
;;;         subprocess, and the DIRECT cross-check of the tag names on
;;;         both sides.  T7 holds 4 checks.
;;;   T8 -- theme 2, the C wiring: the 2 dispatcher resolve sites, the
;;;         tag runner, the STAYS C list, and the raw store.  T8 holds
;;;         4 checks.
;;;   T9 -- the surface re-pins (measured, not copied), the record
;;;         of the negative control, and the 3 limits L3 / L4 / L5.
;;;         T9 holds 5 checks.
;;;
;;; This corpus reads TRACKED files only (src/, mod/, test/, and
;;; tool/run-tests.scm).  It does NOT read docs/ (docs/kb.org
;;; test-must-not-read-docs).
;;;
;;; A read error is a real error, never a silent pass.  An absent
;;; TRACKED file is a real FAIL, not a pass.  Every check registers a
;;; real ERT test, so the harness parses the ERT output and the exit
;;; code is correct.

(princ "=== m58 imp-4 Group B color-mode MOVE suite ===\n")

(require 'imp-ert-report)

(defvar m58-imp4--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))
(defvar m58-imp4--registered 0
  "Total number of checks this corpus has registered.")
(defvar m58-imp4--group nil
  "The group that `m58-imp4--check' counts into: `t1' .. `t9', or nil.")
(defvar m58-imp4--counts nil
  "Alist of (GROUP . COUNT) for the registered checks.")

(defun m58-imp4--group-count (group)
  "Number of checks registered so far in GROUP."
  (or (cdr (assq group m58-imp4--counts)) 0))

(defun m58-imp4--bump-group ()
  "Count one check into `m58-imp4--group'."
  (when m58-imp4--group
    (let ((cell (assq m58-imp4--group m58-imp4--counts)))
      (if cell
          (setcdr cell (1+ (cdr cell)))
        (push (cons m58-imp4--group 1) m58-imp4--counts)))))

(defun m58-imp4--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
the symbol `m58-imp4-absent' when REL does not exist."
  (let ((path (expand-file-name rel m58-imp4--root)))
    (if (not (file-exists-p path))
        'm58-imp4-absent
      (with-temp-buffer
        (insert-file-contents path)
        (funcall fn)))))

(defun m58-imp4--contains-p (rel needle)
  "Non-nil when the TRACKED file REL contains NEEDLE.  An absent file
folds to nil, so the check prints FAIL."
  (let ((hit (m58-imp4--with rel
               (lambda ()
                 (goto-char (point-min))
                 (search-forward needle nil t)))))
    (and (not (eq hit 'm58-imp4-absent)) (and hit t))))

(defun m58-imp4--holds-all (rel needles)
  "Non-nil when the TRACKED file REL holds every NEEDLE."
  (m58-imp4--with rel
    (lambda ()
      (let ((all t))
        (dolist (needle needles)
          (goto-char (point-min))
          (unless (search-forward needle nil t) (setq all nil)))
        all))))

(defun m58-imp4--absent-p (rel needle)
  "Non-nil when the TRACKED file REL does NOT hold NEEDLE."
  (let ((hit (m58-imp4--with rel
               (lambda ()
                 (goto-char (point-min))
                 (search-forward needle nil t)))))
    (and (not (eq hit 'm58-imp4-absent)) (not hit))))

(defun m58-imp4--live-p (rel needle)
  "Non-nil when the TRACKED file REL holds NEEDLE on a line that is NOT
commented out."
  (m58-imp4--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((hit nil))
        (while (and (not hit) (search-forward needle nil t))
          (setq hit (save-excursion
                      (goto-char (line-beginning-position))
                      (not (looking-at-p "[ \t]*;")))))
        hit))))

(defun m58-imp4--ordered-p (rel needles)
  "Non-nil when the TRACKED file REL holds every NEEDLE in the GIVEN
ORDER."
  (m58-imp4--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((all t))
        (dolist (needle needles)
          (when all
            (unless (search-forward needle nil t) (setq all nil))))
        all))))

(defun m58-imp4--region (rel from to)
  "Return the text of REL between FROM and TO (TO searched after FROM).
When TO is nil the region runs to the end of the file."
  (m58-imp4--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((a (and (search-forward from nil t) (point))))
        (when a
          (if (not to)
              (buffer-substring-no-properties a (point-max))
            (let ((b (and (search-forward to nil t)
                          (- (point) (length to)))))
              (and b (< a b) (buffer-substring-no-properties a b)))))))))

(defun m58-imp4--count (rel regexp)
  "Count the matches of REGEXP in REL."
  (m58-imp4--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (re-search-forward regexp nil t) (setq n (1+ n)))
        n))))

(defun m58-imp4--count-in (text needle)
  "Count the non-overlapping occurrences of the literal NEEDLE in TEXT."
  (let ((n 0) (start 0) (re (regexp-quote needle)))
    (while (string-match re text start)
      (setq n (1+ n) start (match-end 0)))
    n))

(defun m58-imp4--pty-case-pins ()
  "Read the `test/pty-driver.py' case-count pins as (TOTAL . SUM).
TOTAL is the `total-case-count' pin; SUM is the sum of the per-group
`-case-count' pins.  Return nil when a pin is absent."
  (m58-imp4--with "test/pty-driver.py"
    (lambda ()
      (goto-char (point-min))
      (let ((total nil) (sum 0) (n 0))
        (while (re-search-forward "check(\"\\([a-z0-9-]*-case-count\\)\", " nil t)
          (let ((name (match-string 1))
                (pin (progn (re-search-forward "), \\([0-9]+\\))" nil t)
                           (match-string 1))))
            (if (string= name "total-case-count")
                (setq total (string-to-number (or pin "0")))
              (setq sum (+ sum (string-to-number (or pin "0"))))
              (setq n (1+ n)))))
        (and total (> n 0) (cons total sum))))))

(defun m58-imp4--run (prog args)
  "Run PROG with ARGS in a subprocess from the repo root and return its
combined output as a string, or the symbol `m58-imp4-prog-absent'."
  (if (not (executable-find prog))
      'm58-imp4-prog-absent
    (let ((buf (get-buffer-create " *m58-imp4-run*"))
          (default-directory m58-imp4--root))
      (unwind-protect
          (progn
            (with-current-buffer buf (erase-buffer))
            (apply #'call-process prog nil buf nil args)
            (with-current-buffer buf
              (buffer-substring-no-properties (point-min) (point-max))))
        (kill-buffer buf)))))

(defun m58-imp4--scheme (expr)
  "Evaluate EXPR with a plain `guile -L mod' and return its output."
  (m58-imp4--run "guile" (list "-L" "mod" "-c" expr)))

(defun m58-imp4--check (name ok)
  "Report and register one check.  OK is a boolean; the symbol
`m58-imp4-absent' means the TRACKED file is absent and prints FAIL."
  (let* ((absent (eq ok 'm58-imp4-absent))
         (pass (and (not absent) (and ok t))))
    (if absent
        (princ (format "FAIL m58/imp4/%s (source file absent)\n" name))
      (princ (format "%s m58/imp4/%s\n" (if pass "PASS" "FAIL") name)))
    (setq m58-imp4--registered (1+ m58-imp4--registered))
    (m58-imp4--bump-group)
    (imp-register-bool-as-ert-test (format "m58-imp4/%s" name) pass)))

(defun m58-imp4--info-skip (name reason)
  "Register one explicit INFO skip, counted into the current group."
  (princ (format "INFO m58/imp4/%s %s\n" name reason))
  (setq m58-imp4--registered (1+ m58-imp4--registered))
  (m58-imp4--bump-group)
  (imp-register-skip-as-ert-test (format "m58-imp4/%s" name) reason))

;;; --- T1. The C sites that stay C, after the MOVE --------------------

;; The MOVE adds code above the color functions, so these pins use
;; CONTENT, not line numbers: a line pin would block its own target.
;; The 2 dispatchers, the 2 hub signatures, the observable, and the
;; declaration in src/dispextern.h.
(setq m58-imp4--group 't1)

(m58-imp4--check "c/sites"
                 (and (m58-imp4--holds-all
                       "src/term.c"
                       '("static Lisp_Object m58_tty_color_mode_tag_scheme (Lisp_Object);"
                         "static Lisp_Object m58_tty_color_mode_changed_scheme (Lisp_Object,"
                         "tty_setup_colors (struct tty_display_info *tty, int mode)"
                         "set_tty_color_mode (struct tty_display_info *tty, struct frame *f)"
                         "DEFUN (\"tty-display-color-cells\", Ftty_display_color_cells,"))
                      (m58-imp4--holds-all
                       "src/dispextern.h"
                       '("extern void set_tty_color_mode (struct tty_display_info *, struct frame *);"))
                      ;; The one caller stays ONE caller.
                      (eql 1 (m58-imp4--count "src/xdisp.c"
                                              "set_tty_color_mode (FRAME_TTY (sf), sf);"))))

;; The 2 DECISIONS are DELETED from C.  A second path in C would be a C
;; dedup, not a port (brief.org section 11).
(m58-imp4--check "c/decisions-deleted"
                 (and (m58-imp4--absent-p "src/term.c" "if (mode < -1)")
                      (m58-imp4--absent-p "src/term.c" "switch (mode)")
                      (m58-imp4--absent-p "src/term.c" "case -1:")
                      (m58-imp4--absent-p "src/term.c" "case 8:")
                      (m58-imp4--absent-p "src/term.c"
                                          "(mode != tty->previous_color_mode)")))

;; The gate acts only on a non-zero FIXNUM verdict, and C keeps the RAW
;; store and the face recompute.
(m58-imp4--check "c/gate-and-raw-store"
                 (m58-imp4--holds-all
                  "src/term.c"
                  '("m58_tty_color_mode_changed_scheme (make_fixnum (mode),"
                    "make_fixnum (tty->previous_color_mode));"
                    "if (FIXNUMP (changed) && XFIXNUM (changed) != 0)"
                    "tty->previous_color_mode = mode;"
                    "tty_setup_colors (tty , mode);"
                    "safe_calln (Qtty_set_up_initial_frame_faces);"
                    ;; A non-fixnum verdict is a broken module: C acts
                    ;; as "no change" and raises no error.
                    "a broken module answers")))

;; The 3 scheme mechanisms stay C: the cap strings (with the TERMINFO
;; variants), the TN_* writes, and the default slot restore.
(m58-imp4--check "c/scheme-mechanisms-stay-c"
                 (m58-imp4--holds-all
                  "src/term.c"
                  '("tty->TN_max_colors = 0;"
                    "tty->TN_no_color_video = 0;"
                    "tty->TS_set_foreground = tty->TS_set_background = tty->TS_orig_pair = NULL;"
                    "tty->TS_orig_pair = \"\\033[0m\";"
                    "#ifdef TERMINFO"
                    "tty->TS_set_foreground = \"\\033[3%p1%dm\";"
                    "tty->TS_set_background = \"\\033[4%p1%dm\";"
                    "tty->TS_set_foreground = \"\\033[3%dm\";"
                    "tty->TS_set_background = \"\\033[4%dm\";"
                    "tty->TN_max_colors = 8;"
                    "tty_default_color_capabilities (tty, 0);"
                    "tty_default_color_capabilities (tty, 1);")))

;; The frame switch is the trigger.  The caller tests previous_frame, so
;; the PTY case must switch frames; a plain second (redisplay t) on the
;; same frame does not run the gate.
(m58-imp4--check "c/frame-switch-and-boundary"
                 (and (m58-imp4--holds-all
                       "src/xdisp.c"
                       '("if (previous_frame == NULL"
                         "|| root_frame (previous_frame) != root_frame (sf))"
                         "set_tty_color_mode (FRAME_TTY (sf), sf);"))
                      ;; The boundary rule, by name in the TRACKED C
                      ;; source (src/term.c :5484 family).
                      (m58-imp4--contains-p "src/term.c"
                                            "no Guile port owns a FILE *")))

;;; --- T2. The PTY case (theme 1) ------------------------------------

(setq m58-imp4--group 't2)

(m58-imp4--check "pty/case-and-group"
                 (and (m58-imp4--holds-all
                       "test/pty-driver.py"
                       '("\"m58-imp4/color-mode-e2e\""
                         "M58_IMP4_CASES = ("
                         "\"expect\": \"8 0 8\""
                         "\"info_report_prefix\": M58_IMP4_SKIP"
                         "\"pty_contains\": M58_IMP4_END"
                         "\"m58-imp4\","))
                      (m58-imp4--contains-p
                       "test/pty-driver.py"
                       "+ M56_IMP2_CASES + M58_IMP2_CASES + M58_IMP3_CASES")
                      (m58-imp4--contains-p
                       "test/pty-driver.py"
                       "         + M58_IMP4_CASES)")))

(m58-imp4--check "pty/case-counts-32"
                 (let ((pins (m58-imp4--pty-case-pins)))
                   (and (consp pins)
                        (eql 32 (car pins))
                        (eql (car pins) (cdr pins)))))

(m58-imp4--check "pty/case-pins-value-not-bytes"
                 (let ((case-region (m58-imp4--region
                                     "test/pty-driver.py"
                                     "M58_IMP4_CASES = ("
                                     "CASES = (M42_IMP3_CASES")))
                   (and (stringp case-region)
                        (not (string-match-p "output_span" case-region))
                        (not (string-match-p "span_requires" case-region))
                        (not (string-match-p "env_gate" case-region)))))

;; The skip is NARROW: only the probe's own prefix is an INFO skip, and
;; a WRONG value stays a FAIL.  The driver selftest pins both.
(m58-imp4--check "pty/explicit-skip-is-narrow"
                 (and (m58-imp4--contains-p
                       "test/pty-driver.py"
                       "if skip is not None and isinstance(got, str) and got.startswith(skip):")
                      (m58-imp4--contains-p
                       "test/pty-driver.py"
                       "return (\"INFO\", got[len(skip):].strip())")
                      (m58-imp4--contains-p
                       "test/pty-driver.py"
                       "check(\"m58-imp4-wrong-value-fails\"")
                      (m58-imp4--contains-p
                       "test/pty-driver.py"
                       "check(\"m58-imp4-explicit-skip-is-info\"")))

;; The sequence: mode 8, then mode -5, then mode 8 again.  -5 pins the
;; canonicalization; the third switch pins a gate that fires twice.
(m58-imp4--check "pty/switch-is-the-trigger"
                 (let ((probe (m58-imp4--region
                               "test/pty-driver.py"
                               "M58_IMP4_PROBE = r\"\"\""
                               "\"\"\"")))
                   (and (stringp probe)
                        (string-match-p "(make-frame)" probe)
                        (string-match-p "(select-frame frame)" probe)
                        (string-match-p "'tty-color-mode mode" probe)
                        (string-match-p "(redisplay #t)" probe)
                        (string-match-p "(cells)" probe)
                        (string-match-p "(switch f2 8)" probe)
                        (string-match-p "(switch f1 -5)" probe)
                        (string-match-p "(switch f2 8)" probe)
                        (not (string-match-p "(switch f1 -1)" probe)))))

(m58-imp4--check "pty/skip-is-narrow"
                 (let ((probe (m58-imp4--region
                               "test/pty-driver.py"
                               "M58_IMP4_PROBE = r\"\"\""
                               "\"\"\"")))
                   (and (stringp probe)
                        ;; ONE handler, and it wraps `make-frame' alone.
                        (eql 1 (m58-imp4--count-in probe "catch"))
                        (string-match-p "(catch #t (lambda () (make-frame))" probe)
                        ;; The skip prefix is the child's OWN report.
                        (m58-imp4--contains-p "test/pty-driver.py"
                                              "M58_IMP4_SKIP = \"m58-imp4-skip:\""))))

;;; --- T3. The real path ----------------------------------------------

(setq m58-imp4--group 't3)

(let ((emacs (expand-file-name "src/emacs" m58-imp4--root)))
  (cond
   ((not (and (file-exists-p emacs) (file-executable-p emacs)))
    (m58-imp4--info-skip "pty-real-path-color-mode" "no built src/emacs"))
   (t
    (let* ((args (list "test/pty-driver.py" "--emacs" emacs
                       "--group" "m58-imp4"))
           (out1 (m58-imp4--run "python3" args))
           (done (or (eq out1 'm58-imp4-prog-absent)
                     (string-match-p
                      "PASS m58-imp4/color-mode-e2e" out1)
                     (string-match-p
                      "INFO m58-imp4/color-mode-e2e" out1)))
           ;; The PTY cases can intermit (a timing race), so a bad run
           ;; retries ONCE before it reports.
           (out2 (unless done (m58-imp4--run "python3" args)))
           (out (or out2 out1)))
      (cond
       ((eq out1 'm58-imp4-prog-absent)
        (m58-imp4--info-skip "pty-real-path-color-mode"
                             "no python3 binary on PATH"))
       ((string-match-p "PASS m58-imp4/color-mode-e2e" out)
        (m58-imp4--check "pty-real-path-color-mode" t))
       ((string-match-p "INFO m58-imp4/color-mode-e2e" out)
        (m58-imp4--info-skip "pty-real-path-color-mode"
                             "no PTY, or no second tty frame on this host"))
       (t
        (princ (format "m58 imp4 PTY run 1 (neither PASS nor INFO):\n%s\n" out1))
        (princ (format "m58 imp4 PTY run 2 (retry):\n%s\n" out2))
        (m58-imp4--check "pty-real-path-color-mode" nil)))))))

;;; --- T4. The registration -------------------------------------------

(setq m58-imp4--group 't4)

(m58-imp4--check "run-tests-m58-imp4"
                 (and (m58-imp4--live-p "tool/run-tests.scm"
                                        "test/m58/test-m58-imp4.el")
                      (m58-imp4--live-p "tool/run-tests.scm"
                                        "(group (m58)")))

(m58-imp4--check "run-tests-m58-imp4-after-imp3"
                 (and (m58-imp4--ordered-p "tool/run-tests.scm"
                                           '("test/m58/test-m58-imp3.el"
                                             "test/m58/test-m58-imp4.el"))
                      (m58-imp4--live-p "tool/run-tests.scm"
                                        "test/m58/test-m58-imp1.el")
                      (m58-imp4--live-p "tool/run-tests.scm"
                                        "test/m58/test-m58-imp2.el")))

;;; --- T5. The cross-corpus re-pins -----------------------------------

(setq m58-imp4--group 't5)

(m58-imp4--check "repin/imp1-cases-32"
                 (and (m58-imp4--live-p "test/m58/test-m58-imp1.el"
                                        "\"pty-driver-cases-32\"")
                      (m58-imp4--live-p "test/m58/test-m58-imp1.el"
                                        "(eql 32 (car pins))")))

(m58-imp4--check "repin/imp2-cases-32"
                 (and (m58-imp4--live-p "test/m58/test-m58-imp2.el"
                                        "\"pty-case-counts-32\"")
                      (m58-imp4--live-p "test/m58/test-m58-imp2.el"
                                        "(eql 32 (car pins))")
                      (m58-imp4--live-p "test/m58/test-m58-imp2.el"
                                        "\"imp1-repinned-32\"")
                      (m58-imp4--live-p "test/m58/test-m58-imp2.el"
                                        "pty-driver-cases-32")))

(m58-imp4--check "repin/imp3-cases-32"
                 (and (m58-imp4--live-p "test/m58/test-m58-imp3.el"
                                        "\"pty/case-counts-32\"")
                      (m58-imp4--live-p "test/m58/test-m58-imp3.el"
                                        "(eql 32 (car pins))")
                      (m58-imp4--live-p "test/m58/test-m58-imp3.el"
                                        "pty-driver-cases-32")
                      (m58-imp4--live-p "test/m58/test-m58-imp3.el"
                                        "pty-case-counts-32")))

(defun m58-imp4--stale-pinners (needles)
  "Return the base names of the test/*/m*/*.el files that hold a NEEDLE."
  (let ((dirs (directory-files (expand-file-name "test" m58-imp4--root) t
                               "^m[0-9]+$"))
        (bad '()))
    (dolist (dir dirs)
      (dolist (f (directory-files dir t "\\.el\\'"))
        (with-temp-buffer
          (insert-file-contents f)
          (let ((hit nil))
            (dolist (needle needles)
              (goto-char (point-min))
              (when (search-forward needle nil t) (setq hit t)))
            (when hit (push (file-name-nondirectory f) bad))))))
    (nreverse bad)))

;; The (m58-imp4) group comment must hold the NUMBERS MEASURED at this
;; commit (cr.org section 4.2: a comment that does not hold them is a
;; defect, not a detail).  git show --numstat HEAD: C +91 / -29, Scheme
;; +46 / -1.  C GREW, so no line drop is claimed (brief.org section 14,
;; the A1 rule).
(m58-imp4--check "repin/group-comment-measured"
                 (and (m58-imp4--holds-all
                       "tool/run-tests.scm"
                       '("C delta +91 / -29"
                         "Scheme delta +46 / -1"
                         "src/term.c 6,425 lines"
                         "mod/emacs/tty-output.scm 682 lines"))
                      (m58-imp4--absent-p
                       "tool/run-tests.scm" "C delta +62 / -32")
                      (m58-imp4--absent-p
                       "tool/run-tests.scm" "Scheme delta +51 / -1")))

;; The needles are built with `concat' so that this check does not match
;; its own source.
(m58-imp4--check "repin/no-stale-31"
                 (null (m58-imp4--stale-pinners
                        (list (concat "\"pty-driver-" "cases-31\"")
                              (concat "\"pty-case-" "counts-31\"")
                              (concat "\"pty/" "case-counts-31\"")
                              (concat "\"imp1-" "repinned-31\"")
                              (concat "(eql " "31 (car pins))")))))

;;; --- T7. Theme 2: the 2 pure procedures -----------------------------

(setq m58-imp4--group 't7)

(m58-imp4--check "scheme/definitions-and-exports"
                 (and (m58-imp4--holds-all
                       "mod/emacs/tty-output.scm"
                       '("(define (tty-color-mode-tag mode)"
                         "(define (tty-color-mode-changed-p mode previous)"
                         "tty-color-mode-tag tty-color-mode-changed-p))"))))

;; Purity: the 2 procedures hold no leaf call, no emit, and no set!.
(m58-imp4--check "scheme/purity"
                 (let ((body (m58-imp4--region "mod/emacs/tty-output.scm"
                                               "(define (tty-color-mode-tag mode)"
                                               nil)))
                   (and (stringp body)
                        (not (string-match-p "%--tty" body))
                        (not (string-match-p "emit" body))
                        (not (string-match-p "set!" body))
                        (not (string-match-p "defelisp" body)))))

;; The semantics of the 5 mode rows and the -5 / -1 raw pair, on the
;; REAL module through a plain `guile -L mod'.  A missing guile is an
;; explicit INFO skip, never a pass.
(let* ((expr (concat "(let ((m (resolve-module '(emacs tty-output))))"
                     "(format #t \"~s|~s|~s|~s|~s|~s|~s|~s\" "
                     "((module-ref m 'tty-color-mode-tag) -5) "
                     "((module-ref m 'tty-color-mode-tag) -1) "
                     "((module-ref m 'tty-color-mode-tag) 0) "
                     "((module-ref m 'tty-color-mode-tag) 8) "
                     "((module-ref m 'tty-color-mode-tag) 42) "
                     "((module-ref m 'tty-color-mode-changed-p) -5 -1) "
                     "((module-ref m 'tty-color-mode-changed-p) 8 8) "
                     "((module-ref m 'tty-color-mode-changed-p) -1 -5)))"))
       (out (m58-imp4--scheme expr)))
  (cond
   ((eq out 'm58-imp4-prog-absent)
    (m58-imp4--info-skip "scheme/semantics" "no guile on PATH"))
   (t
    (m58-imp4--check "scheme/semantics"
                     (and (stringp out)
                          (string-match-p
                           (regexp-quote
                            "(\"none\")|(\"none\")|(\"default\")|(\"ansi-8\")|(\"default\")|1|0|1")
                           out))))))

;; The DIRECT cross-check of the 2 sides (brief.org section 12, L5): the
;; tag NAMES are DERIVED from src/term.c and from a `guile -L mod'
;; subprocess, then compared as a SET.  The earlier "c/tag-runner"
;; check pins the 2 sides, but a single edit could still drift one side
;; alone and stay green.  This check fails when either side drifts.
(defun m58-imp4--c-tag-names ()
  "The tag NAMEs that tty_setup_colors tests in the TRACKED src/term.c."
  (m58-imp4--with
   "src/term.c"
   (lambda ()
     (goto-char (point-min))
     (let ((names '()))
       (while (re-search-forward
               "m52_tty_step_tag_p (tag, \"\\([^\"]+\\)\")" nil t)
         (push (match-string 1) names))
       (sort (delete-dups (nreverse names)) #'string<)))))

(let* ((c-names (m58-imp4--c-tag-names))
       (expr (concat "(let ((tag (module-ref (resolve-module "
                     "'(emacs tty-output)) 'tty-color-mode-tag))) "
                     "(for-each (lambda (mode) "
                     "(format #t \"~a\\n\" (car (tag mode)))) "
                     "(list -5 -1 0 8 42)))"))
       (out (m58-imp4--scheme expr)))
  (cond
   ((eq out 'm58-imp4-prog-absent)
    (m58-imp4--info-skip "scheme/tag-strings-match-C" "no guile on PATH"))
   (t
    (m58-imp4--check
     "scheme/tag-strings-match-C"
     (let ((scheme-names (and (stringp out)
                              (sort (delete-dups
                                     (split-string (or out "") "[\n \t]+" t))
                                    #'string<))))
       (and (listp c-names)
            (equal c-names '("ansi-8" "default" "none"))
            (equal scheme-names c-names)))))))

;;; --- T8. Theme 2: the C wiring --------------------------------------

(setq m58-imp4--group 't8)

(m58-imp4--check "c/dispatcher-resolve-sites"
                 (and (m58-imp4--holds-all
                       "src/term.c"
                       '("proc = scm_c_public_ref (\"emacs tty-output\", \"tty-color-mode-tag\");"
                         "\"tty-color-mode-changed-p\");"
                         "return SCM_CALL_1 (proc, mode);"
                         "return SCM_CALL_2 (proc, mode, previous);"))))

;; The 3 tag strings must match the Scheme names BYTE FOR BYTE on both
;; sides: a drifted tag emits nothing and raises no error.
(m58-imp4--check "c/tag-runner"
                 (and (m58-imp4--holds-all
                       "src/term.c"
                       '("m52_tty_step_tag_p (tag, \"none\")"
                         "m52_tty_step_tag_p (tag, \"ansi-8\")"
                         "m52_tty_step_tag_p (tag, \"default\")"))
                      (m58-imp4--holds-all
                       "mod/emacs/tty-output.scm"
                       '("(list \"none\")" "(list \"ansi-8\")"
                         "(list \"default\")"))))

;; The STAYS C list of brief.org section 5.3.
(m58-imp4--check "c/stays-c"
                 (m58-imp4--holds-all
                  "src/term.c"
                  '("assq_no_quit (Qtty_color_mode, f->param_alist)"
                    "Fassq (val, Fsymbol_value (tty_color_mode_alist))"
                    "TYPE_RANGED_FIXNUMP (int, color_mode) ? XFIXNUM (color_mode) : 0"
                    "static int default_max_colors;"
                    "dupstring (&default_orig_pair, tty->TS_orig_pair);")))

(m58-imp4--check "c/raw-store-and-nonfixnum-verdict"
                 (and (m58-imp4--contains-p
                       "src/term.c"
                       "tty->previous_color_mode = mode;")
                      (m58-imp4--contains-p
                       "src/term.c"
                       "if (FIXNUMP (changed) && XFIXNUM (changed) != 0)")
                      ;; The compare is on the RAW modes, so -5 and -1
                      ;; are a change even though both give ("none").
                      (m58-imp4--contains-p
                       "mod/emacs/tty-output.scm"
                       "(if (= mode previous) 0 1)")))

;;; --- T9. The surface and the negative control -----------------------

;; Measured on this tree AFTER the MOVE (not copied from HEAD):
;;   src/term.c                    6425 lines
;;   scm_c_public_ref in term.c    41  (HEAD: 39)
;;   scm_c_public_ref tree-wide    265 (HEAD: 263)
;;   mod/emacs/tty-output.scm      682 lines (HEAD: 637)
(setq m58-imp4--group 't9)

(m58-imp4--check "surface/term-c-lines"
                 (eql 6425 (m58-imp4--count "src/term.c" "\n")))

(defun m58-imp4--src-public-refs ()
  "Count the scm_c_public_ref sites in every src/*.c and src/*.h file."
  (let ((dir (expand-file-name "src" m58-imp4--root))
        (n 0))
    (dolist (f (directory-files dir t "\\.\\(c\\|h\\)\\'"))
      (with-temp-buffer
        (insert-file-contents f)
        (goto-char (point-min))
        (while (re-search-forward "scm_c_public_ref" nil t)
          (setq n (1+ n)))))
    n))

(m58-imp4--check "surface/public-refs"
                 (and (eql 41 (m58-imp4--count "src/term.c" "scm_c_public_ref"))
                      (eql 265 (m58-imp4--src-public-refs))))

(m58-imp4--check "surface/module-lines"
                 (eql 682 (m58-imp4--count "mod/emacs/tty-output.scm" "\n")))

;; The negative control (brief.org section 7): with
;; tty-color-mode-changed-p forced to 0, the case reports "8 8 8", not
;; "8 0 8".  The first value repeats, so the SECOND switch never
;; reaches tty_setup_colors.  The edit was reverted; the measured
;; result is in the M58_IMP4 group comment of test/pty-driver.py.
(m58-imp4--check "negative-control-record"
                 (and (m58-imp4--contains-p
                       "test/pty-driver.py"
                       "Negative control")
                      (m58-imp4--contains-p
                       "test/pty-driver.py"
                       "forced to return 0")
                      (m58-imp4--contains-p
                       "test/pty-driver.py"
                       "\"8 8 8\", not \"8 0 8\"")))

;; cr.org sections 7 and 9.3: the 3 limits must be in the durable
;; record and in the group comment, not only in the review.
(m58-imp4--check "record/limits-written-down"
                 (m58-imp4--holds-all
                  "tool/run-tests.scm"
                  '("L3 no C fallback"
                    "L4 the extra crossing is not measured"
                    "L5 a tag that drifts from the Scheme names")))

;;; --- T6. The guards -------------------------------------------------

;; An --filter that matches no group reports exit 0 with 0 tests, so a
;; green m58 gate proves nothing until the corpus really registers.
(setq m58-imp4--group 't6)

(m58-imp4--check "reg/min-t1-checks-5" (>= (m58-imp4--group-count 't1) 5))
(m58-imp4--check "reg/min-t2-checks-6" (>= (m58-imp4--group-count 't2) 6))
(m58-imp4--check "reg/min-t3-checks-1" (>= (m58-imp4--group-count 't3) 1))
(m58-imp4--check "reg/min-t4-checks-2" (>= (m58-imp4--group-count 't4) 2))
(m58-imp4--check "reg/min-t5-checks-5" (>= (m58-imp4--group-count 't5) 5))
(m58-imp4--check "reg/min-t7-checks-4" (>= (m58-imp4--group-count 't7) 4))
(m58-imp4--check "reg/min-t8-checks-4" (>= (m58-imp4--group-count 't8) 4))
(m58-imp4--check "reg/min-t9-checks-5" (>= (m58-imp4--group-count 't9) 5))
(m58-imp4--check "reg/min-t6-prior-checks-8"
                 ;; This guard counts 8 prior guards; it becomes the 9th.
                 (>= (m58-imp4--group-count 't6) 8))

;;; --- The group-total check ------------------------------------------

;; The measured count of m58-imp4 tests: 41 registered checks (T1 5,
;; T2 6, T3 1, T4 2, T5 5, T6 9, T7 4, T8 4, T9 5) plus the
;; group-total deftest itself.  The T3 and T7 checks may fold to a
;; controlled INFO skip on a host with no built src/emacs, no PTY, or
;; no guile, and a controlled skip is still a registered test.

(defvar m58-imp4--gate-total 42
  "The EXACT number of m58-imp4 ERT tests: 41 registered checks (T1 5,
T2 6, T3 1, T4 2, T5 5, T6 9, T7 4, T8 4, T9 5) plus the group-total
deftest itself.  The guard uses `equal', not `>=', so a DUPLICATE
registration fails too.")

(ert-deftest m58-imp4/gate-m58-total ()
  "The m58-imp4 corpus registers exactly its docs-independent count."
  (should (equal (length (ert-select-tests "^m58-imp4" t))
                 m58-imp4--gate-total)))

(princ (format "=== m58 imp-4 suite done (%d checks; t1 %d, t2 %d, t3 %d, t4 %d, t5 %d, t6 %d, t7 %d, t8 %d, t9 %d) ===\n"
               m58-imp4--registered
               (m58-imp4--group-count 't1)
               (m58-imp4--group-count 't2)
               (m58-imp4--group-count 't3)
               (m58-imp4--group-count 't4)
               (m58-imp4--group-count 't5)
               (m58-imp4--group-count 't6)
               (m58-imp4--group-count 't7)
               (m58-imp4--group-count 't8)
               (m58-imp4--group-count 't9)))
