;;; test-m58-imp3.el --- M58 imp-3 the Group A face-appearance MOVE corpus.
;;;
;;; M58 imp-3 MOVES the face-appearance DECISION of src/term.c to
;;; (emacs tty-output): turn_on_face, turn_off_face, and tty_capable_p
;;; no longer decide anything.  C keeps every mechanism (the struct face
;;; field reads, MAY_USE_WITH_COLORS_P, the TS_* / TF_* / TN_* reads,
;;; face_tty_specified_color, the strcmp of the exit sequences, tparam,
;;; the OUTPUT / OUTPUT1 / OUTPUT_IF macros, tty_toggle_highlight, the
;;; standout_mode clear, and the FILE * streams).
;;;
;;; This corpus pins:
;;;
;;;   U1 -- the 3 pure Scheme procedures in mod/emacs/tty-output.scm:
;;;         tty-face-on-steps, tty-face-off-steps, tty-capable-p, their
;;;         #:export entries, their purity (no leaf call, no emit, no
;;;         module state), and the published step protocol.  U1 holds 4
;;;         checks.
;;;   U2 -- the REAL behaviour: a plain `guile -L mod -c' subprocess
;;;         calls the 3 procedures with plain fixnums and the corpus
;;;         checks the returned step lists and verdicts against the C
;;;         semantics they replaced.  A missing guile is an explicit INFO
;;;         skip, never a pass.  U2 holds 5 checks.
;;;   U3 -- the C wiring in src/term.c: the 3 dispatcher resolve sites,
;;;         the step walker and the mechanisms that STAY C, the 7
;;;         non-parameterized face keys in m52_caps, the 4 tparam keys
;;;         that must NOT be there, and the DELETED inline decision.
;;;         U3 holds 6 checks.
;;;   U4 -- the 5 real-path PTY cases in test/pty-driver.py: their names,
;;;         the (m58-imp3) group, the case-count pins (TOTAL 32 = the SUM
;;;         of the 19 group pins), the distinct marker spans, and the
;;;         ordered needle run of the color case.  U4 holds 4 checks.
;;;   U5 -- the cross-corpus re-pins: this MOVE moves the src/term.c and
;;;         mod/emacs/tty-output.scm line counts, the scm_c_public_ref
;;;         counts, the PTY case total, and the hub signature lines.  The
;;;         older corpora must hold the re-pins in the SAME commit.
;;;         U5 holds 4 checks (the last one scans EVERY corpus file).
;;;   U6 -- the guards: 5 per-group min-count guards, plus the in-process
;;;         group-total `ert-deftest' selecting ^m58-imp3.
;;;
;;; This corpus reads TRACKED files only (src/, mod/,
;;; test/pty-driver.py, tool/run-tests.scm, and the older
;;; test/m58/test-m58-imp1.el and test-m58-imp2.el).  It does NOT read
;;; docs/ (docs/kb.org test-must-not-read-docs).
;;;
;;; A read error is a real error, never a silent pass.  An absent TRACKED
;;; file is a real FAIL, not a pass.  Every check registers a real ERT
;;; test, so the harness parses the ERT output and the exit code is
;;; correct.

(princ "=== m58 imp-3 Group A face-appearance MOVE suite ===\n")

(require 'imp-ert-report)

(defvar m58-imp3--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))
(defvar m58-imp3--registered 0
  "Total number of checks this corpus has registered.")
(defvar m58-imp3--group nil
  "The group that `m58-imp3--check' counts into: `u1' .. `u6', or nil.")
(defvar m58-imp3--counts nil
  "Alist of (GROUP . COUNT) for the registered checks.")

(defun m58-imp3--group-count (group)
  "Number of checks registered so far in GROUP."
  (or (cdr (assq group m58-imp3--counts)) 0))

(defun m58-imp3--bump-group ()
  "Count one check into `m58-imp3--group'."
  (when m58-imp3--group
    (let ((cell (assq m58-imp3--group m58-imp3--counts)))
      (if cell
          (setcdr cell (1+ (cdr cell)))
        (push (cons m58-imp3--group 1) m58-imp3--counts)))))

(defun m58-imp3--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
the symbol `m58-imp3-absent' when REL does not exist."
  (let ((path (expand-file-name rel m58-imp3--root)))
    (if (not (file-exists-p path))
        'm58-imp3-absent
      (with-temp-buffer
        (insert-file-contents path)
        (funcall fn)))))

(defun m58-imp3--contains-p (rel needle)
  "Non-nil when the TRACKED file REL contains NEEDLE.  An absent file
folds to nil, so the check prints FAIL."
  (let ((hit (m58-imp3--with rel
               (lambda ()
                 (goto-char (point-min))
                 (search-forward needle nil t)))))
    (and (not (eq hit 'm58-imp3-absent)) (and hit t))))

(defun m58-imp3--holds-all (rel needles)
  "Non-nil when the TRACKED file REL holds every NEEDLE."
  (m58-imp3--with rel
    (lambda ()
      (let ((all t))
        (dolist (needle needles)
          (goto-char (point-min))
          (unless (search-forward needle nil t) (setq all nil)))
        all))))

(defun m58-imp3--absent-p (rel needle)
  "Non-nil when the TRACKED file REL does NOT hold NEEDLE.  Used for the
literals the MOVE DELETED: a re-introduced inline C decision FAILS here."
  (let ((hit (m58-imp3--with rel
               (lambda ()
                 (goto-char (point-min))
                 (search-forward needle nil t)))))
    (and (not (eq hit 'm58-imp3-absent)) (not hit))))

(defun m58-imp3--live-p (rel needle)
  "Non-nil when the TRACKED file REL holds NEEDLE on a line that is NOT
commented out."
  (m58-imp3--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((hit nil))
        (while (and (not hit) (search-forward needle nil t))
          (setq hit (save-excursion
                      (goto-char (line-beginning-position))
                      (not (looking-at-p "[ \t]*;")))))
        hit))))

(defun m58-imp3--ordered-p (rel needles)
  "Non-nil when the TRACKED file REL holds every NEEDLE in the GIVEN
ORDER."
  (m58-imp3--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((all t))
        (dolist (needle needles)
          (when all
            (unless (search-forward needle nil t) (setq all nil))))
        all))))

(defun m58-imp3--line-text (rel n)
  "Return the text of the 1-based line N of REL, or nil."
  (m58-imp3--with rel
    (lambda ()
      (goto-char (point-min))
      (when (zerop (forward-line (1- n)))
        (buffer-substring-no-properties (line-beginning-position)
                                       (line-end-position))))))

(defun m58-imp3--lines (rel)
  "Number of lines of REL, or nil."
  (m58-imp3--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (not (eobp)) (forward-line 1) (setq n (1+ n)))
        n))))

(defun m58-imp3--count (rel regexp)
  "Count the matches of REGEXP in REL."
  (m58-imp3--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (re-search-forward regexp nil t) (setq n (1+ n)))
        n))))

(defun m58-imp3--region (rel from to)
  "Return the text of REL between FROM and TO (TO searched after FROM).
When TO is nil the region runs to the end of the file."
  (m58-imp3--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((a (and (search-forward from nil t) (point))))
        (when a
          (if (not to)
              (buffer-substring-no-properties a (point-max))
            (let ((b (and (search-forward to nil t)
                          (- (point) (length to)))))
              (and b (< a b) (buffer-substring-no-properties a b)))))))))

(defun m58-imp3--pty-case-pins ()
  "Read the `test/pty-driver.py' case-count pins as (TOTAL . SUM).
TOTAL is the `total-case-count' pin; SUM is the sum of the per-group
`-case-count' pins.  Return nil when a pin is absent."
  (m58-imp3--with "test/pty-driver.py"
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

(defun m58-imp3--run (prog args)
  "Run PROG with ARGS in a subprocess from the repo root and return its
combined output as a string, or the symbol `m58-imp3-prog-absent'."
  (if (not (executable-find prog))
      'm58-imp3-prog-absent
    (let ((buf (get-buffer-create " *m58-imp3-run*"))
          (default-directory m58-imp3--root))
      (unwind-protect
          (progn
            (with-current-buffer buf (erase-buffer))
            (apply #'call-process prog nil buf nil args)
            (with-current-buffer buf
              (buffer-substring-no-properties (point-min) (point-max))))
        (kill-buffer buf)))))

(defun m58-imp3--scheme (expr)
  "Evaluate EXPR with a plain `guile -L mod' and return its output, or
the symbol `m58-imp3-prog-absent' when guile is not on PATH."
  (m58-imp3--run "guile" (list "-L" "mod" "-c" expr)))

(defun m58-imp3--check (name ok)
  "Report and register one check.  OK is a boolean; the symbol
`m58-imp3-absent' means the TRACKED file is absent and prints FAIL."
  (let* ((absent (eq ok 'm58-imp3-absent))
         (pass (and (not absent) (and ok t))))
    (if absent
        (princ (format "FAIL m58/imp3/%s (source file absent)\n" name))
      (princ (format "%s m58/imp3/%s\n" (if pass "PASS" "FAIL") name)))
    (setq m58-imp3--registered (1+ m58-imp3--registered))
    (m58-imp3--bump-group)
    (imp-register-bool-as-ert-test (format "m58-imp3/%s" name) pass)))

(defun m58-imp3--info-skip (name reason)
  "Register one explicit INFO skip, counted into the current group."
  (princ (format "INFO m58/imp3/%s %s\n" name reason))
  (setq m58-imp3--registered (1+ m58-imp3--registered))
  (m58-imp3--bump-group)
  (imp-register-skip-as-ert-test (format "m58-imp3/%s" name) reason))

;;; --- U1. The 3 pure Scheme procedures -------------------------------

;; The MOVE is only a MOVE when the DECISION is in Scheme.  These pins
;; hold the 3 procedure definitions, their export, their purity (a
;; procedure that called a leaf would emit bytes itself), and the
;; published step protocol, so a reader can check a KEY against
;; m52_caps[] without reading C.

(setq m58-imp3--group 'u1)

(m58-imp3--check "scheme/procedures-defined"
                 (m58-imp3--holds-all
                  "mod/emacs/tty-output.scm"
                  '("(define (tty-face-on-steps args)"
                    "(define (tty-face-off-steps has-me attrs has-exit-underline"
                    "(define (tty-capable-p caps presence no-color-video max-colors)")))

(m58-imp3--check "scheme/procedures-exported"
                 (m58-imp3--holds-all
                  "mod/emacs/tty-output.scm"
                  '("tty-face-on-steps tty-face-off-steps tty-capable-p")))

;; Purity: the 3 procedures name no C leaf and no emit helper.  A leaf
;; call inside them would be a passthrough, not a port
;; (docs/kb.org leaf-must-call-the-mechanism).
(let ((on (m58-imp3--region "mod/emacs/tty-output.scm"
                            "(define (tty-face-on-steps args)"
                            ";; The step list of turn_off_face"))
      (off (m58-imp3--region "mod/emacs/tty-output.scm"
                             "(define (tty-face-off-steps has-me attrs"
                             ";; The verdict of tty_capable_p"))
      (cap (m58-imp3--region "mod/emacs/tty-output.scm"
                             "(define (tty-capable-p caps presence"
                             nil)))
  (m58-imp3--check "scheme/procedures-pure"
                   (and (stringp on) (stringp off) (stringp cap)
                        (not (string-match-p "%--tty-" on))
                        (not (string-match-p "%--tty-" off))
                        (not (string-match-p "%--tty-" cap))
                        (not (string-match-p "tty-emit" on))
                        (not (string-match-p "(set!" cap)))))

;; The step protocol comment must publish all 5 step kinds: C tells them
;; apart with m52_tty_step_tag_p, so a wrong tag emits nothing.
(m58-imp3--check "scheme/protocol-documented"
                 (m58-imp3--holds-all
                  "mod/emacs/tty-output.scm"
                  '("(\"cap1\" KEY)"
                    "(\"cap\" KEY)"
                    "(\"tparam\" SLOT V)"
                    "(\"toggle-highlight\")"
                    "(\"clear-standout\")")))

;;; --- U2. The real behaviour of the decision -------------------------

;; The source pins above prove the shape; they do NOT prove the decision.
;; These checks RUN the 3 procedures with a plain `guile -L mod' and
;; compare the returned step lists and verdicts with the C semantics the
;; MOVE replaced.  A missing guile is an explicit INFO skip.

(setq m58-imp3--group 'u2)

;; attrs 1 = bold, may 2 = bold may be used with colors, colors 1.
(let ((out (m58-imp3--scheme
            (concat "(use-modules (emacs tty-output)) "
                    "(write (tty-face-on-steps (list 0 1 0 2 0 1 0 0 0 0)))"))))
  (if (eq out 'm58-imp3-prog-absent)
      (m58-imp3--info-skip "scheme/on-bold" "no guile on PATH")
    (m58-imp3--check "scheme/on-bold"
                     (string-match-p "((\"cap1\" \"bold\"))" out))))

;; The ORDER: reverse FIRST, then bold, then italic, then underline, then
;; strike-through, then the colors.  Reverse video comes first because
;; TS_end_standout_mode may equal TS_exit_attribute_mode.
(let ((out (m58-imp3--scheme
            (concat "(use-modules (emacs tty-output)) (write (tty-face-on-steps "
                    "(list 1 15 1 31 243 1 0 1 4 2)))"))))
  (if (eq out 'm58-imp3-prog-absent)
      (m58-imp3--info-skip "scheme/on-order" "no guile on PATH")
    (m58-imp3--check "scheme/on-order"
                     (string-match-p
                      (concat "(\"toggle-highlight\") (\"cap1\" \"bold\") "
                              "(\"cap1\" \"italic\") (\"cap1\" \"underline\") "
                              "(\"cap1\" \"strike-through\") "
                              "(\"tparam\" 0 1) (\"tparam\" 1 4) (\"tparam\" 2 2)")
                      out))))

;; The off decision: the "me" path plus the standout clear, then the
;; reset pair.  Without "me" only the underline exit sequence is used,
;; and attrs 0 with "me" present emits NOTHING.
(let ((out (m58-imp3--scheme
            (concat "(use-modules (emacs tty-output)) (write (list "
                    "(tty-face-off-steps 1 1 0 1 1 1 1) "
                    "(tty-face-off-steps 0 4 1 0 0 0 0) "
                    "(tty-face-off-steps 1 0 1 0 0 0 0)))"))))
  (if (eq out 'm58-imp3-prog-absent)
      (m58-imp3--info-skip "scheme/off-steps" "no guile on PATH")
    (m58-imp3--check "scheme/off-steps"
                     (and (string-match-p
                           (concat "((\"cap1\" \"exit-attribute\") "
                                   "(\"clear-standout\") (\"cap1\" \"orig-pair\"))")
                           out)
                          (string-match-p "((\"cap\" \"exit-underline\"))" out)
                          (string-match-p " ()" out)))))

;; brief.org section 10.4: the no-"me" branch must test the UNDERLINE bit
;; of attrs (4), not the presence flag alone.  The C source tests
;; face->underline (src/term.c :2352 ... :2358) before OUTPUT_IF.  A face
;; with no underline on a terminal with no "me" emits NOTHING; a branch
;; that tests only the presence flag emits the underline exit string
;; there, which is a silent byte change.
(let ((out (m58-imp3--scheme
            (concat "(use-modules (emacs tty-output)) (write (list "
                    "(tty-face-off-steps 0 1 1 0 0 0 0) "
                    "(tty-face-off-steps 0 0 1 0 0 0 0) "
                    "(tty-face-off-steps 0 4 1 0 0 0 0)))"))))
  (if (eq out 'm58-imp3-prog-absent)
      (m58-imp3--info-skip "scheme/off-no-me-underline" "no guile on PATH")
    (m58-imp3--check "scheme/off-no-me-underline"
                     (string-match-p
                      (regexp-quote "(() () ((\"cap\" \"exit-underline\")))")
                      out))))

;; The capable-p table: one row per TTY_CAPABLE_P_TRY check.  A missing
;; capability or a NC bit blocks; no colors (max-colors 0) never blocks.
(let ((out (m58-imp3--scheme
            (concat "(use-modules (emacs tty-output)) (write (list "
                    "(tty-capable-p 4 8 0 8) "
                    "(tty-capable-p 4 0 0 8) "
                    "(tty-capable-p 1 1 4 8) "
                    "(tty-capable-p 1 1 4 0) "
                    "(tty-capable-p 32 64 64 8) "
                    "(tty-capable-p 2 2 0 8)))"))))
  (if (eq out 'm58-imp3-prog-absent)
      (m58-imp3--info-skip "scheme/capable-p" "no guile on PATH")
    (m58-imp3--check "scheme/capable-p"
                     (string-match-p "(1 0 0 1 0 0)" out))))

;;; --- U3. The C wiring ----------------------------------------------

;; The 3 hubs now call a dispatcher, and the mechanism STAYS C.  A
;; re-introduced inline decision FAILS here.

(setq m58-imp3--group 'u3)

(m58-imp3--check "c/dispatcher-sites"
                 (m58-imp3--holds-all
                  "src/term.c"
                  '("proc = scm_c_public_ref (\"emacs tty-output\", \"tty-face-on-steps\");"
                    "proc = scm_c_public_ref (\"emacs tty-output\", \"tty-face-off-steps\");"
                    "proc = scm_c_public_ref (\"emacs tty-output\", \"tty-capable-p\");"
                    "m58_tty_face_on_scheme (Lisp_Object args)"
                    "m58_tty_face_off_scheme (Lisp_Object has_me"
                    "m58_tty_capable_p_scheme (Lisp_Object caps")))

(m58-imp3--check "c/mechanism-stays-c"
                 (m58-imp3--holds-all
                  "src/term.c"
                  '("m58_tty_face_step_run (struct tty_display_info *tty, Lisp_Object step)"
                    "p = tparam (ts, NULL, 0, a[1], 0, 0, 0);"
                    "OUTPUT (tty, p);"
                    "OUTPUT1_IF (tty, m52_cap_string_1 (tty, CONSP (XCDR (step))"
                    "OUTPUT_IF (tty, m52_cap_string_1 (tty, step));"
                    "tty_toggle_highlight (tty);"
                    "tty->standout_mode = 0;"
                    "strcmp (tty->TS_exit_attribute_mode,")))

;; The 7 non-parameterized face keys are in m52_caps[]; the 4 tparam
;; strings are NOT (an emit without tparam would change the bytes).
(m58-imp3--check "c/m52-caps-face-keys"
                 (and (m58-imp3--holds-all
                       "src/term.c"
                       '("M52_CAP (\"bold\", TS_enter_bold_mode),"
                         "M52_CAP (\"dim\", TS_enter_dim_mode),"
                         "M52_CAP (\"italic\", TS_enter_italic_mode),"
                         "M52_CAP (\"underline\", TS_enter_underline_mode),"
                         "M52_CAP (\"strike-through\", TS_enter_strike_through_mode),"
                         "M52_CAP (\"exit-attribute\", TS_exit_attribute_mode),"
                         "M52_CAP (\"exit-underline\", TS_exit_underline_mode)"))
                      (m58-imp3--absent-p
                       "src/term.c" "M52_CAP (\"set-foreground\"")
                      (m58-imp3--absent-p
                       "src/term.c" "M52_CAP (\"set-background\"")
                      (m58-imp3--absent-p
                       "src/term.c" "M52_CAP (\"set-underline-style\"")
                      (m58-imp3--absent-p
                       "src/term.c" "M52_CAP (\"set-underline-color\"")))

;; The inline C decision is DELETED.  A second copy in C would be dead
;; policy: the Scheme procedure is the only route (brief.org step 3).
(m58-imp3--check "c/inline-decision-deleted"
                 (and (m58-imp3--absent-p
                       "src/term.c" "#define TTY_CAPABLE_P_TRY(tty, cap, TS, NC_bit)")
                      (m58-imp3--absent-p
                       "src/term.c"
                       "if (face->tty_bold_p && MAY_USE_WITH_COLORS_P (tty, NC_BOLD))")
                      (m58-imp3--absent-p
                       "src/term.c" "OUTPUT1_IF (tty, tty->TS_enter_bold_mode);")))

;; cr.org F1: turn_on_face must pass the POST-toggle standout state.  The
;; ("toggle-highlight") step flips tty->standout_mode BEFORE the color
;; steps, so C computes the plain post-toggle value from the SAME two
;; inputs Scheme uses (the may bit 1 and the reverse verdict) and passes
;; it.  The pre-fix code read the stale value, which swapped the setaf and
;; setab slots for a reverse-video face with an explicit color.
;;
;; HONEST LIMIT: no PTY case pins this row on this host.  The child tty
;; color map resolves every color name -- including the frame defaults --
;; to a real index, so face->foreground / face->background never hold the
;; FACE_TTY_DEFAULT_* sentinels and the C reverse branch is not reached
;; (measured 2026-10-18: four inverse-video face specs produced
;; byte-identical spans and no reverse "rev" byte).  This pin is therefore
;; a SOURCE pin of the restored C semantics, not a byte measurement.
(m58-imp3--check "c/f1-post-toggle-standout"
                 (and (m58-imp3--holds-all
                       "src/term.c"
                       '("int will_toggle = (may & 0x01) && reverse;"
                         "int standout_after = will_toggle ? !standout : standout;"
                         "const char *fg_slot = standout_after ? tty->TS_set_background"
                         "make_fixnum (standout_after),"))
                      (m58-imp3--absent-p "src/term.c" "make_fixnum (standout),")))

;; cr.org F2 and F3.  F2: the step runner holds NO bare-KEY arm -- the M52
;; hubs read a bare string as OUTPUT_IF (frame-padded), so a second meaning
;; that reads it as OUTPUT1_IF is a trap (brief.org section 9.1).  F3:
;; tty_capable_p holds no dead "answers true" fallback; a non-fixnum
;; verdict answers false, so a broken module cannot claim capability.
(m58-imp3--check "c/f2-f3-review-fixes"
                 (and (m58-imp3--absent-p
                       "src/term.c"
                       "if (STRINGP (step))\n    OUTPUT1_IF (tty, m52_cap_string_1 (tty, step));")
                      (m58-imp3--contains-p
                       "src/term.c"
                       "return (FIXNUMP (verdict) && XFIXNUM (verdict) != 0);")))

;;; --- U4. The 5 real-path PTY cases ---------------------------------

(setq m58-imp3--group 'u4)

(m58-imp3--check "pty/cases-and-group"
                 (and (m58-imp3--holds-all
                       "test/pty-driver.py"
                       '("\"m58-imp3/face-off-e2e\""
                         "\"m58-imp3/face-italic-e2e\""
                         "\"m58-imp3/face-underline-e2e\""
                         "\"m58-imp3/face-color-e2e\""
                         "\"m58-imp3/capable-p-e2e\""
                         "M58_IMP3_CASES = ("
                         "\"m58-imp3\")"))
                      (m58-imp3--contains-p
                       "test/pty-driver.py"
                       "+ M58_IMP3_CASES")))

(m58-imp3--check "pty/case-counts-32"
                 (let ((pins (m58-imp3--pty-case-pins)))
                   (and (consp pins)
                        (eql 32 (car pins))
                        ;; The 19 group pins must add up to the total, so
                        ;; a group pin that moves alone FAILS.
                        (eql (car pins) (cdr pins)))))

;; Every case carries its OWN marker pair: two cases must never share
;; one, or a byte of one case could satisfy the other.
(m58-imp3--check "pty/distinct-spans"
                 (m58-imp3--holds-all
                  "test/pty-driver.py"
                  '("M58_IMP3_OFF_BEGIN = b\"M58I3-OFF-BEGIN!\""
                    "M58_IMP3_ITALIC_BEGIN = b\"M58I3-ITA-BEGIN!\""
                    "M58_IMP3_UL_BEGIN = b\"M58I3-UL-BEGIN!\""
                    "M58_IMP3_COLOR_BEGIN = b\"M58I3-COL-BEGIN!\""
                    "M58_IMP3_CAP_BEGIN = b\"M58I3-CAP-BEGIN!\"")))

;; The color case pins an ORDERED needle run, so the color bytes are
;; bound to the face's own turn_on_face call and not to the default-face
;; prefix.  The capable-p case reports a Lisp value, not a byte.
(m58-imp3--check "pty/color-order-and-capable-value"
                 (and (m58-imp3--contains-p
                       "test/pty-driver.py"
                       "\"needles_in_order\": (M58_IMP3_BOLD, M58_IMP3_SETAF_RED,")
                      (m58-imp3--contains-p
                       "test/pty-driver.py"
                       "\"expect_terminfo\": ((\"bold\", \"bold\"), (\"italic\", \"sitm\"),")
                      (m58-imp3--contains-p
                       "test/pty-driver.py"
                       "display-supports-face-attributes-p")))

;;; --- U5. The cross-corpus re-pins -----------------------------------

;; The MOVE changes the src/term.c and mod/emacs/tty-output.scm line
;; counts, both scm_c_public_ref counts, and the PTY case total.  The
;; older corpora must hold the re-pins in the SAME commit, else the m58
;; gate goes red on a stale pin.

(setq m58-imp3--group 'u5)

(m58-imp3--check "repin/imp1-surface"
                 (and (m58-imp3--contains-p
                       "test/m58/test-m58-imp1.el"
                       "(eql 6425 (m58-imp1--lines \"src/term.c\"))")
                      (m58-imp3--contains-p
                       "test/m58/test-m58-imp1.el"
                       "(eql 41 (m58-imp1--count \"src/term.c\" \"scm_c_public_ref\"))")
                      (m58-imp3--contains-p
                       "test/m58/test-m58-imp1.el"
                       "(eql 267 (m58-imp1--count-scm-ref))")
                      (m58-imp3--contains-p
                       "test/m58/test-m58-imp1.el"
                       "(eql 682 (m58-imp1--lines \"mod/emacs/tty-output.scm\"))")))

(m58-imp3--check "repin/imp1-cases-and-group-a"
                 (and (m58-imp3--contains-p
                       "test/m58/test-m58-imp1.el" "\"pty-driver-cases-32\"")
                      (m58-imp3--contains-p
                       "test/m58/test-m58-imp1.el" "(eql 32 (car pins))")
                      ;; The Group A row re-pin: TTY_CAPABLE_P_TRY is
                      ;; gone, so the row pins the 3 dispatcher keys.
                      (m58-imp3--contains-p
                       "test/m58/test-m58-imp1.el" "tty-face-on-steps")))

(m58-imp3--check "repin/imp2-signatures-and-total"
                 (and (string= "turn_on_face (struct frame *f, struct face *face)"
                               (or (m58-imp3--line-text "src/term.c" 2380) ""))
                      (string= "tty_capable_p (struct tty_display_info *tty, unsigned int caps)"
                               (or (m58-imp3--line-text "src/term.c" 2503) ""))
                      (m58-imp3--contains-p
                       "test/m58/test-m58-imp2.el"
                       "(m58-imp2--line-text \"src/term.c\" 2379)")
                      (m58-imp3--contains-p
                       "test/m58/test-m58-imp2.el" "\"pty-case-counts-32\"")
                      (m58-imp3--contains-p
                       "test/m58/test-m58-imp2.el" "(eql 32 (car pins))")
                      (m58-imp3--contains-p "tool/run-tests.scm"
                                            "test/m58/test-m58-imp3.el")))

;; F3 of cr.org: the first attempt re-pinned 15 files and missed 25, so
;; the count surface was split across two values.  A sampled check cannot
;; see that, so this check scans EVERY test/*/*.el file.  The needles are
;; built with `concat' so that this check does not match its own source.
(defun m58-imp3--stale-pinners (needles)
  "Return the base names of the test/*/*.el files that hold a NEEDLE."
  (let ((dirs (directory-files (expand-file-name "test" m58-imp3--root) t
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

(m58-imp3--check "repin/no-stale-surface"
                 (null (m58-imp3--stale-pinners
                        (list (concat "(eql " "6350 ")
                              (concat "(eql " "260 ")
                              (concat "(eql " "635 (")))))

;; The review of the MOVE (cr.org section 6.2) found that the (m58-imp3)
;; group comment of tool/run-tests.scm still held the PRE-measurement
;; numbers.  A number in a comment that no test reads is a trap for the
;; next reader, so the measurable set is pinned here.  Change one number
;; in the comment and this check goes red.
(m58-imp3--check "repin/group-comment-measured"
                 (m58-imp3--holds-all
                  "tool/run-tests.scm"
                  (list "C delta +267 / -118"
                        "Scheme delta +184 / -1"
                        "src/term.c 6,363 lines"
                        "mod/emacs/tty-output.scm 637 lines"
                        "the hub signature lines 2372 / 2495")))

;; The same review (cr.org section 6.4) found pointers to brief.org
;; sections that hold no such rule.  Each pointer now names the section
;; that really holds the rule, so a reader who follows it finds the text:
;; the OUTPUT / OUTPUT1 rule is section 5.1 rule 1, the bare-string rule
;; is section 5.1 rule 2, and the off-hub underline rule is S2 point 4.
(m58-imp3--check "docs/pointer-targets-exist"
                 (and (m58-imp3--contains-p
                       "src/term.c"
                       "silent byte change (brief.org section 5.1 rule 1)")
                      (m58-imp3--contains-p
                       "src/term.c"
                       "section 5.1 rule 2).  Every step carries an explicit tag.")
                      (m58-imp3--contains-p
                       "mod/emacs/tty-output.scm"
                       "OUTPUT1 uses 1 line (brief.org section")
                      (m58-imp3--contains-p
                       "mod/emacs/tty-output.scm"
                       "5.1 rule 1).  The KEY therefore carries its macro")
                      (m58-imp3--contains-p
                       "mod/emacs/tty-output.scm"
                       "change on a terminal without \"me\" (brief.org S2 point 4).")
                      (m58-imp3--absent-p
                       "src/term.c" "brief.org section 9.1")
                      (m58-imp3--absent-p
                       "src/term.c" "brief.org section 10.4")
                      (m58-imp3--absent-p
                       "mod/emacs/tty-output.scm" "brief.org section 10.4")))

;;; --- U6. The guards -------------------------------------------------

;; An --filter that matches no group reports exit 0 with 0 tests, so a
;; green m58 gate proves nothing until the corpus really registers.
;; U1 holds 4 checks, U2 holds 5, U3 holds 6, U4 holds 4, U5 holds 6.

(setq m58-imp3--group 'u6)

(m58-imp3--check "reg/min-u1-checks-4" (>= (m58-imp3--group-count 'u1) 4))
(m58-imp3--check "reg/min-u2-checks-4" (>= (m58-imp3--group-count 'u2) 4))
(m58-imp3--check "reg/min-u3-checks-6" (>= (m58-imp3--group-count 'u3) 6))
(m58-imp3--check "reg/min-u4-checks-4" (>= (m58-imp3--group-count 'u4) 4))
(m58-imp3--check "reg/min-u5-checks-4" (>= (m58-imp3--group-count 'u5) 4))

;;; --- The group-total check ------------------------------------------

;; The measured count of m58-imp3 tests is 30: 29 registered checks
;; (U1 4, U2 5, U3 6, U4 4, U5 6, U6 5) plus the group-total deftest
;; itself.  The U2 checks may fold to a controlled INFO skip on a host
;; with no guile, and a controlled skip is still a registered test.

(defvar m58-imp3--min-gate-total 30
  "The exact number of m58-imp3 ERT tests: 29 registered checks (U1 4,
U2 5, U3 6, U4 4, U5 6, U6 5) plus the group-total deftest itself.")

(ert-deftest m58-imp3/gate-m58-total ()
  "The m58-imp3 corpus registers at least its docs-independent floor."
  (should (>= (length (ert-select-tests "^m58-imp3" t))
              m58-imp3--min-gate-total)))

(princ (format "=== m58 imp-3 suite done (%d checks; u1 %d, u2 %d, u3 %d, u4 %d, u5 %d, u6 %d) ===\n"
               m58-imp3--registered
               (m58-imp3--group-count 'u1)
               (m58-imp3--group-count 'u2)
               (m58-imp3--group-count 'u3)
               (m58-imp3--group-count 'u4)
               (m58-imp3--group-count 'u5)
               (m58-imp3--group-count 'u6)))
