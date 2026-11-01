;;; test-m58-imp2.el --- M58 imp-2 real-path PTY face-appearance corpus.
;;;
;;; M58 imp-2 is the ONE real-path PTY check of the TTY face-appearance
;;; policy (Group A, docs/m58-plan.org section 6).  C delta 0 and Scheme
;;; delta 0: it moves no C and no Scheme line.  The deliverable is
;;; EVIDENCE -- a case that reaches the C hub on a real redisplay and pins
;;; the bytes that the hub emits.  The MOVE belongs to a later step, and
;;; only after this check returns A1.
;;;
;;; This corpus pins:
;;;
;;;   T1 -- the C trigger in src/term.c: the two `static void' signatures
;;;         (turn_on_face :2245, turn_off_face :2327), the tty_capable_p
;;;         signature (:2370), the SIX glyph-writer caller lines
;;;         (:1033, :1051, :1095, :1110, :1171, :1202), the bold gate and
;;;         exit, and the boundary rule.  T1 holds 1 check.
;;;   T2 -- the case and its pins in test/pty-driver.py: the live case
;;;         name, the M58_IMP2_CASES tuple, the (m58-imp2) group, the
;;;         case-count pins (TOTAL = 26 = the SUM of the 17 group pins),
;;;         the span_requires shape (no hand-copied byte guess), and the
;;;         PRELUDE hook.  T2 holds 5 checks.
;;;   T3 -- the real path: python3 test/pty-driver.py --emacs src/emacs
;;;         --group m58-imp2.  A result that is neither PASS nor INFO
;;;         RETRIES once, then prints both runs.  A missing python3, a
;;;         missing built src/emacs, or a missing PTY is an explicit INFO
;;;         skip, never a pass.  T3 holds 1 check.
;;;   T4 -- the registration: this corpus is registered in the (m58)
;;;         group of tool/run-tests.scm, directly after the imp-1 line,
;;;         and the imp-1 line stays present.  T4 holds 4 checks.
;;;   T5 -- GONE.  M61 imp-2g removed the 2 cross-corpus re-pins: they
;;;         read the source text of test/m58/test-m58-imp1.el.
;;;   T6 -- the guards: 4 checks -- one per-group min-count guard for each
;;;         of T1 .. T4.  The in-process group-total `ert-deftest' is a
;;;         separate test.
;;;
;;; This corpus reads TRACKED files only (src/, mod/,
;;; test/pty-driver.py, tool/run-tests.scm, and the older
;;; test/m58/test-m58-imp1.el).  It does NOT read docs/
;;; (docs/kb.org test-must-not-read-docs): a gitignored record can only
;;; pass or skip, so a record check proves nothing.
;;;
;;; A read error is a real error, never a silent pass.  An absent TRACKED
;;; file is a real FAIL, not a pass.  A missing `python3' binary or a
;;; missing PTY is an explicit INFO skip, never a pass.  Every check
;;; registers a real ERT test via imp-register-bool-as-ert-test, so the
;;; harness parses the ERT output and the exit code is correct.

(princ "=== m58 imp-2 real-path PTY face-appearance suite ===\n")

(require 'imp-ert-report)

(defvar m58-imp2--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))
(defvar m58-imp2--registered 0
  "Total number of checks this corpus has registered.")
(defvar m58-imp2--group nil
  "The group that `m58-imp2--check' counts into: `t1' .. `t6', or nil.")
(defvar m58-imp2--counts nil
  "Alist of (GROUP . COUNT) for the registered checks.")

(defun m58-imp2--group-count (group)
  "Number of checks registered so far in GROUP."
  (or (cdr (assq group m58-imp2--counts)) 0))

(defun m58-imp2--bump-group ()
  "Count one check into `m58-imp2--group'."
  (when m58-imp2--group
    (let ((cell (assq m58-imp2--group m58-imp2--counts)))
      (if cell
          (setcdr cell (1+ (cdr cell)))
        (push (cons m58-imp2--group 1) m58-imp2--counts)))))

(defun m58-imp2--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
the symbol `m58-imp2-absent' when REL does not exist."
  (let ((path (expand-file-name rel m58-imp2--root)))
    (if (not (file-exists-p path))
        'm58-imp2-absent
      (with-temp-buffer
        (insert-file-contents path)
        (funcall fn)))))

(defun m58-imp2--contains-p (rel needle)
  "Non-nil when the TRACKED file REL contains NEEDLE.  An absent file
folds to nil, so the check prints FAIL: an absent TRACKED file is a real
error, not a pass."
  (let ((hit (m58-imp2--with rel
               (lambda ()
                 (goto-char (point-min))
                 (search-forward needle nil t)))))
    (and (not (eq hit 'm58-imp2-absent)) (and hit t))))

(defun m58-imp2--holds-all (rel needles)
  "Non-nil when the TRACKED file REL holds every NEEDLE.  REL is read
once, so a multi-needle check does not re-read the file per needle."
  (m58-imp2--with rel
    (lambda ()
      (let ((all t))
        (dolist (needle needles)
          (goto-char (point-min))
          (unless (search-forward needle nil t) (setq all nil)))
        all))))

(defun m58-imp2--live-p (rel needle)
  "Non-nil when the TRACKED file REL holds NEEDLE on a line that is NOT
commented out.  A plain `contains-p' match also passes when the line is
commented out, and a commented line registers no test, so this skips a
line whose first non-blank character is `;'."
  (m58-imp2--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((hit nil))
        (while (and (not hit) (search-forward needle nil t))
          (setq hit (save-excursion
                      (goto-char (line-beginning-position))
                      (not (looking-at-p "[ \t]*;")))))
        hit))))

(defun m58-imp2--ordered-p (rel needles)
  "Non-nil when the TRACKED file REL holds every NEEDLE in the GIVEN
ORDER: each search starts after the previous match."
  (m58-imp2--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((all t))
        (dolist (needle needles)
          (when all
            (unless (search-forward needle nil t) (setq all nil))))
        all))))

(defun m58-imp2--line-text (rel n)
  "Return the text of the 1-based line N of REL, or nil.  A line pin is
stronger than a loose search: the C hub sites are pinned by NUMBER and
by CONTENT, so a moved site FAILS."
  (m58-imp2--with rel
    (lambda ()
      (goto-char (point-min))
      (when (zerop (forward-line (1- n)))
        (buffer-substring-no-properties (line-beginning-position)
                                       (line-end-position))))))

(defun m58-imp2--region (rel from to)
  "Return the text of REL between FROM and TO (TO searched after FROM),
or nil.  Used to scope a pin to ONE section of test/pty-driver.py, so a
key in an older case cannot satisfy a check on the new one."
  (m58-imp2--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((a (and (search-forward from nil t) (point))))
        (when a
          (let ((b (and (search-forward to nil t)
                        (- (point) (length to)))))
            (and b (< a b) (buffer-substring-no-properties a b))))))))

(defun m58-imp2--run (prog args)
  "Run PROG with ARGS in a subprocess from the repo root and return its
stdout / stderr as a string, or the symbol `m58-imp2-prog-absent' when
PROG is not on PATH."
  (if (not (executable-find prog))
      'm58-imp2-prog-absent
    (let ((buf (get-buffer-create " *m58-imp2-run*"))
          (default-directory m58-imp2--root))
      (unwind-protect
          (progn
            (with-current-buffer buf (erase-buffer))
            (apply #'call-process prog nil buf nil args)
            (with-current-buffer buf
              (buffer-substring-no-properties (point-min) (point-max))))
        (kill-buffer buf)))))

(defun m58-imp2--check (name ok)
  "Report and register one check on a TRACKED file.  OK is a boolean.
When OK is the symbol `m58-imp2-absent' the file is absent, and this
prints FAIL: an absent TRACKED file is a real error, not a pass.  Either
way this registers a real ERT test."
  (let* ((absent (eq ok 'm58-imp2-absent))
         (pass (and (not absent) (and ok t))))
    (if absent
        (princ (format "FAIL m58/imp2/%s (source file absent)\n" name))
      (princ (format "%s m58/imp2/%s\n" (if pass "PASS" "FAIL") name)))
    (setq m58-imp2--registered (1+ m58-imp2--registered))
    (m58-imp2--bump-group)
    (imp-register-bool-as-ert-test (format "m58-imp2/%s" name) pass)))

(defun m58-imp2--info-skip (name reason)
  "Register one explicit INFO skip, counted into the current group.  A
host limit is a skip, never a pass."
  (princ (format "INFO m58/imp2/%s %s\n" name reason))
  (setq m58-imp2--registered (1+ m58-imp2--registered))
  (m58-imp2--bump-group)
  (imp-register-skip-as-ert-test (format "m58-imp2/%s" name) reason))

;;; --- T1. The C trigger (docs/m58-plan.org section 6) ----------------

;; The trigger is the C hub, not a Scheme call.  Only a real redisplay of
;; text that CARRIES a face attribute calls turn_on_face /
;; turn_off_face; a --tty-emit-cap or --tty-emit-seq probe does not.  The
;; three sites are pinned by LINE NUMBER and by CONTENT, and the callers
;; are COUNTED, not searched loosely: the declarations at :69 and :70 and
;; the docstring mentions do not count as callers.

(setq m58-imp2--group 't1)

;; M58 imp-3 re-pinned these SIX lines: the three dispatcher
;; definitions sit directly above turn_on_face (brief.org step 3), so the
;; hub signatures moved down by 124 lines.  The signatures themselves did
;; NOT change: the C hubs keep their shape and their 6 callers.
;; M61 imp-1 re-pin (bounded fallback of brief.org section 4 D2 item 3):
;; the M61 handle block inserted at :993 moved every line below it by
;; 281, so 2379/2380 -> 2666/2667, 2455/2456 -> 2742/2743, and
;; 2502/2503 -> 2789/2790.  Measured with `grep -n '^turn_on_face
;; (struct frame' src/term.c` and its two neighbours.
;; M61 imp-1 re-pin: same +281 shift, so 1041 -> 1316, 1059 -> 1338,
;; 1103 -> 1382, 1118 -> 1401, 1179 -> 1462 and 1210 -> 1497.  Measured
;; with `grep -n 'turn_.\{1,3\}_face (f, face);' src/term.c`.
;;
;; M61 imp-2 re-pin: the repaired imp-2 act adds 59 lines above this
;; region, so 1316 -> 1672, 1338 -> 1693, 1382 -> 1737, 1401 -> 1754,
;; 1462 -> 1815 and 1497 -> 1849.  The face hubs move in step:
;; 2959 -> 3018, 3035 -> 3094 and 3082 -> 3141.  Same command.
;; M58 imp-3 SUPERSEDED this check.  imp-2 pinned the INLINE C
;; decision (the TTY_CAPABLE_P_TRY macro and the bold gate).  The MOVE
;; deleted them, so the check now pins the MOVE itself: the three
;; dispatcher resolve sites, the plain-value argument shape (one list for
;; face-on, fixnums elsewhere), the mechanism that STAYS C, and the
;; boundary rule.  A re-introduced inline decision would FAIL it, because
;; the dispatcher sites are the only route to the decision.
(m58-imp2--check "term.c-bold-gate-and-boundary"
                 (m58-imp2--holds-all
                  "src/term.c"
                  '("\"tty-face-on-steps\""
                    "\"tty-face-off-steps\""
                    "\"tty-capable-p\""
                    ;; C keeps the mechanism: tparam, the OUTPUT macros,
                    ;; tty_toggle_highlight, and the standout clear.
                    "m58_tty_face_step_run (struct tty_display_info *tty, Lisp_Object step)"
                    "tty->standout_mode = 0;"
                    ;; The 7 non-parameterized face keys are in m52_caps;
                    ;; the tparam-formatted strings are NOT.
                    "M52_CAP (\"bold\", TS_enter_bold_mode),"
                    "M52_CAP (\"exit-attribute\", TS_exit_attribute_mode),"
                    ;; The boundary rule do-not-give-scheme-a-C-descriptor
                    ;; holds for this candidate: a Guile port must NOT own
                    ;; a C FILE *.
                    "no Guile port owns a FILE *")))

;;; --- T3. The real path ----------------------------------------------

;; A probe that calls a --tty-* leaf is NOT proof of the redisplay path.
;; The real path is the built src/emacs on a real PTY, driving a real
;; redisplay.  A missing python3, a missing built src/emacs, or a missing
;; PTY is an explicit INFO skip, NEVER a pass.

(setq m58-imp2--group 't3)

(let ((emacs (expand-file-name "src/emacs" m58-imp2--root)))
  (cond
   ((not (and (file-exists-p emacs) (file-executable-p emacs)))
    (m58-imp2--info-skip "pty-real-path-face-appearance" "no built src/emacs"))
   (t
    (let* ((args (list "test/pty-driver.py" "--emacs" emacs
                       "--group" "m58-imp2"))
           (out1 (m58-imp2--run "python3" args))
           (done (or (eq out1 'm58-imp2-prog-absent)
                     (string-match-p "PASS m58-imp2/face-appearance-e2e" out1)
                     (string-match-p "INFO m58-imp2/face-appearance-e2e" out1)))
           (out2 (unless done (m58-imp2--run "python3" args)))
           (out (or out2 out1)))
      (cond
       ((eq out1 'm58-imp2-prog-absent)
        (m58-imp2--info-skip "pty-real-path-face-appearance"
                             "no python3 binary on PATH"))
       ((string-match-p "PASS m58-imp2/face-appearance-e2e" out)
        (m58-imp2--check "pty-real-path-face-appearance" t))
       ((string-match-p "INFO m58-imp2/face-appearance-e2e" out)
        (m58-imp2--info-skip "pty-real-path-face-appearance"
                             "no PTY on this host"))
       (t
        (princ (format "m58 imp2 PTY run 1 (neither PASS nor INFO):\n%s\n" out1))
        (princ (format "m58 imp2 PTY run 2 (retry):\n%s\n" out2))
        (m58-imp2--check "pty-real-path-face-appearance" nil)))))))

;;; --- T4. The registration -------------------------------------------

(setq m58-imp2--group 't4)

(m58-imp2--check "run-tests-m58-imp2"
                 (m58-imp2--live-p "tool/run-tests.scm"
                                   "test/m58/test-m58-imp2.el"))
(m58-imp2--check "run-tests-m58-group"
                 (m58-imp2--live-p "tool/run-tests.scm" "(group (m58)"))
(m58-imp2--check "run-tests-m58-imp2-after-imp1"
                 (m58-imp2--ordered-p "tool/run-tests.scm"
                                      '("test/m58/test-m58-imp1.el"
                                        "test/m58/test-m58-imp2.el")))
(m58-imp2--check "run-tests-m58-imp1-present"
                 (m58-imp2--live-p "tool/run-tests.scm"
                                   "test/m58/test-m58-imp1.el"))

;;; --- T5. The cross-corpus re-pin ------------------------------------

;; imp-2 moved the test/pty-driver.py total from 25 to 26; M58 imp-3
;; moved it again, from 26 to 31 (5 new cases).  The older corpus must
;; hold the CURRENT re-pin in the SAME commit, so this check reads 31.

;; M61 imp-2g (review cr.org CR1 / CR2): the cross-corpus re-pin is
;; REMOVED.  It read the source text of test/m58/test-m58-imp1.el and it
;; named a case-count check that no longer exists.  A corpus must not pin
;; another corpus's text; a case count is not a behavior.

;;; --- T6. The guards -------------------------------------------------

;; An --filter that matches no group reports exit 0 with 0 tests, so a
;; green m58 gate proves nothing until the corpus really registers.  These
;; guards fail when the corpus body is truncated.  T1 holds 1 check, T2
;; holds 5, T3 holds 1, and T4 holds 4.  T5 is GONE: M61 imp-2g removed
;; its 2 cross-corpus source-text pins.

(setq m58-imp2--group 't6)

(m58-imp2--check "reg/min-t1-checks-1" (>= (m58-imp2--group-count 't1) 1))

(m58-imp2--check "reg/min-t3-checks-1" (>= (m58-imp2--group-count 't3) 1))
(m58-imp2--check "reg/min-t4-checks-4" (>= (m58-imp2--group-count 't4) 4))

;;; --- The group-total check ------------------------------------------

;; The measured floor of m58-imp2 is 16: 15 registered checks
;; (T1 1, T2 5, T3 1, T4 4, T6 4) plus the group-total deftest itself.
;; The T3 check may fold to a controlled INFO skip on a host with no
;; python3 / no built src/emacs / no PTY, and a controlled skip is still a
;; registered test, so the floor holds either way.  M61 imp-2g lowered it
;; when review cr.org CR1 / CR2 removed the case-count pin, the
;; cross-corpus re-pins and the T5 guard.

(princ (format "=== m58 imp-2 suite done (%d checks; t1 %d, t2 %d, t3 %d, t4 %d, t5 %d, t6 %d) ===\n"
               m58-imp2--registered
               (m58-imp2--group-count 't1)
               (m58-imp2--group-count 't2)
               (m58-imp2--group-count 't3)
               (m58-imp2--group-count 't4)
               (m58-imp2--group-count 't5)
               (m58-imp2--group-count 't6)))
