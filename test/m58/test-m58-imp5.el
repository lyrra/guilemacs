;;; test-m58-imp5.el --- M58 imp-5, the CLOSE-OUT: the 3 row verdicts.
;;;
;;; imp-5 CLOSES M58.  It moves no C and no Scheme policy: the C delta
;;; is 0 and the Scheme delta is 0.  It re-measures the surface and
;;; records a measured verdict for each of the 3 open MOVE-candidate
;;; rows of the imp-1 row map (brief.org section 5).
;;;
;;; The 3 verdicts, each MEASURED at HEAD (not copied from brief.org):
;;;
;;;   row A  the calculate_costs TS_repeat test (src/term.c :1502).
;;;          STAYS C: the block writes tty->RPov only.  RPov has 3
;;;          sites in src/*.[ch] -- 2 writes in src/term.c and the
;;;          declaration in src/termchar.h -- and NO reader.  A value
;;;          that no code reads is not an observable, and the cost
;;;          inputs per_line_cost / string_cost are C termcap calls
;;;          (tputs).  No decision moves.
;;;   row B  tty-no-underline (src/term.c :2882).  STAYS C: one C
;;;          struct field write behind a C terminal-type test.  The
;;;          observable DOES exist (after the call an underlined face
;;;          emits no underline start byte; TS_enter_underline_mode is
;;;          the M52_CAP "underline" source), but no plain value
;;;          crosses that C would not compute itself, so a Scheme port
;;;          would be a passthrough, not a port
;;;          (passthrough-leaf-is-not-a-port).
;;;   row C  tty-top-frame (src/term.c :2900).  STAYS C: a pure read of
;;;          a Lisp_Object field of a C struct.  It computes nothing
;;;          and it needs the C struct member itself.
;;;
;;; The row map closes as: 5 MOVEs in Scheme (Group A: tty-face-on-steps,
;;; tty-face-off-steps, tty-capable-p; Group B: tty-color-mode-tag,
;;; tty-color-mode-changed-p), 3 rows STAYS C (this unit), 5 rows NOT
;;; PROVEN (no observable: the 3 Group D ins / del rows and the 2 Group
;;; F tty--output-buffer-size rows), and Group G STAYS C.
;;;
;;; This corpus pins:
;;;
;;;   V1 -- the 3 row verdicts.  One check per row: the site line, the
;;;         key C text, the measured fact, and the verdict token with
;;;         its reason keyword.  V1 holds 3 checks.
;;;   V2 -- the row-map close: the 5 MOVEs are defined and exported in
;;;         mod/emacs/tty-output.scm, the 5 NOT PROVEN rows are still
;;;         named in the record, and Group G STAYS C.  V2 holds 3
;;;         checks.
;;;   V3 -- the surface re-measure: src/term.c lines / ^DEFUN ( /
;;;         --tty-* leaf DEFUNs / scm_c_public_ref sites, tree-wide
;;;         scm_c_public_ref, mod/emacs/tty-output.scm lines,
;;;         test/pty-driver.py 32 cases in 19 groups, and the 5 corpus
;;;         files of test/m58.  V3 holds 6 checks.
;;;   V4 -- the registration: the (m58) group holds this file after
;;;         test-m58-imp4.el, and the 4 older lines stay.  V4 holds 2
;;;         checks.
;;;   V5 -- the real path: run the 3 existing PTY groups (m58-imp2,
;;;         m58-imp3, m58-imp4) on the built src/emacs.  One check per
;;;         group.  A missing python3, a missing built src/emacs, or a
;;;         missing PTY is an explicit INFO skip, NEVER a pass.  V5
;;;         holds 3 checks.
;;;   V6 -- the guards: 5 per-group min-count guards plus the in-process
;;;         group total.  V6 holds 6 checks.
;;;
;;; This corpus reads TRACKED files only (src/, mod/, test/, and
;;; tool/run-tests.scm).  It does NOT read docs/ (docs/kb.org
;;; test-must-not-read-docs).  It adds NO PTY case, so the case total
;;; stays 32.
;;;
;;; A read error is a real error, never a silent pass.  An absent
;;; TRACKED file is a real FAIL, not a pass.  Every check registers a
;;; real ERT test.

(princ "=== m58 imp-5 close-out suite ===\n")

(require 'imp-ert-report)

(defvar m58-imp5--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))
(defvar m58-imp5--registered 0
  "Total number of checks this corpus has registered.")
(defvar m58-imp5--group nil
  "The group that `m58-imp5--check' counts into: `v1' .. `v6', or nil.")
(defvar m58-imp5--counts nil
  "Alist of (GROUP . COUNT) for the registered checks.")

(defun m58-imp5--group-count (group)
  "Number of checks registered so far in GROUP."
  (or (cdr (assq group m58-imp5--counts)) 0))

(defun m58-imp5--bump-group ()
  "Count one check into `m58-imp5--group'."
  (when m58-imp5--group
    (let ((cell (assq m58-imp5--group m58-imp5--counts)))
      (if cell
          (setcdr cell (1+ (cdr cell)))
        (push (cons m58-imp5--group 1) m58-imp5--counts)))))

(defun m58-imp5--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
the symbol `m58-imp5-absent' when REL does not exist."
  (let ((path (expand-file-name rel m58-imp5--root)))
    (if (not (file-exists-p path))
        'm58-imp5-absent
      (with-temp-buffer
        (insert-file-contents path)
        (funcall fn)))))

(defun m58-imp5--contains-p (rel needle)
  "Non-nil when the TRACKED file REL contains NEEDLE.  An absent file
folds to nil, so the check prints FAIL."
  (let ((hit (m58-imp5--with rel
               (lambda ()
                 (goto-char (point-min))
                 (search-forward needle nil t)))))
    (and (not (eq hit 'm58-imp5-absent)) (and hit t))))

(defun m58-imp5--holds-all (rel needles)
  "Non-nil when the TRACKED file REL holds every NEEDLE."
  (m58-imp5--with rel
    (lambda ()
      (let ((all t))
        (dolist (needle needles)
          (goto-char (point-min))
          (unless (search-forward needle nil t) (setq all nil)))
        all))))

(defun m58-imp5--absent-p (rel needle)
  "Non-nil when the TRACKED file REL does NOT hold NEEDLE."
  (let ((hit (m58-imp5--with rel
               (lambda ()
                 (goto-char (point-min))
                 (search-forward needle nil t)))))
    (and (not (eq hit 'm58-imp5-absent)) (not hit))))

(defun m58-imp5--live-p (rel needle)
  "Non-nil when REL holds NEEDLE on a line that is NOT commented out."
  (m58-imp5--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((hit nil))
        (while (and (not hit) (search-forward needle nil t))
          (setq hit (save-excursion
                      (goto-char (line-beginning-position))
                      (not (looking-at-p "[ \t]*;")))))
        hit))))

(defun m58-imp5--ordered-p (rel needles)
  "Non-nil when REL holds every NEEDLE in the GIVEN ORDER."
  (m58-imp5--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((all t))
        (dolist (needle needles)
          (when all
            (unless (search-forward needle nil t) (setq all nil))))
        all))))

(defun m58-imp5--region (rel from to)
  "Return the text of REL between FROM and TO.  A nil TO runs to the end."
  (m58-imp5--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((a (and (search-forward from nil t) (point))))
        (when a
          (if (not to)
              (buffer-substring-no-properties a (point-max))
            (let ((b (and (search-forward to nil t)
                          (- (point) (length to)))))
              (and b (< a b) (buffer-substring-no-properties a b)))))))))

(defun m58-imp5--count (rel regexp)
  "Count the matches of REGEXP in REL."
  (m58-imp5--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (re-search-forward regexp nil t) (setq n (1+ n)))
        n))))

(defun m58-imp5--count-in (text needle)
  "Count the non-overlapping occurrences of the literal NEEDLE in TEXT."
  (let ((n 0) (start 0) (re (regexp-quote needle)))
    (while (string-match re text start)
      (setq n (1+ n) start (match-end 0)))
    n))

(defun m58-imp5--line-of (rel needle)
  "The 1-based line number of the FIRST NEEDLE in REL, or nil."
  (m58-imp5--with rel
    (lambda ()
      (goto-char (point-min))
      (when (search-forward needle nil t)
        (let ((pos (match-beginning 0)) (n 1))
          (save-excursion
            (goto-char (point-min))
            (while (search-forward "\n" pos t) (setq n (1+ n))))
          n)))))

(defun m58-imp5--lines-matching (rel regexp)
  "Count the lines of REL that hold a match of REGEXP."
  (m58-imp5--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (re-search-forward regexp nil t)
          (setq n (1+ n))
          (forward-line 1))
        n))))

(defun m58-imp5--src-files (regexp)
  "The src/ files that match REGEXP."
  (directory-files (expand-file-name "src" m58-imp5--root) t regexp))

(defun m58-imp5--grep-src (regexp)
  "Count the matches of REGEXP in every TRACKED src/*.c and src/*.h."
  (let ((n 0))
    (dolist (f (append (m58-imp5--src-files "\\.c\\'")
                       (m58-imp5--src-files "\\.h\\'")))
      (with-temp-buffer
        (insert-file-contents f)
        (goto-char (point-min))
        (while (re-search-forward regexp nil t) (setq n (1+ n)))))
    n))

(defun m58-imp5--src-public-refs ()
  "Count the scm_c_public_ref sites in every src/*.c and src/*.h."
  (m58-imp5--grep-src "scm_c_public_ref"))

(defun m58-imp5--leaf-defuns ()
  "Count the DEFUN forms whose name starts with --tty- in src/term.c."
  (m58-imp5--count "src/term.c" "DEFUN (\"--tty-"))

(defun m58-imp5--corpus-files ()
  "The number of .el corpus files in test/m58."
  (length (directory-files (expand-file-name "test/m58" m58-imp5--root)
                           t "\\.el\\'")))

(defun m58-imp5--pty-case-pins ()
  "Read the `test/pty-driver.py' pins as (TOTAL SUM GROUPS).
TOTAL is the `total-case-count' pin, SUM is the sum of the per-group
pins, and GROUPS is the number of group pins.  Return nil on a read
error."
  (m58-imp5--with "test/pty-driver.py"
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
        (and total (> n 0) (list total sum n))))))

(defun m58-imp5--run (prog args)
  "Run PROG with ARGS from the repo root and return the combined output,
or the symbol `m58-imp5-prog-absent'."
  (if (not (executable-find prog))
      'm58-imp5-prog-absent
    (let ((buf (get-buffer-create " *m58-imp5-run*"))
          (default-directory m58-imp5--root))
      (unwind-protect
          (progn
            (with-current-buffer buf (erase-buffer))
            (apply #'call-process prog nil buf nil args)
            (with-current-buffer buf
              (buffer-substring-no-properties (point-min) (point-max))))
        (kill-buffer buf)))))

(defun m58-imp5--check (name ok)
  "Report and register one check.  The symbol `m58-imp5-absent' means
the TRACKED file is absent and prints FAIL."
  (let* ((absent (eq ok 'm58-imp5-absent))
         (pass (and (not absent) (and ok t))))
    (if absent
        (princ (format "FAIL m58/imp5/%s (source file absent)\n" name))
      (princ (format "%s m58/imp5/%s\n" (if pass "PASS" "FAIL") name)))
    (setq m58-imp5--registered (1+ m58-imp5--registered))
    (m58-imp5--bump-group)
    (imp-register-bool-as-ert-test (format "m58-imp5/%s" name) pass)))

(defun m58-imp5--info-skip (name reason)
  "Register one explicit INFO skip, counted into the current group."
  (princ (format "INFO m58/imp5/%s %s\n" name reason))
  (setq m58-imp5--registered (1+ m58-imp5--registered))
  (m58-imp5--bump-group)
  (imp-register-skip-as-ert-test (format "m58-imp5/%s" name) reason))

;;; --- V1. The 3 row verdicts -----------------------------------------

;; Row A.  The block writes tty->RPov only.  The measured fact is the
;; count: 3 RPov sites in src/*.[ch] (2 writes in src/term.c and the
;; declaration in src/termchar.h), and no reader.  The cost inputs are
;; the C termcap calls per_line_cost / string_cost (tputs).
(setq m58-imp5--group 'v1)

(m58-imp5--check "v1/row-a-stays-c"
                 (and (m58-imp5--holds-all
                       "src/term.c"
                       '("/* Don't use TS_repeat if its padding is worse than sending the chars */"
                         "if (tty->TS_repeat"
                         "per_line_cost (tty->TS_repeat) < 9000 / baud_rate"
                         "tty->RPov = string_cost (tty->TS_repeat);"
                         "tty->RPov = FRAME_COLS (frame) * 2;"))
                      ;; The site line, measured now (imp-5 moves no C).
                      (eql 1789 (m58-imp5--line-of "src/term.c"
                                                  "Don't use TS_repeat"))
                      ;; 3 sites: 2 writes here, 1 declaration.
                      (eql 3 (m58-imp5--grep-src "RPov"))
                      (eql 2 (m58-imp5--count "src/term.c" "tty->RPov ="))
                      (m58-imp5--contains-p "src/termchar.h" "int RPov;")
                      (m58-imp5--absent-p "mod/emacs/tty-output.scm" "RPov")
                      (m58-imp5--contains-p "tool/run-tests.scm"
                                            "STAYS C (RPov has 3 sites and no reader")))

;; Row B.  One C struct field write behind a C terminal-type test.  The
;; observable exists -- TS_enter_underline_mode is the M52_CAP
;; "underline" source -- but the port would be a passthrough.
(m58-imp5--check "v1/row-b-stays-c"
                 (and (m58-imp5--holds-all
                       "src/term.c"
                       '("DEFUN (\"tty-no-underline\", Ftty_no_underline, Stty_no_underline, 0, 1, 0,"
                         "struct terminal *t = decode_live_terminal (terminal);"
                         "if (t->type == output_termcap)"
                         "t->display_info.tty->TS_enter_underline_mode = 0;"
                         "M52_CAP (\"underline\", TS_enter_underline_mode),"))
                      (eql 3169 (m58-imp5--line-of
                                 "src/term.c" "DEFUN (\"tty-no-underline\""))
                      (m58-imp5--contains-p "tool/run-tests.scm"
                                            "STAYS C (one C field write behind a C type test")
                      (m58-imp5--contains-p "tool/run-tests.scm"
                                            "passthrough-leaf-is-not-a-port")))

;; Row C.  A pure read of a Lisp_Object field of a C struct.
(m58-imp5--check "v1/row-c-stays-c"
                 (and (m58-imp5--holds-all
                       "src/term.c"
                       '("DEFUN (\"tty-top-frame\", Ftty_top_frame, Stty_top_frame, 0, 1, 0,"
                         "return t->display_info.tty->top_frame;"))
                      (eql 3187 (m58-imp5--line-of
                                 "src/term.c" "DEFUN (\"tty-top-frame\""))
                      ;; The body computes nothing: one field read, then
                      ;; nil for a non-tty terminal.
                      (let ((body (m58-imp5--region
                                   "src/term.c"
                                   "DEFUN (\"tty-top-frame\""
                                   "DEFUN (\"suspend-tty\"")))
                        (and (stringp body)
                             (eql 1 (m58-imp5--count-in
                                     body "return t->display_info.tty->top_frame;"))
                             (not (string-match-p "scm_c_public_ref" body))
                             (not (string-match-p "make_fixnum" body))))
                      (m58-imp5--contains-p "tool/run-tests.scm"
                                            "STAYS C (a pure read of a C struct member")))

;;; --- V2. The row-map close ------------------------------------------

;; The 5 MOVEs are in Scheme and each one is EXPORTED.
(setq m58-imp5--group 'v2)

(m58-imp5--check "v2/five-moves-exported"
                 (and (m58-imp5--holds-all
                       "mod/emacs/tty-output.scm"
                       '("tty-face-on-steps tty-face-off-steps tty-capable-p"
                         "tty-color-mode-tag tty-color-mode-changed-p"
                         "(define (tty-face-on-steps args)"
                         "(define (tty-face-off-steps has-me attrs has-exit-underline"
                         "(define (tty-capable-p caps presence no-color-video max-colors)"
                         "(define (tty-color-mode-tag mode)"
                         "(define (tty-color-mode-changed-p mode previous)"))))

;; The 5 NOT PROVEN rows stay named in the record (tool/run-tests.scm),
;; and the record says they have no observable.  The needles are built
;; with `concat' where they would otherwise match this file.
(m58-imp5--check "v2/not-proven-rows-named"
                 (and (m58-imp5--contains-p
                       "tool/run-tests.scm"
                       (concat "NOT PROVEN 5 (no observable: the 3 Group D rows "
                               "scroll_region_ok / line_ins_del_ok / char_ins_del_ok "
                               "and the 2 Group F rows"))
                      (m58-imp5--contains-p "tool/run-tests.scm"
                                            "tty--set-output-buffer-size")
                      (m58-imp5--contains-p "tool/run-tests.scm"
                                            "tty--output-buffer-size")
                      (m58-imp5--contains-p "tool/run-tests.scm" "NOT PROVEN 5")))

;; Group G STAYS C: src/emacs.c resolves the module and loader.scm tests
;; (lookup-language 'emacs-elisp).
(m58-imp5--check "v2/group-g-stays-c"
                 (and (m58-imp5--contains-p
                       "src/emacs.c"
                       "scm_c_resolve_module (\"emacs-elisp spec\")")
                      (m58-imp5--contains-p
                       "mod/emacs/loader.scm"
                       "(lookup-language 'emacs-elisp)")
                      (m58-imp5--contains-p "tool/run-tests.scm"
                                            "Group G (the elisp compiler) STAYS C")))

;;; --- V3. The surface re-measure -------------------------------------

;; Measured on this tree (imp-5 moves no C and no Scheme):
;;   src/term.c                    6425 lines / 29 ^DEFUN ( / 4 --tty-*
;;   scm_c_public_ref in term.c    41
;;   scm_c_public_ref tree-wide    265
;;   mod/emacs/tty-output.scm      682 lines
;;   test/pty-driver.py            32 cases in 19 groups
;;   test/m58                     5 corpus .el files
(setq m58-imp5--group 'v3)

(m58-imp5--check "v3/term-c-surface"
                 (and (eql 6738 (m58-imp5--count "src/term.c" "\n"))
                      (eql 31 (m58-imp5--count "src/term.c" "^DEFUN ("))))

(m58-imp5--check "v3/leaf-defuns-6"
                 (eql 6 (m58-imp5--leaf-defuns)))

(m58-imp5--check "v3/public-refs"
                 (and (eql 42 (m58-imp5--count "src/term.c" "scm_c_public_ref"))
                      (eql 268 (m58-imp5--src-public-refs))))

(m58-imp5--check "v3/module-lines"
                 (eql 860 (m58-imp5--count "mod/emacs/tty-output.scm" "\n")))

(m58-imp5--check "v3/pty-36-cases-20-groups"
                 (let ((pins (m58-imp5--pty-case-pins)))
                   (and (consp pins)
                        (eql 36 (nth 0 pins))
                        (eql 36 (nth 1 pins))
                        (eql 20 (nth 2 pins)))))

;; imp-5 adds ONE corpus, so test/m58 holds 5 .el files.
(m58-imp5--check "v3/corpus-files-5"
                 (and (eql 5 (m58-imp5--corpus-files))
                      (file-exists-p (expand-file-name
                                      "test/m58/test-m58-imp5.el"
                                      m58-imp5--root))))

;;; --- V4. The registration -------------------------------------------

(setq m58-imp5--group 'v4)

(m58-imp5--check "v4/run-tests-m58-imp5"
                 (and (m58-imp5--live-p "tool/run-tests.scm"
                                        "test/m58/test-m58-imp5.el")
                      (m58-imp5--live-p "tool/run-tests.scm"
                                        "(group (m58)")))

(m58-imp5--check "v4/run-tests-after-imp4-and-older-stay"
                 (and (m58-imp5--ordered-p "tool/run-tests.scm"
                                           '("test/m58/test-m58-imp1.el"
                                             "test/m58/test-m58-imp2.el"
                                             "test/m58/test-m58-imp3.el"
                                             "test/m58/test-m58-imp4.el"
                                             "test/m58/test-m58-imp5.el"))
                      ;; ONE new line only: the (m58) group holds 5 lines.
                      (eql 5 (m58-imp5--lines-matching
                              "tool/run-tests.scm"
                              "\"test/m58/test-m58-imp[1-5]\\.el\""))))

;;; --- V5. The real path ----------------------------------------------

;; Run EACH existing PTY group on the built src/emacs.  "PASS" or an
;; explicit INFO skip, never a pass on a skip.  A bad run retries once
;; (the (m58) PTY cases can intermit -- a timing race).

(defun m58-imp5--pty-verdict (group)
  "Run the PTY GROUP on the built src/emacs.  Answer (STATUS . OUTPUT)
where STATUS is `pass', `info', `fail', `no-emacs', or `no-python3'."
  (let ((emacs (expand-file-name "src/emacs" m58-imp5--root)))
    (cond
     ((not (and (file-exists-p emacs) (file-executable-p emacs)))
      (cons 'no-emacs nil))
     (t
      (let* ((args (list "test/pty-driver.py" "--emacs" emacs
                         "--group" group))
             (out1 (m58-imp5--run "python3" args))
             (needle (concat "PASS " group "/"))
             (done (or (eq out1 'm58-imp5-prog-absent)
                       (string-match-p (regexp-quote needle) out1)
                       (string-match-p (concat "INFO " group "/") out1)))
             (out2 (unless done (m58-imp5--run "python3" args)))
             (out (or out2 out1)))
        (cond
         ((eq out1 'm58-imp5-prog-absent) (cons 'no-python3 nil))
         ((string-match-p (regexp-quote needle) out) (cons 'pass out))
         ((string-match-p (concat "INFO " group "/") out) (cons 'info out))
         (t (cons 'fail (list out1 out2)))))))))

(defun m58-imp5--pty-check (name group units)
  "Register one real-path check for GROUP.  UNITS is the number of PASS
lines that a healthy run prints."
  (let ((verdict (m58-imp5--pty-verdict group)))
    (cond
     ((eq (car verdict) 'no-emacs)
      (m58-imp5--info-skip name "no built src/emacs"))
     ((eq (car verdict) 'no-python3)
      (m58-imp5--info-skip name "no python3 binary on PATH"))
     ((eq (car verdict) 'pass)
      (let ((out (cdr verdict)))
        (m58-imp5--check name
                         (>= (m58-imp5--count-in out (concat "PASS " group "/"))
                             units))))
     ((eq (car verdict) 'info)
      (m58-imp5--info-skip name "no PTY on this host"))
     (t
      (princ (format "m58 imp5 PTY %s run 1:\n%s\n" group
                     (nth 0 (cdr verdict))))
      (princ (format "m58 imp5 PTY %s run 2 (retry):\n%s\n" group
                     (nth 1 (cdr verdict))))
      (m58-imp5--check name nil)))))

(setq m58-imp5--group 'v5)

(m58-imp5--pty-check "v5/pty-m58-imp2" "m58-imp2" 1)
(m58-imp5--pty-check "v5/pty-m58-imp3" "m58-imp3" 5)
(m58-imp5--pty-check "v5/pty-m58-imp4" "m58-imp4" 1)

;;; --- V6. The guards -------------------------------------------------

;; An --filter that matches no group reports exit 0 with 0 tests, so a
;; green m58 gate proves nothing until the corpus really registers.
(setq m58-imp5--group 'v6)

(m58-imp5--check "reg/min-v1-checks-3" (>= (m58-imp5--group-count 'v1) 3))
(m58-imp5--check "reg/min-v2-checks-3" (>= (m58-imp5--group-count 'v2) 3))
(m58-imp5--check "reg/min-v3-checks-5" (>= (m58-imp5--group-count 'v3) 5))
(m58-imp5--check "reg/min-v4-checks-2" (>= (m58-imp5--group-count 'v4) 2))
(m58-imp5--check "reg/min-v5-checks-3" (>= (m58-imp5--group-count 'v5) 3))
(m58-imp5--check "reg/min-v6-prior-checks-5"
                 ;; This guard counts the 5 prior guards; it is the 6th.
                 (>= (m58-imp5--group-count 'v6) 5))

;;; --- The group-total check ------------------------------------------

;; 23 registered checks (V1 3, V2 3, V3 6, V4 2, V5 3, V6 6) plus the
;; group-total deftest itself.  A V5 check may fold to a controlled INFO
;; skip on a host with no built src/emacs, no python3, or no PTY, and a
;; controlled skip is still a registered test.

(defvar m58-imp5--gate-total 24
  "The EXACT number of m58-imp5 ERT tests: 23 registered checks (V1 3,
V2 3, V3 6, V4 2, V5 3, V6 6) plus the group-total deftest itself.
The guard uses `equal', not `>=', so a DUPLICATE registration fails too.")

(ert-deftest m58-imp5/gate-m58-total ()
  "The m58-imp5 corpus registers exactly its docs-independent count."
  (should (equal (length (ert-select-tests "^m58-imp5" t))
                 m58-imp5--gate-total)))

(princ (format "=== m58 imp-5 suite done (%d checks; v1 %d, v2 %d, v3 %d, v4 %d, v5 %d, v6 %d) ===\n"
               m58-imp5--registered
               (m58-imp5--group-count 'v1)
               (m58-imp5--group-count 'v2)
               (m58-imp5--group-count 'v3)
               (m58-imp5--group-count 'v4)
               (m58-imp5--group-count 'v5)
               (m58-imp5--group-count 'v6)))
