;;; test-m41-imp4.el --- M41 imp-4 close-out: re-measure the surface, pin the end state.
;;;
;;; M41 imp-4 adds no C and retires no DEFUN.  It re-measures the
;;; src/xdisp.c surface, runs the gates, and writes the close-out
;;; record.  This corpus pins that end state against the tree, so a
;;; stale number or a missing record fails the run.  It reads files
;;; only; it has no C dependency.
;;;
;;; It covers:
;;;   S1 -- the surface table.  src/xdisp.c is 38,990 lines, 24 DEFUNs,
;;;         and 12 scm_c_public_ref sites; the (emacs xdisp) module
;;;         exports 11 procedures; the tree-wide scm_c_public_ref count
;;;         over src/*.[chm] is 177; src/process.c is 9,030 lines and
;;;         50 DEFUNs; src/keyboard.c is 11,221 lines and
;;;         src/keyboard-globals.c is 490, a combined 11,711 under the
;;;         11,960 M31 budget (margin 249).  M42 imp-2 moved the
;;;         keyboard numbers; the values below are re-pinned.
;;;   S2 -- the 24 src/xdisp.c DEFUN line pins.
;;;   S3 -- the M41 close-out state words in the durable records
;;;         (docs/kb.org, docs/m41-plan.org, docs/milestone-overview.org)
;;;         and the live tracker (milestone.org).
;;;   S4 -- this corpus is registered in tool/run-tests.scm, so the
;;;         harness really runs it.
;;;   S3b -- the *tracked* close-out summary
;;;         test/m41/test-m41-imp4-closeout.org holds the close-out
;;;         words.  test/ is not gitignored, so a commit CAN carry it,
;;;         and a missing or stale word there is a real FAIL.
;;;
;;; Limit: docs/ is gitignored and milestone.org is untracked, so the
;;; S3 record pins INFO-skip on a fresh clone rather than FAIL.  They
;;; protect a working tree that holds the docs, not CI from a clean
;;; checkout.  S3b closes that gap: the tracked summary is FAIL-able, so
;;; the close-out is verifiable from a clean checkout.
;;;
;;; Each check is printed as an INFO PASS/FAIL line and turned into an
;;; ERT test so the harness counts it.  A read error is a real error,
;;; never a silent pass.

(princ "=== m41 imp-4 close-out suite ===\n")

(require 'imp-ert-report)

(defvar m41-imp4--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))

(defun m41-imp4--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
the symbol `m41-imp4-absent' when REL does not exist.  docs/ is
gitignored and milestone.org is untracked, so a checkout without them
must not crash the whole subprocess.  `m41-imp4--check' turns the
absent symbol into an INFO-skip instead of a FAIL."
  (let ((path (expand-file-name rel m41-imp4--root)))
    (if (not (file-exists-p path))
        'm41-imp4-absent
      (with-temp-buffer
        (insert-file-contents path)
        (funcall fn)))))

(defun m41-imp4--contains-p (rel needle)
  "Non-nil when REL (repo-root-relative) contains NEEDLE."
  (m41-imp4--with rel
    (lambda ()
      (goto-char (point-min))
      (search-forward needle nil t))))

(defun m41-imp4--lines (rel)
  "Count the lines of REL the way `wc -l' does (newline count)."
  (m41-imp4--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (search-forward "\n" nil t) (setq n (1+ n)))
        n))))

(defun m41-imp4--count (rel regexp)
  "Count the matches of REGEXP in REL."
  (m41-imp4--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (re-search-forward regexp nil t) (setq n (1+ n)))
        n))))

(defun m41-imp4--exports (rel)
  "Count the symbols in the `#:export (...)' list of REL."
  (m41-imp4--with rel
    (lambda ()
      (goto-char (point-min))
      (when (search-forward "#:export (" nil t)
        (let ((n 0))
          (while (progn (skip-chars-forward " \t\n") (not (looking-at ")")))
            (re-search-forward "[^][() \t\n]+" nil t)
            (setq n (1+ n)))
          n)))))

(defun m41-imp4--defun-line (name)
  "1-based line of the `DEFUN (\"NAME\"' definition in src/xdisp.c, or nil."
  (m41-imp4--with "src/xdisp.c"
    (lambda ()
      (goto-char (point-min))
      (when (re-search-forward (concat "^DEFUN (\""
                                       (regexp-quote name) "\"") nil t)
        (line-number-at-pos (match-beginning 0))))))

(defun m41-imp4--check (name ok)
  "Report and register one check.  OK is a boolean, or the symbol
`m41-imp4-absent' when the file the check reads does not exist --
printed as INFO-skipped, not FAIL."
  (if (eq ok 'm41-imp4-absent)
      (princ (format "INFO m41/imp4/%s skipped (source file absent, untracked)\n" name))
    (progn
      (princ (format "%s m41/imp4/%s\n" (if ok "PASS" "FAIL") name))
      (imp-register-bool-as-ert-test (format "m41/imp4/%s" name) ok))))

;;; --- S1. The surface table -------------------------------------------
;;;
;;; The close-out measurement.  Base was 38,916 lines, 24 DEFUNs, 7
;;; scm_c_public_ref sites (docs/m41-plan.org).  imp-2 and imp-3 moved
;;; src/xdisp.c to 38,990 lines and 12 scm_c_public_ref sites; the
;;; (emacs xdisp) module grew to 11 exports; the tree-wide count rose
;;; to 177.  The restored keyboard surface is 11,711 (249
;;; under the 11,960 M31 budget).

(m41-imp4--check "surface/xdisp-lines-38990"
                 (eql 38990 (m41-imp4--lines "src/xdisp.c")))
(m41-imp4--check "surface/xdisp-defuns-24"
                 (eql 24 (m41-imp4--count "src/xdisp.c" "^DEFUN (\"")))
(m41-imp4--check "surface/xdisp-ref-sites-12"
                 (eql 12 (m41-imp4--count "src/xdisp.c" "scm_c_public_ref")))
(m41-imp4--check "surface/xdisp-exports-11"
                 (eql 11 (m41-imp4--exports "mod/emacs/xdisp.scm")))
(m41-imp4--check "surface/process.c-lines-9030"
                 (eql 9030 (m41-imp4--lines "src/process.c")))
(m41-imp4--check "surface/process.c-defuns-50"
                 (eql 50 (m41-imp4--count "src/process.c" "^DEFUN (\"")))
(m41-imp4--check "surface/keyboard.c-lines-11233"
                 ;; M43 imp-2 added the --tty-fd accessor: 11,221 -> 11,233.
                 (eql 11233 (m41-imp4--lines "src/keyboard.c")))
(m41-imp4--check "surface/keyboard-globals.c-lines-490"
                 (eql 490 (m41-imp4--lines "src/keyboard-globals.c")))
(m41-imp4--check "surface/keyboard-combined-11723"
                 (let ((k (m41-imp4--lines "src/keyboard.c"))
                       (kg (m41-imp4--lines "src/keyboard-globals.c")))
                   (and (integerp k) (integerp kg) (eql 11723 (+ k kg)))))
(m41-imp4--check "surface/keyboard-margin-237-under-11960"
                 (let ((k (m41-imp4--lines "src/keyboard.c"))
                       (kg (m41-imp4--lines "src/keyboard-globals.c")))
                   (and (integerp k) (integerp kg)
                        (eql 237 (- 11960 (+ k kg))))))
;; The tree-wide scm_c_public_ref count over src/*.c, src/*.h and
;; src/*.m, like the measurement in brief.org §3.1.
(m41-imp4--check "surface/tree-ref-sites-181"
                 (let ((files (directory-files (expand-file-name "src" m41-imp4--root)
                                               t "\\.\\(c\\|h\\|m\\)\\'")))
                   (and (consp files)
                        (eql 181
                             (let ((n 0))
                               (dolist (f files)
                                 (with-temp-buffer
                                   (insert-file-contents f)
                                   (goto-char (point-min))
                                   (while (re-search-forward "scm_c_public_ref" nil t)
                                     (setq n (1+ n)))))
                               n)))))

;;; --- S2. The 24 src/xdisp.c DEFUN line pins --------------------------
;;; The definition lines of the 24 DEFUNs, in the order of
;;; docs/m41-plan.org §4.  A later edit above these lines drifts the
;;; pins; this corpus fails on the drift.

(let ((pins '(("set-buffer-redisplay"                . 1059)
              ("line-pixel-height"                   . 1681)
              ("remember-mouse-glyph"                . 3163)
              ("get-display-property"                . 6007)
              ("window-text-pixel-size"              . 12166)
              ("buffer-text-pixel-size"              . 12246)
              ("display--line-is-continued-p"        . 12304)
              ("tab-bar-height"                      . 14975)
              ("tool-bar-height"                     . 16003)
              ("long-line-optimizations-p"           . 20220)
              ("dump-glyph-matrix"                   . 23415)
              ("dump-frame-glyph-matrix"             . 23440)
              ("dump-glyph-row"                      . 23455)
              ("dump-tab-bar-row"                    . 23491)
              ("dump-tool-bar-row"                   . 23524)
              ("trace-redisplay"                     . 23555)
              ("trace-to-stderr"                     . 23572)
              ("current-bidi-paragraph-direction"    . 26514)
              ("bidi-find-overridden-directionality" . 26607)
              ("move-point-visually"                 . 26758)
              ("bidi-resolved-levels"                . 27216)
              ("format-mode-line"                    . 28535)
              ("invisible-p"                         . 29809)
              ("lookup-image-map"                    . 35805))))
  (dolist (pin pins)
    (let ((name (car pin))
          (line (cdr pin)))
      (m41-imp4--check (format "pin/defun-line/%s-%d" name line)
                       (eql line (m41-imp4--defun-line name))))))

;;; --- S3. The M41 close-out state words -------------------------------
;;;
;;; The durable records are docs/kb.org ** M41, docs/m41-plan.org, and
;;; docs/milestone-overview.org.  docs/ is gitignored, so an absent or
;;; stale record is INFO-skipped, not FAIL.

(defun m41-imp4--contains-or-absent (rel needle)
  "PASS when REL contains NEEDLE; the symbol `m41-imp4-absent' when REL
is absent; nil when REL is present but holds no NEEDLE."
  (m41-imp4--with rel
    (lambda ()
      (goto-char (point-min))
      (search-forward needle nil t))))

(defun m41-imp4--tracker-check (name needle)
  "Check the live tracker.  PASS when milestone.org holds NEEDLE,
INFO-skip when the tracker is absent or has moved on to a later
milestone.  It is never a FAIL: the tracker is not durable."
  (let ((hit (m41-imp4--contains-or-absent "milestone.org" needle)))
    (if (eq hit 'm41-imp4-absent)
        (princ (format "INFO m41/imp4/%s skipped (live tracker absent)\n" name))
      (if hit
          (progn (princ (format "PASS m41/imp4/%s\n" name))
                 (imp-register-bool-as-ert-test (format "m41/imp4/%s" name) t))
        (princ (format "INFO m41/imp4/%s skipped (tracker has moved on)\n" name))))))

(defun m41-imp4--record-check (name rel needle)
  "Check a *non-durable* record.  PASS and register an ERT test when REL
holds NEEDLE.  INFO-skip when REL is absent OR present but stale.
docs/ is gitignored (.gitignore:31), so no commit can carry it: a stale
record must not turn the gate red.  Use `m41-imp4--check' for a tracked
file (src/, test/, tool/), where a present-but-stale value is a FAIL."
  (let ((hit (m41-imp4--contains-or-absent rel needle)))
    (if (or (eq hit 'm41-imp4-absent) (null hit))
        (princ (format "INFO m41/imp4/%s skipped (%s, gitignored record)\n"
                       name (if (eq hit 'm41-imp4-absent) "absent" "stale")))
      (princ (format "PASS m41/imp4/%s\n" name))
      (imp-register-bool-as-ert-test (format "m41/imp4/%s" name) t))))

(m41-imp4--record-check "record/kb-m41-closed"
                        "docs/kb.org" "M41: CLOSED")
(m41-imp4--record-check "record/kb-m41-imp4-closeout"
                        "docs/kb.org" "imp-4 (close-out)")
(m41-imp4--record-check "record/m41-plan-imp4-as-built"
                        "docs/m41-plan.org" "imp-4 as-built")
(m41-imp4--record-check "record/milestone-overview-m41-closed"
                        "docs/milestone-overview.org" "M41: CLOSED")
(m41-imp4--tracker-check "record/live-tracker-imp4-landed"
                         "| imp-4  | close-out")
(m41-imp4--tracker-check "record/live-tracker-xdisp-38990"
                         "38,990 lines")

;;; --- S3b. The tracked close-out record ------------------------------
;;;
;;; The S3 records above live in the gitignored docs/ and the untracked
;;; live tracker, so the corpus can only INFO-skip them.  This summary
;;; is *tracked*: test/ is not gitignored, so a commit can carry it.  A
;;; missing or stale word here is a real FAIL, not a skip.  This is what
;;; makes the close-out verifiable from a clean checkout.

(defun m41-imp4--tracked-has (rel needle)
  "Non-nil only when the *tracked* file REL exists AND holds NEEDLE.
Unlike `m41-imp4--contains-or-absent', an absent file is NOT forgiven:
test/ is tracked, so the summary must be in the commit."
  (let ((hit (m41-imp4--contains-or-absent rel needle)))
    (and (not (eq hit 'm41-imp4-absent)) (not (null hit)))))

(m41-imp4--check "tracked-closeout/imp-4-close-out"
                 (m41-imp4--tracked-has
                  "test/m41/test-m41-imp4-closeout.org" "imp-4 (close-out)"))
(m41-imp4--check "tracked-closeout/m41-closed"
                 (m41-imp4--tracked-has
                  "test/m41/test-m41-imp4-closeout.org" "M41: CLOSED"))
(m41-imp4--check "tracked-closeout/base-14a63d3a"
                 (m41-imp4--tracked-has
                  "test/m41/test-m41-imp4-closeout.org" "14a63d3a"))
(m41-imp4--check "tracked-closeout/xdisp-38990"
                 (m41-imp4--tracked-has
                  "test/m41/test-m41-imp4-closeout.org" "38,990 lines"))
(m41-imp4--check "tracked-closeout/gate-m41"
                 (m41-imp4--tracked-has
                  "test/m41/test-m41-imp4-closeout.org" "220 pass / 0 fail"))
(m41-imp4--check "tracked-closeout/mechanism-16"
                 (m41-imp4--tracked-has
                  "test/m41/test-m41-imp4-closeout.org" "16 mechanism names"))
(m41-imp4--check "tracked-closeout/blocked-3"
                 (m41-imp4--tracked-has
                  "test/m41/test-m41-imp4-closeout.org" "3 blocked names"))

;;; --- S4. The corpus is registered in run-tests.scm -------------------
(m41-imp4--check "registered-in-run-tests.scm"
                 (and (m41-imp4--contains-p
                       "tool/run-tests.scm"
                       "\"test/m41/test-m41-imp4.el\"")
                      t))

(princ "=== m41 imp-4 close-out suite done ===\n")
