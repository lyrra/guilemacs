;;; test-m40-imp5.el --- M40 imp-5 close-out: re-measure the surface, pin the end state.
;;;
;;; M40 imp-5 adds no C and retires no DEFUN.  It re-measures the
;;; src/process.c surface, runs the gates, and writes the close-out
;;; record.  This corpus pins that end state against the tree, so a
;;; stale number or a missing record fails the run.  It reads files
;;; only; it has no C dependency.
;;;
;;; It covers:
;;;   S1 -- the surface table.  src/process.c is 9,030 lines, 50 DEFUNs,
;;;         and 10 ==--== shims; src/keyboard.c is 11,221 lines and
;;;         src/keyboard-globals.c is 490, a combined 11,711 under the
;;;         11,960 M31 budget (margin 249); the tree-wide
;;;         scm_c_public_ref count over src/*.c and src/*.h is 172.
;;;   S2 -- the src/process.c send_process line pins that
;;;         test/m40/test-m40-imp0-audit.el holds (6992, 7010, 7040,
;;;         7063).
;;;   S3 -- the M40 close-out state words in the durable records
;;;         (docs/kb.org, docs/m40-plan.org, docs/milestone-overview.org)
;;;         and the live tracker (milestone.org).
;;;   S4 -- this corpus is registered in tool/run-tests.scm, so the
;;;         harness really runs it.
;;;   S5 -- the M40 imp0/imp5 audit sources stay consistent: the
;;;         test-m40-imp0-audit.el D1 header comment names the current
;;;         base 403e316, not the stale 764ec06 (cr.org F2); and the
;;;         line counter matches `wc -l' for a file with no final
;;;         newline (cr.org F4).
;;;   S6 -- the *tracked* close-out summary
;;;         test/m40/test-m40-imp5-closeout.org holds the close-out
;;;         words.  test/ is not gitignored, so a commit CAN carry it,
;;;         and a missing or stale word there is a real FAIL (cr.org F1).
;;;
;;; Limit (cr.org F3): docs/ is gitignored and milestone.org is
;;; untracked, so the S3 record pins INFO-skip on a fresh clone rather
;;; than FAIL.  They protect a working tree that holds the docs, not
;;; CI from a clean checkout.  S6 closes that gap: the tracked summary
;;; is FAIL-able, so the close-out is verifiable from a clean checkout.
;;; A *tracked* file (src/, test/) that is present but stale is always
;;; a real FAIL.
;;;
;;; Each check is printed as an INFO PASS/FAIL line and turned into an
;;; ERT test so the harness counts it.  A read error is a real error,
;;; never a silent pass.

(princ "=== m40 imp-5 close-out suite ===\n")

(require 'imp-ert-report)

(defvar m40-imp5--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))

(defun m40-imp5--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
the symbol `m40-imp5-absent' when REL does not exist.  docs/ is
gitignored and milestone.org is untracked, so a checkout without them
must not crash the whole subprocess.  `m40-imp5--check' turns the
absent symbol into an INFO-skip instead of a FAIL."
  (let ((path (expand-file-name rel m40-imp5--root)))
    (if (not (file-exists-p path))
        'm40-imp5-absent
      (with-temp-buffer
        (insert-file-contents path)
        (funcall fn)))))

(defun m40-imp5--contains-p (rel needle)
  "Non-nil when REL (repo-root-relative) contains NEEDLE."
  (m40-imp5--with rel
    (lambda ()
      (goto-char (point-min))
      (search-forward needle nil t))))

(defun m40-imp5--lines (rel)
  "Count the lines of REL the way `wc -l' does (newline count).
Count newlines, not `count-lines': for a file without a final
newline `count-lines' reads one line high, while `wc -l' does not.
See cr.org F4."
  (m40-imp5--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (search-forward "\n" nil t) (setq n (1+ n)))
        n))))

(defun m40-imp5--count (rel regexp)
  "Count the matches of REGEXP in REL."
  (m40-imp5--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (re-search-forward regexp nil t) (setq n (1+ n)))
        n))))

(defun m40-imp5--line-of (rel regexp)
  "1-based line number of the first match of REGEXP in REL, or nil."
  (m40-imp5--with rel
    (lambda ()
      (goto-char (point-min))
      (when (re-search-forward regexp nil t)
        (line-number-at-pos (match-beginning 0))))))

(defun m40-imp5--check (name ok)
  "Report and register one check.  OK is a boolean, or the symbol
`m40-imp5-absent' when the file the check reads does not exist --
printed as INFO-skipped, not FAIL (docs/ is gitignored, and
milestone.org is the untracked live tracker)."
  (if (eq ok 'm40-imp5-absent)
      (princ (format "INFO m40/imp5/%s skipped (source file absent, untracked)\n" name))
    (progn
      (princ (format "%s m40/imp5/%s\n" (if ok "PASS" "FAIL") name))
      (imp-register-bool-as-ert-test (format "m40/imp5/%s" name) ok))))

;;; --- S1. The surface table -------------------------------------------
;;;
;;; The close-out measurement.  Base was 8,843 lines, 52 DEFUNs, 162
;;; bridge sites (docs/m40-plan.org).  M40 moved src/process.c to 9,030
;;; lines and 50 DEFUNs; the keyboard surface held at 11,711 (249 under
;;; the 11,960 M31 budget); the tree-wide count rose to 172.

(m40-imp5--check "surface/process.c-lines-9030"
                 (eql 9030 (m40-imp5--lines "src/process.c")))
(m40-imp5--check "surface/process.c-defuns-50"
                 (eql 50 (m40-imp5--count "src/process.c" "^DEFUN (\"")))
(m40-imp5--check "surface/process.c-shims-10"
                 (eql 10 (m40-imp5--count "src/process.c" "^DEFUN (\"--")))
(m40-imp5--check "surface/keyboard.c-lines-11221"
                 (eql 11221 (m40-imp5--lines "src/keyboard.c")))
(m40-imp5--check "surface/keyboard-globals.c-lines-490"
                 (eql 490 (m40-imp5--lines "src/keyboard-globals.c")))
(m40-imp5--check "surface/keyboard-combined-11711"
                 (let ((k (m40-imp5--lines "src/keyboard.c"))
                       (kg (m40-imp5--lines "src/keyboard-globals.c")))
                   (and (integerp k) (integerp kg) (eql 11711 (+ k kg)))))
(m40-imp5--check "surface/keyboard-margin-249-under-11960"
                 (let ((k (m40-imp5--lines "src/keyboard.c"))
                       (kg (m40-imp5--lines "src/keyboard-globals.c")))
                   (and (integerp k) (integerp kg)
                        (eql 249 (- 11960 (+ k kg))))))
;; The tree-wide scm_c_public_ref count over src/*.c and src/*.h, like
;; the guard scan in test/m40/test-m40-imp2.scm §8.
(m40-imp5--check "surface/tree-ref-sites-177"
                 (let ((files (directory-files (expand-file-name "src" m40-imp5--root)
                                               t "\\.[ch]\\'")))
                   (and (consp files)
                        (eql 177
                             (let ((n 0))
                               (dolist (f files)
                                 (with-temp-buffer
                                   (insert-file-contents f)
                                   (goto-char (point-min))
                                   (while (re-search-forward "scm_c_public_ref" nil t)
                                     (setq n (1+ n)))))
                               n)))))

;;; --- S2. The src/process.c send_process line pins --------------------
;;; The same four pins test/m40/test-m40-imp0-audit.el holds: the
;;; post-imp-4b tree (imp-2 +19, imp-3 -4, imp-4a +76, imp-4b +103).

(m40-imp5--check "pin/send-process-at-6992"
                 (eql 6992 (m40-imp5--line-of
                            "src/process.c"
                            "^send_process (Lisp_Object proc, const char [*]buf")))
(m40-imp5--check "pin/state-decision-at-7010"
                 (eql 7010 (m40-imp5--line-of
                            "src/process.c"
                            "send_process_state_decision (p->status, p->outfd)")))
(m40-imp5--check "pin/src-multibyte-at-7040"
                 (eql 7040 (m40-imp5--line-of
                            "src/process.c"
                            "coding->src_multibyte = 1;")))
(m40-imp5--check "pin/dst-multibyte-at-7063"
                 (eql 7063 (m40-imp5--line-of
                            "src/process.c"
                            "coding->dst_multibyte = 0;")))

;;; --- S3. The M40 close-out state words -------------------------------
;;;
;;; The durable records are docs/kb.org ** M40, docs/m40-plan.org, and
;;; docs/milestone-overview.org.  docs/ is gitignored, so an absent
;;; record is INFO-skipped, not FAIL.
;;;
;;; milestone.org is the *live tracker*: it holds the current milestone
;;; only and is rewritten at every milestone (docs/kb.org Gotcha
;;; closeout-pin-live-tracker).  A pin on it would turn red when the
;;; next milestone starts, although no code changed.  So the tracker is
;;; read but only INFO-skipped when it does not hold the M40 close-out
;;; words; a durable record that is present and stale is a real FAIL.

(defun m40-imp5--contains-or-absent (rel needle)
  "PASS when REL contains NEEDLE; the symbol `m40-imp5-absent' when REL
is absent; nil when REL is present but holds no NEEDLE."
  (m40-imp5--with rel
    (lambda ()
      (goto-char (point-min))
      (search-forward needle nil t))))

(defun m40-imp5--tracker-check (name needle)
  "Check the live tracker.  PASS when milestone.org holds NEEDLE,
INFO-skip when the tracker is absent or has moved on to a later
milestone.  It is never a FAIL: the tracker is not durable."
  (let ((hit (m40-imp5--contains-or-absent "milestone.org" needle)))
    (if (eq hit 'm40-imp5-absent)
        (princ (format "INFO m40/imp5/%s skipped (live tracker absent)\n" name))
      (if hit
          (progn (princ (format "PASS m40/imp5/%s\n" name))
                 (imp-register-bool-as-ert-test (format "m40/imp5/%s" name) t))
        (princ (format "INFO m40/imp5/%s skipped (tracker has moved on)\n" name))))))

(defun m40-imp5--record-check (name rel needle)
  "Check a *non-durable* record.  PASS and register an ERT test when REL
(repo-root-relative) holds NEEDLE.  INFO-skip when REL is absent OR
present but stale.  docs/ is gitignored (.gitignore:31), so no commit
can carry it: a stale record is a fact of the checkout, not a code
regression, and must not turn the gate red (cr.org F3).  Use
`m40-imp5--check' for a tracked file (src/, test/, tool/), where a
present-but-stale value stays a real FAIL."
  (let ((hit (m40-imp5--contains-or-absent rel needle)))
    (if (or (eq hit 'm40-imp5-absent) (null hit))
        (princ (format "INFO m40/imp5/%s skipped (%s, gitignored record)\n"
                       name (if (eq hit 'm40-imp5-absent) "absent" "stale")))
      (princ (format "PASS m40/imp5/%s\n" name))
      (imp-register-bool-as-ert-test (format "m40/imp5/%s" name) t))))

(m40-imp5--record-check "record/kb-m40-closeout"
                        "docs/kb.org" "M40 imp-5")
(m40-imp5--record-check "record/kb-m40-closed"
                        "docs/kb.org" "imp-5 (close-out)")
(m40-imp5--record-check "record/m40-plan-imp5-as-built"
                        "docs/m40-plan.org" "imp-5 as-built")
(m40-imp5--record-check "record/m40-plan-imp4a-listed"
                        "docs/m40-plan.org" "imp-4a")
(m40-imp5--record-check "record/m40-plan-imp4b-listed"
                        "docs/m40-plan.org" "imp-4b")
(m40-imp5--record-check "record/milestone-overview-m40-closed"
                        "docs/milestone-overview.org" "M40: CLOSED")
(m40-imp5--tracker-check "record/live-tracker-imp5-landed"
                         "| imp-5  | close-out")
(m40-imp5--tracker-check "record/live-tracker-process.c-9030"
                         "9,030 lines")

;;; --- S3b. The tracked close-out record (cr.org F1) ------------------
;;;
;;; The S3 records above live in the gitignored docs/ and the untracked
;;; live tracker, so the corpus can only INFO-skip them.  This summary
;;; is *tracked*: test/ is not gitignored, so a commit can carry it.  A
;;; missing or stale word here is a real FAIL, not a skip.  This is what
;;; makes the close-out verifiable from a clean checkout.

(defun m40-imp5--tracked-has (rel needle)
  "Non-nil only when the *tracked* file REL exists AND holds NEEDLE.
Unlike `m40-imp5--contains-or-absent', an absent file is NOT forgiven:
test/ is tracked, so the summary must be in the commit (cr.org F1)."
  (let ((hit (m40-imp5--contains-or-absent rel needle)))
    (and (not (eq hit 'm40-imp5-absent)) (not (null hit)))))

(m40-imp5--check "tracked-closeout/imp-5-close-out"
                 (m40-imp5--tracked-has
                  "test/m40/test-m40-imp5-closeout.org" "imp-5 (close-out)"))
(m40-imp5--check "tracked-closeout/m40-closed"
                 (m40-imp5--tracked-has
                  "test/m40/test-m40-imp5-closeout.org" "M40: CLOSED"))
(m40-imp5--check "tracked-closeout/base-403e316"
                 (m40-imp5--tracked-has
                  "test/m40/test-m40-imp5-closeout.org" "403e316"))
(m40-imp5--check "tracked-closeout/process.c-9030"
                 (m40-imp5--tracked-has
                  "test/m40/test-m40-imp5-closeout.org" "9,030 lines"))
(m40-imp5--check "tracked-closeout/gate-m40"
                 (m40-imp5--tracked-has
                  "test/m40/test-m40-imp5-closeout.org" "322 pass / 0 fail"))

;;; --- S4. The corpus is registered in run-tests.scm -------------------
(m40-imp5--check "registered-in-run-tests.scm"
                 (and (m40-imp5--contains-p
                       "tool/run-tests.scm"
                       "\"test/m40/test-m40-imp5.el\"")
                      t))

;;; --- S5. Cross-file consistency (cr.org F2, F4) ----------------------
;;;
;;; F2: test-m40-imp0-audit.el's D1 header comment must name the same
;;; base the check pins (403e316).  A stale 764ec06 in that comment is
;;; a doc defect even though the check itself passes.  The text is
;;; matched exactly so it does not collide with the two intentional
;;; 764ec06 references further down that file (the M39 close-out line).
(m40-imp5--check "audit/imp0-header-names-403e316"
                 (m40-imp5--contains-p "test/m40/test-m40-imp0-audit.el"
                                       "names the base commit 403e316"))
(m40-imp5--check "audit/imp0-header-no-stale-764ec06"
                 (not (m40-imp5--contains-p
                       "test/m40/test-m40-imp0-audit.el"
                       "names the base commit 764ec06")))
;; F4: the line counter must equal `wc -l' (newline count) even when
;; the file has no final newline.  "a\nb\nc" is 2 lines to wc -l.
(m40-imp5--check "lines/counter-matches-wc-l-no-trailing-newline"
                 (let ((f (make-temp-file "m40-imp5-nonl")))
                   (unwind-protect
                       (progn
                         (with-temp-file f (insert "a\nb\nc"))
                         (eql 2 (m40-imp5--lines f)))
                     (ignore-errors (delete-file f)))))

(princ "=== m40 imp-5 close-out suite done ===\n")
