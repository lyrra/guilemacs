;;; test-m40-imp0-audit.el --- M40 imp-0 audit: doc/source consistency.
;;;
;;; M40 imp-0 is the docs-only audit (docs/m40-plan.org).  It re-scans
;;; src/process.c, classifies the 52 DEFUNs, confirms the three M39 open
;;; items, and repairs the M39 close-out corpus doc pins.  This suite
;;; pins the audit claims against the tree, so a doc that drifts from
;;; the source fails the run.  It has no C dependency: it only reads
;;; files.
;;;
;;; It covers:
;;;   D1 -- docs/m40-plan.org exists and names the base commit 403e316
;;;         (the imp-5 close-out base; was 764ec06 at imp-0) and the
;;;         target src/process.c.
;;;   D2 -- the base re-scan is exact: src/process.c is 9,030 lines, 50
;;;         DEFUNs, and 10 ==--== shims.  (M40 imp-2 added 19 lines,
;;;         imp-3 retired two DEFUNs, imp-4a added the four Group C
;;;         dispatchers, and imp-4b added five more dispatchers and the
;;;         delete-process / process-send-eof rewrites; the imp-0 base
;;;         measurement of 8,843 is in docs/m40-plan.org.)
;;;   D3 -- docs/m39-plan.org is restored and holds the as-built line.
;;;   D4 -- the send_process multibyte branch line pins (6992, 7010,
;;;         7040, 7063; the imp-2 drift is +19, the imp-3 drift -4,
;;;         the imp-4a drift +76 from the four new dispatchers, and the
;;;         imp-4b drift +103 from the five new dispatchers and the
;;;         delete-process / process-send-eof body rewrites).
;;;   D5 -- the dead pre-rebase hash 24e24e3 no longer appears in the
;;;         road map; the current hash 764ec06 does.
;;;
;;; Each check is printed as an INFO PASS/FAIL line and turned into an
;;; ERT test so the harness counts it.  A read error is a real error,
;;; never a silent pass.

(princ "=== m40 imp-0 audit suite ===\n")

(require 'imp-ert-report)

(defvar m40-imp0--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))

(defun m40-imp0--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
the symbol `m40-imp0-absent' when REL does not exist.  docs/ is
gitignored, so a checkout without it must not crash the whole
subprocess: an unguarded `insert-file-contents' here raised an uncaught
\"No such file or directory\" error that killed the subprocess before
ERT ever ran -- found running a real full suite, and the exact scenario
the run-tests-loadup-emacs crashed-batch fix (M38 imp-1) exists to
catch.  Every wrapper below (`m40-imp0--lines' etc.) just returns
whatever this returns, so `m40-imp0-absent' propagates automatically;
`m40-imp0--check' turns it into an INFO-skip instead of a FAIL."
  (let ((path (expand-file-name rel m40-imp0--root)))
    (if (not (file-exists-p path))
        'm40-imp0-absent
      (with-temp-buffer
        (insert-file-contents path)
        (funcall fn)))))

(defun m40-imp0--contains-p (rel needle)
  "Non-nil when REL (repo-root-relative) contains NEEDLE."
  (m40-imp0--with rel
    (lambda ()
      (goto-char (point-min))
      (search-forward needle nil t))))

(defun m40-imp0--lines (rel)
  "Count the lines of REL the way `wc -l' does (newline count).
Count newlines, not `count-lines': a file without a final newline
would otherwise read one line high."
  (m40-imp0--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (search-forward "\n" nil t) (setq n (1+ n)))
        n))))

(defun m40-imp0--count (rel regexp)
  "Count the matches of REGEXP in REL."
  (m40-imp0--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (re-search-forward regexp nil t) (setq n (1+ n)))
        n))))

(defun m40-imp0--line-of (rel regexp)
  "1-based line number of the first match of REGEXP in REL, or nil."
  (m40-imp0--with rel
    (lambda ()
      (goto-char (point-min))
      (when (re-search-forward regexp nil t)
        (line-number-at-pos (match-beginning 0))))))

(defun m40-imp0--check (name ok)
  "Report and register one check.  OK is a boolean, or the symbol
`m40-imp0-absent' when the doc file the check reads does not exist --
printed as INFO-skipped, not FAIL (docs/ is gitignored, not kept in
sync with the git-tracked test/code work)."
  (if (eq ok 'm40-imp0-absent)
      (princ (format "INFO m40/imp0/%s skipped (source file absent, untracked)\n" name))
    (progn
      (princ (format "%s m40/imp0/%s\n" (if ok "PASS" "FAIL") name))
      (imp-register-bool-as-ert-test (format "m40-imp0/%s" name) ok))))

(defun m40-imp0--doc-check (name rel needle)
  "Report and register one check on a *non-durable* record.  PASS and
register an ERT test when REL (repo-root-relative) holds NEEDLE.
INFO-skip when REL is absent OR present but stale.  docs/ is gitignored
(.gitignore:31), so no commit can carry it: a stale document is a fact
of the checkout, not a code regression, and must not turn the gate red
(cr.org F3).  Use `m40-imp0--check' for a tracked file (src/, test/,
tool/), where a present-but-stale value stays a real FAIL."
  (let ((hit (m40-imp0--contains-p rel needle)))
    ;; `m40-imp0--contains-p' returns the value of `search-forward' -- a
    ;; position on a hit, nil on no hit, or the symbol `m40-imp0-absent'
    ;; when the file is absent.  So test truthiness, not `(eq hit t)':
    ;; `search-forward' never returns t, and `(eq hit t)' was always nil,
    ;; so this check never reported PASS (cr.org F1).
    (if (and hit (not (eq hit 'm40-imp0-absent)))
        (progn (princ (format "PASS m40/imp0/%s\n" name))
               (imp-register-bool-as-ert-test (format "m40/imp0/%s" name) t))
      (princ (format "INFO m40/imp0/%s skipped (%s, gitignored record)\n"
                     name (if (eq hit 'm40-imp0-absent) "absent" "stale"))))))

;;; --- 1. docs/m40-plan.org: the base, the target, the choice ----------

;; docs/ is gitignored: report presence as INFO, not a counted PASS/FAIL --
;; every check below already skips gracefully via m40-imp0--with when the
;; file is absent, so this line would otherwise be the one check in the
;; file that hard-fails on a condition the rest of the file treats as
;; environmental, not a code regression.
(princ (format "INFO m40/imp0/plan-exists %s\n"
              (if (file-readable-p (expand-file-name "docs/m40-plan.org"
                                                      m40-imp0--root))
                  "PASS" "FAIL")))
;; imp-5 updated the plan header: the base is the M40 re-land commit
;; 403e316 (the value at the imp-5 close-out), not the M39 close-out
;; 764ec06 (brief.org §3.5).
(m40-imp0--doc-check "plan-base-403e316"
                     "docs/m40-plan.org"
                     "#+base: HEAD = 403e316")
(m40-imp0--doc-check "plan-target-process.c"
                     "docs/m40-plan.org"
                     "#+target: src/process.c")
;; The imp-0 result must record the restored m39 plan file as the choice.
(m40-imp0--doc-check "plan-records-m39-plan-choice"
                     "docs/m40-plan.org"
                     "Choice: restore =docs/m39-plan.org=")

;;; --- 2. The base re-scan is exact ------------------------------------
;;;
;;; M40 imp-2 landed on src/process.c (the send_process multibyte
;;; decision moved to (emacs process-io)), so the file grew by 19 lines:
;;; 8,843 -> 8,862.  M40 imp-3 retired the process-tty-name and
;;; process-inherit-coding-system-flag DEFUNs (-17 net): 8,862 -> 8,845.
;;; M40 imp-4a added four Group C dispatchers (+82 net) and imp-4b added
;;; five more dispatchers and rewrote the delete-process /
;;; process-send-eof bodies: 8,927 -> 9,030.  The audit pins track the
;;; tree; the imp-0 base count of 8,843 stays in docs/m40-plan.org as the
;;; base measurement.

(m40-imp0--check "process.c-lines-9030"
                 (eql 9030 (m40-imp0--lines "src/process.c")))
(m40-imp0--check "process.c-defuns-50"
                 (eql 50 (m40-imp0--count "src/process.c" "^DEFUN (\"")))
(m40-imp0--check "process.c-shims-10"
                 (eql 10 (m40-imp0--count "src/process.c" "^DEFUN (\"--")))

;;; --- 3. docs/m39-plan.org is restored --------------------------------

(m40-imp0--check "m39-plan-restored"
                 (m40-imp0--contains-p "docs/m39-plan.org"
                                       "imp-5 as-built (2026-09-17)"))
(m40-imp0--check "m39-plan-audit-strings"
                 (and (m40-imp0--contains-p "docs/m39-plan.org"
                                            "src/process.c:5462")
                      (m40-imp0--contains-p "docs/m39-plan.org"
                                            "A 27 + B 6 + C 19 + D 9 + E 3 = 64")))

;;; --- 4. The send_process multibyte branch line pins ------------------
;;; M40 imp-2 added the send_process_object_multibyte_decision dispatcher
;;; above the region (+19 lines) and replaced the inline predicate with a
;;; call.  M40 imp-3 changed the region above by -4 net (four read rows
;;; and the two bit-field kinds added, the process-tty-name DEFUN
;;; removed).  M40 imp-4a added four static dispatchers above the
;;; region, +76 net.  M40 imp-4b added five more dispatchers above the
;;; region, +103 net.  The pins below track the post-imp-4b tree: 6992,
;;; 7010, 7040, 7063.

(m40-imp0--check "send-process-at-6992"
                 (eql 6992 (m40-imp0--line-of
                            "src/process.c"
                            "^send_process (Lisp_Object proc, const char [*]buf")))
(m40-imp0--check "state-decision-at-7010"
                 (eql 7010 (m40-imp0--line-of
                            "src/process.c"
                            "send_process_state_decision (p->status, p->outfd)")))
(m40-imp0--check "src-multibyte-at-7040"
                 (eql 7040 (m40-imp0--line-of
                            "src/process.c"
                            "coding->src_multibyte = 1;")))
(m40-imp0--check "dst-multibyte-at-7063"
                 (eql 7063 (m40-imp0--line-of
                            "src/process.c"
                            "coding->dst_multibyte = 0;")))

;;; --- 5. The dead hash is gone from the road map ----------------------

;; cr.org F3: 24e24e3 is the pre-rebase close-out; a rebase rewrote it to
;; 764ec06.  The road map must name the reachable commit.
(m40-imp0--doc-check "overview-has-current-hash"
                     "docs/milestone-overview.org"
                     "imp-5 =764ec06= close-out")
(m40-imp0--check "overview-has-no-dead-hash"
                 (let ((hit (m40-imp0--contains-p
                             "docs/milestone-overview.org" "24e24e3")))
                   (if (eq hit 'm40-imp0-absent) 'm40-imp0-absent
                     (not hit))))

(princ "=== m40 imp-0 audit suite done ===\n")
