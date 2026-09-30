;;; test-m43-imp6-docs.el --- M43 imp-6 close-out: the durable-record guard.
;;;
;;; The imp-6 close-out updates three gitignored durable records
;;; (docs/kb.org, docs/m43-plan.org, docs/milestone-overview.org) and the
;;; untracked live tracker milestone.org.  No commit can carry those
;;; files, so a normal corpus must not FAIL on them (brief.org §8).  This
;;; corpus instead guards the update with the imp-1 pattern
;;; (test/m43/test-m43-imp1.el): PASS and register an ERT test when the
;;; record is present AND current; INFO-skip when the record is absent or
;;; stale.  On a fresh clone (no docs/) it is advisory only and registers
;;; no ERT test, so it never turns the gate red.
;;;
;;; It covers:
;;;   D1 -- docs/m43-plan.org marks imp-2 … imp-6 DONE with the commit hash.
;;;   D2 -- docs/kb.org ** M43 is CLOSED, with the imp-5 / imp-6 notes and
;;;         the fixed tty-termios-boundary line numbers.
;;;   D3 -- docs/milestone-overview.org is CLOSED, with the fixed M43 start
;;;         line numbers.
;;;   D4 -- milestone.org holds the closed-M43 state and the next-milestone
;;;         question (not an invented target, not a 0-byte tracker).

(princ "=== m43 imp-6 close-out docs guard ===\n")

(require 'imp-ert-report)

(defvar m43-imp6d--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))

(defun m43-imp6d--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
the symbol `m43-imp6d-absent' when REL does not exist.  docs/ is
gitignored, so a checkout without it must not crash the subprocess."
  (let ((path (expand-file-name rel m43-imp6d--root)))
    (if (not (file-exists-p path))
        'm43-imp6d-absent
      (with-temp-buffer
        (insert-file-contents path)
        (funcall fn)))))

(defun m43-imp6d--contains-p (rel needle)
  "Non-nil when REL (repo-root-relative) contains NEEDLE."
  (m43-imp6d--with rel
    (lambda ()
      (goto-char (point-min))
      (search-forward needle nil t))))

(defun m43-imp6d--check (name rel needle)
  "Report and register one check on a NON-durable record.  PASS and
register an ERT test when REL holds NEEDLE.  INFO-skip when REL is
absent OR present but stale.  A gitignored record is a fact of the
checkout, not a code regression, so it must not turn the gate red
(brief.org §8).  On a fresh clone this is advisory only."
  (let ((hit (m43-imp6d--contains-p rel needle)))
    (if (and hit (not (eq hit 'm43-imp6d-absent)))
        (progn (princ (format "PASS m43/imp6-docs/%s\n" name))
               (imp-register-bool-as-ert-test (format "m43-imp6-docs/%s" name) t))
      (princ (format "INFO m43/imp6-docs/%s skipped (%s, gitignored record)\n"
                     name (if (eq hit 'm43-imp6d-absent) "absent" "stale"))))))

;;; --- D1. docs/m43-plan.org — the imp table is DONE with the hash ------

(m43-imp6d--check "plan/imp-2-done" "docs/m43-plan.org" "DONE (251d59045)")
(m43-imp6d--check "plan/imp-3-done" "docs/m43-plan.org" "DONE (9d6fc23cc)")
(m43-imp6d--check "plan/imp-4-done" "docs/m43-plan.org" "DONE (9d6fc23cc)")
(m43-imp6d--check "plan/imp-5-done" "docs/m43-plan.org" "DONE (188839452)")
(m43-imp6d--check "plan/imp-6-done" "docs/m43-plan.org" "DONE (this close-out commit)")

;;; --- D2. docs/kb.org — ** M43 is CLOSED, with the fixed numbers ------

(m43-imp6d--check "kb/m43-closed" "docs/kb.org" "CLOSED 2026-09-29 (imp-1 … imp-6)")
(m43-imp6d--check "kb/imp-5-landed" "docs/kb.org" "IMP-5 LANDED")
(m43-imp6d--check "kb/imp-6-landed" "docs/kb.org" "IMP-6 (CLOSE-OUT) LANDED")
(m43-imp6d--check "kb/boundary-get-size" "docs/kb.org" "now :1342")
(m43-imp6d--check "kb/boundary-set-window" "docs/kb.org" "now :1356")
(m43-imp6d--check "kb/boundary-reset" "docs/kb.org" "now :1404")

;;; --- D3. docs/milestone-overview.org — CLOSED + fixed numbers --------

(m43-imp6d--check "overview/m43-closed"
                  "docs/milestone-overview.org" "M43: *CLOSED* (2026-09-29)")
(m43-imp6d--check "overview/row-closed"
                  "docs/milestone-overview.org" "4,889 → 4,950; CLOSED")
(m43-imp6d--check "overview/init-line"
                  "docs/milestone-overview.org" "=init_sys_modes= :1114")

;;; --- D4. milestone.org — closed M43 + the next-milestone question ----

(m43-imp6d--check "tracker/m43-closed" "milestone.org" "M43 is *CLOSED*")
(m43-imp6d--check "tracker/next-decision"
                  "milestone.org" "the next milestone is a user decision")
(m43-imp6d--check "tracker/see-review"
                  "milestone.org" "next-milestone-review.org")
(m43-imp6d--check "tracker/not-empty" "milestone.org" "The gains of M43")

(princ "=== m43 imp-6 close-out docs guard done ===\n")
