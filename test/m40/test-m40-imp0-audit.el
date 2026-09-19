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
;;;   D1 -- docs/m40-plan.org exists and names the base commit 764ec06
;;;         and the target src/process.c.
;;;   D2 -- the base re-scan is exact: src/process.c is 8,843 lines, 52
;;;         DEFUNs, and 10 ==--== shims.
;;;   D3 -- docs/m39-plan.org is restored and holds the as-built line.
;;;   D4 -- the send_process multibyte branch line pins (6815, 6845).
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
  "Call FN in a temp buffer holding REL (repo-root-relative)."
  (with-temp-buffer
    (insert-file-contents (expand-file-name rel m40-imp0--root))
    (funcall fn)))

(defun m40-imp0--contains-p (rel needle)
  "Non-nil when REL (repo-root-relative) contains NEEDLE."
  (m40-imp0--with rel
    (lambda ()
      (goto-char (point-min))
      (search-forward needle nil t))))

(defun m40-imp0--lines (rel)
  "Count the lines of REL the way `wc -l' does (newline count)."
  (m40-imp0--with rel (lambda () (count-lines (point-min) (point-max)))))

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
  "Report and register one check.  OK is a boolean."
  (princ (format "%s m40/imp0/%s\n" (if ok "PASS" "FAIL") name))
  (imp-register-bool-as-ert-test (format "m40-imp0/%s" name) ok))

;;; --- 1. docs/m40-plan.org: the base, the target, the choice ----------

(m40-imp0--check "plan-exists"
                 (file-readable-p (expand-file-name "docs/m40-plan.org"
                                                    m40-imp0--root)))
(m40-imp0--check "plan-base-764ec06"
                 (m40-imp0--contains-p "docs/m40-plan.org"
                                       "#+base: HEAD = 764ec06"))
(m40-imp0--check "plan-target-process.c"
                 (m40-imp0--contains-p "docs/m40-plan.org"
                                       "#+target: src/process.c"))
;; The imp-0 result must record the restored m39 plan file as the choice.
(m40-imp0--check "plan-records-m39-plan-choice"
                 (m40-imp0--contains-p "docs/m40-plan.org"
                                       "Choice: restore =docs/m39-plan.org="))

;;; --- 2. The base re-scan is exact ------------------------------------

(m40-imp0--check "process.c-lines-8843"
                 (eql 8843 (m40-imp0--lines "src/process.c")))
(m40-imp0--check "process.c-defuns-52"
                 (eql 52 (m40-imp0--count "src/process.c" "^DEFUN (\"")))
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

(m40-imp0--check "send-process-at-6815"
                 (eql 6815 (m40-imp0--line-of
                            "src/process.c"
                            "^send_process (Lisp_Object proc, const char [*]buf")))
(m40-imp0--check "state-decision-at-6833"
                 (eql 6833 (m40-imp0--line-of
                            "src/process.c"
                            "send_process_state_decision (p->status, p->outfd)")))
(m40-imp0--check "src-multibyte-at-6863"
                 (eql 6863 (m40-imp0--line-of
                            "src/process.c"
                            "coding->src_multibyte = 1;")))
(m40-imp0--check "dst-multibyte-at-6886"
                 (eql 6886 (m40-imp0--line-of
                            "src/process.c"
                            "coding->dst_multibyte = 0;")))

;;; --- 5. The dead hash is gone from the road map ----------------------

;; cr.org F3: 24e24e3 is the pre-rebase close-out; a rebase rewrote it to
;; 764ec06.  The road map must name the reachable commit.
(m40-imp0--check "overview-has-current-hash"
                 (m40-imp0--contains-p "docs/milestone-overview.org"
                                       "imp-5 =764ec06= close-out"))
(m40-imp0--check "overview-has-no-dead-hash"
                 (not (m40-imp0--contains-p "docs/milestone-overview.org"
                                            "24e24e3")))

(princ "=== m40 imp-0 audit suite done ===\n")
