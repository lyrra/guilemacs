;;; test-m39-imp5.el --- M39 imp-5 close-out corpus suite.
;;;
;;; M39 imp-5 is the close-out (brief.org).  It ports no new C and adds no
;;; Scheme module.  This corpus pins the close-out end state against the
;;; tree, so a stale number or a missing record fails the run.  It has no
;;; C dependency: it only reads files.
;;;
;;; It covers:
;;;   1. the Step 2 surface table, as the measured value;
;;;   2. the two line pins of Step 2 (5465 and 8278), held by
;;;      test/m39/test-m39-imp0-audit.el;
;;;   3. the M39 state words in milestone.org and docs/kb.org, the
;;;      as-built imp-5 line in docs/m39-plan.org, and the close-out
;;;      state in docs/milestone-overview.org;
;;;   4. that this corpus is registered in tool/run-tests.scm.
;;;
;;; Each check is printed as a PASS/FAIL line and turned into an ERT test
;;; so the harness counts it.  A read error is a real error, never a
;;; silent pass.
;;;
;;; The scan helpers work on the buffer directly (re-search-forward /
;;; count-lines / search-forward).  They do not build a line list: a
;;; whole-file split-string over the large sources is expensive in this
;;; Guile build.

(princ "=== m39 imp-5 close-out suite ===\n")

(defvar m39-imp5--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))

(defun m39-imp5--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative)."
  (with-temp-buffer
    (insert-file-contents (expand-file-name rel m39-imp5--root))
    (funcall fn)))

(defun m39-imp5--wc (rel)
  "Count the lines of REL the way `wc -l' does (newline count)."
  (m39-imp5--with rel (lambda () (count-lines (point-min) (point-max)))))

(defun m39-imp5--count (rel regexp)
  "Count the matches of REGEXP in REL."
  (m39-imp5--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (re-search-forward regexp nil t) (setq n (1+ n)))
        n))))

(defun m39-imp5--line-of (rel regexp)
  "1-based line number of the first match of REGEXP in REL, or nil."
  (m39-imp5--with rel
    (lambda ()
      (goto-char (point-min))
      (when (re-search-forward regexp nil t)
        (line-number-at-pos (match-beginning 0))))))

(defun m39-imp5--file-contains-p (rel needle)
  "Non-nil when REL (repo-root-relative) contains NEEDLE."
  (m39-imp5--with rel
    (lambda ()
      (goto-char (point-min))
      (search-forward needle nil t))))

(defun m39-imp5--occurrences (rel needle)
  "Count occurrences of NEEDLE in REL (repo-root-relative)."
  (m39-imp5--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (search-forward needle nil t) (setq n (1+ n)))
        n))))

(defun m39-imp5--public-refs ()
  "Count scm_c_public_ref over the files directly in src/ ending in .c or .h."
  (let ((total 0))
    (dolist (f (directory-files (expand-file-name "src" m39-imp5--root)
                                t "\\.[ch]\\'"))
      (when (and (not (file-directory-p f)) (file-regular-p f))
        (setq total (+ total (m39-imp5--occurrences
                              (file-relative-name f m39-imp5--root)
                              "scm_c_public_ref")))))
    total))

(defun m39-imp5--check (name ok)
  "Report and register one check.  OK is a boolean."
  (princ (format "%s m39/imp5/%s\n" (if ok "PASS" "FAIL") name))
  (eval `(ert-deftest ,(intern (format "m39-imp5/%s" name)) ()
           (should ,ok))))

;;; --- 1. The Step 2 surface table, as the measured value --------------

(m39-imp5--check "keyboard.c-lines-11221"
                 (eql 11221 (m39-imp5--wc "src/keyboard.c")))
(m39-imp5--check "keyboard-globals.c-lines-490"
                 (eql 490 (m39-imp5--wc "src/keyboard-globals.c")))
(m39-imp5--check "combined-11711"
                 (eql 11711 (+ (m39-imp5--wc "src/keyboard.c")
                               (m39-imp5--wc "src/keyboard-globals.c"))))
;; cr.org F3: the old margin check was a tautology, (- 11711 11960).  Check
;; the budget and the margin as the working doc records them instead.
(m39-imp5--check "milestone-budget-11960"
                 (m39-imp5--file-contains-p "milestone.org" "11,960"))
(m39-imp5--check "milestone-margin-249"
                 (m39-imp5--file-contains-p "milestone.org" "249"))
(m39-imp5--check "scm_c_public_ref-162"
                 (eql 162 (m39-imp5--public-refs)))
(m39-imp5--check "keyboard.c-defuns-446"
                 (eql 446 (m39-imp5--count "src/keyboard.c" "^DEFUN (\"")))
(m39-imp5--check "keyboard.c-shims-420"
                 (eql 420 (m39-imp5--count "src/keyboard.c" "^DEFUN (\"--")))
(m39-imp5--check "process.c-lines-8843"
                 (eql 8843 (m39-imp5--wc "src/process.c")))
(m39-imp5--check "process.c-defuns-52"
                 (eql 52 (m39-imp5--count "src/process.c" "^DEFUN (\"")))
(m39-imp5--check "process.c-shims-10"
                 (eql 10 (m39-imp5--count "src/process.c" "^DEFUN (\"--")))

;;; --- 2. The two line pins of Step 2 (held by imp0-audit) -------------

(m39-imp5--check "wait-definition-at-5465"
                 (eql 5465 (m39-imp5--line-of
                            "src/process.c"
                            "^wait_reading_process_output (intmax_t")))
(m39-imp5--check "else-subprocesses-at-8278"
                 (eql 8278 (m39-imp5--line-of
                            "src/process.c"
                            "^#else  /[*] subprocesses [*]/")))
;; The imp0-audit corpus must hold the same two pins.
(m39-imp5--check "imp0-audit-pins-5465"
                 (m39-imp5--file-contains-p "test/m39/test-m39-imp0-audit.el"
                                            "\"wait-definition-at-5465\""))
(m39-imp5--check "imp0-audit-pins-8278"
                 (m39-imp5--file-contains-p "test/m39/test-m39-imp0-audit.el"
                                            "\"else-subprocesses-at-8278\""))

;;; --- 3. The M39 state words in the working docs ----------------------

;; milestone.org: M39 is closed, the imp-5 row is present, and the
;; surface table holds the measured value.
(m39-imp5--check "milestone-M39-closed"
                 (m39-imp5--file-contains-p "milestone.org"
                                            "src/process.c port (CLOSED)"))
(m39-imp5--check "milestone-M39-closed-row"
                 (m39-imp5--file-contains-p "milestone.org" "| M39       | CLOSED"))
(m39-imp5--check "milestone-imp5-row"
                 (m39-imp5--file-contains-p "milestone.org"
                                            "close-out: re-measure the surface, run the gates, record"))
;; cr.org F2: the brief (Step 6) asks for the close-out commit hash.
(m39-imp5--check "milestone-imp5-hash"
                 (m39-imp5--file-contains-p "milestone.org"
                                            "imp-5 =24e24e3= (close-out)"))
(m39-imp5--check "milestone-surface-8843"
                 (m39-imp5--file-contains-p "milestone.org" "8,843"))
;; cr.org F3: anchor the value in the row that names the metric, not a bare
;; table cell.
(m39-imp5--check "milestone-surface-162"
                 (and (m39-imp5--file-contains-p "milestone.org"
                                                 "scm_c_public_ref= sites")
                      (m39-imp5--file-contains-p "milestone.org" "|    162 |")))

;; docs/kb.org ** M39: the imp-5 record, the four live decision modules,
;; and the surface.
(m39-imp5--check "kb-M39-imp5-record"
                 (m39-imp5--file-contains-p "docs/kb.org"
                                            "imp-5 (one commit, 2026-09-17) is the close-out"))
(m39-imp5--check "kb-M39-module-wait"
                 (m39-imp5--file-contains-p "docs/kb.org" "(emacs process-wait)"))
(m39-imp5--check "kb-M39-module-io"
                 (m39-imp5--file-contains-p "docs/kb.org" "(emacs process-io)"))
(m39-imp5--check "kb-M39-module-accessors"
                 (m39-imp5--file-contains-p "docs/kb.org" "(emacs process-accessors)"))
(m39-imp5--check "kb-M39-module-signal"
                 (m39-imp5--file-contains-p "docs/kb.org" "(emacs process-signal)"))
(m39-imp5--check "kb-M39-surface-8843"
                 (m39-imp5--file-contains-p "docs/kb.org" "8,843"))

;; docs/m39-plan.org: the as-built imp-5 line.
(m39-imp5--check "m39-plan-imp5-as-built"
                 (m39-imp5--file-contains-p "docs/m39-plan.org"
                                            "imp-5 as-built (2026-09-17)"))

;; docs/milestone-overview.org: M39 moved to the closed list with its hash.
;; cr.org F3: the old check only matched the bare string "M39".
(m39-imp5--check "overview-M39-closed"
                 (m39-imp5--file-contains-p "docs/milestone-overview.org"
                                            "imp-5 =24e24e3= close-out"))
(m39-imp5--check "overview-M39-closed-word"
                 (m39-imp5--file-contains-p "docs/milestone-overview.org"
                                            "8,860 → 8,843 as-built; CLOSED"))

;;; --- 4. The corpus is registered in run-tests.scm --------------------

(m39-imp5--check "run-tests.scm-registers-el"
                 (m39-imp5--file-contains-p "tool/run-tests.scm"
                                            "test/m39/test-m39-imp5.el"))

(princ "=== m39 imp-5 close-out suite done ===\n")
