;;; test-m39-imp0-audit.el --- M39 imp-0 audit: doc/source consistency.
;;;
;;; M39 imp-0 is the docs-only audit (docs/m39-plan.org).  It makes
;;; numeric and line-number claims about src/process.c.  This suite pins
;;; those claims against the tree, so a doc that drifts from the source
;;; fails the run.  It has no C dependency: it only reads files.
;;;
;;; It covers the review findings (cr.org):
;;;   D1 -- wait_reading_process_output is defined at src/process.c:5462
;;;         (5416 at the imp-0 base, +11 after imp-1, +46 after imp-2),
;;;         not 5329, and there is no #ifndef subprocesses fallback.
;;;   D2 -- the DEFUN count is 64 and the six regrouped syscall members
;;;         exist; the plan's group counts are 27/6/19/9/3.
;;;
;;; Each check is printed as an INFO PASS/FAIL line and turned into an
;;; ERT test so the harness counts it.  A read error is a real error,
;;; never a silent pass.

(princ "=== m39 imp-0 audit suite ===\n")

(defvar m39-imp0--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))

(defun m39-imp0--lines (rel)
  "Return the lines of REL (repo-root-relative) as a list."
  (with-temp-buffer
    (insert-file-contents (expand-file-name rel m39-imp0--root))
    (split-string (buffer-string) "\n")))

(defun m39-imp0--count (rel regexp)
  "Count lines of REL that match REGEXP."
  (let ((n 0))
    (dolist (l (m39-imp0--lines rel))
      (when (string-match-p regexp l) (setq n (1+ n))))
    n))

(defun m39-imp0--line-of (rel regexp)
  "1-based line number of the first line of REL that matches REGEXP."
  (let ((ln 0) (res nil))
    (dolist (l (m39-imp0--lines rel))
      (setq ln (1+ ln))
      (when (and (not res) (string-match-p regexp l)) (setq res ln)))
    res))

(defun m39-imp0--check (name ok)
  "Report and register one check.  OK is a boolean."
  (princ (format "INFO m39/imp0/%s %s\n" name (if ok "PASS" "FAIL")))
  (eval `(ert-deftest ,(intern (format "m39-imp0/%s" name)) ()
           (should ,ok))))

;; D1: the wait definition line and the absence of a subprocesses fallback.
;; (imp-1 added the accept-process-output dispatcher and its forward
;; declaration before the wait definition: 5416 -> 5427.  imp-2 added the
;; two (emacs process-io) dispatchers at the same place: 5427 -> 5462.
;; imp-2 then shortened the send_process state-gate call by one line, so
;; the Fdelete_process #else line drifted 8295 -> 8306 -> 8349 -> 8348.
;; imp-3 adds the --process-ref/--process-set! bridge and retires the
;; Group A accessors above these lines: the wait line 5462 -> 5461 and
;; the #else line 8348 -> 8341.)
(m39-imp0--check "wait-definition-at-5461"
                 (eql 5461 (m39-imp0--line-of
                            "src/process.c"
                            "^wait_reading_process_output (intmax_t")))
(m39-imp0--check "no-ifndef-subprocesses"
                 (= 0 (m39-imp0--count "src/process.c"
                                       "^(ifndef subprocesses")))
(m39-imp0--check "else-subprocesses-at-8341"
                 (eql 8341 (m39-imp0--line-of
                            "src/process.c"
                            "^#else  /[*] subprocesses [*]/")))

;; D2: the DEFUN total and the six re-grouped members.  imp-3 retired 12
;; Group A DEFUNs and the dead #if 0 process-connection DEFUN, and added
;; the two bridge DEFUNs --process-ref/--process-set!: 64 -> 52.
(m39-imp0--check "defun-count-52"
                 (= 52 (m39-imp0--count "src/process.c" "^DEFUN (\"")))
(dolist (name '("process-running-child-p" "set-network-process-option"
                "process-datagram-address" "set-process-datagram-address"
                "set-process-window-size" "set-process-coding-system"))
  (m39-imp0--check (format "defun-exists-%s" name)
                   (= 1 (m39-imp0--count
                         "src/process.c"
                         (concat "^DEFUN (\"" (regexp-quote name) "\"")))))

;; The plan must carry the corrected numbers, not the stale ones.
(m39-imp0--check "plan-has-5462"
                 (string-match-p "src/process\\.c:5462"
                                 (mapconcat #'identity
                                            (m39-imp0--lines "docs/m39-plan.org")
                                            "\n")))
(m39-imp0--check "plan-has-no-5329"
                 (not (string-match-p "process\\.c:5329"
                                      (mapconcat #'identity
                                                 (m39-imp0--lines "docs/m39-plan.org")
                                                 "\n"))))
(m39-imp0--check "plan-group-counts"
                 (string-match-p
                  "A 27 \\+ B 6 \\+ C 19 \\+ D 9 \\+ E 3 = 64"
                  (mapconcat #'identity
                             (m39-imp0--lines "docs/m39-plan.org")
                             "\n")))
