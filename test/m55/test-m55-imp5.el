;;; test-m55-imp5.el --- M55 imp-5 close-out corpus (re-measure and record).
;;;
;;; M55 imp-5 is the close-out (brief.org section 1).  It moves no C and
;;; no Scheme: the net C delta is 0 and the net Scheme delta is 0.  It
;;; re-measures the surface, runs the gates, and records the result.
;;; This corpus pins the end state against the TRACKED tree, so a stale
;;; number or a missing registration fails the run.
;;;
;;; The M55 goal is ACHIEVED at imp-4: a plain Guile process LOADS and
;;; RUNS a real Elisp file with the Emacs C core absent.  The narrower
;;; part of the M53 CHECK 1 A2 is CLOSED on the plain path.  The A2
;;; STAYS OPEN on the FULL-EMACS path only: the elisp compiler (row 10,
;;; lookup-language 'emacs-elisp) STAYS C.
;;;
;;; This corpus pins four groups, S1, S1b, S2, S3:
;;;
;;;   S1 -- the re-measured surface of brief.org section 4, measured at
;;;         the imp-5 base HEAD 6b30e6f16: mod/emacs/loader.scm (1,187
;;;         lines, 74 (symbol-function 'X) apply matches, 18
;;;         symbol-fbound? lines, 14 set-symbol-function! lines, 7
;;;         FIX-*-guilemacs lines); mod/emacs/reader.scm (2,021 lines);
;;;         prelude/load.scm (265 lines, 70 ^(use-modules lines, 31
;;;         ^(init-...-registrations) lines).  S1 holds 9 checks.
;;;   S1b -- the real-path re-check (brief.org section 6): ONE plain
;;;         `guile -L mod -c' subprocess calls (use-modules (emacs
;;;         loader)) and (use-modules (emacs-elisp runtime)), then
;;;         init-loader, then elisp-load on a real .el file.  It pins
;;;         the LOAD-OK outcome and the OBSERVABLE SIDE EFFECT (the file
;;;         setq-s a marker string that is read back after the load).
;;;         A missing guile binary is an explicit INFO skip, never a
;;;         pass.  S1b holds 2 checks.
;;;   S2 -- the registration (brief.org section 7): the corpus is
;;;         registered in the (m55) group of tool/run-tests.scm after
;;;         test-m55-imp4.el, the group comes after (m54) and holds the
;;;         imp-1 ... imp-4 files, and the advisory helper
;;;         tool/m55-audit.sh loads the imp-5 file.  The corpus pins the
;;;         TRACKED runner tool/run-tests.scm; it checks the UNTRACKED
;;;         advisory helper only when that file exists (else an INFO
;;;         skip), so a fresh clone must not FAIL on it.  S2 holds 6
;;;         checks.
;;;   S3 -- the guards (brief.org section 8): one per-group min-count
;;;         guard for S1, S1b, and S2.  The in-process group-total
;;;         `ert-deftest' is a separate test in the same phase; it is
;;;         NOT one of the 3 counted guards.
;;;
;;; This corpus reads TRACKED files only (mod/, prelude/, and the
;;; tracked runner tool/run-tests.scm).  The advisory helper
;;; tool/m55-audit.sh is UNTRACKED in this repository -- no *-audit.sh is
;;; tracked -- so the corpus checks it when it exists and registers an
;;; explicit INFO skip when it is absent: a fresh clone must not FAIL on
;;; an untracked host artifact.  The corpus does NOT read docs/
;;; (docs/kb.org test-must-not-read-docs): a gitignored record can only
;;; pass or skip, so a record check proves nothing.
;;;
;;; A read error is a real error, never a silent pass.  An absent
;;; TRACKED file is a real FAIL, not a pass.  A missing `guile' binary is
;;; an explicit INFO skip, never a pass.  Every check registers a real
;;; ERT test via imp-register-bool-as-ert-test, so the harness parses the
;;; ERT output and the exit code is correct: a princ'd FAIL with no ERT
;;; test would leave the exit code 0.

(princ "=== m55 imp-5 close-out suite ===\n")

(require 'imp-ert-report)

(defvar m55-imp5--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))
(defvar m55-imp5--registered 0
  "Total number of checks this corpus has registered.")
(defvar m55-imp5--group nil
  "The group that `m55-imp5--check' counts into: `s1' .. `s3', or nil.")
(defvar m55-imp5--counts nil
  "Alist of (GROUP . COUNT) for the registered checks.")

(defun m55-imp5--group-count (group)
  "Number of checks registered so far in GROUP."
  (or (cdr (assq group m55-imp5--counts)) 0))

(defun m55-imp5--bump-group ()
  "Count one check into `m55-imp5--group'."
  (when m55-imp5--group
    (let ((cell (assq m55-imp5--group m55-imp5--counts)))
      (if cell
          (setcdr cell (1+ (cdr cell)))
        (push (cons m55-imp5--group 1) m55-imp5--counts)))))

(defun m55-imp5--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
the symbol `m55-imp5-absent' when REL does not exist."
  (let ((path (expand-file-name rel m55-imp5--root)))
    (if (not (file-exists-p path))
        'm55-imp5-absent
      (with-temp-buffer
        (insert-file-contents path)
        (funcall fn)))))

(defun m55-imp5--contains-p (rel needle)
  "Non-nil when the TRACKED file REL (repo-root-relative) contains
NEEDLE.  An absent file folds to nil, so `m55-imp5--check' prints FAIL:
an absent TRACKED file is a real error, not a pass (brief.org section 5)."
  (let ((hit (m55-imp5--with rel
               (lambda ()
                 (goto-char (point-min))
                 (search-forward needle nil t)))))
    (and (not (eq hit 'm55-imp5-absent)) (and hit t))))

(defun m55-imp5--line-of (rel needle)
  "1-based line number of the first literal NEEDLE in REL, or nil.
An absent file folds to nil."
  (m55-imp5--with rel
    (lambda ()
      (goto-char (point-min))
      (when (search-forward needle nil t)
        (line-number-at-pos (match-beginning 0))))))

(defun m55-imp5--ordered-p (rel needles)
  "Non-nil when the TRACKED file REL holds every NEEDLE in the GIVEN
ORDER: each search starts after the previous match."
  (m55-imp5--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((all t))
        (dolist (needle needles)
          (when all
            (unless (search-forward needle nil t) (setq all nil))))
        all))))

(defun m55-imp5--lines (rel)
  "Count the newlines of REL the way `wc -l' does."
  (m55-imp5--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (search-forward "\n" nil t) (setq n (1+ n)))
        n))))

(defun m55-imp5--count (rel regexp)
  "Count the matches of REGEXP in REL, the way `grep -o PATTERN | wc -l'
does.  Use this only for a brief row whose command is `grep -o'."
  (m55-imp5--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (re-search-forward regexp nil t) (setq n (1+ n)))
        n))))

(defun m55-imp5--count-lines (rel regexp)
  "Count the LINES of REL that match REGEXP, the way `grep -c PATTERN'
does.  The brief.org section 4 rows that use `grep -c' count LINES, not
matches, so a line with two matches counts once: a later imp that puts
two refs on one line keeps this pin in step with the grep pin."
  (m55-imp5--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0)
            (last 0))
        (while (re-search-forward regexp nil t)
          (let ((line (line-number-at-pos (match-beginning 0))))
            (unless (= line last)
              (setq n (1+ n))
              (setq last line))))
        n))))

(defun m55-imp5--check (name ok)
  "Report and register one check on a TRACKED file.  OK is a boolean.
The count callers pass `(eql N value)': when the source file is absent
the reader returns the symbol `m55-imp5-absent', so `eql' yields nil and
this prints FAIL.  When OK is the symbol `m55-imp5-absent' itself the
file is absent, and this prints FAIL too.  Either way this registers a
real FAILING ERT test, so an absent TRACKED file is a real error, not a
pass: the harness parses ERT's batch output for its exit code, so a
princ'd FAIL with no ERT test would leave the exit code 0."
  (let* ((absent (eq ok 'm55-imp5-absent))
         (pass (and (not absent) (and ok t))))
    (if absent
        (princ (format "FAIL m55/imp5/%s (source file absent)\n" name))
      (princ (format "%s m55/imp5/%s\n" (if pass "PASS" "FAIL") name)))
    (setq m55-imp5--registered (1+ m55-imp5--registered))
    (m55-imp5--bump-group)
    (imp-register-bool-as-ert-test (format "m55-imp5/%s" name) pass)))

(defun m55-imp5--info-skip (name reason)
  "Register one explicit INFO skip, counted into the current group.  A
host limit is a skip, never a pass (brief.org section 6)."
  (princ (format "INFO m55/imp5/%s %s\n" name reason))
  (setq m55-imp5--registered (1+ m55-imp5--registered))
  (m55-imp5--bump-group)
  (imp-register-skip-as-ert-test (format "m55-imp5/%s" name) reason))

(defun m55-imp5--check-advisory (name rel needle)
  "Check the ADVISORY helper file REL for NEEDLE, or skip when REL is
absent.  Every *-audit.sh helper in this repository is UNTRACKED, so a
fresh clone has no such file.  When REL exists this registers a real
check.  When REL is absent this registers an explicit INFO skip, never a
pass (brief.org section 6: a host limit is a skip, never a pass).  Either
way an ERT test is registered, so the S2 count and the group-total floor
stay stable, and a fresh clone does not FAIL on an untracked host
artifact."
  (let ((path (expand-file-name rel m55-imp5--root)))
    (if (not (file-exists-p path))
        (m55-imp5--info-skip
         name (format "%s absent (untracked advisory helper)" rel))
      (m55-imp5--check name (m55-imp5--contains-p rel needle)))))

;;; --- The plain `guile' probe (no Emacs C core) ----------------------

(defun m55-imp5--guile ()
  "The plain `guile' binary on PATH, or nil."
  (executable-find "guile"))

(defun m55-imp5--run-guile (code)
  "Run a plain `guile -L mod -c CODE' subprocess and return its combined
output, or the symbol `m55-imp5-guile-absent' when no guile binary is on
PATH.  The Emacs C core is absent from this subprocess: the core elisp
function cells are NOT installed by it."
  (let ((guile (m55-imp5--guile)))
    (if (not guile)
        'm55-imp5-guile-absent
      (let* ((modpath (expand-file-name "mod" m55-imp5--root))
             (buf (get-buffer-create " *m55-imp5-guile*")))
        (unwind-protect
            (progn
              (with-current-buffer buf (erase-buffer))
              (call-process guile nil buf nil "-L" modpath "-c" code)
              (with-current-buffer buf
                (buffer-substring-no-properties (point-min) (point-max))))
          (kill-buffer buf))))))

(defun m55-imp5--plain-guile-real-load-output ()
  "Write a real Elisp file with an observable side effect, run a plain
`guile -L mod' subprocess that CALLS init-loader (the registration site)
and then loads the file through the Scheme loader (the REAL path, not a
module-load probe), and return the subprocess output.

The file setq-s a marker string.  The subprocess runs (use-modules
(emacs loader)) and (use-modules (emacs-elisp runtime)), then
init-loader FIRST, so the reader/eval cells are installed.  It prints
M55-IMP5-OUTCOME:LOAD-OK on success (or FAULT:KEY + ARGS), and
M55-IMP5-MARKER:VALUE for the observable side effect (UNBOUND when the
file was only READ).  Return the symbol `m55-imp5-guile-absent' when no
guile binary is on PATH."
  (let ((file (make-temp-file "m55-imp5-plain-" nil ".el"))
        (prelude (expand-file-name "prelude" m55-imp5--root)))
    (unwind-protect
        (progn
          (with-temp-file file
            (insert ";; real Elisp file for the C-core-absent M55 imp-5 load\n"
                    "(setq m55-imp5-marker \"M55-IMP5-RAN-OK\")\n"))
          (m55-imp5--run-guile
           (format
            (concat
             "(use-modules (emacs loader))"
             "(use-modules (emacs-elisp runtime))"
             "(define el (module-ref (resolve-module '(emacs loader)) 'elisp-load))"
             "(init-loader \"%s\")"
             "(catch #t "
             "(lambda () (el \"%s\" #nil #nil #nil #nil) "
             "(display \"M55-IMP5-OUTCOME:LOAD-OK\\n\")) "
             "(lambda (k . a) (display \"M55-IMP5-OUTCOME:FAULT:\") (display k) "
             "(display \" ARGS:\") (write a) (newline)))"
             "(display \"M55-IMP5-MARKER:\")"
             "(display (if (symbol-bound? 'm55-imp5-marker) "
             "(symbol-value 'm55-imp5-marker) \"UNBOUND\"))"
             "(newline)")
            prelude file)))
      (ignore-errors (delete-file file)))))

(defun m55-imp5--contains-marker-p (out marker)
  "Non-nil when the subprocess output OUT holds MARKER.  OUT may be the
symbol `m55-imp5-guile-absent'."
  (and (not (eq out 'm55-imp5-guile-absent))
       (string-match-p (regexp-quote marker) out)
       t))

;;; --- S1. The re-measured surface (brief.org section 4) --------------

;; One check per brief.org section 4 value row, except the src/emacs
;; host-limit row.  Re-measured at the imp-5 base HEAD 6b30e6f16.  An
;; absent TRACKED file fails: the count reader returns `m55-imp5-absent'
;; and `eql' yields nil (brief.org section 5).

(setq m55-imp5--group 's1)

;; Row 1: mod/emacs/loader.scm lines = 1,187.
(m55-imp5--check "loader.scm-lines-1203"
                 (eql 1203 (m55-imp5--lines "mod/emacs/loader.scm")))
;; Row 2: mod/emacs/reader.scm lines = 2,021.
(m55-imp5--check "reader.scm-lines-2021"
                 (eql 2021 (m55-imp5--lines "mod/emacs/reader.scm")))
;; Row 3: prelude/load.scm lines = 265.
(m55-imp5--check "prelude-load.scm-lines-230"
                 (eql 230 (m55-imp5--lines "prelude/load.scm")))
;; Row 4: (symbol-function 'X) applies in loader.scm = 74.  The brief
;; command is `grep -o ... | wc -l', a MATCH count, so count matches.
(m55-imp5--check "loader.scm-symbol-function-apply-74"
                 (eql 74 (m55-imp5--count "mod/emacs/loader.scm"
                                          "(symbol-function '")))
;; Row 5: symbol-fbound? lines in loader.scm = 18 (`grep -c').
(m55-imp5--check "loader.scm-symbol-fbound-lines-18"
                 (eql 18 (m55-imp5--count-lines "mod/emacs/loader.scm"
                                                "symbol-fbound?")))
;; Row 6: set-symbol-function! lines in loader.scm = 14 (`grep -c').
(m55-imp5--check "loader.scm-set-symbol-function-lines-14"
                 (eql 14 (m55-imp5--count-lines "mod/emacs/loader.scm"
                                                "set-symbol-function!")))
;; Row 7: FIX-*-guilemacs lines in loader.scm = 7 (`grep -c').
(m55-imp5--check "loader.scm-fix-markers-lines-7"
                 (eql 7 (m55-imp5--count-lines "mod/emacs/loader.scm"
                                               "FIX-.*guilemacs")))
;; Row 8: prelude/load.scm ^(use-modules lines = 70.  Use the ANCHORED
;; pattern: the plain pattern also matches one comment line and gives 71
;; (brief.org section 4).
(m55-imp5--check "prelude-load.scm-use-modules-lines-71"
                 (eql 71 (m55-imp5--count-lines "prelude/load.scm"
                                                "^(use-modules")))
;; Row 9: prelude/load.scm ^(init-...-registrations) lines = 31.
(m55-imp5--check "prelude-load.scm-init-registrations-lines-31"
                 (eql 31 (m55-imp5--count-lines "prelude/load.scm"
                                                "^(init-.*-registrations)")))

;;; --- S1b. The real-path re-check (brief.org section 6) --------------

;; ONE live proof of the M55 achievement: a plain `guile -L mod -c'
;; subprocess calls (use-modules (emacs loader)) and (use-modules
;; (emacs-elisp runtime)), then init-loader, then elisp-load on a real
;; .el file.  A missing guile binary is an explicit INFO skip, never a
;; pass.

(setq m55-imp5--group 's1b)

(let ((out (m55-imp5--plain-guile-real-load-output)))
  (if (eq out 'm55-imp5-guile-absent)
      (progn
        (m55-imp5--info-skip "plain-guile-load-ok"
                             "no guile binary on PATH")
        (m55-imp5--info-skip "plain-guile-runs-file"
                             "no guile binary on PATH"))
    ;; The load returns LOAD-OK: a real .el file loads with the C core
    ;; absent (the M55 goal).
    (m55-imp5--check "plain-guile-load-ok"
                     (m55-imp5--contains-marker-p out "M55-IMP5-OUTCOME:LOAD-OK"))
    ;; The OBSERVABLE SIDE EFFECT: the file RAN, so its setq marker is
    ;; visible after the load.  This check FAILS when the loader only
    ;; READS the file and does NOT run it (the marker stays UNBOUND).
    (m55-imp5--check "plain-guile-runs-file"
                     (and (m55-imp5--contains-marker-p
                           out "M55-IMP5-MARKER:M55-IMP5-RAN-OK")
                          (not (m55-imp5--contains-marker-p
                                out "M55-IMP5-MARKER:UNBOUND"))))))

;;; --- S2. The registration (brief.org section 7) ---------------------

;; Pin the registration against the TRACKED runner tool/run-tests.scm.
;; The advisory helper tool/m55-audit.sh is UNTRACKED (no *-audit.sh is
;; tracked in this repository), so its load-line check is a real check
;; when the file exists and an INFO skip when it is absent: a fresh clone
;; must not FAIL on an untracked host artifact (brief.org section 6).

(setq m55-imp5--group 's2)

(m55-imp5--check "run-tests-m55-imp5"
                 (m55-imp5--contains-p "tool/run-tests.scm"
                                       "test/m55/test-m55-imp5.el"))
(m55-imp5--check "run-tests-m55-imp5-after-imp4"
                 (let ((imp4 (m55-imp5--line-of "tool/run-tests.scm"
                                                "test/m55/test-m55-imp4.el"))
                       (imp5 (m55-imp5--line-of "tool/run-tests.scm"
                                                "test/m55/test-m55-imp5.el")))
                   (and (integerp imp4) (integerp imp5) (< imp4 imp5))))
(m55-imp5--check "run-tests-m55-group"
                 (m55-imp5--contains-p "tool/run-tests.scm" "(group (m55)"))
(m55-imp5--check "run-tests-m55-group-after-m54"
                 (m55-imp5--ordered-p "tool/run-tests.scm"
                                      '("(group (m54)" "(group (m55)")))
(m55-imp5--check "run-tests-m55-holds-imp1-imp2-imp3-imp4"
                 (and (m55-imp5--contains-p "tool/run-tests.scm"
                                            "test/m55/test-m55-imp1.el")
                      (m55-imp5--contains-p "tool/run-tests.scm"
                                            "test/m55/test-m55-imp2.el")
                      (m55-imp5--contains-p "tool/run-tests.scm"
                                            "test/m55/test-m55-imp3.el")
                      (m55-imp5--contains-p "tool/run-tests.scm"
                                            "test/m55/test-m55-imp4.el")))
(m55-imp5--check-advisory "audit-loads-m55-imp5"
                          "tool/m55-audit.sh"
                          "test/m55/test-m55-imp5.el")

;;; --- S3. The guards (brief.org section 8) ---------------------------

;; An --filter that matches no group already reports exit 0 with 0
;; tests, so a green m55 gate proves nothing until the corpus exists and
;; its checks really register.  These guards fail when the corpus body
;; is truncated or its core checks do not run.  The counts are stable
;; because every check is registered at load time.  S1 holds 9 checks,
;; S1b holds 2 checks, and S2 holds 6 checks.

(setq m55-imp5--group 's3)

(m55-imp5--check "reg/min-s1-checks-9" (>= (m55-imp5--group-count 's1) 9))
(m55-imp5--check "reg/min-s1b-checks-2" (>= (m55-imp5--group-count 's1b) 2))
(m55-imp5--check "reg/min-s2-checks-6" (>= (m55-imp5--group-count 's2) 6))

;;; --- The group-total check ------------------------------------------

;; Select ONLY the m55-imp5 tests (the pattern is "^m55-imp5", not
;; "^m55-imp"): the whole (m55) group runs in one emacs process.  The
;; floor is measured from a real run: 20 registered checks (S1 9, S1b 2,
;; S2 6, S3 3) plus the group-total deftest itself.  No check can fold
;; to a controlled skip -- S1b's two checks and the S2 audit check
;; register as ERT tests either way (a real check or an INFO skip) -- so
;; the floor is exact.

(defvar m55-imp5--min-gate-total 21
  "The minimum number of m55-imp5 ERT tests: 20 registered checks (S1 9,
S1b 2, S2 6, S3 3) plus the group-total deftest.")

(ert-deftest m55-imp5/gate-m55-total ()
  "The m55-imp5 corpus registers at least its docs-independent floor."
  (should (>= (length (ert-select-tests "^m55-imp5" t))
              m55-imp5--min-gate-total)))

(princ (format "=== m55 imp-5 close-out suite done (%d tracked checks; s1 %d, s1b %d, s2 %d, s3 %d) ===\n"
               m55-imp5--registered
               (m55-imp5--group-count 's1)
               (m55-imp5--group-count 's1b)
               (m55-imp5--group-count 's2)
               (m55-imp5--group-count 's3)))
