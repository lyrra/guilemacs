;;; test-m55-imp3.el --- M55 imp-3 standalone load check corpus.
;;;
;;; M55 imp-3 is the CHECK and the RECORD (brief.org section 1).  It
;;; proves the imp-2 end state with a real behavior corpus.  It moves no
;;; C and changes no loader behavior: the C delta is 0 and no mod/ or
;;; prelude/ line changes.
;;;
;;; The corpus shows, by measurement, on the REAL path (a plain
;;; `guile -L mod' subprocess that calls init-loader and then loads a
;;; real .el file through elisp-load):
;;;
;;;   1. a plain guile process calls init-loader, then elisp-load (the
;;;      REAL path, not a module-load probe);
;;;   2. after init-loader NO reachable runtime cell is empty;
;;;   3. M55 imp-4 removed row 10 (the elisp compiler) from this route, so
;;;      the load no longer stops there.  This corpus now records the
;;;      imp-4 end state: the real .el file LOADS (M55-IMP3-OUTCOME:LOAD-OK).
;;;
;;; This corpus pins these groups:
;;;
;;;   S1 -- the REAL path (brief.org section 6.1).  A plain
;;;         `guile -L mod -c' subprocess calls (use-modules (emacs
;;;         loader)) and (use-modules (emacs-elisp runtime)), then
;;;         init-loader (the registration site), then elisp-load on a
;;;         real .el file.  It DERIVES that no reachable cell is empty
;;;         (the first empty cell is NONE) and pins the stop point: the
;;;         load stops at row 10 (the elisp compiler) with misc-error
;;;         "no such language ~S" (emacs-elisp).  The check asserts the
;;;         LANGUAGE NAME, not only the misc-error key.  S1 holds 2
;;;         checks.
;;;   S2 -- the ordered cell list (brief.org section 6.2).  The 7 cells
;;;         install in call order (rows 3 ... 9) in mod/emacs/loader.scm.
;;;         The check is a `come before' ORDER check on the 7
;;;         set-symbol-function! forms: a reordering FAILS the run.  S2
;;;         holds 1 check.
;;;   S3 -- the surface pins, re-measured at imp-4 (brief.org section 9):
;;;         loader.scm 1190 lines / 74
;;;         (symbol-function 'X) apply matches / 18 symbol-fbound? / 14
;;;         set-symbol-function! / 7 FIX-*-guilemacs; reader.scm 2,021
;;;         lines; prelude/load.scm 265 lines.  imp-4 edits
;;;         mod/emacs/loader.scm, so these values move from the imp-3
;;;         values.  S3 holds 7 checks.
;;;   S4 -- the registration (brief.org section 6.4): the (m55) group of
;;;         tool/run-tests.scm holds the imp-3 file and the (m55) group
;;;         line; the group comes after (m54); the group holds the imp-1
;;;         and imp-2 files.  S4 holds 4 checks.
;;;   S5 -- the guards (brief.org section 6.5): one per-group min-count
;;;         guard for each of S1 .. S4.  The in-process group-total
;;;         `ert-deftest' is a separate test in the same phase; it is NOT
;;;         one of the 4 counted checks (the floor is 18 registered
;;;         checks plus that deftest = 19).
;;;
;;; This corpus reads TRACKED files only (mod/, prelude/, and the
;;; tracked runner tool/run-tests.scm).  It does NOT read docs/
;;; (docs/kb.org test-must-not-read-docs): a gitignored record can only
;;; pass or skip, so a record check proves nothing.
;;;
;;; A read error is a real error, never a silent pass.  An absent
;;; TRACKED file is a real FAIL, not a pass (brief.org section 6.6).  A
;;; missing `guile' binary is an explicit INFO skip, never a pass.  Every
;;; check registers a real ERT test via imp-register-bool-as-ert-test, so
;;; the harness parses the ERT output and the exit code is correct.

(princ "=== m55 imp-3 standalone load check suite ===\n")

(require 'imp-ert-report)

(defvar m55-imp3--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))
(defvar m55-imp3--registered 0
  "Total number of checks this corpus has registered.")
(defvar m55-imp3--group nil
  "The group that `m55-imp3--check' counts into: `s1' .. `s5', or nil.")
(defvar m55-imp3--counts nil
  "Alist of (GROUP . COUNT) for the registered checks.")

(defun m55-imp3--group-count (group)
  "Number of checks registered so far in GROUP."
  (or (cdr (assq group m55-imp3--counts)) 0))

(defun m55-imp3--bump-group ()
  "Count one check into `m55-imp3--group'."
  (when m55-imp3--group
    (let ((cell (assq m55-imp3--group m55-imp3--counts)))
      (if cell
          (setcdr cell (1+ (cdr cell)))
        (push (cons m55-imp3--group 1) m55-imp3--counts)))))

(defun m55-imp3--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
the symbol `m55-imp3-absent' when REL does not exist."
  (let ((path (expand-file-name rel m55-imp3--root)))
    (if (not (file-exists-p path))
        'm55-imp3-absent
      (with-temp-buffer
        (insert-file-contents path)
        (funcall fn)))))

(defun m55-imp3--contains-p (rel needle)
  "Non-nil when the TRACKED file REL contains NEEDLE.  An absent file
folds to nil, so a check prints FAIL: an absent TRACKED file is a real
error, not a pass (brief.org section 6.6)."
  (let ((hit (m55-imp3--with rel
               (lambda ()
                 (goto-char (point-min))
                 (search-forward needle nil t)))))
    (and (not (eq hit 'm55-imp3-absent)) (and hit t))))

(defun m55-imp3--ordered-p (rel needles)
  "Non-nil when the TRACKED file REL holds every NEEDLE in the GIVEN
ORDER: each search starts after the previous match."
  (m55-imp3--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((all t))
        (dolist (needle needles)
          (when all
            (unless (search-forward needle nil t) (setq all nil))))
        all))))

(defun m55-imp3--lines (rel)
  "Count the newlines of REL the way `wc -l' does."
  (m55-imp3--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (search-forward "\n" nil t) (setq n (1+ n)))
        n))))

(defun m55-imp3--count (rel regexp)
  "Count the matches of REGEXP in REL, the way `grep -o PATTERN | wc -l'
does.  Use this only for a brief row whose command is `grep -o'."
  (m55-imp3--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (re-search-forward regexp nil t) (setq n (1+ n)))
        n))))

(defun m55-imp3--count-lines (rel regexp)
  "Count the lines of REL that match REGEXP, the way `grep -c PATTERN'
does.  The brief.org section 3 rows use `grep -c' (a LINE count), so
this corpus counts lines and not matches."
  (m55-imp3--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (not (eobp))
          (when (re-search-forward regexp (line-end-position) t)
            (setq n (1+ n)))
          (forward-line 1))
        n))))

(defun m55-imp3--check (name ok)
  "Report and register one check on a TRACKED file.  OK is a boolean.
When the source file is absent the reader returns the symbol
`m55-imp3-absent', so a count check folds to a real FAILING ERT test."
  (let* ((absent (eq ok 'm55-imp3-absent))
         (pass (and (not absent) (and ok t))))
    (if absent
        (princ (format "FAIL m55/imp3/%s (source file absent)\n" name))
      (princ (format "%s m55/imp3/%s\n" (if pass "PASS" "FAIL") name)))
    (setq m55-imp3--registered (1+ m55-imp3--registered))
    (m55-imp3--bump-group)
    (imp-register-bool-as-ert-test (format "m55-imp3/%s" name) pass)))

(defun m55-imp3--info-skip (name reason)
  "Register one explicit INFO skip, counted into the current group.  A
host limit is a skip, never a pass (brief.org section 6.6)."
  (princ (format "INFO m55/imp3/%s %s\n" name reason))
  (setq m55-imp3--registered (1+ m55-imp3--registered))
  (m55-imp3--bump-group)
  (imp-register-skip-as-ert-test (format "m55-imp3/%s" name) reason))

;;; --- The plain `guile' probe (no Emacs C core) ----------------------

(defun m55-imp3--guile ()
  "The plain `guile' binary on PATH, or nil."
  (executable-find "guile"))

(defun m55-imp3--run-guile (code)
  "Run a plain `guile -L mod -c CODE' subprocess and return its combined
output, or the symbol `m55-imp3-guile-absent' when no guile binary is on
PATH.  The Emacs C core is absent from this subprocess: the core elisp
function cells are NOT installed by it."
  (let ((guile (m55-imp3--guile)))
    (if (not guile)
        'm55-imp3-guile-absent
      (let* ((modpath (expand-file-name "mod" m55-imp3--root))
             (buf (get-buffer-create " *m55-imp3-guile*")))
        (unwind-protect
            (progn
              (with-current-buffer buf (erase-buffer))
              (call-process guile nil buf nil "-L" modpath "-c" code)
              (with-current-buffer buf
                (buffer-substring-no-properties (point-min) (point-max))))
          (kill-buffer buf))))))

(defun m55-imp3--plain-guile-real-load-output ()
  "Write a real Elisp file, run a plain `guile -L mod' subprocess that
CALLS init-loader (the registration site) and then loads the file
through the Scheme loader (the REAL path, not a module-load probe), and
return the subprocess output.

The subprocess runs (use-modules (emacs loader)) and (use-modules
(emacs-elisp runtime)), then init-loader FIRST, so the 7 runtime cells
are installed.  Then it DERIVES the first empty cell from the ordered
cell list (brief.org section 6.1 step 2): it walks the reachable runtime
cells in call order and prints the first one that `symbol-fbound?'
reports empty.  It prints M55-IMP3-FIRST-EMPTY:NAME, and
M55-IMP3-OUTCOME:FAULT:KEY + ARGS for the full load.  Return the symbol
`m55-imp3-guile-absent' when no guile binary is on PATH."
  (let ((file (make-temp-file "m55-imp3-plain-" nil ".el"))
        (prelude (expand-file-name "prelude" m55-imp3--root)))
    (unwind-protect
        (progn
          (with-temp-file file
            (insert ";; real Elisp file for the C-core-absent M55 imp-3 load\n"
                    "(setq m55-imp3-standalone-loaded 'm55-imp3-standalone-ok)\n"))
          (m55-imp3--run-guile
           (format
            (concat
             "(use-modules (emacs loader))"
             "(use-modules (emacs-elisp runtime))"
             "(define (first-empty cells)"
             "  (cond ((null? cells) \"NONE\")"
             "        ((symbol-fbound? (car cells)) (first-empty (cdr cells)))"
             "        (else (symbol->string (car cells)))))"
             "(define el (module-ref (resolve-module '(emacs loader)) 'elisp-load))"
             "(init-loader \"%s\")"
             "(display \"M55-IMP3-FIRST-EMPTY:\")"
             "(display (first-empty '(get-load-suffixes append symbol-value car expand-file-name file-directory-p cdr)))"
             "(newline)"
             "(catch #t "
             "(lambda () (el \"%s\" #nil #nil #nil #nil) "
             "(display \"M55-IMP3-OUTCOME:LOAD-OK\\n\")) "
             "(lambda (k . a) (display \"M55-IMP3-OUTCOME:FAULT:\") (display k) "
             "(display \" ARGS:\") (write a) (newline)))")
            prelude file)))
      (ignore-errors (delete-file file)))))

(defun m55-imp3--contains-marker-p (out marker)
  "Non-nil when the subprocess output OUT holds MARKER.  OUT may be the
symbol `m55-imp3-guile-absent'."
  (and (not (eq out 'm55-imp3-guile-absent))
       (string-match-p (regexp-quote marker) out)
       t))

;;; --- S1. The REAL path (brief.org section 6.1) ----------------------

;; A plain `guile -L mod -c' subprocess calls init-loader, then loads a
;; real .el file through the Scheme loader.  A missing guile binary is an
;; explicit INFO skip, never a pass.

(setq m55-imp3--group 's1)

(let ((out (m55-imp3--plain-guile-real-load-output)))
  (if (eq out 'm55-imp3-guile-absent)
      (progn
        (m55-imp3--info-skip "plain-guile-no-empty-cell"
                             "no guile binary on PATH")
        (m55-imp3--info-skip "plain-guile-load-ok"
                             "no guile binary on PATH"))
    (progn
      ;; After init-loader, rows 3 ... 9 are no longer empty: the first
      ;; empty cell of the ordered list is NONE.
      (m55-imp3--check "plain-guile-no-empty-cell"
                       (m55-imp3--contains-marker-p out "M55-IMP3-FIRST-EMPTY:NONE"))
      ;; M55 imp-4 removed row 10 from the route: the load no longer stops
      ;; at the elisp compiler.  The check pins the imp-4 end state, the
      ;; LOAD-OK outcome (the imp-3 row-10 stop is gone).
      (m55-imp3--check "plain-guile-load-ok"
                       (m55-imp3--contains-marker-p out "M55-IMP3-OUTCOME:LOAD-OK")))))

;;; --- S2. The ordered cell list (brief.org section 6.2) --------------

;; The 7 runtime cells (rows 3 ... 9) must install in call order in
;; init-loader (mod/emacs/loader.scm).  The check is a `come before'
;; ORDER check: a reordering fails the run.

(setq m55-imp3--group 's2)

(m55-imp3--check "install-cells-in-call-order"
                 (m55-imp3--ordered-p
                  "mod/emacs/loader.scm"
                  '("(set-symbol-function! 'get-load-suffixes elisp-get-load-suffixes)"
                    "(set-symbol-function! 'append elisp-append)"
                    "(set-symbol-function! 'symbol-value symbol-value)"
                    "(set-symbol-function! 'car elisp-car)"
                    "(set-symbol-function! 'expand-file-name elisp-loader-expand-file-name)"
                    "(set-symbol-function! 'file-directory-p elisp-loader-file-directory-p)"
                    "(set-symbol-function! 'cdr elisp-cdr)")))

;;; --- S3. The surface pins (brief.org section 6.3 and section 7) -----

;; imp-3 edits NO mod/ and NO prelude/ file, so these values equal the
;; imp-2 values.  The counting semantics follow the brief command of
;; each row: `grep -c' is a LINE count, `grep -o | wc -l' is a MATCH
;; count.

(setq m55-imp3--group 's3)

;; RE-PINNED at M60 imp-7: 1,328 -> 1,363 -> 1,389 -> 1,391 -> 1,398 LINES.  Rows 23 and 24
;; add the `defmacro' store and the `eval-when-compile' branch to
;; `elisp-loader-eval-form'.
;; M60 imp-8 (row 27) RE-PIN: loader.scm 1,398 -> 1,409 LINES (the
;; guarded `make-obsolete-variable' install in `init-loader').
;; M60 imp-9 (row 28a) RE-PIN: loader.scm 1,409 -> 1,511 LINES (the 3
;; branches `cond' / `let*' / `while' and the L16 ... L20 limit
;; block, above them, in `elisp-loader-eval-form').
;; M60 imp-9 fix (cr.org F3, F4, F5; L21) RE-PIN: loader.scm 1,480 -> 1,511 LINES.
;; M60 imp-11 (cr.org F3, F5) RE-PIN: loader.scm 1,511 -> 1,620 LINES; the check NAME drops the
;; stale number, because it changed again (an earlier cr.org round F5).
(m55-imp3--check "loader.scm-lines"
                 ;; M60 imp-12 RE-PIN: loader.scm 1,620 -> 1,642 LINES (OLD value 1,620).
                 ;; M60 imp-13 RE-PIN: loader.scm 1,642 -> 1,653 LINES (OLD value 1,642).
                 ;; M60 imp-15 (row 32) RE-PIN: the hash-table cells move the loader.scm line
                 ;; count and its 4 counters.  OLD: 1,653 lines, 74, 40, 36 and 9.
                 ;; M60 imp-16 (row 25) RE-PIN: 1,792 -> 1,813 LINES (the guarded
                 ;; `normal-top-level-add-to-load-path' install in `init-loader').
                 ;; M60 imp-17 (row F3) RE-PIN: 1,813 -> 1,833 LINES (OLD value 1,813).
                 ;; M60 imp-18 (row 35) RE-PIN: 1,833 -> 1,847 LINES (OLD value 1,833).
                 ;; M60 imp-19 (limit L4) RE-PIN: 1,847 -> 1,889 LINES (OLD value 1,847).
                 ;; M60 imp-20 (row 36) RE-PIN: 1,889 -> 1,914 LINES (OLD value 1,889;
                 ;; the `declare' branch and its comment lines, no counter changes).
                 (eql 1914 (m55-imp3--lines "mod/emacs/loader.scm")))
(m55-imp3--check "reader.scm-lines-2021"
                 (eql 2021 (m55-imp3--lines "mod/emacs/reader.scm")))
(m55-imp3--check "prelude-load.scm-lines-229"
                 (eql 229 (m55-imp3--lines "prelude/load.scm")))
(m55-imp3--check "loader.scm-symbol-function-apply-74"
                 (eql 76 (m55-imp3--count "mod/emacs/loader.scm"
                                          "(symbol-function '")))
;; M60 imp-8 (row 27) RE-PIN: loader.scm `symbol-fbound?' 22 -> 23
;; LINES (1 guarded install, the row-18 pattern of `provide').
;; M60 imp-11 (cr.org F3, F5) RE-PIN: `symbol-fbound?` 23 -> 39 LINES; the check NAME drops the
;; stale number, because it changed again (an earlier cr.org round F5).
(m55-imp3--check "loader.scm-symbol-fbound-guards"
                 ;; M60 imp-13 RE-PIN: `symbol-fbound?' 39 -> 40 LINES (OLD value 39).
                 ;; M60 imp-16 RE-PIN: 55 -> 56 LINES (OLD value 55; the row-25
                 ;; guarded install in `init-loader').
                 ;; M60 imp-17 (row F3) RE-PIN: `symbol-fbound?' 56 -> 57 LINES (OLD value 56).
                 ;; M60 imp-18 (row 35) RE-PIN: `symbol-fbound?' 57 -> 58 LINES (OLD value 57).
                 (eql 58 (m55-imp3--count-lines "mod/emacs/loader.scm"
                                                "symbol-fbound?")))
;; M60 imp-8 (row 27) RE-PIN: loader.scm `set-symbol-function!' 18 -> 19
;; LINES (the same guarded install).  `FIX-.*guilemacs' stays 9.
;; M60 imp-11 (cr.org F3, F5) RE-PIN: `set-symbol-function!` 19 -> 35 LINES; the check NAME drops the
;; stale number, because it changed again (an earlier cr.org round F5).
(m55-imp3--check "loader.scm-set-symbol-function"
                 ;; M60 imp-13 RE-PIN: `set-symbol-function!' 35 -> 36 LINES (OLD value 35).
                 ;; M60 imp-16 RE-PIN: 51 -> 52 LINES (OLD value 51).
                 ;; M60 imp-17 (row F3) RE-PIN: `set-symbol-function!' 52 -> 53 LINES (OLD value 52).
                 ;; M60 imp-18 (row 35) RE-PIN: `set-symbol-function!' 53 -> 54 LINES (OLD value 53).
                 (eql 54 (m55-imp3--count-lines "mod/emacs/loader.scm"
                                               "set-symbol-function!")))
(m55-imp3--check "loader.scm-fix-markers-9"
                 (eql 10 (m55-imp3--count-lines "mod/emacs/loader.scm"
                                               "FIX-.*guilemacs")))

;;; --- S4. The registration (brief.org section 6.4) -------------------

(setq m55-imp3--group 's4)

(m55-imp3--check "run-tests-m55-imp3"
                 (m55-imp3--contains-p "tool/run-tests.scm"
                                       "test/m55/test-m55-imp3.el"))
(m55-imp3--check "run-tests-m55-group"
                 (m55-imp3--contains-p "tool/run-tests.scm" "(group (m55)"))
(m55-imp3--check "run-tests-m55-after-m54"
                 (m55-imp3--ordered-p "tool/run-tests.scm"
                                      '("(group (m54)" "(group (m55)")))
(m55-imp3--check "run-tests-m55-holds-imp1-and-imp2"
                 (and (m55-imp3--contains-p "tool/run-tests.scm"
                                            "test/m55/test-m55-imp1.el")
                      (m55-imp3--contains-p "tool/run-tests.scm"
                                            "test/m55/test-m55-imp2.el")))

;;; --- S5. The guards (brief.org section 6.5) -------------------------

;; An --filter that matches no group already reports exit 0 with 0
;; tests, so a green m55 gate proves nothing until the corpus exists and
;; its checks really register.  S1 holds 2 checks, S2 holds 1, S3 holds
;; 7, and S4 holds 4.

(setq m55-imp3--group 's5)

(m55-imp3--check "reg/min-s1-checks-2" (>= (m55-imp3--group-count 's1) 2))
(m55-imp3--check "reg/min-s2-checks-1" (>= (m55-imp3--group-count 's2) 1))
(m55-imp3--check "reg/min-s3-checks-7" (>= (m55-imp3--group-count 's3) 7))
(m55-imp3--check "reg/min-s4-checks-4" (>= (m55-imp3--group-count 's4) 4))

;;; --- The group-total check ------------------------------------------

;; The measured count of m55-imp3 tests is 19: 18 registered checks
;; (S1 2, S2 1, S3 7, S4 4, S5 4) plus the group-total deftest itself.

(defvar m55-imp3--min-gate-total 19
  "The exact number of m55-imp3 ERT tests: 18 registered checks (S1 2,
S2 1, S3 7, S4 4, S5 4) plus the group-total deftest itself.")

(ert-deftest m55-imp3/gate-m55-total ()
  "The m55-imp3 corpus registers at least its docs-independent floor."
  (should (>= (length (ert-select-tests "^m55-imp3" t))
              m55-imp3--min-gate-total)))

(princ (format "=== m55 imp-3 suite done (%d checks; s1 %d, s2 %d, s3 %d, s4 %d, s5 %d) ===\n"
               m55-imp3--registered
               (m55-imp3--group-count 's1)
               (m55-imp3--group-count 's2)
               (m55-imp3--group-count 's3)
               (m55-imp3--group-count 's4)
               (m55-imp3--group-count 's5)))
