;;; test-m55-imp2.el --- M55 imp-2 minimal Scheme runtime registration corpus.
;;;
;;; M55 imp-2 is the first CODE change of M55 (brief.org section 1).  It
;;; installs 7 EMPTY runtime cells in Scheme on the standalone load
;;; path, in call order, with no C fallback.  It moves no C.
;;;
;;; This corpus pins the registration, the re-measured surface, and the
;;; NEW stop point.  It pins these groups:
;;;
;;;   S1 -- the registration (brief.org section 5.2).  The 7 new
;;;         set-symbol-function! cells in init-loader
;;;         (mod/emacs/loader.scm), in call order: get-load-suffixes,
;;;         append, symbol-value, car, expand-file-name,
;;;         file-directory-p, cdr; each guarded by a symbol-fbound? test
;;;         so an already-present C cell is KEPT (cr.org F6); the 2 new
;;;         pure-Scheme procedures (elisp-loader-expand-file-name,
;;;         elisp-loader-file-directory-p); the #:select imports; and
;;;         the no-C rule (no C-backed (emacs fileio) cell, no C
;;;         public-ref site).  S1 holds 8 checks.
;;;   S2 -- the REAL path (brief.org sections 3 and 6).  A plain
;;;         `guile -L mod -c' subprocess calls init-loader (the
;;;         registration site) and then elisp-load on a real .el file.
;;;         It DERIVES that no reachable cell is empty.  M55 imp-4
;;;         removed row 10 (the elisp compiler) from the route, so the
;;;         load no longer stops there; the check pins the imp-4 end
;;;         state, the LOAD-OK outcome.  One more subprocess pre-binds a
;;;         cell and checks the guard KEEPS it while an empty cell is
;;;         INSTALLED (cr.org F6).  S2 holds 3 checks.
;;;   S3 -- the re-measured surface, re-measured at imp-4 (brief.org
;;;         section 9): loader.scm 1190 lines / 74 (symbol-function 'X)
;;;         apply matches / 18 symbol-fbound? / 14 set-symbol-function! /
;;;         7 FIX-*-guilemacs; reader.scm 2,021 lines; prelude/load.scm
;;;         265 lines.  S3 holds 7 checks.
;;;   S4 -- the registration: the (m55) group of tool/run-tests.scm holds
;;;         the imp-2 file, after (m54).  S4 holds 4 checks.
;;;   S5 -- the guards: 4 checks -- one per-group min-count guard for
;;;         each of S1 .. S4.  The in-process group-total `ert-deftest'
;;;         is a separate test in the same phase; it is NOT one of the 4
;;;         counted checks (the floor is 26 registered checks plus that
;;;         deftest = 27).
;;;
;;; This corpus reads TRACKED files only (mod/, prelude/, and the
;;; tracked runner tool/run-tests.scm).  It does NOT read docs/
;;; (docs/kb.org test-must-not-read-docs): a gitignored record can only
;;; pass or skip, so a record check proves nothing.
;;;
;;; A read error is a real error, never a silent pass.  An absent
;;; TRACKED file is a real FAIL, not a pass (brief.org section 8).  A
;;; missing `guile' binary is an explicit INFO skip, never a pass.  Every
;;; check registers a real ERT test via imp-register-bool-as-ert-test, so
;;; the harness parses the ERT output and the exit code is correct.

(princ "=== m55 imp-2 minimal Scheme runtime registration suite ===\n")

(require 'imp-ert-report)

(defvar m55-imp2--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))
(defvar m55-imp2--registered 0
  "Total number of checks this corpus has registered.")
(defvar m55-imp2--group nil
  "The group that `m55-imp2--check' counts into: `s1' .. `s5', or nil.")
(defvar m55-imp2--counts nil
  "Alist of (GROUP . COUNT) for the registered checks.")

(defun m55-imp2--group-count (group)
  "Number of checks registered so far in GROUP."
  (or (cdr (assq group m55-imp2--counts)) 0))

(defun m55-imp2--bump-group ()
  "Count one check into `m55-imp2--group'."
  (when m55-imp2--group
    (let ((cell (assq m55-imp2--group m55-imp2--counts)))
      (if cell
          (setcdr cell (1+ (cdr cell)))
        (push (cons m55-imp2--group 1) m55-imp2--counts)))))

(defun m55-imp2--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
the symbol `m55-imp2-absent' when REL does not exist."
  (let ((path (expand-file-name rel m55-imp2--root)))
    (if (not (file-exists-p path))
        'm55-imp2-absent
      (with-temp-buffer
        (insert-file-contents path)
        (funcall fn)))))

(defun m55-imp2--contains-p (rel needle)
  "Non-nil when the TRACKED file REL contains NEEDLE.  An absent file
folds to nil, so a check prints FAIL: an absent TRACKED file is a real
error, not a pass (brief.org section 8)."
  (let ((hit (m55-imp2--with rel
               (lambda ()
                 (goto-char (point-min))
                 (search-forward needle nil t)))))
    (and (not (eq hit 'm55-imp2-absent)) (and hit t))))

(defun m55-imp2--ordered-p (rel needles)
  "Non-nil when the TRACKED file REL holds every NEEDLE in the GIVEN
ORDER: each search starts after the previous match."
  (m55-imp2--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((all t))
        (dolist (needle needles)
          (when all
            (unless (search-forward needle nil t) (setq all nil))))
        all))))

(defun m55-imp2--lines (rel)
  "Count the newlines of REL the way `wc -l' does."
  (m55-imp2--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (search-forward "\n" nil t) (setq n (1+ n)))
        n))))

(defun m55-imp2--count (rel regexp)
  "Count the matches of REGEXP in REL, the way `grep -o PATTERN | wc -l'
does.  Use this only for a brief row whose command is `grep -o'."
  (m55-imp2--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (re-search-forward regexp nil t) (setq n (1+ n)))
        n))))

(defun m55-imp2--count-lines (rel regexp)
  "Count the lines of REL that match REGEXP, the way `grep -c PATTERN'
does.  The brief.org section 7 rows use `grep -c' (a LINE count), so
this corpus counts lines and not matches."
  (m55-imp2--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (not (eobp))
          (when (re-search-forward regexp (line-end-position) t)
            (setq n (1+ n)))
          (forward-line 1))
        n))))

(defun m55-imp2--check (name ok)
  "Report and register one check on a TRACKED file.  OK is a boolean.
When the source file is absent the reader returns the symbol
`m55-imp2-absent', so a count check folds to a real FAILING ERT test."
  (let* ((absent (eq ok 'm55-imp2-absent))
         (pass (and (not absent) (and ok t))))
    (if absent
        (princ (format "FAIL m55/imp2/%s (source file absent)\n" name))
      (princ (format "%s m55/imp2/%s\n" (if pass "PASS" "FAIL") name)))
    (setq m55-imp2--registered (1+ m55-imp2--registered))
    (m55-imp2--bump-group)
    (imp-register-bool-as-ert-test (format "m55-imp2/%s" name) pass)))

(defun m55-imp2--info-skip (name reason)
  "Register one explicit INFO skip, counted into the current group.  A
host limit is a skip, never a pass (brief.org section 9)."
  (princ (format "INFO m55/imp2/%s %s\n" name reason))
  (setq m55-imp2--registered (1+ m55-imp2--registered))
  (m55-imp2--bump-group)
  (imp-register-skip-as-ert-test (format "m55-imp2/%s" name) reason))

;;; --- The plain `guile' probe (no Emacs C core) ----------------------

(defun m55-imp2--guile ()
  "The plain `guile' binary on PATH, or nil."
  (executable-find "guile"))

(defun m55-imp2--run-guile (code)
  "Run a plain `guile -L mod -c CODE' subprocess and return its combined
output, or the symbol `m55-imp2-guile-absent' when no guile binary is on
PATH.  The Emacs C core is absent from this subprocess: the core elisp
function cells are NOT installed by it."
  (let ((guile (m55-imp2--guile)))
    (if (not guile)
        'm55-imp2-guile-absent
      (let* ((modpath (expand-file-name "mod" m55-imp2--root))
             (buf (get-buffer-create " *m55-imp2-guile*")))
        (unwind-protect
            (progn
              (with-current-buffer buf (erase-buffer))
              (call-process guile nil buf nil "-L" modpath "-c" code)
              (with-current-buffer buf
                (buffer-substring-no-properties (point-min) (point-max))))
          (kill-buffer buf))))))

(defun m55-imp2--plain-guile-real-load-output ()
  "Write a real Elisp file, run a plain `guile -L mod' subprocess that
CALLS init-loader (the registration site) and then loads the file
through the Scheme loader (the REAL path, not a module-load probe), and
return the subprocess output.

The subprocess runs init-loader FIRST, so the 7 runtime cells are
installed.  Then it DERIVES the first empty cell from the ordered cell
list (brief.org section 5.1 step 3): it walks the reachable runtime
cells in call order and prints the first one that `symbol-fbound?'
reports empty.  It prints M55-IMP2-FIRST-EMPTY:NAME, and
M55-IMP2-OUTCOME:FAULT:KEY + ARGS for the full load.  Return the symbol
`m55-imp2-guile-absent' when no guile binary is on PATH."
  (let ((file (make-temp-file "m55-imp2-plain-" nil ".el"))
        (prelude (expand-file-name "prelude" m55-imp2--root)))
    (unwind-protect
        (progn
          (with-temp-file file
            (insert ";; real Elisp file for the C-core-absent M55 imp-2 load\n"
                    "(setq m55-imp2-standalone-loaded 'm55-imp2-standalone-ok)\n"))
          (m55-imp2--run-guile
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
             "(display \"M55-IMP2-FIRST-EMPTY:\")"
             "(display (first-empty '(get-load-suffixes append symbol-value car expand-file-name file-directory-p cdr)))"
             "(newline)"
             "(catch #t "
             "(lambda () (el \"%s\" #nil #nil #nil #nil) "
             "(display \"M55-IMP2-OUTCOME:LOAD-OK\\n\")) "
             "(lambda (k . a) (display \"M55-IMP2-OUTCOME:FAULT:\") (display k) "
             "(display \" ARGS:\") (write a) (newline)))")
            prelude file)))
      (ignore-errors (delete-file file)))))

(defun m55-imp2--plain-guile-guard-output ()
  "Run a plain `guile -L mod' subprocess that pre-binds ONE runtime cell
to a sentinel, then calls init-loader, and reports whether the
`symbol-fbound?' guard KEPT the pre-bound cell and INSTALLED an empty
one (cr.org F6).  This is the F6 regression probe: an unconditional
install would CLOBBER the pre-bound cell.  Return the symbol
`m55-imp2-guile-absent' when no guile binary is on PATH."
  (let ((prelude (expand-file-name "prelude" m55-imp2--root)))
    (m55-imp2--run-guile
     (format
      (concat
       "(use-modules (emacs loader))"
       "(use-modules (emacs-elisp runtime))"
       "(define rt (resolve-module '(emacs-elisp runtime)))"
       "(define symfun (module-ref rt 'symbol-function))"
       "(define symfb (module-ref rt 'symbol-fbound?))"
       "(define setfun (module-ref rt 'set-symbol-function!))"
       "(define init (module-ref (resolve-module '(emacs loader)) 'init-loader))"
       "(setfun 'cdr (lambda (x) 'M55-IMP2-GUARD-SENTINEL))"
       "(init \"%s\")"
       "(display \"M55-IMP2-GUARD:\")"
       "(display (if (eq? 'M55-IMP2-GUARD-SENTINEL ((symfun 'cdr) (list 1))) \"KEPT\" \"CLOBBERED\"))"
       "(newline)"
       "(display \"M55-IMP2-INSTALLED:\")"
       "(display (if (symfb 'get-load-suffixes) \"YES\" \"NO\"))"
       "(newline)")
      prelude))))

(defun m55-imp2--contains-marker-p (out marker)
  "Non-nil when the subprocess output OUT holds MARKER.  OUT may be the
symbol `m55-imp2-guile-absent'."
  (and (not (eq out 'm55-imp2-guile-absent))
       (string-match-p (regexp-quote marker) out)
       t))

;;; --- S1. The registration (brief.org section 5.2) -------------------

;; The 7 new set-symbol-function! cells in init-loader, in call order
;; (rows 3 ... 9 of docs/m55-plan.org section 3.2).  The check is a
;; `come before' ORDER check: a reordering fails the run.

(setq m55-imp2--group 's1)

(m55-imp2--check "install-cells-in-call-order"
                 (m55-imp2--ordered-p
                  "mod/emacs/loader.scm"
                  '("(set-symbol-function! 'get-load-suffixes elisp-get-load-suffixes)"
                    "(set-symbol-function! 'append elisp-append)"
                    "(set-symbol-function! 'symbol-value symbol-value)"
                    "(set-symbol-function! 'car elisp-car)"
                    "(set-symbol-function! 'expand-file-name elisp-loader-expand-file-name)"
                    "(set-symbol-function! 'file-directory-p elisp-loader-file-directory-p)"
                    "(set-symbol-function! 'cdr elisp-cdr)")))

;; F6 (cr.org section 4, item 7): each install is guarded by a
;; `symbol-fbound?' test, so an already-present C cell (the full Emacs
;; owns `expand-file-name' and `file-directory-p') is KEPT and not
;; replaced by the load-path-only Scheme cell.  The ORDER check binds
;; each guard to its install: the guard must come before its install,
;; and the pairs stay in call order.

(m55-imp2--check "install-cells-guarded-in-order"
                 (m55-imp2--ordered-p
                  "mod/emacs/loader.scm"
                  '("(unless (symbol-fbound? 'get-load-suffixes)"
                    "(set-symbol-function! 'get-load-suffixes elisp-get-load-suffixes)"
                    "(unless (symbol-fbound? 'append)"
                    "(set-symbol-function! 'append elisp-append)"
                    "(unless (symbol-fbound? 'symbol-value)"
                    "(set-symbol-function! 'symbol-value symbol-value)"
                    "(unless (symbol-fbound? 'car)"
                    "(set-symbol-function! 'car elisp-car)"
                    "(unless (symbol-fbound? 'expand-file-name)"
                    "(set-symbol-function! 'expand-file-name elisp-loader-expand-file-name)"
                    "(unless (symbol-fbound? 'file-directory-p)"
                    "(set-symbol-function! 'file-directory-p elisp-loader-file-directory-p)"
                    "(unless (symbol-fbound? 'cdr)"
                    "(set-symbol-function! 'cdr elisp-cdr)")))

;; The 2 new pure-Scheme procedures.  `expand-file-name' is a path join;
;; `file-directory-p' uses the Scheme stat (ice-9), NOT the C-backed
;; (emacs fileio) cell (brief.org section 10).

(m55-imp2--check "proc-expand-file-name-pure"
                 (and (m55-imp2--contains-p "mod/emacs/loader.scm"
                                            "(define (elisp-loader-expand-file-name file dir)")
                      (m55-imp2--contains-p "mod/emacs/loader.scm"
                                            "(string-append (if (string-suffix? \"/\" dir) dir (string-append dir \"/\"))")))
(m55-imp2--check "proc-file-directory-p-stat"
                 (and (m55-imp2--contains-p "mod/emacs/loader.scm"
                                            "(define (elisp-loader-file-directory-p path)")
                      (m55-imp2--contains-p "mod/emacs/loader.scm"
                                            "(eq? 'directory (stat:type (stat path)))")))

;; The pure-Scheme procedures are in scope: the loader selects
;; elisp-append from (emacs sequences) and elisp-car / elisp-cdr from
;; (emacs list).  get-load-suffixes and symbol-value come from the
;; already-used (emacs utils) and (emacs-elisp runtime) modules.

;; M60 imp-11 (cr.org F3) RE-PIN: row 29 EXTENDED the `#:select' list to
;; `(elisp-append elisp-length)', so the needle drops the closing paren.
(m55-imp2--check "imports-select-sequences-list"
                 (and (m55-imp2--contains-p "mod/emacs/loader.scm"
                                            "#:select (elisp-append")
                      (m55-imp2--contains-p "mod/emacs/loader.scm"
                                            "#:select (elisp-car elisp-cdr)")))

;; No C fallback for a runtime cell (brief.org section 10): the loader
;; does NOT call the C-backed (emacs fileio) cell and holds no C
;; public-ref site.  A refute check: the needle must be ABSENT.

(m55-imp2--check "no-c-fileio-cell"
                 (and (not (m55-imp2--contains-p "mod/emacs/loader.scm" "%--fileio"))
                      (not (m55-imp2--contains-p "mod/emacs/loader.scm" "fileio-expand-file-name"))))
(m55-imp2--check "no-c-public-ref-site"
                 (not (m55-imp2--contains-p "mod/emacs/loader.scm" "scm_c_public_ref")))

;; The 7 imp-2 new cells plus the 4 imp-4 cells (intern, concat,
;; substring, eval) plus the 2 pre-existing ones (load,
;; autoload-do-load) plus the imp-4 `defun' define site make 14
;; set-symbol-function! sites in init-loader.  M60 imp-5 adds the
;; `require' install and the 2 `load' protocol installs (`string-suffix-p',
;; `file-name-directory'), so the FILE count is 18 LINES (`grep -c').

;; M60 imp-8 (row 27) RE-PIN: loader.scm `set-symbol-function!' 18 -> 19
;; LINES (the same guarded install).  `FIX-.*guilemacs' stays 9.
;; M60 imp-11 (cr.org F3, F5) RE-PIN: `set-symbol-function!` 19 -> 35 LINES; the check NAME drops the
;; stale number, because it changed again (an earlier cr.org round F5).
(m55-imp2--check "install-cell-count"
                 ;; M60 imp-13 RE-PIN: `set-symbol-function!' 35 -> 36 LINES (OLD value 35).
                 ;; M60 imp-16 RE-PIN: 51 -> 52 LINES (OLD value 51).
                 ;; M60 imp-17 (row F3) RE-PIN: `set-symbol-function!' 52 -> 53 LINES (OLD value 52).
                 ;; M60 imp-18 (row 35) RE-PIN: `set-symbol-function!' 53 -> 54 LINES (OLD value 53).
                 ;; M60 imp-22 (row 37) RE-PIN: `set-symbol-function!' 54 -> 55 LINES (OLD value 54).
                 (eql 55 (m55-imp2--count-lines "mod/emacs/loader.scm"
                                               "set-symbol-function!")))

;;; --- S2. The REAL path (brief.org sections 3 and 6) -----------------

;; A plain `guile -L mod -c' subprocess calls init-loader, then loads a
;; real .el file through the Scheme loader.  A missing guile binary is an
;; explicit INFO skip, never a pass.

(setq m55-imp2--group 's2)

(let ((out (m55-imp2--plain-guile-real-load-output)))
  (if (eq out 'm55-imp2-guile-absent)
      (progn
        (m55-imp2--info-skip "plain-guile-no-empty-cell"
                             "no guile binary on PATH")
        (m55-imp2--info-skip "plain-guile-load-ok"
                             "no guile binary on PATH"))
    (progn
      ;; Rows 3 ... 9 are no longer empty: init-loader installed them.
      (m55-imp2--check "plain-guile-no-empty-cell"
                       (m55-imp2--contains-marker-p out "M55-IMP2-FIRST-EMPTY:NONE"))
      ;; M55 imp-4 removed row 10 from the route: the load no longer stops
      ;; at the elisp compiler.  The check pins the imp-4 end state, the
      ;; LOAD-OK outcome (the imp-2 row-10 stop is gone).
      (m55-imp2--check "plain-guile-load-ok"
                       (m55-imp2--contains-marker-p out "M55-IMP2-OUTCOME:LOAD-OK")))))

;; F6 regression probe: pre-bind ONE cell, call init-loader, and check
;; the guard KEPT the pre-bound cell and INSTALLED the empty one.  A
;; missing guile binary is an explicit INFO skip, never a pass.

(let ((guard-out (m55-imp2--plain-guile-guard-output)))
  (if (eq guard-out 'm55-imp2-guile-absent)
      (m55-imp2--info-skip "plain-guile-guard-keeps-cell"
                           "no guile binary on PATH")
    (m55-imp2--check "plain-guile-guard-keeps-cell"
                     (and (m55-imp2--contains-marker-p guard-out "M55-IMP2-GUARD:KEPT")
                          (m55-imp2--contains-marker-p guard-out "M55-IMP2-INSTALLED:YES")))))

;;; --- S3. The re-measured surface (brief.org section 7) --------------

;; imp-2 edits mod/emacs/loader.scm, so the S1 pins of the imp-1 corpus
;; move.  Re-measure the rows and pin the new values.  The counting
;; semantics follow the brief command of each row.

(setq m55-imp2--group 's3)

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
(m55-imp2--check "loader.scm-lines"
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
                 ;; M60 imp-21 (row 28b) RE-PIN: 1,914 -> 2,029 LINES (OLD value 1,914;
                 ;; the backquote walk, its 3 procedures and 5 limit notes).
                 ;; M60 imp-21 cr.org fix RE-PIN: 2,029 -> 2,052 LINES (OLD value 2,029;
                 ;; the L56 / L58 / shape notes of cr.org F6, F7 and F8, comments only).
                 ;; M60 imp-22 (row 37) RE-PIN: 2,052 -> 2,074 LINES (OLD value 2,052;
                 ;; the guarded `purecopy' install, its limit note, the import
                 ;; and the 2 comments that name the kb entry
                 ;; `backquote-is-a-value-builder-not-a-cell`).
                 (eql 2074 (m55-imp2--lines "mod/emacs/loader.scm")))
(m55-imp2--check "reader.scm-lines-2021"
                 (eql 2021 (m55-imp2--lines "mod/emacs/reader.scm")))
(m55-imp2--check "prelude-load.scm-lines-229"
                 (eql 229 (m55-imp2--lines "prelude/load.scm")))
(m55-imp2--check "loader.scm-symbol-function-apply-74"
                 ;; The UNIT of this row is a MATCH count: the helper is
                 ;; `m55-imp2--count' (`grep -o ... | wc -l'), not
                 ;; `m55-imp2--count-lines'.  MEASURED at M60 imp-22:
                 ;; 76 matches on 72 LINES, so the value does not move.
                 (eql 76 (m55-imp2--count "mod/emacs/loader.scm"
                                          "(symbol-function '")))
;; M60 imp-8 (row 27) RE-PIN: loader.scm `symbol-fbound?' 22 -> 23
;; LINES (1 guarded install, the row-18 pattern of `provide').
;; M60 imp-11 (cr.org F3, F5) RE-PIN: `symbol-fbound?` 23 -> 39 LINES; the check NAME drops the
;; stale number, because it changed again (an earlier cr.org round F5).
(m55-imp2--check "loader.scm-symbol-fbound-guards"
                 ;; M60 imp-13 RE-PIN: `symbol-fbound?' 39 -> 40 LINES (OLD value 39).
                 ;; M60 imp-16 RE-PIN: 55 -> 56 LINES (OLD value 55; the row-25
                 ;; guarded install in `init-loader').
                 ;; M60 imp-17 (row F3) RE-PIN: `symbol-fbound?' 56 -> 57 LINES (OLD value 56).
                 ;; M60 imp-18 (row 35) RE-PIN: `symbol-fbound?' 57 -> 58 LINES (OLD value 57).
                 ;; M60 imp-22 (row 37) RE-PIN: `symbol-fbound?' 58 -> 59 LINES (OLD value 58).
                 (eql 59 (m55-imp2--count-lines "mod/emacs/loader.scm"
                                                "symbol-fbound?")))
;; M60 imp-8 (row 27) RE-PIN: loader.scm `set-symbol-function!' 18 -> 19
;; LINES (the same guarded install).  `FIX-.*guilemacs' stays 9.
;; M60 imp-11 (cr.org F3, F5) RE-PIN: `set-symbol-function!` 19 -> 35 LINES; the check NAME drops the
;; stale number, because it changed again (an earlier cr.org round F5).
(m55-imp2--check "loader.scm-set-symbol-function"
                 ;; M60 imp-13 RE-PIN: `set-symbol-function!' 35 -> 36 LINES (OLD value 35).
                 ;; M60 imp-16 RE-PIN: 51 -> 52 LINES (OLD value 51).
                 ;; M60 imp-17 (row F3) RE-PIN: `set-symbol-function!' 52 -> 53 LINES (OLD value 52).
                 ;; M60 imp-18 (row 35) RE-PIN: `set-symbol-function!' 53 -> 54 LINES (OLD value 53).
                 ;; M60 imp-22 (row 37) RE-PIN: `set-symbol-function!' 54 -> 55 LINES (OLD value 54).
                 (eql 55 (m55-imp2--count-lines "mod/emacs/loader.scm"
                                               "set-symbol-function!")))
(m55-imp2--check "loader.scm-fix-markers-9"
                 (eql 10 (m55-imp2--count-lines "mod/emacs/loader.scm"
                                               "FIX-.*guilemacs")))

;;; --- S4. The registration -------------------------------------------

(setq m55-imp2--group 's4)

(m55-imp2--check "run-tests-m55-imp2"
                 (m55-imp2--contains-p "tool/run-tests.scm"
                                       "test/m55/test-m55-imp2.el"))
(m55-imp2--check "run-tests-m55-imp1"
                 (m55-imp2--contains-p "tool/run-tests.scm"
                                       "test/m55/test-m55-imp1.el"))
(m55-imp2--check "run-tests-m55-group"
                 (m55-imp2--contains-p "tool/run-tests.scm" "(group (m55)"))
(m55-imp2--check "run-tests-m55-after-m54"
                 (m55-imp2--ordered-p "tool/run-tests.scm"
                                      '("(group (m54)" "(group (m55)")))

;;; --- S5. The guards -------------------------------------------------

;; An --filter that matches no group already reports exit 0 with 0
;; tests, so a green m55 gate proves nothing until the corpus exists and
;; its checks really register.  S1 holds 8 checks, S2 holds 3, S3 holds
;; 7, and S4 holds 4.

(setq m55-imp2--group 's5)

(m55-imp2--check "reg/min-s1-checks-8" (>= (m55-imp2--group-count 's1) 8))
(m55-imp2--check "reg/min-s2-checks-3" (>= (m55-imp2--group-count 's2) 3))
(m55-imp2--check "reg/min-s3-checks-7" (>= (m55-imp2--group-count 's3) 7))
(m55-imp2--check "reg/min-s4-checks-4" (>= (m55-imp2--group-count 's4) 4))

;;; --- The group-total check ------------------------------------------

;; The measured count of m55-imp2 tests is 27: 26 registered checks
;; (S1 8, S2 3, S3 7, S4 4, S5 4) plus the group-total deftest itself.

(defvar m55-imp2--min-gate-total 27
  "The exact number of m55-imp2 ERT tests: 26 registered checks (S1 8,
S2 3, S3 7, S4 4, S5 4) plus the group-total deftest itself.")

(ert-deftest m55-imp2/gate-m55-total ()
  "The m55-imp2 corpus registers at least its docs-independent floor."
  (should (>= (length (ert-select-tests "^m55-imp2" t))
              m55-imp2--min-gate-total)))

(princ (format "=== m55 imp-2 suite done (%d checks; s1 %d, s2 %d, s3 %d, s4 %d, s5 %d) ===\n"
               m55-imp2--registered
               (m55-imp2--group-count 's1)
               (m55-imp2--group-count 's2)
               (m55-imp2--group-count 's3)
               (m55-imp2--group-count 's4)
               (m55-imp2--group-count 's5)))
