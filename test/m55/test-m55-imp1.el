;;; test-m55-imp1.el --- M55 imp-1 standalone loader runtime registration audit corpus.
;;;
;;; M55 imp-1 is the standalone loader runtime registration AUDIT
;;; (brief.org section 1).  It is docs only: the C delta is 0 and the
;;; Scheme delta is 0.  It traces the runtime function cells on the REAL
;;; plain-`guile' load path and records the A1 / A2 verdict
;;; (docs/m55-plan.org).
;;;
;;; This corpus pins the measured surface, the ordered cell map, the
;;; registration site, and the registration in the tree, so a stale
;;; number or a missing registration fails the run.
;;;
;;; It pins these groups:
;;;
;;;   S1 -- the re-measured surface of brief.org section 4, re-measured
;;;         at imp-2 when it edits the loader.  S1 holds 9
;;;         checks: mod/emacs/loader.scm 1187 lines / 74 (symbol-function
;;;         'X) apply sites / 18 symbol-fbound? guards / 14
;;;         set-symbol-function! sites / 7 FIX-*-guilemacs markers;
;;;         mod/emacs/reader.scm 2,021 lines; prelude/load.scm 265 lines
;;;         / 70 (use-modules ...) lines / 31 (init-...-registrations)
;;;         calls.
;;;   S2 -- the cell map (brief.org section 5).  The loader POLICY cells
;;;         (`length', `find-file-name-handler'), the reachable runtime
;;;         cells in call order (`get-load-suffixes', `append',
;;;         `symbol-value', `car', `expand-file-name',
;;;         `file-directory-p', `cdr'), the reached-from procedures, the
;;;         REAL path probe (a plain `guile -L mod' subprocess loads a
;;;         real .el file: it derives the first empty cell from the
;;;         ordered list -- `get-load-suffixes' -- and the raise is
;;;         `wrong-type-arg'), and the deep trace (supply the cells with
;;;         Scheme stubs, repeat: the path advances to the elisp
;;;         compiler and raises `misc-error').  S2 holds 7 checks.
;;;   S3 -- the registration site (brief.org section 5.4).  The install
;;;         site prelude/load.scm and the 2 loader
;;;         set-symbol-function! cells (`load' and `autoload-do-load').
;;;         S3 holds 4 checks.
;;;   S4 -- the registration: the corpus is registered in the (m55)
;;;         group of tool/run-tests.scm, after the (m54) group, and the
;;;         (m54) group stays present.  S4 holds 4 checks.
;;;   S5 -- the guards: 4 checks -- one per-group min-count guard for
;;;         each of S1 .. S4.  The in-process group-total `ert-deftest'
;;;         is a separate test in the same phase; it is NOT one of the 4
;;;         counted checks (the floor is 28 registered checks plus that
;;;         deftest = 29).
;;;
;;; This corpus reads TRACKED files only (mod/, prelude/, and the
;;; tracked runner tool/run-tests.scm).  It does NOT read docs/
;;; (docs/kb.org test-must-not-read-docs): a gitignored record can only
;;; pass or skip, so a record check proves nothing.
;;;
;;; A read error is a real error, never a silent pass.  An absent
;;; TRACKED file is a real FAIL, not a pass (brief.org section 4).  A
;;; missing `guile' binary is an explicit INFO skip, never a pass.  Every check
;;; registers a real ERT test via imp-register-bool-as-ert-test, so the
;;; harness parses the ERT output and the exit code is correct.

(princ "=== m55 imp-1 standalone loader runtime registration audit suite ===\n")

(require 'imp-ert-report)

(defvar m55-imp1--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))
(defvar m55-imp1--registered 0
  "Total number of checks this corpus has registered.")
(defvar m55-imp1--group nil
  "The group that `m55-imp1--check' counts into: `s1' .. `s5', or nil.")
(defvar m55-imp1--counts nil
  "Alist of (GROUP . COUNT) for the registered checks.")

(defun m55-imp1--group-count (group)
  "Number of checks registered so far in GROUP."
  (or (cdr (assq group m55-imp1--counts)) 0))

(defun m55-imp1--bump-group ()
  "Count one check into `m55-imp1--group'."
  (when m55-imp1--group
    (let ((cell (assq m55-imp1--group m55-imp1--counts)))
      (if cell
          (setcdr cell (1+ (cdr cell)))
        (push (cons m55-imp1--group 1) m55-imp1--counts)))))

(defun m55-imp1--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
the symbol `m55-imp1-absent' when REL does not exist."
  (let ((path (expand-file-name rel m55-imp1--root)))
    (if (not (file-exists-p path))
        'm55-imp1-absent
      (with-temp-buffer
        (insert-file-contents path)
        (funcall fn)))))

(defun m55-imp1--contains-p (rel needle)
  "Non-nil when the TRACKED file REL contains NEEDLE.  An absent file
folds to nil, so a check prints FAIL: an absent TRACKED file is a real
error, not a pass (brief.org section 4)."
  (let ((hit (m55-imp1--with rel
               (lambda ()
                 (goto-char (point-min))
                 (search-forward needle nil t)))))
    (and (not (eq hit 'm55-imp1-absent)) (and hit t))))

(defun m55-imp1--holds-all (rel needles)
  "Non-nil when the TRACKED file REL holds every NEEDLE.  REL is read
once, so a multi-needle check does not re-read the file per needle."
  (m55-imp1--with rel
    (lambda ()
      (let ((all t))
        (dolist (needle needles)
          (goto-char (point-min))
          (unless (search-forward needle nil t) (setq all nil)))
        all))))

(defun m55-imp1--ordered-p (rel needles)
  "Non-nil when the TRACKED file REL holds every NEEDLE in the GIVEN
ORDER: each search starts after the previous match."
  (m55-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((all t))
        (dolist (needle needles)
          (when all
            (unless (search-forward needle nil t) (setq all nil))))
        all))))

(defun m55-imp1--lines (rel)
  "Count the newlines of REL the way `wc -l' does."
  (m55-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (search-forward "\n" nil t) (setq n (1+ n)))
        n))))

(defun m55-imp1--count (rel regexp)
  "Count the matches of REGEXP in REL, the way `grep -o PATTERN | wc -l'
does.  Use this only for a brief row whose command is `grep -o'."
  (m55-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (re-search-forward regexp nil t) (setq n (1+ n)))
        n))))

(defun m55-imp1--count-lines (rel regexp)
  "Count the lines of REL that match REGEXP, the way `grep -c PATTERN'
does.  The brief.org section 4 rows 5 .. 9 use `grep -c' (a LINE count),
so this corpus counts lines and not matches: one line with two matches
counts once, as `grep -c' reports it (cr.org F5)."
  (m55-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (not (eobp))
          (when (re-search-forward regexp (line-end-position) t)
            (setq n (1+ n)))
          (forward-line 1))
        n))))

(defun m55-imp1--check (name ok)
  "Report and register one check on a TRACKED file.  OK is a boolean.
When the source file is absent the reader returns the symbol
`m55-imp1-absent', so a count check folds to a real FAILING ERT test."
  (let* ((absent (eq ok 'm55-imp1-absent))
         (pass (and (not absent) (and ok t))))
    (if absent
        (princ (format "FAIL m55/imp1/%s (source file absent)\n" name))
      (princ (format "%s m55/imp1/%s\n" (if pass "PASS" "FAIL") name)))
    (setq m55-imp1--registered (1+ m55-imp1--registered))
    (m55-imp1--bump-group)
    (imp-register-bool-as-ert-test (format "m55-imp1/%s" name) pass)))

(defun m55-imp1--info-skip (name reason)
  "Register one explicit INFO skip, counted into the current group.  A
host limit is a skip, never a pass (brief.org section 11)."
  (princ (format "INFO m55/imp1/%s %s\n" name reason))
  (setq m55-imp1--registered (1+ m55-imp1--registered))
  (m55-imp1--bump-group)
  (imp-register-skip-as-ert-test (format "m55-imp1/%s" name) reason))

;;; --- The plain `guile' probe (no Emacs C core) ----------------------

(defun m55-imp1--guile ()
  "The plain `guile' binary on PATH, or nil."
  (executable-find "guile"))

(defun m55-imp1--run-guile (code)
  "Run a plain `guile -L mod -c CODE' subprocess and return its stdout
and stderr, or the symbol `m55-imp1-guile-absent' when no guile binary
is on PATH.  The Emacs C core is absent from this subprocess: the core
elisp function cells are NOT installed."
  (let ((guile (m55-imp1--guile)))
    (if (not guile)
        'm55-imp1-guile-absent
      (let* ((modpath (expand-file-name "mod" m55-imp1--root))
             (buf (get-buffer-create " *m55-imp1-guile*")))
        (unwind-protect
            (progn
              (with-current-buffer buf (erase-buffer))
              (call-process guile nil buf nil "-L" modpath "-c" code)
              (with-current-buffer buf
                (buffer-substring-no-properties (point-min) (point-max))))
          (kill-buffer buf))))))

(defun m55-imp1--plain-guile-real-load-output ()
  "Write a real Elisp file, run a plain `guile -L mod' subprocess that
loads it through the Scheme loader (the REAL path, not a module-load
probe), and return the subprocess output.

The subprocess DERIVES the first empty cell from the ordered cell list
(brief.org section 5.1 step 3): it walks the reachable runtime cells in
call order and prints the first one that `symbol-fbound?' reports empty.
It prints M55-FIRST-CELL:NAME for that cell, and M55-OUTCOME:FAULT:KEY
for the full load.  Return the symbol `m55-imp1-guile-absent' when no
guile binary is on PATH."
  (let ((file (make-temp-file "m55-imp1-plain-" nil ".el")))
    (unwind-protect
        (progn
          (with-temp-file file
            (insert ";; real Elisp file for the C-core-absent M55 imp-1 load\n"
                    "(setq m55-imp1-standalone-loaded 'm55-imp1-standalone-ok)\n"))
          (m55-imp1--run-guile
           (format
            (concat
             "(use-modules (emacs loader))"
             "(use-modules (emacs-elisp runtime))"
             "(define rp (resolve-module '(emacs loader)))"
             "(define (ref n) (module-ref rp n))"
             "(define (first-empty cells)"
             "  (cond ((null? cells) \"NONE\")"
             "        ((symbol-fbound? (car cells)) (first-empty (cdr cells)))"
             "        (else (symbol->string (car cells)))))"
             "(display \"M55-FIRST-CELL:\")"
             "(display (first-empty '(get-load-suffixes append symbol-value car expand-file-name file-directory-p cdr)))"
             "(newline)"
             "(catch #t "
             "(lambda () ((ref 'elisp-load) \"%s\" #nil #nil #nil #nil) "
             "(display \"M55-OUTCOME:LOAD-OK\\n\")) "
             "(lambda (k . a) (display \"M55-OUTCOME:FAULT:\") (display k) (newline)))")
            file)))
      (ignore-errors (delete-file file)))))

(defun m55-imp1--plain-guile-deep-trace-output ()
  "Write a real Elisp file, then run a plain `guile -L mod' subprocess
that supplies the reachable runtime cells (rows 3 .. 9) with tolerant
Scheme stubs and repeats the REAL load.  When rows 3 .. 9 are the whole
pre-compiler set, the path advances PAST them to row 10 (the elisp
compiler) and the load raises `misc-error \"no such language ~S\"'
(emacs-elisp).  The probe prints the raised key AND its arguments, so
the caller can assert the LANGUAGE NAME and not only the generic key.

This confirms the recorded A2 blocker by measurement: it re-runs the
brief.org section 5.1 step 4 trace.  Return the symbol
`m55-imp1-guile-absent' when no guile binary is on PATH."
  (let ((file (make-temp-file "m55-imp1-deep-" nil ".el")))
    (unwind-protect
        (progn
          (with-temp-file file
            (insert ";; real Elisp file for the M55 imp-1 deep trace\n"))
          (m55-imp1--run-guile
           (format
            (concat
             "(use-modules (emacs loader))"
             "(use-modules (emacs-elisp runtime))"
             "(define rp (resolve-module '(emacs loader)))"
             "(define (ref n) (module-ref rp n))"
             "(set-symbol-function! 'get-load-suffixes (lambda () (list \".el\")))"
             "(set-symbol-function! 'append (lambda a (apply append a)))"
             "(set-symbol-function! 'symbol-value (lambda (s) (list)))"
             "(set-symbol-function! 'car (lambda (x) (if (null? x) #nil (car x))))"
             "(set-symbol-function! 'cdr (lambda (x) (if (null? x) #nil (cdr x))))"
             "(set-symbol-function! 'expand-file-name"
             "  (lambda (f d) (if (and (string? d) (not (string-null? d))) (string-append d f) f)))"
             "(set-symbol-function! 'file-directory-p (lambda (f) #nil))"
             "(catch #t "
             "(lambda () ((ref 'elisp-load) \"%s\" #nil #nil #nil #nil) "
             "(display \"M55-DEEP:LOAD-OK\\n\")) "
             "(lambda (k . a) (display \"M55-DEEP:FAULT:\") (display k) "
             "(display \" ARGS:\") (write a) (newline)))")
            file)))
      (ignore-errors (delete-file file)))))

(defun m55-imp1--contains-marker-p (out marker)
  "Non-nil when the subprocess output OUT holds MARKER.  OUT may be the
symbol `m55-imp1-guile-absent'."
  (and (not (eq out 'm55-imp1-guile-absent))
       (string-match-p (regexp-quote marker) out)
       t))

;;; --- S1. The measured surface (brief.org section 4) -----------------

;; One check per stable row of brief.org section 4.  The corpus
;; S1 pins the stable rows, one check per row.  The counting semantics
;; follow the brief command of each row: row 4 uses `grep -o ... | wc -l'
;; (m55-imp1--count, a MATCH count = 74); rows 5 .. 9 use `grep -c'
;; (m55-imp1--count-lines, a LINE count).  A match count and a line count
;; agree today, but they can differ when one line holds two matches
;; (cr.org F5).

(setq m55-imp1--group 's1)

(m55-imp1--check "loader.scm-lines-1187"
                 (eql 1187 (m55-imp1--lines "mod/emacs/loader.scm")))
(m55-imp1--check "reader.scm-lines-2021"
                 (eql 2021 (m55-imp1--lines "mod/emacs/reader.scm")))
(m55-imp1--check "prelude-load.scm-lines-265"
                 (eql 265 (m55-imp1--lines "prelude/load.scm")))
(m55-imp1--check "loader.scm-symbol-function-apply-74"
                 (eql 74 (m55-imp1--count "mod/emacs/loader.scm"
                                          "(symbol-function '")))
(m55-imp1--check "loader.scm-symbol-fbound-guards-18"
                 (eql 18 (m55-imp1--count-lines "mod/emacs/loader.scm"
                                                "symbol-fbound?")))
(m55-imp1--check "prelude-load.scm-use-modules-70"
                 (eql 70 (m55-imp1--count-lines "prelude/load.scm"
                                                "^(use-modules")))
(m55-imp1--check "prelude-load.scm-init-registrations-31"
                 (eql 31 (m55-imp1--count-lines "prelude/load.scm"
                                                "^(init-.*-registrations)")))
(m55-imp1--check "loader.scm-set-symbol-function-14"
                 (eql 14 (m55-imp1--count-lines "mod/emacs/loader.scm"
                                               "set-symbol-function!")))
(m55-imp1--check "loader.scm-fix-markers-7"
                 (eql 7 (m55-imp1--count-lines "mod/emacs/loader.scm"
                                               "FIX-.*guilemacs")))

;;; --- S2. The cell map (brief.org section 5) -------------------------

;; Group (a): the loader POLICY cells.  Scheme owns the bound test and
;; the Scheme fallback (the M53 imp-2 fix).  Group (b): the reachable
;; runtime cells the (emacs ...) modules can install in Scheme.  Group
;; (c): the cells that need a C mechanism (the elisp compiler and the C
;; bootstrap's core runtime cells), recorded STAYS C in the plan.

(setq m55-imp1--group 's2)

;; The loader POLICY cells, in call order: `length' (in
;; elisp-validate-load-file), then `find-file-name-handler' (in
;; elisp-check-file-handler).
(m55-imp1--check "policy-cell-length"
                 (and (m55-imp1--contains-p "mod/emacs/loader.scm"
                                            "(symbol-fbound? 'length)")
                      (m55-imp1--contains-p "mod/emacs/loader.scm"
                                            "elisp-string-length-for-load")))
(m55-imp1--check "policy-cell-find-file-name-handler"
                 (and (m55-imp1--contains-p "mod/emacs/loader.scm"
                                            "(symbol-fbound? 'find-file-name-handler)")
                      (m55-imp1--contains-p "mod/emacs/loader.scm"
                                            "elisp-check-file-handler")))

;; The reachable runtime cells, in call order (the plain `guile' trace):
;; get-load-suffixes, append, symbol-value, car, expand-file-name,
;; file-directory-p, cdr.  Each is an empty cell in a plain `guile'
;; process.  In `search-elisp-load-path' one loop step runs car (:705),
;; expand-file-name (:706), file-directory-p (:708), then cdr (:710).
;; The check is a `come before' ORDER check (m55-imp1--ordered-p): each
;; needle must appear after the previous one in loader.scm, so a
;; reordering of the path cells fails the run.  Each needle carries the
;; call-site context, so it matches the PATH site and not an earlier
;; occurrence of the same cell (brittle line pins; a precise needle is
;; the remedy).  The exact first-empty
;; derivation (get-load-suffixes) is pinned by the S2 deep-trace probe.
(m55-imp1--check "runtime-cells-reached"
                 (m55-imp1--ordered-p
                  "mod/emacs/loader.scm"
                  '("(symbol-function 'get-load-suffixes)"
                    "(symbol-function 'append)"
                    "((symbol-function 'symbol-value) 'load-path)"
                    "((symbol-function 'car) paths)"
                    "((symbol-function 'expand-file-name) file dir)"
                    "((symbol-function 'file-directory-p) full-path)"
                    "((symbol-function 'cdr) paths)")))

;; The reached-from procedures on the real path (brief.org section 5.1).
(m55-imp1--check "reached-from-procedures"
                 (m55-imp1--holds-all
                  "mod/emacs/loader.scm"
                  '("(define (elisp-validate-load-file file)"
                    "(define (elisp-check-file-handler file"
                    "(define (elisp-process-load-file-path file"
                    "(define (search-elisp-load-path file)"
                    "(define (load-elisp-full found-file")))

;; The REAL path probe: a plain `guile -L mod' subprocess loads a real
;; .el file through the Scheme loader.  The probe DERIVES the first empty
;; cell from the ordered cell list (it is `get-load-suffixes'); the raise
;; is `wrong-type-arg'.  A missing guile binary is an explicit INFO skip,
;; never a pass.
(let ((out (m55-imp1--plain-guile-real-load-output)))
  (if (eq out 'm55-imp1-guile-absent)
      (progn
        (m55-imp1--info-skip "plain-guile-first-empty-cell"
                             "no guile binary on PATH")
        (m55-imp1--info-skip "plain-guile-recorded-raise"
                             "no guile binary on PATH"))
    (progn
      (m55-imp1--check "plain-guile-first-empty-cell"
                       (m55-imp1--contains-marker-p out
                                                   "M55-FIRST-CELL:get-load-suffixes"))
      (m55-imp1--check "plain-guile-recorded-raise"
                       (m55-imp1--contains-marker-p out "M55-OUTCOME:FAULT:wrong-type-arg")))))

;; The deep trace (brief.org section 5.1 step 4): supply rows 3 .. 9 with
;; tolerant Scheme stubs and repeat the REAL load.  M55 imp-4 removed row
;; 10 (the elisp compiler) from the route, so the trace no longer stops
;; there: with the stub cells the load advances past rows 3 .. 9 and
;; COMPLETES (the probe file holds no form, so the read reaches EOF at
;; once).  This records the imp-4 end state by measurement, per the
;; exact-value rule (cr.org section 8).  A missing guile binary is an
;; explicit INFO skip.
(let ((deep (m55-imp1--plain-guile-deep-trace-output)))
  (if (eq deep 'm55-imp1-guile-absent)
      (m55-imp1--info-skip "plain-guile-deep-trace-load-ok"
                           "no guile binary on PATH")
    (m55-imp1--check "plain-guile-deep-trace-load-ok"
                     (m55-imp1--contains-marker-p deep "M55-DEEP:LOAD-OK"))))

;;; --- S3. The registration site (brief.org section 5.4) --------------

;; The install site is prelude/load.scm: it runs the (use-modules ...)
;; lines and the 31 (init-...-registrations) calls.  A cell must be
;; bound before the loader applies it: the (emacs loader) module loads
;; before init-loader.  The loader itself registers 2 cells with
;; set-symbol-function! (`load' and `autoload-do-load').

(setq m55-imp1--group 's3)

(m55-imp1--check "install-site-init-loader"
                 (m55-imp1--contains-p "prelude/load.scm"
                                       "(init-loader %prelude-directory)"))
(m55-imp1--check "loader-self-registers-load"
                 (m55-imp1--contains-p "mod/emacs/loader.scm"
                                       "(set-symbol-function! 'load elisp-load)"))
(m55-imp1--check "loader-self-registers-autoload-do-load"
                 (m55-imp1--contains-p "mod/emacs/loader.scm"
                                       "(set-symbol-function! 'autoload-do-load elisp-autoload-do-load)"))
(m55-imp1--check "install-order-modules-before-init"
                 (m55-imp1--ordered-p
                  "prelude/load.scm"
                  '("(use-modules (emacs loader))" "(init-loader %prelude-directory)")))

;;; --- S4. The registration -------------------------------------------

(setq m55-imp1--group 's4)

(m55-imp1--check "run-tests-m55-imp1"
                 (m55-imp1--contains-p "tool/run-tests.scm"
                                       "test/m55/test-m55-imp1.el"))
(m55-imp1--check "run-tests-m55-group"
                 (m55-imp1--contains-p "tool/run-tests.scm" "(group (m55)"))
(m55-imp1--check "run-tests-m55-after-m54"
                 (m55-imp1--ordered-p "tool/run-tests.scm"
                                      '("(group (m54)" "(group (m55)")))
(m55-imp1--check "run-tests-m54-present"
                 (m55-imp1--contains-p "tool/run-tests.scm" "(group (m54)"))

;;; --- S5. The guards -------------------------------------------------

;; An --filter that matches no group already reports exit 0 with 0
;; tests, so a green m55 gate proves nothing until the corpus exists and
;; its checks really register.  S1 holds 9 checks, S2 holds 7, S3 holds
;; 4, and S4 holds 4.

(setq m55-imp1--group 's5)

(m55-imp1--check "reg/min-s1-checks-9" (>= (m55-imp1--group-count 's1) 9))
(m55-imp1--check "reg/min-s2-checks-7" (>= (m55-imp1--group-count 's2) 7))
(m55-imp1--check "reg/min-s3-checks-4" (>= (m55-imp1--group-count 's3) 4))
(m55-imp1--check "reg/min-s4-checks-4" (>= (m55-imp1--group-count 's4) 4))

;;; --- The group-total check ------------------------------------------

;; The measured count of m55-imp1 tests is 29: 28 registered checks
;; (S1 9, S2 7, S3 4, S4 4, S5 4) plus the group-total deftest itself.

(defvar m55-imp1--min-gate-total 29
  "The exact number of m55-imp1 ERT tests: 28 registered checks (S1 9,
S2 7, S3 4, S4 4, S5 4) plus the group-total deftest itself.")

(ert-deftest m55-imp1/gate-m55-total ()
  "The m55-imp1 corpus registers at least its docs-independent floor."
  (should (>= (length (ert-select-tests "^m55-imp1" t))
              m55-imp1--min-gate-total)))

(princ (format "=== m55 imp-1 suite done (%d checks; s1 %d, s2 %d, s3 %d, s4 %d, s5 %d) ===\n"
               m55-imp1--registered
               (m55-imp1--group-count 's1)
               (m55-imp1--group-count 's2)
               (m55-imp1--group-count 's3)
               (m55-imp1--group-count 's4)
               (m55-imp1--group-count 's5)))
