;;; test-m53-imp2.el --- M53 imp-2 standalone Guile loader check corpus.
;;;
;;; M53 imp-2 is the CHECK 1 "smaller step" of the M53 end-state audit
;;; (brief.org section 1): a plain `guile' process loads a real Elisp
;;; file through the Scheme loader, with no Emacs C core.
;;;
;;; The real load path is:
;;;
;;;   elisp-load -> elisp-validate-and-check-handler
;;;     -> elisp-validate-load-file  (holds the length cell)
;;;     -> elisp-check-file-handler  (holds find-file-name-handler)
;;;   -> elisp-process-load-file-path -> search-elisp-load-path
;;;
;;; The FIRST blocked cell on that path is the elisp `length' primitive,
;;; applied in `elisp-validate-load-file' (mod/emacs/loader.scm).  It is
;;; EMPTY in a plain `guile' process, so the old
;;; `((symbol-function 'length) file)' apply raised
;;; `wrong-type-arg "Wrong type to apply: #nil"'.  The file-name handler
;;; cell `find-file-name-handler' (in `elisp-check-file-handler') is the
;;; SECOND blocked cell, DOWNSTREAM of `length'.
;;;
;;; The loader POLICY fix (brief.org section 4, option (a)) tolerates
;;; both empty cells in Scheme: `elisp-string-length-for-load' guards the
;;; `length' call with `symbol-fbound?' and uses the Scheme string
;;; primitive when the cell is empty, and `elisp-check-file-handler'
;;; guards the handler call the same way.  No C fallback is added.  The
;;; old comment claimed "Scheme treats #nil as truthy"; that claim is
;;; FALSE for this Guile -- `(if #nil 'T 'F)' yields F -- so only the
;;; apply raised, inside the `let' binding, before the `(if handler ...)'
;;; test ran.  (The C `scm_is_true' accepts #nil, but the loader uses the
;;; Scheme `if'.)
;;;
;;; After the fix the load advances PAST validation and the handler
;;; check; the next blocked cell is `get-load-suffixes' (in
;;; `elisp-process-load-file-path').  The core elisp primitives
;;; (`length', `get-load-suffixes', `symbol-value', `car', `cdr',
;;; `expand-file-name', ...) come from the C bootstrap, not from the
;;; (emacs ...) modules, so the full C-core-absent load stays A2
;;; (docs/kb.org standalone-load-needs-runtime-cells).
;;;
;;; This corpus pins:
;;;
;;;   S1 -- the loader POLICY fix and the REAL path.  The source guards
;;;         the `length' cell (the first cell) and the handler cell; a
;;;         plain `guile -L mod' subprocess loads a real temporary .el
;;;         file through the Scheme loader, passes validation, and stops
;;;         at the recorded blocker.  S1 holds 4 checks.
;;;   S2 -- the traced cell list, in call order: `length' (cell 1,
;;;         tolerated), `find-file-name-handler' (cell 2, tolerated),
;;;         `get-load-suffixes' (cell 3, blocked).  Each cell is EMPTY in
;;;         a plain `guile' process.  S2 holds 3 checks.
;;;   S3 -- the A1 sub-check.  A real Elisp file loads through the
;;;         Scheme loader in this process (the built src/emacs) and its
;;;         `setq' side effect is read (brief.org section 3.3).  S3 holds
;;;         1 check.
;;;   S4 -- the registration and the guards: the corpus is registered in
;;;         the (m53) group of tool/run-tests.scm; a per-group min-count
;;;         guard for S1 .. S3; the group-total `ert-deftest'.  S4 holds
;;;         4 checks.
;;;
;;; This corpus reads TRACKED files only (mod/, src/, test/, and the
;;; tracked runner tool/run-tests.scm).  It does NOT read docs/
;;; (docs/kb.org test-must-not-read-docs).
;;;
;;; A read error is a real error, never a silent pass.  An absent src/
;;; file is a real FAIL, not a pass (brief.org section 2).  Every check
;;; registers a real ERT test via imp-register-bool-as-ert-test, so the
;;; exit code is correct.

(princ "=== m53 imp-2 standalone Guile loader suite ===\n")

(require 'imp-ert-report)

(defvar m53-imp2--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))
(defvar m53-imp2--registered 0
  "Total number of checks this corpus has registered.")
(defvar m53-imp2--group nil
  "The group that `m53-imp2--check' counts into: `s1' .. `s4', or nil.")
(defvar m53-imp2--counts nil
  "Alist of (GROUP . COUNT) for the registered checks.")

(defun m53-imp2--group-count (group)
  "Number of checks registered so far in GROUP."
  (or (cdr (assq group m53-imp2--counts)) 0))

(defun m53-imp2--bump-group ()
  "Count one check into `m53-imp2--group'."
  (when m53-imp2--group
    (let ((cell (assq m53-imp2--group m53-imp2--counts)))
      (if cell
          (setcdr cell (1+ (cdr cell)))
        (push (cons m53-imp2--group 1) m53-imp2--counts)))))

(defun m53-imp2--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
the symbol `m53-imp2-absent' when REL does not exist."
  (let ((path (expand-file-name rel m53-imp2--root)))
    (if (not (file-exists-p path))
        'm53-imp2-absent
      (with-temp-buffer
        (insert-file-contents path)
        (funcall fn)))))

(defun m53-imp2--contains-p (rel needle)
  "Non-nil when the TRACKED file REL contains NEEDLE.  An absent file
folds to nil, so `m53-imp2--check' prints FAIL."
  (let ((hit (m53-imp2--with rel
               (lambda ()
                 (goto-char (point-min))
                 (search-forward needle nil t)))))
    (and (not (eq hit 'm53-imp2-absent)) (and hit t))))

(defun m53-imp2--check (name ok)
  "Report and register one check on a TRACKED file.  OK is a boolean.
An absent source file folds to a real FAILING ERT test (brief.org
section 2)."
  (let* ((absent (eq ok 'm53-imp2-absent))
         (pass (and (not absent) (and ok t))))
    (if absent
        (princ (format "FAIL m53/imp2/%s (source file absent)\n" name))
      (princ (format "%s m53/imp2/%s\n" (if pass "PASS" "FAIL") name)))
    (setq m53-imp2--registered (1+ m53-imp2--registered))
    (m53-imp2--bump-group)
    (imp-register-bool-as-ert-test (format "m53-imp2/%s" name) pass)))

(defun m53-imp2--info-skip (name reason)
  "Register one explicit INFO skip, counted into the current group.  A
host limit is a skip, never a pass (brief.org section 2)."
  (princ (format "INFO m53/imp2/%s %s\n" name reason))
  (setq m53-imp2--registered (1+ m53-imp2--registered))
  (m53-imp2--bump-group)
  (imp-register-skip-as-ert-test (format "m53-imp2/%s" name) reason))

;;; --- The plain `guile' probe (no Emacs C core) ----------------------

(defun m53-imp2--guile ()
  "The plain `guile' binary on PATH, or nil."
  (executable-find "guile"))

(defun m53-imp2--run-guile (code)
  "Run a plain `guile -L mod -c CODE' subprocess and return its stdout
and stderr, or the symbol `m53-imp2-guile-absent' when no guile binary
is on PATH.  The Emacs C core is absent from this subprocess:
find-file-name-handler and the core elisp primitives are NOT installed."
  (let ((guile (m53-imp2--guile)))
    (if (not guile)
        'm53-imp2-guile-absent
      (let* ((modpath (expand-file-name "mod" m53-imp2--root))
             (buf (get-buffer-create " *m53-imp2-guile*")))
        (unwind-protect
            (progn
              (with-current-buffer buf (erase-buffer))
              (call-process guile nil buf nil "-L" modpath "-c" code)
              (with-current-buffer buf
                (buffer-substring-no-properties (point-min) (point-max))))
          (kill-buffer buf))))))

(defun m53-imp2--plain-guile-cell-fbound-p (cell)
  "A plain `guile' subprocess reports whether the elisp function CELL is
bound (installed by the Emacs C bootstrap).  Return `t', `nil', or the
symbol `m53-imp2-guile-absent'."
  (let ((code (format
               (concat
                "(use-modules (emacs-elisp runtime))"
                "(display (if (symbol-fbound? '%s) \"M53-BOUND\" \"M53-EMPTY\"))")
               cell)))
    (let ((out (m53-imp2--run-guile code)))
      (cond
       ((eq out 'm53-imp2-guile-absent) out)
       ((string-match-p "M53-BOUND" out) t)
       (t nil)))))

(defvar m53-imp2--plain-guile-recorded-outcome "M53-OUTCOME:FAULT:wrong-type-arg"
  "The recorded observable outcome of the C-core-absent real load: the
plain `guile' subprocess passes validation, then stops at the empty
`get-load-suffixes' cell and raises `wrong-type-arg'.  When imp-3/imp-4
supply the core runtime cells this marker flips to M53-OUTCOME:LOAD-OK
and this pin must be updated (the honest A2, brief.org section 1).")

(defun m53-imp2--plain-guile-real-load-output ()
  "Write a real Elisp file, run a plain `guile -L mod' subprocess that
loads it through the Scheme loader, and return the subprocess output.
The subprocess prints M53-VALIDATE-OK when validation and the handler
check pass, and M53-OUTCOME:LOAD-OK or M53-OUTCOME:FAULT:KEY for the
full load.  Return the symbol `m53-imp2-guile-absent' when no guile
binary is on PATH.  This is the REAL path (a real .el file through the
Scheme loader), not a module-load probe."
  (let ((file (make-temp-file "m53-imp2-plain-" nil ".el")))
    (unwind-protect
        (progn
          (with-temp-file file
            (insert ";; real Elisp file for the C-core-absent M53 imp-2 load\n"
                    "(setq m53-imp2-standalone-loaded 'm53-imp2-standalone-ok)\n"))
          (m53-imp2--run-guile
           (format
            (concat
             "(use-modules (emacs loader))"
             "(define rp (resolve-module '(emacs loader)))"
             "(define (ref n) (module-ref rp n))"
             "(define file \"%s\")"
             "(catch #t "
             "(lambda () ((ref 'elisp-validate-and-check-handler) file #nil #nil #nil #nil) "
             "(display \"M53-VALIDATE-OK\\n\")) "
             "(lambda (k . a) (display \"M53-VALIDATE-FAULT:\") (display k) (newline)))"
             "(catch #t "
             "(lambda () ((ref 'elisp-load) file #nil #nil #nil #nil) "
             "(display \"M53-OUTCOME:LOAD-OK\\n\")) "
             "(lambda (k . a) (display \"M53-OUTCOME:FAULT:\") (display k) (newline)))")
            file)))
      (when (file-exists-p file) (delete-file file)))))

(defun m53-imp2--contains-marker-p (out marker)
  "Non-nil when the subprocess output OUT holds MARKER.  OUT may be the
symbol `m53-imp2-guile-absent'."
  (and (not (eq out 'm53-imp2-guile-absent))
       (string-match-p (regexp-quote marker) out)
       t))

;;; --- The A1 sub-check (built src/emacs) -----------------------------

(defun m53-imp2--real-elisp-load-p ()
  "Load a real Elisp file through the Scheme loader and check its side
effect.  This is the A1 sub-check (brief.org section 3.3): the built
src/emacs still loads a real Elisp file through the Scheme loader.  The
file is written to a temp path, loaded with `load', and removed after."
  (let ((file (make-temp-file "m53-imp2-" nil ".el"))
        (result nil))
    (unwind-protect
        (progn
          (with-temp-file file
            (insert ";; a real Elisp file for the M53 imp-2 loader check\n"
                    "(setq m53-imp2-fixture-loaded 'm53-imp2-fixture-ok)\n"))
          (condition-case nil
              (progn
                (load file nil t)
                (setq result (and (boundp 'm53-imp2-fixture-loaded)
                                  (equal (symbol-value 'm53-imp2-fixture-loaded)
                                         'm53-imp2-fixture-ok))))
            (error (setq result nil))))
      (when (file-exists-p file) (delete-file file)))
    result))

;;; --- S1. The loader POLICY fix and the REAL path --------------------

;; Check 1 / 2 pin the two POLICY guards in the source: the `length' cell
;; (the FIRST blocked cell, reached in elisp-validate-load-file) and the
;; `find-file-name-handler' cell (the SECOND, reached in
;; elisp-check-file-handler).  Check 3 / 4 run the real C-core-absent
;; load: the plain `guile' subprocess passes validation, then stops at
;; the recorded blocker.

(setq m53-imp2--group 's1)

(m53-imp2--check "loader-length-first-cell-fix"
                 (m53-imp2--contains-p
                  "mod/emacs/loader.scm"
                  "(elisp-string-length-for-load file)"))

(m53-imp2--check "loader-handler-cell-fix"
                 (m53-imp2--contains-p
                  "mod/emacs/loader.scm"
                  "(symbol-fbound? 'find-file-name-handler)"))

(let ((out (m53-imp2--plain-guile-real-load-output)))
  (if (eq out 'm53-imp2-guile-absent)
      (progn
        (m53-imp2--info-skip "plain-guile-real-load-validates"
                             "no guile binary on PATH")
        (m53-imp2--info-skip "plain-guile-real-load-recorded-blocker"
                             "no guile binary on PATH"))
    (m53-imp2--check "plain-guile-real-load-validates"
                     (m53-imp2--contains-marker-p out "M53-VALIDATE-OK"))
    (m53-imp2--check "plain-guile-real-load-recorded-blocker"
                     (m53-imp2--contains-marker-p
                      out m53-imp2--plain-guile-recorded-outcome))))

;;; --- S2. The traced cell list (call order) --------------------------

;; The plain `guile' process has no Emacs C core, so the core elisp
;; cells that the C bootstrap installs are empty.  The traced list, in
;; call order: (1) length (tolerated by elisp-string-length-for-load),
;; (2) find-file-name-handler (tolerated by elisp-check-file-handler),
;; (3) get-load-suffixes (blocked, the next cell after the fix).  Each
;; probe pins the empty cell, so the class matches the record.

(setq m53-imp2--group 's2)

(defun m53-imp2--check-cell-empty (name cell)
  "Check that CELL is EMPTY in a plain `guile' process (a missing guile
binary is an explicit INFO skip, never a pass)."
  (let ((res (m53-imp2--plain-guile-cell-fbound-p cell)))
    (if (eq res 'm53-imp2-guile-absent)
        (m53-imp2--info-skip name "no guile binary on PATH")
      (m53-imp2--check name (null res)))))

(m53-imp2--check-cell-empty "cell-length-empty" "length")
(m53-imp2--check-cell-empty "cell-find-file-name-handler-empty"
                            "find-file-name-handler")
(m53-imp2--check-cell-empty "cell-get-load-suffixes-empty"
                            "get-load-suffixes")

;;; --- S3. The A1 sub-check -------------------------------------------

(setq m53-imp2--group 's3)

(m53-imp2--check "real-elisp-load-through-scheme-loader"
                 (m53-imp2--real-elisp-load-p))

;;; --- S4. The registration and the guards ----------------------------

(setq m53-imp2--group 's4)

(m53-imp2--check "run-tests-m53-imp2"
                 (m53-imp2--contains-p "tool/run-tests.scm"
                                       "test/m53/test-m53-imp2.el"))
(m53-imp2--check "reg/min-s1-checks-4" (>= (m53-imp2--group-count 's1) 4))
(m53-imp2--check "reg/min-s2-checks-3" (>= (m53-imp2--group-count 's2) 3))
(m53-imp2--check "reg/min-s3-checks-1" (>= (m53-imp2--group-count 's3) 1))

;;; --- The group-total check ------------------------------------------

;; Select ONLY the m53-imp2 tests (the pattern is "^m53-imp2", not
;; "^m53-imp"): the whole (m53) group runs in one emacs process, so a
;; "^m53-imp" pattern would match the imp-1 tests too and the floor
;; could not catch a zero-check imp-2 run (cr.org F6).

(defvar m53-imp2--min-gate-total 12
  "The minimum number of m53-imp2 ERT tests: 12 registered checks
(S1 4, S2 3, S3 1, S4 4) plus the group-total deftest.  When no guile
binary is on PATH the S1/S2 subprocess checks fold to controlled INFO
skips, and a controlled skip is still a registered test, so the floor
holds either way.")

(ert-deftest m53-imp2/gate-m53-total ()
  "The m53-imp2 corpus registers at least its docs-independent floor."
  (should (>= (length (ert-select-tests "^m53-imp2" t))
              m53-imp2--min-gate-total)))

(princ (format "=== m53 imp-2 suite done (%d checks; s1 %d, s2 %d, s3 %d, s4 %d) ===\n"
               m53-imp2--registered
               (m53-imp2--group-count 's1)
               (m53-imp2--group-count 's2)
               (m53-imp2--group-count 's3)
               (m53-imp2--group-count 's4)))
