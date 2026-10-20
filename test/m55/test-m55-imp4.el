;;; test-m55-imp4.el --- M55 imp-4 source-reading load path corpus.
;;;
;;; M55 imp-4 removes row 10 (the elisp compiler) from the plain `guile'
;;; load path (brief.org section 1).  A real .el file must LOAD and RUN:
;;; the loader READS the source text, SKIPS the elisp compiler, and
;;; evaluates the forms.  Row 10 STAYS C for the full-Emacs path; the C
;;; delta is 0 and the Scheme delta is the route, the runtime cells, and
;;; this corpus.
;;;
;;; This corpus shows, by measurement, on the REAL path (a plain
;;; `guile -L mod' subprocess that calls init-loader and then loads a
;;; real .el file through elisp-load):
;;;
;;;   1. after init-loader no reachable cell is empty: the FIRST empty
;;;      cell of the ordered list (the 7 imp-2 cells get-load-suffixes,
;;;      append, symbol-value, car, expand-file-name, file-directory-p,
;;;      cdr, then the 4 imp-4 cells intern, concat, substring, eval) is
;;;      NONE;
;;;   2. the load no longer stops at row 10: it returns LOAD-OK;
;;;   3. the file RAN: its observable side effect (setq of a marker
;;;      string) is visible after the load.  The corpus FAILS when the
;;;      loader only READS the file and does NOT run it.
;;;
;;; This corpus pins these groups:
;;;
;;;   S1 -- the REAL path (brief.org sections 3 and 6).  A plain
;;;         `guile -L mod -c' subprocess calls (use-modules (emacs
;;;         loader)) and (use-modules (emacs-elisp runtime)), then
;;;         init-loader (the registration site), then elisp-load on a
;;;         real .el file.  It DERIVES that no reachable cell is empty
;;;         (the first empty cell of the ordered 11-cell list -- the 7
;;;         imp-2 cells plus the 4 imp-4 cells -- is NONE), pins the
;;;         LOAD-OK outcome, and pins the OBSERVABLE SIDE EFFECT: the
;;;         file setq-s a marker string, DEFINES a function (defun) and
;;;         CALLS it (F2), and `let' RESTORES its binding (F4).  The
;;;         side-effect check FAILS when the loader only READS the file.
;;;         A second subprocess loads a BROKEN file and pins that the
;;;         evaluator raises void-function (F3), and error exits restore
;;;         both `let' and lambda bindings.  S1 holds 8 checks.
;;;   S2 -- the route and the cells (brief.org sections 5 and 6).  The
;;;         source-reading branch in load-elisp-full: the compiler-absent
;;;         test (elisp-loader-compiler-available?), which catches ONLY
;;;         the "no such language" message (F6); the source reader
;;;         (elisp-load-source-file, open-input-file); the 4 cells
;;;         (intern, concat, substring, eval) installed in call order,
;;;         each with a symbol-fbound? guard; and the evaluator special
;;;         forms, the void raise (F3), and the binding restore (F4).
;;;         S2 holds 8 checks.
;;;   S3 -- the re-measured surface (brief.org section 9): loader.scm
;;;         1,187 lines / 74 (symbol-function 'X) apply matches / 18
;;;         symbol-fbound? / 14 set-symbol-function! / 7
;;;         FIX-*-guilemacs; reader.scm 2,021 lines; prelude/load.scm 265
;;;         lines.  imp-4 edits mod/emacs/loader.scm, so these values
;;;         differ from the imp-3 values.  S3 holds 7 checks.
;;;   S4 -- the registration (brief.org section 8): the (m55) group of
;;;         tool/run-tests.scm holds the imp-4 file and the (m55) group
;;;         line; the group comes after (m54); the group holds the imp-1,
;;;         imp-2, and imp-3 files.  S4 holds 4 checks.
;;;   S5 -- the guards (brief.org section 8): one per-group min-count
;;;         guard for each of S1 .. S4.  The in-process group-total
;;;         `ert-deftest' is a separate test in the same phase; it is NOT
;;;         one of the 4 counted checks (the floor is 29 registered
;;;         checks plus that deftest = 30).
;;;
;;; This corpus reads TRACKED files only (mod/, prelude/, and the
;;; tracked runner tool/run-tests.scm).  It does NOT read docs/
;;; (docs/kb.org test-must-not-read-docs): a gitignored record can only
;;; pass or skip, so a record check proves nothing.
;;;
;;; A read error is a real error, never a silent pass.  An absent
;;; TRACKED file is a real FAIL, not a pass.  A missing `guile' binary is
;;; an explicit INFO skip, never a pass.  Every check registers a real
;;; ERT test via imp-register-bool-as-ert-test, so the harness parses the
;;; ERT output and the exit code is correct.

(princ "=== m55 imp-4 source-reading load path suite ===\n")

(require 'imp-ert-report)

(defvar m55-imp4--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))
(defvar m55-imp4--registered 0
  "Total number of checks this corpus has registered.")
(defvar m55-imp4--group nil
  "The group that `m55-imp4--check' counts into: `s1' .. `s5', or nil.")
(defvar m55-imp4--counts nil
  "Alist of (GROUP . COUNT) for the registered checks.")

(defun m55-imp4--group-count (group)
  "Number of checks registered so far in GROUP."
  (or (cdr (assq group m55-imp4--counts)) 0))

(defun m55-imp4--bump-group ()
  "Count one check into `m55-imp4--group'."
  (when m55-imp4--group
    (let ((cell (assq m55-imp4--group m55-imp4--counts)))
      (if cell
          (setcdr cell (1+ (cdr cell)))
        (push (cons m55-imp4--group 1) m55-imp4--counts)))))

(defun m55-imp4--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
the symbol `m55-imp4-absent' when REL does not exist."
  (let ((path (expand-file-name rel m55-imp4--root)))
    (if (not (file-exists-p path))
        'm55-imp4-absent
      (with-temp-buffer
        (insert-file-contents path)
        (funcall fn)))))

(defun m55-imp4--contains-p (rel needle)
  "Non-nil when the TRACKED file REL contains NEEDLE.  An absent file
folds to nil, so a check prints FAIL: an absent TRACKED file is a real
error, not a pass."
  (let ((hit (m55-imp4--with rel
               (lambda ()
                 (goto-char (point-min))
                 (search-forward needle nil t)))))
    (and (not (eq hit 'm55-imp4-absent)) (and hit t))))

(defun m55-imp4--ordered-p (rel needles)
  "Non-nil when the TRACKED file REL holds every NEEDLE in the GIVEN
ORDER: each search starts after the previous match."
  (m55-imp4--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((all t))
        (dolist (needle needles)
          (when all
            (unless (search-forward needle nil t) (setq all nil))))
        all))))

(defun m55-imp4--lines (rel)
  "Count the newlines of REL the way `wc -l' does."
  (m55-imp4--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (search-forward "\n" nil t) (setq n (1+ n)))
        n))))

(defun m55-imp4--count (rel regexp)
  "Count the matches of REGEXP in REL, the way `grep -o PATTERN | wc -l'
does.  Use this only for a brief row whose command is `grep -o'."
  (m55-imp4--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (re-search-forward regexp nil t) (setq n (1+ n)))
        n))))

(defun m55-imp4--count-lines (rel regexp)
  "Count the lines of REL that match REGEXP, the way `grep -c PATTERN'
does.  The brief.org section 9 rows use `grep -c' (a LINE count), so
this corpus counts lines and not matches."
  (m55-imp4--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (not (eobp))
          (when (re-search-forward regexp (line-end-position) t)
            (setq n (1+ n)))
          (forward-line 1))
        n))))

(defun m55-imp4--check (name ok)
  "Report and register one check on a TRACKED file.  OK is a boolean.
When the source file is absent the reader returns the symbol
`m55-imp4-absent', so a count check folds to a real FAILING ERT test."
  (let* ((absent (eq ok 'm55-imp4-absent))
         (pass (and (not absent) (and ok t))))
    (if absent
        (princ (format "FAIL m55/imp4/%s (source file absent)\n" name))
      (princ (format "%s m55/imp4/%s\n" (if pass "PASS" "FAIL") name)))
    (setq m55-imp4--registered (1+ m55-imp4--registered))
    (m55-imp4--bump-group)
    (imp-register-bool-as-ert-test (format "m55-imp4/%s" name) pass)))

(defun m55-imp4--info-skip (name reason)
  "Register one explicit INFO skip, counted into the current group.  A
host limit is a skip, never a pass (brief.org section 10)."
  (princ (format "INFO m55/imp4/%s %s\n" name reason))
  (setq m55-imp4--registered (1+ m55-imp4--registered))
  (m55-imp4--bump-group)
  (imp-register-skip-as-ert-test (format "m55-imp4/%s" name) reason))

;;; --- The plain `guile' probe (no Emacs C core) ----------------------

(defun m55-imp4--guile ()
  "The plain `guile' binary on PATH, or nil."
  (executable-find "guile"))

(defun m55-imp4--run-guile (code)
  "Run a plain `guile -L mod -c CODE' subprocess and return its combined
output, or the symbol `m55-imp4-guile-absent' when no guile binary is on
PATH.  The Emacs C core is absent from this subprocess: the core elisp
function cells are NOT installed by it."
  (let ((guile (m55-imp4--guile)))
    (if (not guile)
        'm55-imp4-guile-absent
      (let* ((modpath (expand-file-name "mod" m55-imp4--root))
             (buf (get-buffer-create " *m55-imp4-guile*")))
        (unwind-protect
            (progn
              (with-current-buffer buf (erase-buffer))
              (call-process guile nil buf nil "-L" modpath "-c" code)
              (with-current-buffer buf
                (buffer-substring-no-properties (point-min) (point-max))))
          (kill-buffer buf))))))

(defun m55-imp4--plain-guile-real-load-output ()
  "Write a real Elisp file with an observable side effect, run a plain
`guile -L mod' subprocess that CALLS init-loader (the registration site)
and then loads the file through the Scheme loader (the REAL path, not a
module-load probe), and return the subprocess output.

The file setq-s a marker string.  The subprocess runs (use-modules
(emacs loader)) and (use-modules (emacs-elisp runtime)), then
init-loader FIRST, so the reader/eval cells are installed.  Then it
DERIVES the first empty cell from the ordered reader-cell list
(intern, concat, substring, eval) and prints M55-IMP4-FIRST-EMPTY:NAME.
It prints M55-IMP4-OUTCOME:LOAD-OK on success (or FAULT:KEY + ARGS), and
M55-IMP4-MARKER:VALUE for the observable side effect (UNBOUND when the
file was only READ).  Return the symbol `m55-imp4-guile-absent' when no
guile binary is on PATH."
  (let ((file (make-temp-file "m55-imp4-plain-" nil ".el"))
        (prelude (expand-file-name "prelude" m55-imp4--root)))
    (unwind-protect
        (progn
          (with-temp-file file
            (insert ";; real Elisp file for the C-core-absent M55 imp-4 load\n"
                    "(setq m55-imp4-marker \"M55-IMP4-RAN-OK\")\n"
                    ";; F2: a DEFINITION that a later form CALLS\n"
                    "(defun m55-imp4-double (x) (concat x x))\n"
                    "(setq m55-imp4-call (m55-imp4-double \"AB\"))\n"
                    ";; F4: `let' must RESTORE the old binding on exit\n"
                    "(setq m55-imp4-zz 1)\n"
                    "(let ((m55-imp4-zz 99)) m55-imp4-zz)\n"))
          (m55-imp4--run-guile
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
             "(display \"M55-IMP4-FIRST-EMPTY:\")"
             "(display (first-empty '(get-load-suffixes append symbol-value "
             "car expand-file-name file-directory-p cdr "
             "intern concat substring eval)))"
             "(newline)"
             "(catch #t "
             "(lambda () (el \"%s\" #nil #nil #nil #nil) "
             "(display \"M55-IMP4-OUTCOME:LOAD-OK\\n\")) "
             "(lambda (k . a) (display \"M55-IMP4-OUTCOME:FAULT:\") (display k) "
             "(display \" ARGS:\") (write a) (newline)))"
             "(display \"M55-IMP4-MARKER:\")"
             "(display (if (symbol-bound? 'm55-imp4-marker) "
             "(symbol-value 'm55-imp4-marker) \"UNBOUND\"))"
             "(newline)"
             "(display \"M55-IMP4-CALL:\")"
             "(display (if (symbol-bound? 'm55-imp4-call) "
             "(symbol-value 'm55-imp4-call) \"UNBOUND\"))"
             "(newline)"
             "(display \"M55-IMP4-ZZ:\")"
             "(display (if (symbol-bound? 'm55-imp4-zz) "
             "(symbol-value 'm55-imp4-zz) \"UNBOUND\"))"
             "(newline)")
            prelude file)))
      (ignore-errors (delete-file file)))))

(defun m55-imp4--plain-guile-void-function-output ()
  "Load a BROKEN Elisp file (a call to an unbound function) in a plain
`guile -L mod' subprocess that calls init-loader and then loads the file
through the Scheme loader.  The evaluator MUST raise `void-function' (F3),
so a broken file can NOT look like a clean load.  Return the subprocess
output, or the symbol `m55-imp4-guile-absent' when no guile binary is on
PATH."
  (let ((file (make-temp-file "m55-imp4-voidfn-" nil ".el"))
        (prelude (expand-file-name "prelude" m55-imp4--root)))
    (unwind-protect
        (progn
          (with-temp-file file
            (insert ";; a broken Elisp file: a call to an unbound function\n"
                    "(m55-imp4-undefined-fn 1)\n"))
          (m55-imp4--run-guile
           (format
            (concat
             "(use-modules (emacs loader))"
             "(use-modules (emacs-elisp runtime))"
             "(define el (module-ref (resolve-module '(emacs loader)) 'elisp-load))"
             "(init-loader \"%s\")"
             "(catch #t "
             "(lambda () (el \"%s\" #nil #nil #nil #nil) "
             "(display \"M55-IMP4-BAD-OUTCOME:LOAD-OK\\n\")) "
             "(lambda (k . a) (display \"M55-IMP4-BAD-OUTCOME:FAULT:\") (display k) "
             "(display \" ARGS:\") (write a) (newline)))")
            prelude file)))
      (ignore-errors (delete-file file)))))

(defun m55-imp4--plain-guile-error-binding-output (body)
  "Load BODY after setting a dynamic variable, then report its value."
  (let ((file (make-temp-file "m55-imp4-unwind-" nil ".el"))
        (prelude (expand-file-name "prelude" m55-imp4--root)))
    (unwind-protect
        (progn
          (with-temp-file file
            (insert "(setq m55-imp4-error-binding 1)\n" body "\n"))
          (m55-imp4--run-guile
           (format
            (concat
             "(use-modules (emacs loader))"
             "(use-modules (emacs-elisp runtime))"
             "(define el (module-ref (resolve-module '(emacs loader)) 'elisp-load))"
             "(init-loader \"%s\")"
             "(catch #t (lambda () (el \"%s\" #nil #nil #nil #nil))"
             "  (lambda (k . a) (display \"M55-IMP4-UNWIND-FAULT:\")"
             "    (display k) (newline)))"
             "(display \"M55-IMP4-UNWIND-VALUE:\")"
             "(write (symbol-value 'm55-imp4-error-binding)) (newline)")
            prelude file)))
      (ignore-errors (delete-file file)))))

(defun m55-imp4--contains-marker-p (out marker)
  "Non-nil when the subprocess output OUT holds MARKER.  OUT may be the
symbol `m55-imp4-guile-absent'."
  (and (not (eq out 'm55-imp4-guile-absent))
       (string-match-p (regexp-quote marker) out)
       t))

;;; --- S1. The REAL path (brief.org sections 3 and 6) -----------------

;; A plain `guile -L mod -c' subprocess calls init-loader, then loads a
;; real .el file through the Scheme loader.  A missing guile binary is an
;; explicit INFO skip, never a pass.

(setq m55-imp4--group 's1)

(let ((out (m55-imp4--plain-guile-real-load-output)))
  (if (eq out 'm55-imp4-guile-absent)
      (progn
        (m55-imp4--info-skip "plain-guile-no-empty-cell"
                             "no guile binary on PATH")
        (m55-imp4--info-skip "plain-guile-load-ok"
                             "no guile binary on PATH")
        (m55-imp4--info-skip "plain-guile-runs-file"
                             "no guile binary on PATH")
        (m55-imp4--info-skip "plain-guile-runs-call"
                             "no guile binary on PATH")
        (m55-imp4--info-skip "plain-guile-let-restores"
                             "no guile binary on PATH"))
    (progn
      ;; After init-loader the reader/eval cells are no longer empty: the
      ;; first empty cell of the ordered list is NONE.
      (m55-imp4--check "plain-guile-no-empty-cell"
                       (m55-imp4--contains-marker-p out "M55-IMP4-FIRST-EMPTY:NONE"))
      ;; imp-4 removes row 10 from the route: the load no longer stops at
      ;; the elisp compiler.  It returns LOAD-OK.
      (m55-imp4--check "plain-guile-load-ok"
                       (m55-imp4--contains-marker-p out "M55-IMP4-OUTCOME:LOAD-OK"))
      ;; The OBSERVABLE SIDE EFFECT: the file ran, so its setq marker is
      ;; visible after the load.  This check FAILS when the loader only
      ;; READS the file and does NOT run it (the marker stays UNBOUND).
      (m55-imp4--check "plain-guile-runs-file"
                       (and (m55-imp4--contains-marker-p
                             out "M55-IMP4-MARKER:M55-IMP4-RAN-OK")
                            (not (m55-imp4--contains-marker-p
                                  out "M55-IMP4-MARKER:UNBOUND"))))
      ;; F2: a DEFINITION (defun) and a CALL really ran.  The file defines
      ;; m55-imp4-double and calls it; the result "ABAB" is visible only
      ;; when both the definition and the application evaluated.
      (m55-imp4--check "plain-guile-runs-call"
                       (m55-imp4--contains-marker-p out "M55-IMP4-CALL:ABAB"))
      ;; F4: `let' RESTORED the old binding.  The file setq-s
      ;; m55-imp4-zz to 1, then evaluates (let ((m55-imp4-zz 99)) ...).
      ;; Elisp restores the outer binding, so the value is 1 (NOT 99).
      (m55-imp4--check "plain-guile-let-restores"
                       (m55-imp4--contains-marker-p out "M55-IMP4-ZZ:1")))))

;; F3: a BROKEN file must NOT look like a clean load.  A call to an
;; unbound function raises `void-function'.
(let ((bad (m55-imp4--plain-guile-void-function-output)))
  (if (eq bad 'm55-imp4-guile-absent)
      (m55-imp4--info-skip "plain-guile-void-function-fault"
                           "no guile binary on PATH")
    (m55-imp4--check "plain-guile-void-function-fault"
                     (and (m55-imp4--contains-marker-p
                           bad "M55-IMP4-BAD-OUTCOME:FAULT:void-function")
                          (not (m55-imp4--contains-marker-p
                                bad "M55-IMP4-BAD-OUTCOME:LOAD-OK"))))))

;; Binding cleanup must run when evaluation exits through an error.
(dolist (case
         (list
          (cons "let"
                (m55-imp4--plain-guile-error-binding-output
                 (concat "(let ((m55-imp4-error-binding 99)) "
                         "(m55-imp4-undefined-fn 1))")))
          (cons "lambda"
                (m55-imp4--plain-guile-error-binding-output
                 (concat "(defun m55-imp4-error-lambda "
                         "(m55-imp4-error-binding) "
                         "(m55-imp4-undefined-fn 1))\n"
                         "(m55-imp4-error-lambda 99)")))))
  (let ((name (car case)) (out (cdr case)))
    (if (eq out 'm55-imp4-guile-absent)
        (m55-imp4--info-skip (format "unwind-%s-restores" name)
                             "no guile binary on PATH")
      (m55-imp4--check
       (format "unwind-%s-restores" name)
       (and (m55-imp4--contains-marker-p
             out "M55-IMP4-UNWIND-FAULT:void-function")
            (m55-imp4--contains-marker-p
             out "M55-IMP4-UNWIND-VALUE:1"))))))

;;; --- S2. The route and the cells (brief.org sections 5 and 6) -------

(setq m55-imp4--group 's2)

;; The source-reading branch in load-elisp-full: the compiler-absent
;; test, the source reader, and the open-input-file call.

(m55-imp4--check "route-compiler-absent-test"
                 (and (m55-imp4--contains-p "mod/emacs/loader.scm"
                                            "(elisp-loader-compiler-available?)")
                      (m55-imp4--contains-p "mod/emacs/loader.scm"
                                            "(catch 'misc-error")))
(m55-imp4--check "route-source-reader"
                 (and (m55-imp4--contains-p "mod/emacs/loader.scm"
                                            "(define (elisp-load-source-file src)")
                      (m55-imp4--contains-p "mod/emacs/loader.scm"
                                            "(open-input-file src)")
                      (m55-imp4--contains-p "mod/emacs/loader.scm"
                                            "(elisp-load-read-eval-loop-from-port port #f)")))

;; cr.org M2: load-elisp is an exported entry point, so it can be reached
;; in a plain `guile' process too.  It must test the compiler the same way
;; (elisp-loader-compiler-available?) and take the source-reading branch
;; (elisp-load-source-file), NOT call lookup-language unguarded.
(m55-imp4--check "route-load-elisp-branch-guarded"
                 (m55-imp4--ordered-p
                  "mod/emacs/loader.scm"
                  '("(define (load-elisp file)"
                    "(elisp-loader-compiler-available?)"
                    "(elisp-load-source-file src)")))

;; The 4 new cells (intern, concat, substring, eval) install in call
;; order in init-loader, each bound to its guard: a `come before' ORDER
;; check, so a reordering fails the run.

(m55-imp4--check "install-reader-eval-cells-guarded-in-order"
                 (m55-imp4--ordered-p
                  "mod/emacs/loader.scm"
                  '("(unless (symbol-fbound? 'intern)"
                    "(set-symbol-function! 'intern elisp-intern)"
                    "(unless (symbol-fbound? 'concat)"
                    "(set-symbol-function! 'concat elisp-loader-concat)"
                    "(unless (symbol-fbound? 'substring)"
                    "(set-symbol-function! 'substring elisp-loader-substring)"
                    "(unless (symbol-fbound? 'eval)"
                    "(set-symbol-function! 'eval elisp-loader-eval)")))

;; The evaluator is the minimal elisp evaluator (brief.org section 7),
;; NOT the elisp compiler (row 10): it defines the special forms and does
;; not call the compiler.

(m55-imp4--check "evaluator-minimal-special-forms"
                 (and (m55-imp4--contains-p "mod/emacs/loader.scm"
                                            "(define (elisp-loader-eval form)")
                      (m55-imp4--contains-p "mod/emacs/loader.scm"
                                            "(eq? head 'quote)")
                      (m55-imp4--contains-p "mod/emacs/loader.scm"
                                            "(eq? head 'setq)")
                      (m55-imp4--contains-p "mod/emacs/loader.scm"
                                            "(eq? head 'if)")
                      (m55-imp4--contains-p "mod/emacs/loader.scm"
                                            "(eq? head 'progn)")
                      (m55-imp4--contains-p "mod/emacs/loader.scm"
                                            "(eq? head 'let)")
                      (m55-imp4--contains-p "mod/emacs/loader.scm"
                                            "(eq? head 'lambda)")
                      (m55-imp4--contains-p "mod/emacs/loader.scm"
                                            "(eq? head 'defun)")))

;; F3: the evaluator RAISES on an unbound function and an unbound
;; variable, so a broken file can NOT look like a clean load.
(m55-imp4--check "evaluator-raises-void"
                 (and (m55-imp4--contains-p "mod/emacs/loader.scm"
                                            "(throw 'void-function fn)")
                      (m55-imp4--contains-p "mod/emacs/loader.scm"
                                            "(throw 'void-variable form)")
                      (m55-imp4--contains-p "mod/emacs/loader.scm"
                                            "(throw 'void-function head)")))

;; F4: `let' and a lambda argument RESTORE the previous binding.
(m55-imp4--check "evaluator-restores-bindings"
                 (and (m55-imp4--contains-p "mod/emacs/loader.scm"
                                            "(define (elisp-loader-bind-thunk name value)")
                      (m55-imp4--contains-p "mod/emacs/loader.scm"
                                            "(define (elisp-loader-bind-params! params args)")))

;; F6: the compiler-absent test catches ONLY the "no such language"
;; message, and re-raises any other misc-error.
(m55-imp4--check "route-compiler-catch-narrow"
                 (and (m55-imp4--contains-p "mod/emacs/loader.scm"
                                            "\"no such language\"")
                      (m55-imp4--contains-p "mod/emacs/loader.scm"
                                            "(apply throw key args)")))

;;; --- S3. The re-measured surface (brief.org section 9) --------------

;; imp-4 edits mod/emacs/loader.scm, so the loader pins MOVE from the
;; imp-3 values (959 lines / 74 / 11 / 9 / 4).  re-measure and pin the
;; new values.  The counting semantics follow the brief command of each
;; row: `grep -c' is a LINE count, `grep -o | wc -l' is a MATCH count.

(setq m55-imp4--group 's3)

(m55-imp4--check "loader.scm-lines-1214"
                 (eql 1214 (m55-imp4--lines "mod/emacs/loader.scm")))
(m55-imp4--check "reader.scm-lines-2021"
                 (eql 2021 (m55-imp4--lines "mod/emacs/reader.scm")))
(m55-imp4--check "prelude-load.scm-lines-229"
                 (eql 229 (m55-imp4--lines "prelude/load.scm")))
(m55-imp4--check "loader.scm-symbol-function-apply-74"
                 (eql 74 (m55-imp4--count "mod/emacs/loader.scm"
                                          "(symbol-function '")))
(m55-imp4--check "loader.scm-symbol-fbound-guards-19"
                 (eql 19 (m55-imp4--count-lines "mod/emacs/loader.scm"
                                                "symbol-fbound?")))
(m55-imp4--check "loader.scm-set-symbol-function-15"
                 (eql 15 (m55-imp4--count-lines "mod/emacs/loader.scm"
                                               "set-symbol-function!")))
(m55-imp4--check "loader.scm-fix-markers-8"
                 (eql 8 (m55-imp4--count-lines "mod/emacs/loader.scm"
                                               "FIX-.*guilemacs")))

;;; --- S4. The registration (brief.org section 8) ---------------------

(setq m55-imp4--group 's4)

(m55-imp4--check "run-tests-m55-imp4"
                 (m55-imp4--contains-p "tool/run-tests.scm"
                                       "test/m55/test-m55-imp4.el"))
(m55-imp4--check "run-tests-m55-group"
                 (m55-imp4--contains-p "tool/run-tests.scm" "(group (m55)"))
(m55-imp4--check "run-tests-m55-after-m54"
                 (m55-imp4--ordered-p "tool/run-tests.scm"
                                      '("(group (m54)" "(group (m55)")))
(m55-imp4--check "run-tests-m55-holds-imp1-imp2-imp3"
                 (and (m55-imp4--contains-p "tool/run-tests.scm"
                                            "test/m55/test-m55-imp1.el")
                      (m55-imp4--contains-p "tool/run-tests.scm"
                                            "test/m55/test-m55-imp2.el")
                      (m55-imp4--contains-p "tool/run-tests.scm"
                                            "test/m55/test-m55-imp3.el")))

;;; --- S5. The guards (brief.org section 8) ---------------------------

;; An --filter that matches no group already reports exit 0 with 0
;; tests, so a green m55 gate proves nothing until the corpus exists and
;; its checks really register.  S1 holds 8 checks, S2 holds 8, S3 holds
;; 7, and S4 holds 4.

(setq m55-imp4--group 's5)

(m55-imp4--check "reg/min-s1-checks-8" (>= (m55-imp4--group-count 's1) 8))
(m55-imp4--check "reg/min-s2-checks-8" (>= (m55-imp4--group-count 's2) 8))
(m55-imp4--check "reg/min-s3-checks-7" (>= (m55-imp4--group-count 's3) 7))
(m55-imp4--check "reg/min-s4-checks-4" (>= (m55-imp4--group-count 's4) 4))

;;; --- The group-total check ------------------------------------------

;; The measured count of m55-imp4 tests is 32: 31 registered checks
;; (S1 8, S2 8, S3 7, S4 4, S5 4) plus the group-total deftest itself.

(defvar m55-imp4--min-gate-total 32
  "The exact number of m55-imp4 ERT tests: 31 registered checks (S1 8,
S2 8, S3 7, S4 4, S5 4) plus the group-total deftest itself.")

(ert-deftest m55-imp4/gate-m55-total ()
  "The m55-imp4 corpus registers at least its docs-independent floor."
  (should (>= (length (ert-select-tests "^m55-imp4" t))
              m55-imp4--min-gate-total)))

(princ (format "=== m55 imp-4 suite done (%d checks; s1 %d, s2 %d, s3 %d, s4 %d, s5 %d) ===\n"
               m55-imp4--registered
               (m55-imp4--group-count 's1)
               (m55-imp4--group-count 's2)
               (m55-imp4--group-count 's3)
               (m55-imp4--group-count 's4)
               (m55-imp4--group-count 's5)))
