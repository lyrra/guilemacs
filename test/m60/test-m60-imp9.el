;;; test-m60-imp9.el --- M60 imp-9 `cond' / `let*' / `while' corpus.
;;;
;;; M60 imp-9 lands row 28a of the row map of docs/m60-plan.org section
;;; 6: the 3 evaluator branches `cond', `let*' and `while' of
;;; `elisp-loader-eval-form' in mod/emacs/loader.scm.  All 3 names are
;;; SPECIAL FORMS, so `init-loader' gets NO new install site, the C
;;; delta is 0 and mod/emacs/reader.scm is NOT touched.
;;;
;;; Row 28b (`backquote', `,' and `,@') stays OPEN.  The 3 branches are
;;; a PORT of the elisp special forms, not a workaround: no
;;; FIX-YYYYMMDD-guilemacs marker is added.
;;;
;;; The branch rules of brief.org section 4:
;;;   `cond'  the catch-all `t' and `otherwise' are tested as SYMBOLS,
;;;           before the evaluation of the test, because `t' is a
;;;           variable and `otherwise' is usually unbound.  A clause
;;;           with a TEST only returns the test value.  No match and an
;;;           empty clause list return #nil.  The test uses
;;;           `elisp-loader-truthy?', not Scheme truth.
;;;   `let*'  the bindings are made ONE AT A TIME, so a later INIT sees
;;;           the PREVIOUS name.  The undo path is the `let' path: 1
;;;           `elisp-loader-bind-thunk' per name, the body inside
;;;           `dynamic-wind', every restore thunk in the exit thunk.
;;;   `while' the test runs BEFORE the first body form, a false test
;;;           runs the body 0 times, and the value is ALWAYS #nil.  A
;;;           named `let' loop, not Guile `while'.
;;;
;;; LIMITS, named in the source and NOT claimed here: L16 no `=>' and no
;;; `cl-case' clause shape, L17 `while' has no loop limit, L18 the
;;; binding model is DYNAMIC (as L3), L19 the catch-all symbols are
;;; tested without evaluation, L20 no `catch' /
;;; `unwind-protect' / `condition-case', L21 the `cond' clause-shape
;;; error is a Guile `misc-error', not an elisp signal (cr.org F6).
;;;
;;; The cr.org review of this row is answered here too:
;;;   F3 an INIT that raises RESTORES the names that are bound already,
;;;      so the binding loop runs INSIDE the `dynamic-wind' body.  This
;;;      holds for `let*', where the names are bound ONE AT A TIME: in
;;;      `let' no name is bound when the INITS run, so there is nothing
;;;      to restore (cr.org review of imp-9, finding F5).
;;;   F4 the restore thunks run LAST-IN-FIRST-OUT, so a DUPLICATE name
;;;      gets the OUTER value back, in both branches.
;;;   F5 a BARE SYMBOL binding binds elisp nil, as in Emacs.
;;;   F8 test/m60/fixture-imp9.el is a TRACKED `.el' file that mode
;;;      `control' loads through the elisp READER and then the elisp
;;;      EVALUATOR, so the 3 forms are proven on the REAL path and not
;;;      only on hand-built datum.
;;;
;;; The LATER cr.org review (of commit imp-9 itself) adds 1 observable:
;;;   F4 mode `control' pins `let parallel-init: 1'.  `let' maps EVERY
;;;      init BEFORE it binds any name, so the 2nd INIT reads the OUTER
;;;      value and not the 1st binding.  That is parallel binding, and
;;;      before this check only the `let*' order was pinned.
;;;
;;; The plain-guile values are measured by test/m60/probe-imp3.scm as a
;;; `guile -L mod' child process with GUILE_AUTO_COMPILE=0 -- one MODE
;;; per child.  Mode `control' is NEW here, and it is named in the
;;; `cells|provide|...' list of the mode error message.
;;; `elisp-loader-eval' is NOT in the #export list of (emacs loader), so
;;; the fixture gets it with `module-ref'.
;;;
;;; The 3 recorded FIRST STOPS of brief.org section 3 are real `.el'
;;; files on the plain path, and NONE of the 3 is `cond', `let*' or
;;; `while': the files stop on an EARLIER missing cell (that is the
;;; stated deviation from the row map).
;;;
;;; This corpus reads TRACKED files only.  It does NOT read docs/.
;;; A read error is a real error, never a silent pass.  An absent TRACKED
;;; file is a real FAIL.  A missing `guile' binary is an explicit INFO
;;; skip, never a pass: `m60-imp9--check' routes the marker
;;; `m60-imp9-prog-absent' to `m60-imp9--info-skip', and `m60-imp9--all'
;;; carries that marker through a composite check.
;;;
;;; MEASURED total on this host 2026-10-21: 49 registered checks (S1 9,
;;; S2 6, S3 13, S4 7, S5 4, S6 3, S7 7) plus the group-total deftest =
;;; 50 ERT tests.

(princ "=== m60 imp-9 cond/let*/while suite ===\n")

(require 'imp-ert-report)

(defvar m60-imp9--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))
(defvar m60-imp9--registered 0
  "Total number of checks this corpus has registered.")
(defvar m60-imp9--group nil
  "The group that `m60-imp9--check' counts into: `s1' .. `s7', or nil.")
(defvar m60-imp9--counts nil
  "Alist of (GROUP . COUNT) for the registered checks.")
(defvar m60-imp9--probe-cache nil
  "Alist of (MODE . RESULT) of the plain-guile probe runs of this corpus.
A mode is measured once per corpus run, so a group starts one child
process, not one per check.")

(defun m60-imp9--group-count (group)
  "Number of checks registered so far in GROUP."
  (or (cdr (assq group m60-imp9--counts)) 0))

(defun m60-imp9--bump-group ()
  "Count one check into `m60-imp9--group'."
  (when m60-imp9--group
    (let ((cell (assq m60-imp9--group m60-imp9--counts)))
      (if cell
          (setcdr cell (1+ (cdr cell)))
        (push (cons m60-imp9--group 1) m60-imp9--counts)))))

;;; --- tracked-file helpers (the imp-1 / imp-4 / imp-6 / imp-7 idioms) --

(defun m60-imp9--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
the symbol `m60-imp9-absent' when REL does not exist.  `case-fold-search'
is bound to nil: the elisp default folds case and inflates a count."
  (let ((path (expand-file-name rel m60-imp9--root)))
    (if (not (file-exists-p path))
        'm60-imp9-absent
      (with-temp-buffer
        (insert-file-contents path)
        (let ((case-fold-search nil))
          (funcall fn))))))

(defun m60-imp9--holds-all (rel needles)
  "Non-nil when the TRACKED file REL holds every NEEDLE.  An absent file
fails the check."
  (m60-imp9--with rel
    (lambda ()
      (let ((all t))
        (dolist (needle needles)
          (goto-char (point-min))
          (unless (search-forward needle nil t) (setq all nil)))
        all))))

(defun m60-imp9--holds-none (rel needles)
  "Non-nil when the TRACKED file REL holds NO needle of NEEDLES."
  (m60-imp9--with rel
    (lambda ()
      (let ((none t))
        (dolist (needle needles)
          (goto-char (point-min))
          (when (search-forward needle nil t) (setq none nil)))
        none))))

(defun m60-imp9--ordered-p (rel needles)
  "Non-nil when the TRACKED file REL holds every NEEDLE in the GIVEN
ORDER: each search starts after the previous match."
  (m60-imp9--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((all t))
        (dolist (needle needles)
          (when all
            (unless (search-forward needle nil t) (setq all nil))))
        all))))

(defun m60-imp9--lines (rel)
  "Count the NEWLINES of REL, the unit of `wc -l'."
  (m60-imp9--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (search-forward "\n" nil t) (setq n (1+ n)))
        n))))

(defun m60-imp9--grep-c (rel regexp)
  "Count the LINES of REL that match REGEXP, the unit of `grep -c'."
  (m60-imp9--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (not (eobp))
          (when (re-search-forward regexp (line-end-position) t)
            (setq n (1+ n)))
          (forward-line 1))
        n))))

(defun m60-imp9--literal-lines (rel needle)
  "Count the LINES of REL that hold NEEDLE as a LITERAL substring.  Use
this helper and not `m60-imp9--grep-c' where NEEDLE holds a regexp
metacharacter: `?' and `*' are operators of the search syntax."
  (m60-imp9--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (not (eobp))
          (when (search-forward needle (line-end-position) t)
            (setq n (1+ n)))
          (forward-line 1))
        n))))

(defun m60-imp9--line-of (rel needle)
  "The 1-BASED LINE number of the FIRST line of REL that holds NEEDLE as
a LITERAL substring, or nil.  The unit is a LINE of the file, the same
unit that a `:NNN' anchor of a review uses."
  (m60-imp9--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0) (found nil))
        (while (and (not found) (not (eobp)))
          (setq n (1+ n))
          (when (search-forward needle (line-end-position) t) (setq found n))
          (forward-line 1))
        found))))

(defun m60-imp9--literal-lines-in-eval-form (needle)
  "Count the LINES of `elisp-loader-eval-form' that hold NEEDLE as a
LITERAL substring, or return the symbol `m60-imp9-absent'.  The region is
SCOPED: a file-wide pin turns a check of row 28a red when an UNRELATED
row adds the same text, and the red check then names the wrong cause.
The form starts at `(define (elisp-loader-eval-form form)' and ends at
the next top-level `(define'."
  (m60-imp9--with "mod/emacs/loader.scm"
    (lambda ()
      (goto-char (point-min))
      (if (not (search-forward "(define (elisp-loader-eval-form form)" nil t))
          nil
        (let ((start (line-beginning-position)))
          (if (re-search-forward "^(define " nil t)
              (narrow-to-region start (line-beginning-position))
            (narrow-to-region start (point-max)))
          (goto-char (point-min))
          (let ((n 0))
            (while (not (eobp))
              (when (search-forward needle (line-end-position) t)
                (setq n (1+ n)))
              (forward-line 1))
            n))))))

;;; --- the plain-guile probe runner -----------------------------------

(defun m60-imp9--probe-1 (mode)
  "Run test/m60/probe-imp3.scm in MODE as a `guile -L mod' child
process, with GUILE_AUTO_COMPILE=0 and GUILEMACS_ROOT set, and with
`default-directory' at the repo root.  Return (EXIT . OUTPUT), where
OUTPUT holds stdout AND stderr, or the symbol `m60-imp9-prog-absent'
when the `guile' binary is not on PATH."
  (if (not (executable-find "guile"))
      'm60-imp9-prog-absent
    (let ((buf (get-buffer-create " *m60-imp9-probe*"))
          (default-directory m60-imp9--root)
          (process-environment
           (append (list (concat "GUILEMACS_ROOT=" m60-imp9--root)
                         "GUILE_AUTO_COMPILE=0")
                   process-environment)))
      (unwind-protect
          (progn
            (with-current-buffer buf (erase-buffer))
            (let ((exit (apply #'call-process
                               "guile" nil buf nil
                               (list "-L" "mod"
                                     "test/m60/probe-imp3.scm"
                                     mode))))
              (cons exit (with-current-buffer buf
                           (buffer-substring-no-properties
                            (point-min) (point-max))))))
        (kill-buffer buf)))))

(defun m60-imp9--probe (mode)
  "The cached result of `m60-imp9--probe-1' for MODE."
  (let ((cell (assoc mode m60-imp9--probe-cache)))
    (if cell
        (cdr cell)
      (let ((result (m60-imp9--probe-1 mode)))
        (push (cons mode result) m60-imp9--probe-cache)
        result))))

(defun m60-imp9--probe-raw (mode)
  "The OUTPUT of the probe MODE whatever the exit status is, or the
marker `m60-imp9-prog-absent'.  Mode `registration' raises on purpose,
so its output is only readable this way."
  (let ((result (m60-imp9--probe mode)))
    (cond
     ((eq result 'm60-imp9-prog-absent) result)
     ((consp result) (cdr result))
     (t nil))))

(defun m60-imp9--probe-output (mode)
  "The OUTPUT of the probe MODE when the child exited 0, else nil.  When
the `guile' binary is absent, the marker `m60-imp9-prog-absent' is
returned instead of nil, so the caller can SKIP and not pass or fail."
  (let ((result (m60-imp9--probe mode)))
    (cond
     ((eq result 'm60-imp9-prog-absent) result)
     ((and (consp result) (eql 0 (car result))) (cdr result))
     (t nil))))

(defun m60-imp9--probe-line (mode line)
  "Non-nil when the probe MODE printed LINE as one WHOLE line and the
child exited 0.  A substring match is NOT enough: a line pin holds the
whole line, so a changed value can not hide inside it."
  (let ((out (m60-imp9--probe-output mode)))
    (cond
     ((eq out 'm60-imp9-prog-absent) out)
     ((not (stringp out)) nil)
     (t (with-temp-buffer
          (insert "\n" out "\n")
          (goto-char (point-min))
          (and (search-forward (concat "\n" line "\n") nil t) t))))))

(defun m60-imp9--probe-holds (mode needle)
  "Non-nil when the OUTPUT of the probe MODE holds NEEDLE (a substring
pin; use it only where an address sits in the text)."
  (let ((out (m60-imp9--probe-output mode)))
    (cond
     ((eq out 'm60-imp9-prog-absent) out)
     ((not (stringp out)) nil)
     (t (with-temp-buffer
          (insert out)
          (goto-char (point-min))
          (and (search-forward needle nil t) t))))))

(defun m60-imp9--probe-holds-none (mode needle)
  "Non-nil when the OUTPUT of the probe MODE holds NO NEEDLE."
  (let ((out (m60-imp9--probe-output mode)))
    (cond
     ((eq out 'm60-imp9-prog-absent) out)
     ((not (stringp out)) nil)
     (t (with-temp-buffer
          (insert out)
          (goto-char (point-min))
          (not (search-forward needle nil t)))))))

(defun m60-imp9--probe-raw-holds (mode needle)
  "Non-nil when the RAW output of the probe MODE holds NEEDLE, whatever
the exit status is."
  (let ((out (m60-imp9--probe-raw mode)))
    (cond
     ((eq out 'm60-imp9-prog-absent) out)
     ((not (stringp out)) nil)
     (t (with-temp-buffer
          (insert out)
          (goto-char (point-min))
          (and (search-forward needle nil t) t))))))

(defun m60-imp9--all (&rest values)
  "`and' over the ALREADY-EVALUATED VALUES, with one difference: a
MARKER wins over a nil.  The verdict order matches `m60-imp9--verdict':
the absent FILE marker first (a real FAIL), then the absent `guile'
marker (a skip), then nil (a FAIL), then t (a PASS)."
  (cond
   ((memq 'm60-imp9-absent values) 'm60-imp9-absent)
   ((memq 'm60-imp9-prog-absent values) 'm60-imp9-prog-absent)
   ((memq nil values) nil)
   (t t)))

;;; --- report helpers -------------------------------------------------

(defun m60-imp9--verdict (ok)
  "Classify the value OK of one check: `pass', `fail', `absent' (the
TRACKED file is missing -- a real FAIL), or `skip' (the `guile' binary is
not on PATH -- never a pass)."
  (cond
   ((eq ok 'm60-imp9-prog-absent) 'skip)
   ((eq ok 'm60-imp9-absent) 'absent)
   (ok 'pass)
   (t 'fail)))

(defun m60-imp9--check (name ok)
  "Report and register one check.  An absent TRACKED file prints FAIL and
registers a failing ERT test; an absent `guile' binary prints INFO and
registers a controlled ERT skip -- never a pass."
  (let ((verdict (m60-imp9--verdict ok)))
    (cond
     ((eq verdict 'skip)
      (m60-imp9--info-skip name "no guile binary on PATH"))
     ((eq verdict 'absent)
      (princ (format "FAIL m60/imp9/%s (source file absent)\n" name))
      (setq m60-imp9--registered (1+ m60-imp9--registered))
      (m60-imp9--bump-group)
      (imp-register-bool-as-ert-test (format "m60-imp9/%s" name) nil))
     (t
      (princ (format "%s m60/imp9/%s\n"
                     (if (eq verdict 'pass) "PASS" "FAIL") name))
      (setq m60-imp9--registered (1+ m60-imp9--registered))
      (m60-imp9--bump-group)
      (imp-register-bool-as-ert-test (format "m60-imp9/%s" name)
                                     (eq verdict 'pass))))))

(defun m60-imp9--info-skip (name reason)
  "Register one explicit INFO skip, counted into the current group.  A
host limit is a skip, never a pass."
  (princ (format "INFO m60/imp9/%s %s\n" name reason))
  (setq m60-imp9--registered (1+ m60-imp9--registered))
  (m60-imp9--bump-group)
  (imp-register-skip-as-ert-test (format "m60-imp9/%s" name) reason))

;;; --- S1. The 3 branch sources ---------------------------------------

(setq m60-imp9--group 's1)

;; 1 branch per name, MEASURED with `grep -c' (unit LINES): 1 each.
(m60-imp9--check "s1/one-branch-each"
                 (m60-imp9--all
                  (eql 1 (m60-imp9--literal-lines
                          "mod/emacs/loader.scm" "((eq? head 'cond)"))
                  (eql 1 (m60-imp9--literal-lines
                          "mod/emacs/loader.scm" "((eq? head 'let*)"))
                  (eql 1 (m60-imp9--literal-lines
                          "mod/emacs/loader.scm" "((eq? head 'while)"))))

;; The `cond' branch uses the shared helpers and no new evaluator: the
;; clause loop, the 2 sequence calls and the shared truth test.
(m60-imp9--check "s1/cond-branch-source"
                 (m60-imp9--all
                  (m60-imp9--ordered-p
                   "mod/emacs/loader.scm"
                   '("((eq? head 'cond)"
                     "(let loop ((clauses (cdr form)))"
                     "(let ((value (elisp-loader-eval (car clause))))"
                     "(elisp-loader-truthy? value)"
                     "(elisp-loader-eval-seq (cdr clause))"))
                  (eql 2 (m60-imp9--literal-lines
                          "mod/emacs/loader.scm"
                          "(elisp-loader-eval-seq (cdr clause))"))))

;; L19: the 2 catch-all names are tested as SYMBOLS, BEFORE the
;; evaluation of the test.  The reverse order would raise
;; `void-variable' on an unbound `otherwise'.
(m60-imp9--check "s1/cond-catch-all-before-eval"
                 (m60-imp9--ordered-p
                  "mod/emacs/loader.scm"
                  '("((eq? head 'cond)"
                    "(memq (car clause) '(t otherwise))"
                    "(let ((value (elisp-loader-eval (car clause))))")))

;; The `let*' branch reuses `elisp-loader-bind-thunk' and the
;; `dynamic-wind' undo path of `let', and it returns the last body value.
(m60-imp9--check "s1/let*-branch-source"
                 (m60-imp9--all
                  (m60-imp9--ordered-p
                   "mod/emacs/loader.scm"
                   '("((eq? head 'let*)"
                     "(let ((body (cddr form))"
                     "(dynamic-wind"
                     "(if (pair? bindings)"
                     "(elisp-loader-eval-seq body)"
                     "(for-each (lambda (thunk) (thunk)) restore)"))
                  (eql 3 (m60-imp9--literal-lines
                          "mod/emacs/loader.scm"
                          "(for-each (lambda (thunk) (thunk)) restore)"))))

;; The bindings are made ONE AT A TIME: the INIT is evaluated INSIDE the
;; binding loop.  A pre-evaluating `map' would evaluate every INIT in the
;; OUTER environment, and the 2nd INIT would then read the OUTER name.
(m60-imp9--check "s1/let*-binds-in-order"
                 (m60-imp9--all
                  (m60-imp9--ordered-p
                   "mod/emacs/loader.scm"
                   '("((eq? head 'let*)"
                     "(let loop ((bindings (cadr form)))"
                     "(cons (elisp-loader-bind-thunk"
                     "(elisp-loader-binding-init (car bindings))"))
                  ;; MEASURED 1 LINE: the pre-evaluating `map' belongs to
                  ;; the `let' branch ONLY, never to `let*'.
                  (eql 1 (m60-imp9--literal-lines
                          "mod/emacs/loader.scm"
                          "(map elisp-loader-binding-init"))))

;; cr.org F3: the binding loop of BOTH branches runs INSIDE the
;; `dynamic-wind' body, so an INIT that raises still restores the names
;; that are bound already.  MEASURED: 2 LINES hold `(set! restore'.
(m60-imp9--check "s1/binding-loop-inside-dynamic-wind"
                 (m60-imp9--all
                  (eql 2 (m60-imp9--literal-lines
                          "mod/emacs/loader.scm"
                          "(set! restore"))
                  (m60-imp9--ordered-p
                   "mod/emacs/loader.scm"
                   '("((eq? head 'let)"
                     "(dynamic-wind"
                     "(set! restore"))
                  (m60-imp9--ordered-p
                   "mod/emacs/loader.scm"
                   '("((eq? head 'let*)"
                     "(dynamic-wind"
                     "(set! restore"))))

;; cr.org F5: a BARE SYMBOL binding binds elisp nil.  The 2 shape helpers
;; are SHAPE readers, not a 2nd undo path.
(m60-imp9--check "s1/bare-symbol-binding-shape"
                 (m60-imp9--all
                  (eql 1 (m60-imp9--literal-lines
                          "mod/emacs/loader.scm"
                          "(define (elisp-loader-binding-name binding)"))
                  (m60-imp9--holds-all
                   "mod/emacs/loader.scm"
                   '("(if (symbol? binding) binding (car binding))"))
                  (eql 1 (m60-imp9--literal-lines
                          "mod/emacs/loader.scm"
                          "(define (elisp-loader-binding-init binding)"))))

;; L17: `while' is a NAMED LET loop, not Guile `while'.  The test comes
;; before the body, and the value is always #nil.
(m60-imp9--check "s1/while-branch-source"
                 (m60-imp9--all
                  (m60-imp9--ordered-p
                   "mod/emacs/loader.scm"
                   '("((eq? head 'while)"
                     "(let loop ()"
                     "(elisp-loader-truthy? (elisp-loader-eval (cadr form)))"
                     "(begin (elisp-loader-eval-seq (cddr form)) (loop))"
                     "#nil)"))
                  (m60-imp9--holds-none
                   "mod/emacs/loader.scm"
                   '("(while (elisp-loader-truthy?"))))

;; The 3 names are SPECIAL FORMS, not function cells: `init-loader' must
;; get NO new install site.  MEASURED: 0 sites in loader.scm and 0 in
;; the prelude.
(m60-imp9--check "s1/zero-install-sites"
                 (m60-imp9--all
                  (m60-imp9--holds-none
                   "mod/emacs/loader.scm"
                   '("(set-symbol-function! 'cond"
                     "(set-symbol-function! 'let*"
                     "(set-symbol-function! 'while"))
                  (m60-imp9--holds-none
                   "prelude/load.scm"
                   '("set-symbol-function! 'cond"
                     "set-symbol-function! 'let*"
                     "set-symbol-function! 'while"))))

;;; --- S2. The branch order and the neighbours ------------------------

(setq m60-imp9--group 's2)

;; The row-map order is FIXED by brief.org section 4: `cond', then
;; `let*', then `while', AFTER `defmacro' and BEFORE the final `else'.
(m60-imp9--check "s2/ordered-after-defmacro-before-else"
                 (m60-imp9--ordered-p
                  "mod/emacs/loader.scm"
                  '("((eq? head 'defmacro)"
                    "((eq? head 'cond)"
                    "((eq? head 'let*)"
                    "((eq? head 'while)"
                    "(else"
                    "(throw 'void-function head)")))

;; `defun' still writes the elisp function cell and `defmacro' still
;; stores the expander: the 3 new branches sit BETWEEN them and the
;; `else', and neither store moved.
(m60-imp9--check "s2/neighbours-untouched"
                 (m60-imp9--all
                  ;; MEASURED 2 LINES: the `defmacro' branch and the
                  ;; `elisp-loader-macro-drop!' helper (the imp-7 value).
                  (eql 2 (m60-imp9--literal-lines
                          "mod/emacs/loader.scm"
                          "(set! elisp-loader-macro-table"))
                  (eql 1 (m60-imp9--literal-lines
                          "mod/emacs/loader.scm"
                          "(elisp-loader-macro-drop! (cadr form))"))))

;; The `else' body is NOT touched: its macro-table lookup, its function
;; cell call and its `void-function' throw stay as they were.  The
;; counts are SCOPED to the form.
(m60-imp9--check "s2/else-body-untouched"
                 (m60-imp9--all
                  (eql 1 (m60-imp9--literal-lines-in-eval-form
                          "(elisp-loader-macro-ref head)"))
                  (eql 1 (m60-imp9--literal-lines-in-eval-form
                          "(elisp-loader-apply (symbol-function head)"))
                  (eql 1 (m60-imp9--literal-lines-in-eval-form
                          "(throw 'void-function head)"))))

;; `elisp-loader-eval' and the argument evaluation are unchanged.
;; MEASURED: 2 LINES hold `(elisp-loader-eval-seq (cdr form))' -- the
;; `progn' branch and the `eval-when-compile' branch -- because the 3 new
;; branches pass `(cdr clause)', `body' and `(cddr form)'.
(m60-imp9--check "s2/eval-unchanged"
                 (m60-imp9--all
                  (eql 1 (m60-imp9--literal-lines
                          "mod/emacs/loader.scm"
                          "(define (elisp-loader-eval form)"))
                  (eql 1 (m60-imp9--literal-lines
                          "mod/emacs/loader.scm"
                          "((pair? form) (elisp-loader-eval-form form))"))
                  (eql 1 (m60-imp9--literal-lines
                          "mod/emacs/loader.scm"
                          "(define (elisp-loader-apply fn args)"))
                  ;; M60 imp-12 RE-PIN: 2 -> 3 LITERAL LINES.  The
                  ;; `eval-and-compile' branch of row 31 adds the 3rd.
                  (eql 3 (m60-imp9--literal-lines
                          "mod/emacs/loader.scm"
                          "(elisp-loader-eval-seq (cdr form))"))))

;; `let*' reuses the `let' undo path.  MEASURED: 4 LINES hold
;; `elisp-loader-bind-thunk' -- the definition, the `let' branch, the
;; `let*' branch and `elisp-loader-bind-params!' -- and 3 LINES hold the
;; exit form (the 2 dynamic-wind branches and the procedure maker).
(m60-imp9--check "s2/let*-reuses-let-undo-path"
                 (m60-imp9--all
                  (eql 4 (m60-imp9--literal-lines
                          "mod/emacs/loader.scm"
                          "(elisp-loader-bind-thunk"))
                  (eql 3 (m60-imp9--literal-lines
                          "mod/emacs/loader.scm"
                          "(for-each (lambda (thunk) (thunk)) restore)"))
                  (m60-imp9--ordered-p
                   "mod/emacs/loader.scm"
                   '("(define (elisp-loader-bind-thunk name value)"
                     "((eq? head 'let)"
                     "((eq? head 'let*)"))))

;; 1 binding helper is enough (brief.org section 4.2): no 2nd helper.
(m60-imp9--check "s2/one-bind-helper"
                 (m60-imp9--all
                  (eql 1 (m60-imp9--literal-lines
                          "mod/emacs/loader.scm"
                          "(define (elisp-loader-bind-thunk name value)"))
                  (eql 1 (m60-imp9--literal-lines
                          "mod/emacs/loader.scm"
                          "(define (elisp-loader-bind-params! params args)"))
                  (m60-imp9--holds-none
                   "mod/emacs/loader.scm"
                   '("(define (elisp-loader-bind-let*"))))

;;; --- S3. The observables (live `guile' child, mode `control') --------

(setq m60-imp9--group 's3)

;; The catch-all `t' clause, the `otherwise' clause and the FIRST match.
(m60-imp9--check "s3/cond-catch-all"
                 (m60-imp9--all
                  (m60-imp9--probe-line "control" "cond t-clause: 2")
                  (m60-imp9--probe-line "control" "cond otherwise-clause: 2")
                  (m60-imp9--probe-line "control" "cond first-match-wins: a")))

(m60-imp9--check "s3/cond-no-match-or-empty"
                 (m60-imp9--all
                  (m60-imp9--probe-line "control" "cond no-match: #nil")
                  (m60-imp9--probe-line "control" "cond empty: #nil")))

;; A clause with a TEST only returns the TEST VALUE, and #nil and not a
;; Scheme false for a false test.
(m60-imp9--check "s3/cond-test-only"
                 (m60-imp9--all
                  (m60-imp9--probe-line "control" "cond test-only-true: yes")
                  (m60-imp9--probe-line "control" "cond test-only-false: #nil")))

;; The 2nd INIT reads the 1st name: `(2 . 2)', not `(2 . 1)'.
(m60-imp9--check "s3/let*-later-init-sees-earlier"
                 (m60-imp9--all
                  (m60-imp9--probe-line "control"
                                        "let* later-init-sees-earlier: (2 . 2)")
                  (m60-imp9--probe-line "control" "let* body-last-value: last")))

;; L18: dynamic binding.  The outer value 1 is RESTORED after the form.
(m60-imp9--check "s3/let*-restored-after"
                 (m60-imp9--all
                  (m60-imp9--probe-line "control" "let* restored-after: 1")
                  (m60-imp9--probe-line "control" "let* no-init: #nil")))

;; The counter runs 2 times, the walk ends on #nil, and the value is
;; #nil although the body ran.
(m60-imp9--check "s3/while-counter"
                 (m60-imp9--all
                  (m60-imp9--probe-line "control" "while steps: (2 1)")
                  (m60-imp9--probe-line "control" "while rest-after: #nil")
                  (m60-imp9--probe-line "control" "while return: #nil")))

;; A false FIRST test runs the body 0 times, and a 0-form body is legal.
(m60-imp9--check "s3/while-false-first-test"
                 (m60-imp9--all
                  (m60-imp9--probe-line "control"
                                        "while false-first-test return: #nil")
                  (m60-imp9--probe-line "control"
                                        "while false-first-test body-runs: #nil")
                  (m60-imp9--probe-line "control" "while empty-body: #nil")))

;; The 3 recorded FIRST STOPS of brief.org section 3.  None of the 3 is
;; `cond', `let*' or `while': that is the stated deviation from the row
;; map.  The lines are the MEASURED stops of this host.
;; M60 imp-10 RE-PIN: `lisp/color.el' now loads to the END in mode
;; `control', because row 29 installs the `/` cell.  The OLD value was
;; `LOAD lisp/color.el: ERROR void-function (/)'.  The other 2 stops were
;; row 30 (`put') and row 31 (`eval-and-compile'); row 30 moved the first
;; of them, and row 31 (M60 imp-12) moved the second one to `defalias'.
(m60-imp9--check "s3/recorded-first-stops"
                 (m60-imp9--all
                  (m60-imp9--probe-line
                   "control"
                   ;; M60 imp-12 RE-PIN: the OLD line was
                   ;; `LOAD lisp/subr.el: ERROR void-function (eval-and-compile)'.
                   ;; Row 31 adds the branch, so the load moves PAST form 1
                   ;; to the NEXT wall, `defalias' at subr.el :29.  `subr.el'
                   ;; does NOT load: a `done' value is a FAIL.
                   "LOAD lisp/subr.el: ERROR void-function (defalias)")
                  ;; M60 imp-11 RE-PIN: the OLD line was
                  ;; `LOAD lisp/calendar/time-date.el: ERROR void-function
                  ;; (put)'.  Row 30 installs the `put' cell, so mode
                  ;; `control' records the NEXT stop of the same chain.
                  (m60-imp9--probe-line
                   "control"
                   "LOAD lisp/calendar/time-date.el: ERROR wrong-type-arg (#f \"Wrong type to apply: ~S\" (#nil) (#nil))")
                  (m60-imp9--probe-line
                   "control"
                   "LOAD lisp/color.el: done")))

;; The mode is registered in the 3 places of the fixture: the header
;; comment, the `case' dispatch and the unknown-mode text.
;; M60 imp-10 RE-PIN: mode `arith' extends the header list and the
;; unknown-mode text, so `control' is no longer the LAST name.  The OLD
;; literals were "`obsolete', or `control'" and "language|obsolete|control)".
;; M60 imp-11 RE-PIN: mode `put' is now the LAST name, so `arith' takes a
;; comma and the unknown-mode text ends with `put'.  The OLD literals
;; were "`obsolete', `control', or `arith'" and
;; "language|obsolete|control|arith)".
;; M60 imp-12 RE-PIN: mode `eac' is now the LAST name, so `put' takes a
;; comma and the unknown-mode text ends with `eac'.  The OLD literals
;; were "`obsolete', `control', `arith', or `put'" and
;; "language|obsolete|control|arith|put)".
(m60-imp9--check "s3/mode-registration"
                 (m60-imp9--all
                  (eql 1 (m60-imp9--literal-lines
                          "test/m60/probe-imp3.scm" "`obsolete', `control', `arith', `put', or `eac'"))
                  (eql 1 (m60-imp9--literal-lines
                          "test/m60/probe-imp3.scm" "((control) (mode-control))"))
                  (eql 1 (m60-imp9--literal-lines
                          "test/m60/probe-imp3.scm" "(define (mode-control)"))
                  (m60-imp9--holds-all
                   "test/m60/probe-imp3.scm"
                   '("language|obsolete|control|arith|put|eac)"))))

;; cr.org F4: a DUPLICATE name gets the OUTER value 0 back, in both
;; branches.  cr.org F3: a raising INIT leaves the OUTER value `outer'.
(m60-imp9--check "s3/restore-order-and-raising-init"
                 (m60-imp9--all
                  (m60-imp9--probe-line "control" "let* duplicate-value: 2")
                  (m60-imp9--probe-line "control" "let* duplicate-after: 0")
                  (m60-imp9--probe-line "control" "let duplicate-value: 2")
                  (m60-imp9--probe-line "control" "let duplicate-after: 0")
                  (m60-imp9--probe-line "control" "let* init-raises: void-variable")
                  (m60-imp9--probe-line "control" "let* leak-after: outer")))

;; cr.org review of imp-9, finding F4: `let' maps EVERY init BEFORE it
;; binds any name, so the 2nd INIT reads the OUTER value 1 and not the
;; 1st binding 2.  That is parallel binding.  Before this check only the
;; `let*' order was pinned.
(m60-imp9--check "s3/let-parallel-init"
                 (m60-imp9--probe-line "control" "let parallel-init: 1"))

;; cr.org F5: a bare-symbol binding binds elisp nil, in both branches.
(m60-imp9--check "s3/bare-symbol-binds-nil"
                 (m60-imp9--all
                  (m60-imp9--probe-line "control" "let* bare-symbol: #nil")
                  (m60-imp9--probe-line "control" "let bare-symbol: #nil")))

;; cr.org F8: the REAL path.  test/m60/fixture-imp9.el is read by the
;; elisp READER and run by the elisp EVALUATOR, and the `setq' side
;; effects are the proof of the 3 forms.
(m60-imp9--check "s3/real-path-fixture"
                 (m60-imp9--all
                  (m60-imp9--probe-line "control" "real load: done")
                  (m60-imp9--probe-line "control" "real cond t-clause: yes")
                  (m60-imp9--probe-line "control"
                                        "real cond otherwise-clause: other")
                  (m60-imp9--probe-line "control" "real cond no-match: #nil")
                  (m60-imp9--probe-line "control"
                                        "real cond test-only: plain-test-value")
                  (m60-imp9--probe-line
                   "control" "real let* later-init-sees-earlier: (inner . inner)")
                  (m60-imp9--probe-line "control" "real let* restored-after: outer")
                  (m60-imp9--probe-line "control" "real let* bare-symbol: #nil")
                  (m60-imp9--probe-line "control" "real while steps: (2 1)")
                  (m60-imp9--probe-line "control" "real while return: #nil")))

;; The fixture is a TRACKED file with the 3 forms in it.
(m60-imp9--check "s3/real-path-fixture-tracked"
                 (m60-imp9--all
                  (m60-imp9--holds-all
                   "test/m60/fixture-imp9.el"
                   '("(cond (nil 'no) (t 'yes))"
                     "(let* (m60-fixture-q) m60-fixture-q)"
                     "(while m60-fixture-rest"))))

;;; --- S4. No regression on the 11 older modes ------------------------

(setq m60-imp9--group 's4)

(m60-imp9--check "s4/cells-unchanged"
                 (m60-imp9--all
                  (m60-imp9--probe-line "cells" "EMPTY-CELLS: ()")
                  (m60-imp9--probe-line
                   "cells" "UNGUARDED: load=#t autoload-do-load=#t")
                  (m60-imp9--probe-line
                   "cells"
                   (concat "VARS: load-path=#t load-suffixes=#t"
                           " load-file-rep-suffixes=#t load-read-function=#t"))
                  (m60-imp9--probe-line "cells" "ASYM: require=#t provide=#t")
                  (m60-imp9--probe-line "cells" "LOAD lisp/cdl.el: done")
                  (m60-imp9--probe-line "cells" "LOAD lisp/obarray.el: done")
                  (m60-imp9--probe-line "cells" "LOAD lisp/hex-util.el: done")
                  (m60-imp9--probe-line "cells" "features: (cdl)")
                  (m60-imp9--probe-line "cells" "FEATURES-BOUND: #t")))

;; Row 25 is STILL the one wall: `subdirs.el' stops at the missing cell.
(m60-imp9--check "s4/row-25-still-open"
                 (m60-imp9--probe-line
                  "cells"
                  "LOAD lisp/subdirs.el: ERROR void-function (normal-top-level-add-to-load-path)"))

(m60-imp9--check "s4/stubs-blockers"
                 (m60-imp9--all
                  (m60-imp9--probe-line "stubs" "stub-provide / cdl: done")
                  (m60-imp9--probe-line "stubs" "stub-defconst / obarray: done")
                  (m60-imp9--probe-line
                   "stubs" "stub-eval-when-compile / hex-util: done")
                  (m60-imp9--probe-line "stubs" "stub-ntl / subdirs: done")))

(m60-imp9--check "s4/provide-and-require"
                 (m60-imp9--all
                  (m60-imp9--probe-line "provide" "LOAD cdl: done")
                  (m60-imp9--probe-line "provide" "require-fbound: #t")
                  (m60-imp9--probe-line "require" "REQUIRE cdl: cdl")
                  (m60-imp9--probe-line "require" "REQUIRE-NOERROR: #nil")))

(m60-imp9--check "s4/controls-unchanged"
                 (m60-imp9--all
                  (m60-imp9--probe-line "negative" "features-bound: #f")
                  (m60-imp9--probe-holds "negative" "LOAD cdl: ERROR wrong-type-arg")
                  (m60-imp9--probe-holds-none "negative" "void-function")
                  (m60-imp9--probe-line "noboot" "features-bound: #f")
                  (m60-imp9--probe-holds "noboot" "Wrong type to apply")))

(m60-imp9--check "s4/defs-and-macros-unchanged"
                 (m60-imp9--all
                  (m60-imp9--probe-line "defs" "defconst value: 2")
                  (m60-imp9--probe-line "defs" "defvar no-init bound: #f")
                  (m60-imp9--probe-line "macros" "defmacro fbound: #f")
                  (m60-imp9--probe-line "macros" "defun shadow call: 9")
                  (m60-imp9--probe-line
                   "macros" "eval-when-compile form1 ret: num-to-hex-char")))

;; Row 27 keeps its 2 observables, row 26 keeps its blocker, and the
;; language object still resolves.  Mode `registration' raises on
;; purpose, so its output is read raw.
(m60-imp9--check "s4/obsolete-language-registration"
                 (m60-imp9--all
                  (m60-imp9--probe-line "obsolete" "RETURN: obarray-default-size")
                  (m60-imp9--probe-line
                   "obsolete"
                   (concat "MARK: (\"obarrays now grow automatically.\""
                           " #nil \"30.1\")"))
                  (m60-imp9--probe-raw-holds "registration"
                                             "Unbound variable: mapcar")
                  (m60-imp9--probe-line "language" "LANGUAGE-NAME: emacs-elisp")))

;;; --- S5. The re-measured surface ------------------------------------

;; Unit: NEWLINES (`wc -l'), MEASURED 2026-10-21 after imp-9:
;; loader.scm 1,409 -> 1,480 (the L16 ... L20 limit block, the 3 branches
;; and their comments) -> 1,511 (the cr.org F3/F4/F5 fix, L21 and the
;; real-path section of mode `control'); utils.scm 640 UNCHANGED;
;; prelude/load.scm 229 UNCHANGED; probe-imp3.scm 471 -> 535 (mode
;; `control', its comment block, 1 dispatch clause, 1 mode name and 1
;; header line) -> 584 (the cr.org fix observables and the real path)
;; -> 591 (cr.org F4 of the imp-9 review: the `let parallel-init'
;; observable, its comment and its `defconst').
(setq m60-imp9--group 's5)

;; M60 imp-10 RE-PIN: row 29 adds 2 `#:use-module' forms and 15
;; guarded installs to loader.scm -- 1,511 -> 1,588 LINES (wc -l) and
;; 23 / 19 -> 38 / 34 LINES (grep -c) -- and mode `arith' to
;; test/m60/probe-imp3.scm (591 -> 691 LINES).  OLD VALUES are the
;; cells that the numbers above replace.
(m60-imp9--check "s5/line-counts"
                 (m60-imp9--all
;; M60 imp-11 RE-PIN: loader.scm 1,588 -> 1,620 LINES (OLD value 1,588).
                  ;; M60 imp-12 RE-PIN: loader.scm 1,620 -> 1,642 LINES (OLD value 1,620).
                  (eql 1642 (m60-imp9--lines "mod/emacs/loader.scm"))
                  (eql 640 (m60-imp9--lines "mod/emacs/utils.scm"))
                  (eql 229 (m60-imp9--lines "prelude/load.scm"))
;; M60 imp-11 RE-PIN: probe-imp3.scm 691 -> 789 LINES (OLD value 691).
                  ;; M60 imp-12 RE-PIN: probe-imp3.scm 789 -> 825 LINES (OLD value 789).
                  (eql 825 (m60-imp9--lines "test/m60/probe-imp3.scm"))
                  (eql 32 (m60-imp9--lines "test/m60/fixture-imp9.el"))))

;; Unit: LINES (`grep -c'), MEASURED 2026-10-21: 23 / 19 / 9, the imp-8
;; values, UNCHANGED.  A branch adds no install site and no FIX marker:
;; these 3 counts are the DESIGN GUARD of row 28a.
;; M60 imp-10 RE-PIN: row 29 adds 2 `#:use-module' forms and 15
;; guarded installs to loader.scm -- 1,511 -> 1,588 LINES (wc -l) and
;; 23 / 19 -> 38 / 34 LINES (grep -c) -- and mode `arith' to
;; test/m60/probe-imp3.scm (591 -> 691 LINES).  OLD VALUES are the
;; cells that the numbers above replace.
(m60-imp9--check "s5/grep-c-counts"
;; M60 imp-11 RE-PIN: `symbol-fbound?` 38 -> 39 LINES (OLD value 38).
                 (and (eql 39 (m60-imp9--grep-c "mod/emacs/loader.scm"
                                                "symbol-fbound?"))
;; M60 imp-11 RE-PIN: `set-symbol-function!` 34 -> 35 LINES (OLD value 34).
                      (eql 35 (m60-imp9--grep-c "mod/emacs/loader.scm"
                                                "set-symbol-function!"))
                      (eql 9 (m60-imp9--grep-c "mod/emacs/loader.scm"
                                               "FIX-.*guilemacs"))))

;; The `lookup-language' site moved: 1,266 at the base state, 1,337 after
;; the row-28a branches, 1,368 after the cr.org fix.
;; Unit: LINE (1-based) of mod/emacs/loader.scm.
;; M60 imp-10 RE-PIN: row 29 adds 2 `#:use-module' forms and 15
;; guarded installs to loader.scm -- 1,511 -> 1,588 LINES (wc -l) and
;; 23 / 19 -> 38 / 34 LINES (grep -c) -- and mode `arith' to
;; test/m60/probe-imp3.scm (591 -> 691 LINES).  OLD VALUES are the
;; cells that the numbers above replace.
;; M60 imp-12 RE-PIN: the row-31 branch and its L27 ... L30 limit block
;; add 22 lines ABOVE the site, so it moves 1,385 -> 1,407.
(m60-imp9--check "s5/lookup-language-line"
                 (eql 1407 (m60-imp9--line-of "mod/emacs/loader.scm"
                                              "(lookup-language 'emacs-elisp)")))

;; The 5 limits of brief.org section 10 are NAMED in the source.  A
;; reader who finds a limit here must not read it as a claim.
(m60-imp9--check "s5/limits-named"
                 (m60-imp9--holds-all
                  "mod/emacs/loader.scm"
                  '("M60 imp-9 LIMITS of row 28a"
                    "L16 `cond' has no `=>' extension"
                    "L17 `while' has no loop limit"
                    "L18 the binding model is DYNAMIC, as for `let' (L3)"
                    "L19 `cond' tests the catch-all SYMBOLS `t' and `otherwise'"
                    "L20 the loader still has no `catch' / `unwind-protect'"
                    "L21 the `cond' clause-shape error is a Guile `misc-error'"
                    "Row 28b (backquote) stays OPEN")))

;;; --- S6. The registration of THIS corpus ----------------------------

(setq m60-imp9--group 's6)

(m60-imp9--check "s6/run-tests-m60-imp9"
                 (m60-imp9--holds-all "tool/run-tests.scm"
                                      '("test/m60/test-m60-imp9.el")))

(m60-imp9--check "s6/imp9-after-imp8"
                 (m60-imp9--ordered-p
                  "tool/run-tests.scm"
                  '("test/m60/test-m60-imp1.el"
                    "test/m60/test-m60-imp2.el"
                    "test/m60/test-m60-imp3.el"
                    "test/m60/test-m60-imp4.el"
                    "test/m60/test-m60-imp5.el"
                    "test/m60/test-m60-imp6.el"
                    "test/m60/test-m60-imp7.el"
                    "test/m60/test-m60-imp8.el"
                    "test/m60/test-m60-imp9.el")))

;; The (m60) group must not take the prelude key: a prelude run would
;; load the prelude BEFORE the corpus and hide a missing boot.
(m60-imp9--check "s6/m60-group-no-prelude"
                 (m60-imp9--all
                  (m60-imp9--holds-all "tool/run-tests.scm" '("(group (m60)"))
                  (m60-imp9--holds-none "tool/run-tests.scm"
                                        '("(group (m60 "))))

;;; --- S7. The guards -------------------------------------------------

(setq m60-imp9--group 's7)

(m60-imp9--check "s7/min-s1-checks-9" (>= (m60-imp9--group-count 's1) 9))
(m60-imp9--check "s7/min-s2-checks-6" (>= (m60-imp9--group-count 's2) 6))
(m60-imp9--check "s7/min-s3-checks-13" (>= (m60-imp9--group-count 's3) 13))
(m60-imp9--check "s7/min-s4-checks-7" (>= (m60-imp9--group-count 's4) 7))
(m60-imp9--check "s7/min-s5-checks-4" (>= (m60-imp9--group-count 's5) 4))
(m60-imp9--check "s7/min-s6-checks-3" (>= (m60-imp9--group-count 's6) 3))

(m60-imp9--check "s7/prog-absent-routes-to-skip"
                 (and (eq 'skip (m60-imp9--verdict 'm60-imp9-prog-absent))
                      (eq 'skip (m60-imp9--verdict
                                 (m60-imp9--all
                                  'm60-imp9-prog-absent
                                  (m60-imp9--probe-line "control"
                                                        "cond empty: #nil"))))
                      (eq 'absent (m60-imp9--verdict 'm60-imp9-absent))
                      (eq 'absent (m60-imp9--verdict
                                   (m60-imp9--all 'm60-imp9-absent t)))
                      (eq 'pass (m60-imp9--verdict t))
                      (eq 'fail (m60-imp9--verdict nil))
                      (eq 'fail (m60-imp9--verdict (m60-imp9--all t nil)))))

;;; --- The group-total check ------------------------------------------

;; MEASURED: 50 registered checks (S1 9, S2 6, S3 14, S4 7, S5 4, S6 3,
;; S7 7) plus this deftest itself = 51 ERT tests.  S3 gained 1 check in
;; the cr.org review fix of imp-9 (finding F4).

(defvar m60-imp9--min-gate-total 51
  "The exact number of m60-imp9 ERT tests: 50 registered checks (S1 9,
S2 6, S3 14, S4 7, S5 4, S6 3, S7 7) plus the group-total deftest
itself.")

(ert-deftest m60-imp9/gate-m60-total ()
  "The m60-imp9 corpus registers at least its docs-independent floor."
  (should (>= (length (ert-select-tests "^m60-imp9" t))
              m60-imp9--min-gate-total)))

(princ (format "=== m60 imp-9 suite done (%d checks; s1 %d, s2 %d, s3 %d, s4 %d, s5 %d, s6 %d, s7 %d) ===\n"
               m60-imp9--registered
               (m60-imp9--group-count 's1)
               (m60-imp9--group-count 's2)
               (m60-imp9--group-count 's3)
               (m60-imp9--group-count 's4)
               (m60-imp9--group-count 's5)
               (m60-imp9--group-count 's6)
               (m60-imp9--group-count 's7)))
