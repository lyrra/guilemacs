;;; test-m59-imp3.el --- M59 imp-3: the face-attribute-relative-p MOVE.
;;;
;;; M59 imp-3 moves the DECISION of `face-attribute-relative-p' from C
;;; to Scheme (docs/m59-plan.org, brief.org).  The decision is the
;;; 3-branch combine of src/xfaces.c :4187 ... :4192 (M59 imp-3 base):
;;;
;;;   if (EQ (value, Qunspecified) || (EQ (value, QCignore_defface)))
;;;     return Qt;
;;;   else if (EQ (attribute, QCheight))
;;;     return FIXNUMP (value) ? Qnil : Qt;
;;;   else
;;;     return Qnil;
;;;
;;; After the MOVE, C holds only the 3 type tests and ONE dispatcher,
;;; `m59_face_attribute_relative_p_scheme', which resolves the Scheme
;;; procedure `face-attribute-relative-verdict' from ((emacs faces)).
;;; C holds NO fallback verdict.
;;;
;;; The (m59) group of tool/run-tests.scm has NO `prelude' key, so this
;;; group runs through `run-tests-loadup-emacs': the corpus runs INSIDE
;;; the built src/emacs and a direct call to the subr is the REAL path.
;;; There is no child process and no PTY case; the
;;; test/pty-driver.py pin stays 32.
;;;
;;; The measured groups:
;;;
;;;   U1 -- the new module: mod/emacs/faces.scm exists, holds ONE
;;;         #:export entry and ONE procedure definition, is pure (no
;;;         defelisp, no FFI leaf, no set!, no I/O), and prelude/load.scm
;;;         holds exactly ONE (emacs faces) load line, BEFORE the
;;;         `;; initializing emacs modules' message.  U1 holds 6 checks.
;;;   U2 -- the REAL behaviour: one call of the subr per row of the
;;;         8-row truth table, plus the 5 imp-2 controls.  U2 holds 13
;;;         checks.
;;;   U3 -- the C wiring: the dispatcher, its 2 resolve strings, the
;;;         SCM_CALL_3, the 3 type tests that STAY C, the DELETED inline
;;;         decision, the 33 ^DEFUN ( count, the 1 scm_c_public_ref LINE
;;;         in src/xfaces.c, the tree-wide 266 OCCURRENCES, and the
;;;         absence of a C fallback.  U3 holds 8 checks.
;;;   U4 -- the negative control: the Scheme side answers a constant and
;;;         the verdict changes, which shows that C holds no fallback.
;;;         U4 holds 2 checks.
;;;   U5 -- the registration in tool/run-tests.scm.  U5 holds 4 checks.
;;;   U6 -- the guards: one min-count guard per group plus the in-process
;;;         group-total `ert-deftest'.  U6 holds 6 counted checks.
;;;
;;; MEASURED VALUES (2026-10-19, HEAD 2841bc4db + this MOVE, built
;;; src/emacs):
;;;
;;;   (face-attribute-relative-p :height 1.5)                   => t
;;;   (face-attribute-relative-p :height 12)                    => nil
;;;   (face-attribute-relative-p :foreground 'unspecified)       => t
;;;   (face-attribute-relative-p :space-width 1.5)               => nil
;;;   (face-attribute-relative-p nil 1.5)                        => nil
;;;   (face-attribute-relative-p :foreground "red")              => nil
;;;   (face-attribute-relative-p :height 1)                      => nil
;;;   (face-attribute-relative-p :height 'unspecified)           => t
;;;   (face-attribute-relative-p :height :ignore-defface)        => t
;;;   (face-attribute-relative-p :foreground :ignore-defface)    => t
;;;   (face-attribute-relative-p :foreground 'ignore-defface)    => nil
;;;
;;; The negative control (U4), MEASURED on this host with NO rebuild:
;;; the exported name in mod/emacs/faces.scm was renamed for one run, so
;;; `scm_c_public_ref' fails at the first call and the subr SIGNALS.  It
;;; does NOT return a default verdict.  The edit was reverted.
;;; Before the rename: the 3 values were t / nil / t.  With the rename:
;;; (face-attribute-relative-p :height 1.5) raised the exact text
;;;   misc-error: ("public-lookup" "No variable bound to ~s in module ~s"
;;;                (face-attribute-relative-verdict (emacs faces)) #f)
;;; After the revert: the 3 values were t / nil / t again.  So C holds no
;;; fallback (L1).
;;;
;;; This corpus reads TRACKED files only (src/, mod/, prelude/,
;;; tool/run-tests.scm).  It does NOT read docs/ (docs/kb.org
;;; test-must-not-read-docs): a gitignored record can only pass or skip.
;;; src/globals.h is GENERATED and untracked, so this corpus does NOT pin
;;; a line of it.  Every count names its unit: `--grep-c' counts LINES
;;; (the unit of `grep -c') and `--count' counts OCCURRENCES (the unit of
;;; `grep -o | wc -l').
;;;
;;; An absent TRACKED file is a real FAIL, never a pass.  Every check
;;; registers a real ERT test through `imp-register-bool-as-ert-test', so
;;; the harness parses the ERT output and the exit code is correct.

(princ "=== m59 imp-3 face-attribute-relative-p MOVE suite ===\n")

(require 'imp-ert-report)

(defvar m59-imp3--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))
(defvar m59-imp3--registered 0
  "Total number of checks this corpus has registered.")
(defvar m59-imp3--group nil
  "The group that `m59-imp3--check' counts into: `u1' .. `u6', or nil.")
(defvar m59-imp3--counts nil
  "Alist of (GROUP . COUNT) for the registered checks.")

(defun m59-imp3--group-count (group)
  "Number of checks registered so far in GROUP."
  (or (cdr (assq group m59-imp3--counts)) 0))

(defun m59-imp3--bump-group ()
  "Count one check into `m59-imp3--group'."
  (when m59-imp3--group
    (let ((cell (assq m59-imp3--group m59-imp3--counts)))
      (if cell
          (setcdr cell (1+ (cdr cell)))
        (push (cons m59-imp3--group 1) m59-imp3--counts)))))

(defun m59-imp3--exists-p (rel)
  "Non-nil when the TRACKED file REL exists."
  (file-exists-p (expand-file-name rel m59-imp3--root)))

(defun m59-imp3--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
the symbol `m59-imp3-absent' when REL does not exist.  `case-fold-search'
is bound to nil: every pin in this corpus is case-SENSITIVE, like its
grep command."
  (let ((path (expand-file-name rel m59-imp3--root)))
    (if (not (file-exists-p path))
        'm59-imp3-absent
      (with-temp-buffer
        (insert-file-contents path)
        (let ((case-fold-search nil))
          (funcall fn))))))

(defun m59-imp3--contains-p (rel needle)
  "Non-nil when the TRACKED file REL holds NEEDLE."
  (m59-imp3--holds-all rel (list needle)))

(defun m59-imp3--holds-all (rel needles)
  "Non-nil when the TRACKED file REL holds every NEEDLE."
  (m59-imp3--with rel
    (lambda ()
      (let ((all t))
        (dolist (needle needles)
          (goto-char (point-min))
          (unless (search-forward needle nil t) (setq all nil)))
        all))))

(defun m59-imp3--holds-none (rel needles)
  "Non-nil when the TRACKED file REL holds NO needle of NEEDLES."
  (m59-imp3--with rel
    (lambda ()
      (let ((none t))
        (dolist (needle needles)
          (goto-char (point-min))
          (when (search-forward needle nil t) (setq none nil)))
        none))))

(defun m59-imp3--live-p (rel needle)
  "Non-nil when the TRACKED file REL holds NEEDLE on a line that is NOT
a comment line."
  (m59-imp3--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((hit nil))
        (while (and (not hit) (search-forward needle nil t))
          (setq hit (save-excursion
                      (goto-char (line-beginning-position))
                      (not (looking-at-p "[ \t]*;")))))
        hit))))

(defun m59-imp3--ordered-p (rel needles)
  "Non-nil when the TRACKED file REL holds every NEEDLE in the GIVEN
ORDER: each search starts after the previous match."
  (m59-imp3--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((all t))
        (dolist (needle needles)
          (when all
            (unless (search-forward needle nil t) (setq all nil))))
        all))))

(defun m59-imp3--grep-c (rel regexp)
  "Count the LINES of REL that match REGEXP, the unit of `grep -c'."
  (m59-imp3--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (not (eobp))
          (when (re-search-forward regexp (line-end-position) t)
            (setq n (1+ n)))
          (forward-line 1))
        n))))

(defun m59-imp3--count (rel regexp)
  "Count the OCCURRENCES of REGEXP in REL, the unit of
`grep -o | wc -l'.  This is NOT the unit of `grep -c'."
  (m59-imp3--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (re-search-forward regexp nil t) (setq n (1+ n)))
        n))))

(defun m59-imp3--src-public-refs ()
  "Count the OCCURRENCES of `scm_c_public_ref' over the TRACKED files
src/*.[ch] of the tree, the unit of `grep -o ... | wc -l'."
  (let ((dir (expand-file-name "src/" m59-imp3--root))
        (n 0))
    (dolist (f (directory-files dir t "\\.\\(c\\|h\\)\\'"))
      (with-temp-buffer
        (insert-file-contents f)
        (goto-char (point-min))
        (while (re-search-forward "scm_c_public_ref" nil t)
          (setq n (1+ n)))))
    n))

(defun m59-imp3--rel-p (&rest args)
  "Call the real subr `face-attribute-relative-p' with ARGS and return
its value, or the symbol `m59-imp3-call-error' when the call signals."
  (condition-case _err
      (apply #'face-attribute-relative-p args)
    (error 'm59-imp3-call-error)))

(defun m59-imp3--check (name ok)
  "Report and register one check.  OK is a boolean.  An absent TRACKED
file gives the symbol `m59-imp3-absent', which is a FAIL, not a pass."
  (let* ((absent (eq ok 'm59-imp3-absent))
         (pass (and (not absent) (and ok t))))
    (if absent
        (princ (format "FAIL m59/imp3/%s (source file absent)\n" name))
      (princ (format "%s m59/imp3/%s\n" (if pass "PASS" "FAIL") name)))
    (setq m59-imp3--registered (1+ m59-imp3--registered))
    (m59-imp3--bump-group)
    (imp-register-bool-as-ert-test (format "m59-imp3/%s" name) pass)))

;; A missing guile binary is an explicit INFO skip, never a pass.
(defun m59-imp3--info-skip (name reason)
  "Register one explicit INFO skip, counted into the current group."
  (princ (format "INFO m59/imp3/%s %s\n" name reason))
  (setq m59-imp3--registered (1+ m59-imp3--registered))
  (m59-imp3--bump-group)
  (imp-register-skip-as-ert-test (format "m59-imp3/%s" name) reason))

;;; --- U1. The new module and its ONE load line -----------------------

(setq m59-imp3--group 'u1)

(m59-imp3--check "module-present"
                 (m59-imp3--exists-p "mod/emacs/faces.scm"))

;; ONE #:export FORM that names the procedure that C resolves.  M59
;; imp-4 added a second entry (bitmap-spec-verdict) to the same form, so
;; the pin follows that landing: the MOVE this corpus proves is
;; face-attribute-relative-verdict, and that entry must stay.  A drifted
;; name makes `scm_c_public_ref' fail at the first call.
(m59-imp3--check "module-export-entry"
                 (and (eql 1 (m59-imp3--grep-c "mod/emacs/faces.scm"
                                               "^  #:export ("))
                      (m59-imp3--holds-all
                       "mod/emacs/faces.scm"
                       '("(define-module (emacs faces)"
                         "#:export (face-attribute-relative-verdict"
                         "bitmap-spec-verdict))"))))
(m59-imp3--check "module-procedure"
                 (m59-imp3--holds-all
                  "mod/emacs/faces.scm"
                  '("(define (face-attribute-relative-verdict"
                    "(if same-as-unspecified? #t (and height? (not fixnum?)))")))
;; Purity: the procedure is a plain boolean function.  No elisp name
;; registration, no FFI leaf, no mutation, no I/O, no module load.
(m59-imp3--check "module-pure"
                 (and (m59-imp3--holds-none
                       "mod/emacs/faces.scm"
                       '("(defelisp" "(%--" "(set! " "(primitive-load"
                         "(display" "(format"))
                      (eql 1 (m59-imp3--grep-c "mod/emacs/faces.scm"
                                               "^(define (face-"))))
;; ONE load line in prelude/load.scm.  A second line moves the pinned
;; `^(use-modules' count of the older corpora.
(m59-imp3--check "load-line-once"
                 (eql 1 (m59-imp3--grep-c "prelude/load.scm"
                                          "^(use-modules (emacs faces))")))
;; The module must exist BEFORE the runtime starts: the load line is
;; after the (emacs tty-output) line and before the init message.
(m59-imp3--check "load-line-before-init"
                 (m59-imp3--ordered-p
                  "prelude/load.scm"
                  '("(use-modules (emacs tty-output))"
                    "(use-modules (emacs faces))"
                    ";; initializing emacs modules")))

;;; --- U2. The REAL behaviour: the truth table ------------------------

;; The corpus runs inside the built src/emacs, so these are direct calls
;; to the C subr, which now asks Scheme for the verdict.
;;
;; The 8 rows are the full truth table of the old C text:
;;
;;   a  b  c  verdict        row
;;   t  -  -  t              a: the keyword branch wins first
;;   f  t  t  f              a fixnum height is absolute
;;   f  t  f  t              a float height is relative
;;   f  f  -  f              branch 3
;;
;; A CALL THAT PASSES ON ANY INPUT IS NOT A PROOF, so every row is a
;; separate check.

(setq m59-imp3--group 'u2)

(dolist (row '(;; a true: `unspecified', with and without :height.
               ("u2/a-height-unspecified" :height unspecified t)
               ("u2/a-foreground-unspecified" :foreground unspecified t)
               ;; a true: the KEYWORD :ignore-defface (not the symbol).
               ("u2/a-height-ignore-defface-kw" :height :ignore-defface t)
               ("u2/a-foreground-ignore-defface-kw" :foreground
                                                    :ignore-defface t)
               ;; a false, b true: a fixnum height is absolute.
               ("u2/ab-height-fixnum" :height 12 nil)
               ;; a false, b true, c false: a float height is relative.
               ("u2/ab-height-float" :height 1.5 t)
               ;; a false, b false: an absolute value.
               ("u2/non-height-string" :foreground "red" nil)
               ("u2/non-height-float" :space-width 1.5 nil)))
  (m59-imp3--check (nth 0 row)
                   (eq (nth 3 row)
                       (m59-imp3--rel-p (nth 1 row) (nth 2 row)))))

;; The 5 imp-2 controls, unchanged.  They tell the 3 branches apart.
(m59-imp3--check "u2/control-foreground-absolute"
                 (null (m59-imp3--rel-p :foreground "red")))
(m59-imp3--check "u2/control-height-integer-1"
                 (null (m59-imp3--rel-p :height 1)))
(m59-imp3--check "u2/control-height-unspecified"
                 (eq t (m59-imp3--rel-p :height 'unspecified)))
(m59-imp3--check "u2/control-height-ignore-defface"
                 (eq t (m59-imp3--rel-p :height :ignore-defface)))
;; QCignore_defface is the KEYWORD (:ignore-defface, src/xfaces.c :7468),
;; so the SYMBOL misses branch a and falls to the last branch -> nil.
(m59-imp3--check "u2/control-foreground-ignore-defface-symbol"
                 (null (m59-imp3--rel-p :foreground 'ignore-defface)))

;;; --- U3. The C wiring ------------------------------------------------

(setq m59-imp3--group 'u3)

;; The dispatcher: one signature, one resolve site with the module name
;; and the procedure name, and one 3-argument crossing.
(m59-imp3--check "c/dispatcher"
                 (m59-imp3--holds-all
                  "src/xfaces.c"
                  '("m59_face_attribute_relative_p_scheme (bool unspecified_or_ignore,"
                    "static SCM proc = SCM_UNDEFINED;"
                    "if (SCM_UNBNDP (proc))"
                    "return scm_is_true (SCM_CALL_3 (proc,")))

(m59-imp3--check "c/resolve-strings"
                 (m59-imp3--holds-all
                  "src/xfaces.c"
                  '("scm_c_public_ref (\"emacs faces\","
                    "\"face-attribute-relative-verdict\");")))

;; The 3 type tests STAY C.  A type test on a Lisp_Object is a C read;
;; the combine is the decision, and that is in Scheme.
(m59-imp3--check "c/type-tests-stay"
                 (m59-imp3--holds-all
                  "src/xfaces.c"
                  '("bool a = EQ (value, Qunspecified) || EQ (value, QCignore_defface);"
                    "bool b = EQ (attribute, QCheight);"
                    "bool c = FIXNUMP (value);"
                    "return m59_face_attribute_relative_p_scheme (a, b, c);")))

;; The OLD inline decision is GONE.  A MOVE that keeps the decision in C
;; is a passthrough, not a port (docs/kb.org passthrough-leaf-is-not-a-port).
(m59-imp3--check "c/inline-decision-gone"
                 (m59-imp3--holds-none
                  "src/xfaces.c"
                  '("return FIXNUMP (value) ? Qnil : Qt;"
                    "if (EQ (value, Qunspecified) || (EQ (value, QCignore_defface)))")))

;; A resolve site must resolve: no default verdict on the C side.
(m59-imp3--check "c/no-fallback"
                 (m59-imp3--holds-none
                  "src/xfaces.c"
                  '("SCM_UNBNDP (proc)) return"
                    "SCM_UNBNDP (proc))
    return Qnil;"
                    "SCM_UNBNDP (proc))
    return Qt;")))

;; Unit: LINES (`grep -c "^DEFUN ("').
(m59-imp3--check "c/defun-count-33"
                 (eql 33 (m59-imp3--grep-c "src/xfaces.c" "^DEFUN (")))
;; Unit: LINES (`grep -c scm_c_public_ref src/xfaces.c' = 2).  1 after
;; the imp-3 MOVE, 2 after the M59 imp-4 MOVE (the bitmap-spec-p
;; dispatcher resolves ((emacs faces)) one time as well).
(m59-imp3--check "c/xfaces-scm-ref-2"
                 (eql 2 (m59-imp3--grep-c "src/xfaces.c"
                                          "scm_c_public_ref")))
;; Unit: OCCURRENCES (`grep -o scm_c_public_ref src/*.h src/*.c | wc -l').
(m59-imp3--check "c/tree-wide-scm-ref-268"
                 (eql 268 (m59-imp3--src-public-refs)))

;;; --- U4. The negative control ---------------------------------------

;; The Scheme side answers a constant -> the verdict changes.  That is
;; the proof that C no longer decides.  The real-path shape was MEASURED
;; on this host with NO rebuild: the exported name in
;; mod/emacs/faces.scm was renamed for one run, so scm_c_public_ref fails
;; at the first call and the subr SIGNALS.  It does NOT return a default
;; verdict.  The edit was reverted.  The result is written in the (m59)
;; group comment of tool/run-tests.scm.

(setq m59-imp3--group 'u4)

(m59-imp3--check "negative-control-record"
                 (and (m59-imp3--contains-p
                       "tool/run-tests.scm"
                       "Negative control")
                      (m59-imp3--contains-p
                       "tool/run-tests.scm"
                       "the exported name was renamed for one run")
                      (m59-imp3--contains-p
                       "tool/run-tests.scm"
                       "the subr SIGNALS")))

;; The live Scheme half of the control: a fresh guile rebinds the module
;; binding to a constant and the same 3 arguments change verdict.  This
;; proves the Scheme side only.  A missing guile is an explicit INFO
;; skip, never a pass.
(let ((guile (executable-find "guile")))
  (if (not guile)
      (m59-imp3--info-skip "negative-control-scheme-side"
                           "no guile binary on PATH")
    (m59-imp3--check
     "negative-control-scheme-side"
     (let ((out (with-temp-buffer
                  (call-process
                   guile nil t nil
                   "-L" (expand-file-name "mod" m59-imp3--root)
                   "-c"
                   (concat
                    "(use-modules (emacs faces))"
                    "(define before"
                    " (face-attribute-relative-verdict #t #f #f))"
                    "(module-set! (resolve-module '(emacs faces))"
                    " 'face-attribute-relative-verdict"
                    " (lambda (a b c) #f))"
                    "(define after"
                    " (face-attribute-relative-verdict #t #f #f))"
                    "(display (list before after))"))
                  (buffer-string))))
       (equal out "(#t #f)")))))

;;; --- U5. The registration in tool/run-tests.scm ----------------------

(setq m59-imp3--group 'u5)

(m59-imp3--check "reg/imp3-in-m59-group"
                 (eql 1 (m59-imp3--grep-c "tool/run-tests.scm"
                                          "test/m59/test-m59-imp3\\.el")))
(m59-imp3--check "reg/after-imp2"
                 (m59-imp3--ordered-p
                  "tool/run-tests.scm"
                  '("test/m59/test-m59-imp1.el"
                    "test/m59/test-m59-imp2.el"
                    "test/m59/test-m59-imp3.el")))
(m59-imp3--check "reg/imp1-imp2-lines-present"
                 (and (m59-imp3--live-p "tool/run-tests.scm"
                                        "test/m59/test-m59-imp1.el")
                      (m59-imp3--live-p "tool/run-tests.scm"
                                        "test/m59/test-m59-imp2.el")))
(m59-imp3--check "reg/m58-group-present"
                 (m59-imp3--ordered-p "tool/run-tests.scm"
                                      '("(group (m58)" "(group (m59)")))

;;; --- U6. The guards -------------------------------------------------

;; An --filter that matches no group reports exit 0 with 0 tests, so a
;; green m59 gate proves nothing until the checks really register.

(setq m59-imp3--group 'u6)

(m59-imp3--check "min-u1-checks-6" (>= (m59-imp3--group-count 'u1) 6))
(m59-imp3--check "min-u2-checks-13" (>= (m59-imp3--group-count 'u2) 13))
(m59-imp3--check "min-u3-checks-8" (>= (m59-imp3--group-count 'u3) 8))
(m59-imp3--check "min-u4-checks-2" (>= (m59-imp3--group-count 'u4) 2))
(m59-imp3--check "min-u5-checks-4" (>= (m59-imp3--group-count 'u5) 4))
;; This guard reads its OWN group, so the count is still 5 while the
;; check is evaluated: add 1.  MEASURED: without the 1+ the check FAILS.
(m59-imp3--check "min-u6-checks-6" (>= (1+ (m59-imp3--group-count 'u6)) 6))

;;; --- The group-total check ------------------------------------------

(ert-deftest m59-imp3/gate-m59-total ()
  "The m59-imp3 corpus registers exactly the sum of its group counts."
  (should (= (length (ert-select-tests "^m59-imp3" t))
             (+ 1
                (m59-imp3--group-count 'u1)
                (m59-imp3--group-count 'u2)
                (m59-imp3--group-count 'u3)
                (m59-imp3--group-count 'u4)
                (m59-imp3--group-count 'u5)
                (m59-imp3--group-count 'u6)))))

(princ (format "=== m59 imp-3 suite done (%d checks; u1 %d, u2 %d, u3 %d, u4 %d, u5 %d, u6 %d) ===\n"
               m59-imp3--registered
               (m59-imp3--group-count 'u1)
               (m59-imp3--group-count 'u2)
               (m59-imp3--group-count 'u3)
               (m59-imp3--group-count 'u4)
               (m59-imp3--group-count 'u5)
               (m59-imp3--group-count 'u6)))
