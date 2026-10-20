;;; test-m59-imp4.el --- M59 imp-4: the bitmap-spec-p MOVE.
;;;
;;; M59 imp-4 moves the DECISION of `bitmap-spec-p' from C to Scheme
;;; (docs/m59-plan.org, brief.org).  The decision is the accept rule of
;;; src/xfaces.c :825 ... :860 (M59 imp-4 base):
;;;
;;;   STRINGP (object)                          -> t   (a file name)
;;;   CONSP (object)                            -> unpack (WIDTH HEIGHT DATA)
;;;      STRINGP (DATA)
;;;      && 1 <= WIDTH  <= INT_MAX
;;;      && 1 <= HEIGHT <= INT_MAX
;;;      && HEIGHT <= SBYTES (DATA) / ((WIDTH + 7) / 8)  -> t   else nil
;;;   otherwise                                 -> nil
;;;
;;; After the MOVE, C holds the CONSP unpack, the type tests, the BYTE
;;; length SBYTES, and ONE dispatcher, `m59_bitmap_spec_p_scheme', which
;;; resolves the Scheme procedure `bitmap-spec-verdict' from
;;; ((emacs faces)).  C holds NO fallback verdict, and NO copy of the
;;; accept rule (no bytes-per-row arithmetic, no RANGED_FIXNUMP: the 2
;;; bounds belong to the decision).
;;;
;;; The (m59) group of tool/run-tests.scm has NO `prelude' key, so this
;;; group runs through `run-tests-loadup-emacs': the corpus runs INSIDE
;;; the built src/emacs and a direct call to the subr is the REAL path.
;;; There is no child process and no PTY case; the
;;; test/pty-driver.py pin stays 32.
;;;
;;; The measured groups:
;;;
;;;   W1 -- the module: mod/emacs/faces.scm holds 2 #:export entries and
;;;         2 procedure definitions, the new procedure is the pure
;;;         accept rule, and prelude/load.scm still holds 266 lines and
;;;         exactly ONE (emacs faces) load line, plus the BASE cite of the
;;;         deleted C rule.  W1 holds 7 checks.
;;;   W2 -- the REAL behaviour: one call of the subr per row of
;;;         brief.org section 6, plus 3 measured DATA-length controls.
;;;         W2 holds 16 checks.
;;;   W3 -- the C wiring: the dispatcher, its 2 resolve strings, the
;;;         SCM_CALL_4, the type tests and SBYTES that STAY C, the
;;;         DELETED bytes-per-row rule, the DELETED RANGED_FIXNUMP, the 2
;;;         scm_c_public_ref LINES in src/xfaces.c, the tree-wide 267
;;;         OCCURRENCES, the 5 callers, the 33 ^DEFUN ( LINES, and the
;;;         absence of a C fallback, and a guard that no re-pinned check
;;;         name keeps a stale count (cr.org F4).  W3 holds 12 checks.
;;;   W4 -- the negative control: the recorded text plus the live Scheme
;;;         half.  W4 holds 2 checks.
;;;   W5 -- the registration in tool/run-tests.scm.  W5 holds 4 checks.
;;;   W6 -- the guards: one min-count guard per group plus the in-process
;;;         group-total `ert-deftest'.  W6 holds 6 counted checks.
;;;
;;; MEASURED VALUES (2026-10-19, HEAD 0a20145d0 + this MOVE, built
;;; src/emacs, fboundp 'bitmap-spec-p = t).  The LEFT value was measured
;;; on the C path before the edit, the RIGHT value through Scheme after
;;; the edit; the two series are EQUAL:
;;;
;;;   (bitmap-spec-p "x")                          => t     / t
;;;   (bitmap-spec-p (list 8 2 (string 2 0)))      => t     / t
;;;   (bitmap-spec-p (list 8 1 (string 1 0)))      => t     / t
;;;   (bitmap-spec-p (list 8 2 (string 1 0)))      => t     / t
;;;   (bitmap-spec-p (list 9 1 (string 1 0)))      => t     / t
;;;   (bitmap-spec-p (list 8 2))                   => nil   / nil
;;;   (bitmap-spec-p (list 0 1 (string 2 0)))      => nil   / nil
;;;   (bitmap-spec-p (list 8 0 (string 1 0)))      => nil   / nil
;;;   (bitmap-spec-p (list 8.0 2 (string 2 0)))    => nil   / nil
;;;   (bitmap-spec-p (list 8 2 (string 2 0) 'extra)) => t   / t
;;;   (bitmap-spec-p 42)                           => nil   / nil
;;;   (bitmap-spec-p nil)                          => nil   / nil
;;;   (bitmap-spec-p (list 2147483648 1 (string 1 0))) => nil / nil
;;;
;;; Two facts about these rows, MEASURED on this host:
;;;
;;; - `(string 1 0)' is a TWO-character string (chars 1 and 0), so a row
;;;   that was written as "DATA too short" is an EXACT FIT.  Rows 4 and 5
;;;   therefore measure t, not nil.  The pinned value is the measured
;;;   one.  The 3 extra rows XA / XB / XC below are really too short and
;;;   measure nil, so the DATA-length rule stays covered.
;;; - row 13 needs a 64-bit host, and 2147483648 IS a fixnum there.  C
;;;   crosses it as a plain integer and the Scheme bound rejects it, so
;;;   the row measures nil and it is NOT an INFO skip.
;;;
;;; The negative control (W4), MEASURED on this host with NO rebuild:
;;; the exported name in mod/emacs/faces.scm was renamed for one run, so
;;; `scm_c_public_ref' fails at the first call and the subr SIGNALS.  It
;;; does NOT return a default verdict.  The edit was reverted.
;;; Before the rename: (bitmap-spec-p (list 8 2 (string 2 0))) => t.
;;; With the rename the exact text was
;;;   (error "public-lookup" "No variable bound to ~s in module ~s"
;;;          (bitmap-spec-verdict (emacs faces)) #<scheme #f>)
;;; After the revert: t again.  So C holds no fallback (L1).
;;;
;;; This corpus reads TRACKED files only (src/, mod/, prelude/,
;;; tool/run-tests.scm).  It does NOT read docs/ (docs/kb.org
;;; test-must-not-read-docs).  src/globals.h is GENERATED and untracked,
;;; so this corpus does NOT pin a line of it.  Every count names its
;;; unit: `--grep-c' counts LINES and `--count' counts OCCURRENCES.
;;;
;;; An absent TRACKED file is a real FAIL, never a pass.  Every check
;;; registers a real ERT test through `imp-register-bool-as-ert-test'.

(princ "=== m59 imp-4 bitmap-spec-p MOVE suite ===\n")

(require 'imp-ert-report)

(defvar m59-imp4--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))
(defvar m59-imp4--registered 0
  "Total number of checks this corpus has registered.")
(defvar m59-imp4--group nil
  "The group that `m59-imp4--check' counts into: `w1' .. `w6', or nil.")
(defvar m59-imp4--counts nil
  "Alist of (GROUP . COUNT) for the registered checks.")

(defun m59-imp4--group-count (group)
  "Number of checks registered so far in GROUP."
  (or (cdr (assq group m59-imp4--counts)) 0))

(defun m59-imp4--bump-group ()
  "Count one check into `m59-imp4--group'."
  (when m59-imp4--group
    (let ((cell (assq m59-imp4--group m59-imp4--counts)))
      (if cell
          (setcdr cell (1+ (cdr cell)))
        (push (cons m59-imp4--group 1) m59-imp4--counts)))))

(defun m59-imp4--exists-p (rel)
  "Non-nil when the TRACKED file REL exists."
  (file-exists-p (expand-file-name rel m59-imp4--root)))

(defun m59-imp4--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
the symbol `m59-imp4-absent' when REL does not exist.  `case-fold-search'
is bound to nil: every pin in this corpus is case-SENSITIVE."
  (let ((path (expand-file-name rel m59-imp4--root)))
    (if (not (file-exists-p path))
        'm59-imp4-absent
      (with-temp-buffer
        (insert-file-contents path)
        (let ((case-fold-search nil))
          (funcall fn))))))

(defun m59-imp4--contains-p (rel needle)
  "Non-nil when the TRACKED file REL holds NEEDLE."
  (m59-imp4--holds-all rel (list needle)))

(defun m59-imp4--holds-all (rel needles)
  "Non-nil when the TRACKED file REL holds every NEEDLE."
  (m59-imp4--with rel
    (lambda ()
      (let ((all t))
        (dolist (needle needles)
          (goto-char (point-min))
          (unless (search-forward needle nil t) (setq all nil)))
        all))))

(defun m59-imp4--holds-none (rel needles)
  "Non-nil when the TRACKED file REL holds NO needle of NEEDLES."
  (m59-imp4--with rel
    (lambda ()
      (let ((none t))
        (dolist (needle needles)
          (goto-char (point-min))
          (when (search-forward needle nil t) (setq none nil)))
        none))))

(defun m59-imp4--live-p (rel needle)
  "Non-nil when the TRACKED file REL holds NEEDLE on a line that is NOT
a comment line."
  (m59-imp4--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((hit nil))
        (while (and (not hit) (search-forward needle nil t))
          (setq hit (save-excursion
                      (goto-char (line-beginning-position))
                      (not (looking-at-p "[ \t]*;")))))
        hit))))

(defun m59-imp4--ordered-p (rel needles)
  "Non-nil when the TRACKED file REL holds every NEEDLE in the GIVEN
ORDER: each search starts after the previous match."
  (m59-imp4--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((all t))
        (dolist (needle needles)
          (when all
            (unless (search-forward needle nil t) (setq all nil))))
        all))))

(defun m59-imp4--lines (rel)
  "Number of LINES of the TRACKED file REL, the unit of `wc -l'."
  (m59-imp4--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (not (eobp)) (setq n (1+ n)) (forward-line 1))
        n))))

(defun m59-imp4--grep-c (rel regexp)
  "Count the LINES of REL that match REGEXP, the unit of `grep -c'."
  (m59-imp4--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (not (eobp))
          (when (re-search-forward regexp (line-end-position) t)
            (setq n (1+ n)))
          (forward-line 1))
        n))))

(defun m59-imp4--count (rel regexp)
  "Count the OCCURRENCES of REGEXP in REL, the unit of
`grep -o | wc -l'.  This is NOT the unit of `grep -c'."
  (m59-imp4--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (re-search-forward regexp nil t) (setq n (1+ n)))
        n))))

(defun m59-imp4--src-public-refs ()
  "Count the OCCURRENCES of `scm_c_public_ref' over the TRACKED files
src/*.[ch] of the tree, the unit of `grep -o ... | wc -l'."
  (let ((dir (expand-file-name "src/" m59-imp4--root))
        (n 0))
    (dolist (f (directory-files dir t "\\.\\(c\\|h\\)\\'"))
      (with-temp-buffer
        (insert-file-contents f)
        (goto-char (point-min))
        (while (re-search-forward "scm_c_public_ref" nil t)
          (setq n (1+ n)))))
    n))

(defun m59-imp4--stale-count-names (count)
  "List the check names under test/ that embed the tree-wide
`scm_c_public_ref' COUNT in the name but a DIFFERENT number, as
\(FILE . NAME) pairs.  A re-pin moves the value and the name together
\(brief.org section 9), so a stale name hides which count a failed check
pins (cr.org F4).  Unit: OCCURRENCES."
  (let ((dir (expand-file-name "test" m59-imp4--root))
        (want (number-to-string count))
        (hits nil))
    (dolist (f (directory-files-recursively dir "\\.el\\'"))
      (with-temp-buffer
        (insert-file-contents f)
        (goto-char (point-min))
        (let ((case-fold-search nil))
          (while (re-search-forward
                  "check \"\\([^\"]*\\(?:tree-wide[^\"]*\\|scm-c-public-ref\\)-\\([0-9]+\\)\\)\""
                  nil t)
            (let ((name (match-string 1))
                  (num (match-string 2)))
              (unless (string= num want)
                (push (cons (file-relative-name f m59-imp4--root) name)
                      hits)))))))
    hits))

(defun m59-imp4--bm (object)
  "Call the real subr `bitmap-spec-p' with OBJECT and return its value,
or the symbol `m59-imp4-call-error' when the call signals."
  (condition-case _err
      (bitmap-spec-p object)
    (error 'm59-imp4-call-error)))

(defun m59-imp4--check (name ok)
  "Report and register one check.  OK is a boolean.  An absent TRACKED
file gives the symbol `m59-imp4-absent', which is a FAIL, not a pass."
  (let* ((absent (eq ok 'm59-imp4-absent))
         (pass (and (not absent) (and ok t))))
    (if absent
        (princ (format "FAIL m59/imp4/%s (source file absent)\n" name))
      (princ (format "%s m59/imp4/%s\n" (if pass "PASS" "FAIL") name)))
    (setq m59-imp4--registered (1+ m59-imp4--registered))
    (m59-imp4--bump-group)
    (imp-register-bool-as-ert-test (format "m59-imp4/%s" name) pass)))

;; A missing guile binary is an explicit INFO skip, never a pass.
(defun m59-imp4--info-skip (name reason)
  "Register one explicit INFO skip, counted into the current group."
  (princ (format "INFO m59/imp4/%s %s\n" name reason))
  (setq m59-imp4--registered (1+ m59-imp4--registered))
  (m59-imp4--bump-group)
  (imp-register-skip-as-ert-test (format "m59-imp4/%s" name) reason))

;;; --- W1. The module and its ONE load line ---------------------------

(setq m59-imp4--group 'w1)

(m59-imp4--check "module-present"
                 (m59-imp4--exists-p "mod/emacs/faces.scm"))

;; 2 #:export entries, and they name the 2 procedures that C resolves.
;; A drifted name makes `scm_c_public_ref' fail at the first call.
(m59-imp4--check "module-two-exports"
                 (and (eql 1 (m59-imp4--grep-c "mod/emacs/faces.scm"
                                               "^  #:export ("))
                      (m59-imp4--holds-all
                       "mod/emacs/faces.scm"
                       '("(face-attribute-relative-verdict"
                         "bitmap-spec-verdict))"))))
;; 2 procedure definitions, and the new one is the accept rule.
(m59-imp4--check "module-procedure"
                 (and (eql 2 (m59-imp4--grep-c "mod/emacs/faces.scm"
                                               "^(define ("))
                      (m59-imp4--holds-all
                       "mod/emacs/faces.scm"
                       '("(define (bitmap-spec-verdict file-name? width height data-bytes)"
                         "(and (>= width 1) (<= width 2147483647)"
                         "(let ((bytes-per-row (quotient (+ width 7) 8)))"
                         "(<= height (quotient data-bytes bytes-per-row))))))"))))
;; Purity: the procedure is a plain boolean function.  No elisp name
;; registration, no FFI leaf, no mutation, no I/O, no module load.
(m59-imp4--check "module-pure"
                 (m59-imp4--holds-none
                  "mod/emacs/faces.scm"
                  '("(defelisp" "(%--" "(set! " "(primitive-load"
                    "(display" "(format")))
;; The Scheme comment cites the C lines of the DELETED rule as a BASE
;; cite.  After the MOVE those lines hold the dispatcher and the new
;; body, so the cite must say that it is a base cite (cr.org F5).
(m59-imp4--check "module-base-cite"
                 (m59-imp4--holds-all
                  "mod/emacs/faces.scm"
                  '("src/xfaces.c :825 ..."
                    ":860 at the imp-4 base")))

;; ONE load line in prelude/load.scm.  This imp adds NO line: a second
;; one moves the pinned `^(use-modules' count of the older corpora.
(m59-imp4--check "load-line-once"
                 (eql 1 (m59-imp4--grep-c "prelude/load.scm"
                                          "^(use-modules (emacs faces))")))
(m59-imp4--check "load-lines-230"
                 (eql 229 (m59-imp4--lines "prelude/load.scm")))

;;; --- W2. The REAL behaviour: brief.org section 6 --------------------

;; The corpus runs inside the built src/emacs, so these are direct calls
;; to the C subr, which now asks Scheme for the verdict.  A CALL THAT
;; PASSES ON ANY INPUT IS NOT A PROOF, so every row is a check.
;;
;; The values are the MEASURED ones (see the header).  Rows 4 and 5 are
;; EXACT FITS because `(string 1 0)' is 2 bytes, so they measure t.

(setq m59-imp4--group 'w2)

(dolist (row (list
               (list "w2/row-1-file-name" (lambda () "x") t)
               (list "w2/row-2-exact-fit"
                     (lambda () (list 8 2 (string 2 0))) t)
               (list "w2/row-3-exact-fit-1-row"
                     (lambda () (list 8 1 (string 1 0))) t)
               (list "w2/row-4-two-byte-data"
                     (lambda () (list 8 2 (string 1 0))) t)
               (list "w2/row-5-bytes-per-row-2"
                     (lambda () (list 9 1 (string 1 0))) t)
               (list "w2/row-6-data-absent"
                     (lambda () (list 8 2)) nil)
               (list "w2/row-7-width-0"
                     (lambda () (list 0 1 (string 2 0))) nil)
               (list "w2/row-8-height-0"
                     (lambda () (list 8 0 (string 1 0))) nil)
               (list "w2/row-9-width-float"
                     (lambda () (list 8.0 2 (string 2 0))) nil)
               (list "w2/row-10-fourth-element"
                     (lambda () (list 8 2 (string 2 0) 'extra)) t)
               (list "w2/row-11-not-a-cons" (lambda () 42) nil)
               (list "w2/row-12-nil" (lambda () nil) nil)
               (list "w2/row-13-width-above-int-max"
                     (lambda () (list 2147483648 1 (string 1 0))) nil)))
  (m59-imp4--check (nth 0 row)
                   (eq (nth 2 row) (m59-imp4--bm (funcall (nth 1 row))))))

;; The 3 DATA-length controls.  Every one is really too short, so the
;; deleted `bytes_per_row' rule stays covered.
(m59-imp4--check "w2/ctl-data-short-8-3" (null (m59-imp4--bm (list 8 3 (string 1 0)))))
(m59-imp4--check "w2/ctl-data-short-9-2" (null (m59-imp4--bm (list 9 2 (string 2 0)))))
(m59-imp4--check "w2/ctl-data-short-1-8" (null (m59-imp4--bm (list 1 8 (string 1 0)))))

;;; --- W3. The C wiring ----------------------------------------------

(setq m59-imp4--group 'w3)

;; The dispatcher: one signature, one resolve site with the module name
;; and the procedure name, and one 4-argument crossing.
(m59-imp4--check "c/dispatcher"
                 (m59-imp4--holds-all
                  "src/xfaces.c"
                  '("m59_bitmap_spec_p_scheme (bool file_name, ptrdiff_t width,"
                    "ptrdiff_t height, ptrdiff_t data_bytes)"
                    "static SCM proc = SCM_UNDEFINED;"
                    "if (SCM_UNBNDP (proc))"
                    "return scm_is_true (SCM_CALL_4 (proc,")))

(m59-imp4--check "c/resolve-strings"
                 (m59-imp4--holds-all
                  "src/xfaces.c"
                  '("scm_c_public_ref (\"emacs faces\", \"bitmap-spec-verdict\");")))

;; The type tests and the BYTE length STAY C.  A Scheme
;; (string-length ...) counts characters and answers wrong on a
;; multibyte DATA string.
(m59-imp4--check "c/type-tests-stay"
                 (m59-imp4--holds-all
                  "src/xfaces.c"
                  '("if (STRINGP (object))"
                    "else if (CONSP (object))"
                    "if (FIXNUMP (width_obj))"
                    "width = XFIXNUM (width_obj);"
                    "if (FIXNUMP (height_obj))"
                    "height = XFIXNUM (height_obj);"
                    "return m59_bitmap_spec_p_scheme (file_name, width, height, data_bytes);")))
(m59-imp4--check "c/sbytes-stays"
                 (m59-imp4--holds-all
                  "src/xfaces.c"
                  '("Lisp_Object width_obj, height_obj, data;"
                    "if (STRINGP (data))"
                    "data_bytes = SBYTES (data);")))

;; The OLD accept rule is GONE.  A MOVE that keeps the decision in C is
;; a passthrough, not a port (docs/kb.org passthrough-leaf-is-not-a-port).
(m59-imp4--check "c/bytes-per-row-gone"
                 (m59-imp4--holds-none
                  "src/xfaces.c"
                  '("bytes_per_row"
                    "CHAR_BIT - 1) / CHAR_BIT")))
;; The 2 bounds are part of the decision, so RANGED_FIXNUMP must go too.
(m59-imp4--check "c/ranged-fixnump-gone"
                 (m59-imp4--holds-none
                  "src/xfaces.c"
                  '("RANGED_FIXNUMP (1, width, INT_MAX)"
                    "RANGED_FIXNUMP (1, height, INT_MAX)")))

;; A resolve site must resolve: no default verdict on the C side.
(m59-imp4--check "c/no-fallback"
                 (m59-imp4--holds-none
                  "src/xfaces.c"
                  '("SCM_UNBNDP (proc)) return"
                    "SCM_UNBNDP (proc))
    return Qnil;"
                    "SCM_UNBNDP (proc))
    return Qt;")))

;; The 5 internal callers still call the subr, so they now cross once
;; each.  Unit: OCCURRENCES (the DEFUN name line + the 5 callers = 6).
(m59-imp4--check "c/callers-5"
                 (eql 6 (m59-imp4--count "src/xfaces.c" "Fbitmap_spec_p")))
;; Unit: LINES (`grep -c "^DEFUN ("' = 33: this imp adds NO DEFUN.
(m59-imp4--check "c/defun-count-33"
                 (eql 33 (m59-imp4--grep-c "src/xfaces.c" "^DEFUN (")))
;; Unit: LINES (`grep -c scm_c_public_ref src/xfaces.c' = 2).
(m59-imp4--check "c/xfaces-scm-ref-2"
                 (eql 2 (m59-imp4--grep-c "src/xfaces.c"
                                          "scm_c_public_ref")))
;; Unit: OCCURRENCES (`grep -o scm_c_public_ref src/*.h src/*.c | wc -l').
(m59-imp4--check "c/tree-wide-scm-ref-267"
                 (eql 267 (m59-imp4--src-public-refs)))
;; The re-pin moves the VALUE and the NAME together (brief.org section
;; 9).  A check that still says -260 pins 267, so a failure report names
;; the wrong count (cr.org F4).  This guard computes the current count
;; from src/ and compares it with every name that embeds it.
(m59-imp4--check "c/no-stale-count-name"
                 (null (m59-imp4--stale-count-names
                        (m59-imp4--src-public-refs))))

;;; --- W4. The negative control ---------------------------------------

;; The Scheme side answers a constant -> the verdict changes.  That is
;; the proof that C no longer decides.  The real-path shape was
;; MEASURED on this host with NO rebuild: the exported name in
;; mod/emacs/faces.scm was renamed for one run, so scm_c_public_ref
;; fails at the first call and the subr SIGNALS.  It does NOT return a
;; default verdict (L1).  The edit was reverted.

(setq m59-imp4--group 'w4)

(m59-imp4--check "negative-control-record"
                 (and (m59-imp4--contains-p
                       "tool/run-tests.scm"
                       "Negative control")
                      (m59-imp4--contains-p
                       "tool/run-tests.scm"
                       "the exported name was renamed for one run")
                      (m59-imp4--contains-p
                       "tool/run-tests.scm"
                       "bitmap-spec-verdict")
                      (m59-imp4--contains-p
                       "tool/run-tests.scm"
                       "the subr SIGNALS")))

;; The live Scheme half of the control: a fresh guile rebinds the module
;; binding to a constant and the same 4 arguments change verdict.  This
;; proves the Scheme side only.  A missing guile is an explicit INFO
;; skip, never a pass.
(let ((guile (executable-find "guile")))
  (if (not guile)
      (m59-imp4--info-skip "negative-control-scheme-side"
                           "no guile binary on PATH")
    (m59-imp4--check
     "negative-control-scheme-side"
     (let ((out (with-temp-buffer
                  (call-process
                   guile nil t nil
                   "-L" (expand-file-name "mod" m59-imp4--root)
                   "-c"
                   (concat
                    "(use-modules (emacs faces))"
                    "(define before (bitmap-spec-verdict #f 8 2 2))"
                    "(module-set! (resolve-module '(emacs faces))"
                    " 'bitmap-spec-verdict"
                    " (lambda (f w h d) #f))"
                    "(define after (bitmap-spec-verdict #f 8 2 2))"
                    "(display (list before after))"))
                  (buffer-string))))
       (equal out "(#t #f)")))))

;;; --- W5. The registration in tool/run-tests.scm ---------------------

(setq m59-imp4--group 'w5)

(m59-imp4--check "reg/imp4-in-m59-group"
                 (eql 1 (m59-imp4--grep-c "tool/run-tests.scm"
                                          "test/m59/test-m59-imp4\\.el")))
(m59-imp4--check "reg/after-imp3"
                 (m59-imp4--ordered-p
                  "tool/run-tests.scm"
                  '("test/m59/test-m59-imp1.el"
                    "test/m59/test-m59-imp2.el"
                    "test/m59/test-m59-imp3.el"
                    "test/m59/test-m59-imp4.el")))
(m59-imp4--check "reg/imp1-imp3-lines-present"
                 (and (m59-imp4--live-p "tool/run-tests.scm"
                                        "test/m59/test-m59-imp1.el")
                      (m59-imp4--live-p "tool/run-tests.scm"
                                        "test/m59/test-m59-imp2.el")
                      (m59-imp4--live-p "tool/run-tests.scm"
                                        "test/m59/test-m59-imp3.el")))
(m59-imp4--check "reg/m58-group-present"
                 (m59-imp4--ordered-p "tool/run-tests.scm"
                                      '("(group (m58)" "(group (m59)")))

;;; --- W6. The guards -------------------------------------------------

;; An --filter that matches no group reports exit 0 with 0 tests, so a
;; green m59 gate proves nothing until the checks really register.

(setq m59-imp4--group 'w6)

(m59-imp4--check "min-w1-checks-7" (>= (m59-imp4--group-count 'w1) 7))
(m59-imp4--check "min-w2-checks-16" (>= (m59-imp4--group-count 'w2) 16))
(m59-imp4--check "min-w3-checks-12" (>= (m59-imp4--group-count 'w3) 12))
(m59-imp4--check "min-w4-checks-2" (>= (m59-imp4--group-count 'w4) 2))
(m59-imp4--check "min-w5-checks-4" (>= (m59-imp4--group-count 'w5) 4))
;; This guard reads its OWN group, so the count is still 5 while the
;; check is evaluated: add 1.  MEASURED: without the 1+ the check FAILS.
(m59-imp4--check "min-w6-checks-6" (>= (1+ (m59-imp4--group-count 'w6)) 6))

;;; --- The group-total check ------------------------------------------

(ert-deftest m59-imp4/gate-m59-total ()
  "The m59-imp4 corpus registers exactly the sum of its group counts."
  (should (= (length (ert-select-tests "^m59-imp4" t))
             (+ 1
                (m59-imp4--group-count 'w1)
                (m59-imp4--group-count 'w2)
                (m59-imp4--group-count 'w3)
                (m59-imp4--group-count 'w4)
                (m59-imp4--group-count 'w5)
                (m59-imp4--group-count 'w6)))))

(princ (format "=== m59 imp-4 suite done (%d checks; w1 %d, w2 %d, w3 %d, w4 %d, w5 %d, w6 %d) ===\n"
               m59-imp4--registered
               (m59-imp4--group-count 'w1)
               (m59-imp4--group-count 'w2)
               (m59-imp4--group-count 'w3)
               (m59-imp4--group-count 'w4)
               (m59-imp4--group-count 'w5)
               (m59-imp4--group-count 'w6)))
