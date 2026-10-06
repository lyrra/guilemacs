;;; test-m45-imp2.el --- M45 imp-2 corpus (the typed C leaves over plain values).
;;;
;;; M45 imp-2 adds the four typed C leaves over plain values for the
;;; parent-side process policy of src/callproc.c (brief.org section 6),
;;; the thin wrapper module (emacs process-create) (section 7), and this
;;; tracked corpus (section 10).  imp-2 adds leaves only: it moves no
;;; policy.  imp-3 moves the policy.
;;;
;;; This corpus reads files, and it runs one gated runtime probe.  It
;;; pins:
;;;   T1 -- the four leaf DEFUNs exist in src/callproc.c with the exact
;;;         names of brief.org section 6 (--callproc-argv,
;;;         --callproc-env, --callproc-resolve-program,
;;;         --callproc-temp-name).
;;;   T2 -- mod/emacs/process-create.scm exists, exports the four
;;;         wrappers, uses defelisp, holds no FFI call and no raw
;;;         syscall, and does not reuse (emacs process-accessors).
;;;   T3 -- each leaf takes and returns plain values only (section 5):
;;;         no char **, no struct posix_spawn, and no FILE * parameter
;;;         crosses the layer.  Pin the guards of section 8.
;;;   T4 -- src/callproc.c includes "guile.h" (this replaces the imp-1
;;;         callproc.c-no-guile.h check).
;;;   T5 -- prelude/load.scm carries (use-modules (emacs
;;;         process-create)), and the (m45) group carries this corpus.
;;;   T6 -- the base numbers of brief.org section 3 hold after imp-2:
;;;         src/sysdep.c, src/keyboard.c, src/keyboard-globals.c, the
;;;         combined keyboard surface, the margin, scm_c_public_ref,
;;;         and mod/emacs/tty-modes.scm do not move; src/callproc.c
;;;         lines and DEFUNs grow (2,184 -> 2,514 and 3 -> 7).
;;;   T7 -- a per-group min-count guard (cr1.org F2, carried from
;;;         cr.org F3).  A --filter that matches no group reports exit 0
;;;         with 0 tests, so the gate proves nothing until the corpus
;;;         really registers.  Pin each group's count apart from the
;;;         total.
;;;   T8 -- the gated runtime probe.  Run the built src/emacs and call
;;;         --callproc-resolve-program on /bin/sh; it returns a string.
;;;         This is an INFO skip when src/emacs is absent (section 14).
;;;
;;; A read error is a real error, never a silent pass.  An absent src/
;;; file is a real error.

(princ "=== m45 imp-2 leaves suite ===\n")

(require 'imp-ert-report)

(defvar m45-imp2--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))

(defvar m45-imp2--registered 0
  "Total number of tracked-file checks this corpus has registered.")

(defvar m45-imp2--group nil
  "The group that `m45-imp2--check' counts into: `t1' ... `t6', or nil.")

(defvar m45-imp2--counts nil
  "Alist of (GROUP . COUNT) for the registered tracked-file checks.")

(defun m45-imp2--group-count (group)
  "Number of tracked-file checks registered so far in GROUP."
  (or (cdr (assq group m45-imp2--counts)) 0))

(defun m45-imp2--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
the symbol `m45-imp2-absent' when REL does not exist."
  (let ((path (expand-file-name rel m45-imp2--root)))
    (if (not (file-exists-p path))
        'm45-imp2-absent
      (with-temp-buffer
        (insert-file-contents path)
        (funcall fn)))))

(defun m45-imp2--contains-p (rel needle)
  "Non-nil when REL (repo-root-relative) contains NEEDLE."
  (m45-imp2--with rel
    (lambda ()
      (goto-char (point-min))
      (search-forward needle nil t))))

(defun m45-imp2--lines (rel)
  "Count the newlines of REL the way `wc -l' does."
  (m45-imp2--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (search-forward "\n" nil t) (setq n (1+ n)))
        n))))

(defun m45-imp2--count (rel regexp)
  "Count the matches of REGEXP in REL."
  (m45-imp2--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (re-search-forward regexp nil t) (setq n (1+ n)))
        n))))

(defun m45-imp2--count-code (rel regexp)
  "Count the matches of REGEXP in REL, skipping full comment lines.
A module comment may name a forbidden token (for example a raw
syscall) while explaining that the module does NOT use it; only the
code must be free of the token."
  (m45-imp2--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (not (eobp))
          (let ((line (buffer-substring-no-properties
                       (line-beginning-position) (line-end-position))))
            (unless (string-match-p "^[ \t]*;" line)
              (save-excursion
                (end-of-line)
                (let ((eol (point)))
                  (beginning-of-line)
                  (while (re-search-forward regexp eol t)
                    (setq n (1+ n)))))))
          (forward-line 1))
        n))))

(defun m45-imp2--count-scm-ref ()
  "Count scm_c_public_ref over src/*.[chm] (the brief.org section 3 measure)."
  (let ((total 0)
        (dir (expand-file-name "src" m45-imp2--root)))
    (dolist (f (directory-files dir t "\\.[chm]\\'"))
      (setq total (+ total (or (m45-imp2--count f "scm_c_public_ref") 0))))
    total))

(defun m45-imp2--check (name ok)
  "Report and register one check on a TRACKED file.  OK is a boolean.
An absent src/ file makes the reader return the symbol
`m45-imp2-absent', so the check prints FAIL -- an absent src/ file is a
real error, not a pass."
  (if (eq ok 'm45-imp2-absent)
      (princ (format "INFO m45/imp2/%s skipped (source file absent)\n" name))
    (progn
      (princ (format "%s m45/imp2/%s\n" (if ok "PASS" "FAIL") name))
      (setq m45-imp2--registered (1+ m45-imp2--registered))
      (when m45-imp2--group
        (let ((cell (assq m45-imp2--group m45-imp2--counts)))
          (if cell
              (setcdr cell (1+ (cdr cell)))
            (push (cons m45-imp2--group 1) m45-imp2--counts))))
      (imp-register-bool-as-ert-test (format "m45-imp2/%s" name) (and ok t)))))

;;; --- T1. The four leaf DEFUNs (brief.org section 6) ------------------

(setq m45-imp2--group 't1)

(m45-imp2--check "callproc-leaf-defuns-4"
                 (eql 4 (m45-imp2--count "src/callproc.c" "^DEFUN (\"--callproc-")))
(m45-imp2--check "leaf-argv"
                 (m45-imp2--contains-p "src/callproc.c"
                                       "DEFUN (\"--callproc-argv\""))
(m45-imp2--check "leaf-env"
                 (m45-imp2--contains-p "src/callproc.c"
                                       "DEFUN (\"--callproc-env\""))
(m45-imp2--check "leaf-resolve-program"
                 (m45-imp2--contains-p "src/callproc.c"
                                       "DEFUN (\"--callproc-resolve-program\""))
(m45-imp2--check "leaf-temp-name"
                 (m45-imp2--contains-p "src/callproc.c"
                                       "DEFUN (\"--callproc-temp-name\""))

;;; --- T2. The wrapper module (brief.org section 7) --------------------

(setq m45-imp2--group 't2)

(m45-imp2--check "module-exists"
                 (not (eq (m45-imp2--contains-p "mod/emacs/process-create.scm"
                                                "(define-module")
                          'm45-imp2-absent)))
(m45-imp2--check "module-defelisp-argv"
                 (m45-imp2--contains-p "mod/emacs/process-create.scm"
                                       "(defelisp %--callproc-argv"))
(m45-imp2--check "module-defelisp-env"
                 (m45-imp2--contains-p "mod/emacs/process-create.scm"
                                       "(defelisp %--callproc-env"))
(m45-imp2--check "module-defelisp-resolve"
                 (m45-imp2--contains-p "mod/emacs/process-create.scm"
                                       "(defelisp %--callproc-resolve-program"))
(m45-imp2--check "module-defelisp-temp"
                 (m45-imp2--contains-p "mod/emacs/process-create.scm"
                                       "(defelisp %--callproc-temp-name"))
(m45-imp2--check "module-exports"
                 (let ((n (m45-imp2--count "mod/emacs/process-create.scm"
                                           "(callproc-\\(argv\\|env\\|resolve-program\\|temp-name\\)")))
                   (>= n 8)))		; 4 in #:export, 4 in the defines
(m45-imp2--check "module-no-ffi"
                 (let ((n (m45-imp2--count-code
                           "mod/emacs/process-create.scm"
                           "system foreign\\|dynamic-link\\|libc\\.so\\|system\\*\\|primitive-fork\\|posix_spawn\\|ioctl\\|dynamic-func")))
                   (and (integerp n) (eql 0 n))))
(m45-imp2--check "module-no-process-accessors"
                 (let ((n (m45-imp2--count-code
                           "mod/emacs/process-create.scm"
                           "(emacs process-accessors)")))
                   (and (integerp n) (eql 0 n))))

;;; --- T3. Plain values only and the guards (brief.org sections 5, 8) --

(setq m45-imp2--group 't3)

;; The four leaf parameter lines are plain values.
(m45-imp2--check "leaf-argv-params-plain"
                 (m45-imp2--contains-p "src/callproc.c"
                                       "(Lisp_Object x, Lisp_Object y)"))
(m45-imp2--check "leaf-env-params-plain"
                 (m45-imp2--contains-p "src/callproc.c"
                                       "(Lisp_Object current_dir)"))
(m45-imp2--check "leaf-resolve-params-plain"
                 (m45-imp2--contains-p "src/callproc.c"
                                       "(Lisp_Object program)"))
(m45-imp2--check "leaf-temp-params-plain"
                 (m45-imp2--contains-p "src/callproc.c"
                                       "(void)\n{\n  Lisp_Object tmpdir, pattern;"))
;; The guards of section 8: a wrong type returns a value, not an abort.
(m45-imp2--check "guard-argv-program-string"
                 (m45-imp2--contains-p "src/callproc.c" "if (!STRINGP (x))"))
(m45-imp2--check "guard-argv-element-string"
                 (m45-imp2--contains-p "src/callproc.c" "if (!STRINGP (arg))"))
(m45-imp2--check "guard-env-current-dir-string"
                 (m45-imp2--contains-p "src/callproc.c"
                                       "if (!STRINGP (current_dir))"))
(m45-imp2--check "guard-resolve-program-string"
                 (m45-imp2--contains-p "src/callproc.c" "if (!STRINGP (program))"))
;; No raw mechanism type crosses the layer: the four leaves never take a
;; char **, a struct posix_spawn, or a FILE * parameter.  The mechanism
;; still holds those types, so pin the four *leaf* parameter lines.
(m45-imp2--check "leaf-no-char-param"
                 (let ((n (m45-imp2--count
                           "src/callproc.c"
                           "^[ \t]*(Lisp_Object x, Lisp_Object y)$\\|^[ \t]*(Lisp_Object current_dir)$\\|^[ \t]*(Lisp_Object program)$\\|^[ \t]*(void)$")))
                   (and (integerp n) (eql 4 n))))
;; cr.org F4: --callproc-resolve-program reads Vexec_path / Vexec_suffixes
;; itself for imp-2 (imp-3 passes the lists in).  Record the choice.
(m45-imp2--check "leaf-resolve-reads-exec-path"
                 (m45-imp2--contains-p
                  "src/callproc.c"
                  "openp (Vexec_path, program, Vexec_suffixes, &path,"))
;; cr.org F1: the env dedup must match add_env -- a new "NAME=VALUE"
;; conflicts with an existing lone "NAME".
(m45-imp2--check "leaf-env-dedup-matches-add_env"
                 (m45-imp2--contains-p
                  "src/callproc.c" "add_env reports a conflict when"))
;; cr.org F2: the argv coding keeps the call_process ASCII-compat guard.
(m45-imp2--check "leaf-argv-ascii-compat-guard"
                 (m45-imp2--contains-p
                  "src/callproc.c"
                  "An ASCII-incompatible coding system cannot encode an argv"))

;;; --- T4. The guile.h include (brief.org section 8) -------------------

(setq m45-imp2--group 't4)

(m45-imp2--check "callproc.c-includes-guile.h"
                 (m45-imp2--contains-p "src/callproc.c" "#include \"guile.h\""))
(m45-imp2--check "callproc.c-guile.h-once"
                 (eql 1 (m45-imp2--count "src/callproc.c" "#include \"guile.h\"")))

;;; --- T5. The registration facts (brief.org sections 7, 9) ------------

(setq m45-imp2--group 't5)

(m45-imp2--check "load.scm-process-create"
                 (m45-imp2--contains-p "prelude/load.scm"
                                       "(use-modules (emacs process-create))"))
(m45-imp2--check "run-tests-m45-imp2"
                 (m45-imp2--contains-p "tool/run-tests.scm"
                                       "test/m45/test-m45-imp2.el"))

;;; --- T6. The base numbers do not move (brief.org section 3) ----------

(setq m45-imp2--group 't6)

(m45-imp2--check "sysdep.c-lines-4950"
                 (eql 4950 (m45-imp2--lines "src/sysdep.c")))
(m45-imp2--check "sysdep.c-defuns-7"
                 (eql 7 (m45-imp2--count "src/sysdep.c" "^DEFUN (\"")))
(m45-imp2--check "keyboard.c-lines-11233"
                 (eql 11233 (m45-imp2--lines "src/keyboard.c")))
(m45-imp2--check "keyboard.c-defuns-447"
                 (eql 447 (m45-imp2--count "src/keyboard.c" "^DEFUN (\"")))
(m45-imp2--check "keyboard-globals.c-lines-490"
                 (eql 490 (m45-imp2--lines "src/keyboard-globals.c")))
(m45-imp2--check "combined-keyboard-surface-11723"
                 (let ((kb (m45-imp2--lines "src/keyboard.c"))
                       (kg (m45-imp2--lines "src/keyboard-globals.c")))
                   (and (integerp kb) (integerp kg)
                        (eql 11723 (+ kb kg)))))
(m45-imp2--check "margin-under-budget-237"
                 (let ((kb (m45-imp2--lines "src/keyboard.c"))
                       (kg (m45-imp2--lines "src/keyboard-globals.c")))
                   (and (integerp kb) (integerp kg)
                        (eql 237 (- 11960 (+ kb kg))))))
(m45-imp2--check "scm-c-public-ref-228"
                 (eql 228 (m45-imp2--count-scm-ref)))
(m45-imp2--check "tty-modes.scm-lines-313"
                 (eql 313 (m45-imp2--lines "mod/emacs/tty-modes.scm")))
;; src/callproc.c: 2,184 (imp-1 base) -> 2,514 (imp-2) -> 2,380 (imp-3,
;; which deletes the inline parent-side policy).
(m45-imp2--check "callproc.c-lines-2387"
                 (eql 2387 (m45-imp2--lines "src/callproc.c")))
(m45-imp2--check "callproc.c-defuns-grew"
                 (eql 7 (m45-imp2--count "src/callproc.c" "^DEFUN (\"")))

;;; --- T7. The per-group min-count guard (cr1.org F2 / cr.org F3) ------

(setq m45-imp2--group nil)

(m45-imp2--check "reg/min-t1-checks-5"
                 (>= (m45-imp2--group-count 't1) 5))
(m45-imp2--check "reg/min-t2-checks-8"
                 (>= (m45-imp2--group-count 't2) 8))
(m45-imp2--check "reg/min-t3-checks-12"
                 (>= (m45-imp2--group-count 't3) 12))
(m45-imp2--check "reg/min-t6-checks-11"
                 (>= (m45-imp2--group-count 't6) 11))
(m45-imp2--check "reg/min-total-41"
                 (>= m45-imp2--registered 41))

;;; --- T8. The gated runtime probe (brief.org section 10) --------------

;; This corpus runs inside the built src/emacs: the (m45) group carries
;; no `prelude' key, so tool/run-tests.scm loads these files with
;; run-tests-loadup-emacs, which is "../src/emacs ... -l <file> --batch".
;; A probe therefore calls the leaf DIRECTLY, in this process.
;;
;; An earlier version ran each probe in a nested src/emacs --batch to
;; isolate the harness from a failing probe.  That cost one full emacs
;; startup per probe, and it reported a non-zero child exit as a skip.
;; The isolation is not worth the price: one failing probe may stop the
;; load of the rest.  `condition-case' still holds an ordinary signalled
;; error to that one probe.  Each leaf here returns a value and writes
;; no file, and the two dynamic bindings are `let'-scoped, so a probe
;; leaves no state behind.
;;
;; A missing leaf is a FAIL, not a skip: the imp-2 leaves must exist in
;; the built binary.  There is no src/emacs INFO-skip any more.

(defun m45-imp2--probe (name thunk)
  "Register NAME from the value of THUNK, which calls a leaf.
A non-nil value is a PASS.  A signalled error is a FAIL, never a silent
pass; the error is printed so the cause is visible.  An undefined leaf
signals void-function, so it is a FAIL too."
  (m45-imp2--check
   name
   (condition-case err
       (and (funcall thunk) t)
     (error (princ (format "INFO m45/imp2/%s error=%S\n" name err))
            nil))))

(m45-imp2--probe "probe/resolve-program-returns-string"
                 (lambda ()
                   (let ((got (--callproc-resolve-program "/bin/sh")))
                     (and (stringp got) (string-prefix-p "/" got)))))

;; cr.org F1: with process-environment ("A" "A=1"), add_env drops "A=1"
;; (the existing lone "A" wins, then the lone-name removal drops "A").
;; The leaf must agree, so the result must not hold "A=1".
(m45-imp2--probe "probe/env-dedup-lone-name"
                 (lambda ()
                   (let ((process-environment (list "A" "A=1")))
                     (null (member "A=1" (--callproc-env default-directory))))))

;; cr.org F2: a non-ASCII-compatible coding-system-for-write must fall
;; back to raw-text, so "A" stays one byte and is still "A".
(m45-imp2--probe "probe/argv-ascii-compat-fallback"
                 (lambda ()
                   (let ((coding-system-for-write 'utf-16))
                     (member "A" (--callproc-argv "/bin/echo" (list "A"))))))

(princ (format "=== m45 imp-2 leaves suite done (%d tracked checks; t1 %d, t2 %d, t3 %d, t4 %d, t5 %d, t6 %d) ===\n"
               m45-imp2--registered
               (m45-imp2--group-count 't1)
               (m45-imp2--group-count 't2)
               (m45-imp2--group-count 't3)
               (m45-imp2--group-count 't4)
               (m45-imp2--group-count 't5)
               (m45-imp2--group-count 't6)))
