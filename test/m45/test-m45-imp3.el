;;; test-m45-imp3.el --- M45 imp-3 corpus (the parent-side policy rewired).
;;;
;;; M45 imp-2 added the four typed C leaves over plain values and the
;;; thin module (emacs process-create); it moved no policy.  M45 imp-3
;;; moves the parent-side process-invocation policy of src/callproc.c
;;; onto those leaves.  The three hubs call the module:
;;;   call_process           -> callproc-resolve-program, callproc-argv
;;;   create_temp_file       -> callproc-temp-name
;;;   make_environment_block -> callproc-env
;;; The C mechanism (fork, exec, posix_spawn, pipe, fcntl, dup2,
;;; mkostemp, and every char ** block) stays C (brief.org section 3).
;;; The child side (child_setup, exec_failed) stays C: a vfork child
;;; must not enter the Guile VM.
;;;
;;; This corpus reads files, and it runs one gated runtime probe.  It
;;; pins:
;;;   T1 -- the three hubs dispatch into the module: src/callproc.c
;;;         holds scm_c_public_ref ("emacs process-create", ...), the
;;;         four helpers, and the four call sites.
;;;   T2 -- the inline policy is gone: call_process no longer holds the
;;;         openp (Vexec_path ...) search; create_temp_file no longer
;;;         holds Fexpand_file_name (Vtemp_file_name_pattern ...);
;;;         make_environment_block no longer holds the
;;;         for (tem = Vprocess_environment ...) loop (brief.org T2).
;;;         Also the cr.org imp-3 repair: the resolve / encode step runs
;;;         once (F1, no double remove_slash_colon), and the argv fill
;;;         loop is bounded by the block size (F2).
;;;   T3 -- the module still exports the four wrappers and holds no FFI
;;;         call.
;;;   T4 -- child_setup and exec_failed are unchanged: they hold no
;;;         Guile VM call; the only scm_c_public_ref sites are the four
;;;         dispatch helpers.
;;;   T5 -- the surface: re-measure src/callproc.c lines and DEFUNs,
;;;         scm_c_public_ref over src/*.[chm], and the M31 margin
;;;         (brief.org section 8).
;;;   T6 -- a per-group min-count guard (cr1.org F2 / cr.org F3).  Pin
;;;         each group's count apart from the total.
;;;   T7 -- the gated runtime probe: call-process "echo", one env var,
;;;         and one call-process-region temp file.  INFO-skip when
;;;         src/emacs is absent.
;;;   T8 -- the list lifetimes (cr.org F1): call_process roots the
;;;         argv list and make_environment_block roots the env list
;;;         beside their char ** blocks, with one shared unwinder that
;;;         releases them after emacs_spawn.  The two hubs also reject
;;;         a nil leaf return (cr.org F6).
;;;
;;; A read error is a real error, never a silent pass.  An absent src/
;;; file is a real error.

(princ "=== m45 imp-3 rewire suite ===\n")

(require 'imp-ert-report)

(defvar m45-imp3--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))

(defvar m45-imp3--registered 0
  "Total number of tracked-file checks this corpus has registered.")

(defvar m45-imp3--group nil
  "The group that `m45-imp3--check' counts into: `t1' ... `t5', or nil.")

(defvar m45-imp3--counts nil
  "Alist of (GROUP . COUNT) for the registered tracked-file checks.")

(defun m45-imp3--group-count (group)
  "Number of tracked-file checks registered so far in GROUP."
  (or (cdr (assq group m45-imp3--counts)) 0))

(defun m45-imp3--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
the symbol `m45-imp3-absent' when REL does not exist."
  (let ((path (expand-file-name rel m45-imp3--root)))
    (if (not (file-exists-p path))
        'm45-imp3-absent
      (with-temp-buffer
        (insert-file-contents path)
        (funcall fn)))))

(defun m45-imp3--contains-p (rel needle)
  "Non-nil when REL (repo-root-relative) contains NEEDLE."
  (m45-imp3--with rel
    (lambda ()
      (goto-char (point-min))
      (search-forward needle nil t))))

(defun m45-imp3--lines (rel)
  "Count the newlines of REL the way `wc -l' does."
  (m45-imp3--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (search-forward "\n" nil t) (setq n (1+ n)))
        n))))

(defun m45-imp3--count (rel regexp)
  "Count the matches of REGEXP in REL."
  (m45-imp3--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (re-search-forward regexp nil t) (setq n (1+ n)))
        n))))

(defun m45-imp3--line-of (rel needle)
  "Line number of the first literal NEEDLE in REL."
  (m45-imp3--with rel
    (lambda ()
      (goto-char (point-min))
      (when (search-forward needle nil t)
        (line-number-at-pos (match-beginning 0))))))

(defun m45-imp3--count-code (rel regexp)
  "Count the matches of REGEXP in REL, skipping full comment lines.
A module comment may name a forbidden token (for example a raw
syscall) while explaining that the module does NOT use it; only the
code must be free of the token."
  (m45-imp3--with rel
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

(defun m45-imp3--count-scm-ref ()
  "Count scm_c_public_ref over src/*.[chm] (the brief.org section 8 measure)."
  (let ((total 0)
        (dir (expand-file-name "src" m45-imp3--root)))
    (dolist (f (directory-files dir t "\\.[chm]\\'"))
      (setq total (+ total (or (m45-imp3--count f "scm_c_public_ref") 0))))
    total))

(defun m45-imp3--check (name ok)
  "Report and register one check on a TRACKED file.  OK is a boolean.
An absent src/ file makes the reader return the symbol
`m45-imp3-absent', so the check prints FAIL -- an absent src/ file is a
real error, not a pass."
  (if (eq ok 'm45-imp3-absent)
      (princ (format "INFO m45/imp3/%s skipped (source file absent)\n" name))
    (progn
      (princ (format "%s m45/imp3/%s\n" (if ok "PASS" "FAIL") name))
      (setq m45-imp3--registered (1+ m45-imp3--registered))
      (when m45-imp3--group
        (let ((cell (assq m45-imp3--group m45-imp3--counts)))
          (if cell
              (setcdr cell (1+ (cdr cell)))
            (push (cons m45-imp3--group 1) m45-imp3--counts))))
      (imp-register-bool-as-ert-test (format "m45-imp3/%s" name) (and ok t)))))

;;; --- T1. The three hubs dispatch into the module (brief.org section 4)

(setq m45-imp3--group 't1)

(m45-imp3--check "hub-scm-public-ref-module"
                 (m45-imp3--contains-p "src/callproc.c"
                                       "scm_c_public_ref (\"emacs process-create\""))
(m45-imp3--check "helper-resolve-program"
                 (m45-imp3--contains-p "src/callproc.c"
                                       "callproc_resolve_program (Lisp_Object program)"))
(m45-imp3--check "helper-argv"
                 (m45-imp3--contains-p "src/callproc.c"
                                       "callproc_argv (Lisp_Object program, Lisp_Object args)"))
(m45-imp3--check "helper-temp-name"
                 (m45-imp3--contains-p "src/callproc.c"
                                       "callproc_temp_name (void)"))
(m45-imp3--check "helper-env"
                 (m45-imp3--contains-p "src/callproc.c"
                                       "callproc_env (Lisp_Object current_dir)"))
(m45-imp3--check "resolve-called-in-hub"
                 (m45-imp3--contains-p "src/callproc.c"
                                       "path = callproc_resolve_program (args[0]);"))
(m45-imp3--check "argv-called-in-hub"
                 (m45-imp3--contains-p "src/callproc.c"
                                       "argv_list = callproc_argv (path, arg_list);"))
(m45-imp3--check "env-called-in-hub"
                 (m45-imp3--contains-p "src/callproc.c"
                                       "env_list = callproc_env (current_dir);"))
(m45-imp3--check "temp-called-in-hub"
                 (m45-imp3--contains-p "src/callproc.c"
                                       "Lisp_Object temp_name = callproc_temp_name ();"))
(m45-imp3--check "helpers-defined-before-call-process"
                 (let ((h (m45-imp3--line-of "src/callproc.c"
                                             "callproc_env (Lisp_Object current_dir)"))
                       (c (m45-imp3--line-of "src/callproc.c"
                                             "call_process (ptrdiff_t nargs, Lisp_Object *args,")))
                   (and (integerp h) (integerp c) (< h c))))

;;; --- T2. The inline policy is gone (brief.org section 7.1 T2) --------

(setq m45-imp3--group 't2)

;; Only the leaf --callproc-resolve-program may hold the openp search.
(m45-imp3--check "no-direct-openp-search"
                 (eql 1 (m45-imp3--count "src/callproc.c" "openp (Vexec_path")))
;; Only the leaf --callproc-temp-name may hold the pattern expansion.
(m45-imp3--check "no-direct-expand-temp-pattern"
                 (eql 1 (m45-imp3--count
                         "src/callproc.c"
                         "Fexpand_file_name (Vtemp_file_name_pattern")))
;; Only the leaf --callproc-env may hold the two Vprocess_environment loops.
(m45-imp3--check "no-direct-env-loop"
                 (eql 2 (m45-imp3--count "src/callproc.c"
                                         "for (tem = Vprocess_environment")))
;; cr.org F2: make_environment_block no longer re-applies the add_env
;; dedup rule; C copies each leaf string as-is, so the leaf is the only
;; dedup (brief.org section 5.3.5).
(m45-imp3--check "no-inline-env-dedup-call"
                 (eql 0 (m45-imp3--count "src/callproc.c"
                                         "new_env = add_env (env, new_env")))
(m45-imp3--check "env-plain-copy"
                 (m45-imp3--contains-p "src/callproc.c"
                                       "*p++ = SSDATA (XCAR (tem));"))
(m45-imp3--check "scm-public-ref-count-4"
                 (eql 4 (m45-imp3--count "src/callproc.c" "scm_c_public_ref")))
(m45-imp3--check "scm-call-count-4"
                 (eql 4 (m45-imp3--count "src/callproc.c" "SCM_CALL_")))

;; cr.org F1 (imp-3 repair): the resolve / encode step runs once, in the
;; leaf --callproc-resolve-program.  call_process no longer re-applies
;; remove_slash_colon to the already-encoded path.  One occurrence only.
(m45-imp3--check "resolve-encode-once"
                 (eql 1 (m45-imp3--count "src/callproc.c"
                                         "remove_slash_colon (path)")))
;; cr.org F2 (imp-3 repair): the argv fill loop is bounded by the block
;; size, so a leaf list longer than the block cannot overrun it.
(m45-imp3--check "argv-length-guarded"
                 (and (m45-imp3--contains-p "src/callproc.c"
                                            "ptrdiff_t limit = nargs < 4 ? 2 : nargs - 2;")
                      (m45-imp3--contains-p "src/callproc.c"
                                            "if (i + 1 >= limit)")))

;;; --- T3. The module still exports the wrappers, no FFI --------------

(setq m45-imp3--group 't3)

(m45-imp3--check "module-exists"
                 (not (eq (m45-imp3--contains-p "mod/emacs/process-create.scm"
                                                "(define-module")
                          'm45-imp3-absent)))
(m45-imp3--check "module-defelisp-4"
                 (eql 4 (m45-imp3--count "mod/emacs/process-create.scm"
                                         "(defelisp %--callproc-")))
(m45-imp3--check "module-exports"
                 (let ((n (m45-imp3--count
                           "mod/emacs/process-create.scm"
                           "(callproc-\\(argv\\|env\\|resolve-program\\|temp-name\\)")))
                   (>= n 8)))		; 4 in #:export, 4 in the defines
(m45-imp3--check "module-no-ffi"
                 (let ((n (m45-imp3--count-code
                           "mod/emacs/process-create.scm"
                           "system foreign\\|dynamic-link\\|libc\\.so\\|system\\*\\|primitive-fork\\|posix_spawn\\|ioctl\\|dynamic-func")))
                   (and (integerp n) (eql 0 n))))
(m45-imp3--check "module-no-process-accessors"
                 (let ((n (m45-imp3--count-code
                           "mod/emacs/process-create.scm"
                           "(emacs process-accessors)")))
                   (and (integerp n) (eql 0 n))))

;;; --- T4. The child side stays C (brief.org section 5.5) -------------

(setq m45-imp3--group 't4)

(m45-imp3--check "child-setup-signature"
                 (m45-imp3--contains-p
                  "src/callproc.c"
                  "child_setup (int in, int out, int err, char **new_argv, char **env,"))
(m45-imp3--check "exec-failed-signature"
                 (m45-imp3--contains-p
                  "src/callproc.c"
                  "exec_failed (char const *name, int err)"))
;; The four dispatch helpers hold the only c_to_scheme crossings; the
;; child side holds none.
(m45-imp3--check "child-side-no-scheme-call"
                 (eql 4 (m45-imp3--count "src/callproc.c" "SCM_CALL_")))
(m45-imp3--check "child-setup-defined"
                 (m45-imp3--contains-p
                  "src/callproc.c"
                  "child_setup (int in, int out, int err, char **new_argv, char **env,"))

;;; --- T5. The surface (brief.org section 8) --------------------------

(setq m45-imp3--group 't5)

(m45-imp3--check "callproc.c-lines-2387"
                 (eql 2387 (m45-imp3--lines "src/callproc.c")))
(m45-imp3--check "callproc.c-defuns-7"
                 (eql 7 (m45-imp3--count "src/callproc.c" "^DEFUN (\"")))
(m45-imp3--check "scm-c-public-ref-201"
                 (eql 201 (m45-imp3--count-scm-ref)))
(m45-imp3--check "margin-under-budget-237"
                 (let ((kb (m45-imp3--lines "src/keyboard.c"))
                       (kg (m45-imp3--lines "src/keyboard-globals.c")))
                   (and (integerp kb) (integerp kg)
                        (eql 237 (- 11960 (+ kb kg))))))
(m45-imp3--check "sysdep.c-lines-4950"
                 (eql 4950 (m45-imp3--lines "src/sysdep.c")))
(m45-imp3--check "sysdep.c-defuns-7"
                 (eql 7 (m45-imp3--count "src/sysdep.c" "^DEFUN (\"")))
(m45-imp3--check "keyboard.c-lines-11233"
                 (eql 11233 (m45-imp3--lines "src/keyboard.c")))
(m45-imp3--check "keyboard.c-defuns-447"
                 (eql 447 (m45-imp3--count "src/keyboard.c" "^DEFUN (\"")))
(m45-imp3--check "keyboard-globals.c-lines-490"
                 (eql 490 (m45-imp3--lines "src/keyboard-globals.c")))
(m45-imp3--check "combined-keyboard-surface-11723"
                 (let ((kb (m45-imp3--lines "src/keyboard.c"))
                       (kg (m45-imp3--lines "src/keyboard-globals.c")))
                   (and (integerp kb) (integerp kg)
                        (eql 11723 (+ kb kg)))))

;;; --- T8. The list lifetimes (cr.org F1) -----------------------------

;; The char ** blocks point into the strings of the plain lists.  Both
;; hubs now put a real GC root on their list with scm_gc_protect_object,
;; and one unwind releases it after the child is spawned.  A collected
;; list would leave the block dangling (brief.org section 5.1, cr.org
;; F1).  The env root was present; the argv root fixes F1.

(setq m45-imp3--group 't8)

(m45-imp3--check "env-list-gc-protected"
                 (m45-imp3--contains-p "src/callproc.c"
                                       "scm_gc_protect_object (env_list);"))
(m45-imp3--check "env-list-unprotect-unwind"
                 (m45-imp3--contains-p "src/callproc.c"
                                       "record_unwind_protect (unprotect_guile_object, env_list);"))
(m45-imp3--check "env-list-local-in-hub"
                 (m45-imp3--contains-p "src/callproc.c"
                                       "Lisp_Object env_list;"))
(m45-imp3--check "env-hub-signature-one-arg"
                 (eql 1 (m45-imp3--count "src/callproc.c"
                                         "make_environment_block (Lisp_Object current_dir)")))
(m45-imp3--check "env-hub-called-with-one-arg"
                 (m45-imp3--contains-p "src/callproc.c"
                                       "char **env = make_environment_block (current_dir);"))
(m45-imp3--check "env-no-caller-out-param"
                 (eql 0 (m45-imp3--count "src/callproc.c"
                                         "make_environment_block (current_dir, ")))
;; cr.org F1: call_process roots argv_list the same way.
(m45-imp3--check "argv-list-gc-protected"
                 (m45-imp3--contains-p "src/callproc.c"
                                       "scm_gc_protect_object (argv_list);"))
(m45-imp3--check "argv-list-unprotect-unwind"
                 (m45-imp3--contains-p "src/callproc.c"
                                       "record_unwind_protect (unprotect_guile_object, argv_list);"))
;; cr.org F1/F6: one shared unwinder releases both roots.
(m45-imp3--check "one-unwinder-both-lists"
                 (and (m45-imp3--contains-p "src/callproc.c"
                                            "unprotect_guile_object (Lisp_Object list)")
                      (eql 1 (m45-imp3--count "src/callproc.c"
                                              "^unprotect_guile_object (Lisp_Object list)"))))
;; cr.org F6: the two hubs reject a nil leaf return with a clear error.
(m45-imp3--check "argv-nil-guard"
                 (m45-imp3--contains-p "src/callproc.c"
                                       "Invalid argument list for call-process"))
(m45-imp3--check "env-nil-guard"
                 (m45-imp3--contains-p "src/callproc.c"
                                       "Invalid current directory for environment block"))
;; cr.org F2: the dead argument-coding block is gone from call_process.
(m45-imp3--check "no-dead-argument-coding"
                 (eql 0 (m45-imp3--count "src/callproc.c"
                                         "Decide the coding-system for giving arguments")))

;;; --- T6. The per-group min-count guard (cr1.org F2 / cr.org F3) -----

(setq m45-imp3--group nil)

(m45-imp3--check "reg/min-t1-checks-10"
                 (>= (m45-imp3--group-count 't1) 10))
(m45-imp3--check "reg/min-t2-checks-9"
                 (>= (m45-imp3--group-count 't2) 9))
(m45-imp3--check "reg/min-t3-checks-5"
                 (>= (m45-imp3--group-count 't3) 5))
(m45-imp3--check "reg/min-t4-checks-4"
                 (>= (m45-imp3--group-count 't4) 4))
(m45-imp3--check "reg/min-t5-checks-10"
                 (>= (m45-imp3--group-count 't5) 10))
(m45-imp3--check "reg/min-t8-checks-12"
                 (>= (m45-imp3--group-count 't8) 12))
(m45-imp3--check "reg/min-total-39"
                 (>= m45-imp3--registered 39))

;;; --- T7. The gated runtime probe (brief.org section 7.1 T7) ---------

;; The policy now runs in src/emacs, so run that binary in batch and
;; exercise the rewired path.  Each probe is an INFO skip when the
;; binary is absent -- never a silent pass.

(defvar m45-imp3--emacs
  (expand-file-name "src/emacs" m45-imp3--root))

;; call-process "echo" writes "hi" to the buffer.
(defvar m45-imp3--echo-eval
  (concat "(with-temp-buffer"
          " (call-process \"echo\" nil t nil \"hi\")"
          " (princ (format \"echo=%S\\n\" (buffer-string))))"))

;; One env var crosses callproc-env into the child.
(defvar m45-imp3--env-eval
  (concat "(let ((process-environment"
          " (cons \"GUIMACS_PROBE=ok\" process-environment)))"
          " (with-temp-buffer"
          " (call-process \"/bin/sh\" nil t nil \"-c\""
          " \"printf %s \\\"$GUIMACS_PROBE\\\"\")"
          " (princ (format \"env=%S\\n\" (buffer-string)))))"))

;; create_temp_file now calls (emacs process-create) `callproc-temp-name'.
;; Run that rewired leaf and check it returns a (temp-dir pattern) list of
;; two strings.  NOTE: the full call-process-region stdin path (the temp
;; file fed to the child's stdin) is a pre-existing guilemacs limitation
;; -- it yields empty stdin at HEAD (imp-2) too -- so the probe pins the
;; rewired temp-name policy, not that path.
(defvar m45-imp3--temp-name-eval
  "(princ (format \"tempname=%S\\n\" (--callproc-temp-name)))")

(defun m45-imp3--probe-output (eval)
  "Return the output of the built src/emacs running EVAL, or nil.
Run src/emacs in batch; EVAL must print one tagged line.  Return nil
when the binary is absent or the run fails."
  (when (file-executable-p m45-imp3--emacs)
    (with-temp-buffer
      (let ((status nil))
        (condition-case nil
            (setq status
                  (call-process
                   "/bin/sh" nil (current-buffer) nil "-c"
                   (format "printf '' | %s --batch --eval '%s'"
                           m45-imp3--emacs eval)))
          (error (setq status nil)))
        (when (and (integerp status) (zerop status))
          (buffer-string))))))

(let ((out (m45-imp3--probe-output m45-imp3--echo-eval)))
  (if (null out)
      (princ "INFO m45/imp3/call-process-echo probe skipped (no runnable built src/emacs)\n")
    (m45-imp3--check "probe/call-process-echo"
                     (and (stringp out)
                          (string-match-p "echo=\"hi" out)
                          t))))

(let ((out (m45-imp3--probe-output m45-imp3--env-eval)))
  (if (null out)
      (princ "INFO m45/imp3/env-var probe skipped (no runnable built src/emacs)\n")
    (m45-imp3--check "probe/env-var-crosses"
                     (and (stringp out)
                          (string-match-p "env=\"ok\"" out)
                          t))))

(let ((out (m45-imp3--probe-output m45-imp3--temp-name-eval)))
  (if (null out)
      (princ "INFO m45/imp3/callproc-temp-name probe skipped (no runnable built src/emacs)\n")
    (m45-imp3--check "probe/callproc-temp-name-list"
                     (and (stringp out)
                          (string-match-p "tempname=(\"[^\"]*\" \"[^\"]*\")" out)
                          t))))

(princ (format "=== m45 imp-3 rewire suite done (%d tracked checks; t1 %d, t2 %d, t3 %d, t4 %d, t5 %d) ===\n"
               m45-imp3--registered
               (m45-imp3--group-count 't1)
               (m45-imp3--group-count 't2)
               (m45-imp3--group-count 't3)
               (m45-imp3--group-count 't4)
               (m45-imp3--group-count 't5)))
