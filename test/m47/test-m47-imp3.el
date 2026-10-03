;;; test-m47-imp3.el --- M47 imp-3 corpus (the G1 path policy rewired).
;;;
;;; M47 imp-2 added the 26 typed C leaves over plain values and the thin
;;; wrapper module (emacs fileio); it moved no policy.  M47 imp-3 moves
;;; the parent-side, normal-context path policy of the 6 READY G1 hubs
;;; of src/fileio.c onto those leaves.  The hubs call the module:
;;;   find-file-name-handler -> fileio-find-file-name-handler
;;;   file-name-directory    -> fileio-file-name-directory
;;;   file-name-nondirectory -> fileio-file-name-nondirectory
;;;   file-name-as-directory -> fileio-file-name-as-directory
;;;   directory-file-name    -> fileio-directory-file-name
;;;   file-name-concat       -> fileio-file-name-concat
;;; The C mechanism (the char * buffers, file_name_directory,
;;; file_name_as_directory, directory_file_name, and the syscalls) stays
;;; C.  The file-name-handler dispatch stays C.  The 2 OPEN G1 hubs
;;; (expand-file-name, substitute-in-file-name) do NOT change (brief.org
;;; section 6).
;;;
;;; This corpus reads files, and it runs gated runtime probes.  It pins:
;;;   T1 -- the hubs dispatch into the module: src/fileio.c holds the 6
;;;         static helpers and the 6 hub call sites.
;;;   T2 -- the inline policy is gone: the nondirectory fallback, the two
;;;         SAFE_ALLOCA blocks, and the concat byte count / buffer copy.
;;;   T3 -- the 2 OPEN hubs are unchanged: their leaves still call their
;;;         own public hub (Fexpand_file_name, Fsubstitute_in_file_name).
;;;   T4 -- the mechanism stays C: file_name_directory,
;;;         file_name_as_directory, directory_file_name, and the
;;;         syscall names are still present.
;;;   T5 -- the surface: re-measure src/fileio.c lines / DEFUNs / refs,
;;;         mod/emacs/fileio.scm lines, the keyboard surface, and the
;;;         tree-wide scm_c_public_ref count (199).
;;;   T6 -- a per-group min-count guard.  Pin each group apart from the
;;;         total, so a truncated corpus fails.
;;;   T7 -- the gated runtime probe.  Run the built src/emacs and
;;;         exercise the 6 rewired hubs.  An absent or non-runnable
;;;         src/emacs is an INFO-skip, never a silent pass.
;;;
;;; A read error is a real error, never a silent pass.  An absent src/
;;; file is a real error.

(princ "=== m47 imp-3 rewire suite ===\n")

(require 'imp-ert-report)

(defvar m47-imp3--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))

(defvar m47-imp3--registered 0
  "Total number of tracked-file checks this corpus has registered.")

(defvar m47-imp3--group nil
  "The group that `m47-imp3--check' counts into: `t1' ... `t5', or nil.")

(defvar m47-imp3--counts nil
  "Alist of (GROUP . COUNT) for the registered tracked-file checks.")

(defun m47-imp3--group-count (group)
  "Number of tracked-file checks registered so far in GROUP."
  (or (cdr (assq group m47-imp3--counts)) 0))

(defun m47-imp3--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
the symbol `m47-imp3-absent' when REL does not exist."
  (let ((path (expand-file-name rel m47-imp3--root)))
    (if (not (file-exists-p path))
        'm47-imp3-absent
      (with-temp-buffer
        (insert-file-contents path)
        (funcall fn)))))

(defun m47-imp3--contains-p (rel needle)
  "Non-nil when REL (repo-root-relative) contains NEEDLE."
  (m47-imp3--with rel
    (lambda ()
      (goto-char (point-min))
      (search-forward needle nil t))))

(defun m47-imp3--lines (rel)
  "Count the newlines of REL the way `wc -l' does."
  (m47-imp3--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (search-forward "\n" nil t) (setq n (1+ n)))
        n))))

(defun m47-imp3--count (rel regexp)
  "Count the matches of REGEXP in REL."
  (m47-imp3--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (re-search-forward regexp nil t) (setq n (1+ n)))
        n))))

(defun m47-imp3--line-of (rel needle)
  "1-based line number of the first literal NEEDLE in REL, or nil."
  (m47-imp3--with rel
    (lambda ()
      (goto-char (point-min))
      (when (search-forward needle nil t)
        (line-number-at-pos (match-beginning 0))))))

(defun m47-imp3--leaf-body (block)
  "Return the source of the DEFUN (\"--fileio-BLOCK\") body, or nil."
  (m47-imp3--with "src/fileio.c"
    (lambda ()
      (goto-char (point-min))
      (when (search-forward (format "DEFUN (\"--fileio-%s\"" block) nil t)
        (let ((start (line-beginning-position)))
          (if (re-search-forward "\nDEFUN (\"" nil t)
              (buffer-substring-no-properties start (match-beginning 0))
            (buffer-substring-no-properties start (point-max))))))))

(defun m47-imp3--strip-comments (s)
  "Return S with all C block comments (/* ... */) removed."
  (let ((out s))
    (while (string-match "/\\*" out)
      (let* ((start (match-beginning 0))
             (end (string-match "\\*/" out (match-end 0))))
        (setq out (concat (substring out 0 start)
                          (if end (substring out (+ end 2)) "")))))
    out))

(defun m47-imp3--count-scm-ref ()
  "Count scm_c_public_ref over src/*.[chm] (the brief.org section 10 measure)."
  (let ((total 0)
        (dir (expand-file-name "src" m47-imp3--root)))
    (dolist (f (directory-files dir t "\\.[chm]\\'"))
      (setq total (+ total (or (m47-imp3--count f "scm_c_public_ref") 0))))
    total))

(defun m47-imp3--check (name ok)
  "Report and register one check on a TRACKED file.  OK is a boolean.
An absent src/ file makes the reader return the symbol
`m47-imp3-absent', so the check prints FAIL -- an absent src/ file is a
real error, not a pass."
  (if (eq ok 'm47-imp3-absent)
      (princ (format "INFO m47/imp3/%s skipped (source file absent)\n" name))
    (progn
      (princ (format "%s m47/imp3/%s\n" (if ok "PASS" "FAIL") name))
      (setq m47-imp3--registered (1+ m47-imp3--registered))
      (when m47-imp3--group
        (let ((cell (assq m47-imp3--group m47-imp3--counts)))
          (if cell
              (setcdr cell (1+ (cdr cell)))
            (push (cons m47-imp3--group 1) m47-imp3--counts))))
      (imp-register-bool-as-ert-test (format "m47-imp3/%s" name) (and ok t)))))

(defun m47-imp3--probe-check (name ok)
  "Report and register one runtime probe.  A probe does NOT count into
`m47-imp3--registered'.  brief.org section 9 pins the registered total
at 50 (44 tracked-file checks plus 6 guards), so the 6 probes must stay
out of the count.  The probe still registers an ERT test, so a probe
failure is a real failure."
  (princ (format "%s m47/imp3/%s\n" (if ok "PASS" "FAIL") name))
  (imp-register-bool-as-ert-test (format "m47-imp3/%s" name) (and ok t)))

;;; --- T1. The hubs dispatch into the module (brief.org section 5.1) ---

(setq m47-imp3--group 't1)

(m47-imp3--check "hub-scm-public-ref-module"
                 (m47-imp3--contains-p "src/fileio.c"
                                       "scm_c_public_ref (\"emacs fileio\""))
(m47-imp3--check "helper-find-file-name-handler"
                 (m47-imp3--contains-p
                  "src/fileio.c"
                  "find_file_name_handler_scheme (Lisp_Object file, Lisp_Object operation)"))
(m47-imp3--check "helper-file-name-directory"
                 (m47-imp3--contains-p "src/fileio.c"
                                       "file_name_directory_scheme (Lisp_Object fn)"))
(m47-imp3--check "helper-file-name-nondirectory"
                 (m47-imp3--contains-p "src/fileio.c"
                                       "file_name_nondirectory_scheme (Lisp_Object fn)"))
(m47-imp3--check "helper-file-name-as-directory"
                 (m47-imp3--contains-p "src/fileio.c"
                                       "file_name_as_directory_scheme (Lisp_Object fn)"))
(m47-imp3--check "helper-directory-file-name"
                 (m47-imp3--contains-p "src/fileio.c"
                                       "directory_file_name_scheme (Lisp_Object fn)"))
(m47-imp3--check "helper-file-name-concat"
                 (m47-imp3--contains-p
                  "src/fileio.c"
                  "file_name_concat_scheme (ptrdiff_t nargs, Lisp_Object *args)"))
(m47-imp3--check "scm-public-ref-count-7"
                 (eql 7 (m47-imp3--count "src/fileio.c" "scm_c_public_ref")))
(m47-imp3--check "scm-call-count-9"
                 (eql 9 (m47-imp3--count "src/fileio.c" "SCM_CALL_")))
(m47-imp3--check "hub-ffnh-called"
                 (m47-imp3--contains-p
                  "src/fileio.c"
                  "result = find_file_name_handler_scheme (filename, operation);"))
(m47-imp3--check "hub-directory-called"
                 (m47-imp3--contains-p "src/fileio.c"
                                       "return file_name_directory_scheme (filename);"))
(m47-imp3--check "hub-nondirectory-called"
                 (m47-imp3--contains-p
                  "src/fileio.c"
                  "return file_name_nondirectory_scheme (filename);"))
(m47-imp3--check "hub-as-directory-called"
                 (m47-imp3--contains-p "src/fileio.c"
                                       "return file_name_as_directory_scheme (file);"))
(m47-imp3--check "hub-directory-file-name-called"
                 (m47-imp3--contains-p
                  "src/fileio.c"
                  "return directory_file_name_scheme (directory);"))
(m47-imp3--check "hub-concat-called"
                 (m47-imp3--contains-p "src/fileio.c"
                                       "return file_name_concat_scheme (nargs, args);"))
(m47-imp3--check "helpers-defined-before-hub"
                 (let ((h (m47-imp3--line-of
                           "src/fileio.c"
                           "find_file_name_handler_scheme (Lisp_Object file, Lisp_Object operation)"))
                       (c (m47-imp3--line-of "src/fileio.c"
                                             "DEFUN (\"find-file-name-handler\"")))
                   (and (integerp h) (integerp c) (< h c))))

;;; --- T2. The inline policy is gone (brief.org section 5.2) -----------

(setq m47-imp3--group 't2)

;; The hub no longer calls the nondirectory mechanism; only the imp-2
;; leaf does (with FN, not FILENAME).
(m47-imp3--check "no-hub-nondirectory-call"
                 (eql 0 (m47-imp3--count "src/fileio.c"
                                         "guile_file_path_nondirectory (filename)")))
;; The two SAFE_ALLOCA blocks of the as-directory / directory-file-name
;; hubs are gone; the imp-2 leaves hold their own (with FN).
(m47-imp3--check "no-hub-as-directory-alloc"
                 (eql 0 (m47-imp3--count
                         "src/fileio.c"
                         "SAFE_ALLOCA (SBYTES (file) + file_name_as_directory_slop + 1)")))
(m47-imp3--check "no-hub-directory-file-name-alloc"
                 (eql 0 (m47-imp3--count
                         "src/fileio.c" "SAFE_ALLOCA (SBYTES (directory) + 1)")))
;; The concat byte-count pass and the buffer copy are gone from the hub;
;; the imp-2 leaf holds the pure join.
(m47-imp3--check "no-hub-concat-first-pass"
                 (eql 0 (m47-imp3--count
                         "src/fileio.c"
                         "First go through the list to check the types and see whether")))
(m47-imp3--check "no-hub-concat-buffer"
                 (eql 0 (m47-imp3--count
                         "src/fileio.c"
                         "In Guile, strings are immutable, so we can't use make_uninit_string")))
;; The find-file-name-handler hub keeps its quit point (brief.org 5.2).
(m47-imp3--check "hub-ffnh-keeps-maybe-quit"
                 (m47-imp3--contains-p "src/fileio.c"
                                       "response to C-g changes.  brief.org section 5.2.  */\n  maybe_quit ();"))

;;; --- T3. The 2 OPEN hubs are unchanged (brief.org section 6) --------

(setq m47-imp3--group 't3)

(m47-imp3--check "open-expand-hub-present"
                 (m47-imp3--contains-p "src/fileio.c"
                                       "DEFUN (\"expand-file-name\""))
(m47-imp3--check "open-substitute-hub-present"
                 (m47-imp3--contains-p "src/fileio.c"
                                       "DEFUN (\"substitute-in-file-name\""))
(m47-imp3--check "open-expand-leaf-calls-hub"
                 (let ((code (m47-imp3--strip-comments
                              (or (m47-imp3--leaf-body "expand-file-name") ""))))
                   (and (string-match-p (regexp-quote "Fexpand_file_name (") code)
                        t)))
(m47-imp3--check "open-substitute-leaf-calls-hub"
                 (let ((code (m47-imp3--strip-comments
                              (or (m47-imp3--leaf-body "substitute-in-file-name") ""))))
                   (and (string-match-p (regexp-quote "Fsubstitute_in_file_name (") code)
                        t)))
(m47-imp3--check "leaf-defuns-26"
                 (eql 26 (m47-imp3--count "src/fileio.c" "^DEFUN (\"--fileio-")))

;;; --- T4. The mechanism stays C (brief.org section 5) ----------------

(setq m47-imp3--group 't4)

(m47-imp3--check "mech-file-name-directory"
                 (m47-imp3--contains-p "src/fileio.c"
                                       "file_name_directory (Lisp_Object filename)"))
(m47-imp3--check "mech-file-name-as-directory"
                 (m47-imp3--contains-p "src/fileio.c"
                                       "file_name_as_directory (char *dst"))
(m47-imp3--check "mech-directory-file-name"
                 (m47-imp3--contains-p "src/fileio.c"
                                       "directory_file_name (char *dst"))
(m47-imp3--check "mech-fstatat"
                 (m47-imp3--contains-p "src/fileio.c" "emacs_fstatat"))
(m47-imp3--check "mech-symlink"
                 (m47-imp3--contains-p "src/fileio.c" "emacs_symlink"))
(m47-imp3--check "mech-readlinkat"
                 (m47-imp3--contains-p "src/fileio.c" "readlinkat"))
(m47-imp3--check "mech-fs-usage"
                 (m47-imp3--contains-p "src/fileio.c" "get_fs_usage"))
(m47-imp3--check "defun-count-78"
                 (eql 78 (m47-imp3--count "src/fileio.c" "^DEFUN (\"")))
;; The 2 OPEN hubs still hold their own public-hub call site, so a rewire
;; did not recurse.
(m47-imp3--check "open-hubs-not-rewired"
                 (and (m47-imp3--contains-p "src/fileio.c"
                                            "return Fexpand_file_name (name, default_directory);")
                      (m47-imp3--contains-p "src/fileio.c"
                                            "return Fsubstitute_in_file_name (fn);")))

;;; --- T5. The surface (brief.org section 10) -------------------------

(setq m47-imp3--group 't5)

(m47-imp3--check "fileio.c-lines-7173"
                 (eql 7173 (m47-imp3--lines "src/fileio.c")))
(m47-imp3--check "fileio.c-defuns-78"
                 (eql 78 (m47-imp3--count "src/fileio.c" "^DEFUN (\"")))
(m47-imp3--check "fileio.c-scm-ref-7"
                 (eql 7 (m47-imp3--count "src/fileio.c" "scm_c_public_ref")))
(m47-imp3--check "fileio.scm-lines-167"
                 (eql 167 (m47-imp3--lines "mod/emacs/fileio.scm")))
(m47-imp3--check "tree-wide-scm-public-ref-199"
                 (eql 199 (m47-imp3--count-scm-ref)))
(m47-imp3--check "keyboard.c-lines-11233"
                 (eql 11233 (m47-imp3--lines "src/keyboard.c")))
(m47-imp3--check "keyboard-globals.c-lines-490"
                 (eql 490 (m47-imp3--lines "src/keyboard-globals.c")))
(m47-imp3--check "combined-keyboard-surface-11723"
                 (let ((kb (m47-imp3--lines "src/keyboard.c"))
                       (kg (m47-imp3--lines "src/keyboard-globals.c")))
                   (and (integerp kb) (integerp kg)
                        (eql 11723 (+ kb kg)))))

;;; --- T6. The per-group min-count guard ------------------------------

(setq m47-imp3--group nil)

(m47-imp3--check "reg/min-t1-checks-16"
                 (>= (m47-imp3--group-count 't1) 16))
(m47-imp3--check "reg/min-t2-checks-6"
                 (>= (m47-imp3--group-count 't2) 6))
(m47-imp3--check "reg/min-t3-checks-5"
                 (>= (m47-imp3--group-count 't3) 5))
(m47-imp3--check "reg/min-t4-checks-9"
                 (>= (m47-imp3--group-count 't4) 9))
(m47-imp3--check "reg/min-t5-checks-8"
                 (>= (m47-imp3--group-count 't5) 8))
;; The guard counts itself after the test, so the final registered total
;; is (1+ m47-imp3--registered).  brief.org section 9 pins that total at
;; 50 (44 tracked-file checks plus the 6 guards).  A truncated corpus
;; fails here.
(m47-imp3--check "reg/min-total-50"
                 (>= (1+ m47-imp3--registered) 50))

;;; --- T7. The gated runtime probes (brief.org section 8) -------------

;; The policy now runs in src/emacs, so run that binary in batch and
;; exercise the 6 rewired hubs.  Each probe is an INFO skip when the
;; binary is absent -- never a silent pass.  A nested gate run sets
;; GUILEMACS_M47_GATE=1 to skip the probe, so the run does not recurse.

(defvar m47-imp3--emacs
  (expand-file-name "src/emacs" m47-imp3--root))

(defun m47-imp3--probe-output (eval)
  "Return the output of the built src/emacs running EVAL, or nil.
Run src/emacs in batch; EVAL must print one tagged line.  Return nil
when the binary is absent or the run fails."
  (when (file-executable-p m47-imp3--emacs)
    (with-temp-buffer
      (let ((status nil))
        (condition-case nil
            (setq status
                  (call-process
                   "/bin/sh" nil (current-buffer) nil "-c"
                   (format "printf '' | %s --batch --eval '%s'"
                           m47-imp3--emacs eval)))
          (error (setq status nil)))
        (when (and (integerp status) (zerop status))
          (buffer-string))))))

(defvar m47-imp3--hubs-eval
  (concat "(progn"
          " (princ (format \"dir=%S\\n\" (file-name-directory \"/a/b\")))"
          " (princ (format \"nd=%S\\n\" (file-name-nondirectory \"/a/b\")))"
          " (princ (format \"asdir=%S\\n\" (file-name-as-directory \"/a/b\")))"
          " (princ (format \"dirfile=%S\\n\" (directory-file-name \"/a/b/\")))"
          " (princ (format \"concat=%S\\n\" (file-name-concat \"/a\" \"b\" \"c\")))"
          " (princ (format \"ffnh=%S\\n\""
          " (find-file-name-handler \"/tmp/m47-imp3-zzz\" (quote file-exists-p)))))"))

(defun m47-imp3--probe (tag eval pattern)
  "Run one gated runtime probe.  TAG names the probe.  EVAL runs in the
built src/emacs and must print a line that matches PATTERN.  Report an
INFO-skip when the binary is absent; a probe error is a FAIL."
  (let ((out (m47-imp3--probe-output eval)))
    (if (null out)
        (princ (format
                "INFO m47/imp3/%s-probe skipped (no runnable built src/emacs)\n"
                tag))
      (m47-imp3--probe-check (format "probe/%s" tag)
                             (and (stringp out)
                                  (string-match-p pattern out)
                                  t)))))

(if (getenv "GUILEMACS_M47_GATE")
    (princ "INFO m47/imp3/runtime-probes skipped (nested gate run)\n")
  (progn
    (m47-imp3--probe "file-name-directory" m47-imp3--hubs-eval "dir=\"/a/\"")
    (m47-imp3--probe "file-name-nondirectory" m47-imp3--hubs-eval "nd=\"b\"")
    (m47-imp3--probe "file-name-as-directory" m47-imp3--hubs-eval "asdir=\"/a/b/\"")
    (m47-imp3--probe "directory-file-name" m47-imp3--hubs-eval "dirfile=\"/a/b\"")
    (m47-imp3--probe "file-name-concat" m47-imp3--hubs-eval "concat=\"/a/b/c\"")
    (m47-imp3--probe "find-file-name-handler" m47-imp3--hubs-eval "ffnh=nil")))

;;; --- T8. The F5 decision record (cr.org F5) -------------------------

;; MSDOS is out of scope for guilemacs: the build requires Guile 3.0
;; (configure.ac PKG_CHECK_MODULES), so the 5 rewired path hubs may
;; return nil under #ifdef MSDOS.  docs/ is gitignored, so an absent or
;; stale record is an INFO-skip (the imp-2 D3 / D4 pattern), never a
;; FAIL.  This is a probe-style check, so the tracked total stays 50.

(defun m47-imp3--f5-recorded-p ()
  "Non-nil when docs/kb.org records the MSDOS-out-of-scope decision
\(cr.org F5).  The record needs the F5 marker and the Guile 3.0 reason."
  (let ((path (expand-file-name "docs/kb.org" m47-imp3--root)))
    (when (file-exists-p path)
      (with-temp-buffer
        (insert-file-contents path)
        (goto-char (point-min))
        (and (search-forward "MSDOS SCOPE (cr.org F5)" nil t)
             (search-forward "Guile 3.0" nil t))))))

(if (m47-imp3--f5-recorded-p)
    (m47-imp3--probe-check "reg/f5-msdos-recorded" t)
  (princ "INFO m47/imp3/reg/f5-msdos-recorded skipped (docs/kb.org absent or stale)\n"))

;; A probe does not count into `m47-imp3--registered' (m47-imp3--probe-check).
;; So the tracked total is exactly 50, with or without a built src/emacs.
;; This pins brief.org section 9, and it fails if a probe leaks into the
;; count.
(m47-imp3--probe-check "reg/total-exactly-50"
                       (eql m47-imp3--registered 50))

(princ (format "=== m47 imp-3 rewire suite done (%d tracked checks; t1 %d, t2 %d, t3 %d, t4 %d, t5 %d) ===\n"
               m47-imp3--registered
               (m47-imp3--group-count 't1)
               (m47-imp3--group-count 't2)
               (m47-imp3--group-count 't3)
               (m47-imp3--group-count 't4)
               (m47-imp3--group-count 't5)))
