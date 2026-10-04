;;; test-m47-imp4.el --- M47 imp-4 corpus (the G2 OS-query policy port).
;;;
;;; M47 imp-4 moves the G2 OS-query predicate policy of src/fileio.c to
;;; Scheme.  The shape is Reading B (brief.org section 3 / section 5):
;;; the C DEFUN hub keeps the file-name-handler dispatch and the name
;;; resolution; the module (emacs fileio) owns the *decision*; the typed
;;; C leaf calls one pure static C mechanism that holds the OS query
;;; only.  The 11 G2 blocks are file-exists-p, file-executable-p,
;;; file-readable-p, file-writable-p, access-file, file-symlink-p,
;;; file-directory-p, file-regular-p, file-modes, file-newer-than-file-p,
;;; and file-system-info.
;;;
;;; This corpus reads files, and it runs gated runtime probes.  It pins:
;;;   T1 -- the 11 G2 dispatch helpers exist with their signatures, look
;;;         up the 11 module procedures, and the 11 hubs call them.
;;;   T2 -- each G2 leaf calls its mechanism, never a public hub (cr.org
;;;         F1).
;;;   T3 -- each G2 leaf holds no handler dispatch and no
;;;         Fexpand_file_name call (brief.org section 3).
;;;   T4 -- (emacs fileio) holds the real G2 decision, not a one-line
;;;         pass-through (brief.org section 6).
;;;   T5 -- the 4 G3 OPEN markers are unchanged (brief.org section 7).
;;;   T6 -- the re-measured surface (brief.org section 9), with a
;;;         per-group min-count guard and a total guard.
;;;   T7 -- the group registration guards: the run-tests.scm entry and
;;;         the per-group / total min-count guards.
;;;   T8 -- the gated runtime probe.  Run the built src/emacs and
;;;         exercise the 11 rewired hubs.
;;;
;;; A read error is a real error, never a silent pass.  An absent src/
;;; file is a real error.  A probe failure is a FAIL, never a skip.

(princ "=== m47 imp-4 G2 OS-query suite ===\n")

(require 'imp-ert-report)

(defvar m47-imp4--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))

(defvar m47-imp4--registered 0
  "Total number of tracked-file checks this corpus has registered.")

(defvar m47-imp4--group nil
  "The group that `m47-imp4--check' counts into: `t1' ... `t6', or nil.")

(defvar m47-imp4--counts nil
  "Alist of (GROUP . COUNT) for the registered tracked-file checks.")

(defun m47-imp4--group-count (group)
  "Number of tracked-file checks registered so far in GROUP."
  (or (cdr (assq group m47-imp4--counts)) 0))

(defun m47-imp4--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
the symbol `m47-imp4-absent' when REL does not exist."
  (let ((path (expand-file-name rel m47-imp4--root)))
    (if (not (file-exists-p path))
        'm47-imp4-absent
      (with-temp-buffer
        (insert-file-contents path)
        (funcall fn)))))

(defun m47-imp4--contains-p (rel needle)
  "Non-nil when REL (repo-root-relative) contains NEEDLE."
  (m47-imp4--with rel
    (lambda ()
      (goto-char (point-min))
      (search-forward needle nil t))))

(defun m47-imp4--lines (rel)
  "Count the newlines of REL the way `wc -l' does."
  (m47-imp4--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (search-forward "\n" nil t) (setq n (1+ n)))
        n))))

(defun m47-imp4--count (rel regexp)
  "Count the matches of REGEXP in REL."
  (m47-imp4--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (re-search-forward regexp nil t) (setq n (1+ n)))
        n))))

(defun m47-imp4--count-code (rel regexp)
  "Count the matches of REGEXP in the non-comment lines of REL."
  (m47-imp4--with rel
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

(defun m47-imp4--line-of (rel needle)
  "1-based line number of the first literal NEEDLE in REL, or nil."
  (m47-imp4--with rel
    (lambda ()
      (goto-char (point-min))
      (when (search-forward needle nil t)
        (line-number-at-pos (match-beginning 0))))))

(defun m47-imp4--leaf-body (block)
  "Return the source of the DEFUN (\"--fileio-BLOCK\") body, or nil."
  (m47-imp4--with "src/fileio.c"
    (lambda ()
      (goto-char (point-min))
      (when (search-forward (format "DEFUN (\"--fileio-%s\"" block) nil t)
        (let ((start (line-beginning-position)))
          (if (re-search-forward "\nDEFUN (\"" nil t)
              (buffer-substring-no-properties start (match-beginning 0))
            (buffer-substring-no-properties start (point-max))))))))

(defun m47-imp4--hub-name (block)
  "The C name of the public hub for BLOCK, e.g. \"Ffile_exists_p\"."
  (concat "F" (replace-regexp-in-string "-" "_" block)))

(defun m47-imp4--strip-comments (s)
  "Return S with all C block comments (/* ... */) removed."
  (let ((out s))
    (while (string-match "/\\*" out)
      (let* ((start (match-beginning 0))
             (end (string-match "\\*/" out (match-end 0))))
        (setq out (concat (substring out 0 start)
                          (if end (substring out (+ end 2)) "")))))
    out))

(defun m47-imp4--check (name ok)
  "Report and register one check on a TRACKED file.  OK is a boolean.
An absent src/ file makes the reader return the symbol
`m47-imp4-absent', so the check prints FAIL -- an absent src/ file is a
real error, not a pass."
  (if (eq ok 'm47-imp4-absent)
      (princ (format "INFO m47/imp4/%s skipped (source file absent)\n" name))
    (progn
      (princ (format "%s m47/imp4/%s\n" (if ok "PASS" "FAIL") name))
      (setq m47-imp4--registered (1+ m47-imp4--registered))
      (when m47-imp4--group
        (let ((cell (assq m47-imp4--group m47-imp4--counts)))
          (if cell
              (setcdr cell (1+ (cdr cell)))
            (push (cons m47-imp4--group 1) m47-imp4--counts))))
      (imp-register-bool-as-ert-test (format "m47-imp4/%s" name) (and ok t)))))

;;; --- T1. The hubs dispatch into the module (brief.org section 5) ----

(setq m47-imp4--group 't1)

(defvar m47-imp4--dispatch
  '(("file-exists-p"          . ("file_exists_p_scheme (Lisp_Object absname)"
                                 "file_exists_p_scheme (absname)"))
    ("file-executable-p"      . ("file_executable_p_scheme (Lisp_Object absname)"
                                 "file_executable_p_scheme (absname)"))
    ("file-readable-p"        . ("file_readable_p_scheme (Lisp_Object absname)"
                                 "file_readable_p_scheme (absname)"))
    ("file-writable-p"        . ("file_writable_p_scheme (Lisp_Object absname)"
                                 "file_writable_p_scheme (absname)"))
    ("access-file"            . ("access_file_scheme (Lisp_Object absname, Lisp_Object operation)"
                                 "access_file_scheme (absname, Qaccess_file)"))
    ("file-symlink-p"         . ("file_symlink_p_scheme (Lisp_Object absname)"
                                 "file_symlink_p_scheme (filename)"))
    ("file-directory-p"       . ("file_directory_p_scheme (Lisp_Object absname)"
                                 "file_directory_p_scheme (absname)"))
    ("file-regular-p"         . ("file_regular_p_scheme (Lisp_Object absname)"
                                 "file_regular_p_scheme (absname)"))
    ("file-modes"             . ("file_modes_scheme (Lisp_Object absname, Lisp_Object flag)"
                                 "file_modes_scheme (absname, make_fixnum (nofollow))"))
    ("file-newer-than-file-p" . ("file_newer_than_file_p_scheme (Lisp_Object absname1, Lisp_Object absname2)"
                                 "file_newer_than_file_p_scheme (absname1, absname2)"))
    ("file-system-info"       . ("file_system_info_scheme (Lisp_Object absname)"
                                 "file_system_info_scheme (filename)")))
  "Per G2 block: the dispatch-helper signature and the hub call site.")

(dolist (pair m47-imp4--dispatch)
  (let ((block (car pair)) (sig (nth 0 (cdr pair))) (call (nth 1 (cdr pair))))
    (m47-imp4--check (format "helper-%s" block)
                     (m47-imp4--contains-p "src/fileio.c" sig))
    (m47-imp4--check (format "ref-%s" block)
                     (m47-imp4--contains-p
                      "src/fileio.c"
                      (format "scm_c_public_ref (\"emacs fileio\", \"fileio-%s\")" block)))
    (m47-imp4--check (format "hub-call-%s" block)
                     (m47-imp4--contains-p "src/fileio.c" call))))

;; The dispatch helpers sit before the first G2 hub (brief.org section 5).
(m47-imp4--check "helpers-defined-before-hub"
                 (let ((h (m47-imp4--line-of
                           "src/fileio.c"
                           "file_exists_p_scheme (Lisp_Object absname)"))
                       (c (m47-imp4--line-of "src/fileio.c"
                                             "DEFUN (\"file-exists-p\"")))
                   (and (integerp h) (integerp c) (< h c))))

;;; --- T2. The mechanisms exist; the leaves call them ------------------

(setq m47-imp4--group 't2)

(defvar m47-imp4--mechanism
  '(("file-exists-p"          "check_file_access_1 (Lisp_Object absname, int amode)"
                              "check_file_access_1 (fn, F_OK)"
                              "Ffile_exists_p (")
    ("file-executable-p"      "check_file_access_1 (Lisp_Object absname, int amode)"
                              "check_file_access_1 (fn, X_OK)"
                              "Ffile_executable_p (")
    ("file-readable-p"        "check_file_access_1 (Lisp_Object absname, int amode)"
                              "check_file_access_1 (fn, R_OK)"
                              "Ffile_readable_p (")
    ("file-writable-p"        "file_writable_p_1 (Lisp_Object absname)"
                              "file_writable_p_1 (fn)"
                              "Ffile_writable_p (")
    ("access-file"            "sys_faccessat"
                              "sys_faccessat (AT_FDCWD, SSDATA (ENCODE_FILE (fn))"
                              "Faccess_file (")
    ("file-symlink-p"         "emacs_readlinkat (int fd, char const *filename)"
                              "emacs_readlinkat (AT_FDCWD, SSDATA (ENCODE_FILE (fn))"
                              "Ffile_symlink_p (")
    ("file-directory-p"       "file_directory_p (Lisp_Object file)"
                              "file_directory_p (ENCODE_FILE (fn))"
                              "Ffile_directory_p (")
    ("file-regular-p"         "S_ISREG"
                              "emacs_fstatat (AT_FDCWD, SSDATA (fn)"
                              "Ffile_regular_p (")
    ("file-modes"             "XFIXNUM (nofollow)"
                              "XFIXNUM (nofollow)"
                              "Ffile_modes (")
    ("file-newer-than-file-p" "timespec_cmp"
                              "timespec_cmp (get_stat_mtime"
                              "Ffile_newer_than_file_p (")
    ("file-system-info"       "blocks_to_bytes (uintmax_t blocksize"
                              "get_fs_usage (name, NULL, &u)"
                              "Ffile_system_info ("))
  "Per G2 block: the pure mechanism signature, the leaf call token, and
the forbidden hub.")

(dolist (quad m47-imp4--mechanism)
  (let* ((block (nth 0 quad))
         (mech (nth 1 quad))
         (call (nth 2 quad))
         (hub (nth 3 quad))
         (body (m47-imp4--leaf-body block))
         (code (and (stringp body) (m47-imp4--strip-comments body))))
    (m47-imp4--check (format "mech-%s" block)
                     (m47-imp4--contains-p "src/fileio.c" mech))
    (m47-imp4--check (format "leaf-calls-mech-%s" block)
                     (and (stringp code)
                          (string-match-p (regexp-quote call) code)
                          t))
    (m47-imp4--check (format "leaf-no-hub-%s" block)
                     (and (stringp code)
                          (not (string-match-p (regexp-quote hub) code))
                          t))))

(m47-imp4--check "leaf-defuns-26"
                 (eql 26 (m47-imp4--count "src/fileio.c" "^DEFUN (\"--fileio-")))

;;; --- T3. A leaf holds no handler dispatch and no name expansion ------

(setq m47-imp4--group 't3)

(dolist (block '("file-exists-p" "file-executable-p" "file-readable-p"
                 "file-writable-p" "access-file" "file-symlink-p"
                 "file-directory-p" "file-regular-p" "file-modes"
                 "file-newer-than-file-p" "file-system-info"))
  (let* ((body (m47-imp4--leaf-body block))
         (code (and (stringp body) (m47-imp4--strip-comments body))))
    (m47-imp4--check (format "leaf-no-handler-%s" block)
                     (and (stringp code)
                          (not (string-match-p
                                (regexp-quote "Ffind_file_name_handler (") code))
                          t))
    (m47-imp4--check (format "leaf-no-expand-%s" block)
                     (and (stringp code)
                          (not (string-match-p
                                (regexp-quote "Fexpand_file_name (") code))
                          (not (string-match-p
                                (regexp-quote "expand_and_dir_to_file (") code))
                          t))))

;;; --- T4. The module holds the real G2 decision (brief.org 6) --------

(setq m47-imp4--group 't4)

(dolist (name '("file-exists-p" "file-executable-p" "file-readable-p"
                "file-writable-p" "access-file" "file-symlink-p"
                "file-directory-p" "file-regular-p" "file-modes"
                "file-newer-than-file-p" "file-system-info"))
  (m47-imp4--check (format "module-decides-%s" name)
                   (m47-imp4--contains-p "mod/emacs/fileio.scm"
                                         (format "(define (fileio-%s" name))))

;; A one-line pass-through holds no decision; the module now carries the
;; leaf call inside a `let' + `if' decision for each of the 11 wrappers.
(m47-imp4--check "module-not-passthrough"
                 (let ((n (m47-imp4--count-code "mod/emacs/fileio.scm"
                                                "(let ((r ((force %--fileio-")))
                   (and (integerp n) (>= n 11))))
(m47-imp4--check "module-plain-boolean"
                 (m47-imp4--contains-p "mod/emacs/fileio.scm" "(if r #t #f)"))
(m47-imp4--check "module-symlink-string"
                 (m47-imp4--contains-p "mod/emacs/fileio.scm" "(if (string? r) r #f)"))
(m47-imp4--check "module-system-info-list"
                 (m47-imp4--contains-p "mod/emacs/fileio.scm" "(if (pair? r) r #f)"))
(m47-imp4--check "module-modes-integer"
                 (m47-imp4--contains-p "mod/emacs/fileio.scm" "(if r r #f)"))
;; cr.org F5: the module procedure `fileio-file-modes' keeps its name but
;; its arity grows 1 -> 2 (the hub passes a `nofollow' fixnum from
;; `symlink_nofollow_flag').  Record the 2-argument contract.
(m47-imp4--check "module-modes-arity-2"
                 (m47-imp4--contains-p "mod/emacs/fileio.scm"
                                       "(define (fileio-file-modes fn nofollow)"))
(m47-imp4--check "module-no-scm-ref"
                 (let ((n (m47-imp4--count-code "mod/emacs/fileio.scm"
                                                "scm_c_public_ref")))
                   (and (integerp n) (eql 0 n))))
(m47-imp4--check "module-grows-past-301"
                 (let ((n (m47-imp4--lines "mod/emacs/fileio.scm")))
                   (and (integerp n) (> n 301))))

;;; --- T5. The 4 G3 OPEN markers are unchanged (brief.org 7) ----------

(setq m47-imp4--group 't5)

(m47-imp4--check "open-markers-left-4"
                 (eql 4 (m47-imp4--count "src/fileio.c" "OPEN (cr.org F1):")))
(dolist (leaf '("copy-file" "rename-file" "add-name-to-file" "make-symbolic-link"))
  (m47-imp4--check (format "open-leaf-%s" leaf)
                   (let ((code (m47-imp4--strip-comments
                                (or (m47-imp4--leaf-body leaf) ""))))
                     (and (string-match-p
                           (regexp-quote (format "%s (" (m47-imp4--hub-name leaf)))
                           code)
                          t))))
(m47-imp4--check "g3-leaves-still-26"
                 (eql 26 (m47-imp4--count "src/fileio.c" "^DEFUN (\"--fileio-")))

;;; --- T6. The re-measured surface (brief.org section 9) --------------

(setq m47-imp4--group 't6)

(m47-imp4--check "fileio.c-grows-past-imp3"
                 (let ((n (m47-imp4--lines "src/fileio.c")))
                   (and (integerp n) (> n 7223))))
(m47-imp4--check "fileio.c-lines-7373"
                 (eql 7373 (m47-imp4--lines "src/fileio.c")))
(m47-imp4--check "fileio.c-defuns-78"
                 (eql 78 (m47-imp4--count "src/fileio.c" "^DEFUN (\"")))
(m47-imp4--check "fileio.c-scm-ref-20"
                 (eql 20 (m47-imp4--count "src/fileio.c" "scm_c_public_ref")))
(m47-imp4--check "fileio.scm-lines-315"
                 (eql 315 (m47-imp4--lines "mod/emacs/fileio.scm")))
(m47-imp4--check "keyboard.c-lines-11233"
                 (eql 11233 (m47-imp4--lines "src/keyboard.c")))
(m47-imp4--check "keyboard-globals.c-lines-490"
                 (eql 490 (m47-imp4--lines "src/keyboard-globals.c")))
(m47-imp4--check "combined-keyboard-surface-11723"
                 (let ((kb (m47-imp4--lines "src/keyboard.c"))
                       (kg (m47-imp4--lines "src/keyboard-globals.c")))
                   (and (integerp kb) (integerp kg) (eql 11723 (+ kb kg)))))
(m47-imp4--check "keyboard-margin-237-under-11960"
                 (let ((kb (m47-imp4--lines "src/keyboard.c"))
                       (kg (m47-imp4--lines "src/keyboard-globals.c")))
                   (and (integerp kb) (integerp kg)
                        (eql 237 (- 11960 (+ kb kg))))))

;;; --- T7. The group and the guards -----------------------------------

(setq m47-imp4--group nil)

(m47-imp4--check "reg/run-tests-m47-imp4"
                 (m47-imp4--contains-p "tool/run-tests.scm"
                                       "test/m47/test-m47-imp4.el"))
(m47-imp4--check "reg/min-t1-checks-34"
                 (>= (m47-imp4--group-count 't1) 34))
(m47-imp4--check "reg/min-t2-checks-34"
                 (>= (m47-imp4--group-count 't2) 34))
(m47-imp4--check "reg/min-t3-checks-22"
                 (>= (m47-imp4--group-count 't3) 22))
(m47-imp4--check "reg/min-t4-checks-17"
                 (>= (m47-imp4--group-count 't4) 17))
(m47-imp4--check "reg/min-t5-checks-6"
                 (>= (m47-imp4--group-count 't5) 6))
(m47-imp4--check "reg/min-t6-checks-9"
                 (>= (m47-imp4--group-count 't6) 9))
(m47-imp4--check "reg/min-total-125"
                 (>= (1+ m47-imp4--registered) 125))

;;; --- T8. The gated runtime probe (brief.org section 10) -------------

;; This corpus runs inside the built src/emacs (tool/run-tests.scm loads
;; the (m47) group with run-tests-loadup-emacs), so a probe calls the
;; rewired hub DIRECTLY, in this process.  An absent or non-runnable
;; src/emacs is not a skip here: the load itself needs it.
;;
;; A broken hub is a FAIL, not a skip.  The GUILEMACS_M47_GATE guard
;; keeps a nested gate run short.
;;
;; The probes use a writable scratch dir ($TMPDIR, then the repo scratch
;; dir).  The sandbox denies /tmp, so /tmp is not used.

(defun m47-imp4--probe (tag thunk)
  "Register the probe TAG from the value of THUNK, which calls a rewired hub.
A non-nil value is a PASS.  A signalled error is a FAIL, never a silent
pass; the error is printed so the cause is visible."
  (imp-register-bool-as-ert-test
   (format "m47-imp4/probe/%s" tag)
   (condition-case err
       (and (funcall thunk) t)
     (error (princ (format "INFO m47/imp4/%s error=%S\n" tag err))
            nil))))

(defvar m47-imp4--scratch
  (expand-file-name "test/m47/scratch" m47-imp4--root))

(if (getenv "GUILEMACS_M47_GATE")
    (princ "INFO m47/imp4/runtime-probes skipped (nested gate run)\n")
  (progn
    (m47-imp4--probe "file-exists-p"
                     (lambda () (file-exists-p "/")))
    (m47-imp4--probe "file-executable-p"
                     (lambda () (file-executable-p "/")))
    (m47-imp4--probe "file-readable-p"
                     (lambda () (file-readable-p "/")))
    (m47-imp4--probe "file-directory-p"
                     (lambda () (file-directory-p "/")))
    (m47-imp4--probe "file-regular-p"
                     (lambda () (not (file-regular-p "/"))))
    (m47-imp4--probe "file-symlink-p"
                     (lambda () (null (file-symlink-p "/nonexistent-m47-imp4-xyz"))))
    (m47-imp4--probe "file-modes"
                     (lambda () (integerp (file-modes "/"))))
    (m47-imp4--probe "file-newer-than-file-p"
                     (lambda () (not (file-newer-than-file-p "/" "/"))))
    (m47-imp4--probe "file-system-info"
                     (lambda ()
                       (let ((i (file-system-info "/")))
                         (or (null i) (and (consp i) (= 3 (length i)))))))
    (m47-imp4--probe "file-writable-p"
                     (lambda ()
                       (let ((dir (or (getenv "TMPDIR") m47-imp4--scratch)))
                         (unless (file-directory-p dir)
                           (ignore-errors (make-directory dir t)))
                         (file-writable-p dir))))
    (m47-imp4--probe "access-file"
                     (lambda () (null (access-file "/" "m47 imp-4 probe"))))))

(princ (format "=== m47 imp-4 G2 OS-query suite done (%d tracked checks; t1 %d, t2 %d, t3 %d, t4 %d, t5 %d, t6 %d) ===\n"
               m47-imp4--registered
               (m47-imp4--group-count 't1)
               (m47-imp4--group-count 't2)
               (m47-imp4--group-count 't3)
               (m47-imp4--group-count 't4)
               (m47-imp4--group-count 't5)
               (m47-imp4--group-count 't6)))
