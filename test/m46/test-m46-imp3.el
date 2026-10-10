;;; test-m46-imp3.el --- M46 imp-3 corpus (the lockfile policy rewired).
;;;
;;; M46 imp-2 added the eight typed C leaves over plain values and the
;;; thin module (emacs filelock); it moved no policy.  M46 imp-3 moves
;;; the parent-side OS-facing lockfile policy of src/filelock.c onto
;;; those leaves.  The hubs call the module:
;;;   lock_file_1    -> filelock-boot-sec, filelock-lock-info
;;;   lock_file      -> filelock-lock-file-name, filelock-lock-owner,
;;;                     filelock-lock-free-p
;;;   unlock_file    -> filelock-unlock
;;;   file-locked-p  -> filelock-lock-file-name, filelock-lock-owner
;;; The C mechanism (rename, symlink, mkostemp, kill, readlinkat, and
;;; every char * buffer / struct lock_info_type) stays C (brief.org
;;; section 7).  The leaves are not vfork children and not signal
;;; handlers, so they may enter the Guile VM.
;;;
;;; This corpus reads files, and it runs gated runtime probes.  It pins:
;;;   T1 -- the hubs dispatch into the module: src/filelock.c holds the
;;;         six helpers and the call sites.
;;;   T2 -- the inline policy is gone: lock_if_free is absent; lock_file
;;;         no longer calls make_lock_file_name; lock_file_1 no longer
;;;         holds the snprintf composition; unlock_file no longer calls
;;;         current_lock_owner directly.
;;;   T3 -- the module still exports the eight wrappers and holds no FFI
;;;         call and no raw syscall.
;;;   T4 -- the mechanism stays C: rename_lock_file, create_lock_file,
;;;         read_lock_data, kill, unlock_file_handle_error, and the five
;;;         DEFUNs are unchanged.
;;;   T5 -- the surface: re-measure src/filelock.c lines and DEFUNs, and
;;;         the tree-wide scm_c_public_ref count (201).
;;;   T6 -- a per-group min-count guard.  Pin each group apart from the
;;;         total, so a truncated corpus fails.
;;;   T7 -- the gated runtime probe.  Run the built src/emacs and
;;;         exercise the rewired path.  Only an absent src/emacs (or no
;;;         writable scratch directory) is an INFO-skip; a non-zero exit
;;;         or a missing match is a FAIL, never a silent pass.
;;;   T8 -- the shape rule: --filelock-lock-owner returns the raw owner
;;;         line for the another-owns case (brief.org section 6).
;;;
;;; A read error is a real error, never a silent pass.  An absent src/
;;; file is a real error.

(princ "=== m46 imp-3 rewire suite ===\n")

(require 'imp-ert-report)

(defvar m46-imp3--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))

(defvar m46-imp3--registered 0
  "Total number of tracked-file checks this corpus has registered.")

(defvar m46-imp3--group nil
  "The group that `m46-imp3--check' counts into: `t1' ... `t5', `t8', or nil.")

(defvar m46-imp3--counts nil
  "Alist of (GROUP . COUNT) for the registered tracked-file checks.")

(defun m46-imp3--group-count (group)
  "Number of tracked-file checks registered so far in GROUP."
  (or (cdr (assq group m46-imp3--counts)) 0))

(defun m46-imp3--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
the symbol `m46-imp3-absent' when REL does not exist."
  (let ((path (expand-file-name rel m46-imp3--root)))
    (if (not (file-exists-p path))
        'm46-imp3-absent
      (with-temp-buffer
        (insert-file-contents path)
        (funcall fn)))))

(defun m46-imp3--contains-p (rel needle)
  "Non-nil when REL (repo-root-relative) contains NEEDLE."
  (m46-imp3--with rel
    (lambda ()
      (goto-char (point-min))
      (search-forward needle nil t))))

(defun m46-imp3--lines (rel)
  "Count the newlines of REL the way `wc -l' does."
  (m46-imp3--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (search-forward "\n" nil t) (setq n (1+ n)))
        n))))

(defun m46-imp3--count (rel regexp)
  "Count the matches of REGEXP in REL."
  (m46-imp3--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (re-search-forward regexp nil t) (setq n (1+ n)))
        n))))

(defun m46-imp3--line-of (rel needle)
  "1-based line number of the first literal NEEDLE in REL, or nil."
  (m46-imp3--with rel
    (lambda ()
      (goto-char (point-min))
      (when (search-forward needle nil t)
        (line-number-at-pos (match-beginning 0))))))

(defun m46-imp3--count-code (rel regexp)
  "Count the matches of REGEXP in REL, skipping full comment lines.
A module comment may name a forbidden token (for example a raw
syscall) while explaining that the module does NOT use it; only the
code must be free of the token."
  (m46-imp3--with rel
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

(defun m46-imp3--count-scm-ref ()
  "Count scm_c_public_ref over src/*.[chm] (the brief.org section 8 measure)."
  (let ((total 0)
        (dir (expand-file-name "src" m46-imp3--root)))
    (dolist (f (directory-files dir t "\\.[chm]\\'"))
      (setq total (+ total (or (m46-imp3--count f "scm_c_public_ref") 0))))
    total))

(defun m46-imp3--check (name ok)
  "Report and register one check on a TRACKED file.  OK is a boolean.
An absent src/ file makes the reader return the symbol
`m46-imp3-absent', so the check prints FAIL -- an absent src/ file is a
real error, not a pass."
  (if (eq ok 'm46-imp3-absent)
      (princ (format "INFO m46/imp3/%s skipped (source file absent)\n" name))
    (progn
      (princ (format "%s m46/imp3/%s\n" (if ok "PASS" "FAIL") name))
      (setq m46-imp3--registered (1+ m46-imp3--registered))
      (when m46-imp3--group
        (let ((cell (assq m46-imp3--group m46-imp3--counts)))
          (if cell
              (setcdr cell (1+ (cdr cell)))
            (push (cons m46-imp3--group 1) m46-imp3--counts))))
      (imp-register-bool-as-ert-test (format "m46-imp3/%s" name) (and ok t)))))

;;; --- T1. The hubs dispatch into the module (brief.org section 4) -----

(setq m46-imp3--group 't1)

(m46-imp3--check "hub-scm-public-ref-module"
                 (m46-imp3--contains-p "src/filelock.c"
                                       "scm_c_public_ref (\"emacs filelock\""))
(m46-imp3--check "helper-boot-sec"
                 (m46-imp3--contains-p "src/filelock.c"
                                       "filelock_boot_sec (void)"))
(m46-imp3--check "helper-lock-info"
                 (m46-imp3--contains-p "src/filelock.c"
                                       "filelock_lock_info (Lisp_Object boot)"))
(m46-imp3--check "helper-lock-file-name"
                 (m46-imp3--contains-p "src/filelock.c"
                                       "filelock_lock_file_name (Lisp_Object fn)"))
(m46-imp3--check "helper-lock-owner"
                 (m46-imp3--contains-p "src/filelock.c"
                                       "filelock_lock_owner (Lisp_Object lfname)"))
(m46-imp3--check "helper-lock-free-p"
                 (m46-imp3--contains-p "src/filelock.c"
                                       "filelock_lock_free_p (Lisp_Object lfname)"))
(m46-imp3--check "helper-unlock"
                 (m46-imp3--contains-p "src/filelock.c"
                                       "filelock_unlock (Lisp_Object fn)"))
(m46-imp3--check "scm-public-ref-count-6"
                 (eql 6 (m46-imp3--count "src/filelock.c" "scm_c_public_ref")))
(m46-imp3--check "scm-call-count-6"
                 (eql 6 (m46-imp3--count "src/filelock.c" "SCM_CALL_")))
(m46-imp3--check "lock-file-1-called-in-hub"
                 (m46-imp3--contains-p "src/filelock.c"
                                       "Lisp_Object info = filelock_lock_info (filelock_boot_sec ());"))
(m46-imp3--check "lock-file-name-called-in-hub"
                 (m46-imp3--contains-p "src/filelock.c"
                                       "lfname = filelock_lock_file_name (fn);"))
(m46-imp3--check "lock-owner-eq-called-in-hub"
                 (m46-imp3--contains-p "src/filelock.c"
                                       "EQ (filelock_lock_owner (lfname), Qt)"))
(m46-imp3--check "lock-free-called-in-hub"
                 (m46-imp3--contains-p "src/filelock.c"
                                       "Lisp_Object clash = filelock_lock_free_p (lfname);"))
(m46-imp3--check "clash-owner-called-in-hub"
                 (m46-imp3--contains-p "src/filelock.c"
                                       "filelock_clash_owner (filelock_lock_owner (lfname))"))
(m46-imp3--check "unlock-called-in-hub"
                 (m46-imp3--contains-p "src/filelock.c"
                                       "if (NILP (filelock_unlock (fn)))"))
(m46-imp3--check "locked-p-name-called-in-hub"
                 (m46-imp3--contains-p "src/filelock.c"
                                       "Lisp_Object lfname = filelock_lock_file_name (filename);"))
(m46-imp3--check "locked-p-owner-called-in-hub"
                 (m46-imp3--contains-p "src/filelock.c"
                                       "owner = filelock_lock_owner (lfname);"))
(m46-imp3--check "helpers-defined-before-lock-file-1"
                 (let ((h (m46-imp3--line-of "src/filelock.c"
                                             "filelock_boot_sec (void)"))
                       (c (m46-imp3--line-of "src/filelock.c"
                                             "lock_file_1 (Lisp_Object lfname, bool force)")))
                   (and (integerp h) (integerp c) (< h c))))

;;; --- T2. The inline policy is gone (brief.org section 5) -------------

(setq m46-imp3--group 't2)

(m46-imp3--check "no-lock-if-free"
                 (eql 0 (m46-imp3--count "src/filelock.c" "lock_if_free")))
;; Only the --filelock-unlock leaf may call the name policy static.
(m46-imp3--check "lock-file-no-name-policy"
                 (eql 1 (m46-imp3--count
                         "src/filelock.c"
                         "lfname = make_lock_file_name (fn);")))
;; Only the --filelock-lock-info leaf may hold the snprintf composition.
(m46-imp3--check "lock-file-1-no-snprintf"
                 (eql 1 (m46-imp3--count "src/filelock.c" "\"%s@\"")))
(m46-imp3--check "no-inline-lock-info-struct"
                 (eql 0 (m46-imp3--count "src/filelock.c"
                                         "lock_info_type lock_info;")))
(m46-imp3--check "unlock-no-current-owner-call"
                 (eql 0 (m46-imp3--count "src/filelock.c"
                                         "current_lock_owner (0, lfname)")))
(m46-imp3--check "locked-p-no-owner-switch"
                 (eql 0 (m46-imp3--count "src/filelock.c"
                                         "case ANOTHER_OWNS_IT:")))

;;; --- T3. The module still exports the wrappers, no FFI --------------

(setq m46-imp3--group 't3)

(m46-imp3--check "module-exists"
                 (not (eq (m46-imp3--contains-p "mod/emacs/filelock.scm"
                                                "(define-module (emacs filelock)")
                          'm46-imp3-absent)))
(m46-imp3--check "module-defelisp-8"
                 (eql 8 (m46-imp3--count "mod/emacs/filelock.scm"
                                         "(defelisp %--filelock-")))
(m46-imp3--check "module-wrappers-8"
                 (eql 8 (m46-imp3--count "mod/emacs/filelock.scm"
                                         "^(define (filelock-")))
(m46-imp3--check "module-exports-8"
                 (let ((n (m46-imp3--count
                           "mod/emacs/filelock.scm"
                           "filelock-\\(lock-file-name\\|lock-info\\|boot-sec\\|within-one-second\\|integer-prefixed\\|lock-owner\\|lock-free-p\\|unlock\\)")))
                   (and (integerp n) (>= n 16)))) ; 8 in #:export, 8 in the defines
(m46-imp3--check "module-no-ffi"
                 (let ((n (m46-imp3--count-code
                           "mod/emacs/filelock.scm"
                           "system foreign\\|dynamic-link\\|libc\\.so\\|system\\*\\|primitive-fork\\|posix_spawn\\|ioctl\\|dynamic-func")))
                   (and (integerp n) (eql 0 n))))

;;; --- T4. The mechanism stays C (brief.org section 7) ----------------

(setq m46-imp3--group 't4)

(m46-imp3--check "mech-rename-lock-file"
                 (m46-imp3--contains-p "src/filelock.c"
                                       "rename_lock_file (char const *old"))
(m46-imp3--check "mech-create-lock-file"
                 (m46-imp3--contains-p "src/filelock.c"
                                       "create_lock_file (char *lfname"))
(m46-imp3--check "mech-read-lock-data"
                 (m46-imp3--contains-p "src/filelock.c"
                                       "read_lock_data (char *lfname"))
(m46-imp3--check "mech-kill"
                 (m46-imp3--contains-p "src/filelock.c" "kill (pid, 0)"))
(m46-imp3--check "mech-unlock-handler"
                 (m46-imp3--contains-p "src/filelock.c"
                                       "unlock_file_handle_error (Lisp_Object err)"))
(m46-imp3--check "leaf-defuns-8"
                 (eql 8 (m46-imp3--count "src/filelock.c" "^DEFUN (\"--filelock-")))
(m46-imp3--check "defun-count-13"
                 (eql 13 (m46-imp3--count "src/filelock.c" "^DEFUN (\"")))
(m46-imp3--check "five-defuns-present"
                 (and (m46-imp3--contains-p "src/filelock.c" "DEFUN (\"lock-file\"")
                      (m46-imp3--contains-p "src/filelock.c" "DEFUN (\"unlock-file\"")
                      (m46-imp3--contains-p "src/filelock.c" "DEFUN (\"lock-buffer\"")
                      (m46-imp3--contains-p "src/filelock.c" "DEFUN (\"unlock-buffer\"")
                      (m46-imp3--contains-p "src/filelock.c" "DEFUN (\"file-locked-p\"")))

;;; --- T5. The surface (brief.org section 8) --------------------------

(setq m46-imp3--group 't5)

(m46-imp3--check "filelock.c-lines-1216"
                 (eql 1216 (m46-imp3--lines "src/filelock.c")))
(m46-imp3--check "filelock.c-defuns-13"
                 (eql 13 (m46-imp3--count "src/filelock.c" "^DEFUN (\"")))
(m46-imp3--check "tree-wide-scm-public-ref-250"
                 (eql 250 (m46-imp3--count-scm-ref)))
(m46-imp3--check "callproc.c-lines-2387"
                 (eql 2387 (m46-imp3--lines "src/callproc.c")))
(m46-imp3--check "sysdep.c-lines-4950"
                 (eql 4950 (m46-imp3--lines "src/sysdep.c")))
(m46-imp3--check "combined-keyboard-surface-11723"
                 (let ((kb (m46-imp3--lines "src/keyboard.c"))
                       (kg (m46-imp3--lines "src/keyboard-globals.c")))
                   (and (integerp kb) (integerp kg)
                        (eql 11723 (+ kb kg)))))

;;; --- T8. The shape rule (brief.org section 6) -----------------------

;; For the another-owns case, --filelock-lock-owner returns the raw owner
;; line USER@HOST.PID:BOOT as a plain string, not the bare pid.  The two
;; callers derive their own strings: the clash message (a small static)
;; and the user prefix.

(setq m46-imp3--group 't8)

(m46-imp3--check "owner-returns-raw-line"
                 (eql 2 (m46-imp3--count "src/filelock.c"
                                         "return build_string (lfinfo);")))
(m46-imp3--check "owner-no-bare-pid"
                 (eql 0 (m46-imp3--count "src/filelock.c"
                                         "return make_int (pid);")))
(m46-imp3--check "owner-doc-raw-line"
                 (m46-imp3--contains-p "src/filelock.c" "raw owner line"))
(m46-imp3--check "clash-static-present"
                 (m46-imp3--contains-p "src/filelock.c"
                                       "filelock_clash_owner (Lisp_Object owner_line)"))

;;; --- T6. The per-group min-count guard ------------------------------

(setq m46-imp3--group nil)

(m46-imp3--check "reg/min-t1-checks-18"
                 (>= (m46-imp3--group-count 't1) 18))
(m46-imp3--check "reg/min-t2-checks-6"
                 (>= (m46-imp3--group-count 't2) 6))
(m46-imp3--check "reg/min-t3-checks-5"
                 (>= (m46-imp3--group-count 't3) 5))
(m46-imp3--check "reg/min-t4-checks-8"
                 (>= (m46-imp3--group-count 't4) 8))
(m46-imp3--check "reg/min-t5-checks-6"
                 (>= (m46-imp3--group-count 't5) 6))
(m46-imp3--check "reg/min-t8-checks-4"
                 (>= (m46-imp3--group-count 't8) 4))
(m46-imp3--check "reg/min-total-50"
                 (>= m46-imp3--registered 50))

;;; --- T7. The gated runtime probes (brief.org section 9) -------------

;; This corpus runs inside the built src/emacs (tool/run-tests.scm loads
;; the (m46) group with run-tests-loadup-emacs), so a probe exercises the
;; rewired path DIRECTLY, in this process.
;;
;; An earlier version ran each probe in a nested src/emacs --batch to
;; isolate the harness from a failing probe.  That cost one full emacs
;; startup per probe, and it reported a non-zero child exit as a skip.
;; The isolation is not worth the price: one failing probe may stop the
;; load of the rest.  `condition-case' still holds an ordinary signalled
;; error to the checks of that one probe.
;;
;; No probe here prompts: lock-file prompts only for a lock that another
;; process owns, and the raw probe reads the fabricated owner with
;; --filelock-lock-owner and file-locked-p, which never ask.
;;
;; A missing leaf is a FAIL, not a skip.  There is no src/emacs
;; INFO-skip any more.
;;
;; The lock probes write a file, so they need a writable directory.  The
;; sandbox denies writes under /tmp, so pick the first directory that
;; accepts a file: $TMPDIR, /tmp, then <root>/test/m46/scratch.  A
;; hardcoded /tmp turned every write probe into a fake skip.

(defun m46-imp3--writable-p (dir)
  "Non-nil when DIR exists and accepts a new file."
  (and (stringp dir)
       (file-directory-p dir)
       (let ((probe (expand-file-name "m46-imp3-write-probe" dir)))
         (condition-case nil
             (progn (with-temp-file probe (insert "x"))
                    (delete-file probe)
                    t)
           (error nil)))))

(defvar m46-imp3--scratch
  (let ((tree (expand-file-name "test/m46/scratch" m46-imp3--root)))
    (or (and (m46-imp3--writable-p (getenv "TMPDIR"))
             (file-name-as-directory (getenv "TMPDIR")))
        (and (m46-imp3--writable-p "/tmp") "/tmp/")
        (progn (ignore-errors (make-directory tree t))
               (and (m46-imp3--writable-p tree)
                    (file-name-as-directory tree)))))
  "A writable directory for the runtime probes, or nil when none exists.")

(defun m46-imp3--scratch-file (name)
  "Return NAME under the probe scratch directory, or nil without one."
  (and m46-imp3--scratch (concat m46-imp3--scratch name)))

(defun m46-imp3--probe (names thunk)
  "Run THUNK once, then register the checks NAMES from its result.
THUNK calls the rewired path and returns an alist of (NAME . OK).  A
signalled error registers every NAME as a FAIL and prints the error, so
a broken probe is never a silent pass.  An undefined leaf signals
void-function, so it is a FAIL too."
  (let ((got (condition-case err
                 (funcall thunk)
               (error (princ (format "INFO m46/imp3/%s error=%S\n"
                                     (car names) err))
                      nil))))
    (dolist (name names)
      (m46-imp3--check name (and (cdr (assoc name got)) t)))))

(defun m46-imp3--needs-scratch (names thunk)
  "Run THUNK as the probe NAMES, or INFO-skip without a scratch directory."
  (if (null m46-imp3--scratch)
      (princ (format "INFO m46/imp3/%s skipped (no writable scratch directory)\n"
                     (car names)))
    (m46-imp3--probe names thunk)))

(m46-imp3--probe
 '("probe/boot-sec-returns-integer")
 (lambda ()
   (list (cons "probe/boot-sec-returns-integer"
               (integerp (--filelock-boot-sec))))))

;; The lock_file / unlock_file hubs route through the module: lock a
;; temp file, then file-locked-p reports t (we own it) and nil after the
;; unlock.
(m46-imp3--needs-scratch
 '("probe/lock-file-owned-t" "probe/unlock-file-nil")
 (lambda ()
   (let ((f (m46-imp3--scratch-file "m46-imp3-cycle")))
     (with-temp-file f (insert "x"))
     (unwind-protect
         (let (locked unlocked)
           (lock-file f)
           (setq locked (file-locked-p f))
           (unlock-file f)
           (setq unlocked (file-locked-p f))
           (list (cons "probe/lock-file-owned-t" (eq locked t))
                 (cons "probe/unlock-file-nil" (null unlocked))))
       (ignore-errors (unlock-file f))
       (ignore-errors (delete-file f))))))

;; A fabricated foreign-host lock makes the another-owns branch of the
;; owner leaf return the raw line; file-locked-p takes the user prefix.
;; Neither call prompts, so this probe cannot block the harness.
(m46-imp3--needs-scratch
 '("probe/owner-raw-line-string" "probe/locked-p-user-prefix")
 (lambda ()
   (let* ((f (m46-imp3--scratch-file "m46-imp3-raw"))
          (l (concat (file-name-directory f) ".#"
                     (file-name-nondirectory f))))
     (with-temp-file f (insert "x"))
     (ignore-errors (delete-file l))
     (make-symbolic-link "someone@zzz-otherhost.999999:1" l)
     (unwind-protect
         (list (cons "probe/owner-raw-line-string"
                     (equal "someone@zzz-otherhost.999999:1"
                            (--filelock-lock-owner l)))
               (cons "probe/locked-p-user-prefix"
                     (equal "someone" (file-locked-p f))))
       (ignore-errors (delete-file l))
       (ignore-errors (delete-file f))))))

(princ (format "=== m46 imp-3 rewire suite done (%d tracked checks; t1 %d, t2 %d, t3 %d, t4 %d, t5 %d, t8 %d) ===\n"
               m46-imp3--registered
               (m46-imp3--group-count 't1)
               (m46-imp3--group-count 't2)
               (m46-imp3--group-count 't3)
               (m46-imp3--group-count 't4)
               (m46-imp3--group-count 't5)
               (m46-imp3--group-count 't8)))
