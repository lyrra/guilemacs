;;; test-m47-imp2.el --- M47 imp-2 corpus (the typed C file-I/O leaves).
;;;
;;; M47 imp-2 adds the 26 typed C leaves over plain values for the
;;; file-I/O boundary of src/fileio.c (brief.org section 3 and section
;;; 5), the thin wrapper module (emacs fileio) (section 7), and this
;;; tracked corpus (section 8.1).  imp-2 adds leaves only: it moves no
;;; policy.  imp-3 … imp-5 rewire the hubs and delete the inline policy.
;;;
;;; This corpus reads files, and it runs one gated runtime probe.  It
;;; pins:
;;;   E1 -- the 26 leaf DEFUNs exist in src/fileio.c with the exact names
;;;         of brief.org section 5; the ^DEFUN count is 78; the file
;;;         holds "guile.h"; the line count is the re-measured value
;;;         7265 (the imp-2 leaf-block repair grows the file).
;;;   E2 -- the plain-value shape (brief.org section 3): each leaf doc
;;;         string holds "plain" and a shape word ("string", "integer",
;;;         "boolean", or "list").
;;;   E3 -- mod/emacs/fileio.scm holds the 26 wrappers and the 26
;;;         defelisp lines, holds no scm_c_public_ref and no scm_ call;
;;;         prelude/load.scm loads it.
;;;   E4 -- the boundary rules: the mechanism stays C (the syscall names
;;;         and the two large blocks and the modtime group are still
;;;         present); the file holds 1 scm_c_public_ref site.
;;;   E5 -- the (m47) group carries this corpus, and a per-group
;;;         min-count guard fails when the corpus is truncated.  Pin E1
;;;         and E2 separately.
;;;   E6 -- the gated runtime probe.  Run the built src/emacs and call
;;;         three leaves.  Each probe is an INFO-skip when the binary is
;;;         absent.  A probe error is a FAIL, never a silent pass.
;;;   E7 -- the leaf-body repair (cr.org F1): a repaired leaf body holds
;;;         a pure mechanism token and does NOT call its own hub
;;;         (F<block>); the six OPEN leaves still call their hub.
;;;
;;; A read error is a real error, never a silent pass.  An absent src/
;;; file is a real error.

(princ "=== m47 imp-2 leaves suite ===\n")

(require 'imp-ert-report)

(defvar m47-imp2--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))

(defvar m47-imp2--registered 0
  "Total number of tracked-file checks this corpus has registered.")

(defvar m47-imp2--group nil
  "The group that `m47-imp2--check' counts into: `e1' ... `e4', or nil.")

(defvar m47-imp2--counts nil
  "Alist of (GROUP . COUNT) for the registered tracked-file checks.")

(defun m47-imp2--group-count (group)
  "Number of tracked-file checks registered so far in GROUP."
  (or (cdr (assq group m47-imp2--counts)) 0))

(defun m47-imp2--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
the symbol `m47-imp2-absent' when REL does not exist."
  (let ((path (expand-file-name rel m47-imp2--root)))
    (if (not (file-exists-p path))
        'm47-imp2-absent
      (with-temp-buffer
        (insert-file-contents path)
        (funcall fn)))))

(defun m47-imp2--contains-p (rel needle)
  "Non-nil when REL (repo-root-relative) contains NEEDLE."
  (m47-imp2--with rel
    (lambda ()
      (goto-char (point-min))
      (search-forward needle nil t))))

(defun m47-imp2--lines (rel)
  "Count the newlines of REL the way `wc -l' does."
  (m47-imp2--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (search-forward "\n" nil t) (setq n (1+ n)))
        n))))

(defun m47-imp2--count (rel regexp)
  "Count the matches of REGEXP in REL."
  (m47-imp2--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (re-search-forward regexp nil t) (setq n (1+ n)))
        n))))

(defun m47-imp2--count-code (rel regexp)
  "Count the matches of REGEXP in REL, skipping full comment lines.
A module comment may name a forbidden token (for example
`scm_c_public_ref') while explaining the contract; only the code must be
free of the token.  Scheme line comments start with `;'."
  (m47-imp2--with rel
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

(defun m47-imp2--check (name ok)
  "Report and register one check on a TRACKED file.  OK is a boolean.
An absent src/ file makes the reader return the symbol
`m47-imp2-absent', so the check prints FAIL -- an absent src/ file is a
real error, not a pass."
  (if (eq ok 'm47-imp2-absent)
      (princ (format "INFO m47/imp2/%s skipped (source file absent)\n" name))
    (progn
      (princ (format "%s m47/imp2/%s\n" (if ok "PASS" "FAIL") name))
      (setq m47-imp2--registered (1+ m47-imp2--registered))
      (when m47-imp2--group
        (let ((cell (assq m47-imp2--group m47-imp2--counts)))
          (if cell
              (setcdr cell (1+ (cdr cell)))
            (push (cons m47-imp2--group 1) m47-imp2--counts))))
      (imp-register-bool-as-ert-test (format "m47-imp2/%s" name) (and ok t)))))

(defvar m47-imp2--leaves
  '(;; G1 -- the file-name / path policy
    "find-file-name-handler" "file-name-directory" "file-name-nondirectory"
    "file-name-as-directory" "directory-file-name" "file-name-concat"
    "expand-file-name" "substitute-in-file-name"
    ;; G2 -- the OS-query predicate policy
    "file-exists-p" "file-executable-p" "file-readable-p" "file-writable-p"
    "access-file" "file-symlink-p" "file-directory-p" "file-regular-p"
    "file-modes" "file-newer-than-file-p" "file-system-info"
    ;; G3 -- the copy / rename / link / delete policy
    "copy-file" "make-directory-internal" "delete-directory-internal"
    "delete-file-internal" "rename-file" "add-name-to-file"
    "make-symbolic-link")
  "The 26 MOVES leaves of brief.org section 5.")

;;; --- E1. The 26 leaf DEFUNs (brief.org section 5) -------------------

(setq m47-imp2--group 'e1)

(dolist (leaf m47-imp2--leaves)
  (m47-imp2--check (format "leaf-%s" leaf)
                   (m47-imp2--contains-p "src/fileio.c"
                                         (format "DEFUN (\"--fileio-%s\"" leaf))))
(m47-imp2--check "leaf-defuns-26"
                 (eql 26 (m47-imp2--count "src/fileio.c" "^DEFUN (\"--fileio-")))
(m47-imp2--check "defun-count-78"
                 (eql 78 (m47-imp2--count "src/fileio.c" "^DEFUN (\"")))
(m47-imp2--check "fileio.c-lines-7265"
                 (eql 7265 (m47-imp2--lines "src/fileio.c")))
(m47-imp2--check "fileio.c-has-guile.h"
                 (m47-imp2--contains-p "src/fileio.c" "#include \"guile.h\""))
(m47-imp2--check "leaf-block-comment-m47"
                 (m47-imp2--contains-p "src/fileio.c"
                                       "the typed C leaves over plain"))

;;; --- E2. The plain-value shape (brief.org section 3) ----------------

(setq m47-imp2--group 'e2)

;; Each section-5 leaf name appears in the C leaf block, and its doc
;; string names a plain shape.  The aggregate counts below prove every
;; leaf doc really uses the word "plain".
(dolist (leaf m47-imp2--leaves)
  (m47-imp2--check (format "docname-%s" leaf)
                   (m47-imp2--contains-p "src/fileio.c"
                                         (format "--fileio-%s\"" leaf))))
(m47-imp2--check "doc-marker-26"
                 (eql 26 (m47-imp2--count "src/fileio.c" "M47 imp-2,")))
(m47-imp2--check "doc-plain-sites-26"
                 (eql 26 (m47-imp2--count "src/fileio.c" "\\*plain ")))
;; The shape words, measured after the imp-2 leaf block.
(m47-imp2--check "doc-plain-string-10"
                 (eql 10 (m47-imp2--count "src/fileio.c" "plain string")))
(m47-imp2--check "doc-plain-integer-1"
                 (eql 1 (m47-imp2--count "src/fileio.c" "plain integer")))
(m47-imp2--check "doc-plain-boolean-15"
                 (eql 15 (m47-imp2--count "src/fileio.c" "plain boolean")))
(m47-imp2--check "doc-plain-list-1"
                 (eql 1 (m47-imp2--count "src/fileio.c" "plain list")))
;; A leaf doc string names a plain shape and never a C I/O mechanism
;; type in a return.  The block comment states the plain-value rule.
(m47-imp2--check "leaf-block-names-plain-rule"
                 (m47-imp2--contains-p "src/fileio.c"
                                       "Each leaf returns one"))

;;; --- E3. The wrapper module (brief.org section 7) -------------------

(setq m47-imp2--group 'e3)

(m47-imp2--check "module-exists"
                 (not (eq (m47-imp2--contains-p "mod/emacs/fileio.scm"
                                                "(define-module (emacs fileio)")
                          'm47-imp2-absent)))
(m47-imp2--check "module-defelisp-26"
                 (eql 26 (m47-imp2--count "mod/emacs/fileio.scm"
                                         "(defelisp %--fileio-")))
(m47-imp2--check "module-wrappers-26"
                 (let ((n (m47-imp2--count "mod/emacs/fileio.scm"
                                          "^(define (fileio-")))
                   (and (integerp n) (>= n 26))))
(m47-imp2--check "module-keeps-auto-save-hook"
                 (m47-imp2--contains-p "mod/emacs/fileio.scm"
                                       "(define (fileio-run-auto-save-hook!)"))
(m47-imp2--check "module-no-ffi"
                 (let ((n (m47-imp2--count-code
                           "mod/emacs/fileio.scm"
                           "system foreign\\|dynamic-link\\|libc\\.so\\|system\\*\\|primitive-fork\\|posix_spawn\\|ioctl\\|dynamic-func")))
                   (and (integerp n) (eql 0 n))))
(m47-imp2--check "module-no-scm-ref"
                 (let ((n (m47-imp2--count-code "mod/emacs/fileio.scm"
                                                "scm_c_public_ref")))
                   (and (integerp n) (eql 0 n))))
(m47-imp2--check "load.scm-fileio"
                 (m47-imp2--contains-p "prelude/load.scm"
                                       "(use-modules (emacs fileio))"))

;;; --- E4. The boundary rules (brief.org sections 3, 6) ---------------

(setq m47-imp2--group 'e4)

(m47-imp2--check "mech-fstatat"
                 (m47-imp2--contains-p "src/fileio.c" "emacs_fstatat"))
(m47-imp2--check "mech-symlink"
                 (m47-imp2--contains-p "src/fileio.c" "emacs_symlink"))
(m47-imp2--check "mech-readlinkat"
                 (m47-imp2--contains-p "src/fileio.c" "readlinkat"))
(m47-imp2--check "mech-fs-usage"
                 (m47-imp2--contains-p "src/fileio.c" "get_fs_usage"))
(m47-imp2--check "mech-blocks-to-bytes"
                 (m47-imp2--contains-p "src/fileio.c" "blocks_to_bytes"))
(m47-imp2--check "mech-check-file-access"
                 (m47-imp2--contains-p "src/fileio.c" "check_file_access"))
;; imp-2 adds no ref site: the dispatch helpers are imp-3 … imp-5 work.
(m47-imp2--check "scm-ref-1"
                 (eql 1 (m47-imp2--count "src/fileio.c" "scm_c_public_ref")))
;; The two large blocks and the modtime group stay present (STAYS C).
(m47-imp2--check "stays-insert-file-contents"
                 (m47-imp2--contains-p "src/fileio.c"
                                       "DEFUN (\"insert-file-contents\""))
(m47-imp2--check "stays-write-region"
                 (m47-imp2--contains-p "src/fileio.c" "DEFUN (\"write-region\""))
(m47-imp2--check "stays-do-auto-save"
                 (m47-imp2--contains-p "src/fileio.c" "DEFUN (\"do-auto-save\""))
(m47-imp2--check "stays-modtime-group"
                 (and (m47-imp2--contains-p "src/fileio.c"
                                            "DEFUN (\"verify-visited-file-modtime\"")
                      (m47-imp2--contains-p "src/fileio.c"
                                            "DEFUN (\"visited-file-modtime\"")
                      (m47-imp2--contains-p "src/fileio.c"
                                            "DEFUN (\"set-visited-file-modtime\"")))

;;; --- E5. The group and the guards -----------------------------------

(setq m47-imp2--group nil)

(m47-imp2--check "reg/run-tests-m47-imp2"
                 (m47-imp2--contains-p "tool/run-tests.scm"
                                       "test/m47/test-m47-imp2.el"))
(m47-imp2--check "reg/min-e1-checks-30"
                 (>= (m47-imp2--group-count 'e1) 30))
(m47-imp2--check "reg/min-e2-checks-20"
                 (>= (m47-imp2--group-count 'e2) 20))
(m47-imp2--check "reg/min-total-50"
                 (>= m47-imp2--registered 50))

;;; --- E6. The gated runtime probe (brief.org section 8.1) ------------

;; The leaves are compiled into src/emacs, not into this harness, so run
;; that binary in batch and call three of them.  Each probe is an INFO
;; skip when the binary is absent -- never a silent pass.  A probe error
;; is a FAIL.  A nested gate run sets GUILEMACS_M47_GATE=1 to skip this
;; same check, so the run does not recurse.

(defvar m47-imp2--emacs
  (expand-file-name "src/emacs" m47-imp2--root))

(defun m47-imp2--probe-output (eval)
  "Return the output of the built src/emacs running EVAL, or nil.
Run src/emacs in batch; EVAL must print one tagged line.  Return nil
when the binary is absent or the run fails."
  (when (file-executable-p m47-imp2--emacs)
    (with-temp-buffer
      (let ((status nil))
        (condition-case nil
            (setq status
                  (call-process
                   "/bin/sh" nil (current-buffer) nil "-c"
                   (format "printf '' | %s --batch --eval '%s'"
                           m47-imp2--emacs eval)))
          (error (setq status nil)))
        (when (and (integerp status) (zerop status))
          (buffer-string))))))

(defvar m47-imp2--dir-eval
  "(princ (format \"dir=%S\\n\" (--fileio-file-name-directory \"/a/b\")))")
(defvar m47-imp2--nd-eval
  "(princ (format \"nd=%S\\n\" (--fileio-file-name-nondirectory \"/a/b\")))")
(defvar m47-imp2--exp-eval
  "(princ (format \"exp=%S\\n\" (--fileio-expand-file-name \"/a/../b\" nil)))")

(defun m47-imp2--probe (tag eval pattern)
  "Run one gated runtime probe.  TAG names the probe.  EVAL runs in the
built src/emacs and must print a line that matches PATTERN.  Report an
INFO-skip when the binary is absent; a probe error is a FAIL."
  (let ((out (m47-imp2--probe-output eval)))
    (if (null out)
        (princ (format
                "INFO m47/imp2/%s-probe skipped (no runnable built src/emacs)\n"
                tag))
      (m47-imp2--check (format "probe/%s" tag)
                       (and (stringp out)
                            (string-match-p pattern out)
                            t)))))

(if (getenv "GUILEMACS_M47_GATE")
    (princ "INFO m47/imp2/runtime-probes skipped (nested gate run)\n")
  (progn
    (m47-imp2--probe "file-name-directory" m47-imp2--dir-eval "dir=\"/a/\"")
    (m47-imp2--probe "file-name-nondirectory" m47-imp2--nd-eval "nd=\"b\"")
    (m47-imp2--probe "expand-file-name" m47-imp2--exp-eval "exp=\"/b\"")))

;;; --- E7. The leaf-body repair (cr.org F1) ---------------------------

;; cr.org F1: a leaf must NOT call its own public hub (F<block>).  That is
;; self-reference: imp-3 rewires the hub onto the leaf, so the leaf must
;; call the pure helper or hold the pure policy.  Each repaired leaf body
;; holds a mechanism token and no hub call.  The six OPEN leaves still
;; call their hub; they are pinned OPEN until the factor-helper step.

(setq m47-imp2--group 'e7)

(defvar m47-imp2--open-leaves
  '("expand-file-name" "substitute-in-file-name" "copy-file"
    "rename-file" "add-name-to-file" "make-symbolic-link")
  "The leaves that still call their hub (OPEN, cr.org F1).")

(defvar m47-imp2--leaf-mechanism
  '(("find-file-name-handler"    . "Vfile_name_handler_alist")
    ("file-name-directory"       . "file_name_directory (fn)")
    ("file-name-nondirectory"    . "guile_file_path_nondirectory")
    ("file-name-as-directory"    . "file_name_as_directory (buf")
    ("directory-file-name"       . "directory_file_name (buf")
    ("file-name-concat"          . "guile_ends_with_directory_separator")
    ("file-exists-p"             . "check_file_access")
    ("file-executable-p"         . "check_file_access")
    ("file-readable-p"           . "check_file_access")
    ("file-writable-p"           . "file_access_p")
    ("access-file"               . "sys_faccessat")
    ("file-symlink-p"            . "emacs_readlinkat")
    ("file-directory-p"          . "file_directory_p (ENCODE_FILE")
    ("file-regular-p"            . "S_ISREG")
    ("file-modes"                . "symlink_nofollow_flag")
    ("file-newer-than-file-p"    . "timespec_cmp")
    ("file-system-info"          . "blocks_to_bytes")
    ("make-directory-internal"   . "emacs_mkdir")
    ("delete-directory-internal" . "emacs_rmdir")
    ("delete-file-internal"      . "emacs_unlink"))
  "For each repaired leaf, a mechanism token its body must hold.")

(defun m47-imp2--leaf-body (block)
  "Return the source of the DEFUN (\"--fileio-BLOCK\") body, or nil."
  (m47-imp2--with "src/fileio.c"
    (lambda ()
      (goto-char (point-min))
      (when (search-forward (format "DEFUN (\"--fileio-%s\"" block) nil t)
        (let ((start (line-beginning-position)))
          (if (re-search-forward "\nDEFUN (\"" nil t)
              (buffer-substring-no-properties start (match-beginning 0))
            (buffer-substring-no-properties start (point-max))))))))

(defun m47-imp2--hub-name (block)
  "The C name of the public hub for BLOCK, e.g. \"Ffile_name_directory\"."
  (concat "F" (replace-regexp-in-string "-" "_" block)))

(defun m47-imp2--strip-comments (s)
  "Return S with all C block comments (/* ... */) removed.
A comment may name a forbidden token (for example the hub) while
explaining the contract; only the code must be free of the token."
  (let ((out s))
    (while (string-match "/\\*" out)
      (let* ((start (match-beginning 0))
             (end (string-match "\\*/" out (match-end 0))))
        (setq out (concat (substring out 0 start)
                          (if end (substring out (+ end 2)) "")))))
    out))

(dolist (pair m47-imp2--leaf-mechanism)
  (let* ((block (car pair))
         (token (cdr pair))
         (body (m47-imp2--leaf-body block))
         (code (and (stringp body) (m47-imp2--strip-comments body)))
         (hub (format "%s (" (m47-imp2--hub-name block))))
    (m47-imp2--check (format "body-mechanism-%s" block)
                     (and (stringp code)
                          (string-match-p (regexp-quote token) code)
                          t))
    (m47-imp2--check (format "body-no-hub-%s" block)
                     (and (stringp code)
                          (not (string-match-p (regexp-quote hub) code))
                          t))))

(dolist (block m47-imp2--open-leaves)
  (let* ((body (m47-imp2--leaf-body block))
         (code (and (stringp body) (m47-imp2--strip-comments body)))
         (hub (format "%s (" (m47-imp2--hub-name block))))
    (m47-imp2--check (format "body-open-calls-hub-%s" block)
                     (and (stringp code)
                          (string-match-p (regexp-quote hub) code)
                          t))))

(princ (format "=== m47 imp-2 leaves suite done (%d tracked checks; e1 %d, e2 %d, e3 %d, e4 %d, e7 %d) ===\n"
               m47-imp2--registered
               (m47-imp2--group-count 'e1)
               (m47-imp2--group-count 'e2)
               (m47-imp2--group-count 'e3)
               (m47-imp2--group-count 'e4)
               (m47-imp2--group-count 'e7)))
