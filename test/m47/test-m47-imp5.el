;;; test-m47-imp5.el --- M47 imp-5 corpus (the G3 copy / rename / link /
;;; delete policy port).
;;;
;;; M47 imp-5 moves the G3 target-name resolution and the overwrite /
;;; preserve decision of src/fileio.c to Scheme.  The shape is Reading B
;;; (brief.org section 3 / section 5): the C DEFUN hub keeps the file
;;; name handler dispatch and the error report; the module (emacs fileio)
;;; owns the *decision*; the typed C leaf calls one pure static C
;;; mechanism that holds the OS work only.  The 7 G3 blocks are
;;; copy-file, make-directory-internal, delete-directory-internal,
;;; delete-file-internal, rename-file, add-name-to-file, and
;;; make-symbolic-link.
;;;
;;; This corpus reads files, and it runs gated runtime probes.  It pins:
;;;   T1 -- the 7 G3 dispatch helpers exist with their signatures, look
;;;         up the 7 module procedures, and the 7 hubs call them.
;;;   T2 -- each G3 leaf calls its mechanism, never a public hub (cr.org
;;;         F1).
;;;   T3 -- each G3 leaf holds no handler dispatch and no
;;;         Fexpand_file_name call (brief.org section 3).
;;;   T4 -- (emacs fileio) holds the real G3 decision, not a one-line
;;;         pass-through (brief.org section 6).
;;;   T5 -- no G3 OPEN marker remains (brief.org section 5.5).
;;;   T6 -- the re-measured surface (brief.org section 8), with a
;;;         per-group min-count guard and a total guard.
;;;   T7 -- the group registration guards: the run-tests.scm entry and
;;;         the per-group / total min-count guards.
;;;   T8 -- the gated runtime probe.  Run the built src/emacs and
;;;         exercise the 7 rewired hubs.
;;;
;;; A read error is a real error, never a silent pass.  An absent src/
;;; file is a real error.  A probe failure is a FAIL, never a skip.

(princ "=== m47 imp-5 G3 copy/rename/link/delete suite ===\n")

(require 'imp-ert-report)

(defvar m47-imp5--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))

(defvar m47-imp5--registered 0
  "Total number of tracked-file checks this corpus has registered.")

(defvar m47-imp5--group nil
  "The group that `m47-imp5--check' counts into: `t1' ... `t6', or nil.")

(defvar m47-imp5--counts nil
  "Alist of (GROUP . COUNT) for the registered tracked-file checks.")

(defun m47-imp5--group-count (group)
  "Number of tracked-file checks registered so far in GROUP."
  (or (cdr (assq group m47-imp5--counts)) 0))

(defun m47-imp5--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
the symbol `m47-imp5-absent' when REL does not exist."
  (let ((path (expand-file-name rel m47-imp5--root)))
    (if (not (file-exists-p path))
        'm47-imp5-absent
      (with-temp-buffer
        (insert-file-contents path)
        (funcall fn)))))

(defun m47-imp5--contains-p (rel needle)
  "Non-nil when REL (repo-root-relative) contains NEEDLE."
  (m47-imp5--with rel
    (lambda ()
      (goto-char (point-min))
      (search-forward needle nil t))))

(defun m47-imp5--lines (rel)
  "Count the newlines of REL the way `wc -l' does."
  (m47-imp5--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (search-forward "\n" nil t) (setq n (1+ n)))
        n))))

(defun m47-imp5--count (rel regexp)
  "Count the matches of REGEXP in REL."
  (m47-imp5--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (re-search-forward regexp nil t) (setq n (1+ n)))
        n))))

(defun m47-imp5--count-code (rel regexp)
  "Count the matches of REGEXP in the non-comment lines of REL."
  (m47-imp5--with rel
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

(defun m47-imp5--line-of (rel needle)
  "1-based line number of the first literal NEEDLE in REL, or nil."
  (m47-imp5--with rel
    (lambda ()
      (goto-char (point-min))
      (when (search-forward needle nil t)
        (line-number-at-pos (match-beginning 0))))))

(defun m47-imp5--leaf-body (block)
  "Return the source of the DEFUN (\"--fileio-BLOCK\") body, or nil."
  (m47-imp5--with "src/fileio.c"
    (lambda ()
      (goto-char (point-min))
      (when (search-forward (format "DEFUN (\"--fileio-%s\"" block) nil t)
        (let ((start (line-beginning-position)))
          (if (re-search-forward "\nDEFUN (\"" nil t)
              (buffer-substring-no-properties start (match-beginning 0))
            (buffer-substring-no-properties start (point-max))))))))

(defun m47-imp5--hub-name (block)
  "The C name of the public hub for BLOCK, e.g. \"Fcopy_file\"."
  (concat "F" (replace-regexp-in-string "-" "_" block)))

(defun m47-imp5--strip-comments (s)
  "Return S with all C block comments (/* ... */) removed."
  (let ((out s))
    (while (string-match "/\\*" out)
      (let* ((start (match-beginning 0))
             (end (string-match "\\*/" out (match-end 0))))
        (setq out (concat (substring out 0 start)
                          (if end (substring out (+ end 2)) "")))))
    out))

(defun m47-imp5--check (name ok)
  "Report and register one check on a TRACKED file.  OK is a boolean.
An absent src/ file makes the reader return the symbol
`m47-imp5-absent', so the check prints FAIL -- an absent src/ file is a
real error, not a pass."
  (if (eq ok 'm47-imp5-absent)
      (princ (format "INFO m47/imp5/%s skipped (source file absent)\n" name))
    (progn
      (princ (format "%s m47/imp5/%s\n" (if ok "PASS" "FAIL") name))
      (setq m47-imp5--registered (1+ m47-imp5--registered))
      (when m47-imp5--group
        (let ((cell (assq m47-imp5--group m47-imp5--counts)))
          (if cell
              (setcdr cell (1+ (cdr cell)))
            (push (cons m47-imp5--group 1) m47-imp5--counts))))
      (imp-register-bool-as-ert-test (format "m47-imp5/%s" name) (and ok t)))))

;;; --- T1. The hubs dispatch into the module (brief.org section 5) ----

(setq m47-imp5--group 't1)

(defvar m47-imp5--dispatch
  '(("copy-file"                 . ("copy_file_scheme (Lisp_Object file, Lisp_Object newname,"
                                    "copy_file_scheme (file, newname, ok_if_already_exists, keep_time,"))
    ("make-directory-internal"   . ("make_directory_internal_scheme (Lisp_Object dir)"
                                    "make_directory_internal_scheme (directory)"))
    ("delete-directory-internal" . ("delete_directory_internal_scheme (Lisp_Object dir)"
                                    "delete_directory_internal_scheme (directory)"))
    ("delete-file-internal"      . ("delete_file_internal_scheme (Lisp_Object fn)"
                                    "delete_file_internal_scheme (filename)"))
    ("rename-file"               . ("rename_file_scheme (Lisp_Object file, Lisp_Object newname,"
                                    "rename_file_scheme (file, newname, ok_if_already_exists)"))
    ("add-name-to-file"          . ("add_name_to_file_scheme (Lisp_Object file, Lisp_Object newname,"
                                    "add_name_to_file_scheme (file, newname, ok_if_already_exists)"))
    ("make-symbolic-link"        . ("make_symbolic_link_scheme (Lisp_Object target, Lisp_Object linkname,"
                                    "make_symbolic_link_scheme (target, linkname,")))
  "Per G3 block: the dispatch-helper signature and the hub call site.")

(dolist (pair m47-imp5--dispatch)
  (let ((block (car pair)) (sig (nth 0 (cdr pair))) (call (nth 1 (cdr pair))))
    (m47-imp5--check (format "helper-%s" block)
                     (m47-imp5--contains-p "src/fileio.c" sig))
    (m47-imp5--check (format "ref-%s" block)
                     (m47-imp5--contains-p
                      "src/fileio.c"
                      (format "scm_c_public_ref (\"emacs fileio\", \"fileio-%s\")" block)))
    (m47-imp5--check (format "hub-call-%s" block)
                     (m47-imp5--contains-p "src/fileio.c" call))
    ;; The helper resolves the module procedure with one ref only.
    (m47-imp5--check (format "hub-name-%s" block)
                     (m47-imp5--contains-p "src/fileio.c"
                                           (format "DEFUN (\"%s\"" block)))))

;; The dispatch helpers sit before the first G3 hub (brief.org section 5).
(m47-imp5--check "helpers-defined-before-hub"
                 (let ((h (m47-imp5--line-of
                           "src/fileio.c"
                           "copy_file_scheme (Lisp_Object file, Lisp_Object newname,"))
                       (c (m47-imp5--line-of "src/fileio.c"
                                             "DEFUN (\"copy-file\"")))
                   (and (integerp h) (integerp c) (< h c))))

;;; --- T2. The mechanisms exist; the leaves call them ------------------

(setq m47-imp5--group 't2)

(defvar m47-imp5--mechanism
  '(("copy-file"                 "copy_file_1 (Lisp_Object file, Lisp_Object newname,"
                                 "copy_file_1 (file, newname, ok_if_exists, keep_time,"
                                 "Fcopy_file (")
    ("make-directory-internal"   "make_directory_internal_1 (Lisp_Object directory)"
                                 "make_directory_internal_1 (dir)"
                                 "Fmake_directory_internal (")
    ("delete-directory-internal" "delete_directory_internal_1 (Lisp_Object directory)"
                                 "delete_directory_internal_1 (dir)"
                                 "Fdelete_directory_internal (")
    ("delete-file-internal"      "delete_file_internal_1 (Lisp_Object filename)"
                                 "delete_file_internal_1 (fn)"
                                 "Fdelete_file_internal (")
    ("rename-file"               "rename_file_1 (Lisp_Object file, Lisp_Object newname, bool plain)"
                                 "rename_file_1 (file, newname, !NILP (plain))"
                                 "Frename_file (")
    ("add-name-to-file"          "add_name_to_file_1 (Lisp_Object file, Lisp_Object newname,"
                                 "add_name_to_file_1 (file, newname, ok_if_exists)"
                                 "Fadd_name_to_file (")
    ("make-symbolic-link"        "make_symbolic_link_1 (Lisp_Object target, Lisp_Object linkname,"
                                 "make_symbolic_link_1 (target, linkname, ok_if_exists)"
                                 "Fmake_symbolic_link ("))
  "Per G3 block: the pure mechanism signature, the leaf call token, and
the forbidden hub.")

(dolist (quad m47-imp5--mechanism)
  (let* ((block (nth 0 quad))
         (mech (nth 1 quad))
         (call (nth 2 quad))
         (hub (nth 3 quad))
         (body (m47-imp5--leaf-body block))
         (code (and (stringp body) (m47-imp5--strip-comments body))))
    (m47-imp5--check (format "mech-%s" block)
                     (m47-imp5--contains-p "src/fileio.c" mech))
    (m47-imp5--check (format "leaf-calls-mech-%s" block)
                     (and (stringp code)
                          (string-match-p (regexp-quote call) code)
                          t))
    (m47-imp5--check (format "leaf-no-hub-%s" block)
                     (and (stringp code)
                          (not (string-match-p (regexp-quote hub) code))
                          t))))

(m47-imp5--check "leaf-defuns-26"
                 (eql 26 (m47-imp5--count "src/fileio.c" "^DEFUN (\"--fileio-")))

;;; --- T3. A leaf holds no handler dispatch and no name expansion ------

(setq m47-imp5--group 't3)

(dolist (block '("copy-file" "make-directory-internal"
                 "delete-directory-internal" "delete-file-internal"
                 "rename-file" "add-name-to-file" "make-symbolic-link"))
  (let* ((body (m47-imp5--leaf-body block))
         (code (and (stringp body) (m47-imp5--strip-comments body))))
    (m47-imp5--check (format "leaf-no-handler-%s" block)
                     (and (stringp code)
                          (not (string-match-p
                                (regexp-quote "Ffind_file_name_handler (") code))
                          t))
    (m47-imp5--check (format "leaf-no-expand-%s" block)
                     (and (stringp code)
                          (not (string-match-p
                                (regexp-quote "Fexpand_file_name (") code))
                          (not (string-match-p
                                (regexp-quote "expand_and_dir_to_file (") code))
                          t))))

;;; --- T4. The module holds the real G3 decision (brief.org 6) --------

(setq m47-imp5--group 't4)

(dolist (name '("copy-file" "make-directory-internal"
                "delete-directory-internal" "delete-file-internal"
                "rename-file" "add-name-to-file" "make-symbolic-link"))
  (m47-imp5--check (format "module-decides-%s" name)
                   (m47-imp5--contains-p "mod/emacs/fileio.scm"
                                         (format "(define (fileio-%s" name))))

;; The expand_cp_target target-name resolution is the real G3 decision.
(m47-imp5--check "module-resolve-helper"
                 (m47-imp5--contains-p "mod/emacs/fileio.scm"
                                       "(define (fileio--resolve-target"))
(dolist (pair '(("resolve-uses-ends-with"      . "(force %ends-with-directory-separator?)")
                ("resolve-uses-nondirectory"   . "(fileio-file-name-nondirectory file)")
                ("resolve-uses-expand"         . "(fileio-expand-file-name")
                ("delete-dir-strip"            . "(fileio-directory-file-name dir)")
                ("rename-dir-strip"            . "(fileio-directory-file-name file)")
                ("symlink-tilde-rule"          . "(fileio--starts-with? target \"~\")")
                ("symlink-slash-colon-rule"    . "(fileio--starts-with? target \"/:\")")))
  (m47-imp5--check (format "module-policy-%s" (car pair))
                   (m47-imp5--contains-p "mod/emacs/fileio.scm" (cdr pair))))

;; A one-line pass-through holds no decision; the module now carries the
;; target resolution inside a `let' for each of the 4 resolving wrappers.
(m47-imp5--check "module-not-passthrough"
                 (let ((n (m47-imp5--count-code "mod/emacs/fileio.scm"
                                                "(fileio--resolve-target")))
                   (and (integerp n) (>= n 4))))
(m47-imp5--check "module-no-scm-ref"
                 (let ((n (m47-imp5--count-code "mod/emacs/fileio.scm"
                                                "scm_c_public_ref")))
                   (and (integerp n) (eql 0 n))))
(m47-imp5--check "module-grows-past-315"
                 (let ((n (m47-imp5--lines "mod/emacs/fileio.scm")))
                   (and (integerp n) (> n 315))))

;;; --- T5. No G3 OPEN marker remains (brief.org section 5.5) ----------

(setq m47-imp5--group 't5)

(m47-imp5--check "open-markers-left-0"
                 (eql 0 (m47-imp5--count "src/fileio.c" "OPEN (cr.org F1):")))
(m47-imp5--check "no-open-text"
                 (not (m47-imp5--contains-p "src/fileio.c" "OPEN (cr.org F1)")))

;;; --- T6. The re-measured surface (brief.org section 8) --------------

(setq m47-imp5--group 't6)

(m47-imp5--check "fileio.c-grows-past-imp4"
                 (let ((n (m47-imp5--lines "src/fileio.c")))
                   (and (integerp n) (> n 7373))))
(m47-imp5--check "fileio.c-defuns-78"
                 (eql 78 (m47-imp5--count "src/fileio.c" "^DEFUN (\"")))
(m47-imp5--check "fileio.c-scm-ref-27"
                 (eql 27 (m47-imp5--count "src/fileio.c" "scm_c_public_ref")))
(m47-imp5--check "fileio.scm-grows-past-315"
                 (let ((n (m47-imp5--lines "mod/emacs/fileio.scm")))
                   (and (integerp n) (> n 315))))
(m47-imp5--check "keyboard.c-lines-11233"
                 (eql 11233 (m47-imp5--lines "src/keyboard.c")))
(m47-imp5--check "keyboard-globals.c-lines-490"
                 (eql 490 (m47-imp5--lines "src/keyboard-globals.c")))
(m47-imp5--check "combined-keyboard-surface-11723"
                 (let ((kb (m47-imp5--lines "src/keyboard.c"))
                       (kg (m47-imp5--lines "src/keyboard-globals.c")))
                   (and (integerp kb) (integerp kg) (eql 11723 (+ kb kg)))))
(m47-imp5--check "keyboard-margin-237-under-11960"
                 (let ((kb (m47-imp5--lines "src/keyboard.c"))
                       (kg (m47-imp5--lines "src/keyboard-globals.c")))
                   (and (integerp kb) (integerp kg)
                        (eql 237 (- 11960 (+ kb kg))))))

;; The one place for the tree-wide scm_c_public_ref pin (brief.org
;; section 9).  The pin is 212 + 7 G3 dispatch helpers = 219 at imp-5;
;; M48 imp-3 adds 4 G1, imp-4 adds 4 G3, so it is 227.
(m47-imp5--check "tree-wide-scm-public-ref-260"
                 (let ((total 0)
                       (dir (expand-file-name "src" m47-imp5--root)))
                   (dolist (f (directory-files dir t "\\.[chm]\\'"))
                     (setq total (+ total
                                    (or (m47-imp5--count f "scm_c_public_ref")
                                        0))))
                   (and (integerp total) (eql 265 total))))

;;; --- T7. The group and the guards -----------------------------------

(setq m47-imp5--group nil)

(m47-imp5--check "reg/run-tests-m47-imp5"
                 (m47-imp5--contains-p "tool/run-tests.scm"
                                       "test/m47/test-m47-imp5.el"))
(m47-imp5--check "reg/run-tests-m47-imp5-after-imp4"
                 (let ((imp4 (m47-imp5--line-of "tool/run-tests.scm"
                                                "test/m47/test-m47-imp4.el"))
                       (imp5 (m47-imp5--line-of "tool/run-tests.scm"
                                                "test/m47/test-m47-imp5.el")))
                   (and (integerp imp4) (integerp imp5) (< imp4 imp5))))
(m47-imp5--check "reg/min-t1-checks-28"
                 (>= (m47-imp5--group-count 't1) 28))
(m47-imp5--check "reg/min-t2-checks-21"
                 (>= (m47-imp5--group-count 't2) 21))
(m47-imp5--check "reg/min-t3-checks-14"
                 (>= (m47-imp5--group-count 't3) 14))
(m47-imp5--check "reg/min-t4-checks-15"
                 (>= (m47-imp5--group-count 't4) 15))
(m47-imp5--check "reg/min-t5-checks-2"
                 (>= (m47-imp5--group-count 't5) 2))
(m47-imp5--check "reg/min-t6-checks-8"
                 (>= (m47-imp5--group-count 't6) 8))
(m47-imp5--check "reg/min-total-90"
                 (>= (1+ m47-imp5--registered) 90))

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

(defun m47-imp5--probe (tag thunk)
  "Register the probe TAG from the value of THUNK, which calls a rewired hub.
A non-nil value is a PASS.  A signalled error is a FAIL, never a silent
pass; the error is printed so the cause is visible."
  (imp-register-bool-as-ert-test
   (format "m47-imp5/probe/%s" tag)
   (condition-case err
       (and (funcall thunk) t)
     (error (princ (format "INFO m47/imp5/%s error=%S\n" tag err))
            nil))))

(defvar m47-imp5--scratch
  (expand-file-name "test/m47/scratch" m47-imp5--root))

(defun m47-imp5--scratch-dir ()
  "A writable scratch directory for the probe."
  (let ((dir (or (getenv "TMPDIR") m47-imp5--scratch)))
    (unless (file-directory-p dir)
      (ignore-errors (make-directory dir t)))
    dir))

(if (getenv "GUILEMACS_M47_GATE")
    (princ "INFO m47/imp5/runtime-probes skipped (nested gate run)\n")
  (progn
    (m47-imp5--probe "make-directory-internal"
                     (lambda ()
                       (let* ((d (make-temp-file "m47i5-mk" t))
                              (sub (expand-file-name "sub" d)))
                         (make-directory-internal sub)
                         (file-directory-p sub))))
    (m47-imp5--probe "delete-directory-internal"
                     (lambda ()
                       (let* ((d (make-temp-file "m47i5-rd" t))
                              (sub (expand-file-name "sub" d)))
                         (make-directory sub)
                         (delete-directory sub)
                         (not (file-directory-p sub)))))
    (m47-imp5--probe "delete-file-internal"
                     (lambda ()
                       (let* ((d (make-temp-file "m47i5-df" t))
                              (f (expand-file-name "f" d)))
                         (write-region "x" nil f nil 'silent)
                         (delete-file f)
                         (not (file-exists-p f)))))
    (m47-imp5--probe "copy-file"
                     (lambda ()
                       (let* ((d (make-temp-file "m47i5-cp" t))
                              (a (expand-file-name "a" d))
                              (b (expand-file-name "b" d)))
                         (write-region "hello" nil a nil 'silent)
                         (copy-file a b)
                         (file-exists-p b))))
    (m47-imp5--probe "copy-file-to-directory"
                     (lambda ()
                       ;; The target-name resolution: NEWNAME is a
                       ;; directory name, so the target is DIR/BASENAME.
                       (let* ((d (make-temp-file "m47i5-cd" t))
                              (a (expand-file-name "a" d))
                              (sub (expand-file-name "sub" d)))
                         (write-region "hello" nil a nil 'silent)
                         (make-directory sub)
                         (copy-file a (file-name-as-directory sub))
                         (file-exists-p (expand-file-name "a" sub)))))
    (m47-imp5--probe "rename-file"
                     (lambda ()
                       (let* ((d (make-temp-file "m47i5-rn" t))
                              (a (expand-file-name "a" d))
                              (b (expand-file-name "b" d)))
                         (write-region "hello" nil a nil 'silent)
                         (rename-file a b)
                         (and (file-exists-p b) (not (file-exists-p a))))))
    (m47-imp5--probe "add-name-to-file"
                     (lambda ()
                       (let* ((d (make-temp-file "m47i5-hl" t))
                              (a (expand-file-name "a" d))
                              (b (expand-file-name "b" d)))
                         (write-region "hello" nil a nil 'silent)
                         (add-name-to-file a b)
                         (file-exists-p b))))
    (m47-imp5--probe "make-symbolic-link"
                     (lambda ()
                       (let* ((d (make-temp-file "m47i5-sl" t))
                              (a (expand-file-name "a" d))
                              (l (expand-file-name "l" d)))
                         (write-region "hello" nil a nil 'silent)
                         (make-symbolic-link a l)
                         (file-symlink-p l))))))

(princ (format "=== m47 imp-5 G3 suite done (%d tracked checks; t1 %d, t2 %d, t3 %d, t4 %d, t5 %d, t6 %d) ===\n"
               m47-imp5--registered
               (m47-imp5--group-count 't1)
               (m47-imp5--group-count 't2)
               (m47-imp5--group-count 't3)
               (m47-imp5--group-count 't4)
               (m47-imp5--group-count 't5)
               (m47-imp5--group-count 't6)))
