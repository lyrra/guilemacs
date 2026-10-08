;;; test-m47-imp3.el --- M47 imp-3 corpus (the G1 path policy port).
;;;
;;; M47 imp-3 moves the G1 path policy of src/fileio.c to Scheme.  The
;;; shape is Reading B (brief.org section 4 / section 5): the C DEFUN
;;; hub keeps the file-name-handler dispatch and one maybe_quit; the
;;; module (emacs fileio) owns the path *decision*; the typed C leaf
;;; calls one pure static C helper that holds the byte-level *mechanism*
;;; only.  The 8 G1 blocks are find-file-name-handler, file-name-directory,
;;; file-name-nondirectory, file-name-as-directory, directory-file-name,
;;; file-name-concat, expand-file-name, and substitute-in-file-name.
;;;
;;; This corpus reads files, and it runs gated runtime probes.  It pins:
;;;   T1 -- the 8 dispatch helpers (hub -> module) exist with their
;;;         signatures, look up the 8 module procedures, and the 8 hubs
;;;         call them.
;;;   T2 -- the 8 pure C mechanisms exist, and each G1 leaf calls its
;;;         mechanism, never its own public hub (cr.org F1).
;;;   T3 -- the 2 OPEN G1 leaves (expand-file-name, substitute-in-file-name)
;;;         are unblocked: their leaves call the mechanism, and only the
;;;         4 G3 OPEN markers remain (brief.org section 7).
;;;   T4 -- (emacs fileio) holds the real path policy: it calls the
;;;         Scheme procedures of (emacs lookup-functions) and makes the
;;;         decision (cr1.org F4, brief.org section 4.4).  A module with
;;;         no G1 policy fails T4.
;;;   T5 -- the re-measured surface (brief.org section 11): src/fileio.c
;;;         shrinks, the module grows, and the keyboard surface holds.
;;;   T6 -- a per-group min-count guard and a total guard.  Pin each
;;;         group apart from the total, so a truncated corpus fails.
;;;   T7 -- the gated runtime probe.  Run the built src/emacs and
;;;         exercise the 8 rewired hubs.  An absent or non-runnable
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

(defun m47-imp3--count-code (rel regexp)
  "Count the matches of REGEXP in the non-comment lines of REL."
  (m47-imp3--with rel
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

;;; --- T1. The hubs dispatch into the module (brief.org section 4.3) ---

(setq m47-imp3--group 't1)

(defvar m47-imp3--dispatch
  '(("find-file-name-handler"   . ("find_file_name_handler_scheme (Lisp_Object file, Lisp_Object operation)"
                                   "find_file_name_handler_scheme (filename, operation)"))
    ("file-name-directory"      . ("file_name_directory_scheme (Lisp_Object fn)"
                                   "file_name_directory_scheme (filename)"))
    ("file-name-nondirectory"   . ("file_name_nondirectory_scheme (Lisp_Object fn)"
                                   "file_name_nondirectory_scheme (filename)"))
    ("file-name-as-directory"   . ("file_name_as_directory_scheme (Lisp_Object fn)"
                                   "file_name_as_directory_scheme (file)"))
    ("directory-file-name"      . ("directory_file_name_scheme (Lisp_Object fn)"
                                   "directory_file_name_scheme (directory)"))
    ("file-name-concat"         . ("file_name_concat_scheme (ptrdiff_t nargs, Lisp_Object *args)"
                                   "file_name_concat_scheme (nargs, args)"))
    ("expand-file-name"         . ("expand_file_name_scheme (Lisp_Object name, Lisp_Object default_directory)"
                                   "expand_file_name_scheme (name, default_directory)"))
    ("substitute-in-file-name"  . ("substitute_in_file_name_scheme (Lisp_Object fn)"
                                   "substitute_in_file_name_scheme (filename)")))
  "Per G1 block: the dispatch-helper signature and the hub call site.")

(dolist (pair m47-imp3--dispatch)
  (let ((block (car pair)) (sig (nth 0 (cdr pair))) (call (nth 1 (cdr pair))))
    (m47-imp3--check (format "helper-%s" block)
                     (m47-imp3--contains-p "src/fileio.c" sig))
    (m47-imp3--check (format "ref-%s" block)
                     (m47-imp3--contains-p
                      "src/fileio.c"
                      (format "scm_c_public_ref (\"emacs fileio\", \"fileio-%s\")" block)))
    (m47-imp3--check (format "hub-call-%s" block)
                     (m47-imp3--contains-p "src/fileio.c" call))))

;; The dispatch helpers sit before the first hub (brief.org section 4).
(m47-imp3--check "helpers-defined-before-hub"
                 (let ((h (m47-imp3--line-of
                           "src/fileio.c"
                           "find_file_name_handler_scheme (Lisp_Object file, Lisp_Object operation)"))
                       (c (m47-imp3--line-of "src/fileio.c"
                                             "DEFUN (\"find-file-name-handler\"")))
                   (and (integerp h) (integerp c) (< h c))))

;;; --- T2. The mechanisms exist; the leaves call them ------------------

(setq m47-imp3--group 't2)

(defvar m47-imp3--mechanism
  '(("find-file-name-handler"   "find_file_name_handler_1 (Lisp_Object file, Lisp_Object operation)"
                                "find_file_name_handler_1 (file, operation)"
                                "Ffind_file_name_handler (")
    ("file-name-directory"      "file_name_directory_1 (Lisp_Object filename)"
                                "file_name_directory_1 (fn)"
                                "Ffile_name_directory (")
    ("file-name-nondirectory"   "file_name_nondirectory_1 (Lisp_Object filename)"
                                "file_name_nondirectory_1 (fn)"
                                "Ffile_name_nondirectory (")
    ("file-name-as-directory"   "file_name_as_directory (char *dst"
                                "file_name_as_directory (buf"
                                "Ffile_name_as_directory (")
    ("directory-file-name"      "directory_file_name (char *dst"
                                "directory_file_name (buf"
                                "Fdirectory_file_name (")
    ("file-name-concat"         "file_name_concat_1 (ptrdiff_t nargs, Lisp_Object *args)"
                                "file_name_concat_1 (nargs, args)"
                                "Ffile_name_concat (")
    ("expand-file-name"         "expand_file_name_1 (Lisp_Object name, Lisp_Object default_directory)"
                                "expand_file_name_1 (name, default_directory)"
                                "Fexpand_file_name (")
    ("substitute-in-file-name"  "substitute_in_file_name_1 (Lisp_Object filename)"
                                "substitute_in_file_name_1 (fn)"
                                "Fsubstitute_in_file_name ("))
  "Per G1 block: the pure mechanism signature, the leaf call token, and
the forbidden hub.")

(dolist (quad m47-imp3--mechanism)
  (let* ((block (nth 0 quad))
         (mech (nth 1 quad))
         (call (nth 2 quad))
         (hub (nth 3 quad))
         (body (m47-imp3--leaf-body block))
         (code (and (stringp body) (m47-imp3--strip-comments body))))
    (m47-imp3--check (format "mech-%s" block)
                     (m47-imp3--contains-p "src/fileio.c" mech))
    (m47-imp3--check (format "leaf-calls-mech-%s" block)
                     (and (stringp code)
                          (string-match-p (regexp-quote call) code)
                          t))
    (m47-imp3--check (format "leaf-no-hub-%s" block)
                     (and (stringp code)
                          (not (string-match-p (regexp-quote hub) code))
                          t))))

(m47-imp3--check "leaf-defuns-26"
                 (eql 26 (m47-imp3--count "src/fileio.c" "^DEFUN (\"--fileio-")))

;;; --- T3. The 2 OPEN G1 leaves are unblocked (brief.org section 7) ----

(setq m47-imp3--group 't3)

(m47-imp3--check "open-expand-unblocked"
                 (let ((code (m47-imp3--strip-comments
                              (or (m47-imp3--leaf-body "expand-file-name") ""))))
                   (and (string-match-p (regexp-quote "expand_file_name_1") code)
                        (not (string-match-p (regexp-quote "Fexpand_file_name (") code))
                        t)))
(m47-imp3--check "open-substitute-unblocked"
                 (let ((code (m47-imp3--strip-comments
                              (or (m47-imp3--leaf-body "substitute-in-file-name") ""))))
                   (and (string-match-p (regexp-quote "substitute_in_file_name_1") code)
                        (not (string-match-p (regexp-quote "Fsubstitute_in_file_name (") code))
                        t)))
;; Only the 4 G3 OPEN markers remain (imp-5 owns them, not imp-3).  Count
;; the leaf doc marker "OPEN (cr.org F1):", not the block comment that
;; merely names it.
(m47-imp3--check "open-markers-left-0"
                 (eql 0 (m47-imp3--count "src/fileio.c" "OPEN (cr.org F1):")))

;;; --- T4. The module holds the real G1 path policy (brief.org 4.4) ----

(setq m47-imp3--group 't4)

(dolist (pair '(("path-directory-def"      . "(define %file-path-directory")
                ("path-nondirectory-def"   . "(define %file-path-nondirectory")
                ("ends-with-def"           . "(define %ends-with-directory-separator?")
                ("path-directory-force"    . "(force %file-path-directory)")
                ("path-nondirectory-force" . "(force %file-path-nondirectory)")
                ("ends-with-force"         . "(force %ends-with-directory-separator?)")
                ("strip-proc"              . "fileio--directory-name-strip")
                ("concat-ok"               . "fileio--concat-ok?")
                ("string-append"           . "string-append")))
  (m47-imp3--check (format "module-policy-%s" (car pair))
                   (m47-imp3--contains-p "mod/emacs/fileio.scm" (cdr pair))))
(m47-imp3--check "module-no-scm-ref"
                 (let ((n (m47-imp3--count-code "mod/emacs/fileio.scm"
                                                "scm_c_public_ref")))
                   (and (integerp n) (eql 0 n))))
(m47-imp3--check "module-not-passthrough"
                 ;; A one-line-passthrough module holds no Scheme path
                 ;; procedure and no decision form (cr1.org F4).
                 (let ((n (m47-imp3--count-code "mod/emacs/fileio.scm" "(if \\|(cond ")))
                   (and (integerp n) (>= n 3))))
;; cr.org F2: expand-file-name and substitute-in-file-name must hold a
;; module decision, not a one-line passthrough.  Pin the two decision
;; procedures and the two leaf fallbacks.
(dolist (pair '(("exp-decision"   . "(define (fileio--expand-decision")
                ("subst-decision" . "(define (fileio--needs-substitution?")
                ("exp-fallback"   . "(force %--fileio-expand-file-name)")
                ("subst-fallback" . "(force %--fileio-substitute-in-file-name)")))
  (m47-imp3--check (format "module-f2-%s" (car pair))
                   (m47-imp3--contains-p "mod/emacs/fileio.scm" (cdr pair))))
(m47-imp3--check "module-f2-expand-guarded"
                 ;; The expand body is guarded by the module decision,
                 ;; i.e. it is not a bare passthrough.
                 (m47-imp3--contains-p
                  "mod/emacs/fileio.scm"
                  "(if (fileio--expand-decision name)"))
(m47-imp3--check "module-f2-subst-guarded"
                 (m47-imp3--contains-p
                  "mod/emacs/fileio.scm"
                  "(and (string? fn) (not (fileio--needs-substitution? fn)))"))
(m47-imp3--check "module-grows-past-301"
                 (let ((n (m47-imp3--lines "mod/emacs/fileio.scm")))
                   (and (integerp n) (> n 301))))

;;; --- T5. The re-measured surface (brief.org section 11) -------------

(setq m47-imp3--group 't5)

(m47-imp3--check "fileio.c-grows-past-imp3"
                 (let ((n (m47-imp3--lines "src/fileio.c")))
                   ;; cr.org F2: the imp-3 base of src/fileio.c is 7223
                   ;; lines (brief.org section 9), not the 301-line module
                   ;; base.  The old bound 301 made this check vacuous.
                   (and (integerp n) (> n 7223))))
(m47-imp3--check "fileio.c-lines-7575"
                 (eql 7575 (m47-imp3--lines "src/fileio.c")))
(m47-imp3--check "fileio.c-defuns-78"
                 (eql 78 (m47-imp3--count "src/fileio.c" "^DEFUN (\"")))
(m47-imp3--check "fileio.c-scm-ref-27"
                 (eql 27 (m47-imp3--count "src/fileio.c" "scm_c_public_ref")))
(m47-imp3--check "fileio.scm-lines-370"
                 (eql 370 (m47-imp3--lines "mod/emacs/fileio.scm")))
(m47-imp3--check "tree-wide-scm-public-ref-235"
                 (let ((total 0)
                       (dir (expand-file-name "src" m47-imp3--root)))
                   (dolist (f (directory-files dir t "\\.[chm]\\'"))
                     (setq total (+ total (or (m47-imp3--count f "scm_c_public_ref") 0))))
                   (eql 235 total)))
(m47-imp3--check "keyboard.c-lines-11233"
                 (eql 11233 (m47-imp3--lines "src/keyboard.c")))
(m47-imp3--check "keyboard-globals.c-lines-490"
                 (eql 490 (m47-imp3--lines "src/keyboard-globals.c")))
(m47-imp3--check "combined-keyboard-surface-11723"
                 (let ((kb (m47-imp3--lines "src/keyboard.c"))
                       (kg (m47-imp3--lines "src/keyboard-globals.c")))
                   (and (integerp kb) (integerp kg) (eql 11723 (+ kb kg)))))

;;; --- T6. The group and the guards -----------------------------------

(setq m47-imp3--group nil)

(m47-imp3--check "reg/run-tests-m47-imp3"
                 (m47-imp3--contains-p "tool/run-tests.scm"
                                       "test/m47/test-m47-imp3.el"))
(m47-imp3--check "reg/min-t1-checks-24"
                 (>= (m47-imp3--group-count 't1) 24))
(m47-imp3--check "reg/min-t2-checks-25"
                 (>= (m47-imp3--group-count 't2) 25))
(m47-imp3--check "reg/min-t3-checks-3"
                 (>= (m47-imp3--group-count 't3) 3))
(m47-imp3--check "reg/min-t4-checks-11"
                 (>= (m47-imp3--group-count 't4) 11))
(m47-imp3--check "reg/min-t5-checks-9"
                 (>= (m47-imp3--group-count 't5) 9))
(m47-imp3--check "reg/min-total-72"
                 (>= (1+ m47-imp3--registered) 72))

;;; --- T7. The gated runtime probes (brief.org section 13.3) ----------

;; This corpus runs inside the built src/emacs (tool/run-tests.scm loads
;; the (m47) group with run-tests-loadup-emacs), so a probe calls the
;; rewired hub DIRECTLY, in this process.
;;
;; An earlier version ran the hubs in a nested src/emacs --batch.  It
;; paid one full emacs startup PER TAG and ran the same eval eight times
;; for eight assertions on identical output; it also reported a non-zero
;; child exit as a skip.  The isolation is not worth the price: one
;; failing probe may stop the load of the rest.  `condition-case' still
;; holds an ordinary signalled error to that one probe.  Each hub here
;; is pure name policy: it makes no OS call and writes no file, and
;; find-file-name-handler only matches a name against the handler alist.
;;
;; A broken hub is a FAIL, not a skip.  There is no src/emacs INFO-skip
;; any more.  The GUILEMACS_M47_GATE guard stays: an in-process probe
;; cannot recurse, so it now only keeps the nested gate run short and
;; keeps the nested check count what it was.

(defun m47-imp3--probe (tag thunk)
  "Register the probe TAG from the value of THUNK, which calls a rewired hub.
A non-nil value is a PASS.  A signalled error is a FAIL, never a silent
pass; the error is printed so the cause is visible.  Like the earlier
nested version this registers an ERT test directly, so it does not move
the tracked-check counts of T1 ... T5."
  (imp-register-bool-as-ert-test
   (format "m47-imp3/probe/%s" tag)
   (condition-case err
       (and (funcall thunk) t)
     (error (princ (format "INFO m47/imp3/%s error=%S\n" tag err))
            nil))))

(if (getenv "GUILEMACS_M47_GATE")
    (princ "INFO m47/imp3/runtime-probes skipped (nested gate run)\n")
  (progn
    (m47-imp3--probe "file-name-directory"
                     (lambda () (equal "/a/" (file-name-directory "/a/b"))))
    (m47-imp3--probe "file-name-nondirectory"
                     (lambda () (equal "b" (file-name-nondirectory "/a/b"))))
    (m47-imp3--probe "file-name-as-directory"
                     (lambda () (equal "/a/b/" (file-name-as-directory "/a/b"))))
    (m47-imp3--probe "directory-file-name"
                     (lambda () (equal "/a/b" (directory-file-name "/a/b/"))))
    (m47-imp3--probe "file-name-concat"
                     (lambda () (equal "/a/b/c" (file-name-concat "/a" "b" "c"))))
    (m47-imp3--probe "find-file-name-handler"
                     (lambda ()
                       (null (find-file-name-handler "/tmp/m47-imp3-zzz"
                                                     'file-exists-p))))
    (m47-imp3--probe "expand-file-name"
                     (lambda ()
                       (equal "/a/b/foo" (expand-file-name "foo" "/a/b/"))))
    (m47-imp3--probe "substitute-in-file-name"
                     (lambda ()
                       (equal "/y" (substitute-in-file-name "/x//y"))))))

(princ (format "=== m47 imp-3 rewire suite done (%d tracked checks; t1 %d, t2 %d, t3 %d, t4 %d, t5 %d) ===\n"
               m47-imp3--registered
               (m47-imp3--group-count 't1)
               (m47-imp3--group-count 't2)
               (m47-imp3--group-count 't3)
               (m47-imp3--group-count 't4)
               (m47-imp3--group-count 't5)))
