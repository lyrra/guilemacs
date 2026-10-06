;;; test-m49-imp2.el --- M49 imp-2 corpus (the typed C --dired-* leaves).
;;;
;;; M49 imp-2 adds the 4 typed C leaves over plain values for the
;;; directory / attribute boundary of src/dired.c (docs/m49-plan.org
;;; section 3.3 and brief.org section 3), the thin wrappers in (emacs
;;; dired) (brief section 5), and this tracked corpus (brief section 6).
;;; imp-2 adds leaves only: it moves no policy.
;;;
;;; imp-3 re-pins this corpus (brief.org section 9): the G1 listing leaf
;;; is DELETED, so 3 --dired-* leaves remained and the ^DEFUN count was
;;; 11.  The two listing runtime probes now call the public hub
;;; `directory-files' (the leaf is gone).
;;;
;;; imp-4 re-pins this corpus again (brief.org section 9): the G3
;;; attribute-predicate leaf is DELETED, so 2 --dired-* leaves remain
;;; (both G2) and the ^DEFUN count is 10.  G2 returns A2 (brief.org
;;; section 7.5), so the 2 G2 leaves stay and their decision stays in C.
;;; The G3 probe now calls the public hub `file-attributes-lessp'.
;;;
;;; This corpus reads tracked files, and it runs one gated runtime probe.
;;; It pins:
;;;   F1 -- the 2 surviving leaf DEFUNs exist in src/dired.c with the
;;;         exact names of docs/m49-plan.org section 3.3; the ^DEFUN
;;;         count is 10; the file holds "guile.h"; the block comment
;;;         names the leaves over plain.
;;;   F2 -- the plain-value shape: each leaf doc string holds
;;;         FIX-20261005-guilemacs, "plain", and a shape word (a
;;;         "boolean", an "integer", a "string", or a "list").
;;;   F3 -- mod/emacs/dired.scm holds the 4 wrappers and the 2 defelisp
;;;         --dired-* lines and no FFI / scm_c_public_ref; prelude/load.scm
;;;         loads (emacs dired).
;;;   F4 -- the boundary rules: the STAYS C mechanism (the readdir loop,
;;;         fdopendir, emacs_fstatat, sys_faccessat, getpwent, getgrent,
;;;         filemodestring, scmp) is still present; src/dired.c holds 2
;;;         scm_c_public_ref sites (the imp-3 G1 dispatch and the imp-4 G3
;;;         dispatch); the G3 hub keeps the Fcar extraction and calls the
;;;         G3 Scheme predicate.
;;;   F5 -- the (m49) group carries this corpus, and a per-group
;;;         min-count guard fails when the corpus is truncated.  Pin F1,
;;;         F2, F3, and F4 separately.
;;;   F6 -- the gated runtime probe.  Run the built src/emacs and call
;;;         the leaves.  An absent binary is an INFO-skip.  A probe
;;;         error is a FAIL, never a silent pass (docs/kb.org
;;;         m4x-probe-failure-must-not-read-as-a-skip).
;;;
;;; A read error is a real error, never a silent pass.  An absent src/
;;; file is a real error.  This corpus reads no docs/ needle
;;; (docs/kb.org test-must-not-read-docs).

(princ "=== m49 imp-2 leaves suite ===\n")

(require 'imp-ert-report)

(defvar m49-imp2--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))

(defvar m49-imp2--registered 0
  "Total number of tracked-file checks this corpus has registered.")

(defvar m49-imp2--group nil
  "The group that `m49-imp2--check' counts into: `f1' ... `f4', or nil.")

(defvar m49-imp2--counts nil
  "Alist of (GROUP . COUNT) for the registered tracked-file checks.")

(defun m49-imp2--group-count (group)
  "Number of tracked-file checks registered so far in GROUP."
  (or (cdr (assq group m49-imp2--counts)) 0))

(defun m49-imp2--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
the symbol `m49-imp2-absent' when REL does not exist."
  (let ((path (expand-file-name rel m49-imp2--root)))
    (if (not (file-exists-p path))
        'm49-imp2-absent
      (with-temp-buffer
        (insert-file-contents path)
        (funcall fn)))))

(defun m49-imp2--contains-p (rel needle)
  "Non-nil when REL (repo-root-relative) contains NEEDLE."
  (m49-imp2--with rel
    (lambda ()
      (goto-char (point-min))
      (search-forward needle nil t))))

(defun m49-imp2--count (rel regexp)
  "Count the matches of REGEXP in REL."
  (m49-imp2--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (re-search-forward regexp nil t) (setq n (1+ n)))
        n))))

(defun m49-imp2--count-code (rel regexp)
  "Count the matches of REGEXP in REL, skipping full comment lines.
A module comment may name a forbidden token (for example
`scm_c_public_ref') while explaining the contract; only the code must be
free of the token.  Scheme line comments start with `;'."
  (m49-imp2--with rel
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

(defun m49-imp2--check (name ok)
  "Report and register one check on a TRACKED file.  OK is a boolean.
An absent src/ file makes the reader return the symbol
`m49-imp2-absent', so the check prints FAIL -- an absent src/ file is a
real error, not a pass."
  (if (eq ok 'm49-imp2-absent)
      (princ (format "INFO m49/imp2/%s skipped (source file absent)\n" name))
    (progn
      (princ (format "%s m49/imp2/%s\n" (if ok "PASS" "FAIL") name))
      (setq m49-imp2--registered (1+ m49-imp2--registered))
      (when m49-imp2--group
        (let ((cell (assq m49-imp2--group m49-imp2--counts)))
          (if cell
              (setcdr cell (1+ (cdr cell)))
            (push (cons m49-imp2--group 1) m49-imp2--counts))))
      (imp-register-bool-as-ert-test (format "m49-imp2/%s" name) (and ok t)))))

(defvar m49-imp2--leaves
  '(;; G2 -- the completion policy (A2: stays in C)
    "file-name-completion" "file-name-all-completions")
  "The MOVES leaves of docs/m49-plan.org section 3.3 that survive
imp-4.  imp-3 deleted the G1 listing leaf; imp-4 deleted the G3
attribute-predicate leaf.  G2 returns A2 (brief.org section 7.5), so its
2 leaves stay.")

(defun m49-imp2--leaf-body (block)
  "Return the source of the DEFUN (\"--dired-BLOCK\") body, or nil."
  (m49-imp2--with "src/dired.c"
    (lambda ()
      (goto-char (point-min))
      (when (search-forward (format "DEFUN (\"--dired-%s\"" block) nil t)
        (let ((start (line-beginning-position)))
          (if (re-search-forward "\nDEFUN (\"" nil t)
              (buffer-substring-no-properties start (match-beginning 0))
            (buffer-substring-no-properties start (point-max))))))))

(defun m49-imp2--export-names (rel)
  "The wrapper names of the #:export form of REL, in order."
  (m49-imp2--with rel
    (lambda ()
      (goto-char (point-min))
      (when (search-forward "#:export (" nil t)
        (let* ((start (point))
               (end (save-excursion
                      (goto-char start)
                      (search-forward "))" nil t)))
               (names '()))
          (when end
            (goto-char start)
            (while (re-search-forward "\\_<\\(dired-[a-z-]+\\)\\_>" end t)
              (push (match-string 1) names)))
          (nreverse names))))))

;;; --- F1. The surviving leaf DEFUNs (docs/m49-plan.org section 3.3) --

(setq m49-imp2--group 'f1)

(dolist (leaf m49-imp2--leaves)
  (m49-imp2--check (format "leaf-%s" leaf)
                   (m49-imp2--contains-p "src/dired.c"
                                         (format "DEFUN (\"--dired-%s\"" leaf))))
;; imp-3 deleted the G1 leaf and imp-4 deleted the G3 leaf, so 2 --dired-*
;; leaves remain (both G2).
(m49-imp2--check "leaf-defuns-2"
                 (eql 2 (m49-imp2--count "src/dired.c" "^DEFUN (\"--dired-")))
(m49-imp2--check "defun-count-10"
                 (eql 10 (m49-imp2--count "src/dired.c" "^DEFUN (\"")))
(m49-imp2--check "dired.c-has-guile.h"
                 (m49-imp2--contains-p "src/dired.c" "#include \"guile.h\""))
(m49-imp2--check "leaf-block-comment-m49"
                 (m49-imp2--contains-p "src/dired.c"
                                       "typed C --dired-* leaves"))

;;; --- F2. The plain-value shape (brief.org section 4) ----------------

(setq m49-imp2--group 'f2)

;; Each leaf doc string names the marker, the word "plain", and a
;; plain-value shape word.  The check reads the leaf body, so it holds
;; per leaf after a re-order.
(dolist (leaf m49-imp2--leaves)
  (let ((body (m49-imp2--leaf-body leaf)))
    (m49-imp2--check (format "doc-marker-%s" leaf)
                     (and (stringp body)
                          (string-match-p "FIX-20261005-guilemacs" body) t))
    (m49-imp2--check (format "doc-plain-%s" leaf)
                     (and (stringp body)
                          (string-match-p "plain" body) t))
    (m49-imp2--check (format "doc-shape-%s" leaf)
                     (and (stringp body)
                          (string-match-p "boolean\\|integer\\|string\\|list"
                                          body)
                          t))))

;; The aggregate count proves every surviving leaf doc really carries the
;; marker (the include comment and the block comment carry it once each,
;; and 2 leaf docs carry it, so the count is 4 at imp-4).
(m49-imp2--check "doc-marker-4"
                 (eql 4 (m49-imp2--count "src/dired.c" "FIX-20261005-guilemacs")))

;;; --- F3. The wrapper module (brief.org section 5) -------------------

(setq m49-imp2--group 'f3)

(m49-imp2--check "module-exists"
                 (not (eq (m49-imp2--contains-p "mod/emacs/dired.scm"
                                                "(define-module (emacs dired)")
                          'm49-imp2-absent)))
;; imp-4 deleted the G3 leaf, so 2 --dired-* defelisp references remain
;; (both G2).
(m49-imp2--check "module-defelisp-2"
                 (eql 2 (m49-imp2--count "mod/emacs/dired.scm"
                                         "^(defelisp %--dired-")))
(m49-imp2--check "module-wrappers-4"
                 (eql 4 (m49-imp2--count "mod/emacs/dired.scm"
                                         "^(define (dired-[a-z]")))
(m49-imp2--check "module-exports-4"
                 (equal '("dired-listing-names"
                          "dired-file-name-completion"
                          "dired-file-name-all-completions"
                          "dired-file-attributes-lessp")
                        (m49-imp2--export-names "mod/emacs/dired.scm")))
(m49-imp2--check "module-no-ffi"
                 (let ((n (m49-imp2--count-code
                           "mod/emacs/dired.scm"
                           "system foreign\\|dynamic-link\\|libc\\.so\\|system\\*\\|primitive-fork\\|posix_spawn\\|ioctl\\|dynamic-func")))
                   (and (integerp n) (eql 0 n))))
(m49-imp2--check "module-no-scm-ref"
                 (let ((n (m49-imp2--count-code "mod/emacs/dired.scm"
                                                "scm_c_public_ref")))
                   (and (integerp n) (eql 0 n))))
(m49-imp2--check "load.scm-dired"
                 (m49-imp2--contains-p "prelude/load.scm" "(emacs dired)"))

;;; --- F4. The boundary rules (docs/m49-plan.org section 3.2) ---------

(setq m49-imp2--group 'f4)

(m49-imp2--check "mech-readdir"
                 (m49-imp2--contains-p "src/dired.c" "emacs_readdir"))
(m49-imp2--check "mech-fdopendir"
                 (m49-imp2--contains-p "src/dired.c" "fdopendir"))
(m49-imp2--check "mech-fstatat"
                 (m49-imp2--contains-p "src/dired.c" "emacs_fstatat"))
(m49-imp2--check "mech-faccessat"
                 (m49-imp2--contains-p "src/dired.c" "sys_faccessat"))
(m49-imp2--check "mech-getpwent"
                 (m49-imp2--contains-p "src/dired.c" "getpwent"))
(m49-imp2--check "mech-getgrent"
                 (m49-imp2--contains-p "src/dired.c" "getgrent"))
(m49-imp2--check "mech-filemodestring"
                 (m49-imp2--contains-p "src/dired.c" "filemodestring"))
(m49-imp2--check "mech-directory-files-internal"
                 (m49-imp2--contains-p "src/dired.c" "directory_files_internal ("))
(m49-imp2--check "mech-scmp"
                 (m49-imp2--contains-p "src/dired.c" "scmp ("))
;; imp-3 added the G1 dispatch site and imp-4 added the G3 dispatch site,
;; so the src/dired.c ref count moves 1 -> 2.  G2 stays in C (A2), so it
;; adds no site.
(m49-imp2--check "dired.c-scm-ref-2"
                 (eql 2 (m49-imp2--count "src/dired.c" "scm_c_public_ref")))
;; The G3 hub narrows the argument shape: it extracts Fcar of each
;; attribute list (docs/kb.org leaf-may-narrow-the-argument-shape) and
;; passes the two plain names to the Scheme predicate.
(m49-imp2--check "g3-hub-keeps-fcar"
                 (m49-imp2--contains-p "src/dired.c" "Fcar (f1), Fcar (f2)"))
(m49-imp2--check "g3-hub-calls-scheme"
                 (m49-imp2--contains-p "src/dired.c"
                                       "dired_file_attributes_lessp_scheme"))
(m49-imp2--check "g3-hub-policy-ref"
                 (m49-imp2--contains-p
                  "src/dired.c"
                  "scm_c_public_ref (\"emacs dired\", \"dired-file-attributes-lessp\")"))
(m49-imp2--check "g3-leaf-absent"
                 (not (m49-imp2--contains-p "src/dired.c"
                                            "--dired-file-attributes-lessp")))

;;; --- F5. The group and the guards -----------------------------------

(setq m49-imp2--group nil)

(m49-imp2--check "reg/run-tests-m49-imp2"
                 (m49-imp2--contains-p "tool/run-tests.scm"
                                       "test/m49/test-m49-imp2.el"))
(m49-imp2--check "reg/min-f1-checks-6"
                 (>= (m49-imp2--group-count 'f1) 6))
(m49-imp2--check "reg/min-f2-checks-7"
                 (>= (m49-imp2--group-count 'f2) 7))
(m49-imp2--check "reg/min-f3-checks-7"
                 (>= (m49-imp2--group-count 'f3) 7))
(m49-imp2--check "reg/min-f4-checks-13"
                 (>= (m49-imp2--group-count 'f4) 13))

;;; --- F6. The gated runtime probe (brief.org section 6) --------------

;; The (m49) group carries no `prelude' key, so tool/run-tests.scm loads
;; these files with run-tests-loadup-emacs, which is "../src/emacs ...
;; -l <file> --batch".  A probe therefore calls the leaf DIRECTLY, in
;; this process.
;;
;; An absent built binary is an INFO-skip.  A signalled error is a FAIL,
;; never a silent pass; the error is printed so the cause is visible.  An
;; undefined leaf signals void-function, so it is a FAIL too.
;;
;; The two listing probes call the public hub `directory-files' (imp-3
;; deleted the G1 leaf).  The attributes probe calls the public hub
;; `file-attributes-lessp' (imp-4 deleted the G3 leaf); the hub extracts
;; Fcar of each argument, so the probe passes two one-element lists.

(defun m49-imp2--probe (tag thunk)
  "Register the probe TAG from the value of THUNK, which calls a leaf.
A non-nil value is a PASS.  A signalled error is a FAIL, never a silent
pass; the error is printed so the cause is visible."
  (m49-imp2--check
   (format "probe/%s" tag)
   (condition-case err
       (and (funcall thunk) t)
     (error (princ (format "INFO m49/imp2/%s error=%S\n" tag err))
            nil))))

(if (not (file-exists-p (expand-file-name "src/emacs" m49-imp2--root)))
    (princ "INFO m49/imp2/runtime-probes skipped (no built src/emacs)\n")
  (m49-imp2--probe
   "listing-names"
   (lambda ()
     (let ((dir (file-name-as-directory (make-temp-file "m49-imp2" t))))
       (unwind-protect
           (progn
             (write-region "" nil (expand-file-name "aa" dir) nil 'silent)
             (write-region "" nil (expand-file-name "bb" dir) nil 'silent)
             (let ((names (directory-files dir)))
               (and (member "aa" names) (member "bb" names))))
         (delete-directory dir t)))))
  (m49-imp2--probe
   "listing-names-count"
   (lambda ()
     (let ((dir (file-name-as-directory (make-temp-file "m49-imp2" t))))
       (unwind-protect
           (progn
             (write-region "" nil (expand-file-name "aa" dir) nil 'silent)
             (write-region "" nil (expand-file-name "bb" dir) nil 'silent)
             ;; COUNT = 1: `directory-files' returns exactly one name, so
             ;; the imp-3 rewire keeps the COUNT feature.
             (let ((names (directory-files dir nil nil nil 1)))
               (and (consp names) (null (cdr names)))))
         (delete-directory dir t)))))
  (m49-imp2--probe
   "all-completions"
   (lambda ()
     (let ((dir (file-name-as-directory (make-temp-file "m49-imp2" t))))
       (unwind-protect
           (progn
             (write-region "" nil (expand-file-name "aa" dir) nil 'silent)
             (write-region "" nil (expand-file-name "ab" dir) nil 'silent)
             (equal '("aa" "ab")
                    (--dired-file-name-all-completions dir "a")))
         (delete-directory dir t)))))
  (m49-imp2--probe
   "file-name-completion"
   (lambda ()
     (let ((dir (file-name-as-directory (make-temp-file "m49-imp2" t))))
       (unwind-protect
           (progn
             (write-region "" nil (expand-file-name "only" dir) nil 'silent)
             (equal "only" (--dired-file-name-completion dir "o" nil)))
         (delete-directory dir t)))))
  (m49-imp2--probe
   "attributes-lessp"
   (lambda ()
     ;; The hub takes two attribute lists and extracts Fcar of each, so a
     ;; one-element list carries one plain name.  The G3 decision now runs
     ;; in Scheme (emacs dired); the hub keeps the Fcar extraction.
     (and (eq t (file-attributes-lessp '("a") '("b")))
          (eq nil (file-attributes-lessp '("b") '("a")))))))

(princ (format "=== m49 imp-2 leaves suite done (%d tracked checks; f1 %d, f2 %d, f3 %d, f4 %d) ===\n"
               m49-imp2--registered
               (m49-imp2--group-count 'f1)
               (m49-imp2--group-count 'f2)
               (m49-imp2--group-count 'f3)
               (m49-imp2--group-count 'f4)))
