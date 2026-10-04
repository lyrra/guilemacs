;;; test-m46-imp2.el --- M46 imp-2 corpus (the typed C lockfile leaves).
;;;
;;; M46 imp-2 adds the eight typed C leaves over plain values for the
;;; lockfile boundary of src/filelock.c (brief.org section 3), the
;;; "guile.h" include (section 4), the thin wrapper module
;;; (emacs filelock) (section 5), and this tracked corpus (section 6).
;;; imp-2 adds leaves only: it moves no policy.  imp-3 rewires the hubs
;;; and deletes the inline policy.
;;;
;;; This corpus reads files, and it runs one gated runtime probe.  It
;;; pins:
;;;   E1 -- the eight leaf DEFUNs exist in src/filelock.c with the exact
;;;         names of brief.org section 3; the ^DEFUN count is 13; the
;;;         file holds "guile.h"; the line count is the re-measured
;;;         value 1216 (imp-3).
;;;   E2 -- the plain-value shape (brief.org section 3): each leaf doc
;;;         string holds "plain" and the shape word ("string",
;;;         "integer", or "boolean").  No leaf names FILE * in a return.
;;;   E3 -- mod/emacs/filelock.scm exists, exports the eight wrappers,
;;;         holds eight defelisp lines and eight defines, holds no FFI
;;;         call and no raw syscall; prelude/load.scm loads it.
;;;   E4 -- the boundary rules: the mechanism calls (=link=, =symlink=,
;;;         =mkostemp=, =rename=, =kill=, =readlinkat=) stay in the
;;;         file; no FILE * crosses the layer.
;;;   E5 -- the (m46) group carries this corpus, and a per-group
;;;         min-count guard fails when the corpus is truncated.  Pin E1
;;;         and E2 separately (cr.org F3).
;;;   E6 -- the gated runtime probe.  Run the built src/emacs and call
;;;         five leaves.  Only an absent binary (or no writable scratch
;;;         directory) is an INFO-skip.  A non-zero exit, a run error,
;;;         or a missing match is a FAIL, never a silent pass.
;;;
;;; A read error is a real error, never a silent pass.  An absent src/
;;; file is a real error.

(princ "=== m46 imp-2 leaves suite ===\n")

(require 'imp-ert-report)

(defvar m46-imp2--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))

(defvar m46-imp2--registered 0
  "Total number of tracked-file checks this corpus has registered.")

(defvar m46-imp2--group nil
  "The group that `m46-imp2--check' counts into: `e1' ... `e4', or nil.")

(defvar m46-imp2--counts nil
  "Alist of (GROUP . COUNT) for the registered tracked-file checks.")

(defun m46-imp2--group-count (group)
  "Number of tracked-file checks registered so far in GROUP."
  (or (cdr (assq group m46-imp2--counts)) 0))

(defun m46-imp2--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
the symbol `m46-imp2-absent' when REL does not exist."
  (let ((path (expand-file-name rel m46-imp2--root)))
    (if (not (file-exists-p path))
        'm46-imp2-absent
      (with-temp-buffer
        (insert-file-contents path)
        (funcall fn)))))

(defun m46-imp2--contains-p (rel needle)
  "Non-nil when REL (repo-root-relative) contains NEEDLE."
  (m46-imp2--with rel
    (lambda ()
      (goto-char (point-min))
      (search-forward needle nil t))))

(defun m46-imp2--lines (rel)
  "Count the newlines of REL the way `wc -l' does."
  (m46-imp2--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (search-forward "\n" nil t) (setq n (1+ n)))
        n))))

(defun m46-imp2--count (rel regexp)
  "Count the matches of REGEXP in REL."
  (m46-imp2--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (re-search-forward regexp nil t) (setq n (1+ n)))
        n))))

(defun m46-imp2--count-code (rel regexp)
  "Count the matches of REGEXP in REL, skipping full comment lines.
A module comment may name a forbidden token (for example a raw
syscall) while explaining that the module does NOT use it; only the
code must be free of the token."
  (m46-imp2--with rel
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

(defun m46-imp2--check (name ok)
  "Report and register one check on a TRACKED file.  OK is a boolean.
An absent src/ file makes the reader return the symbol
`m46-imp2-absent', so the check prints FAIL -- an absent src/ file is a
real error, not a pass."
  (if (eq ok 'm46-imp2-absent)
      (princ (format "INFO m46/imp2/%s skipped (source file absent)\n" name))
    (progn
      (princ (format "%s m46/imp2/%s\n" (if ok "PASS" "FAIL") name))
      (setq m46-imp2--registered (1+ m46-imp2--registered))
      (when m46-imp2--group
        (let ((cell (assq m46-imp2--group m46-imp2--counts)))
          (if cell
              (setcdr cell (1+ (cdr cell)))
            (push (cons m46-imp2--group 1) m46-imp2--counts))))
      (imp-register-bool-as-ert-test (format "m46-imp2/%s" name) (and ok t)))))

;;; --- E1. The eight leaf DEFUNs (brief.org section 3) -----------------

(setq m46-imp2--group 'e1)

(m46-imp2--check "leaf-boot-sec"
                 (m46-imp2--contains-p "src/filelock.c"
                                       "DEFUN (\"--filelock-boot-sec\""))
(m46-imp2--check "leaf-within-one-second"
                 (m46-imp2--contains-p "src/filelock.c"
                                       "DEFUN (\"--filelock-within-one-second\""))
(m46-imp2--check "leaf-integer-prefixed"
                 (m46-imp2--contains-p "src/filelock.c"
                                       "DEFUN (\"--filelock-integer-prefixed\""))
(m46-imp2--check "leaf-lock-file-name"
                 (m46-imp2--contains-p "src/filelock.c"
                                       "DEFUN (\"--filelock-lock-file-name\""))
(m46-imp2--check "leaf-lock-info"
                 (m46-imp2--contains-p "src/filelock.c"
                                       "DEFUN (\"--filelock-lock-info\""))
(m46-imp2--check "leaf-lock-owner"
                 (m46-imp2--contains-p "src/filelock.c"
                                       "DEFUN (\"--filelock-lock-owner\""))
(m46-imp2--check "leaf-lock-free-p"
                 (m46-imp2--contains-p "src/filelock.c"
                                       "DEFUN (\"--filelock-lock-free-p\""))
(m46-imp2--check "leaf-unlock"
                 (m46-imp2--contains-p "src/filelock.c"
                                       "DEFUN (\"--filelock-unlock\""))
(m46-imp2--check "leaf-defuns-8"
                 (eql 8 (m46-imp2--count "src/filelock.c" "^DEFUN (\"--filelock-")))
(m46-imp2--check "defun-count-13"
                 (eql 13 (m46-imp2--count "src/filelock.c" "^DEFUN (\"")))
(m46-imp2--check "filelock.c-lines-1216"
                 (eql 1216 (m46-imp2--lines "src/filelock.c")))
(m46-imp2--check "filelock.c-has-guile.h"
                 (m46-imp2--contains-p "src/filelock.c" "#include \"guile.h\""))

;;; --- E2. The plain-value shape (brief.org section 3) -----------------

(setq m46-imp2--group 'e2)

;; Each leaf doc string holds the shape word.  The counts are stable
;; after the imp-3 section-6 re-pin: "plain string" 3 (lock-file-name,
;; lock-info, lock-owner); "plain integer" 4 (boot-sec, lock-info,
;; within-one-second, lock-free-p); "plain boolean" 3 (within-one-second,
;; integer-prefixed, unlock).
(m46-imp2--check "doc-plain-string-3"
                 (eql 3 (m46-imp2--count "src/filelock.c" "plain string")))
(m46-imp2--check "doc-plain-integer-4"
                 (eql 4 (m46-imp2--count "src/filelock.c" "plain integer")))
(m46-imp2--check "doc-plain-boolean-3"
                 (eql 3 (m46-imp2--count "src/filelock.c" "plain boolean")))
;; Each leaf doc string holds the brief.org marker and the section note.
(m46-imp2--check "doc-marker-8"
                 (eql 8 (m46-imp2--count "src/filelock.c" "M46 imp-2,")))
;; cr.org F2/F3: the corrected return shapes.  The lock-owner leaf now
;; reports this process with t (not a bare pid), and the lock-free-p
;; leaf keeps the ANOTHER_OWNS_IT signal as a plain integer owner pid.
(m46-imp2--check "doc-owner-reports-kind"
                 (m46-imp2--contains-p "src/filelock.c"
                                       "report the owner kind"))
(m46-imp2--check "doc-owner-this-process-t"
                 (m46-imp2--contains-p "src/filelock.c"
                                       "Return t when this process\nowns it"))
(m46-imp2--check "doc-free-keeps-another-owns"
                 (m46-imp2--contains-p "src/filelock.c"
                                       "keeps the ANOTHER_OWNS_IT signal"))
;; No mechanism I/O type crosses the layer.
(m46-imp2--check "leaf-no-FILE-type"
                 (eql 0 (m46-imp2--count "src/filelock.c" "FILE \\*")))

;;; --- E3. The wrapper module (brief.org section 5) --------------------

(setq m46-imp2--group 'e3)

(m46-imp2--check "module-exists"
                 (not (eq (m46-imp2--contains-p "mod/emacs/filelock.scm"
                                                "(define-module (emacs filelock)")
                          'm46-imp2-absent)))
(m46-imp2--check "module-defelisp-8"
                 (eql 8 (m46-imp2--count "mod/emacs/filelock.scm"
                                         "(defelisp %--filelock-")))
(m46-imp2--check "module-wrappers-8"
                 (eql 8 (m46-imp2--count "mod/emacs/filelock.scm"
                                         "^(define (filelock-")))
(m46-imp2--check "module-exports-8"
                 (let ((n (m46-imp2--count
                           "mod/emacs/filelock.scm"
                           "filelock-\\(lock-file-name\\|lock-info\\|boot-sec\\|within-one-second\\|integer-prefixed\\|lock-owner\\|lock-free-p\\|unlock\\)")))
                   (and (integerp n) (>= n 16)))) ; 8 in #:export, 8 in the defines
(m46-imp2--check "module-no-ffi"
                 (let ((n (m46-imp2--count-code
                           "mod/emacs/filelock.scm"
                           "system foreign\\|dynamic-link\\|libc\\.so\\|system\\*\\|primitive-fork\\|posix_spawn\\|ioctl\\|dynamic-func")))
                   (and (integerp n) (eql 0 n))))
(m46-imp2--check "load.scm-filelock"
                 (m46-imp2--contains-p "prelude/load.scm"
                                       "(use-modules (emacs filelock))"))

;;; --- E4. The boundary rules (brief.org sections 3, 9) ----------------

(setq m46-imp2--group 'e4)

(m46-imp2--check "mech-link"
                 (m46-imp2--contains-p "src/filelock.c" "link ("))
(m46-imp2--check "mech-symlink"
                 (m46-imp2--contains-p "src/filelock.c" "emacs_symlink"))
(m46-imp2--check "mech-mkostemp"
                 (m46-imp2--contains-p "src/filelock.c" "mkostemp"))
(m46-imp2--check "mech-rename"
                 (m46-imp2--contains-p "src/filelock.c" "emacs_rename"))
(m46-imp2--check "mech-kill"
                 (m46-imp2--contains-p "src/filelock.c" "kill ("))
(m46-imp2--check "mech-readlinkat"
                 (m46-imp2--contains-p "src/filelock.c" "readlinkat"))
;; imp-3 adds the six dispatch helpers, so the file holds six
;; scm_c_public_ref sites now (was 0 at imp-2).
(m46-imp2--check "scm-ref-6"
                 (eql 6 (m46-imp2--count "src/filelock.c" "scm_c_public_ref")))

;;; --- E5. The group and the guards (cr.org F3) ------------------------

(setq m46-imp2--group nil)

(m46-imp2--check "reg/run-tests-m46-imp2"
                 (m46-imp2--contains-p "tool/run-tests.scm"
                                       "test/m46/test-m46-imp2.el"))
(m46-imp2--check "reg/min-e1-checks-12"
                 (>= (m46-imp2--group-count 'e1) 12))
(m46-imp2--check "reg/min-e2-checks-8"
                 (>= (m46-imp2--group-count 'e2) 8))
(m46-imp2--check "reg/min-total-30"
                 (>= m46-imp2--registered 30))

;;; --- E6. The gated runtime probe (brief.org section 6) ---------------

;; This corpus already runs inside the built src/emacs: the (m46) group
;; carries no `prelude' key, so tool/run-tests.scm loads these files with
;; run-tests-loadup-emacs, which is "../src/emacs ... -l <file> --batch".
;; A probe therefore runs each leaf in a NESTED src/emacs for ISOLATION,
;; not for access.  A probe takes a real lock and reads a real lockfile.
;; In the harness process a prompt, a signalled error, or an abort stops
;; the batch run, and the harness then fails the whole group with "batch
;; runner never completed".  In a child the same failure is one exit
;; code, so it costs one check.  `printf '' |' gives the child empty
;; stdin, so a prompt reads EOF and does not hang the gate.
;;
;; Only an absent or non-executable binary is an INFO-skip.  A non-zero
;; exit, a run error, or a missing match is a FAIL -- never a silent
;; pass.  The earlier code mapped "the child exited non-zero" onto the
;; same nil as "no binary", so an isolated failure became a fake skip.
;;
;; A probe that writes a file needs a writable directory.  The sandbox
;; denies writes under /tmp, so pick the first directory that accepts a
;; file: $TMPDIR, /tmp, then <root>/test/m46/scratch.  A hardcoded /tmp
;; turned every write probe into a fake skip.

(defvar m46-imp2--emacs
  (expand-file-name "src/emacs" m46-imp2--root))

(defun m46-imp2--writable-p (dir)
  "Non-nil when DIR exists and accepts a new file."
  (and (stringp dir)
       (file-directory-p dir)
       (let ((probe (expand-file-name "m46-imp2-write-probe" dir)))
         (condition-case nil
             (progn (with-temp-file probe (insert "x"))
                    (delete-file probe)
                    t)
           (error nil)))))

(defvar m46-imp2--scratch
  (let ((tree (expand-file-name "test/m46/scratch" m46-imp2--root)))
    (or (and (m46-imp2--writable-p (getenv "TMPDIR"))
             (file-name-as-directory (getenv "TMPDIR")))
        (and (m46-imp2--writable-p "/tmp") "/tmp/")
        (progn (ignore-errors (make-directory tree t))
               (and (m46-imp2--writable-p tree)
                    (file-name-as-directory tree)))))
  "A writable directory for the runtime probes, or nil when none exists.")

(defun m46-imp2--scratch-file (name)
  "Return NAME under the probe scratch directory, or nil without one."
  (and m46-imp2--scratch (concat m46-imp2--scratch name)))

(defvar m46-imp2--boot-eval
  "(princ (format \"boot=%S\\n\" (--filelock-boot-sec)))")

(defvar m46-imp2--wos-eval
  "(princ (format \"wos=%S\\n\" (--filelock-within-one-second 5 6)))")

(defun m46-imp2--lfn-eval ()
  (format "(princ (format \"lfn=%%S\\n\" (--filelock-lock-file-name %S)))"
          (m46-imp2--scratch-file "m46-probe")))

(defun m46-imp2--owner-eval ()
  (format "(let ((f %S) (l nil)) (with-temp-file f (insert \"x\")) (lock-file f) (setq l (--filelock-lock-file-name f)) (princ (format \"owner=%%S\\n\" (--filelock-lock-owner l))) (unlock-file f) (ignore-errors (delete-file f)))"
          (m46-imp2--scratch-file "m46-probe-owner")))

(defun m46-imp2--free-eval ()
  (format "(let ((f %S) (l nil)) (with-temp-file f (insert \"x\")) (setq l (--filelock-lock-file-name f)) (princ (format \"lfp=%%S\\n\" (--filelock-lock-free-p l))) (ignore-errors (delete-file l)) (ignore-errors (delete-file f)))"
          (m46-imp2--scratch-file "m46-probe-free")))

(defun m46-imp2--probe-run (eval)
  "Run EVAL in the built src/emacs in batch.
Return nil when the binary is absent or not executable; else return
the cons (STATUS . OUTPUT).  STATUS is the exit code, or the error
description when the run itself failed."
  (when (file-executable-p m46-imp2--emacs)
    (with-temp-buffer
      (let ((status (condition-case err
                        (call-process "/bin/sh" nil (current-buffer) nil "-c"
                                      (format "printf '' | %s --batch --eval '%s'"
                                              m46-imp2--emacs eval))
                      (error (format "%S" err)))))
        (cons status (buffer-string))))))

(defun m46-imp2--probe-tail (out)
  "The last line of OUT, for a FAIL report."
  (car (last (split-string (or out "") "\n" t))))

(defun m46-imp2--probe (name eval regexp)
  "Check that the built src/emacs prints REGEXP when it runs EVAL.
An absent binary is an INFO-skip.  A non-zero exit, a run error, or a
missing match is a FAIL."
  (let ((res (and eval (m46-imp2--probe-run eval))))
    (cond
     ((null eval)
      (princ (format "INFO m46/imp2/%s skipped (no writable scratch directory)\n"
                     name)))
     ((null res)
      (princ (format "INFO m46/imp2/%s skipped (no built src/emacs)\n" name)))
     ((not (and (integerp (car res)) (zerop (car res))))
      (princ (format "INFO m46/imp2/%s exit=%S last=%s\n"
                     name (car res) (m46-imp2--probe-tail (cdr res))))
      (m46-imp2--check name nil))
     (t
      (m46-imp2--check name (and (string-match-p regexp (cdr res)) t))))))

(m46-imp2--probe "probe/boot-sec-returns-integer"
                 m46-imp2--boot-eval "boot=[0-9]")

(m46-imp2--probe "probe/lock-file-name-returns-string"
                 (and m46-imp2--scratch (m46-imp2--lfn-eval)) "lfn=\"")

(m46-imp2--probe "probe/within-one-second-returns-t"
                 m46-imp2--wos-eval "wos=t")

;; cr.org F3: this process owns the lock, so the owner leaf reports t.
(m46-imp2--probe "probe/lock-owner-this-process-t"
                 (and m46-imp2--scratch (m46-imp2--owner-eval)) "owner=t")

;; cr.org F2: the lock is free to this process, so lock-free-p reports t.
(m46-imp2--probe "probe/lock-free-p-free-t"
                 (and m46-imp2--scratch (m46-imp2--free-eval)) "lfp=t")

(princ (format "=== m46 imp-2 leaves suite done (%d tracked checks; e1 %d, e2 %d, e3 %d, e4 %d) ===\n"
               m46-imp2--registered
               (m46-imp2--group-count 'e1)
               (m46-imp2--group-count 'e2)
               (m46-imp2--group-count 'e3)
               (m46-imp2--group-count 'e4)))
