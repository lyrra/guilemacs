;;; test-m50-imp2.el --- M50 imp-2 corpus (the (emacs emacs) module and the
;;;                     daemonp boundary facts that survive M50 imp-3).
;;;
;;; M50 imp-2 added the typed C leaf --emacs-daemon-state and the module
;;; (emacs emacs) (docs/m50-plan.org section 3.3 and brief.org).  M50
;;; imp-3 DELETED that leaf and moved the daemonp decision into the
;;; module.  So this corpus no longer pins the leaf; it pins the module
;;; facts and the C boundary facts that survive imp-3 (brief.org
;;; section 7).  The moved decision, the C bridge, and the Scheme policy
;;; are pinned by test/m50/test-m50-imp3.el.
;;;
;;; This corpus reads tracked files only.  It pins:
;;;   G3 -- mod/emacs/emacs.scm holds (define-module (emacs emacs), it
;;;         is declarative, it states the elisp-nil rule (nil (#nil),
;;;         not #f), it holds no FFI and no scm_c_public_ref, and
;;;         prelude/load.scm loads (emacs emacs).
;;;   G4 -- the boundary rules: src/emacs.c still holds "guile.h", the
;;;         IS_DAEMON read, the daemon_name read, the Fdaemonp hub, and
;;;         daemon-initialized.
;;;   G5 -- the (m50) group carries this corpus, and a per-group
;;;         min-count guard fails when the corpus is truncated.
;;;
;;; A read error is a real error, never a silent pass.  An absent src/
;;; file is a real error.  This corpus reads no docs/ needle
;;; (docs/kb.org test-must-not-read-docs).

(princ "=== m50 imp-2 module / boundary suite ===\n")

(require 'imp-ert-report)

(defvar m50-imp2--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))

(defvar m50-imp2--registered 0
  "Total number of tracked-file checks this corpus has registered.")

(defvar m50-imp2--group nil
  "The group that `m50-imp2--check' counts into: `g3' or `g4', or nil.")

(defvar m50-imp2--counts nil
  "Alist of (GROUP . COUNT) for the registered tracked-file checks.")

(defun m50-imp2--group-count (group)
  "Number of tracked-file checks registered so far in GROUP."
  (or (cdr (assq group m50-imp2--counts)) 0))

(defun m50-imp2--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
the symbol `m50-imp2-absent' when REL does not exist."
  (let ((path (expand-file-name rel m50-imp2--root)))
    (if (not (file-exists-p path))
        'm50-imp2-absent
      (with-temp-buffer
        (insert-file-contents path)
        (funcall fn)))))

(defun m50-imp2--contains-p (rel needle)
  "Non-nil when REL (repo-root-relative) contains NEEDLE."
  (m50-imp2--with rel
    (lambda ()
      (goto-char (point-min))
      (search-forward needle nil t))))

(defun m50-imp2--tracked-p (rel needle)
  "Non-nil when the TRACKED file REL contains NEEDLE.  An absent tracked
file yields nil, so `m50-imp2--check' prints FAIL: an absent src/ file is
a real error, not a pass."
  (let ((hit (m50-imp2--contains-p rel needle)))
    (and (not (eq hit 'm50-imp2-absent)) (and hit t))))

(defun m50-imp2--count-code (rel regexp)
  "Count the matches of REGEXP in REL, skipping full comment lines.
A module comment may name a forbidden token (for example
`scm_c_public_ref') while explaining the contract; only the code must be
free of the token.  Scheme line comments start with `;'."
  (m50-imp2--with rel
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

(defun m50-imp2--check (name ok)
  "Report and register one check on a TRACKED file.  OK is a boolean.
An absent src/ file makes the reader return the symbol
`m50-imp2-absent', so `m50-imp2--check' prints FAIL -- an absent src/
file is a real error, not a pass."
  (if (eq ok 'm50-imp2-absent)
      (princ (format "INFO m50/imp2/%s skipped (source file absent)\n" name))
    (progn
      (princ (format "%s m50/imp2/%s\n" (if ok "PASS" "FAIL") name))
      (setq m50-imp2--registered (1+ m50-imp2--registered))
      (when m50-imp2--group
        (let ((cell (assq m50-imp2--group m50-imp2--counts)))
          (if cell
              (setcdr cell (1+ (cdr cell)))
            (push (cons m50-imp2--group 1) m50-imp2--counts))))
      (imp-register-bool-as-ert-test (format "m50-imp2/%s" name) (and ok t)))))

;;; --- G3. The module (brief.org section 4) ---------------------------

(setq m50-imp2--group 'g3)

(m50-imp2--check "module-exists"
                 (m50-imp2--tracked-p "mod/emacs/emacs.scm"
                                      "(define-module (emacs emacs)"))
(m50-imp2--check "module-declarative"
                 (m50-imp2--tracked-p "mod/emacs/emacs.scm" "#:declarative? #t"))
;; The C facts are Qt / Qnil; Qnil reads as Guile #nil, not #f.  The
;; module doc must keep that rule so no imp folds the elisp nil to #f.
(m50-imp2--check "module-nil-comment"
                 (m50-imp2--tracked-p "mod/emacs/emacs.scm" "nil (#nil)"))
(m50-imp2--check "module-no-ffi"
                 (let ((n (m50-imp2--count-code
                           "mod/emacs/emacs.scm"
                           "system foreign\\|dynamic-link\\|libc\\.so\\|system\\*\\|primitive-fork\\|posix_spawn\\|ioctl\\|dynamic-func")))
                   (and (integerp n) (eql 0 n))))
(m50-imp2--check "module-no-scm-ref"
                 (let ((n (m50-imp2--count-code "mod/emacs/emacs.scm"
                                                "scm_c_public_ref")))
                   (and (integerp n) (eql 0 n))))
(m50-imp2--check "load.scm-emacs"
                 (m50-imp2--tracked-p "prelude/load.scm"
                                      "(use-modules (emacs emacs))"))

;;; --- G4. The boundary rules (brief.org section 3) -------------------

(setq m50-imp2--group 'g4)

(m50-imp2--check "emacs.c-has-guile.h"
                 (m50-imp2--tracked-p "src/emacs.c" "#include \"guile.h\""))
(m50-imp2--check "mech-is-daemon"
                 (m50-imp2--tracked-p "src/emacs.c" "IS_DAEMON"))
(m50-imp2--check "mech-daemon-name"
                 (m50-imp2--tracked-p "src/emacs.c" "daemon_name"))
(m50-imp2--check "hub-fdaemonp-body"
                 (m50-imp2--tracked-p "src/emacs.c" "Fdaemonp"))
(m50-imp2--check "hub-daemon-initialized"
                 (m50-imp2--tracked-p "src/emacs.c" "daemon-initialized"))

;;; --- G5. The group and the guards -----------------------------------

(setq m50-imp2--group nil)

(m50-imp2--check "reg/run-tests-m50-imp2"
                 (m50-imp2--tracked-p "tool/run-tests.scm"
                                      "test/m50/test-m50-imp2.el"))
;; `m50-imp2--tracked-p' must fold an absent tracked file to nil, so that
;; `m50-imp2--check' prints FAIL for it: an absent src/ file is a real
;; error, not a pass.  A non-existent path stands in for an absent
;; tracked file.
(m50-imp2--check "reg/absent-tracked-file-fails"
                 (null (m50-imp2--tracked-p "src/m50-imp2-no-such-file.c"
                                            "needle")))
(m50-imp2--check "reg/min-g3-checks-6"
                 (>= (m50-imp2--group-count 'g3) 6))
(m50-imp2--check "reg/min-g4-checks-5"
                 (>= (m50-imp2--group-count 'g4) 5))

(princ (format "=== m50 imp-2 module / boundary suite done (%d tracked checks; g3 %d, g4 %d) ===\n"
               m50-imp2--registered
               (m50-imp2--group-count 'g3)
               (m50-imp2--group-count 'g4)))
