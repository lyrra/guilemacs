;;; test-m48-imp2.el --- M48 imp-2 corpus (the typed C --term-* leaves).
;;;
;;; M48 imp-2 added typed C leaves over plain values for the TTY terminal
;;; boundary (docs/m48-plan.org section 3.3).  Imp-6 retired the two
;;; geometry leaves after moving their arithmetic into Scheme.  This
;;; corpus checks the six surviving leaves and the module wrappers.
;;;
;;; This corpus reads tracked files, and it runs one gated runtime probe.
;;; It pins:
;;;   E1 -- the 6 surviving leaf DEFUNs exist in src/term.c; the two
;;;         retired geometry leaves are absent; the ^DEFUN count is 25;
;;;         the file holds "guile.h" and the block comment names the leaves.
;;;   E2 -- the plain-value shape: each leaf doc string holds
;;;         FIX-20261005-guilemacs, "plain", and a shape word (a
;;;         "boolean", an "integer", a "string", or a "list").
;;;   E3 -- mod/emacs/terminal.scm holds 8 public wrappers and 6
;;;         defelisp lines, and no FFI / scm_c_public_ref;
;;;         prelude/load.scm loads (emacs terminal).
;;;   E4 -- the boundary rules: the STAYS C mechanism (the terminfo
;;;         handle, tputs, ioctl, tcgetpgrp, setsid, emacs_open, the
;;;         hooks) is still present; the 3 (emacs terminal) ref sites are
;;;         still present.
;;;   E5 -- the (m48) group carries this corpus, and a per-group
;;;         min-count guard fails when the corpus is truncated.  Pin E1
;;;         and E2 separately.
;;;   E6 -- the gated runtime probe.  Run the built src/emacs and call
;;;         three leaves.  An absent binary is an INFO-skip.  A probe
;;;         error is a FAIL, never a silent pass (docs/kb.org
;;;         m4x-probe-failure-must-not-read-as-a-skip).
;;;
;;; A read error is a real error, never a silent pass.  An absent src/
;;; file is a real error.

(princ "=== m48 imp-2 leaves suite ===\n")

(require 'imp-ert-report)

(defvar m48-imp2--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))

(defvar m48-imp2--registered 0
  "Total number of tracked-file checks this corpus has registered.")

(defvar m48-imp2--group nil
  "The group that `m48-imp2--check' counts into: `e1' ... `e4', or nil.")

(defvar m48-imp2--counts nil
  "Alist of (GROUP . COUNT) for the registered tracked-file checks.")

(defun m48-imp2--group-count (group)
  "Number of tracked-file checks registered so far in GROUP."
  (or (cdr (assq group m48-imp2--counts)) 0))

(defun m48-imp2--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
the symbol `m48-imp2-absent' when REL does not exist."
  (let ((path (expand-file-name rel m48-imp2--root)))
    (if (not (file-exists-p path))
        'm48-imp2-absent
      (with-temp-buffer
        (insert-file-contents path)
        (funcall fn)))))

(defun m48-imp2--contains-p (rel needle)
  "Non-nil when REL (repo-root-relative) contains NEEDLE."
  (m48-imp2--with rel
    (lambda ()
      (goto-char (point-min))
      (search-forward needle nil t))))

(defun m48-imp2--count (rel regexp)
  "Count the matches of REGEXP in REL."
  (m48-imp2--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (re-search-forward regexp nil t) (setq n (1+ n)))
        n))))

(defun m48-imp2--count-code (rel regexp)
  "Count the matches of REGEXP in REL, skipping full comment lines.
A module comment may name a forbidden token (for example
`scm_c_public_ref') while explaining the contract; only the code must be
free of the token.  Scheme line comments start with `;'."
  (m48-imp2--with rel
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

(defun m48-imp2--check (name ok)
  "Report and register one check on a TRACKED file.  OK is a boolean.
An absent src/ file makes the reader return the symbol
`m48-imp2-absent', so the check prints FAIL -- an absent src/ file is a
real error, not a pass."
  (if (eq ok 'm48-imp2-absent)
      (princ (format "INFO m48/imp2/%s skipped (source file absent)\n" name))
    (progn
      (princ (format "%s m48/imp2/%s\n" (if ok "PASS" "FAIL") name))
      (setq m48-imp2--registered (1+ m48-imp2--registered))
      (when m48-imp2--group
        (let ((cell (assq m48-imp2--group m48-imp2--counts)))
          (if cell
              (setcdr cell (1+ (cdr cell)))
            (push (cons m48-imp2--group 1) m48-imp2--counts))))
      (imp-register-bool-as-ert-test (format "m48-imp2/%s" name) (and ok t)))))

(defvar m48-imp2--leaves
  '(;; G1 -- the terminal-capability policy
    "display-color-p" "display-color-cells" "type" "controlling-tty-p"
    ;; G3 -- the surviving pixel-dimension leaves
    "display-pixel-width" "display-pixel-height")
  "The six surviving --term-* leaves.")

(defun m48-imp2--leaf-body (block)
  "Return the source of the DEFUN (\"--term-BLOCK\") body, or nil."
  (m48-imp2--with "src/term.c"
    (lambda ()
      (goto-char (point-min))
      (when (search-forward (format "DEFUN (\"--term-%s\"" block) nil t)
        (let ((start (line-beginning-position)))
          (if (re-search-forward "\nDEFUN (\"" nil t)
              (buffer-substring-no-properties start (match-beginning 0))
            (buffer-substring-no-properties start (point-max))))))))

;;; --- E1. The surviving leaf DEFUNs (docs/m48-plan.org section 3.3) ---

(setq m48-imp2--group 'e1)

(dolist (leaf m48-imp2--leaves)
  (m48-imp2--check (format "leaf-%s" leaf)
                   (m48-imp2--contains-p "src/term.c"
                                         (format "DEFUN (\"--term-%s\"" leaf))))
(m48-imp2--check "leaf-defuns-6"
                 (eql 6 (m48-imp2--count "src/term.c" "^DEFUN (\"--term-")))
;; M61 imp-2 re-pin: the 2 new leaves, the shared guard and the routed
;; flush/termscript sites moved the surface.  MEASURED on this tree.
(m48-imp2--check "defun-count-33"
                 (eql 33 (m48-imp2--count "src/term.c" "^DEFUN (\"")))
(m48-imp2--check "geometry-leaves-retired"
                 (and (not (m48-imp2--contains-p
                            "src/term.c" "DEFUN (\"--term-frame-geometry\""))
                      (not (m48-imp2--contains-p
                            "src/term.c" "DEFUN (\"--term-frame-edges\""))))
(m48-imp2--check "term.c-has-guile.h"
                 (m48-imp2--contains-p "src/term.c" "#include \"guile.h\""))
(m48-imp2--check "leaf-block-comment-m48"
                 (m48-imp2--contains-p "src/term.c"
                                       "typed C leaves over plain"))

;;; --- E2. The plain-value shape (brief.org section 4) ----------------

(setq m48-imp2--group 'e2)

;; Each leaf doc string names the marker, the word "plain", and a
;; plain-value shape word.  The check reads the leaf body, so it holds
;; per leaf after a re-order.
(dolist (leaf m48-imp2--leaves)
  (let ((body (m48-imp2--leaf-body leaf)))
    (m48-imp2--check (format "doc-marker-%s" leaf)
                     (and (stringp body)
                          (string-match-p "FIX-20261005-guilemacs" body) t))
    (m48-imp2--check (format "doc-plain-%s" leaf)
                     (and (stringp body)
                          (string-match-p "plain" body) t))
    (m48-imp2--check (format "doc-shape-%s" leaf)
                     (and (stringp body)
                          (string-match-p "boolean\\|integer\\|string\\|list"
                                          body)
                          t))))

;; Six typed leaves remain after imp-6 retired the two geometry leaves.
;; The source currently has ten FIX markers and six M48 imp-2 leaf docs.
(m48-imp2--check "doc-marker-count-10"
                 (eql 10 (m48-imp2--count "src/term.c"
                                           "FIX-20261005-guilemacs")))
(m48-imp2--check "leaf-doc-count-6"
                 (eql 6 (m48-imp2--count "src/term.c" "M48 imp-2,")))

;;; --- E3. The wrapper module (brief.org section 5) -------------------

(setq m48-imp2--group 'e3)

(m48-imp2--check "module-exists"
                 (not (eq (m48-imp2--contains-p "mod/emacs/terminal.scm"
                                                "(define-module (emacs terminal)")
                          'm48-imp2-absent)))
(m48-imp2--check "module-defelisp-6"
                 (eql 6 (m48-imp2--count "mod/emacs/terminal.scm"
                                         "(defelisp %--term-")))
(m48-imp2--check "module-wrappers-8"
                 (eql 8 (m48-imp2--count "mod/emacs/terminal.scm"
                                         "^(define (term-[a-z]")))
(m48-imp2--check "module-exports-8"
                 (eql 8 (m48-imp2--count "mod/emacs/terminal.scm"
                                         "^            term-")))
(m48-imp2--check "module-no-ffi"
                 (let ((n (m48-imp2--count-code
                           "mod/emacs/terminal.scm"
                           "system foreign\\|dynamic-link\\|libc\\.so\\|system\\*\\|primitive-fork\\|posix_spawn\\|ioctl\\|dynamic-func")))
                   (and (integerp n) (eql 0 n))))
(m48-imp2--check "module-no-scm-ref"
                 (let ((n (m48-imp2--count-code "mod/emacs/terminal.scm"
                                                "scm_c_public_ref")))
                   (and (integerp n) (eql 0 n))))
(m48-imp2--check "load.scm-terminal"
                 (m48-imp2--contains-p "prelude/load.scm" "(emacs terminal)"))

;;; --- E4. The boundary rules (docs/m48-plan.org section 3.2) ---------

(setq m48-imp2--group 'e4)

(m48-imp2--check "mech-tgetent"
                 (m48-imp2--contains-p "src/term.c" "tgetent"))
(m48-imp2--check "mech-tputs"
                 (m48-imp2--contains-p "src/term.c" "tputs"))
(m48-imp2--check "mech-ioctl"
                 (m48-imp2--contains-p "src/term.c" "ioctl"))
(m48-imp2--check "mech-tcgetpgrp"
                 (m48-imp2--contains-p "src/term.c" "tcgetpgrp"))
(m48-imp2--check "mech-setsid"
                 (m48-imp2--contains-p "src/term.c" "setsid"))
(m48-imp2--check "mech-emacs-open"
                 (m48-imp2--contains-p "src/term.c" "emacs_open"))
(m48-imp2--check "mech-hooks"
                 (and (m48-imp2--contains-p "src/term.c"
                                            "suspend-tty-functions")
                      (m48-imp2--contains-p "src/term.c"
                                            "resume-tty-functions")))
;; The 3 M33 imp-1 ref sites do not move (imp-3 / imp-4 do not touch them).
(m48-imp2--check "refs-tty-menu-clear-help"
                 (m48-imp2--contains-p
                  "src/term.c"
                  "scm_c_public_ref (\"emacs terminal\", \"tty-menu-clear-help!\""))
(m48-imp2--check "refs-tty-menu-discard-mouse-events"
                 (m48-imp2--contains-p
                  "src/term.c"
                  "scm_c_public_ref (\"emacs terminal\", \"tty-menu-discard-mouse-events!\""))
(m48-imp2--check "refs-tty-menu-help-callback"
                 (m48-imp2--contains-p
                  "src/term.c"
                  "scm_c_public_ref (\"emacs terminal\", \"tty-menu-help-callback\""))

;;; --- E5. The group and the guards -----------------------------------

(setq m48-imp2--group nil)

(m48-imp2--check "reg/run-tests-m48-imp2"
                 (m48-imp2--contains-p "tool/run-tests.scm"
                                       "test/m48/test-m48-imp2.el"))
(m48-imp2--check "reg/min-e1-checks-11"
                 (>= (m48-imp2--group-count 'e1) 11))
(m48-imp2--check "reg/min-e2-checks-20"
                 (>= (m48-imp2--group-count 'e2) 20))
(m48-imp2--check "reg/min-total-40"
                 (>= m48-imp2--registered 40))

;;; --- E6. The gated runtime probe (brief.org section 6.1) ------------

;; The (m48) group carries no `prelude' key, so tool/run-tests.scm loads
;; these files with run-tests-loadup-emacs, which is "../src/emacs ...
;; -l <file> --batch".  A probe therefore calls the leaf DIRECTLY, in
;; this process.
;;
;; An absent built binary is an INFO-skip.  A signalled error is a FAIL,
;; never a silent pass; the error is printed so the cause is visible.  An
;; undefined leaf signals void-function, so it is a FAIL too.

(defun m48-imp2--probe (tag thunk)
  "Register the probe TAG from the value of THUNK, which calls a leaf.
A non-nil value is a PASS.  A signalled error is a FAIL, never a silent
pass; the error is printed so the cause is visible."
  (m48-imp2--check
   (format "probe/%s" tag)
   (condition-case err
       (and (funcall thunk) t)
     (error (princ (format "INFO m48/imp2/%s error=%S\n" tag err))
            nil))))

(if (not (file-exists-p (expand-file-name "src/emacs" m48-imp2--root)))
    (princ "INFO m48/imp2/runtime-probes skipped (no built src/emacs)\n")
  (progn
    (m48-imp2--probe "display-color-p"
                     (lambda () (--term-display-color-p 8)))
    (m48-imp2--probe "display-color-cells"
                     (lambda () (eql 8 (--term-display-color-cells 8))))
    (m48-imp2--probe "term-type"
                     (lambda () (equal "xterm" (--term-type "xterm"))))))

(princ (format "=== m48 imp-2 leaves suite done (%d tracked checks; e1 %d, e2 %d, e3 %d, e4 %d) ===\n"
               m48-imp2--registered
               (m48-imp2--group-count 'e1)
               (m48-imp2--group-count 'e2)
               (m48-imp2--group-count 'e3)
               (m48-imp2--group-count 'e4)))
