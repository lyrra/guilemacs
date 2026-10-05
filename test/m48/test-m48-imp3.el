;;; test-m48-imp3.el --- M48 imp-3 corpus (G1, the terminal-capability policy).
;;;
;;; M48 imp-3 moves the G1 terminal-capability policy of src/term.c to
;;; (emacs terminal) (brief.org section 2 and section 3).  It adds one
;;; static *_scheme dispatch helper per hub, rewires the 4 G1 hubs onto
;;; the imp-2 leaves, and deletes the inline decision.  The mechanism
;;; stays C.  imp-3 changes no Scheme.
;;;
;;; This corpus reads tracked files, and it runs one gated runtime probe.
;;; It pins:
;;;   F1 -- the 4 rewired hubs.  Each of the 4 G1 hub DEFUN bodies calls
;;;         its *_scheme helper.
;;;   F2 -- the 4 new ref sites.  src/term.c holds the 4
;;;         scm_c_public_ref ("emacs terminal", "term-<block>") strings,
;;;         the term.c ref count is 11 (3 old + 4 G1 + 4 G3), and the
;;;         tree-wide count over src/*.[chm] is 227.
;;;   F3 -- the inline decision is gone.  The tty-display-color-p and
;;;         tty-display-color-cells bodies no longer hold
;;;         "TN_max_colors > 0", and every TN_max_colors read in those
;;;         bodies sits inside make_fixnum.  The controlling-tty-p body
;;;         no longer holds strcmp.
;;;   F4 -- the leaves stay.  The 8 "^DEFUN (\"--term-" lines stay, the
;;;         "^DEFUN (" count stays 27, and src/term.c still holds
;;;         "guile.h".
;;;   F5 -- the module is unchanged.  mod/emacs/terminal.scm stays 194
;;;         lines, holds 8 wrappers, and holds no FFI call and no
;;;         scm_c_public_ref in code.
;;;   F6 -- the group and the guards.  The (m48) group carries this
;;;         corpus, plus a per-group min-count guard and a total
;;;         min-count guard.  An --filter= that matches no group reports
;;;         exit 0 and 0 tests, so the gate proves nothing until these
;;;         guards hold.
;;;   F7 -- the gated runtime probe.  Run the built src/emacs and call
;;;         the 4 leaves with plain values.  An absent binary is an
;;;         INFO-skip.  A probe error is a FAIL, never a silent pass
;;;         (docs/kb.org m4x-probe-failure-must-not-read-as-a-skip).  Do
;;;         not probe the hub tty-display-color-p in batch: batch may
;;;         have no live tty.
;;;
;;; A read error is a real error, never a silent pass.  An absent src/
;;; file is a real error.
;;;
;;; Count note: the 4 G1 dispatch helpers carry one FIX-20261005-guilemacs
;;; block comment.  That grows the src/term.c FIX-marker count from 9 to
;;; 10, so test-m48-imp2.el "doc-marker-9" is re-pinned to 10 in this
;;; commit (brief.org section 8).

(princ "=== m48 imp-3 G1 suite ===\n")

(require 'imp-ert-report)

(defvar m48-imp3--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))

(defvar m48-imp3--registered 0
  "Total number of tracked-file checks this corpus has registered.")

(defvar m48-imp3--group nil
  "The group that `m48-imp3--check' counts into: `f1' ... `f5', or nil.")

(defvar m48-imp3--counts nil
  "Alist of (GROUP . COUNT) for the registered tracked-file checks.")

(defun m48-imp3--group-count (group)
  "Number of tracked-file checks registered so far in GROUP."
  (or (cdr (assq group m48-imp3--counts)) 0))

(defun m48-imp3--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
the symbol `m48-imp3-absent' when REL does not exist."
  (let ((path (expand-file-name rel m48-imp3--root)))
    (if (not (file-exists-p path))
        'm48-imp3-absent
      (with-temp-buffer
        (insert-file-contents path)
        (funcall fn)))))

(defun m48-imp3--contains-p (rel needle)
  "Non-nil when REL (repo-root-relative) contains NEEDLE."
  (m48-imp3--with rel
    (lambda ()
      (goto-char (point-min))
      (search-forward needle nil t))))

(defun m48-imp3--lines (rel)
  "Count the newlines of REL the way `wc -l' does."
  (m48-imp3--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (search-forward "\n" nil t) (setq n (1+ n)))
        n))))

(defun m48-imp3--count (rel regexp)
  "Count the matches of REGEXP in REL."
  (m48-imp3--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (re-search-forward regexp nil t) (setq n (1+ n)))
        n))))

(defun m48-imp3--count-code (rel regexp)
  "Count the matches of REGEXP in REL, skipping full comment lines.
A module comment may name a forbidden token (for example
`scm_c_public_ref') while explaining the contract; only the code must be
free of the token.  Scheme line comments start with `;'."
  (m48-imp3--with rel
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

(defun m48-imp3--check (name ok)
  "Report and register one check on a TRACKED file.  OK is a boolean.
An absent src/ file makes the reader return the symbol
`m48-imp3-absent', so the guard checks print FAIL -- an absent src/ file
is a real error, not a pass."
  (if (eq ok 'm48-imp3-absent)
      (princ (format "INFO m48/imp3/%s skipped (source file absent)\n" name))
    (progn
      (princ (format "%s m48/imp3/%s\n" (if ok "PASS" "FAIL") name))
      (setq m48-imp3--registered (1+ m48-imp3--registered))
      (when m48-imp3--group
        (let ((cell (assq m48-imp3--group m48-imp3--counts)))
          (if cell
              (setcdr cell (1+ (cdr cell)))
            (push (cons m48-imp3--group 1) m48-imp3--counts))))
      (imp-register-bool-as-ert-test (format "m48-imp3/%s" name) (and ok t)))))

(defvar m48-imp3--hubs
  '(("tty-display-color-p"     "tty_display_color_p_scheme"
     "term-display-color-p")
    ("tty-display-color-cells" "tty_display_color_cells_scheme"
     "term-display-color-cells")
    ("tty-type"                "term_type_scheme"
     "term-type")
    ("controlling-tty-p"       "controlling_tty_p_scheme"
     "term-controlling-tty-p"))
  "The 4 G1 hubs of brief.org section 2: (HUB HELPER WRAPPER).")

(defun m48-imp3--hub-body (hub)
  "Return the source of the DEFUN (\"HUB\") body, or nil.
The body runs to the closing brace at column 0.  It must NOT run to the
next DEFUN: between tty-display-color-cells and tty-type sit the C
mechanism helpers, whose TN_max_colors reads are not the hub policy."
  (m48-imp3--with "src/term.c"
    (lambda ()
      (goto-char (point-min))
      (when (search-forward (format "DEFUN (\"%s\"" hub) nil t)
        (let ((start (line-beginning-position)))
          (if (re-search-forward "^}" nil t)
              (buffer-substring-no-properties start (match-end 0))
            (buffer-substring-no-properties start (point-max))))))))

(defun m48-imp3--count-scm-ref ()
  "Count scm_c_public_ref over src/*.[chm] (brief.org section 7 F2)."
  (let ((total 0)
        (dir (expand-file-name "src" m48-imp3--root)))
    (dolist (f (directory-files dir t "\\.[chm]\\'"))
      (setq total (+ total (or (m48-imp3--count f "scm_c_public_ref") 0))))
    total))

;;; --- F1. The 4 rewired hubs (brief.org section 3.2) -----------------

(setq m48-imp3--group 'f1)

(dolist (hubs m48-imp3--hubs)
  (let* ((hub (nth 0 hubs))
         (helper (nth 1 hubs))
         (body (m48-imp3--hub-body hub)))
    (m48-imp3--check (format "hub-%s-calls-helper" hub)
                     (and (stringp body)
                          (string-match-p (regexp-quote helper) body)
                          t))
    (m48-imp3--check (format "hub-%s-body-has-scheme" hub)
                     (and (stringp body)
                          (string-match-p "_scheme" body)
                          t))))

;;; --- F1b. No helper parameter shadows a file-scope global (cr.org M1).
;;; controlling_tty_p_scheme must take `dev', not `dev_tty': the name
;;; `dev_tty' is a file-scope global, and a parameter of the same name
;;; hides it (legal, but confusing).  The helper passes the plain value.

(m48-imp3--check "helper-controlling-tty-p-param-not-dev_tty"
                 (m48-imp3--with "src/term.c"
                   (lambda ()
                     (goto-char (point-min))
                     (when (re-search-forward
                            "^controlling_tty_p_scheme (Lisp_Object name,\\(.*\\)$"
                            nil t)
                       (let ((params (match-string 1)))
                         (and (not (string-match-p "dev_tty" params))
                              (string-match-p "Lisp_Object dev)" params)
                              t))))))

;;; --- F2. The 4 new ref sites (brief.org section 7 F2) ---------------

(setq m48-imp3--group 'f2)

(dolist (hubs m48-imp3--hubs)
  (let ((hub (nth 0 hubs))
        (wrapper (nth 2 hubs)))
    (m48-imp3--check (format "refs-%s" hub)
                     (m48-imp3--contains-p
                      "src/term.c"
                      (format "scm_c_public_ref (\"emacs terminal\", \"%s\")"
                              wrapper)))))
(m48-imp3--check "term.c-scm-ref-11"
                 (eql 11 (m48-imp3--count "src/term.c" "scm_c_public_ref")))
(m48-imp3--check "scm-c-public-ref-227"
                 (eql 227 (m48-imp3--count-scm-ref)))

;;; --- F3. The inline decision is gone (brief.org section 3.2) --------

(setq m48-imp3--group 'f3)

(defun m48-imp3--no-inline-color-p (hub)
  "Non-nil when the HUB body holds no \"TN_max_colors > 0\" decision."
  (let ((body (m48-imp3--hub-body hub)))
    (and (stringp body)
         (not (string-match-p "TN_max_colors[ \t]*>[ \t]*0" body))
         t)))

(defun m48-imp3--max-colors-in-fixnum-p (hub)
  "Non-nil when every TN_max_colors read in the HUB body sits on a line
that also holds make_fixnum."
  (let ((body (m48-imp3--hub-body hub)))
    (if (not (stringp body))
        nil
      (let ((ok t)
            (lines (split-string body "\n")))
        (dolist (line lines)
          (when (and (string-match-p "TN_max_colors" line)
                     (not (string-match-p "make_fixnum" line)))
            (setq ok nil)))
        ok))))

(m48-imp3--check "no-inline-tty-display-color-p"
                 (m48-imp3--no-inline-color-p "tty-display-color-p"))
(m48-imp3--check "no-inline-tty-display-color-cells"
                 (m48-imp3--no-inline-color-p "tty-display-color-cells"))
(m48-imp3--check "max-colors-in-fixnum-tty-display-color-p"
                 (m48-imp3--max-colors-in-fixnum-p "tty-display-color-p"))
(m48-imp3--check "max-colors-in-fixnum-tty-display-color-cells"
                 (m48-imp3--max-colors-in-fixnum-p "tty-display-color-cells"))
(m48-imp3--check "no-strcmp-controlling-tty-p"
                 (let ((body (m48-imp3--hub-body "controlling-tty-p")))
                   (and (stringp body)
                        (not (string-match-p "strcmp" body))
                        t)))

;;; --- F4. The leaves stay (brief.org section 7 F4) -------------------

(setq m48-imp3--group 'f4)

(m48-imp3--check "leaf-defuns-8"
                 (eql 8 (m48-imp3--count "src/term.c" "^DEFUN (\"--term-")))
(m48-imp3--check "defun-count-27"
                 (eql 27 (m48-imp3--count "src/term.c" "^DEFUN (\"")))
(m48-imp3--check "term.c-has-guile.h"
                 (m48-imp3--contains-p "src/term.c" "#include \"guile.h\""))

;;; --- F5. The module is unchanged (brief.org section 4) --------------

(setq m48-imp3--group 'f5)

(m48-imp3--check "module-lines-194"
                 (eql 194 (m48-imp3--lines "mod/emacs/terminal.scm")))
(m48-imp3--check "module-wrappers-8"
                 (eql 8 (m48-imp3--count "mod/emacs/terminal.scm"
                                         "^(define (term-")))
(m48-imp3--check "module-defelisp-8"
                 (eql 8 (m48-imp3--count "mod/emacs/terminal.scm"
                                         "(defelisp %--term-")))
(m48-imp3--check "module-no-ffi"
                 (let ((n (m48-imp3--count-code
                           "mod/emacs/terminal.scm"
                           "system foreign\\|dynamic-link\\|libc\\.so\\|system\\*\\|primitive-fork\\|posix_spawn\\|ioctl\\|dynamic-func")))
                   (and (integerp n) (eql 0 n))))
(m48-imp3--check "module-no-scm-ref"
                 (let ((n (m48-imp3--count-code "mod/emacs/terminal.scm"
                                                "scm_c_public_ref")))
                   (and (integerp n) (eql 0 n))))

;;; --- F6. The group and the guards (brief.org section 7 F6) ----------

(setq m48-imp3--group nil)

(m48-imp3--check "reg/run-tests-m48-imp3"
                 (m48-imp3--contains-p "tool/run-tests.scm"
                                       "test/m48/test-m48-imp3.el"))
(m48-imp3--check "reg/min-f1-checks-9"
                 (>= (m48-imp3--group-count 'f1) 9))
(m48-imp3--check "reg/min-f2-checks-6"
                 (>= (m48-imp3--group-count 'f2) 6))
(m48-imp3--check "reg/min-f3-checks-5"
                 (>= (m48-imp3--group-count 'f3) 5))
(m48-imp3--check "reg/min-f4-checks-3"
                 (>= (m48-imp3--group-count 'f4) 3))
(m48-imp3--check "reg/min-f5-checks-5"
                 (>= (m48-imp3--group-count 'f5) 5))
(m48-imp3--check "reg/min-total-33"
                 (>= m48-imp3--registered 33))

;;; --- F7. The gated runtime probe (brief.org section 7 F7) -----------

;; The (m48) group carries no `prelude' key, so tool/run-tests.scm loads
;; these files with run-tests-loadup-emacs, which is "../src/emacs ...
;; -l <file> --batch".  A probe therefore calls the leaf DIRECTLY, in
;; this process.
;;
;; An absent built binary is an INFO-skip.  A signalled error is a FAIL,
;; never a silent pass; the error is printed so the cause is visible.  An
;; undefined leaf signals void-function, so it is a FAIL too.
;;
;; The 4 G1 leaves take plain values, so the probe is deterministic in
;; batch.  Do NOT probe the hub tty-display-color-p here: batch may have
;; no live tty.

(defun m48-imp3--probe (tag thunk)
  "Register the probe TAG from the value of THUNK, which calls a leaf.
A non-nil value is a PASS.  A signalled error is a FAIL, never a silent
pass; the error is printed so the cause is visible."
  (m48-imp3--check
   (format "probe/%s" tag)
   (condition-case err
       (and (funcall thunk) t)
     (error (princ (format "INFO m48/imp3/%s error=%S\n" tag err))
            nil))))

(if (not (file-exists-p (expand-file-name "src/emacs" m48-imp3--root)))
    (princ "INFO m48/imp3/runtime-probes skipped (no built src/emacs)\n")
  (progn
    (m48-imp3--probe "display-color-p"
                     (lambda () (--term-display-color-p 8)))
    (m48-imp3--probe "display-color-cells"
                     (lambda () (eql 8 (--term-display-color-cells 8))))
    (m48-imp3--probe "term-type"
                     (lambda () (equal "xterm" (--term-type "xterm"))))
    (m48-imp3--probe "controlling-tty-p"
                     (lambda () (--term-controlling-tty-p "/dev/tty" "/dev/tty")))))

(princ (format "=== m48 imp-3 G1 suite done (%d tracked checks; f1 %d, f2 %d, f3 %d, f4 %d, f5 %d) ===\n"
               m48-imp3--registered
               (m48-imp3--group-count 'f1)
               (m48-imp3--group-count 'f2)
               (m48-imp3--group-count 'f3)
               (m48-imp3--group-count 'f4)
               (m48-imp3--group-count 'f5)))
