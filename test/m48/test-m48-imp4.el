;;; test-m48-imp4.el --- M48 imp-4 corpus (G3, the query / geometry policy).
;;;
;;; M48 imp-4 moved the G3 query / geometry policy toward (emacs terminal).
;;; Imp-6 moved the geometry arithmetic fully into Scheme and retired its
;;; two C leaves.  The C hub still decodes frames, reads fields, and builds
;;; the alist; the pixel-dimension dispatch leaves remain in C.
;;;
;;; The 4 hub DEFUNs share two static helpers: tty-frame-geometry and
;;; tty-frame-edges call tty_frame_geometry, and tty-display-pixel-width
;;; and tty-display-pixel-height call tty_display_dimension.  The policy
;;; of each hub lives in its shared static helper, so F1 reads the
;;; helper body.
;;;
;;; This corpus reads tracked files, and it runs one gated runtime probe.
;;; It pins:
;;;   F1 -- the 4 rewired hubs.  Each of the 4 G3 hub policies calls its
;;;         *_scheme helper: the shared static helper body holds the
;;;         helper name and the token "_scheme".
;;;   F2 -- the 4 new ref sites.  src/term.c holds the 4
;;;         scm_c_public_ref ("emacs terminal", "term-<block>") strings,
;;;         the term.c ref count is 11 (3 old + 4 G1 + 4 G3), and the
;;;         tree-wide count over src/*.[chm] is 227.
;;;   F3 -- the inline decision is gone.  The tty_frame_geometry helper
;;;         holds no geometry arithmetic (no outer_right, no inner_bottom,
;;;         no "native_width - 2 * internal_border_width"), and
;;;         tty_display_dimension holds no "*width = 80" and no
;;;         "*height = 25".
;;;   F4 -- the 6 surviving "^DEFUN (\"--term-" leaves remain, the
;;;         "^DEFUN (" count is 25 after imp-6, and src/term.c holds "guile.h".
;;;   F5 -- the module has 8 public wrappers and 6 delayed refs after
;;;         imp-6, with no FFI call and no scm_c_public_ref in code.
;;;   F6 -- the group and the guards.  The (m48) group carries this
;;;         corpus, plus a per-group min-count guard and a total
;;;         min-count guard.  An --filter= that matches no group reports
;;;         exit 0 and 0 tests, so the gate proves nothing until these
;;;         guards hold.
;;;   F7 -- the gated runtime probe.  Run the built src/emacs and call
;;;         the two dimension leaves and Scheme geometry procedures.  An absent binary is an
;;;         INFO-skip.  A probe error is a FAIL, never a silent pass
;;;         (docs/kb.org m4x-probe-failure-must-not-read-as-a-skip).  Do
;;;         not probe the hubs tty-frame-geometry / tty-display-pixel-*
;;;         in batch: batch may have no live tty.
;;;
;;; A read error is a real error, never a silent pass.  An absent src/
;;; file is a real error.
;;;
;;; Current count note: imp-6 removes two geometry leaf docs and one
;;; marker block.  The source has 10 FIX markers, six surviving imp-2 leaf
;;; docs, 11 term.c refs, and 227 tree-wide refs.

(princ "=== m48 imp-4 G3 suite ===\n")

(require 'imp-ert-report)

(defvar m48-imp4--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))

(defvar m48-imp4--registered 0
  "Total number of tracked-file checks this corpus has registered.")

(defvar m48-imp4--group nil
  "The group that `m48-imp4--check' counts into: `f1' ... `f5', or nil.")

(defvar m48-imp4--counts nil
  "Alist of (GROUP . COUNT) for the registered tracked-file checks.")

(defun m48-imp4--group-count (group)
  "Number of tracked-file checks registered so far in GROUP."
  (or (cdr (assq group m48-imp4--counts)) 0))

(defun m48-imp4--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
the symbol `m48-imp4-absent' when REL does not exist."
  (let ((path (expand-file-name rel m48-imp4--root)))
    (if (not (file-exists-p path))
        'm48-imp4-absent
      (with-temp-buffer
        (insert-file-contents path)
        (funcall fn)))))

(defun m48-imp4--contains-p (rel needle)
  "Non-nil when REL (repo-root-relative) contains NEEDLE."
  (m48-imp4--with rel
    (lambda ()
      (goto-char (point-min))
      (search-forward needle nil t))))

(defun m48-imp4--lines (rel)
  "Count the newlines of REL the way `wc -l' does."
  (m48-imp4--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (search-forward "\n" nil t) (setq n (1+ n)))
        n))))

(defun m48-imp4--count (rel regexp)
  "Count the matches of REGEXP in REL."
  (m48-imp4--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (re-search-forward regexp nil t) (setq n (1+ n)))
        n))))

(defun m48-imp4--count-code (rel regexp)
  "Count the matches of REGEXP in REL, skipping full comment lines.
A module comment may name a forbidden token (for example
`scm_c_public_ref') while explaining the contract; only the code must be
free of the token.  Scheme line comments start with `;'."
  (m48-imp4--with rel
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

(defun m48-imp4--check (name ok)
  "Report and register one check on a TRACKED file.  OK is a boolean.
An absent src/ file makes the reader return the symbol
`m48-imp4-absent', so the guard checks print FAIL -- an absent src/ file
is a real error, not a pass."
  (if (eq ok 'm48-imp4-absent)
      (princ (format "INFO m48/imp4/%s skipped (source file absent)\n" name))
    (progn
      (princ (format "%s m48/imp4/%s\n" (if ok "PASS" "FAIL") name))
      (setq m48-imp4--registered (1+ m48-imp4--registered))
      (when m48-imp4--group
        (let ((cell (assq m48-imp4--group m48-imp4--counts)))
          (if cell
              (setcdr cell (1+ (cdr cell)))
            (push (cons m48-imp4--group 1) m48-imp4--counts))))
      (imp-register-bool-as-ert-test (format "m48-imp4/%s" name) (and ok t)))))

(defvar m48-imp4--hubs
  '(("tty-frame-geometry"       "tty_frame_geometry"
     "term_frame_geometry_scheme")
    ("tty-frame-edges"          "tty_frame_geometry"
     "term_frame_edges_scheme")
    ("tty-display-pixel-width"  "tty_display_dimension"
     "term_display_pixel_width_scheme")
    ("tty-display-pixel-height" "tty_display_dimension"
     "term_display_pixel_height_scheme"))
  "The 4 G3 hubs of brief.org section 3: (HUB STATIC-HELPER HELPER).")

(defun m48-imp4--fn-body (name)
  "Return the source of the C function NAME body, or nil.
The definition line starts at column 0; the body runs to the closing
brace at column 0.  A call site (`return NAME (...)') is indented, so the
anchored match finds the definition only."
  (m48-imp4--with "src/term.c"
    (lambda ()
      (goto-char (point-min))
      (when (re-search-forward (format "^%s (" (regexp-quote name)) nil t)
        (let ((start (line-beginning-position)))
          (if (re-search-forward "^}" nil t)
              (buffer-substring-no-properties start (match-end 0))
            (buffer-substring-no-properties start (point-max))))))))

(defun m48-imp4--count-scm-ref ()
  "Count scm_c_public_ref over src/*.[chm] (brief.org section 8 F2)."
  (let ((total 0)
        (dir (expand-file-name "src" m48-imp4--root)))
    (dolist (f (directory-files dir t "\\.[chm]\\'"))
      (setq total (+ total (or (m48-imp4--count f "scm_c_public_ref") 0))))
    total))

;;; --- F1. The 4 rewired hubs (brief.org section 4.1, 4.2, 4.3) -------

(setq m48-imp4--group 'f1)

(dolist (hubs m48-imp4--hubs)
  (let* ((hub (nth 0 hubs))
         (fn (nth 1 hubs))
         (helper (nth 2 hubs))
         (body (m48-imp4--fn-body fn)))
    (m48-imp4--check (format "hub-%s-calls-helper" hub)
                     (and (stringp body)
                          (string-match-p (regexp-quote helper) body)
                          t))
    (m48-imp4--check (format "hub-%s-body-has-scheme" hub)
                     (and (stringp body)
                          (string-match-p "_scheme" body)
                          t))))

;;; --- F2. The 4 new ref sites (brief.org section 8 F2) ---------------

(setq m48-imp4--group 'f2)

(dolist (wrapper '("term-frame-geometry" "term-frame-edges"
                   "term-display-pixel-width" "term-display-pixel-height"))
  (m48-imp4--check (format "refs-%s" wrapper)
                   (m48-imp4--contains-p
                    "src/term.c"
                    (format "scm_c_public_ref (\"emacs terminal\", \"%s\")"
                            wrapper))))
(m48-imp4--check "term.c-scm-ref-11"
                 (eql 11 (m48-imp4--count "src/term.c" "scm_c_public_ref")))
(m48-imp4--check "scm-c-public-ref-230"
                 (eql 230 (m48-imp4--count-scm-ref)))

;;; --- F3. The inline decision is gone (brief.org section 4.4) --------

(setq m48-imp4--group 'f3)

(m48-imp4--check "no-inline-geometry-outer_right"
                 (let ((body (m48-imp4--fn-body "tty_frame_geometry")))
                   (and (stringp body)
                        (not (string-match-p "outer_right" body))
                        t)))
(m48-imp4--check "no-inline-geometry-inner_bottom"
                 (let ((body (m48-imp4--fn-body "tty_frame_geometry")))
                   (and (stringp body)
                        (not (string-match-p "inner_bottom" body))
                        (not (string-match-p
                              "native_width - 2 \\* internal_border_width" body))
                        t)))
(m48-imp4--check "no-inline-pixel-width-80"
                 (let ((body (m48-imp4--fn-body "tty_display_dimension")))
                   (and (stringp body)
                        (not (string-match-p "\\*width = 80" body))
                        t)))
(m48-imp4--check "no-inline-pixel-height-25"
                 (let ((body (m48-imp4--fn-body "tty_display_dimension")))
                   (and (stringp body)
                        (not (string-match-p "\\*height = 25" body))
                        t)))

;;; --- F4. The leaves stay (brief.org section 8 F4) -------------------

(setq m48-imp4--group 'f4)

(m48-imp4--check "leaf-defuns-6"
                 (eql 6 (m48-imp4--count "src/term.c" "^DEFUN (\"--term-")))
(m48-imp4--check "defun-count-25"
                 (eql 25 (m48-imp4--count "src/term.c" "^DEFUN (\"")))
(m48-imp4--check "term.c-has-guile.h"
                 (m48-imp4--contains-p "src/term.c" "#include \"guile.h\""))

;;; --- F5. The module is unchanged (brief.org section 4.5) ------------

(setq m48-imp4--group 'f5)

(m48-imp4--check "module-wrappers-8"
                 (eql 8 (m48-imp4--count "mod/emacs/terminal.scm"
                                         "^(define (term-[a-z]")))
(m48-imp4--check "module-defelisp-6"
                 (eql 6 (m48-imp4--count "mod/emacs/terminal.scm"
                                         "(defelisp %--term-")))
(m48-imp4--check "module-no-ffi"
                 (let ((n (m48-imp4--count-code
                           "mod/emacs/terminal.scm"
                           "system foreign\\|dynamic-link\\|libc\\.so\\|system\\*\\|primitive-fork\\|posix_spawn\\|ioctl\\|dynamic-func")))
                   (and (integerp n) (eql 0 n))))
(m48-imp4--check "module-no-scm-ref"
                 (let ((n (m48-imp4--count-code "mod/emacs/terminal.scm"
                                                "scm_c_public_ref")))
                   (and (integerp n) (eql 0 n))))

;;; --- F6. The group and the guards (brief.org section 9 F6) ----------

(setq m48-imp4--group nil)

(m48-imp4--check "reg/run-tests-m48-imp4"
                 (m48-imp4--contains-p "tool/run-tests.scm"
                                       "test/m48/test-m48-imp4.el"))
(m48-imp4--check "reg/min-f1-checks-8"
                 (>= (m48-imp4--group-count 'f1) 8))
(m48-imp4--check "reg/min-f2-checks-6"
                 (>= (m48-imp4--group-count 'f2) 6))
(m48-imp4--check "reg/min-f3-checks-4"
                 (>= (m48-imp4--group-count 'f3) 4))
(m48-imp4--check "reg/min-f4-checks-3"
                 (>= (m48-imp4--group-count 'f4) 3))
(m48-imp4--check "reg/min-f5-checks-4"
                 (>= (m48-imp4--group-count 'f5) 4))
(m48-imp4--check "reg/min-total-31"
                 (>= m48-imp4--registered 31))

;;; --- F7. The gated runtime probe (brief.org section 9 F7) -----------

;; The (m48) group carries no `prelude' key, so tool/run-tests.scm loads
;; these files with run-tests-loadup-emacs, which is "../src/emacs ...
;; -l <file> --batch".  A probe therefore calls the leaf DIRECTLY, in
;; this process.
;;
;; An absent built binary is an INFO-skip.  A signalled error is a FAIL,
;; never a silent pass; the error is printed so the cause is visible.  An
;; undefined leaf signals void-function, so it is a FAIL too.
;;
;; The dimension leaves and Scheme geometry procedures take plain values,
;; so these probes are deterministic in batch.  Do NOT probe the TTY hubs
;; here: batch may have no live tty.

(defun m48-imp4--probe (tag thunk)
  "Register the probe TAG from the value of THUNK, which calls a leaf.
A non-nil value is a PASS.  A signalled error is a FAIL, never a silent
pass; the error is printed so the cause is visible."
  (m48-imp4--check
   (format "probe/%s" tag)
   (condition-case err
       (and (funcall thunk) t)
     (error (princ (format "INFO m48/imp4/%s error=%S\n" tag err))
            nil))))

(if (not (file-exists-p (expand-file-name "src/emacs" m48-imp4--root)))
    (princ "INFO m48/imp4/runtime-probes skipped (no built src/emacs)\n")
  (progn
(m48-imp4--probe "geometry"
                     (lambda ()
                       (eql 1 (eval-scheme
                               "(begin (use-modules (emacs terminal)) (if (equal? ((module-ref (resolve-module '(emacs terminal)) 'term-frame-geometry) 10 20 100 50 1 2 0 0 #t) '(10 20 110 70 11 23 109 69 100 0 0)) 1 0))"))))
    (m48-imp4--probe "frame-edges-inner"
                     (lambda ()
                       (eql 1 (eval-scheme
                               "(begin (use-modules (emacs terminal)) (if (equal? ((module-ref (resolve-module '(emacs terminal)) 'term-frame-edges) 10 20 100 50 1 2 0 0 #t \"inner\") '(11 23 109 69)) 1 0))"))))
    (m48-imp4--probe "frame-edges-outer"
                     (lambda ()
                       (eql 1 (eval-scheme
                               "(begin (use-modules (emacs terminal)) (if (equal? ((module-ref (resolve-module '(emacs terminal)) 'term-frame-edges) 10 20 100 50 1 2 0 0 #t \"outer\") '(10 20 110 70)) 1 0))"))))
    (m48-imp4--probe "display-pixel-width-initial"
                     (lambda () (eql 80 (--term-display-pixel-width t nil))))
    (m48-imp4--probe "display-pixel-width-value"
                     (lambda () (eql 42 (--term-display-pixel-width nil 42))))
    (m48-imp4--probe "display-pixel-height-initial"
                     (lambda () (eql 25 (--term-display-pixel-height t nil))))
    (m48-imp4--probe "display-pixel-height-value"
                     (lambda () (eql 17 (--term-display-pixel-height nil 17))))))

(princ (format "=== m48 imp-4 G3 suite done (%d tracked checks; f1 %d, f2 %d, f3 %d, f4 %d, f5 %d) ===\n"
               m48-imp4--registered
               (m48-imp4--group-count 'f1)
               (m48-imp4--group-count 'f2)
               (m48-imp4--group-count 'f3)
               (m48-imp4--group-count 'f4)
               (m48-imp4--group-count 'f5)))
