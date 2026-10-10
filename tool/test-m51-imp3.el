;;; test-m51-imp3.el --- M51 imp-3 audit corpus (the image file hop caller / ownership audit).
;;;
;;; M51 imp-3 is the audit-and-contract step (brief.org sections 4 to 7).
;;; It moves no handle: the net C delta is 0 and the net Scheme delta is
;;; 0.  It audits every image open / read / close path in src/image.c,
;;; confirms the `pfd == NULL' case, and defines the handle contract that
;;; imp-4 implements.
;;;
;;; This corpus reads TRACKED files only (src/image.c, src/lread.c,
;;; tool/run-tests.scm).  It has no C dependency.  A test does not read
;;; docs/: a docs needle is not a behaviour, and docs/ is gitignored, so
;;; such a check can never fail on a fresh clone.  The docs needles live
;;; in tool/m51-plan-lint.sh, which the (m51) group does not run.  This
;;; corpus pins:
;;;   D1 -- the four hop functions exist with their exact names and a
;;;         stable signature anchor: image_find_image_fd,
;;;         image_find_image_file, slurp_file, slurp_image.  It pins the
;;;         NAME and the signature, not a line number.  4 checks.
;;;   D2 -- the loader call map as an ORDERED CALLER-NAME LIST: the
;;;         openp sites, the direct emacs_open sites, the emacs_fdopen
;;;         sites, the slurp_image callers, the slurp_file callers, the
;;;         image_find_image_fd callers, and the image_find_image_file
;;;         callers, each by the enclosing function name.  7 checks.
;;;   D3 -- the C delta: src/image.c holds no new `--image-*' leaf, its
;;;         scm_c_public_ref count is 5 (M51 imp-5 adds the Open-Stream,
;;;         Handle-Read, and Close bridges), and the tree-wide count over
;;;         src/*.[chm] is 250.  This corpus is the imp-3 audit, re-pinned
;;;         after M51 imp-5.  Plus the imp-5 line count and the unchanged
;;;         DEFUN count.  5 checks.
;;;   D6 -- the `pfd == NULL' case.  The audit confirms that openp
;;;         cannot return -2 in the no-handle mode: image_find_image_fd
;;;         passes a fixnum predicate then, and openp returns -2 only
;;;         under a non-fixnum predicate.  So the -2 branch opens no
;;;         unused descriptor.  Pinned by source needles in src/image.c
;;;         and src/lread.c.  4 checks.
;;;   D5 -- the (m51) group registration and the per-group min-count
;;;         guard.  The corpus registers after test-m51-imp1.el.  9
;;;         checks.
;;;
;;; Each check is printed as a PASS/FAIL line and turned into an ERT
;;; test so the harness counts it.  A read error is a real error, never
;;; a silent pass.  The corpus holds its own copy of every fact it pins.

(princ "=== m51 imp-3 audit suite ===\n")

(require 'imp-ert-report)

(defvar m51-imp3--root
  (file-name-as-directory
   (expand-file-name ".." (file-name-directory (or load-file-name
                                                       default-directory)))))
(defvar m51-imp3--registered 0
  "Total number of tracked-file checks this corpus has registered.")
(defvar m51-imp3--group nil
  "The group that `m51-imp3--check' counts into: `d1', `d2', `d3',
`d6', or nil.")
(defvar m51-imp3--registered-d1 0)
(defvar m51-imp3--registered-d2 0)
(defvar m51-imp3--registered-d3 0)
(defvar m51-imp3--registered-d6 0)

(defun m51-imp3--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
the symbol `m51-imp3-absent' when REL does not exist."
  (let ((path (expand-file-name rel m51-imp3--root)))
    (if (not (file-exists-p path))
        'm51-imp3-absent
      (with-temp-buffer
        (insert-file-contents path)
        (funcall fn)))))

(defun m51-imp3--tracked-p (rel needle)
  "Non-nil when the TRACKED file REL contains NEEDLE."
  (let ((hit (m51-imp3--with rel
               (lambda ()
                 (goto-char (point-min))
                 (search-forward needle nil t)))))
    (and (not (eq hit 'm51-imp3-absent)) (and hit t))))

(defun m51-imp3--exists-p (rel)
  "Non-nil when REL (repo-root-relative) exists as a file."
  (file-exists-p (expand-file-name rel m51-imp3--root)))

(defun m51-imp3--lines (rel)
  "Count the newlines of REL the way `wc -l' does."
  (m51-imp3--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (search-forward "\n" nil t) (setq n (1+ n)))
        n))))

(defun m51-imp3--count (rel regexp)
  "Count the matches of REGEXP in REL."
  (m51-imp3--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (re-search-forward regexp nil t) (setq n (1+ n)))
        n))))

(defun m51-imp3--count-literal (rel needle)
  "Count the matches of the LITERAL NEEDLE in REL."
  (m51-imp3--count rel (regexp-quote needle)))

(defun m51-imp3--defun-count (rel)
  "Count the `^DEFUN (' lines of REL."
  (m51-imp3--count rel (concat "^" (regexp-quote "DEFUN (\""))))

(defun m51-imp3--line-of (rel needle)
  "1-based line number of the first LITERAL NEEDLE in REL, or nil."
  (m51-imp3--with rel
    (lambda ()
      (goto-char (point-min))
      (when (search-forward needle nil t)
        (line-number-at-pos (match-beginning 0))))))

(defun m51-imp3--enclosing-fn ()
  "Name of the top-level C function that encloses point, or nil.
Scan back to the nearest line that starts at column 0, is not a
preprocessor or comment line, and looks like a function header.  A
forward declaration (`static char *slurp_file (image_fd, ptrdiff_t *);')
has no `(' right after the first token, so it is skipped."
  (let (name)
    (save-excursion
      (while (and (not name) (not (bobp)))
        (beginning-of-line)
        (let ((line (buffer-substring-no-properties (line-beginning-position)
                                                    (line-end-position))))
          (when (and (> (length line) 0)
                     (not (memq (aref line 0) '(?\s ?\t ?# ?/ ?*)))
                     (string-match "\\`\\([A-Za-z_][A-Za-z0-9_]*\\)[ \t]*(" line)
                     (not (string-suffix-p ";" line)))
            (setq name (match-string 1 line))))
        (unless name (forward-line -1))))
    name))

(defun m51-imp3--callers (rel callee)
  "Ordered list of enclosing function names of the CALLEE call sites
in REL.  A call site is a match of `CALLEE (' that is not the function
definition itself and not a column-0 forward declaration."
  (m51-imp3--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((needle (concat callee " ("))
            (acc '()))
        (while (search-forward needle nil t)
          (let* ((mb (match-beginning 0))
                 (bol (save-excursion (goto-char mb) (line-beginning-position)))
                 (eol (save-excursion (goto-char mb) (line-end-position)))
                 (line (buffer-substring-no-properties bol eol))
                 (decl (and (> (length line) 0)
                            (not (memq (aref line 0) '(?\s ?\t)))
                            (string-suffix-p ";" line)))
                 (fn (save-excursion (goto-char mb) (m51-imp3--enclosing-fn))))
            (unless (or decl (equal fn callee))
              (push fn acc))))
        (nreverse acc)))))

(defun m51-imp3--count-scm-ref ()
  "Count scm_c_public_ref over src/*.[chm]."
  (let ((total 0)
        (dir (expand-file-name "src" m51-imp3--root)))
    (dolist (f (directory-files dir t "\\.[chm]\\'"))
      (setq total (+ total (or (m51-imp3--count-literal f "scm_c_public_ref") 0))))
    total))

(defun m51-imp3--check (name ok)
  "Report and register one check on a TRACKED file.  OK is a boolean."
  (if (eq ok 'm51-imp3-absent)
      (princ (format "INFO m51/imp3/%s skipped (source file absent)\n" name))
    (progn
      (princ (format "%s m51/imp3/%s\n" (if ok "PASS" "FAIL") name))
      (setq m51-imp3--registered (1+ m51-imp3--registered))
      (cond ((eq m51-imp3--group 'd1)
             (setq m51-imp3--registered-d1 (1+ m51-imp3--registered-d1)))
            ((eq m51-imp3--group 'd2)
             (setq m51-imp3--registered-d2 (1+ m51-imp3--registered-d2)))
            ((eq m51-imp3--group 'd3)
             (setq m51-imp3--registered-d3 (1+ m51-imp3--registered-d3)))
            ((eq m51-imp3--group 'd6)
             (setq m51-imp3--registered-d6 (1+ m51-imp3--registered-d6))))
      (imp-register-bool-as-ert-test (format "m51-imp3/%s" name) (and ok t)))))

;;; --- D1. The four hop functions (brief.org section 4) -----------------
;;
;; Pin the exact name AND a stable signature anchor.  A line number
;; would invalidate itself at the next imp: imp-4 adds the Scheme
;; bridge, which moves every line below its include.

(setq m51-imp3--group 'd1)

(m51-imp3--check "hop/find-image-fd"
                 (m51-imp3--tracked-p "src/image.c"
                                      "image_find_image_fd (Lisp_Object file, image_fd *pfd)"))
(m51-imp3--check "hop/find-image-file"
                 (m51-imp3--tracked-p "src/image.c"
                                      "image_find_image_file (Lisp_Object file)"))
(m51-imp3--check "hop/slurp-file"
                 (m51-imp3--tracked-p "src/image.c"
                                      "slurp_file (image_fd fd, ptrdiff_t *size)"))
(m51-imp3--check "hop/slurp-image"
                 (m51-imp3--tracked-p "src/image.c"
                                      "slurp_image (Lisp_Object filename, ptrdiff_t *size, const char *image_type)"))

;;; --- D2. The loader call map (brief.org section 4, by function name) --

(setq m51-imp3--group 'd2)

;; The openp sites: the XBM bitmap loader searches x-bitmap-file-path (4
;; sites: the X11, Haiku, and Android bitmap paths) and the hop itself
;; resolves the image path (1 site).
(m51-imp3--check "map/openp-callers"
                 (equal '("image_create_bitmap_from_file"
                          "image_create_bitmap_from_file"
                          "image_create_bitmap_from_file"
                          "image_create_bitmap_from_file"
                          "image_find_image_fd")
                        (m51-imp3--callers "src/image.c" "openp")))

;; The direct emacs_open sites: only the -2 file-name-handler fallback
;; in the hop.  M51 imp-5 removes the PNG / JPEG / GIF sites: all three
;; now read through (emacs image).
(m51-imp3--check "map/emacs_open-callers"
                 (equal '("image_find_image_fd")
                        (m51-imp3--callers "src/image.c" "emacs_open")))

;; The emacs_fdopen sites: only slurp_file wraps an ordinary descriptor.
;; M51 imp-5 removes the PNG / JPEG sites: both now stream from the
;; Scheme-owned port.
(m51-imp3--check "map/emacs_fdopen-callers"
                 (equal '("slurp_file")
                        (m51-imp3--callers "src/image.c" "emacs_fdopen")))

;; The slurp_image callers: XBM, XPM, PBM, WebP.
(m51-imp3--check "map/slurp_image-callers"
                 (equal '("xbm_load" "xpm_load" "pbm_load" "webp_load")
                        (m51-imp3--callers "src/image.c" "slurp_image")))

;; The slurp_file callers: the XBM bitmap loader (5 sites).  M51 imp-4
;; removes the slurp_image and svg_load callers: both now read through
;; image_read_file_scheme, so slurp_file serves only the native platform
;; bitmap branches.
(m51-imp3--check "map/slurp_file-callers"
                 (equal '("image_create_bitmap_from_file"
                          "image_create_bitmap_from_file"
                          "image_create_bitmap_from_file"
                          "image_create_bitmap_from_file"
                          "image_create_bitmap_from_file")
                        (m51-imp3--callers "src/image.c" "slurp_file")))

;; The image_find_image_fd callers: the XBM bitmap loader (7 sites) and
;; the pfd == NULL wrapper image_find_image_file.  M51 imp-4 removes the
;; slurp_image and svg_load callers: both now resolve and read in Scheme.
(m51-imp3--check "map/find-image-fd-callers"
                 (equal '("image_create_bitmap_from_file"
                          "image_create_bitmap_from_file"
                          "image_create_bitmap_from_file"
                          "image_create_bitmap_from_file"
                          "image_create_bitmap_from_file"
                          "image_create_bitmap_from_file"
                          "image_create_bitmap_from_file"
                          "image_find_image_file")
                        (m51-imp3--callers "src/image.c" "image_find_image_fd")))

;; The image_find_image_file callers: only the filename-based paths that
;; STAY C -- the w32 GDI XPM loader and the native platform loader.  M51
;; imp-5 removes the PNG / JPEG / TIFF / GIF / ImageMagick sites: all
;; now resolve and read through (emacs image).
(m51-imp3--check "map/find-image-file-callers"
                 (equal '("xpm_load" "native_image_load")
                        (m51-imp3--callers "src/image.c" "image_find_image_file")))

;;; --- D3. The C delta (brief.org section 8) ----------------------------

(setq m51-imp3--group 'd3)

;; M51 imp-5 adds three scm_c_public_ref sites (image_open_stream_scheme,
;; image_handle_read_scheme, image_close_scheme), so the image.c count is
;; 5 and the tree-wide count is 250.  The DEFUN count and the --image-*
;; leaf count do not move.
(m51-imp3--check "c/no-image-leaf"
                 (eql 0 (m51-imp3--count-literal "src/image.c" "DEFUN (\"--image-")))
(m51-imp3--check "c/image-c-scm-ref-5"
                 (eql 5 (m51-imp3--count-literal "src/image.c" "scm_c_public_ref")))
(m51-imp3--check "c/tree-wide-scm-ref-250"
                 (eql 250 (m51-imp3--count-scm-ref)))
;; The imp-5 C surface: the line count moves with the three bridges and
;; the rewiring; the DEFUN count does not.
(m51-imp3--check "c/image-c-lines-13447"
                 (eql 13447 (m51-imp3--lines "src/image.c")))
(m51-imp3--check "c/image-c-defuns-11"
                 (eql 11 (m51-imp3--defun-count "src/image.c")))

;;; --- D6. The pfd == NULL case (brief.org section 6) -------------------
;;
;; The audit confirms that openp cannot return -2 in the no-handle mode.
;; image_find_image_fd passes `pfd ? Qt : make_fixnum (R_OK)': a FIXNUM
;; predicate when PFD is null.  openp returns -2 only when the predicate
;; is NOT a fixnum (the guard `&& !FIXNATP (predicate)').  So the
;; `if (fd == -2)' branch is not reached, and no unused descriptor is
;; opened.  imp-3 accounts for the case; no C guard lands.

(setq m51-imp3--group 'd6)

(m51-imp3--check "pfd/nohandle-predicate-is-fixnum"
                 (m51-imp3--tracked-p "src/image.c"
                                      "pfd ? Qt : make_fixnum (R_OK)"))
(m51-imp3--check "pfd/image-fd-minus2-branch"
                 (m51-imp3--tracked-p "src/image.c" "if (fd == -2)"))
(m51-imp3--check "pfd/openp-minus2-guard-nonfixnum"
                 (m51-imp3--tracked-p "src/lread.c" "!FIXNATP (predicate)"))
;; openp documents -2 for a remote file; the guard above is the reason it
;; cannot happen for a fixnum predicate.
(m51-imp3--check "pfd/openp-doc-minus2"
                 (m51-imp3--tracked-p "src/lread.c"
                                      "If the file we find is remote, return -2"))

;;; --- D5. The group registration and the min-count guard --------------

(setq m51-imp3--group nil)

(m51-imp3--check "reg/m51-imp4-registered"
                 (m51-imp3--tracked-p "tool/run-tests.scm"
                                      "test/m51/test-m51-imp4.el"))
(m51-imp3--check "reg/m51-group-name"
                 (m51-imp3--tracked-p "tool/run-tests.scm" "(group (m51)"))
(m51-imp3--check "reg/m51-group-after-m50"
                 (let ((m50 (m51-imp3--line-of "tool/run-tests.scm" "(group (m50)"))
                       (m51 (m51-imp3--line-of "tool/run-tests.scm" "(group (m51)")))
                   (and (integerp m50) (integerp m51) (< m50 m51))))
;; The current (m51) group carries the imp-4 corpus.  The imp-1 / imp-3
;; audits are now advisory (tool/), so the old imp-3-after-imp-1 order
;; no longer applies.
(m51-imp3--check "reg/m51-group-carries-imp4"
                 (let ((i4 (m51-imp3--line-of "tool/run-tests.scm"
                                              "test/m51/test-m51-imp4.el")))
                   (integerp i4)))
(m51-imp3--check "reg/absent-tracked-file-fails"
                 (null (m51-imp3--tracked-p "src/m51-imp3-no-such-file.c"
                                            "needle")))

;; Per-group minima: a truncated load cannot pass the gate.
(m51-imp3--check "reg/min-d1-checks-4" (>= m51-imp3--registered-d1 4))
(m51-imp3--check "reg/min-d2-checks-7" (>= m51-imp3--registered-d2 7))
(m51-imp3--check "reg/min-d3-checks-5" (>= m51-imp3--registered-d3 5))
(m51-imp3--check "reg/min-d6-checks-4" (>= m51-imp3--registered-d6 4))

(princ (format "=== m51 imp-3 audit suite done (%d tracked checks: D1 %d, D2 %d, D3 %d, D6 %d) ===\n"
               m51-imp3--registered m51-imp3--registered-d1 m51-imp3--registered-d2
               m51-imp3--registered-d3 m51-imp3--registered-d6))
