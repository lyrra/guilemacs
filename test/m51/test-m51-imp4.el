;;; test-m51-imp4.el --- M51 imp-4 image file handle behavior corpus.
;;;
;;; M51 imp-4 moves the image file HANDLE from C to Scheme.  Scheme
;;; resolves the image path, opens the file as a Guile port, reads the
;;; bytes, and closes the port (mod/emacs/image.scm).  C decodes the
;;; bytes over the C bridge image_read_file_scheme (src/image.c).
;;;
;;; This corpus tests OBSERVABLE Emacs behavior through the built
;;; src/emacs (docs/m51-plan.org "Test strategy").  A test that reads C
;;; or Scheme source tests source layout only; such checks live in
;;; tool/ (tool/m51-audit.sh runs the moved static audits, and
;;; tool/m51-plan-lint.sh holds the record needles).
;;;
;;; Two evidence groups:
;;;
;;;   hop    -- the Scheme handle hop itself, headless-safe.  It calls
;;;             (emacs image) through the elisp `eval-scheme' bridge in
;;;             the running src/emacs and checks the bytevector of a
;;;             real TRACKED image (etc/images/alt.pbm): the resolve,
;;;             the byte count against the file size, the first byte,
;;;             a missing-file miss, and an empty-file read.  This is
;;;             real evidence without a window system (review F2b).  It
;;;             always registers, so the group can never silently run 0
;;;             checks.
;;;   decode -- the full decode path (create-image / image-size).  A
;;;             decode needs a window-system frame (src/frame.c
;;;             check_window_system); a headless build reports "Window
;;;             system frame should be used", which is an explicit
;;;             environment INFO-skip.  This limit is recorded here, not
;;;             hidden (review F2b).
;;;
;;; Gate rules:
;;;   - Any signalled error that is NOT the missing-window-system error
;;;     is a FAIL, never a silent pass
;;;     (docs/kb.org m4x-probe-failure-must-not-read-as-a-skip).
;;;   - The min-count guards make an unexpectedly small run FAIL, so 0
;;;     executed checks cannot read green (review F2a).
;;;
;;; This corpus reads TRACKED files only (etc/images/).  It never reads
;;; docs/ (docs/kb.org test-must-not-read-docs).  Tailored probes use a
;;; writable scratch directory (docs/kb.org
;;; tmp-write-probe-needs-a-scratch-dir).

(princ "=== m51 imp-4 image file handle suite ===\n")

(require 'imp-ert-report)

(defvar m51-imp4--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))

(defvar m51-imp4--group nil
  "The group that `m51-imp4--check' counts into: `hop' / `decode', or nil.")

(defvar m51-imp4--counts nil
  "Alist of (GROUP . COUNT) for the registered behavior checks.")

(defun m51-imp4--group-count (group)
  "Number of behavior checks registered so far in GROUP."
  (or (cdr (assq group m51-imp4--counts)) 0))

(defun m51-imp4--check (name ok)
  "Report and register one behavior check.  OK is a boolean."
  (princ (format "%s m51/imp4/%s\n" (if ok "PASS" "FAIL") name))
  (when m51-imp4--group
    (let ((cell (assq m51-imp4--group m51-imp4--counts)))
      (if cell (setcdr cell (1+ (cdr cell)))
        (push (cons m51-imp4--group 1) m51-imp4--counts))))
  (imp-register-bool-as-ert-test (format "m51-imp4/%s" name) (and ok t)))

(defun m51-imp4--skip (name err)
  "Report an environment INFO-skip for probe NAME, with reason ERR."
  (princ (format "INFO m51/imp4/%s skipped (no window system: %s)\n"
                 name (error-message-string err))))

(defun m51-imp4--ws-error-p (err)
  "Non-nil when ERR is the missing-window-system error of image-size."
  (string-match-p "Window system frame"
                  (error-message-string err)))

(defun m51-imp4--tmpdir (body)
  "Call BODY with a fresh scratch directory, then delete it."
  (let ((dir (file-name-as-directory (make-temp-file "m51-imp4" t))))
    (unwind-protect (funcall body dir) (delete-directory dir t))))

;;; --- The Scheme hop probes (headless-safe) ----------------------------
;;
;; Call (emacs image) through the elisp `eval-scheme' bridge.  Each probe
;; returns a plain integer (or string) so the elisp side compares it with
;; `eql' / `equal'; a Scheme #f would cross as an opaque foreign object
;; and must not be read as elisp nil.

(defun m51-imp4--scheme (form)
  "Evaluate the Scheme string FORM in the running src/emacs and return
its value.  `eval-scheme' is the elisp bridge to `eval-string'."
  (eval-scheme form))

(defun m51-imp4--scheme-ref (proc)
  "Scheme text that resolves (emacs image) PROC to a local binding."
  (format "(module-ref (resolve-module '(emacs image)) '%s)" proc))

(defun m51-imp4--probe-hop (name thunk)
  "Probe hop NAME.  THUNK runs a Scheme form through `eval-scheme' and
yields the integer result.  A signalled error is a FAIL, never a silent
pass; the error is printed so the cause is visible."
  (m51-imp4--check
   name
   (condition-case err
       (funcall thunk)
     (error (princ (format "INFO m51/imp4/%s error=%S\n" name err))
            nil))))

(setq m51-imp4--group 'hop)

(let* ((img (expand-file-name "etc/images/alt.pbm" m51-imp4--root))
       (resolver (m51-imp4--scheme-ref "image-resolve-path"))
       (reader (m51-imp4--scheme-ref "image-read-file"))
       (size (nth 7 (file-attributes img))))
  ;; 1. Resolve: image-resolve-path of a tracked image yields a string.
  (m51-imp4--probe-hop
   "hop/resolve-string"
   (lambda ()
     (eql 1 (m51-imp4--scheme
             (format "(let ((f %s)) (if (string? (f %S)) 1 0))"
                     resolver img)))))
  ;; 2. Read: the bytevector length equals the file size on disk.
  (m51-imp4--probe-hop
   "hop/read-length-matches-size"
   (lambda ()
     (eql size (m51-imp4--scheme
                (format "(let ((f %s)) (let ((bv (f %S))) (if bv (bytevector-length bv) -1)))"
                        reader img)))))
  ;; 3. Read: the first byte is the PBM magic `P'.
  (m51-imp4--probe-hop
   "hop/read-first-byte-magic"
   (lambda ()
     (eql ?P (m51-imp4--scheme
              (format "(let ((f %s)) (let ((bv (f %S))) (if bv (bytevector-u8-ref bv 0) -1)))"
                      reader img)))))
  ;; 4. Miss: a missing file yields #f from image-read-file.
  (m51-imp4--probe-hop
   "hop/missing-file-nil"
   (lambda ()
     (eql 0 (m51-imp4--scheme
             (format "(let ((f %s)) (if (f %S) 1 0))"
                     reader
                     (expand-file-name "etc/images/m51-imp4-nope.pbm"
                                       m51-imp4--root))))))
  ;; 5. Empty file: the read yields a 0-length bytevector, not a miss
  ;;    (restores the old slurp_file 0-size buffer; review F7).
  (m51-imp4--probe-hop
   "hop/empty-file-zero-length"
   (lambda ()
     (m51-imp4--tmpdir
      (lambda (dir)
        (let ((empty (expand-file-name "empty.pbm" dir)))
          (write-region "" nil empty nil 'silent)
          (eql 0 (m51-imp4--scheme
                  (format "(let ((f %s)) (let ((bv (f %S))) (if bv (bytevector-length bv) -1)))"
                          reader empty)))))))))

;;; --- The decode probes (window-system gated) --------------------------

(defun m51-imp4--probe-size (name thunk)
  "Probe NAME: THUNK yields an image size (a (WIDTH . HEIGHT) cons).
Decode happens inside THUNK.  A missing window system is an INFO-skip.
Any other signalled error is a FAIL."
  (condition-case err
      (let ((size (funcall thunk)))
        (m51-imp4--check name (and (consp size)
                                   (integerp (car size)) (> (car size) 0)
                                   (integerp (cdr size)) (> (cdr size) 0))))
    (error
     (if (m51-imp4--ws-error-p err)
         (m51-imp4--skip name err)
       (princ (format "INFO m51/imp4/%s error=%S\n" name err))
       (m51-imp4--check name nil)))))

(defun m51-imp4--probe-decode-error (name file)
  "Probe NAME: loading FILE signals an error.  The failure path must
signal.  A missing window system is an INFO-skip.  No error is a FAIL."
  (condition-case err
      (progn
        (image-size (create-image file) t)
        ;; No error: the failure path did not signal.
        (m51-imp4--check name nil))
    (error
     (if (m51-imp4--ws-error-p err)
         (m51-imp4--skip name err)
       (m51-imp4--check name t)))))

(setq m51-imp4--group 'decode)

;; Success: a real tracked PBM decodes to a positive size.
(m51-imp4--probe-size
 "success/pbm-decode"
 (lambda ()
   (image-size (create-image (expand-file-name "etc/images/alt.pbm"
                                               m51-imp4--root))
               t)))
;; Success: a scratch-dir PBM generated by this corpus decodes to its
;; declared 2x2 size.  This exercises the read of a non-etc file.
(m51-imp4--probe-size
 "success/scratch-pbm-decode"
 (lambda ()
   (m51-imp4--tmpdir
    (lambda (dir)
      (let ((file (expand-file-name "s.pbm" dir)))
        (write-region "P1\n2 2\n0 1\n1 0\n" nil file nil 'silent)
        (image-size (create-image file) t))))))
;; Failure: a missing file must signal.
(m51-imp4--probe-decode-error
 "failure/missing-file"
 (expand-file-name "etc/images/m51-imp4-does-not-exist.pbm"
                   m51-imp4--root))

;;; --- The min-count guards (review F2a) -------------------------------
;;
;; These register into no group.  They make an unexpectedly small run
;; FAIL: a group with zero executed checks must not read green.

(setq m51-imp4--group nil)

(m51-imp4--check "reg/min-hop-checks-5"
                 (>= (m51-imp4--group-count 'hop) 5))
(m51-imp4--check "reg/min-total-checks-5"
                 (>= (apply #'+ (mapcar #'cdr m51-imp4--counts)) 5))
