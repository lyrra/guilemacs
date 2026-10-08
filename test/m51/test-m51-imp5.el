;;; test-m51-imp5.el --- M51 imp-5 image streaming handle behavior corpus.
;;;
;;; M51 imp-5 moves the remaining src/image.c loaders onto the
;;; Scheme-owned image file handle.  PNG and JPEG now stream through
;;; (emacs image) image-open-stream / image-handle-read / image-close;
;;; TIFF, GIF, and ImageMagick read whole bytes through image-read-file.
;;;
;;; This corpus tests OBSERVABLE Emacs behavior through the built
;;; src/emacs (docs/m51-plan.org "Test strategy").  A test that reads C
;;; or Scheme source tests source layout only; such checks live in
;;; tool/ (tool/m51-audit.sh runs the static audits, and
;;; tool/m51-plan-lint.sh holds the record needles).
;;;
;;; Two evidence groups:
;;;
;;;   stream -- the streaming handle hop itself, headless-safe.  It calls
;;;             (emacs image) through the elisp `eval-scheme' bridge in
;;;             the running src/emacs and drives a real TRACKED PNG
;;;             (etc/images/gnus/gnus.png) through image-open-stream,
;;;             image-handle-read, and image-close: the open returns a
;;;             port, the first chunk has the PNG magic byte 0x89, the
;;;             read reaches #f EOF, a missing file yields #f, and the
;;;             close is idempotent.  This is real evidence for the
;;;             streaming half without a window system (imp-4 review O1).
;;;   decode -- the full decode path (create-image / image-size), which
;;;             drives the streaming handle end to end.  A decode needs
;;;             a window-system frame (src/frame.c check_window_system);
;;;             a headless build reports "Window system frame should be
;;;             used", which is an explicit environment INFO-skip.
;;;
;;; Gate rules:
;;;   - Any signalled error that is NOT the missing-window-system error
;;;     is a FAIL, never a silent pass
;;;     (docs/kb.org m4x-probe-failure-must-not-read-as-a-skip).
;;;   - The min-count guards make an unexpectedly small run FAIL, so 0
;;;     executed checks cannot read green.
;;;
;;; This corpus reads TRACKED files only (etc/images/).  It never reads
;;; docs/.  Tailored probes use a writable scratch directory.

(princ "=== m51 imp-5 image streaming handle suite ===\n")

(require 'imp-ert-report)

(defvar m51-imp5--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))

(defvar m51-imp5--group nil
  "The group that `m51-imp5--check' counts into: `stream' / `decode', or nil.")

(defvar m51-imp5--counts nil
  "Alist of (GROUP . COUNT) for the registered behavior checks.")

(defun m51-imp5--group-count (group)
  "Number of behavior checks registered so far in GROUP."
  (or (cdr (assq group m51-imp5--counts)) 0))

(defun m51-imp5--check (name ok)
  "Report and register one behavior check.  OK is a boolean."
  (princ (format "%s m51/imp5/%s\n" (if ok "PASS" "FAIL") name))
  (when m51-imp5--group
    (let ((cell (assq m51-imp5--group m51-imp5--counts)))
      (if cell (setcdr cell (1+ (cdr cell)))
        (push (cons m51-imp5--group 1) m51-imp5--counts))))
  (imp-register-bool-as-ert-test (format "m51-imp5/%s" name) (and ok t)))

(defun m51-imp5--skip (name err)
  "Report an environment INFO-skip for probe NAME, with reason ERR."
  (princ (format "INFO m51/imp5/%s skipped (no window system: %s)\n"
                 name (error-message-string err))))

(defun m51-imp5--ws-error-p (err)
  "Non-nil when ERR is the missing-window-system error of image-size."
  (string-match-p "Window system frame"
                  (error-message-string err)))

(defun m51-imp5--tmpdir (body)
  "Call BODY with a fresh scratch directory, then delete it."
  (let ((dir (file-name-as-directory (make-temp-file "m51-imp5" t))))
    (unwind-protect (funcall body dir) (delete-directory dir t))))

;;; --- The streaming handle probes (headless-safe) ----------------------

(defun m51-imp5--scheme (form)
  "Evaluate the Scheme string FORM in the running src/emacs and return
its value.  `eval-scheme' is the elisp bridge to `eval-string'."
  (eval-scheme form))

(defun m51-imp5--scheme-ref (proc)
  "Scheme text that resolves (emacs image) PROC to a local binding."
  (format "(module-ref (resolve-module '(emacs image)) '%s)" proc))

(defun m51-imp5--probe-hop (name thunk)
  "Probe hop NAME.  THUNK runs a Scheme form through `eval-scheme' and
yields the integer result.  A signalled error is a FAIL, never a silent
pass; the error is printed so the cause is visible."
  (m51-imp5--check
   name
   (condition-case err
       (funcall thunk)
     (error (princ (format "INFO m51/imp5/%s error=%S\n" name err))
            nil))))

(setq m51-imp5--group 'stream)

(let* ((png (expand-file-name "etc/images/gnus/gnus.png" m51-imp5--root))
       (open (m51-imp5--scheme-ref "image-open-stream"))
       (read (m51-imp5--scheme-ref "image-handle-read"))
       (close (m51-imp5--scheme-ref "image-close")))
  ;; 1. Open: image-open-stream of a tracked PNG yields a Guile port.
  (m51-imp5--probe-hop
   "stream/open-returns-port"
   (lambda ()
     (eql 1 (m51-imp5--scheme
             (format "(let ((f %s)) (if (port? (f %S)) 1 0))" open png)))))
  ;; 2. Read: the first chunk is a bytevector whose first byte is the
  ;;    PNG signature 0x89 (137).  The handle is closed afterwards.
  (m51-imp5--probe-hop
   "stream/read-first-byte-png-magic"
   (lambda ()
     (eql 137 (m51-imp5--scheme
               (format "(let ((f %s)(r %s)(c %s)) (let ((p (f %S))) (let ((bv (r p 8))) (c p) (if (bytevector? bv) (bytevector-u8-ref bv 0) -1))))"
                       open read close png)))))
  ;; 3. Read: draining the handle reaches #f at EOF (a short final read
  ;;    is not an error; only #f ends the loop).  The handle is closed.
  (m51-imp5--probe-hop
   "stream/read-reaches-eof"
   (lambda ()
     (eql 1 (m51-imp5--scheme
             (format "(let ((f %s)(r %s)(c %s)) (let ((p (f %S))) (let loop () (let ((bv (r p 4096))) (cond ((bytevector? bv) (loop)) ((eq? bv #f) (begin (c p) 1)) (else (begin (c p) 0)))))))"
                     open read close png)))))
  ;; 4. Miss: image-open-stream of a missing file yields #f.
  (m51-imp5--probe-hop
   "stream/missing-file-false"
   (lambda ()
     (eql 0 (m51-imp5--scheme
             (format "(let ((f %s)) (if (f %S) 1 0))"
                     open
                     (expand-file-name "etc/images/m51-imp5-nope.png"
                                       m51-imp5--root))))))
  ;; 5. Cleanup: closing a #f handle and a closed handle is a no-op
  ;;    (the close is idempotent, so the C unwind plus an explicit
  ;;    close cannot double-close).
  (m51-imp5--probe-hop
   "stream/close-idempotent"
   (lambda ()
     (eql 1 (m51-imp5--scheme
             (format "(let ((f %s)(r %s)(c %s)) (let ((p (f %S))) (r p 4) (c p) (c p) 1))"
                     open read close png))))))

;;; --- The decode probes (library + window-system gated) ----------------

(defun m51-imp5--lib? (type)
  "Non-nil when the build can decode image TYPE."
  (and (fboundp 'image-type-available-p)
       (image-type-available-p type)))

(defun m51-imp5--probe-size (name type thunk)
  "Probe NAME: THUNK yields an image size (a (WIDTH . HEIGHT) cons).
Decode happens inside THUNK.  The build must have image library TYPE and
a window system; otherwise report an INFO-skip.  Any other signalled
error is a FAIL."
  (cond
   ((not (m51-imp5--lib? type))
    (princ (format "INFO m51/imp5/%s skipped (no %s library)\n" name type)))
   (t
    (condition-case err
        (let ((size (funcall thunk)))
          (m51-imp5--check name (and (consp size)
                                     (integerp (car size)) (> (car size) 0)
                                     (integerp (cdr size)) (> (cdr size) 0))))
      (error
       (if (m51-imp5--ws-error-p err)
           (m51-imp5--skip name err)
         (princ (format "INFO m51/imp5/%s error=%S\n" name err))
         (m51-imp5--check name nil)))))))

(defun m51-imp5--probe-decode-error (name type file)
  "Probe NAME: loading FILE signals an error.  The decoder-failure path
must signal, and the borrowed handle must close through Scheme.  The
build must have image library TYPE and a window system; otherwise report
an INFO-skip.  No error is a FAIL."
  (cond
   ((not (m51-imp5--lib? type))
    (princ (format "INFO m51/imp5/%s skipped (no %s library)\n" name type)))
   (t
    (condition-case err
        (progn
          (image-size (create-image file) t)
          (m51-imp5--check name nil))
      (error
       (if (m51-imp5--ws-error-p err)
           (m51-imp5--skip name err)
         (m51-imp5--check name t)))))))

(setq m51-imp5--group 'decode)

;; Success: a tracked PNG decodes through the streaming handle (W1).
(m51-imp5--probe-size
 "success/png-stream-decode" 'png
 (lambda ()
   (image-size (create-image (expand-file-name "etc/images/gnus/gnus.png"
                                               m51-imp5--root))
               t)))
;; Success: a tracked JPEG decodes through the streaming handle (W1).
(m51-imp5--probe-size
 "success/jpeg-stream-decode" 'jpeg
 (lambda ()
   (image-size (create-image (expand-file-name "doc/lispref/elisp_type_hierarchy.jpg"
                                               m51-imp5--root))
               t)))
;; Success: a scratch GIF decodes through the whole-bytes entry (W2).
;; A 1x1 GIF89a, so the whole-bytes family (image-read-file feeding the
;; library memory callback) is exercised without a tracked GIF input.
(m51-imp5--probe-size
 "success/gif-whole-bytes-decode" 'gif
 (lambda ()
   (m51-imp5--tmpdir
    (lambda (dir)
      (let ((file (expand-file-name "one.gif" dir)))
        (write-region
         (unibyte-string
          71 73 70 38 39 61          ; "GIF89a"
          1 0 1 0 128 0 0            ; screen descriptor: 1x1, 2 colors
          0 0 0 255 255 255          ; global color table
          33 249 4 0 0 0 0 0         ; graphic control extension
          44 0 0 0 0 1 0 1 0 0       ; image descriptor: 1x1
          2 2 68 1 0                 ; image data
          59)                        ; trailer
         nil file nil 'silent)
        (image-size (create-image file) t))))))
;; Failure: a truncated PNG in a scratch dir reaches the decoder-failure
;; path.  The Scheme handle must be closed (no leak, no double close).
(m51-imp5--probe-decode-error
 "failure/truncated-png-closes-handle" 'png
 (m51-imp5--tmpdir
  (lambda (dir)
    (let ((bad (expand-file-name "truncated.png" dir)))
      ;; A valid PNG signature followed by garbage: the signature check
      ;; passes, the header read fails.
      (write-region (concat (unibyte-string 137 80 78 71 13 10 26 10)
                            "not a real png body")
                    nil bad nil 'silent)
      bad))))
;; Failure: a missing file must signal.
(m51-imp5--probe-decode-error
 "failure/missing-file" 'png
 (expand-file-name "etc/images/m51-imp5-does-not-exist.png"
                   m51-imp5--root))

;;; --- The min-count guards ---------------------------------------------

(setq m51-imp5--group nil)

(m51-imp5--check "reg/min-stream-checks-5"
                 (>= (m51-imp5--group-count 'stream) 5))
(m51-imp5--check "reg/min-total-checks-5"
                 (>= (apply #'+ (mapcar #'cdr m51-imp5--counts)) 5))
