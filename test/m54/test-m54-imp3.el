;;; test-m54-imp3.el --- M54 imp-3 termscript copy decision corpus.
;;;
;;; M54 imp-3 moves ONE operation of the src/termchar.h TERMSCRIPT stream
;;; (a COPY of the terminal output, src/termchar.h :61) into the module
;;; (emacs tty-output): the after-write DECISION of ONE termscript copy
;;; write (brief.org section 4).  C keeps the FILE *termscript, the
;;; =fwrite=, the =clearerr=, the C open, and the C close; C stays the
;;; single writer.  Scheme borrows the DECISION only.  The copy REUSES
;;; tty-write-verdict (M54 imp-2) through the SAME dispatcher and the
;;; same plain values.
;;;
;;; This corpus pins these groups:
;;;
;;;   S1 -- the copy verdict table.  It resolves (emacs tty-output)
;;;         through `eval-scheme' and calls tty-write-verdict for the
;;;         copy count pairs (done / retry / give-up), and it checks that
;;;         NO twin verdict procedure exists.  S1 holds 2 checks.
;;;   S2 -- the copy counts and the handle (brief.org section 9, Option
;;;         A): tty-termscript-copy-handle builds the plain imp-2
;;;         tty-out-handle from the copy counts; it holds plain fixnums
;;;         only and no port and no FILE *.  S2 holds 2 checks.
;;;   S3 -- the seam.  The REUSED dispatcher, the ONE new call site in
;;;         m52_tty_write_1, the new m54_tty_termscript_* helper, the
;;;         scm_c_public_ref site, and the 10 classified copy sites
;;;         (brief.org section 5), as name checks (not line numbers).
;;;         S3 holds 7 checks.
;;;   S4 -- the registration: the corpus is in the (m54) group of
;;;         tool/run-tests.scm, after test-m54-imp2.el, and the (m52)
;;;         and (m53) groups stay present.  S4 holds 3 checks.
;;;   S5 -- the guards: a per-group min-count guard for S1 .. S4, and
;;;         the in-process group-total `ert-deftest'.  S5 holds 4 checks.
;;;
;;; This corpus reads TRACKED files only (src/, mod/, and the tracked
;;; runner tool/run-tests.scm).  It does NOT read docs/ (docs/kb.org
;;; test-must-not-read-docs): a gitignored record can only pass or skip,
;;; so a record check proves nothing.
;;;
;;; The pure DECISION is proven by the S1 headless table (the M52
;;; imp-4 … imp-8 idiom).  The real path is proven by the separate pty
;;; case m54-imp3/termscript-copy-e2e in test/pty-driver.py: it opens a
;;; real termscript file in the child and compares the termscript bytes
;;; with the bytes read at the pty master.  A read error here is a real
;;; FAIL, never a silent pass.

(princ "=== m54 imp-3 termscript copy decision suite ===\n")

(require 'imp-ert-report)

(defvar m54-imp3--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))
(defvar m54-imp3--registered 0
  "Total number of checks this corpus has registered.")
(defvar m54-imp3--group nil
  "The group that `m54-imp3--check' counts into: `s1' .. `s5', or nil.")
(defvar m54-imp3--counts nil
  "Alist of (GROUP . COUNT) for the registered checks.")

(defun m54-imp3--group-count (group)
  "Number of checks registered so far in GROUP."
  (or (cdr (assq group m54-imp3--counts)) 0))

(defun m54-imp3--bump-group ()
  "Count one check into `m54-imp3--group'."
  (when m54-imp3--group
    (let ((cell (assq m54-imp3--group m54-imp3--counts)))
      (if cell
          (setcdr cell (1+ (cdr cell)))
        (push (cons m54-imp3--group 1) m54-imp3--counts)))))

(defun m54-imp3--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
the symbol `m54-imp3-absent' when REL does not exist."
  (let ((path (expand-file-name rel m54-imp3--root)))
    (if (not (file-exists-p path))
        'm54-imp3-absent
      (with-temp-buffer
        (insert-file-contents path)
        (funcall fn)))))

(defun m54-imp3--contains-p (rel needle)
  "Non-nil when the TRACKED file REL contains NEEDLE.  An absent file
folds to nil, so a check prints FAIL: an absent src/ file is a real
error, not a pass (brief.org section 2)."
  (let ((hit (m54-imp3--with rel
               (lambda ()
                 (goto-char (point-min))
                 (search-forward needle nil t)))))
    (and (not (eq hit 'm54-imp3-absent)) (and hit t))))

(defun m54-imp3--count (rel needle)
  "Count the literal occurrences of NEEDLE in REL, or the symbol
`m54-imp3-absent' when REL does not exist.  This is a literal count, so
a call site that appears twice is caught."
  (m54-imp3--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (search-forward needle nil t) (setq n (1+ n)))
        n))))

(defun m54-imp3--ordered-p (rel needles)
  "Non-nil when the TRACKED file REL holds every NEEDLE in the GIVEN
ORDER: each search starts after the previous match."
  (m54-imp3--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((all t))
        (dolist (needle needles)
          (when all
            (unless (search-forward needle nil t) (setq all nil))))
        all))))

(defun m54-imp3--eval-scheme-int (expr)
  "Evaluate the plain Scheme EXPRESSION in the built Emacs and return
its integer value, or nil on any error.  The corpus calls the module
procedures through `resolve-module' / `module-ref': it does not use a
module-load probe as the proof of behaviour."
  (condition-case nil
      (eval-scheme expr)
    (error nil)))

(defun m54-imp3--check (name ok)
  "Report and register one check.  OK is a boolean.  When the source
file is absent the reader returns the symbol `m54-imp3-absent', so the
caller's test folds to nil and this prints FAIL.  Either way this
registers a real FAILING ERT test, so an absent src/ file is a real
error, not a pass."
  (let* ((absent (eq ok 'm54-imp3-absent))
         (pass (and (not absent) (and ok t))))
    (if absent
        (princ (format "FAIL m54/imp3/%s (source file absent)\n" name))
      (princ (format "%s m54/imp3/%s\n" (if pass "PASS" "FAIL") name)))
    (setq m54-imp3--registered (1+ m54-imp3--registered))
    (m54-imp3--bump-group)
    (imp-register-bool-as-ert-test (format "m54-imp3/%s" name) pass)))

;;; --- S1. The copy verdict table (brief.org section 6) ---------------

;; The copy REUSES the same DECISION.  The verdict procedure takes the
;; plain copy counts (copied len err) and returns a plain string.  A hard
;; errno (EIO) gives up; EINTR / EAGAIN (or err = 0) retry; a complete
;; copy is done.

(setq m54-imp3--group 's1)

(m54-imp3--check "copy-verdict-table"
                 (eql 1 (m54-imp3--eval-scheme-int
                         (concat
                          "(let ((m (resolve-module '(emacs tty-output))))"
                          " (if (and"
                          "  (equal? ((module-ref m 'tty-write-verdict) 7 7 0) \"done\")"
                          "  (equal? ((module-ref m 'tty-write-verdict) 0 0 0) \"done\")"
                          "  (equal? ((module-ref m 'tty-write-verdict) 4 7 EINTR) \"retry\")"
                          "  (equal? ((module-ref m 'tty-write-verdict) 4 7 EAGAIN) \"retry\")"
                          "  (equal? ((module-ref m 'tty-write-verdict) 4 7 0) \"retry\")"
                          "  (equal? ((module-ref m 'tty-write-verdict) 4 7 EIO) \"give-up\")"
                          "  (equal? ((module-ref m 'tty-write-verdict) 0 7 EIO) \"give-up\"))"
                          " 1 0))"))))

;; The copy must REUSE the one procedure: a second definition would be a
;; twin verdict procedure (brief.org section 18).
(m54-imp3--check "copy-no-twin-verdict"
                 (eql 1 (m54-imp3--count
                         "mod/emacs/tty-output.scm"
                         "(define (tty-write-verdict written len err)")))

;;; --- S2. The copy counts and the handle (brief.org section 9) ------

;; Option A: Scheme builds a tty-out-handle from the plain copy counts.
;; The handle is a plain value box: it holds plain fixnums only, and it
;; is NOT a port and NOT a FILE *.  C still does not read the handle, so
;; the handle is borrowed, not transferred.

(setq m54-imp3--group 's2)

(m54-imp3--check "copy-handle-fields"
                 (eql 1 (m54-imp3--eval-scheme-int
                         (concat
                          "(let* ((m (resolve-module '(emacs tty-output)))"
                          "       (h ((module-ref m 'tty-termscript-copy-handle) 10 10 0))"
                          "       (s ((module-ref m 'tty-termscript-copy-handle) 3 5 EIO))"
                          "       (i ((module-ref m 'tty-termscript-copy-handle) 3 5 EINTR)))"
                          " (if (and"
                          "  ((module-ref m 'tty-out-handle?) h)"
                          "  (= ((module-ref m 'tty-out-handle-bytes) h) 10)"
                          "  (= ((module-ref m 'tty-out-handle-short-writes) h) 0)"
                          "  (= ((module-ref m 'tty-out-handle-hard-errors) h) 0)"
                          "  (= ((module-ref m 'tty-out-handle-bytes) s) 3)"
                          "  (= ((module-ref m 'tty-out-handle-short-writes) s) 1)"
                          "  (= ((module-ref m 'tty-out-handle-hard-errors) s) 1)"
                          "  (= ((module-ref m 'tty-out-handle-short-writes) i) 1)"
                          "  (= ((module-ref m 'tty-out-handle-hard-errors) i) 0))"
                          " 1 0))"))))

(m54-imp3--check "copy-handle-no-port"
                 (eql 1 (m54-imp3--eval-scheme-int
                         (concat
                          "(let* ((m (resolve-module '(emacs tty-output)))"
                          "       (h ((module-ref m 'tty-termscript-copy-handle) 0 0 0)))"
                          " (if (and"
                          "  (not (port? h))"
                          "  (not (port? ((module-ref m 'tty-out-handle-bytes) h))))"
                          " 1 0))"))))

;;; --- S3. The seam (brief.org section 4 / section 5) -----------------

;; Name checks, not line pins.  The copy votes through the REUSED
;; dispatcher, and the ONE new call site sits in m52_tty_write_1.

(setq m54-imp3--group 's3)

(m54-imp3--check "seam-reused-dispatcher"
                 (m54-imp3--contains-p
                  "src/term.c"
                  "m54_tty_write_verdict_scheme (Lisp_Object written, Lisp_Object len,"))
;; M61 imp-2 re-pin: the ONE verdict site takes the plain errno as a 4th
;; argument, so no caller reads the global errno (the review of imp-2,
;; finding F3).  MEASURED with `grep -n 'm54_tty_termscript_verdict (size_t'
;; src/term.c`.
(m54-imp3--check "seam-termscript-helper"
                 (m54-imp3--contains-p
                  "src/term.c"
                  "m54_tty_termscript_verdict (size_t copied, size_t len, int err, bool failed)"))
(m54-imp3--check "seam-single-copy-call-site"
                 (eql 1 (m54-imp3--count
                         "src/term.c"
                         "m54_tty_termscript_verdict (copied, len,")))
(m54-imp3--check "seam-scm-ref-site"
                 (m54-imp3--contains-p
                  "src/term.c"
                  "scm_c_public_ref (\"emacs tty-output\", \"tty-termscript-copy-handle\")"))
(m54-imp3--check "seam-copy-handle-procedure"
                 (and (m54-imp3--contains-p
                       "mod/emacs/tty-output.scm"
                       "(define (tty-termscript-copy-handle copied len err)")
                      (m54-imp3--contains-p
                       "mod/emacs/tty-output.scm"
                       "tty-termscript-copy-handle")))
(m54-imp3--check "stay-c-copy-sites"
                 (and
                  ;; M61 imp-2 moved the 3 conversion_buffer copies of the
                  ;; normal glyph path into the per-TTY handle, so 2 of the
                  ;; 5 src/term.c copy sites stay C: the
                  ;; tty_send_additional_strings copy (it can run during a
                  ;; GC emergency escape) and the hard-clear putc loop.
                  (m54-imp3--contains-p
                   "src/term.c"
                   "fwrite (SDATA (string), 1, SBYTES (string), tty->termscript)")
                  (m54-imp3--contains-p "src/term.c" "putc (' ', tty->termscript)")
                  (eql 0 (m54-imp3--count
                          "src/term.c"
                          "fwrite (conversion_buffer, 1, coding->produced, tty->termscript)"))
                  ;; The moved copies run through the ONE mechanism of the
                  ;; M61 ordered path.
                  (eql 1 (m54-imp3--count
                          "src/term.c"
                          "fwrite (bytes, 1, len, tty->termscript)"))
                  ;; The src/cm.c putc sites stay C.  M62 imp-1 DELETED the
                  ;; per-byte capability writer cmputc, so the masked site
                  ;; is now a count of 0: the capability strings of that
                  ;; file cross the ONE sink and no putc writes one byte.
                  (eql 0 (m54-imp3--count
                          "src/cm.c"
                          "putc (c & 0177, current_tty->termscript)"))
                  (m54-imp3--contains-p "src/cm.c" "putc ('\\r', tty->termscript)")
                  (m54-imp3--contains-p "src/cm.c" "putc ('\\n', tty->termscript)")
                  ;; The src/dispnew.c send + flush stay C.
                  (m54-imp3--contains-p
                   "src/dispnew.c"
                   "fwrite (SDATA (string), 1, SBYTES (string), tty->termscript)")
                  (m54-imp3--contains-p "src/dispnew.c" "fflush (tty->termscript)")))

;; FIX-20261012-guilemacs (cr.org F3): the output errno is READ before
;; the copy seam, because the copy Scheme calls can change errno and the
;; output short-write path must keep its own value.
(m54-imp3--check "seam-output-errno-before-copy"
                 (m54-imp3--ordered-p
                  "src/term.c"
                  '("size_t written = fwrite (str, 1, len, tty->output);"
                    "int out_err = errno;"
                    "if (tty->termscript)")))

;;; --- S4. The registration -------------------------------------------

(setq m54-imp3--group 's4)

(m54-imp3--check "run-tests-m54-imp3"
                 (m54-imp3--contains-p "tool/run-tests.scm"
                                       "test/m54/test-m54-imp3.el"))
(m54-imp3--check "run-tests-imp3-after-imp2"
                 (m54-imp3--ordered-p "tool/run-tests.scm"
                                      '("test/m54/test-m54-imp2.el"
                                        "test/m54/test-m54-imp3.el")))
(m54-imp3--check "run-tests-m52-m53-present"
                 (and (m54-imp3--contains-p "tool/run-tests.scm" "(group (m52)")
                      (m54-imp3--contains-p "tool/run-tests.scm" "(group (m53)")))

;;; --- S5. The guards -------------------------------------------------

;; An --filter that matches no group already reports exit 0 with 0
;; tests, so a green m54 gate proves nothing until the corpus exists and
;; its checks really register.  These guards fail when the corpus body
;; is truncated or its core checks do not run.  S1 holds 2 checks, S2
;; holds 2, S3 holds 7, and S4 holds 3.

(setq m54-imp3--group 's5)

(m54-imp3--check "reg/min-s1-checks-2" (>= (m54-imp3--group-count 's1) 2))
(m54-imp3--check "reg/min-s2-checks-2" (>= (m54-imp3--group-count 's2) 2))
(m54-imp3--check "reg/min-s3-checks-7" (>= (m54-imp3--group-count 's3) 7))
(m54-imp3--check "reg/min-s4-checks-3" (>= (m54-imp3--group-count 's4) 3))

;;; --- The group-total check ------------------------------------------

;; The floor is the measured count of m54-imp3 tests: 18 registered
;; checks (S1 2, S2 2, S3 7, S4 3, S5 4) plus the group-total deftest,
;; allowing one slack.

(defvar m54-imp3--min-gate-total 18
  "The minimum number of m54-imp3 ERT tests: 18 registered checks plus
the group-total deftest, allowing one slack.")

(ert-deftest m54-imp3/gate-m54-imp3-total ()
  "The m54-imp3 corpus registers at least its floor."
  (should (>= (length (ert-select-tests "^m54-imp3" t))
              m54-imp3--min-gate-total)))

(princ (format "=== m54 imp-3 suite done (%d checks; s1 %d, s2 %d, s3 %d, s4 %d, s5 %d) ===\n"
               m54-imp3--registered
               (m54-imp3--group-count 's1)
               (m54-imp3--group-count 's2)
               (m54-imp3--group-count 's3)
               (m54-imp3--group-count 's4)
               (m54-imp3--group-count 's5)))
