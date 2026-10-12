;;; test-m54-imp2.el --- M54 imp-2 output after-write verdict corpus.
;;;
;;; M54 imp-2 moves ONE operation of the src/termchar.h OUTPUT stream
;;; into the module (emacs tty-output): the after-write DECISION of one
;;; output write (brief.org section 1).  C keeps the FILE *output, the
;;; =fwrite=, the =clearerr=, and the return shape; C stays the single
;;; writer.  Scheme borrows the DECISION only.  The state is *C owned,
;;; Scheme borrowed* (docs/m54-plan.org section 6).
;;;
;;; This corpus pins these groups:
;;;
;;;   S1 -- the verdict table.  It resolves (emacs tty-output) through
;;;         `eval-scheme' and calls tty-write-verdict for each plain
;;;         input (written len err), and it checks the #nil-free string
;;;         return.  S1 holds 2 checks.
;;;   S2 -- the plain record.  tty-out-handle holds plain fixnums only,
;;;         and it exposes no port and no FILE *.  S2 holds 2 checks.
;;;   S3 -- the seam.  The dispatcher, the single call site in
;;;         m52_tty_write_1, the scm_c_public_ref site, and the give-up
;;;         test, as name checks (not line numbers).  S3 holds 4 checks.
;;;   S4 -- the registration: the corpus is in the (m54) group of
;;;         tool/run-tests.scm, after test-m54-imp1.el, and the (m52)
;;;         and (m53) groups stay present.  S4 holds 4 checks.
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
;;; case m54-imp2/output-write-verdict-e2e in test/pty-driver.py: it
;;; drives the seam to real bytes at the master and checks the reported
;;; count.  A read error here is a real FAIL, never a silent pass.

(princ "=== m54 imp-2 output after-write verdict suite ===\n")

(require 'imp-ert-report)

(defvar m54-imp2--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))
(defvar m54-imp2--registered 0
  "Total number of checks this corpus has registered.")
(defvar m54-imp2--group nil
  "The group that `m54-imp2--check' counts into: `s1' .. `s5', or nil.")
(defvar m54-imp2--counts nil
  "Alist of (GROUP . COUNT) for the registered checks.")

(defun m54-imp2--group-count (group)
  "Number of checks registered so far in GROUP."
  (or (cdr (assq group m54-imp2--counts)) 0))

(defun m54-imp2--bump-group ()
  "Count one check into `m54-imp2--group'."
  (when m54-imp2--group
    (let ((cell (assq m54-imp2--group m54-imp2--counts)))
      (if cell
          (setcdr cell (1+ (cdr cell)))
        (push (cons m54-imp2--group 1) m54-imp2--counts)))))

(defun m54-imp2--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
the symbol `m54-imp2-absent' when REL does not exist."
  (let ((path (expand-file-name rel m54-imp2--root)))
    (if (not (file-exists-p path))
        'm54-imp2-absent
      (with-temp-buffer
        (insert-file-contents path)
        (funcall fn)))))

(defun m54-imp2--contains-p (rel needle)
  "Non-nil when the TRACKED file REL contains NEEDLE.  An absent file
folds to nil, so a check prints FAIL: an absent src/ file is a real
error, not a pass (brief.org section 2)."
  (let ((hit (m54-imp2--with rel
               (lambda ()
                 (goto-char (point-min))
                 (search-forward needle nil t)))))
    (and (not (eq hit 'm54-imp2-absent)) (and hit t))))

(defun m54-imp2--count (rel needle)
  "Count the literal occurrences of NEEDLE in REL, or the symbol
`m54-imp2-absent' when REL does not exist.  This is a literal count, so
a call site that appears twice is caught."
  (m54-imp2--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (search-forward needle nil t) (setq n (1+ n)))
        n))))

(defun m54-imp2--ordered-p (rel needles)
  "Non-nil when the TRACKED file REL holds every NEEDLE in the GIVEN
ORDER: each search starts after the previous match."
  (m54-imp2--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((all t))
        (dolist (needle needles)
          (when all
            (unless (search-forward needle nil t) (setq all nil))))
        all))))

(defun m54-imp2--eval-scheme-int (expr)
  "Evaluate the plain Scheme EXPRESSION in the built Emacs and return
its integer value, or nil on any error.  The corpus calls the module
procedures through `resolve-module' / `module-ref': it does not use a
module-load probe as the proof of behaviour."
  (condition-case nil
      (eval-scheme expr)
    (error nil)))

(defun m54-imp2--check (name ok)
  "Report and register one check.  OK is a boolean.  When the source
file is absent the reader returns the symbol `m54-imp2-absent', so the
caller's test folds to nil and this prints FAIL.  Either way this
registers a real FAILING ERT test, so an absent src/ file is a real
error, not a pass."
  (let* ((absent (eq ok 'm54-imp2-absent))
         (pass (and (not absent) (and ok t))))
    (if absent
        (princ (format "FAIL m54/imp2/%s (source file absent)\n" name))
      (princ (format "%s m54/imp2/%s\n" (if pass "PASS" "FAIL") name)))
    (setq m54-imp2--registered (1+ m54-imp2--registered))
    (m54-imp2--bump-group)
    (imp-register-bool-as-ert-test (format "m54-imp2/%s" name) pass)))

;;; --- S1. The verdict table (brief.org section 7.1) ------------------

;; The pure DECISION runs in Scheme.  The verdict procedure takes the
;; plain counts (written len err) and returns a plain string.  A hard
;; errno (EIO) gives up; EINTR / EAGAIN retry; a complete write is done.

(setq m54-imp2--group 's1)

(m54-imp2--check "verdict-table"
                 (eql 1 (m54-imp2--eval-scheme-int
                         (concat
                          "(let ((m (resolve-module '(emacs tty-output))))"
                          " (if (and"
                          "  (equal? ((module-ref m 'tty-write-verdict) 5 5 0) \"done\")"
                          "  (equal? ((module-ref m 'tty-write-verdict) 0 0 0) \"done\")"
                          "  (equal? ((module-ref m 'tty-write-verdict) 3 5 EINTR) \"retry\")"
                          "  (equal? ((module-ref m 'tty-write-verdict) 3 5 EAGAIN) \"retry\")"
                          "  (equal? ((module-ref m 'tty-write-verdict) 3 5 0) \"retry\")"
                          "  (equal? ((module-ref m 'tty-write-verdict) 3 5 EIO) \"give-up\")"
                          "  (equal? ((module-ref m 'tty-write-verdict) 0 5 EIO) \"give-up\"))"
                          " 1 0))"))))

;; The return type is a plain string, never #nil, for every path: C tests
;; the verdict with a string compare, so a #nil return would break the
;; give-up test.
(m54-imp2--check "string-return-no-nil"
                 (eql 1 (m54-imp2--eval-scheme-int
                         (concat
                          "(let ((m (resolve-module '(emacs tty-output))))"
                          " (if (and"
                          "  (string? ((module-ref m 'tty-write-verdict) 5 5 0))"
                          "  (string? ((module-ref m 'tty-write-verdict) 3 5 EINTR))"
                          "  (string? ((module-ref m 'tty-write-verdict) 3 5 EIO)))"
                          " 1 0))"))))

;;; --- S2. The plain record (brief.org section 7.1) -------------------

;; The safe handle of milestone.org section 5 is a plain value box: it
;; holds plain fixnums only, and it is NOT a port and NOT a FILE *.  A
;; record that held a port would let Scheme own a C stream.

(setq m54-imp2--group 's2)

(m54-imp2--check "record-plain-fixnums"
                 (eql 1 (m54-imp2--eval-scheme-int
                         (concat
                          "(let* ((m (resolve-module '(emacs tty-output)))"
                          "       (h ((module-ref m 'make-tty-out-handle) 12 2 1)))"
                          " (if (and"
                          "  ((module-ref m 'tty-out-handle?) h)"
                          "  (exact-integer? ((module-ref m 'tty-out-handle-bytes) h))"
                          "  (exact-integer? ((module-ref m 'tty-out-handle-short-writes) h))"
                          "  (exact-integer? ((module-ref m 'tty-out-handle-hard-errors) h))"
                          "  (= ((module-ref m 'tty-out-handle-bytes) h) 12)"
                          "  (= ((module-ref m 'tty-out-handle-short-writes) h) 2)"
                          "  (= ((module-ref m 'tty-out-handle-hard-errors) h) 1))"
                          " 1 0))"))))

(m54-imp2--check "record-no-port"
                 (eql 1 (m54-imp2--eval-scheme-int
                         (concat
                          "(let* ((m (resolve-module '(emacs tty-output)))"
                          "       (h ((module-ref m 'make-tty-out-handle) 0 0 0)))"
                          " (if (and"
                          "  (not (port? h))"
                          "  (not (port? ((module-ref m 'tty-out-handle-bytes) h)))"
                          "  (not ((module-ref m 'tty-out-handle?) 0)))"
                          " 1 0))"))))

;;; --- S3. The seam (brief.org section 7.2) ---------------------------

;; Name checks, not line pins.  The dispatcher resolves the module
;; procedure one time, and the single call site sits in m52_tty_write_1.

(setq m54-imp2--group 's3)

(m54-imp2--check "seam-dispatcher"
                 (and (m54-imp2--contains-p
                       "src/term.c"
                       "m54_tty_write_verdict_scheme (Lisp_Object written, Lisp_Object len,")
                      (m54-imp2--contains-p
                       "src/term.c"
                       "m54_tty_write_gives_up_p (Lisp_Object verdict)")))
(m54-imp2--check "seam-scm-ref-site"
                 (m54-imp2--contains-p
                  "src/term.c"
                  "scm_c_public_ref (\"emacs tty-output\", \"tty-write-verdict\")"))
(m54-imp2--check "seam-single-call-site"
                 (eql 1 (m54-imp2--count
                         "src/term.c"
                         "m54_tty_write_verdict_scheme (make_fixnum (written)")))
(m54-imp2--check "seam-verdict-procedure"
                 (and (m54-imp2--contains-p
                       "mod/emacs/tty-output.scm"
                       "(define (tty-write-verdict written len err)")
                      (m54-imp2--contains-p
                       "mod/emacs/tty-output.scm"
                       "(define (make-tty-out-handle bytes short-writes hard-errors)")
                      (m54-imp2--contains-p
                       "mod/emacs/tty-output.scm"
                       "tty-write-verdict")))

;;; --- S4. The registration -------------------------------------------

(setq m54-imp2--group 's4)

(m54-imp2--check "run-tests-m54-imp2"
                 (m54-imp2--contains-p "tool/run-tests.scm"
                                       "test/m54/test-m54-imp2.el"))
(m54-imp2--check "run-tests-m54-group"
                 (m54-imp2--contains-p "tool/run-tests.scm" "(group (m54)"))
(m54-imp2--check "run-tests-imp2-after-imp1"
                 (m54-imp2--ordered-p "tool/run-tests.scm"
                                      '("test/m54/test-m54-imp1.el"
                                        "test/m54/test-m54-imp2.el")))
(m54-imp2--check "run-tests-m52-m53-present"
                 (and (m54-imp2--contains-p "tool/run-tests.scm" "(group (m52)")
                      (m54-imp2--contains-p "tool/run-tests.scm" "(group (m53)")))

;;; --- S5. The guards -------------------------------------------------

;; An --filter that matches no group already reports exit 0 with 0
;; tests, so a green m54 gate proves nothing until the corpus exists and
;; its checks really register.  These guards fail when the corpus body
;; is truncated or its core checks do not run.  S1 holds 2 checks, S2
;; holds 2, S3 holds 4, and S4 holds 4.

(setq m54-imp2--group 's5)

(m54-imp2--check "reg/min-s1-checks-2" (>= (m54-imp2--group-count 's1) 2))
(m54-imp2--check "reg/min-s2-checks-2" (>= (m54-imp2--group-count 's2) 2))
(m54-imp2--check "reg/min-s3-checks-4" (>= (m54-imp2--group-count 's3) 4))
(m54-imp2--check "reg/min-s4-checks-4" (>= (m54-imp2--group-count 's4) 4))

;;; --- The group-total check ------------------------------------------

;; The floor is the measured count of m54-imp2 tests: 16 registered
;; checks (S1 2, S2 2, S3 4, S4 4, S5 4) plus the group-total deftest,
;; allowing one slack.

(defvar m54-imp2--min-gate-total 16
  "The minimum number of m54-imp2 ERT tests: 16 registered checks plus
the group-total deftest, allowing one slack.")

(ert-deftest m54-imp2/gate-m54-imp2-total ()
  "The m54-imp2 corpus registers at least its floor."
  (should (>= (length (ert-select-tests "^m54-imp2" t))
              m54-imp2--min-gate-total)))

(princ (format "=== m54 imp-2 suite done (%d checks; s1 %d, s2 %d, s3 %d, s4 %d, s5 %d) ===\n"
               m54-imp2--registered
               (m54-imp2--group-count 's1)
               (m54-imp2--group-count 's2)
               (m54-imp2--group-count 's3)
               (m54-imp2--group-count 's4)
               (m54-imp2--group-count 's5)))
