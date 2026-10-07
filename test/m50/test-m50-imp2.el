;;; test-m50-imp2.el --- M50 imp-2 corpus (the typed C --emacs-daemon-state leaf).
;;;
;;; M50 imp-2 adds the typed C leaf over plain values for the movable
;;; daemonp block of src/emacs.c (docs/m50-plan.org section 3.3 and
;;; brief.org section 3), the thin wrapper in (emacs emacs) (brief
;;; section 4), and this tracked corpus (brief section 6).  imp-2 adds
;;; leaves only: it moves no decision.  The daemonp decision stays in C
;;; until imp-3.
;;;
;;; This corpus reads tracked files, and it runs one gated runtime probe.
;;; It pins:
;;;   G1 -- the leaf DEFUN --emacs-daemon-state exists in src/emacs.c
;;;         with the exact name of brief.org section 3 (milestone.org
;;;         section 3.3 step 1); the ^DEFUN count is 6; the file holds
;;;         "guile.h"; the block comment names the plain-value rule.
;;;   G2 -- the plain-value shape: the leaf doc string holds
;;;         FIX-20261006-guilemacs, the word "plain", and a shape word
;;;         (a "boolean", a "string", or a "list").
;;;   G3 -- mod/emacs/emacs.scm holds (define-module (emacs emacs), the
;;;         defelisp binding, the wrapper, and the exports; it holds no
;;;         FFI and no scm_c_public_ref; it states the elisp-nil rule
;;;         (nil (#nil), not #f); prelude/load.scm loads (emacs emacs).
;;;   G4 -- the boundary rules: the IS_DAEMON read, the daemon_name
;;;         read, the Fdaemonp body, and daemon-initialized are still
;;;         present; the leaf calls emacs_daemon_state_1, not Fdaemonp.
;;;   G5 -- the (m50) group carries this corpus, and a per-group
;;;         min-count guard fails when the corpus is truncated.  Pin G1,
;;;         G2, G3, and G4 separately.
;;;   G6 -- the gated runtime probe.  Run the built src/emacs and call
;;;         the leaf.  An absent binary is an INFO-skip.  A probe
;;;         error is a FAIL, never a silent pass (docs/kb.org
;;;         m4x-probe-failure-must-not-read-as-a-skip).
;;;
;;; A read error is a real error, never a silent pass.  An absent src/
;;; file is a real error.  This corpus reads no docs/ needle
;;; (docs/kb.org test-must-not-read-docs).

(princ "=== m50 imp-2 leaves suite ===\n")

(require 'imp-ert-report)

(defvar m50-imp2--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))

(defvar m50-imp2--registered 0
  "Total number of tracked-file checks this corpus has registered.")

(defvar m50-imp2--group nil
  "The group that `m50-imp2--check' counts into: `g1' ... `g4', or nil.")

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
a real error, not a pass (brief.org section 6).  Contrast
`m50-imp2--contains-p', which returns `m50-imp2-absent' so the reader can
tell absent from stale.  Every string check on a tracked file uses this
folder, so a missing file registers a real FAILING ERT test."
  (let ((hit (m50-imp2--contains-p rel needle)))
    (and (not (eq hit 'm50-imp2-absent)) (and hit t))))

(defun m50-imp2--count (rel regexp)
  "Count the matches of REGEXP in REL."
  (m50-imp2--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (re-search-forward regexp nil t) (setq n (1+ n)))
        n))))

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
The count callers pass `(eql N value)': when the source file is absent the
reader returns the symbol `m50-imp2-absent', so `eql' yields nil and this
prints FAIL.  The string callers use `m50-imp2--tracked-p', which folds an
absent file to nil for the same reason, so this prints FAIL too.  An
absent src/ file is a real error, not a pass (brief.org section 6).  The
`m50-imp2-absent' branch below is thus a safety net: no tracked caller
passes the raw symbol to reach it."
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

(defun m50-imp2--leaf-body ()
  "Return the source of the DEFUN \"--emacs-daemon-state\" body, or nil."
  (m50-imp2--with "src/emacs.c"
    (lambda ()
      (goto-char (point-min))
      (when (search-forward "DEFUN (\"--emacs-daemon-state\"" nil t)
        (let ((start (line-beginning-position)))
          (if (re-search-forward "\nDEFUN (\"" nil t)
              (buffer-substring-no-properties start (match-beginning 0))
            (buffer-substring-no-properties start (point-max))))))))

(defun m50-imp2--export-names (rel)
  "The wrapper names of the #:export form of REL, in order."
  (m50-imp2--with rel
    (lambda ()
      (goto-char (point-min))
      (when (search-forward "#:export (" nil t)
        (let* ((start (point))
               (end (save-excursion
                      (goto-char start)
                      (search-forward "))" nil t)))
               (names '()))
          (when end
            (goto-char start)
            (while (re-search-forward "\\_<\\(emacs-[a-z-]+\\)\\_>" end t)
              (push (match-string 1) names)))
          (nreverse names))))))

;;; --- G1. The leaf DEFUN (brief.org section 3) -----------------------

(setq m50-imp2--group 'g1)

(m50-imp2--check "leaf-defun"
                 (m50-imp2--tracked-p "src/emacs.c"
                                      "DEFUN (\"--emacs-daemon-state\""))
(m50-imp2--check "defun-count-6"
                 (eql 6 (m50-imp2--count "src/emacs.c" "^DEFUN (\"")))
(m50-imp2--check "emacs.c-has-guile.h"
                 (m50-imp2--tracked-p "src/emacs.c" "#include \"guile.h\""))
(m50-imp2--check "leaf-block-comment-plain"
                 (m50-imp2--tracked-p "src/emacs.c"
                                      "plain values only"))

;;; --- G2. The plain-value shape (brief.org section 3) ----------------

(setq m50-imp2--group 'g2)

;; The check reads the leaf body, so it holds after a re-order of the
;; block.
(let ((body (m50-imp2--leaf-body)))
  (m50-imp2--check "doc-marker"
                   (and (stringp body)
                        (string-match-p "FIX-20261006-guilemacs" body) t))
  (m50-imp2--check "doc-plain"
                   (and (stringp body) (string-match-p "plain" body) t))
  (m50-imp2--check "doc-shape"
                   (and (stringp body)
                        (string-match-p "boolean\\|string\\|list" body)
                        t)))

;; The aggregate count proves the marker really names the block comment,
;; the helper comment, and the leaf doc (3 sites at imp-2).
(m50-imp2--check "doc-marker-3"
                 (eql 3 (m50-imp2--count "src/emacs.c"
                                         "FIX-20261006-guilemacs")))

;;; --- G3. The wrapper module (brief.org section 4) -------------------

(setq m50-imp2--group 'g3)

(m50-imp2--check "module-exists"
                 (m50-imp2--tracked-p "mod/emacs/emacs.scm"
                                      "(define-module (emacs emacs)"))
(m50-imp2--check "module-declarative"
                 (m50-imp2--tracked-p "mod/emacs/emacs.scm" "#:declarative? #t"))
(m50-imp2--check "module-defelisp-1"
                 (eql 1 (m50-imp2--count "mod/emacs/emacs.scm"
                                         "^(defelisp %--emacs-")))
(m50-imp2--check "module-wrapper"
                 (m50-imp2--tracked-p "mod/emacs/emacs.scm"
                                      "(define (emacs-daemon-state)"))
;; The C leaf returns Qt / Qnil; Qnil reads as Guile #nil, not #f.  The
;; module doc must state that rule so imp-3 and imp-5 do not fold the
;; leaf's nil to #f by mistake.
(m50-imp2--check "module-nil-comment"
                 (m50-imp2--tracked-p "mod/emacs/emacs.scm" "nil (#nil)"))
(m50-imp2--check "module-exports"
                 (equal '("emacs-daemon-state")
                        (m50-imp2--export-names "mod/emacs/emacs.scm")))
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

;;; --- G4. The boundary rules (brief.org section 11) ------------------

(setq m50-imp2--group 'g4)

(m50-imp2--check "mech-is-daemon"
                 (m50-imp2--tracked-p "src/emacs.c" "IS_DAEMON"))
(m50-imp2--check "mech-daemon-name"
                 (m50-imp2--tracked-p "src/emacs.c" "daemon_name"))
(m50-imp2--check "hub-fdaemonp-body"
                 (m50-imp2--tracked-p "src/emacs.c" "Fdaemonp"))
(m50-imp2--check "hub-daemon-initialized"
                 (m50-imp2--tracked-p "src/emacs.c" "daemon-initialized"))
;; The leaf calls the mechanism helper, never its own hub, so a later hub
;; rewire cannot recurse (docs/kb.org leaf-must-call-the-mechanism).
(let ((body (m50-imp2--leaf-body)))
  (m50-imp2--check "leaf-calls-helper"
                   (and (stringp body)
                        (string-match-p "emacs_daemon_state_1" body) t))
  (m50-imp2--check "leaf-not-calls-fdaemonp"
                   (and (stringp body)
                        (not (string-match-p "Fdaemonp" body)) t)))

;;; --- G5. The group and the guards -----------------------------------

(setq m50-imp2--group nil)

(m50-imp2--check "reg/run-tests-m50-imp2"
                 (m50-imp2--tracked-p "tool/run-tests.scm"
                                      "test/m50/test-m50-imp2.el"))
;; `m50-imp2--tracked-p' must fold an absent tracked file to nil, so that
;; `m50-imp2--check' prints FAIL for it: an absent src/ file is a real
;; error, not a pass (brief.org section 6).  A non-existent path stands in
;; for an absent tracked file.
(m50-imp2--check "reg/absent-tracked-file-fails"
                 (null (m50-imp2--tracked-p "src/m50-imp2-no-such-file.c"
                                            "needle")))
(m50-imp2--check "reg/min-g1-checks-4"
                 (>= (m50-imp2--group-count 'g1) 4))
(m50-imp2--check "reg/min-g2-checks-4"
                 (>= (m50-imp2--group-count 'g2) 4))
(m50-imp2--check "reg/min-g3-checks-9"
                 (>= (m50-imp2--group-count 'g3) 9))
(m50-imp2--check "reg/min-g4-checks-6"
                 (>= (m50-imp2--group-count 'g4) 6))

;;; --- G6. The gated runtime probe (brief.org section 6) --------------

;; The (m50) group carries no `prelude' key, so tool/run-tests.scm loads
;; these files with run-tests-loadup-emacs, which is "../src/emacs ...
;; -l <file> --batch".  A probe therefore calls the leaf DIRECTLY, in
;; this process.
;;
;; An absent built binary is an INFO-skip.  A signalled error is a FAIL,
;; never a silent pass; the error is printed so the cause is visible.  An
;; undefined leaf signals void-function, so it is a FAIL too.

(defun m50-imp2--probe (tag thunk)
  "Register the probe TAG from the value of THUNK, which calls a leaf.
A non-nil value is a PASS.  A signalled error is a FAIL, never a silent
pass; the error is printed so the cause is visible."
  (m50-imp2--check
   (format "probe/%s" tag)
   (condition-case err
       (and (funcall thunk) t)
     (error (princ (format "INFO m50/imp2/%s error=%S\n" tag err))
            nil))))

(if (not (file-exists-p (expand-file-name "src/emacs" m50-imp2--root)))
    (princ "INFO m50/imp2/runtime-probes skipped (no built src/emacs)\n")
  (m50-imp2--probe
   "daemon-state-list-shape"
   (lambda ()
     (let ((v (--emacs-daemon-state)))
       (and (listp v) (= (length v) 2)))))
  (m50-imp2--probe
   "daemon-state-flag-type"
   (lambda ()
     (let ((flag (car (--emacs-daemon-state))))
       (or (eq flag t) (eq flag nil)))))
  (m50-imp2--probe
   "daemon-state-name-type"
   (lambda ()
     (let ((name (car (cdr (--emacs-daemon-state)))))
       (or (stringp name) (eq name nil)))))
  (m50-imp2--probe
   "daemon-state-nondaemon-nil-nil"
   (lambda ()
     ;; A --batch run is not a daemon, so both raw facts are nil.
     (equal (--emacs-daemon-state) '(nil nil)))))

(princ (format "=== m50 imp-2 leaves suite done (%d tracked checks; g1 %d, g2 %d, g3 %d, g4 %d) ===\n"
               m50-imp2--registered
               (m50-imp2--group-count 'g1)
               (m50-imp2--group-count 'g2)
               (m50-imp2--group-count 'g3)
               (m50-imp2--group-count 'g4)))
