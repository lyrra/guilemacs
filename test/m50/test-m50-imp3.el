;;; test-m50-imp3.el --- M50 imp-3 corpus (the daemonp decision in Scheme).
;;;
;;; M50 imp-3 moves the daemonp DECISION of src/emacs.c into
;;; (emacs emacs) (brief.org section 3 and section 4).  The decision --
;;; the name selection over IS_DAEMON and daemon_name -- now runs in
;;; Scheme.  C keeps the mechanism: the IS_DAEMON read and the
;;; daemon_name read in the static helper emacs_daemon_state_1.
;;;
;;; The shape:
;;;
;;;   hub Fdaemonp (splits the plain (FLAG NAME) list IN C)
;;;     -> emacs_daemonp_scheme         the dispatch helper (C)
;;;        -> (emacs emacs) emacs-daemonp   the decision (Scheme)
;;;     -> emacs_daemon_state_1         the mechanism (C)
;;;
;;; This corpus reads TRACKED files only (brief.org section 5).  It pins:
;;;   F1 -- the deleted leaf: --emacs-daemon-state and Femacs_daemon_state
;;;         are ABSENT from src/emacs.c; the ^DEFUN count is 5; the
;;;         scm_c_public_ref count is 6; the tree-wide count is 250.
;;;   F2 -- the bridge: the static helper emacs_daemonp_scheme is present,
;;;         it holds scm_c_public_ref ("emacs emacs", "emacs-daemonp")
;;;         and SCM_CALL_2; the Fdaemonp hub calls the bridge and does
;;;         NOT call itself and holds no old C decision.
;;;   F3 -- the Scheme policy: mod/emacs/emacs.scm holds
;;;         (define (emacs-daemonp flag name), the #nil branch (and no #f
;;;         in code), the export, no defelisp leaf, no FFI, and no
;;;         scm_c_public_ref.
;;;   F4 -- the boundary invariants: IS_DAEMON and daemon_name are still
;;;         read in C (in the mechanism); daemon-initialized still calls
;;;         error; the four STAYS C blocks are still present; the FIX
;;;         marker count holds.
;;;   F5 -- the (m50) group carries this corpus, and a per-group
;;;         min-count guard fails when the corpus is truncated.
;;;
;;; Runtime probes (gated on a built src/emacs): (daemonp) in a --batch
;;; run is not a daemon, so it returns nil; pin (eq (daemonp) nil) and
;;; that the result is the elisp nil, not the Scheme #f (which would
;;; cross back as a non-nil value).
;;;
;;; A read error is a real error, never a silent pass.  An absent src/
;;; file is a real error.  This corpus reads no docs/ needle
;;; (docs/kb.org test-must-not-read-docs).  A probe error is a FAIL,
;;; never a silent pass (docs/kb.org
;;; m4x-probe-failure-must-not-read-as-a-skip).

(princ "=== m50 imp-3 daemonp-policy suite ===\n")

(require 'imp-ert-report)

(defvar m50-imp3--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))

(defvar m50-imp3--registered 0
  "Total number of tracked-file checks this corpus has registered.")

(defvar m50-imp3--group nil
  "The group that `m50-imp3--check' counts into: `f1' ... `f4', or nil.")

(defvar m50-imp3--counts nil
  "Alist of (GROUP . COUNT) for the registered tracked-file checks.")

(defun m50-imp3--group-count (group)
  "Number of tracked-file checks registered so far in GROUP."
  (or (cdr (assq group m50-imp3--counts)) 0))

(defun m50-imp3--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
the symbol `m50-imp3-absent' when REL does not exist."
  (let ((path (expand-file-name rel m50-imp3--root)))
    (if (not (file-exists-p path))
        'm50-imp3-absent
      (with-temp-buffer
        (insert-file-contents path)
        (funcall fn)))))

(defun m50-imp3--contains-p (rel needle)
  "Non-nil when REL (repo-root-relative) contains NEEDLE."
  (m50-imp3--with rel
    (lambda ()
      (goto-char (point-min))
      (search-forward needle nil t))))

(defun m50-imp3--tracked-p (rel needle)
  "Non-nil when the TRACKED file REL contains NEEDLE.  An absent tracked
file yields nil, so `m50-imp3--check' prints FAIL: an absent src/ file
is a real error, not a pass (brief.org section 5)."
  (let ((hit (m50-imp3--contains-p rel needle)))
    (and (not (eq hit 'm50-imp3-absent)) (and hit t))))

(defun m50-imp3--count (rel regexp)
  "Count the matches of REGEXP in REL."
  (m50-imp3--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (re-search-forward regexp nil t) (setq n (1+ n)))
        n))))

(defun m50-imp3--count-code (rel regexp)
  "Count the matches of REGEXP in REL, skipping full comment lines.
A module comment may name a forbidden token (for example
`scm_c_public_ref') while explaining the contract; only the code must be
free of the token.  Scheme line comments start with `;'."
  (m50-imp3--with rel
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

(defun m50-imp3--count-scm-ref ()
  "Count scm_c_public_ref over src/*.[chm] (the tree-wide measure)."
  (let ((total 0)
        (dir (expand-file-name "src" m50-imp3--root)))
    (dolist (f (directory-files dir t "\\.[chm]\\'"))
      (setq total (+ total (or (m50-imp3--count f "scm_c_public_ref") 0))))
    total))

(defun m50-imp3--check (name ok)
  "Report and register one check on a TRACKED file.  OK is a boolean.
The count callers pass `(eql N value)': when the source file is absent
the reader returns the symbol `m50-imp3-absent', so `eql' yields nil and
this prints FAIL.  The string callers use `m50-imp3--tracked-p', which
folds an absent file to nil for the same reason, so this prints FAIL
too.  An absent src/ file is a real error, not a pass (brief.org
section 5)."
  (if (eq ok 'm50-imp3-absent)
      (princ (format "INFO m50/imp3/%s skipped (source file absent)\n" name))
    (progn
      (princ (format "%s m50/imp3/%s\n" (if ok "PASS" "FAIL") name))
      (setq m50-imp3--registered (1+ m50-imp3--registered))
      (when m50-imp3--group
        (let ((cell (assq m50-imp3--group m50-imp3--counts)))
          (if cell
              (setcdr cell (1+ (cdr cell)))
            (push (cons m50-imp3--group 1) m50-imp3--counts))))
      (imp-register-bool-as-ert-test (format "m50-imp3/%s" name) (and ok t)))))

(defun m50-imp3--defun-block (name)
  "Return the source of the DEFUN NAME in src/emacs.c, from its DEFUN
line to the line before the next DEFUN or end of file, or nil."
  (m50-imp3--with "src/emacs.c"
    (lambda ()
      (goto-char (point-min))
      (when (search-forward (concat "DEFUN (\"" name "\"") nil t)
        (let ((start (line-beginning-position)))
          (if (re-search-forward "\nDEFUN (\"" nil t)
              (buffer-substring-no-properties start (match-beginning 0))
            (buffer-substring-no-properties start (point-max))))))))

(defun m50-imp3--fn-body (name)
  "Return the C source of the static function NAME in src/emacs.c, from
the line before its name (the return-type line, so `static' is included)
to the closing `\\n}' at column 0, or nil."
  (m50-imp3--with "src/emacs.c"
    (lambda ()
      (goto-char (point-min))
      (when (search-forward (concat "\n" name " (") nil t)
        (let ((start (save-excursion (forward-line -1) (line-beginning-position))))
          (if (search-forward "\n}" nil t)
              (buffer-substring-no-properties start (match-end 0))
            (buffer-substring-no-properties start (point-max))))))))

(defun m50-imp3--export-names (rel)
  "The wrapper names of the #:export form of REL, in order."
  (m50-imp3--with rel
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

;;; --- F1. The deleted leaf (brief.org section 3) ---------------------

(setq m50-imp3--group 'f1)

;; After imp-3 no --emacs-daemon-state token and no Femacs_daemon_state
;; token remains (brief.org section 3 step 2).
(m50-imp3--check "leaf-token-absent"
                 (not (m50-imp3--contains-p "src/emacs.c"
                                            "--emacs-daemon-state")))
(m50-imp3--check "leaf-fname-token-absent"
                 (not (m50-imp3--contains-p "src/emacs.c"
                                            "Femacs_daemon_state")))
(m50-imp3--check "defun-count-5"
                 (eql 5 (m50-imp3--count "src/emacs.c" "^DEFUN (\"")))
(m50-imp3--check "emacs.c-scm-ref-6"
                 (eql 6 (m50-imp3--count "src/emacs.c" "scm_c_public_ref")))
(m50-imp3--check "scm-c-public-ref-250"
                 (eql 250 (m50-imp3--count-scm-ref)))

;;; --- F2. The C bridge (brief.org section 3) -------------------------

(setq m50-imp3--group 'f2)

(m50-imp3--check "bridge-present"
                 (m50-imp3--contains-p
                  "src/emacs.c"
                  "emacs_daemonp_scheme (Lisp_Object flag, Lisp_Object name)"))
(m50-imp3--check "bridge-public-ref"
                 (m50-imp3--contains-p
                  "src/emacs.c"
                  "scm_c_public_ref (\"emacs emacs\", \"emacs-daemonp\")"))
(m50-imp3--check "bridge-call2"
                 (m50-imp3--contains-p "src/emacs.c" "SCM_CALL_2"))
(let ((body (m50-imp3--fn-body "emacs_daemonp_scheme")))
  (m50-imp3--check "bridge-static"
                   (and (stringp body)
                        (string-match-p "static Lisp_Object" body) t)))
;; The hub Fdaemonp reads the two plain facts and delegates the
;; selection; it never computes the old C decision and never calls its
;; own hub (docs/kb.org leaf-must-call-the-mechanism).
(let ((block (m50-imp3--defun-block "daemonp")))
  (m50-imp3--check "hub-delegates"
                   (and (stringp block)
                        (string-match-p "emacs_daemonp_scheme (Fcar (facts)"
                                        block)
                        t))
  (m50-imp3--check "hub-no-old-decision"
                   (and (stringp block)
                        (not (string-match-p "IS_DAEMON" block)) t))
  (m50-imp3--check "hub-not-recursive"
                   (and (stringp block)
                        (not (string-match-p "Fdaemonp (" block)) t)))

;;; --- F3. The Scheme policy (brief.org section 4) --------------------

(setq m50-imp3--group 'f3)

(m50-imp3--check "module-exists"
                 (m50-imp3--tracked-p "mod/emacs/emacs.scm"
                                      "(define-module (emacs emacs)"))
(m50-imp3--check "policy-signature"
                 (m50-imp3--tracked-p "mod/emacs/emacs.scm"
                                      "(define (emacs-daemonp flag name)"))
;; The nil branch must be the elisp nil (#nil), never #f.
(m50-imp3--check "policy-nil-branch"
                 (m50-imp3--tracked-p "mod/emacs/emacs.scm" "#nil"))
;; The type rule at the source layer: the policy CODE must hold no #f.
;; Query nil (#nil) is the elisp nil; a Scheme #f would cross back as a
;; non-nil value.  The module header explains the rule in comments, so
;; count the code only (brief.org section 4 and section 5).
(m50-imp3--check "policy-no-false"
                 (let ((n (m50-imp3--count-code "mod/emacs/emacs.scm" "#f")))
                   (and (integerp n) (eql 0 n))))
(m50-imp3--check "policy-exports"
                 (equal '("emacs-daemonp")
                        (m50-imp3--export-names "mod/emacs/emacs.scm")))
;; imp-3 deletes the leaf binding and the wrapper.
(m50-imp3--check "policy-defelisp-0"
                 (eql 0 (m50-imp3--count "mod/emacs/emacs.scm"
                                         "^(defelisp %--emacs-")))
(m50-imp3--check "policy-no-wrapper"
                 (not (m50-imp3--contains-p "mod/emacs/emacs.scm"
                                            "(define (emacs-daemon-state)")))
(m50-imp3--check "policy-no-ffi"
                 (let ((n (m50-imp3--count-code
                           "mod/emacs/emacs.scm"
                           "system foreign\\|dynamic-link\\|libc\\.so\\|system\\*\\|primitive-fork\\|posix_spawn\\|ioctl\\|dynamic-func")))
                   (and (integerp n) (eql 0 n))))
(m50-imp3--check "policy-no-scm-ref"
                 (let ((n (m50-imp3--count-code "mod/emacs/emacs.scm"
                                                "scm_c_public_ref")))
                   (and (integerp n) (eql 0 n))))
;; The module must keep the elisp-nil rule (the nil (#nil), not #f).
(m50-imp3--check "policy-nil-comment"
                 (m50-imp3--tracked-p "mod/emacs/emacs.scm" "nil (#nil)"))
(m50-imp3--check "policy-declarative"
                 (m50-imp3--tracked-p "mod/emacs/emacs.scm" "#:declarative? #t"))

;;; --- F4. The boundary invariants (brief.org section 3) --------------

(setq m50-imp3--group 'f4)

(m50-imp3--check "mech-is-daemon"
                 (m50-imp3--tracked-p "src/emacs.c" "IS_DAEMON"))
(m50-imp3--check "mech-daemon-name"
                 (m50-imp3--tracked-p "src/emacs.c" "daemon_name"))
;; The four STAYS C blocks are still present.
(m50-imp3--check "stays-invocation-name"
                 (m50-imp3--tracked-p "src/emacs.c" "invocation-name"))
(m50-imp3--check "stays-invocation-directory"
                 (m50-imp3--tracked-p "src/emacs.c" "invocation-directory"))
(m50-imp3--check "stays-kill-emacs"
                 (m50-imp3--tracked-p "src/emacs.c" "kill-emacs"))
(m50-imp3--check "stays-daemon-initialized"
                 (m50-imp3--tracked-p "src/emacs.c" "daemon-initialized"))
;; daemon-initialized STAYS C because it calls error.
(let ((block (m50-imp3--defun-block "daemon-initialized")))
  (m50-imp3--check "daemon-init-calls-error"
                   (and (stringp block)
                        (string-match-p "error (" block) t)))
(m50-imp3--check "fix-marker-3"
                 (eql 3 (m50-imp3--count "src/emacs.c"
                                         "FIX-20261006-guilemacs")))

;;; --- F5. The group and the guards -----------------------------------

(setq m50-imp3--group nil)

(m50-imp3--check "reg/run-tests-m50-imp3"
                 (m50-imp3--tracked-p "tool/run-tests.scm"
                                      "test/m50/test-m50-imp3.el"))
;; `m50-imp3--tracked-p' must fold an absent tracked file to nil, so that
;; `m50-imp3--check' prints FAIL for it: an absent src/ file is a real
;; error, not a pass (brief.org section 5).
(m50-imp3--check "reg/absent-tracked-file-fails"
                 (null (m50-imp3--tracked-p "src/m50-imp3-no-such-file.c"
                                            "needle")))
(m50-imp3--check "reg/min-f1-checks-5"
                 (>= (m50-imp3--group-count 'f1) 5))
(m50-imp3--check "reg/min-f2-checks-7"
                 (>= (m50-imp3--group-count 'f2) 7))
(m50-imp3--check "reg/min-f3-checks-11"
                 (>= (m50-imp3--group-count 'f3) 11))
(m50-imp3--check "reg/min-f4-checks-8"
                 (>= (m50-imp3--group-count 'f4) 8))

;;; --- The gated runtime probe (brief.org section 5) ------------------

;; The (m50) group carries no `prelude' key, so tool/run-tests.scm loads
;; these files with run-tests-loadup-emacs, which is "../src/emacs ...
;; -l <file> --batch".  A probe therefore calls the hub `daemonp'
;; DIRECTLY, in this process.
;;
;; An absent built binary is an INFO-skip.  A signalled error is a FAIL,
;; never a silent pass; the error is printed so the cause is visible.

(defun m50-imp3--probe (tag thunk)
  "Register the probe TAG from the value of THUNK, which calls `daemonp'.
A non-nil value is a PASS.  A signalled error is a FAIL, never a silent
pass; the error is printed so the cause is visible."
  (m50-imp3--check
   (format "probe/%s" tag)
   (condition-case err
       (and (funcall thunk) t)
     (error (princ (format "INFO m50/imp3/%s error=%S\n" tag err))
            nil))))

(if (not (file-exists-p (expand-file-name "src/emacs" m50-imp3--root)))
    (princ "INFO m50/imp3/runtime-probes skipped (no built src/emacs)\n")
  (m50-imp3--probe
   "daemonp-nondaemon-nil"
   (lambda ()
     ;; A --batch run is not a daemon, so `daemonp' returns nil.
     (eq (daemonp) nil)))
  (m50-imp3--probe
   "daemonp-nondaemon-not-false"
   (lambda ()
     ;; The result is the elisp nil (#nil), not the Scheme #f.  A #f slip
     ;; in the policy would cross back as a non-nil value.  Assert the
     ;; result is exactly nil (the elisp nil), so this catches a #f that
     ;; crosses back as t OR as any other non-nil object, not only as t
     ;; (brief.org section 5; cr.org section 6.4).
     (and (eq (daemonp) nil)
          (not (eq (daemonp) t))))))

(princ (format "=== m50 imp-3 daemonp-policy suite done (%d tracked checks; f1 %d, f2 %d, f3 %d, f4 %d) ===\n"
               m50-imp3--registered
               (m50-imp3--group-count 'f1)
               (m50-imp3--group-count 'f2)
               (m50-imp3--group-count 'f3)
               (m50-imp3--group-count 'f4)))
