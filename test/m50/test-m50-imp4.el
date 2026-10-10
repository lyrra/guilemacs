;;; test-m50-imp4.el --- M50 imp-4 corpus (the empty finding of src/emacs.c).
;;;
;;; M50 imp-4 is a FINDING imp (brief.org section 1 and section 3).  It
;;; re-scans src/emacs.c and records the verdict: NO movable policy
;;; remains.  The imp-1 audit marks daemonp as the only MOVES block, and
;;; imp-3 moved that decision to (emacs emacs).  The other four blocks
;;; STAY C.  imp-4 moves no C and no Scheme: C delta 0, Scheme delta 0.
;;;
;;; The block map (brief.org section 3):
;;;
;;;   invocation-name       STAYS C   Fcopy_sequence passthrough
;;;   invocation-directory  STAYS C   Fcopy_sequence passthrough
;;;   kill-emacs            STAYS C   noreturn; a SIGTERM / SIGHUP point
;;;   daemonp               MOVED     imp-3 moved the decision to Scheme
;;;   daemon-initialized    STAYS C   the deparenting mechanism; calls error
;;;
;;; The audit ambiguity of brief.org section 3.2 is settled here: an
;;; accessor is a passthrough, and a copy is not a decision.  So the two
;;; invocation accessors STAY C (passthrough-leaf-is-not-a-port).
;;;
;;; This corpus reads TRACKED files only (brief.org section 5).  It reads
;;; no docs/ needle (test-must-not-read-docs).  It pins three groups,
;;; each with a minimum count:
;;;
;;;   G1 -- the finding (the verdict).  11 group checks.
;;;   G2 -- the surface (the re-measured numbers).  10 group checks.
;;;   G3 -- the registration and the guards.  2 group checks; the section
;;;         holds 5 checks in all, because the 3 min-count guards
;;;         register into no group.
;;;
;;; The runtime probe is gated on a built src/emacs: an absent binary is
;;; an INFO skip, and a probe error is a FAIL, never a silent pass
;;; (m4x-probe-failure-must-not-read-as-a-skip).  The probe asserts
;;; (eq (daemonp) nil) and (not (eq (daemonp) t)) in a --batch run.
;;;
;;; A read error is a real error, never a silent pass.  An absent src/
;;; file is a real error.

(princ "=== m50 imp-4 empty-finding suite ===\n")

(require 'imp-ert-report)

(defvar m50-imp4--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))

(defvar m50-imp4--registered 0
  "Total number of tracked-file checks this corpus has registered.")

(defvar m50-imp4--group nil
  "The group that `m50-imp4--check' counts into: `g1' ... `g3', or nil.")

(defvar m50-imp4--counts nil
  "Alist of (GROUP . COUNT) for the registered tracked-file checks.")

(defun m50-imp4--group-count (group)
  "Number of tracked-file checks registered so far in GROUP."
  (or (cdr (assq group m50-imp4--counts)) 0))

(defun m50-imp4--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
the symbol `m50-imp4-absent' when REL does not exist."
  (let ((path (expand-file-name rel m50-imp4--root)))
    (if (not (file-exists-p path))
        'm50-imp4-absent
      (with-temp-buffer
        (insert-file-contents path)
        (funcall fn)))))

(defun m50-imp4--contains-p (rel needle)
  "Non-nil when REL (repo-root-relative) contains NEEDLE."
  (m50-imp4--with rel
    (lambda ()
      (goto-char (point-min))
      (search-forward needle nil t))))

(defun m50-imp4--tracked-p (rel needle)
  "Non-nil when the TRACKED file REL contains NEEDLE.  An absent tracked
file yields nil, so `m50-imp4--check' prints FAIL: an absent src/ file
is a real error, not a pass (brief.org section 5)."
  (let ((hit (m50-imp4--contains-p rel needle)))
    (and (not (eq hit 'm50-imp4-absent)) (and hit t))))

(defun m50-imp4--lines (rel)
  "Count the newlines of REL the way `wc -l' does."
  (m50-imp4--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (search-forward "\n" nil t) (setq n (1+ n)))
        n))))

(defun m50-imp4--count (rel regexp)
  "Count the matches of REGEXP in REL."
  (m50-imp4--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (re-search-forward regexp nil t) (setq n (1+ n)))
        n))))

(defun m50-imp4--count-scm-ref ()
  "Count scm_c_public_ref over src/*.[chm] (the tree-wide measure)."
  (let ((total 0)
        (dir (expand-file-name "src" m50-imp4--root)))
    (dolist (f (directory-files dir t "\\.[chm]\\'"))
      (setq total (+ total (or (m50-imp4--count f "scm_c_public_ref") 0))))
    total))

(defun m50-imp4--check (name ok)
  "Report and register one check on a TRACKED file.  OK is a boolean.
The count callers pass `(eql N value)': when the source file is absent
the reader returns the symbol `m50-imp4-absent', so `eql' yields nil and
this prints FAIL.  The string callers use `m50-imp4--tracked-p', which
folds an absent file to nil for the same reason, so this prints FAIL
too.  An absent src/ file is a real error, not a pass (brief.org
section 5)."
  (if (eq ok 'm50-imp4-absent)
      (princ (format "INFO m50/imp4/%s skipped (source file absent)\n" name))
    (progn
      (princ (format "%s m50/imp4/%s\n" (if ok "PASS" "FAIL") name))
      (setq m50-imp4--registered (1+ m50-imp4--registered))
      (when m50-imp4--group
        (let ((cell (assq m50-imp4--group m50-imp4--counts)))
          (if cell
              (setcdr cell (1+ (cdr cell)))
            (push (cons m50-imp4--group 1) m50-imp4--counts))))
      (imp-register-bool-as-ert-test (format "m50-imp4/%s" name) (and ok t)))))

(defun m50-imp4--defun-block (name)
  "Return the source of the DEFUN NAME in src/emacs.c, from its DEFUN
line to the line before the next DEFUN or end of file, or nil."
  (m50-imp4--with "src/emacs.c"
    (lambda ()
      (goto-char (point-min))
      (when (search-forward (concat "DEFUN (\"" name "\"") nil t)
        (let ((start (line-beginning-position)))
          (if (re-search-forward "\nDEFUN (\"" nil t)
              (buffer-substring-no-properties start (match-beginning 0))
            (buffer-substring-no-properties start (point-max))))))))

(defun m50-imp4--defun-names (rel)
  "The DEFUN names of REL, in file order.  A name that starts with two
hyphens is a typed --emacs-* leaf, not one of the 5 policy blocks, so
it is skipped.  No typed leaf remains at imp-4, so the list is the 5
block names."
  (m50-imp4--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((names '()))
        (while (re-search-forward "^DEFUN (\"\\([^\"]+\\)\"" nil t)
          (let ((name (match-string 1)))
            (unless (string-prefix-p "--" name)
              (push name names))))
        (nreverse names)))))

(defun m50-imp4--export-names (rel)
  "The wrapper names of the #:export form of REL, in order."
  (m50-imp4--with rel
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

;;; --- G1. The finding (brief.org section 3) --------------------------

(setq m50-imp4--group 'g1)

(defconst m50-imp4--emacs-blocks
  '("invocation-name"
    "invocation-directory"
    "kill-emacs"
    "daemonp"
    "daemon-initialized")
  "The 5 src/emacs.c block names, in file order (brief.org section 3).")

(defvar m50-imp4--emacs-defuns
  (let ((found (m50-imp4--defun-names "src/emacs.c")))
    (if (listp found) found '()))
  "The DEFUN names read out of src/emacs.c, in file order.")

;; The ordered block-name list is exactly the 5 names of brief.org
;; section 3.  An absent src/ file folds to the empty list, so this FAILs.
(m50-imp4--check "block-list-exact-5"
                 (equal m50-imp4--emacs-blocks m50-imp4--emacs-defuns))

;; The daemonp hub delegates to the Scheme decision.  This is the MOVED
;; block: its decision runs in (emacs emacs) since imp-3.
(let ((block (m50-imp4--defun-block "daemonp")))
  (m50-imp4--check "hub-delegates"
                   (and (stringp block)
                        (string-match-p "emacs_daemonp_scheme (Fcar (facts)"
                                        block)
                        t))
  ;; The hub holds no old C decision: no IS_DAEMON read, no recursive
  ;; call to its own hub (brief.org section 3;
  ;; leaf-must-call-the-mechanism).
  (m50-imp4--check "hub-no-old-decision"
                   (and (stringp block)
                        (not (string-match-p "IS_DAEMON" block)) t))
  (m50-imp4--check "hub-not-recursive"
                   (and (stringp block)
                        (not (string-match-p "Fdaemonp (" block)) t)))

;; The two invocation accessors are passthroughs over a C global.  A copy
;; is not a decision, so they STAY C (brief.org section 3.2).
(let ((block (m50-imp4--defun-block "invocation-name")))
  (m50-imp4--check "invocation-name-passthrough"
                   (and (stringp block)
                        (string-match-p "Fcopy_sequence (Vinvocation_name)"
                                        block)
                        t)))
(let ((block (m50-imp4--defun-block "invocation-directory")))
  (m50-imp4--check "invocation-directory-passthrough"
                   (and (stringp block)
                        (string-match-p
                         "Fcopy_sequence (Vinvocation_directory)" block)
                        t)))

;; kill-emacs STAYS C: it is noreturn and a SIGTERM / SIGHUP point.  The
;; signal path of the file calls Fkill_emacs over the signal test.
(m50-imp4--check "kill-emacs-signal-point"
                 (and (m50-imp4--tracked-p
                       "src/emacs.c" "sig == SIGTERM || sig == SIGHUP")
                      (m50-imp4--tracked-p
                       "src/emacs.c" "Fkill_emacs (make_fixnum (sig)")))

;; daemon-initialized STAYS C: it calls error and holds the deparenting
;; mechanism.
(let ((block (m50-imp4--defun-block "daemon-initialized")))
  (m50-imp4--check "daemon-init-calls-error"
                   (and (stringp block)
                        (string-match-p "error (" block) t))
  (m50-imp4--check "daemon-init-deparenting"
                   (and (stringp block)
                        (string-match-p "/dev/null" block)
                        (string-match-p "dup2" block) t)))

;; The mechanism stays C: the IS_DAEMON read and the daemon_name read.
(m50-imp4--check "mech-is-daemon"
                 (m50-imp4--tracked-p "src/emacs.c" "IS_DAEMON"))
(m50-imp4--check "mech-daemon-name"
                 (m50-imp4--tracked-p "src/emacs.c" "daemon_name"))

;;; --- G2. The surface (brief.org section 5) --------------------------

(setq m50-imp4--group 'g2)

(m50-imp4--check "emacs.c-lines-3441"
                 (eql 3441 (m50-imp4--lines "src/emacs.c")))
(m50-imp4--check "defun-count-5"
                 (eql 5 (m50-imp4--count "src/emacs.c" "^DEFUN (\"")))
(m50-imp4--check "emacs.c-scm-ref-6"
                 (eql 6 (m50-imp4--count "src/emacs.c" "scm_c_public_ref")))
(m50-imp4--check "fix-marker-3"
                 (eql 3 (m50-imp4--count "src/emacs.c"
                                         "FIX-20261006-guilemacs")))
(m50-imp4--check "scm-c-public-ref-250"
                 (eql 250 (m50-imp4--count-scm-ref)))
;; The two tokens of the deleted typed leaf are absent.
(m50-imp4--check "leaf-token-absent"
                 (not (m50-imp4--contains-p "src/emacs.c"
                                            "--emacs-daemon-state")))
(m50-imp4--check "leaf-fname-token-absent"
                 (not (m50-imp4--contains-p "src/emacs.c"
                                            "Femacs_daemon_state")))
(m50-imp4--check "emacs.scm-lines-47"
                 (eql 47 (m50-imp4--lines "mod/emacs/emacs.scm")))
(m50-imp4--check "emacs.scm-exports"
                 (equal '("emacs-daemonp")
                        (m50-imp4--export-names "mod/emacs/emacs.scm")))
(m50-imp4--check "load.scm-use-modules"
                 (m50-imp4--tracked-p "prelude/load.scm"
                                      "(use-modules (emacs emacs))"))

;;; --- G3. The registration and the guards (brief.org section 5) ------

(setq m50-imp4--group 'g3)

(m50-imp4--check "reg/run-tests-m50-imp4"
                 (m50-imp4--tracked-p "tool/run-tests.scm"
                                      "test/m50/test-m50-imp4.el"))
;; `m50-imp4--tracked-p' must fold an absent tracked file to nil, so that
;; `m50-imp4--check' prints FAIL for it: an absent src/ file is a real
;; error, not a pass (brief.org section 5).
(m50-imp4--check "reg/absent-tracked-file-fails"
                 (null (m50-imp4--tracked-p "src/m50-imp4-no-such-file.c"
                                            "needle")))

;; The min-count guards register into no group.
(setq m50-imp4--group nil)

(m50-imp4--check "reg/min-g1-checks-11"
                 (>= (m50-imp4--group-count 'g1) 11))
(m50-imp4--check "reg/min-g2-checks-10"
                 (>= (m50-imp4--group-count 'g2) 10))
(m50-imp4--check "reg/min-g3-checks-2"
                 (>= (m50-imp4--group-count 'g3) 2))

;;; --- The gated runtime probe (brief.org section 5) ------------------

;; The (m50) group carries no `prelude' key, so tool/run-tests.scm loads
;; these files with run-tests-loadup-emacs, which is "../src/emacs ...
;; -l <file> --batch".  A probe therefore calls the hub `daemonp'
;; DIRECTLY, in this process.
;;
;; An absent built binary is an INFO-skip.  A signalled error is a FAIL,
;; never a silent pass; the error is printed so the cause is visible.

(defun m50-imp4--probe (tag thunk)
  "Register the probe TAG from the value of THUNK, which calls `daemonp'.
A non-nil value is a PASS.  A signalled error is a FAIL, never a silent
pass; the error is printed so the cause is visible."
  (m50-imp4--check
   (format "probe/%s" tag)
   (condition-case err
       (and (funcall thunk) t)
     (error (princ (format "INFO m50/imp4/%s error=%S\n" tag err))
            nil))))

(if (not (file-exists-p (expand-file-name "src/emacs" m50-imp4--root)))
    (princ "INFO m50/imp4/runtime-probes skipped (no built src/emacs)\n")
  (m50-imp4--probe
   "daemonp-nondaemon-nil"
   (lambda ()
     ;; A --batch run is not a daemon, so `daemonp' returns nil.
     (eq (daemonp) nil)))
  (m50-imp4--probe
   "daemonp-nondaemon-not-false"
   (lambda ()
     ;; The result is the elisp nil (#nil), not the Scheme #f, and it is
     ;; not t.  A #f slip in the policy would cross back as a non-nil
     ;; value, so assert the exact nil (brief.org section 5).
     (and (eq (daemonp) nil)
          (not (eq (daemonp) t))))))

(princ (format "=== m50 imp-4 empty-finding suite done (%d tracked checks; g1 %d, g2 %d, g3 %d) ===\n"
               m50-imp4--registered
               (m50-imp4--group-count 'g1)
               (m50-imp4--group-count 'g2)
               (m50-imp4--group-count 'g3)))
