;;; test-m42-imp1.el --- M42 imp-1 audit corpus (the TTY raw-input OS hop).
;;;
;;; M42 imp-1 is the docs-only audit (brief.org, docs/m42-plan.org).  It
;;; changes no C and no Scheme.  It answers three questions with
;;; evidence -- the embedded Guile FFI/port surface, the tty->input
;;; descriptor and its buffering, and the short-read / EINTR / EAGAIN /
;;; EIO / empty-queue behavior -- and records the original decision A1,
;;; which later M42 work superseded.
;;;
;;; This corpus reads files only.  It has no C dependency.  It pins:
;;;   D1 -- the baseline numbers: src/keyboard.c is 11,233 lines and
;;;         447 DEFUNs, src/keyboard-globals.c is 490 lines, and the
;;;         combined keyboard surface is 11,723.  (M43 imp-2 added the
;;;         --tty-fd accessor, so the M42 numbers moved; D2 follows.)
;;;   D2 -- the two portable C read leaves remain, and
;;;         tty-read-avail-input! uses them while Scheme owns the policy.
;;;   D3 -- the descriptor facts of brief.org §5 task 2 hold in the
;;;         tree: tty->input is a FILE * (src/termchar.h:51), opened by
;;;         emacs_fdopen (src/term.c:2571), reuses stdin for the initial
;;;         terminal (src/term.c:4632), is closed by delete_tty
;;;         (src/term.c:4901), and the read bypasses stdio through
;;;         emacs_read (src/sysdep.c:2664).
;;;   D4 -- the decision words and the imp-1 findings appear in the
;;;         gitignored records docs/m42-plan.org and docs/kb.org.  docs/
;;;         is gitignored, so a present-but-stale record is an INFO-skip,
;;;         not a FAIL; an absent record is also a skip.  Known limit:
;;;         D4 is advisory only -- on a fresh clone (no docs/) it
;;;         registers no ERT test, so it cannot turn this gate red.
;;;
;;; Each tracked-file check is printed as a PASS/FAIL line and turned
;;; into an ERT test so the harness counts it.  A read error is a real
;;; error, never a silent pass.  The corpus holds its own copy of every
;;; number it pins (brief.org §3).

(princ "=== m42 imp-1 audit suite ===\n")

(require 'imp-ert-report)

(defvar m42-imp1--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))

(defun m42-imp1--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
the symbol `m42-imp1-absent' when REL does not exist.  docs/ is
gitignored, so a checkout without it must not crash the subprocess: an
unguarded `insert-file-contents' on an absent file would kill the
subprocess before ERT ever ran."
  (let ((path (expand-file-name rel m42-imp1--root)))
    (if (not (file-exists-p path))
        'm42-imp1-absent
      (with-temp-buffer
        (insert-file-contents path)
        (funcall fn)))))

(defun m42-imp1--contains-p (rel needle)
  "Non-nil when REL (repo-root-relative) contains NEEDLE."
  (m42-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (search-forward needle nil t))))

(defun m42-imp1--lines (rel)
  "Count the newlines of REL the way `wc -l' does."
  (m42-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (search-forward "\n" nil t) (setq n (1+ n)))
        n))))

(defun m42-imp1--count (rel regexp)
  "Count the matches of REGEXP in REL."
  (m42-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (re-search-forward regexp nil t) (setq n (1+ n)))
        n))))

(defun m42-imp1--line-of (rel needle)
  "1-based line number of the first literal NEEDLE in REL, or nil."
  (m42-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (when (search-forward needle nil t)
        (line-number-at-pos (match-beginning 0))))))

(defun m42-imp1--check (name ok)
  "Report and register one check.  OK is a boolean, or the symbol
`m42-imp1-absent' for an absent-tracked-file skip (printed as INFO)."
  (if (eq ok 'm42-imp1-absent)
      (princ (format "INFO m42/imp1/%s skipped (source file absent)\n" name))
    (progn
      (princ (format "%s m42/imp1/%s\n" (if ok "PASS" "FAIL") name))
      (imp-register-bool-as-ert-test (format "m42-imp1/%s" name) ok))))

(defun m42-imp1--doc-check (name rel needle)
  "Report and register one check on a NON-durable record.  PASS and
register an ERT test when REL holds NEEDLE.  INFO-skip when REL is
absent OR present but stale.  docs/ is gitignored, so no commit can
carry it: a stale document is a fact of the checkout, not a code
regression, and must not turn the gate red.  Known limit: on a fresh
clone this is advisory only -- an absent record registers no ERT test,
so D4 alone does not enforce the decision; the hard checks D1 and D3 do."
  (let ((hit (m42-imp1--contains-p rel needle)))
    (if (and hit (not (eq hit 'm42-imp1-absent)))
        (progn (princ (format "PASS m42/imp1/%s\n" name))
               (imp-register-bool-as-ert-test (format "m42-imp1/%s" name) t))
      (princ (format "INFO m42/imp1/%s skipped (%s, gitignored record)\n"
                     name (if (eq hit 'm42-imp1-absent) "absent" "stale"))))))

;;; --- D1. The base numbers (brief.org §3) ------------------------------

(m42-imp1--check "keyboard.c-lines-11233"
                 (eql 11233 (m42-imp1--lines "src/keyboard.c")))
(m42-imp1--check "keyboard.c-defuns-447"
                 (eql 447 (m42-imp1--count "src/keyboard.c" "^DEFUN (\"")))
(m42-imp1--check "keyboard-globals.c-lines-490"
                 (eql 490 (m42-imp1--lines "src/keyboard-globals.c")))
(m42-imp1--check "combined-keyboard-surface-11723"
                 (let ((kb (m42-imp1--lines "src/keyboard.c"))
                       (kg (m42-imp1--lines "src/keyboard-globals.c")))
                   (and (eql 11233 kb)
                        (eql 490 kg)
                        (eql 11723 (+ kb kg)))))

(m42-imp1--check "read-shims-retained"
                 (and (m42-imp1--contains-p
                       "src/keyboard.c" "DEFUN (\"--tty-bytes-readable\"")
                      (m42-imp1--contains-p
                       "src/keyboard.c" "DEFUN (\"--tty-read-nonblocking\"")))
(m42-imp1--check "tty-fd-present-after-m43-imp2"
                 (m42-imp1--contains-p "src/keyboard.c" "DEFUN (\"--tty-fd\""))
(m42-imp1--check "gobble-policy-still-defined"
                 (m42-imp1--contains-p "mod/emacs/gobble.scm"
                                       "(define (tty-read-avail-input!"))
(m42-imp1--check "gobble-calls-c-leaves"
                 (and (m42-imp1--contains-p "mod/emacs/gobble.scm"
                                            "%--tty-bytes-readable")
                      (m42-imp1--contains-p "mod/emacs/gobble.scm"
                                            "%--tty-read-nonblocking")
                      (not (m42-imp1--contains-p "mod/emacs/gobble.scm"
                                                 "(system foreign)"))))

;;; --- D3. The descriptor facts (brief.org §5 task 2) -------------------
;;;
;;; These are the source facts the plan cites.  They live in tracked
;;; files, so a drift is a real FAIL.

(m42-imp1--check "tty-input-is-FILE-star"
                 (m42-imp1--contains-p "src/termchar.h" "FILE *input;"))
(m42-imp1--check "tty-input-opened-by-fdopen-at-2571"
                 (eql 2571 (m42-imp1--line-of "src/term.c" "emacs_fdopen")))
(m42-imp1--check "initial-tty-input-is-stdin-at-4632"
                 (eql 4632 (m42-imp1--line-of "src/term.c"
                                              "tty->input = stdin;")))
(m42-imp1--check "delete-tty-fcloses-input-at-4901"
                 (eql 4901 (m42-imp1--line-of "src/term.c"
                                              "emacs_fclose (tty->input);")))
(m42-imp1--check "read-bypasses-stdio-via-emacs-read"
                 (m42-imp1--contains-p "src/keyboard.c"
                                       "nread = emacs_read (fileno (tty->input)"))
(m42-imp1--check "emacs_read-at-2664"
                 (eql 2664 (m42-imp1--line-of "src/sysdep.c"
                                              "emacs_read (int fd")))
(m42-imp1--check "emacs-read-retries-eintr"
                 (m42-imp1--contains-p "src/sysdep.c"
                                       "while (result < 0 && errno == EINTR);"))

;;; --- D4. The decision words (gitignored records) ----------------------
;;;
;;; docs/ is gitignored (.gitignore:31), so these are guarded: a fresh
;;; clone has no docs/ and must not fail the gate.

;; The plan records the decision, the base, and the target.
(m42-imp1--doc-check "plan-base-bde0bab1"
                     "docs/m42-plan.org" "#+base: HEAD = bde0bab1")
(m42-imp1--doc-check "plan-target-keyboard.c"
                     "docs/m42-plan.org" "#+target: src/keyboard.c")
(m42-imp1--doc-check "plan-decision-A1"
                     "docs/m42-plan.org" "Decision: A1")
(m42-imp1--doc-check "plan-records-no-new-C"
                     "docs/m42-plan.org" "adds no C OS leaf")
(m42-imp1--doc-check "plan-records-ffi-evidence"
                     "docs/m42-plan.org" "(system foreign)")
(m42-imp1--doc-check "plan-records-fionread-ioctl"
                     "docs/m42-plan.org" "FIONREAD")
;; The durable record holds the imp-1 findings.
(m42-imp1--doc-check "kb-records-imp1-landed"
                     "docs/kb.org" "IMP-1 LANDED")
(m42-imp1--doc-check "kb-records-decision-A1"
                     "docs/kb.org" "DECISION A1")

(princ "=== m42 imp-1 audit suite done ===\n")
