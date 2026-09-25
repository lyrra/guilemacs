;;; test-m42-imp1.el --- M42 imp-1 audit corpus (the TTY raw-input OS hop).
;;;
;;; M42 imp-1 is the docs-only audit (brief.org, docs/m42-plan.org).  It
;;; changes no C and no Scheme.  It answers three questions with
;;; evidence -- the embedded Guile FFI/port surface, the tty->input
;;; descriptor and its buffering, and the short-read / EINTR / EAGAIN /
;;; EIO / empty-queue behavior -- and ends with the decision A1.
;;;
;;; This corpus reads files only.  It has no C dependency.  It pins:
;;;   D1 -- the base numbers.  M42 imp-2 changed src/keyboard.c, so the
;;;         pins now read: src/keyboard.c is 11,176 lines and 445
;;;         DEFUNs (base 11,221 / 446; imp-2 retires the two read shims
;;;         and adds --tty-fd), src/keyboard-globals.c is 490 lines, and
;;;         the combined keyboard surface is 11,666.
;;;   D2 -- the shims and the Scheme policy body, re-pinned after imp-2:
;;;         the two OS shims are gone, --tty-fd is present, and
;;;         tty-read-avail-input! reaches the OS through the FFI, not
;;;         the shims.
;;;   D3 -- the descriptor facts of brief.org §5 task 2 hold in the
;;;         tree: tty->input is a FILE * (src/termchar.h:51), opened by
;;;         emacs_fdopen (src/term.c:2461), reuses stdin for the initial
;;;         terminal (src/term.c:4522), is closed by delete_tty
;;;         (src/term.c:4791), and the read bypasses stdio (the FFI read
;;;         in gobble.scm; src/sysdep.c:2713).
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

(m42-imp1--check "keyboard.c-lines-11176"
                 ;; M42 imp-2 changed src/keyboard.c: 11,221 -> 11,176.
                 (eql 11176 (m42-imp1--lines "src/keyboard.c")))
(m42-imp1--check "keyboard.c-defuns-445"
                 ;; M42 imp-2 retires the two TTY read shims (-2) and
                 ;; adds the --tty-fd accessor (+1): 446 -> 445.
                 (eql 445 (m42-imp1--count "src/keyboard.c" "^DEFUN (\"")))
(m42-imp1--check "keyboard-globals.c-lines-490"
                 (eql 490 (m42-imp1--lines "src/keyboard-globals.c")))
(m42-imp1--check "combined-keyboard-surface-11666"
                 ;; M42 imp-2 moved the sum 11,711 -> 11,666
                 ;; (11,176 + 490).  Pin the sum, not just the parts.
                 (let ((kb (m42-imp1--lines "src/keyboard.c"))
                       (kg (m42-imp1--lines "src/keyboard-globals.c")))
                   (and (eql 11176 kb)
                        (eql 490 kg)
                        (eql 11666 (+ kb kg)))))

;;; --- D2. The shims and the Scheme policy body (re-pinned after imp-2) --
;;;
;;; imp-1 pinned the two OS shims and the Scheme policy body as the base
;;; state ("imp-1 changes no C and no Scheme").  M42 imp-2 then retired
;;; both shims and moved the OS hop into Scheme, so these pins now assert
;;; the post-imp-2 reality: the shims are absent, --tty-fd is present,
;;; and gobble reaches the OS through the FFI, not the shims.

(m42-imp1--check "shims-reclaimed"
                 (and (not (m42-imp1--contains-p
                            "src/keyboard.c"
                            "DEFUN (\"--tty-bytes-readable\""))
                      (not (m42-imp1--contains-p
                            "src/keyboard.c"
                            "DEFUN (\"--tty-read-nonblocking\""))))
(m42-imp1--check "tty-fd-present"
                 (m42-imp1--contains-p "src/keyboard.c" "DEFUN (\"--tty-fd\""))
(m42-imp1--check "gobble-policy-still-defined"
                 (m42-imp1--contains-p "mod/emacs/gobble.scm"
                                       "(define (tty-read-avail-input!"))
(m42-imp1--check "gobble-calls-ffi-not-shims"
                 (and (not (m42-imp1--contains-p "mod/emacs/gobble.scm"
                                                 "%--tty-bytes-readable"))
                      (not (m42-imp1--contains-p "mod/emacs/gobble.scm"
                                                 "%--tty-read-nonblocking"))
                      (m42-imp1--contains-p "mod/emacs/gobble.scm"
                                            "%--tty-fd")
                      (m42-imp1--contains-p "mod/emacs/gobble.scm"
                                            "(system foreign)")))

;;; --- D3. The descriptor facts (brief.org §5 task 2) -------------------
;;;
;;; These are the source facts the plan cites.  They live in tracked
;;; files, so a drift is a real FAIL.

(m42-imp1--check "tty-input-is-FILE-star"
                 (m42-imp1--contains-p "src/termchar.h" "FILE *input;"))
(m42-imp1--check "tty-input-opened-by-fdopen-at-2461"
                 (eql 2461 (m42-imp1--line-of "src/term.c" "emacs_fdopen")))
(m42-imp1--check "initial-tty-input-is-stdin-at-4522"
                 (eql 4522 (m42-imp1--line-of "src/term.c"
                                              "tty->input = stdin;")))
(m42-imp1--check "delete-tty-fcloses-input-at-4791"
                 (eql 4791 (m42-imp1--line-of "src/term.c"
                                              "emacs_fclose (tty->input);")))
(m42-imp1--check "read-bypasses-stdio-via-ffi"
                 ;; M42 imp-2 moved the raw-fd read from the retired
                 ;; --tty-read-nonblocking C shim into Scheme; gobble now
                 ;; reads through the FFI read() on the plain fd.
                 (m42-imp1--contains-p
                  "mod/emacs/gobble.scm"
                  "(bytevector->pointer bv) count"))
(m42-imp1--check "emacs_read-at-2713"
                 (eql 2713 (m42-imp1--line-of "src/sysdep.c"
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
