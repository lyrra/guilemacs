;;; test-m43-imp1.el --- M43 imp-1 audit corpus (the src/sysdep.c terminal mode).
;;;
;;; M43 imp-1 is the docs-only audit (brief.org, docs/m43-plan.org).  It
;;; changes no C and no Scheme.  It answers three questions with
;;; evidence -- the block map of src/sysdep.c, the class of each block,
;;; and the module name -- and records the decision A1: Scheme computes
;;; the wanted terminal mode as plain values, and two typed C leaves
;;; apply it (the leaves are in imp-2).
;;;
;;; This corpus reads files only.  It has no C dependency.  It pins:
;;;   D1 -- the base numbers, re-measured at M43 imp-5 (this corpus tracks
;;;         the current tree surface across the imps): src/sysdep.c is
;;;         4,950 lines and 7 DEFUNs (imp-2 added the two termios leaves;
;;;         imp-3 added the --tty-mode-constants DEFUN and the
;;;         init_tty_mode dispatcher; imp-4 added the --tty-flow-unlock
;;;         DEFUN and three dispatchers; imp-5 added the --tty-get-size /
;;;         --tty-set-size DEFUNs and two dispatchers, and deleted the
;;;         dropped-platform arms -- the deleted arms shrank the file, so
;;;         the function map below moved up as well as down);
;;;         src/keyboard.c is 11,233 lines and 447 DEFUNs (the --tty-fd
;;;         accessor was added); src/keyboard-globals.c is 490 lines;
;;;         the combined keyboard surface is 11,723; src/process.c is
;;;         9,030 lines and 50 DEFUNs; src/xdisp.c is 38,990 lines and
;;;         24 DEFUNs; scm_c_public_ref over src/*.[chm] is 193 (imp-3
;;;         added one site; imp-4 added three; imp-5 added two); and
;;;         mod/emacs/gobble.scm is 303 lines.
;;;   D2 -- the src/sysdep.c function map and the termios / ioctl sites.
;;;         These are facts in a tracked file, so a drift is a real FAIL.
;;;   D3 -- the imp-2 leaf shape words in docs/m43-plan.org.
;;;   D4 -- the decision words in the gitignored records docs/m43-plan.org
;;;         and docs/kb.org.  docs/ is gitignored, so a present-but-stale
;;;         record is an INFO-skip, not a FAIL; an absent record is also
;;;         a skip.  Known limit: D3 and D4 are advisory only -- on a
;;;         fresh clone (no docs/) they register no ERT test, so they
;;;         cannot turn this gate red; the hard checks D1 and D2 do.
;;;
;;; Each tracked-file check is printed as a PASS/FAIL line and turned
;;; into an ERT test so the harness counts it.  A read error is a real
;;; error, never a silent pass.  The corpus holds its own copy of every
;;; number it pins (brief.org §3 and §4).

(princ "=== m43 imp-1 audit suite ===\n")

(require 'imp-ert-report)

(defvar m43-imp1--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))

(defun m43-imp1--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
the symbol `m43-imp1-absent' when REL does not exist.  docs/ is
gitignored, so a checkout without it must not crash the subprocess: an
unguarded `insert-file-contents' on an absent file would kill the
subprocess before ERT ever ran."
  (let ((path (expand-file-name rel m43-imp1--root)))
    (if (not (file-exists-p path))
        'm43-imp1-absent
      (with-temp-buffer
        (insert-file-contents path)
        (funcall fn)))))

(defun m43-imp1--contains-p (rel needle)
  "Non-nil when REL (repo-root-relative) contains NEEDLE."
  (m43-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (search-forward needle nil t))))

(defun m43-imp1--lines (rel)
  "Count the newlines of REL the way `wc -l' does."
  (m43-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (search-forward "\n" nil t) (setq n (1+ n)))
        n))))

(defun m43-imp1--count (rel regexp)
  "Count the matches of REGEXP in REL."
  (m43-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (re-search-forward regexp nil t) (setq n (1+ n)))
        n))))

(defun m43-imp1--line-of (rel needle)
  "1-based line number of the first literal NEEDLE in REL, or nil."
  (m43-imp1--with rel
    (lambda ()
      (goto-char (point-min))
      (when (search-forward needle nil t)
        (line-number-at-pos (match-beginning 0))))))

(defun m43-imp1--count-scm-ref ()
  "Count scm_c_public_ref over src/*.[chm] (the brief.org §3 measure)."
  (let ((total 0)
        (dir (expand-file-name "src" m43-imp1--root)))
    (dolist (f (directory-files dir t "\\.[chm]\\'"))
      (setq total (+ total (or (m43-imp1--count f "scm_c_public_ref") 0))))
    total))

(defun m43-imp1--check (name ok)
  "Report and register one check on a TRACKED file.  OK is a boolean.
The D1/D2 callers pass `(eql N value)': when the source file is absent
the reader returns the symbol `m43-imp1-absent', so `eql' yields nil and
this prints FAIL.  That is intended -- an absent src/ file is a real
error, not a pass (brief.org §6).  The `m43-imp1-absent' branch below
only fires for a caller that passes the symbol itself; D1 and D2 do not."
  (if (eq ok 'm43-imp1-absent)
      (princ (format "INFO m43/imp1/%s skipped (source file absent)\n" name))
    (progn
      (princ (format "%s m43/imp1/%s\n" (if ok "PASS" "FAIL") name))
      (imp-register-bool-as-ert-test (format "m43-imp1/%s" name) ok))))

(defun m43-imp1--doc-check (name rel needle)
  "Report and register one check on a NON-durable record.  PASS and
register an ERT test when REL holds NEEDLE.  INFO-skip when REL is
absent OR present but stale.  docs/ is gitignored, so no commit can
carry it: a stale document is a fact of the checkout, not a code
regression, and must not turn the gate red.  Known limit: on a fresh
clone this is advisory only -- an absent record registers no ERT test."
  (let ((hit (m43-imp1--contains-p rel needle)))
    (if (and hit (not (eq hit 'm43-imp1-absent)))
        (progn (princ (format "PASS m43/imp1/%s\n" name))
               (imp-register-bool-as-ert-test (format "m43-imp1/%s" name) t))
      (princ (format "INFO m43/imp1/%s skipped (%s, gitignored record)\n"
                     name (if (eq hit 'm43-imp1-absent) "absent" "stale"))))))

;;; --- D1. The base numbers (brief.org §3) ------------------------------

(m43-imp1--check "sysdep.c-lines-4950"
                 (eql 4950 (m43-imp1--lines "src/sysdep.c")))
(m43-imp1--check "sysdep.c-defuns-7"
                 (eql 7 (m43-imp1--count "src/sysdep.c" "^DEFUN (\"")))
(m43-imp1--check "keyboard.c-lines-11233"
                 (eql 11233 (m43-imp1--lines "src/keyboard.c")))
(m43-imp1--check "keyboard.c-defuns-447"
                 (eql 447 (m43-imp1--count "src/keyboard.c" "^DEFUN (\"")))
(m43-imp1--check "keyboard-globals.c-lines-490"
                 (eql 490 (m43-imp1--lines "src/keyboard-globals.c")))
(m43-imp1--check "combined-keyboard-surface-11723"
                 (let ((kb (m43-imp1--lines "src/keyboard.c"))
                       (kg (m43-imp1--lines "src/keyboard-globals.c")))
                   (and (eql 11233 kb)
                        (eql 490 kg)
                        (eql 11723 (+ kb kg)))))
(m43-imp1--check "process.c-lines-9030"
                 (eql 9030 (m43-imp1--lines "src/process.c")))
(m43-imp1--check "process.c-defuns-50"
                 (eql 50 (m43-imp1--count "src/process.c" "^DEFUN (\"")))
(m43-imp1--check "xdisp.c-lines-38990"
                 (eql 38990 (m43-imp1--lines "src/xdisp.c")))
(m43-imp1--check "xdisp.c-defuns-24"
                 (eql 24 (m43-imp1--count "src/xdisp.c" "^DEFUN (\"")))
(m43-imp1--check "scm-c-public-ref-260"
                 (eql 260 (m43-imp1--count-scm-ref)))
(m43-imp1--check "gobble.scm-lines-303"
                 (eql 303 (m43-imp1--lines "mod/emacs/gobble.scm")))

;;; --- D2. The source map and the termios sites (brief.org §4) ----------
;;;
;;; These are the source facts the plan cites.  They live in tracked
;;; files, so a drift is a real FAIL.

(m43-imp1--check "emacs_get_tty-at-960"
                 (eql 960 (m43-imp1--line-of
                           "src/sysdep.c"
                           "emacs_get_tty (int fd, struct emacs_tty *settings)")))
(m43-imp1--check "emacs_set_tty-at-988"
                 (eql 988 (m43-imp1--line-of
                           "src/sysdep.c"
                           "emacs_set_tty (int fd, struct emacs_tty *settings, bool flushp)")))
(m43-imp1--check "init_all_sys_modes-at-1060"
                 (eql 1060 (m43-imp1--line-of
                            "src/sysdep.c" "init_all_sys_modes (void)")))
(m43-imp1--check "init_sys_modes-at-1114"
                 (eql 1114 (m43-imp1--line-of
                            "src/sysdep.c"
                            "init_sys_modes (struct tty_display_info *tty_out)")))
(m43-imp1--check "tabs_safe_p-at-1244"
                 (eql 1244 (m43-imp1--line-of
                            "src/sysdep.c" "tabs_safe_p (int fd)")))
(m43-imp1--check "suppress_echo_on_tty-at-1282"
                 (eql 1282 (m43-imp1--line-of
                            "src/sysdep.c" "suppress_echo_on_tty (int fd)")))
(m43-imp1--check "get_tty_size-at-1342"
                 (eql 1342 (m43-imp1--line-of
                            "src/sysdep.c"
                            "get_tty_size (int fd, int *widthp, int *heightp)")))
(m43-imp1--check "set_window_size-at-1356"
                 (eql 1356 (m43-imp1--line-of
                            "src/sysdep.c"
                            "set_window_size (int fd, int height, int width)")))
(m43-imp1--check "reset_all_sys_modes-at-1366"
                 (eql 1366 (m43-imp1--line-of
                            "src/sysdep.c" "reset_all_sys_modes (void)")))
(m43-imp1--check "reset_sys_modes-at-1404"
                 (eql 1404 (m43-imp1--line-of
                            "src/sysdep.c"
                            "reset_sys_modes (struct tty_display_info *tty_out)")))
(m43-imp1--check "setup_pty-at-1492"
                 (eql 1492 (m43-imp1--line-of
                            "src/sysdep.c" "setup_pty (int fd)")))

(m43-imp1--check "tcgetattr-site-978"
                 (eql 978 (m43-imp1--line-of
                           "src/sysdep.c"
                           "return tcgetattr (fd, &settings->main)")))
(m43-imp1--check "tcsetattr-site-1017"
                 (eql 1017 (m43-imp1--line-of
                            "src/sysdep.c"
                            "if (tcsetattr (fd, flushp ? TCSAFLUSH")))
(m43-imp1--check "tcxonc-arm-4752"
                 (eql 4752 (m43-imp1--line-of
                            "src/sysdep.c"
                            "ioctl (ifd, TCXONC, 1)")))
(m43-imp1--check "tiocstart-arm-4756"
                 (eql 4756 (m43-imp1--line-of
                            "src/sysdep.c"
                            "ioctl (ifd, TIOCSTART, 0)")))
(m43-imp1--check "tiocgwinsz-site-4792"
                 (eql 4792 (m43-imp1--line-of
                            "src/sysdep.c" "ioctl (ifd, TIOCGWINSZ")))
(m43-imp1--check "tiocgsize-site-4802"
                 (eql 4802 (m43-imp1--line-of
                            "src/sysdep.c" "ioctl (ifd, TIOCGSIZE")))
(m43-imp1--check "tiocswinsz-site-4834"
                 (eql 4834 (m43-imp1--line-of
                            "src/sysdep.c" "ioctl (ifd, TIOCSWINSZ")))
(m43-imp1--check "systty-emacs-tty-struct-75"
                 (eql 75 (m43-imp1--line-of
                          "src/systty.h" "struct emacs_tty {")))
(m43-imp1--check "systty-emacs-get-tty-decl-87"
                 (eql 87 (m43-imp1--line-of
                          "src/systty.h"
                          "extern int emacs_get_tty (int, struct emacs_tty *)")))
(m43-imp1--check "systty-emacs-set-tty-decl-88"
                 (eql 88 (m43-imp1--line-of
                          "src/systty.h"
                          "extern int emacs_set_tty (int, struct emacs_tty *, bool)")))
(m43-imp1--check "sysdep-termios-sites-14"
                 (eql 14 (m43-imp1--count
                          "src/sysdep.c"
                          "tcgetattr\\|tcsetattr\\|struct termios")))

;;; --- D3. The imp-2 leaf shape words (gitignored plan) ----------------
;;;
;;; The plan must name the imp-2 leaf shape.  docs/ is gitignored, so a
;;; fresh clone has no plan and these are guarded INFO-skips.

(m43-imp1--doc-check "plan-leaf-get-mode"
                     "docs/m43-plan.org" "(tty-get-mode fd)")
(m43-imp1--doc-check "plan-leaf-set-mode"
                     "docs/m43-plan.org" "(tty-set-mode fd mode flush?)")
(m43-imp1--doc-check "plan-leaf-fd-is-plain-int"
                     "docs/m43-plan.org" "fd is a plain int")

;;; --- D4. The decision words (gitignored records) ----------------------
;;;
;;; docs/ is gitignored (.gitignore:31), so these are guarded: a fresh
;;; clone has no docs/ and must not fail the gate.

;; The plan records the base, the target, and the decision.
(m43-imp1--doc-check "plan-base-eacd92e20"
                     "docs/m43-plan.org" "#+base: HEAD = eacd92e20")
(m43-imp1--doc-check "plan-target-sysdep.c"
                     "docs/m43-plan.org" "#+target: src/sysdep.c")
(m43-imp1--doc-check "plan-decision-A1"
                     "docs/m43-plan.org" "Decision: A1")
;; The durable record holds the imp-1 findings and the decision.
(m43-imp1--doc-check "kb-records-imp1-landed"
                     "docs/kb.org" "IMP-1 LANDED")
(m43-imp1--doc-check "kb-records-decision-A1"
                     "docs/kb.org" "DECISION A1")

(princ "=== m43 imp-1 audit suite done ===\n")
