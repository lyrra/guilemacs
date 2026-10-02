;;; test-m43-imp6.el --- M43 imp-6 close-out corpus: re-measure and record.
;;;
;;; M43 imp-6 adds no C and no Scheme.  It re-measures the surface, runs
;;; the gates, and records.  This corpus pins the end state against the
;;; tree, so a stale number, a moved line, or a missing record fails the
;;; run.  It reads files only; it has no git, no pty and no
;;; built-src/emacs dependency, so it runs on every host (brief.org
;;; section 10.2).
;;;
;;; It covers:
;;;   S1 -- the surface of brief.org section 3: src/sysdep.c is 4,950
;;;         lines / 7 DEFUNs; src/keyboard.c is 11,233 / 447;
;;;         src/keyboard-globals.c is 490; the combined keyboard surface
;;;         is 11,723, margin 237 under the 11,960 M31 budget; tree-wide
;;;         scm_c_public_ref over src/*.[chm] is 187; mod/emacs/tty-modes.scm
;;;         is 313.
;;;   S2 -- the line map of brief.org section 4, pinned with grep.
;;;   S3' -- the tracked close-out record test/m43/test-m43-imp6-closeout.org
;;;         is present and agrees with the surface (brief.org section 10.1).
;;;   S5 -- the (m43) group in tool/run-tests.scm holds the imp-6 line.
;;;
;;; S3 and S4 of brief.org section 12.1 are gone.  S4 (the three pty
;;; drivers are in the git index) and the matching git-index check on the
;;; close-out record asserted a property of the working tree, not of
;;; guilemacs, and failed on any tree without a .git.  S3 grepped bare
;;; digit strings out of the hand-written record, which pins prose, not
;;; behaviour; most of its needles ("7", "447", "237") were substrings
;;; that almost any numeric document satisfies.  S1 measures the same
;;; numbers against the source itself, which is the real check.  S3'
;;; keeps the tracked-file pin that brief.org section 10.1 requires: it
;;; reads whole lines of the tracked close-out record.  S5 keeps its
;;; number so the brief.org section 12.1 labels still line up.
;;;
;;; Each check is printed as a PASS/FAIL line and turned into an ERT test
;;; so the harness counts it.  A read error is a real error, never a
;;; silent pass.

(princ "=== m43 imp-6 close-out suite ===\n")

(require 'imp-ert-report)

(defvar m43-imp6--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))

(defun m43-imp6--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
the symbol `m43-imp6-absent' when REL does not exist."
  (let ((path (expand-file-name rel m43-imp6--root)))
    (if (not (file-exists-p path))
        'm43-imp6-absent
      (with-temp-buffer
        (insert-file-contents path)
        (funcall fn)))))

(defun m43-imp6--contains-p (rel needle)
  "Non-nil when REL (repo-root-relative) contains NEEDLE."
  (m43-imp6--with rel
    (lambda ()
      (goto-char (point-min))
      (search-forward needle nil t))))

(defun m43-imp6--lines (rel)
  "Count the newlines of REL the way `wc -l' does."
  (m43-imp6--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (search-forward "\n" nil t) (setq n (1+ n)))
        n))))

(defun m43-imp6--count (rel regexp)
  "Count the matches of REGEXP in REL."
  (m43-imp6--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (re-search-forward regexp nil t) (setq n (1+ n)))
        n))))

(defun m43-imp6--line-of (rel regexp)
  "1-based line of the first REGEXP match in REL, or nil."
  (m43-imp6--with rel
    (lambda ()
      (goto-char (point-min))
      (when (re-search-forward regexp nil t)
        (line-number-at-pos (match-beginning 0))))))

(defun m43-imp6--count-scm-ref ()
  "Count scm_c_public_ref over src/*.[chm] (the brief.org section 3 measure)."
  (let ((total 0)
        (dir (expand-file-name "src" m43-imp6--root)))
    (dolist (f (directory-files dir t "\\.[chm]\\'"))
      (setq total (+ total (or (m43-imp6--count f "scm_c_public_ref") 0))))
    total))

(defun m43-imp6--check (name ok)
  "Report and register one check.  An absent source file yields a FAIL
(an absent src/ file is a real error, not a pass)."
  (if (eq ok 'm43-imp6-absent)
      (progn
        (princ (format "FAIL m43/imp6/%s (source file absent)\n" name))
        (imp-register-bool-as-ert-test (format "m43-imp6/%s" name) nil))
    (progn
      (princ (format "%s m43/imp6/%s\n" (if ok "PASS" "FAIL") name))
      (imp-register-bool-as-ert-test (format "m43-imp6/%s" name)
                                     (and ok t)))))

;;; --- S1. The surface (brief.org section 3) ---------------------------

(m43-imp6--check "surface/sysdep.c-lines-4950"
                 (eql 4950 (m43-imp6--lines "src/sysdep.c")))
(m43-imp6--check "surface/sysdep.c-defuns-7"
                 (eql 7 (m43-imp6--count "src/sysdep.c" "^DEFUN (\"")))
(m43-imp6--check "surface/keyboard.c-lines-11233"
                 (eql 11233 (m43-imp6--lines "src/keyboard.c")))
(m43-imp6--check "surface/keyboard.c-defuns-447"
                 (eql 447 (m43-imp6--count "src/keyboard.c" "^DEFUN (\"")))
(m43-imp6--check "surface/keyboard-globals.c-lines-490"
                 (eql 490 (m43-imp6--lines "src/keyboard-globals.c")))
(m43-imp6--check "surface/combined-11723-margin-237"
                 (let ((k (m43-imp6--lines "src/keyboard.c"))
                       (kg (m43-imp6--lines "src/keyboard-globals.c")))
                   (and (integerp k) (integerp kg)
                        (eql 11723 (+ k kg))
                        (eql 237 (- 11960 (+ k kg))))))
(m43-imp6--check "surface/scm-c-public-ref-187"
                 (eql 187 (m43-imp6--count-scm-ref)))
(m43-imp6--check "surface/tty-modes.scm-lines-313"
                 (eql 313 (m43-imp6--lines "mod/emacs/tty-modes.scm")))

;;; --- S2. The line map (brief.org section 4) --------------------------

(m43-imp6--check "line/init_sys_modes-1114"
                 (eql 1114 (m43-imp6--line-of "src/sysdep.c" "^init_sys_modes ")))
(m43-imp6--check "line/tabs_safe_p-1244"
                 (eql 1244 (m43-imp6--line-of "src/sysdep.c" "^tabs_safe_p ")))
(m43-imp6--check "line/suppress_echo_on_tty-1282"
                 (eql 1282 (m43-imp6--line-of "src/sysdep.c" "^suppress_echo_on_tty ")))
(m43-imp6--check "line/get_tty_size_policy-1293"
                 (eql 1293 (m43-imp6--line-of "src/sysdep.c" "^get_tty_size_policy ")))
(m43-imp6--check "line/set_window_size_policy-1321"
                 (eql 1321 (m43-imp6--line-of "src/sysdep.c" "^set_window_size_policy ")))
(m43-imp6--check "line/get_tty_size-1342"
                 (eql 1342 (m43-imp6--line-of "src/sysdep.c" "^get_tty_size ")))
(m43-imp6--check "line/set_window_size-1356"
                 (eql 1356 (m43-imp6--line-of "src/sysdep.c" "^set_window_size ")))
(m43-imp6--check "line/reset_sys_modes-1404"
                 (eql 1404 (m43-imp6--line-of "src/sysdep.c" "^reset_sys_modes ")))
(m43-imp6--check "line/setup_pty-1492"
                 (eql 1492 (m43-imp6--line-of "src/sysdep.c" "^setup_pty ")))
(m43-imp6--check "line/emacs_full_write-2700"
                 (eql 2700 (m43-imp6--line-of "src/sysdep.c" "^emacs_full_write ")))
(m43-imp6--check "line/tty-fd-keyboard.c-10431"
                 (eql 10431 (m43-imp6--line-of "src/keyboard.c"
                                               "^DEFUN (\"--tty-fd\"")))
(m43-imp6--check "line/tty-get-mode-4651"
                 (eql 4651 (m43-imp6--line-of "src/sysdep.c"
                                              "^DEFUN (\"--tty-get-mode\"")))
(m43-imp6--check "line/tty-set-mode-4682"
                 (eql 4682 (m43-imp6--line-of "src/sysdep.c"
                                              "^DEFUN (\"--tty-set-mode\"")))
(m43-imp6--check "line/tty-flow-unlock-4740"
                 (eql 4740 (m43-imp6--line-of "src/sysdep.c"
                                              "^DEFUN (\"--tty-flow-unlock\"")))
(m43-imp6--check "line/tty-get-size-4777"
                 (eql 4777 (m43-imp6--line-of "src/sysdep.c"
                                              "^DEFUN (\"--tty-get-size\"")))
(m43-imp6--check "line/tty-set-size-4813"
                 (eql 4813 (m43-imp6--line-of "src/sysdep.c"
                                              "^DEFUN (\"--tty-set-size\"")))
(m43-imp6--check "line/tty-mode-constants-4851"
                 (eql 4851 (m43-imp6--line-of "src/sysdep.c"
                                              "^DEFUN (\"--tty-mode-constants\"")))

;;; --- S5. The (m43) group holds the imp-6 line ------------------------

(m43-imp6--check "reg/m43-group-has-imp6"
                 (m43-imp6--contains-p "tool/run-tests.scm"
                                       "test/m43/test-m43-imp6.el"))

;;; --- S3'. The tracked close-out record (brief.org section 10.1) ------
;;;
;;; A FAIL-able check must read a *tracked* file (brief.org section
;;; 10.1).  test/m43/test-m43-imp6-closeout.org lives under test/, so a
;;; commit carries it.  These checks pin it: a missing record is a real
;;; FAIL, never a silent pass.  S3 of brief.org section 12.1 (bare digit
;;; greps out of the record) stays dropped; these read whole lines that
;;; agree with the surface S1 measures against the source.

(m43-imp6--check "record/closeout-present"
                 (m43-imp6--contains-p "test/m43/test-m43-imp6-closeout.org"
                                       "M43 imp-6 close-out record (tracked)"))
(m43-imp6--check "record/surface-sysdep"
                 (m43-imp6--contains-p "test/m43/test-m43-imp6-closeout.org"
                                       "=src/sysdep.c=: 4,950 lines, 7 DEFUNs."))
(m43-imp6--check "record/surface-tty-modes"
                 (m43-imp6--contains-p "test/m43/test-m43-imp6-closeout.org"
                                       "=mod/emacs/tty-modes.scm=: 313 lines."))

;;; --- S4'. The F2 repair holds (brief.org section 5) ------------------
;;;
;;; The imp-3 / imp-4 / imp-5 corpora call pty-driver-imp3.py,
;;; pty-driver-imp4.py, and pty-driver-imp5.py a "tracked artifact".  The
;;; files live under test/, which is not gitignored, so the close-out
;;; commit carries them.  An absent driver is a real FAIL, never a
;;; silent skip.  This is not S4 of brief.org section 12.1: it reads file
;;; presence, not the git index, so it needs no git and holds on any tree
;;; that carries the drivers.

(m43-imp6--check "f2/pty-driver-imp3-present"
                 (file-exists-p (expand-file-name "test/m43/pty-driver-imp3.py"
                                                  m43-imp6--root)))
(m43-imp6--check "f2/pty-driver-imp4-present"
                 (file-exists-p (expand-file-name "test/m43/pty-driver-imp4.py"
                                                  m43-imp6--root)))
(m43-imp6--check "f2/pty-driver-imp5-present"
                 (file-exists-p (expand-file-name "test/m43/pty-driver-imp5.py"
                                                  m43-imp6--root)))

(princ "=== m43 imp-6 close-out suite done ===\n")
