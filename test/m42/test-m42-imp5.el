;;; test-m42-imp5.el --- M42 imp-5 close-out: re-measure the surface, pin the end state.
;;;
;;; M42 imp-5 adds no C and no Scheme.  It re-measures the keyboard and
;;; process surface, records the gate state, and writes the close-out
;;; record.  This corpus pins that end state against the tree, so a
;;; stale number or a missing record fails the run.  It reads files
;;; only; it has no pty and no built-src/emacs dependency, so it runs on
;;; every host.
;;;
;;; It covers:
;;;   S1 -- the surface table.  src/keyboard.c is 11,233 lines, 447
;;;         DEFUNs; src/keyboard-globals.c is 490 lines, a combined
;;;         11,723 under the 11,960 M31 budget (margin 237);
;;;         src/process.c is 9,030 lines, 50 DEFUNs; src/xdisp.c is
;;;         38,990 lines, 24 DEFUNs; tree-wide scm_c_public_ref over
;;;         src/*.[chm] is 201; mod/emacs/gobble.scm is 303 lines.
;;;         M42 moved no C line; the M42 net delta is 0.
;;;   S2 -- the two C leaf pins: --tty-bytes-readable (src/keyboard.c
;;;         line 10371) and --tty-read-nonblocking (src/keyboard.c line
;;;         10399).  M43 imp-2 re-added the --tty-fd accessor (line
;;;         10431); it now sits below the two leaves.
;;;   S3 -- the direction pins in mod/emacs/gobble.scm: no (system
;;;         foreign), no libc.so.6, and tty-read-avail-input! present.
;;;   S4 -- the five registered test files of the (m42) group in
;;;         tool/run-tests.scm: test-m42-imp1.el ... test-m42-imp5.el.
;;;   S5 -- the *tracked* close-out record
;;;         test/m42/test-m42-imp5-closeout.org: the close-out words and
;;;         the gate record.  test/ is not gitignored, so a commit CAN
;;;         carry it; a missing or stale word there is a real FAIL.
;;;
;;; Limit: this host cannot allocate a pty (os.openpty gives EACCES,
;;; errno 13), so the imp-3 / imp-4 pty cases report an environment-gated
;;; INFO skip.  This corpus does not run a pty case; it pins the files
;;; only.  The m42 gate counts a pty skip as a skip, not a pass.
;;;
;;; Each check is printed as an INFO PASS/FAIL line and turned into an
;;; ERT test so the harness counts it.  A read error is a real error,
;;; never a silent pass.

(princ "=== m42 imp-5 close-out suite ===\n")

(require 'imp-ert-report)

(defvar m42-imp5--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))

(defun m42-imp5--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
nil when REL does not exist.  Every file this corpus pins is tracked, so
an absent file means a broken checkout: every check that reads it is a
real FAIL, not an INFO-skip (brief.org section 4.1)."
  (let ((path (expand-file-name rel m42-imp5--root)))
    (when (file-exists-p path)
      (with-temp-buffer
        (insert-file-contents path)
        (funcall fn)))))

(defun m42-imp5--contains-p (rel needle)
  "Return t when REL (repo-root-relative) contains NEEDLE; else nil.
An absent REL is a real FAIL path, so return nil, never a true symbol."
  (m42-imp5--with rel
    (lambda ()
      (goto-char (point-min))
      (and (search-forward needle nil t) t))))

(defun m42-imp5--lines (rel)
  "Count the lines of REL the way `wc -l' does (newline count)."
  (m42-imp5--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (search-forward "\n" nil t) (setq n (1+ n)))
        n))))

(defun m42-imp5--count (rel regexp)
  "Count the matches of REGEXP in REL."
  (m42-imp5--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (re-search-forward regexp nil t) (setq n (1+ n)))
        n))))

(defun m42-imp5--defun-line (rel name)
  "1-based line of the `DEFUN (\"NAME\"' definition in REL, or nil."
  (m42-imp5--with rel
    (lambda ()
      (goto-char (point-min))
      (when (re-search-forward (concat "^DEFUN (\""
                                       (regexp-quote name) "\"") nil t)
        (line-number-at-pos (match-beginning 0))))))

(defun m42-imp5--check (name ok)
  "Report and register one check.  OK must be t for a PASS; nil, an
integer, or any other non-t value is a real FAIL.  A false check is a
real FAIL, not an INFO-skip (brief.org section 4.1): every file this
corpus pins is tracked, so an absent one means a broken checkout."
  (let ((pass (eq ok t)))
    (princ (format "%s m42/imp5/%s\n" (if pass "PASS" "FAIL") name))
    (imp-register-bool-as-ert-test (format "m42/imp5/%s" name) pass)))

;;; --- S1. The surface table -------------------------------------------
;;;
;;; The close-out measurement, brief.org section 3.  The combined
;;; keyboard surface did not change in M42: imp-2 restored the C leaves
;;; and retired the FFI direction, so the M42 net delta is 0 C lines.

(m42-imp5--check "surface/keyboard.c-lines-11233"
                 (eql 11233 (m42-imp5--lines "src/keyboard.c")))
(m42-imp5--check "surface/keyboard.c-defuns-447"
                 (eql 447 (m42-imp5--count "src/keyboard.c" "^DEFUN (\"")))
(m42-imp5--check "surface/keyboard-globals.c-lines-490"
                 (eql 490 (m42-imp5--lines "src/keyboard-globals.c")))
(m42-imp5--check "surface/keyboard-combined-11723"
                 (let ((k (m42-imp5--lines "src/keyboard.c"))
                       (kg (m42-imp5--lines "src/keyboard-globals.c")))
                   (and (integerp k) (integerp kg) (eql 11723 (+ k kg)))))
(m42-imp5--check "surface/keyboard-margin-237-under-11960"
                 (let ((k (m42-imp5--lines "src/keyboard.c"))
                       (kg (m42-imp5--lines "src/keyboard-globals.c")))
                   (and (integerp k) (integerp kg)
                        (eql 237 (- 11960 (+ k kg))))))
(m42-imp5--check "surface/process.c-lines-9030"
                 (eql 9030 (m42-imp5--lines "src/process.c")))
(m42-imp5--check "surface/process.c-defuns-50"
                 (eql 50 (m42-imp5--count "src/process.c" "^DEFUN (\"")))
(m42-imp5--check "surface/xdisp.c-lines-38990"
                 (eql 38990 (m42-imp5--lines "src/xdisp.c")))
(m42-imp5--check "surface/xdisp.c-defuns-24"
                 (eql 24 (m42-imp5--count "src/xdisp.c" "^DEFUN (\"")))
;; The tree-wide scm_c_public_ref count over src/*.c, src/*.h and
;; src/*.m, like the measurement in brief.org section 7.1.
(m42-imp5--check "surface/tree-ref-sites-230"
                 (let ((files (directory-files (expand-file-name "src" m42-imp5--root)
                                               t "\\.\\(c\\|h\\|m\\)\\'")))
                   (and (consp files)
                        (eql 230
                             (let ((n 0))
                               (dolist (f files)
                                 (with-temp-buffer
                                   (insert-file-contents f)
                                   (goto-char (point-min))
                                   (while (re-search-forward "scm_c_public_ref" nil t)
                                     (setq n (1+ n)))))
                               n)))))
(m42-imp5--check "surface/gobble.scm-lines-303"
                 (eql 303 (m42-imp5--lines "mod/emacs/gobble.scm")))

;;; --- S2. The two C leaf pins -----------------------------------------
;;; The OS hop stays in the two typed C leaves.  Pin the name and the
;;; line number of each DEFUN line.  (M43 imp-2 added the --tty-fd
;;; accessor below the two leaves; the leaf lines above did not move.)

(m42-imp5--check "pin/leaf/tty-bytes-readable-10371"
                 (eql 10371 (m42-imp5--defun-line "src/keyboard.c"
                                                  "--tty-bytes-readable")))
(m42-imp5--check "pin/leaf/tty-read-nonblocking-10399"
                 (eql 10399 (m42-imp5--defun-line "src/keyboard.c"
                                                  "--tty-read-nonblocking")))
(m42-imp5--check "presence/tty-fd-in-keyboard.c-after-m43-imp2"
                 (let ((n (m42-imp5--count "src/keyboard.c"
                                           "DEFUN (\"--tty-fd\"")))
                   (and (integerp n) (eql n 1))))

;;; --- S3. The direction pins in (emacs gobble) ------------------------
;;; Scheme owns the read policy.  The FFI direction is retired: no
;;; (system foreign), no libc.so.6.  tty-read-avail-input! is present.

(m42-imp5--check "direction/no-system-foreign-or-libc"
                 (eql 0 (m42-imp5--count "mod/emacs/gobble.scm"
                                         "system foreign\\|libc\\.so\\.6")))
(m42-imp5--check "direction/tty-read-avail-input!-present"
                 (let ((n (m42-imp5--count "mod/emacs/gobble.scm"
                                           "tty-read-avail-input!")))
                   (and (integerp n) (> n 0))))

;;; --- S4. The corpus is registered in run-tests.scm -------------------
;;; The (m42) group must hold the five imp names.

(dolist (imp '("imp1" "imp2" "imp3" "imp4" "imp5"))
  (m42-imp5--check (format "registered/%s-in-run-tests.scm" imp)
                   (and (m42-imp5--contains-p
                         "tool/run-tests.scm"
                         (format "\"test/m42/test-m42-%s.el\"" imp))
                        t)))

;;; --- S5. The tracked close-out record --------------------------------
;;;
;;; test/ is tracked, so a commit can carry
;;; test/m42/test-m42-imp5-closeout.org.  A missing or stale word is a
;;; real FAIL, not an INFO-skip.  This is what makes the close-out
;;; verifiable from a clean checkout.  Do not pin docs/ or
;;; milestone.org: both are outside git, so a pin on them turns the
;;; gate red on a fresh clone (the m40-imp5-closeout-record-untracked
;;; lesson).

(defun m42-imp5--tracked-has (needle)
  "Non-nil only when the *tracked* close-out record exists AND holds
NEEDLE.  Unlike an INFO-skip path, an absent file is NOT forgiven."
  (and (m42-imp5--contains-p "test/m42/test-m42-imp5-closeout.org" needle)
       t))

;; The close-out words of brief.org section 4.2.
(m42-imp5--check "closeout/words/m42-closed"
                 (m42-imp5--tracked-has "M42: CLOSED 2026-09-28"))
(m42-imp5--check "closeout/words/imp-5-close-out"
                 (m42-imp5--tracked-has "imp-5 (close-out)"))
(m42-imp5--check "closeout/words/keyboard-lines"
                 (m42-imp5--tracked-has "11,233 lines"))
(m42-imp5--check "closeout/words/keyboard-defuns"
                 (m42-imp5--tracked-has "447 DEFUNs"))
(m42-imp5--check "closeout/words/combined"
                 (m42-imp5--tracked-has "11,723"))
(m42-imp5--check "closeout/words/margin"
                 (m42-imp5--tracked-has "237"))

;; The gate record of brief.org section 4.2: each of the four gate names
;; with an exit status and a pass/fail count.
(m42-imp5--check "closeout/gate/m42"
                 (m42-imp5--tracked-has "m42: exit 0; 113 pass / 0 fail"))
(m42-imp5--check "closeout/gate/m41"
                 (m42-imp5--tracked-has "m41: exit 0; 219 pass / 0 fail"))
(m42-imp5--check "closeout/gate/m40"
                 (m42-imp5--tracked-has "m40: exit 0; 322 pass / 0 fail"))
(m42-imp5--check "closeout/gate/m39"
                 (m42-imp5--tracked-has "m39: exit 0; 255 pass / 0 fail"))

(princ "=== m42 imp-5 close-out suite done ===\n")
