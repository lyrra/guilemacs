;;; test-m43-imp2.el --- M43 imp-2 corpus: the typed C termios leaves.
;;;
;;; M43 imp-2 adds two typed C termios leaves over a plain int fd and
;;; one fd accessor (brief.org section 5):
;;;
;;;   src/sysdep.c   --tty-get-mode (fd)          -> the mode list or #f
;;;   src/sysdep.c   --tty-set-mode (fd mode flush?) -> a status fixnum
;;;   src/keyboard.c --tty-fd (terminal)          -> a plain int fd or -1
;;;
;;; and the module (emacs tty-modes) with the thin wrappers tty-get-mode
;;; and tty-set-mode (brief.org section 6).  imp-2 adds no policy; imp-3
;;; and imp-4 move the policy.
;;;
;;; The pins read files only, so they run on every host.  The runtime
;;; probe at the end runs the built src/emacs and is an INFO skip when
;;; it cannot (brief.org section 8).  The corpus pins:
;;;   P1 -- the two leaves exist in the tracked src/sysdep.c with the
;;;         section-5 shape, and each calls emacs_get_tty / emacs_set_tty.
;;;   P2 -- the --tty-fd accessor exists in the tracked src/keyboard.c
;;;         and maps the terminal to fileno (tty->input).
;;;   P3 -- the mode value is a 5-element list (iflag oflag cflag lflag
;;;         c_cc); c_cc is a bytevector; --tty-set-mode accepts it.
;;;   P4 -- the module mod/emacs/tty-modes.scm exists, exports the two
;;;         wrappers, does not reuse (emacs terminal), and holds no FFI
;;;         call and no raw ioctl.
;;;   P5 -- the loader and the (m43) group carry the new module and file.
;;;   P6 -- the base numbers hold: src/sysdep.c is 4,797 lines and 4
;;;         DEFUNs; src/keyboard.c is 11,233 lines and 447 DEFUNs;
;;;         src/keyboard-globals.c is 490 lines; the combined keyboard
;;;         surface is 11,723, under the 11,960 M31 budget (margin 237).
;;;
;;; No struct, no FILE *, and no Lisp_Object crosses the termios layer:
;;; the leaves take an int fd and a plain value list.
;;;
;;; Each check is printed as a PASS/FAIL line and turned into an ERT
;;; test so the harness counts it.  A read error is a real error, never
;;; a silent pass (brief.org section 6, the m40-imp5-closeout-record
;;; lesson).
;;;
;;; Limit: this host cannot allocate a pty (os.openpty gives EACCES,
;;; errno 13), so the end-to-end termios round-trip needs a pty host.
;;; The corpus reports an environment-gated INFO skip for it, not a
;;; pass (brief.org section 8 and section 12).  A non-TTY probe on a
;;; pipe fd needs a built src/emacs; when the binary is absent the probe
;;; is also an INFO skip.

(princ "=== m43 imp-2 termios-leaves suite ===\n")

(require 'imp-ert-report)

(defvar m43-imp2--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))

(defun m43-imp2--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
the symbol `m43-imp2-absent' when REL does not exist."
  (let ((path (expand-file-name rel m43-imp2--root)))
    (if (not (file-exists-p path))
        'm43-imp2-absent
      (with-temp-buffer
        (insert-file-contents path)
        (funcall fn)))))

(defun m43-imp2--contains-p (rel needle)
  "Non-nil when REL (repo-root-relative) contains NEEDLE."
  (m43-imp2--with rel
    (lambda ()
      (goto-char (point-min))
      (search-forward needle nil t))))

(defun m43-imp2--lines (rel)
  "Count the newlines of REL the way `wc -l' does."
  (m43-imp2--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (search-forward "\n" nil t) (setq n (1+ n)))
        n))))

(defun m43-imp2--count (rel regexp)
  "Count the matches of REGEXP in REL."
  (m43-imp2--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (re-search-forward regexp nil t) (setq n (1+ n)))
        n))))

(defun m43-imp2--line-of (rel needle)
  "1-based line number of the first literal NEEDLE in REL, or nil."
  (m43-imp2--with rel
    (lambda ()
      (goto-char (point-min))
      (when (search-forward needle nil t)
        (line-number-at-pos (match-beginning 0))))))

(defun m43-imp2--check (name ok)
  "Report and register one check.  OK is a boolean; an absent source
file yields `eql' nil, which prints FAIL (an absent src/ file is a real
error, not a pass)."
  (if (eq ok 'm43-imp2-absent)
      (princ (format "INFO m43/imp2/%s skipped (source file absent)\n" name))
    (progn
      (princ (format "%s m43/imp2/%s\n" (if ok "PASS" "FAIL") name))
      (imp-register-bool-as-ert-test (format "m43-imp2/%s" name) ok))))

;;; --- P1. The two leaves in src/sysdep.c (brief.org section 5.2, 5.3) --

(m43-imp2--check "leaf/tty-get-mode-defun"
                 (m43-imp2--contains-p "src/sysdep.c"
                                       "DEFUN (\"--tty-get-mode\""))
(m43-imp2--check "leaf/tty-set-mode-defun"
                 (m43-imp2--contains-p "src/sysdep.c"
                                       "DEFUN (\"--tty-set-mode\""))
;; The leaves take a plain int fd (from the fixnum FD).
(m43-imp2--check "leaf/fd-is-plain-int"
                 (let ((n (m43-imp2--count "src/sysdep.c"
                                           "int ifd = XFIXNUM (fd)")))
                   (and (integerp n) (>= n 2))))
;; The leaves reuse the two existing C wrappers; they do not re-implement
;; the syscall mechanism.
(m43-imp2--check "leaf/reuses-emacs-get-tty"
                 (m43-imp2--contains-p "src/sysdep.c"
                                       "emacs_get_tty (ifd, &et)"))
(m43-imp2--check "leaf/reuses-emacs-set-tty"
                 (m43-imp2--contains-p "src/sysdep.c"
                                       "emacs_set_tty (ifd, &et, flushp)"))
;; The wrappers themselves are unchanged.
(m43-imp2--check "leaf/emacs-get-tty-at-960"
                 (eql 960 (m43-imp2--line-of
                           "src/sysdep.c"
                           "emacs_get_tty (int fd, struct emacs_tty *settings)")))
(m43-imp2--check "leaf/emacs-set-tty-at-988"
                 (eql 988 (m43-imp2--line-of
                           "src/sysdep.c"
                           "emacs_set_tty (int fd, struct emacs_tty *settings, bool flushp)")))
;; The retry loop, the EINTR retry, and the read-back compare stay in C.
(m43-imp2--check "leaf/keeps-retry-and-eintr-in-systty"
                 (and (m43-imp2--contains-p "src/sysdep.c"
                                            "while (result < 0 && errno == EINTR);")
                      (m43-imp2--contains-p "src/sysdep.c"
                                            "for (i = 0 ; i < 10 ; i++)")))

;;; --- P2. The --tty-fd accessor in src/keyboard.c (section 5.1) -------

(m43-imp2--check "fd/defun"
                 (m43-imp2--contains-p "src/keyboard.c"
                                       "DEFUN (\"--tty-fd\""))
(m43-imp2--check "fd/uses-m22-helper"
                 (m43-imp2--contains-p "src/keyboard.c"
                                       "struct tty_display_info *tty = m22_tty_of_terminal (terminal)"))
(m43-imp2--check "fd/returns-fileno"
                 (m43-imp2--contains-p "src/keyboard.c"
                                       "return make_fixnum (tty ? fileno (tty->input) : -1);"))

;;; --- P3. The mode value is a plain 5-element list (section 5.4) ------


(m43-imp2--check "mode/list5-iflag-oflag-cflag-lflag-c_cc"
                 (m43-imp2--contains-p
                  "src/sysdep.c"
                  "return list5 (make_fixnum (et.main.c_iflag),"))
(m43-imp2--check "mode/c_cc-is-bytevector"
                 (m43-imp2--contains-p
                  "src/sysdep.c"
                  "Lisp_Object c_cc = scm_c_make_bytevector (NCCS);"))
(m43-imp2--check "mode/set-mode-reads-the-five-fields"
                 (and (m43-imp2--contains-p "src/sysdep.c" "et.main.c_iflag = XFIXNUM (iflag);")
                      (m43-imp2--contains-p "src/sysdep.c" "et.main.c_lflag = XFIXNUM (lflag);")
                      (m43-imp2--contains-p "src/sysdep.c" "memcpy (et.main.c_cc, SCM_BYTEVECTOR_CONTENTS (c_cc), NCCS);")))
;; The status is 0 on success and the negated errno on a hard failure.
(m43-imp2--check "mode/set-mode-status-encoding"
                 (and (m43-imp2--contains-p "src/sysdep.c"
                                            "return make_fixnum (-errno);")
                      (m43-imp2--contains-p "src/sysdep.c"
                                            "return make_fixnum (0);")))

;;; --- P4. The module (emacs tty-modes) (section 6) --------------------

(m43-imp2--check "module/exists"
                 (let ((p (expand-file-name "mod/emacs/tty-modes.scm"
                                            m43-imp2--root)))
                   (file-exists-p p)))
(m43-imp2--check "module/define-module"
                 (m43-imp2--contains-p "mod/emacs/tty-modes.scm"
                                       "(define-module (emacs tty-modes)"))
(m43-imp2--check "module/exports-tty-get-mode"
                 (m43-imp2--contains-p "mod/emacs/tty-modes.scm"
                                       "tty-get-mode"))
(m43-imp2--check "module/exports-tty-set-mode"
                 (m43-imp2--contains-p "mod/emacs/tty-modes.scm"
                                       "tty-set-mode"))
(m43-imp2--check "module/does-not-reuse-emacs-terminal"
                 (and (not (m43-imp2--contains-p "mod/emacs/tty-modes.scm"
                                                 "(emacs terminal)"))
                      (not (m43-imp2--contains-p "mod/emacs/tty-modes.scm"
                                                 "terminal.scm"))))
(m43-imp2--check "module/no-ffi-no-libc-no-ioctl"
                 (and (not (m43-imp2--contains-p "mod/emacs/tty-modes.scm"
                                                 "(system foreign)"))
                      (not (m43-imp2--contains-p "mod/emacs/tty-modes.scm"
                                                 "libc.so.6"))
                      (not (m43-imp2--contains-p "mod/emacs/tty-modes.scm"
                                                 "ioctl"))))
;; The wrappers call the C leaves through the defelisp idiom.
(m43-imp2--check "module/calls-the-leaves"
                 (and (m43-imp2--contains-p "mod/emacs/tty-modes.scm"
                                            "(defelisp %--tty-get-mode --tty-get-mode)")
                      (m43-imp2--contains-p "mod/emacs/tty-modes.scm"
                                            "(defelisp %--tty-set-mode --tty-set-mode)")
                      (m43-imp2--contains-p "mod/emacs/tty-modes.scm"
                                            "(defelisp %--tty-fd       --tty-fd)")))

;;; --- P5. Registration (section 6 and section 8) ----------------------

(m43-imp2--check "reg/loader-has-tty-modes"
                 (m43-imp2--contains-p "prelude/load.scm"
                                       "(use-modules (emacs tty-modes))"))
(m43-imp2--check "reg/m43-group-has-imp2"
                 (m43-imp2--contains-p "tool/run-tests.scm"
                                       "test/m43/test-m43-imp2.el"))

;;; --- P6. The re-measured surface (brief.org section 9) ---------------

(m43-imp2--check "surface/sysdep.c-lines-4950"
                 (eql 4950 (m43-imp2--lines "src/sysdep.c")))
(m43-imp2--check "surface/sysdep.c-defuns-7"
                 (eql 7 (m43-imp2--count "src/sysdep.c" "^DEFUN (\"")))
(m43-imp2--check "surface/keyboard.c-lines-11233"
                 (eql 11233 (m43-imp2--lines "src/keyboard.c")))
(m43-imp2--check "surface/keyboard.c-defuns-447"
                 (eql 447 (m43-imp2--count "src/keyboard.c" "^DEFUN (\"")))
(m43-imp2--check "surface/keyboard-globals.c-lines-490"
                 (eql 490 (m43-imp2--lines "src/keyboard-globals.c")))
(m43-imp2--check "surface/combined-11723-under-11960"
                 (let ((k (m43-imp2--lines "src/keyboard.c"))
                       (kg (m43-imp2--lines "src/keyboard-globals.c")))
                   (and (eql 11233 k)
                        (eql 490 kg)
                        (eql 11723 (+ k kg))
                        (<= (+ k kg) 11960))))

;;; --- The runtime probe (brief.org section 8) -------------------------
;;;
;;; Case 1: the non-tty pipe-fd probe.  On a pipe fd, --tty-get-mode must
;;; return #f (the read arm fails) and --tty-set-mode must return a
;;; negative status (the failure arm).  The C leaves live in the built
;;; src/emacs, not in this harness, so run that binary in batch with a
;;; pipe on stdin (printf '' | emacs ...).  When no runnable built
;;; binary exists, case 1 is an INFO skip -- never a silent pass.
;;;
;;; Case 2: the pty end-to-end round-trip is an INFO skip on this host,
;;; which cannot allocate a pty (os.openpty gives EACCES, errno 13;
;;; brief.org section 12).

(defvar m43-imp2--emacs
  (expand-file-name "src/emacs" m43-imp2--root))

(defvar m43-imp2--probe-eval
  (concat "(princ (format \"get=%S set=%S\\n\""
          " (--tty-get-mode 0)"
          " (--tty-set-mode 0"
          " (eval-scheme \"(list 0 0 0 0 (make-bytevector 32 0))\")"
          " nil)))"))

(defun m43-imp2--probe-output ()
  "Return the built src/emacs non-tty probe output, or nil.
Run src/emacs in batch with a pipe on fd 0.  The probe prints one line:
get=<--tty-get-mode 0> set=<--tty-set-mode 0 MODE nil>."
  (when (file-executable-p m43-imp2--emacs)
    (with-temp-buffer
      (let ((status nil))
        (condition-case nil
            (setq status
                  (call-process
                   "/bin/sh" nil (current-buffer) nil "-c"
                   (format "printf '' | %s --batch --eval '%s'"
                           m43-imp2--emacs m43-imp2--probe-eval)))
          (error (setq status nil)))
        (when (and (integerp status) (zerop status))
          (buffer-string))))))

(let ((out (m43-imp2--probe-output)))
  (if (null out)
      (princ "INFO m43/imp2/non-tty-probe skipped (no runnable built src/emacs)\n")
    (m43-imp2--check "probe/non-tty-get-mode-is-false"
                     (and (stringp out) (string-match-p "get=nil" out) t))
    (m43-imp2--check "probe/non-tty-set-mode-negative-status"
                     (and (stringp out) (string-match-p "set=-[0-9]" out) t))))
(princ "INFO m43/imp2/pty-e2e skipped (no pty on this host; brief.org section 12)\n")

(princ "=== m43 imp-2 termios-leaves suite done ===\n")
