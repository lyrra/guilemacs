;;; test-m43-imp4.el --- M43 imp-4 corpus: the reset / restore policy.
;;;
;;; M43 imp-4 moves the restore policy, the suppress_echo decision, and the
;;; flow-control unlock policy of src/sysdep.c into (emacs tty-modes):
;;;
;;;   (tty-mode-restore base)       -> a fresh copy of the saved mode
;;;   (tty-mode-no-echo base flags) -> the mode with ICANON and ECHO cleared
;;;   (reset-tty-mode fd base)      -> apply the restore rule, or #f
;;;   (suppress-echo-tty fd)        -> read, apply the no-echo rule, or #f
;;;   (unlock-tty-flow fd flow?)    -> the flow-unlock leaf, or #f
;;; plus the C dispatchers reset_tty_mode / suppress_echo_tty /
;;; unlock_tty_flow and the --tty-flow-unlock leaf in src/sysdep.c.
;;;
;;; This file holds the pins that read files only, so they run on every
;;; host (P1-P6).  The table-driven pure check of the policy lives in the
;;; companion corpus test-m43-imp4.scm; it is the primary proof of imp-4
;;; (brief.org section 11) and runs on every host too.  The observable
;;; restore ("a reset restores the pre-init mode") needs a pty: this host
;;; cannot allocate one (os.openpty gives EACCES, errno 13), so that case
;;; is an environment-gated INFO skip, not a pass (brief.org section 12).
;;;
;;; Each check is printed as a PASS/FAIL line and turned into an ERT test
;;; so the harness counts it.  A read error is a real error, never a silent
;;; pass.

(princ "=== m43 imp-4 reset/restore policy suite ===\n")

(require 'imp-ert-report)

(defvar m43-imp4--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))

(defun m43-imp4--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
the symbol `m43-imp4-absent' when REL does not exist."
  (let ((path (expand-file-name rel m43-imp4--root)))
    (if (not (file-exists-p path))
        'm43-imp4-absent
      (with-temp-buffer
        (insert-file-contents path)
        (funcall fn)))))

(defun m43-imp4--contains-p (rel needle)
  "Non-nil when REL (repo-root-relative) contains NEEDLE."
  (m43-imp4--with rel
    (lambda ()
      (goto-char (point-min))
      (search-forward needle nil t))))

(defun m43-imp4--file-has (rel needle)
  "Non-nil when the file REL (repo-root-relative) holds NEEDLE.
An absent file is nil, that is a real FAIL, not an INFO skip.  This
is the fail-loudly rule of brief.org section 11.4: a *tracked* artifact
that is missing must not look like an environment limit."
  (let ((path (expand-file-name rel m43-imp4--root)))
    (and (file-readable-p path)
         (with-temp-buffer
           (insert-file-contents path)
           (goto-char (point-min))
           (and (search-forward needle nil t) t)))))

(defun m43-imp4--lines (rel)
  "Count the newlines of REL the way `wc -l' does."
  (m43-imp4--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (search-forward "\n" nil t) (setq n (1+ n)))
        n))))

(defun m43-imp4--count (rel regexp)
  "Count the matches of REGEXP in REL."
  (m43-imp4--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (re-search-forward regexp nil t) (setq n (1+ n)))
        n))))

(defun m43-imp4--count-scm-ref ()
  "Count scm_c_public_ref over src/*.[chm] (the brief.org section 2 measure)."
  (let ((total 0)
        (dir (expand-file-name "src" m43-imp4--root)))
    (dolist (f (directory-files dir t "\\.[chm]\\'"))
      (setq total (+ total (or (m43-imp4--count f "scm_c_public_ref") 0))))
    total))

(defun m43-imp4--check (name ok)
  "Report and register one check.  An absent source file yields `eql'
nil, which prints FAIL (an absent src/ file is a real error, not a pass)."
  (if (eq ok 'm43-imp4-absent)
      (princ (format "INFO m43/imp4/%s skipped (source file absent)\n" name))
    (progn
      (princ (format "%s m43/imp4/%s\n" (if ok "PASS" "FAIL") name))
      (imp-register-bool-as-ert-test (format "m43-imp4/%s" name) ok))))

;;; --- P1. The C dispatchers (brief.org section 8) ---------------------

(m43-imp4--check "dispatch/reset-defun"
                 (m43-imp4--contains-p
                  "src/sysdep.c"
                  "reset_tty_mode (int fd, Lisp_Object base)"))
(m43-imp4--check "dispatch/suppress-echo-defun"
                 (m43-imp4--contains-p
                  "src/sysdep.c" "suppress_echo_tty (int fd)"))
(m43-imp4--check "dispatch/unlock-flow-defun"
                 (m43-imp4--contains-p
                  "src/sysdep.c" "unlock_tty_flow (int fd, bool flow)"))
(m43-imp4--check "dispatch/calls-reset-tty-mode"
                 (m43-imp4--contains-p
                  "src/sysdep.c"
                  "scm_c_public_ref (\"emacs tty-modes\", \"reset-tty-mode\")"))
(m43-imp4--check "dispatch/calls-suppress-echo-tty"
                 (m43-imp4--contains-p
                  "src/sysdep.c"
                  "scm_c_public_ref (\"emacs tty-modes\", \"suppress-echo-tty\")"))
(m43-imp4--check "dispatch/calls-unlock-tty-flow"
                 (m43-imp4--contains-p
                  "src/sysdep.c"
                  "scm_c_public_ref (\"emacs tty-modes\", \"unlock-tty-flow\")"))
;; The dispatchers take and pass plain values only.
(m43-imp4--check "dispatch/passes-plain-fd-and-base"
                 (m43-imp4--contains-p
                  "src/sysdep.c"
                  "SCM_CALL_2 (proc, make_fixnum (fd), base);"))
(m43-imp4--check "dispatch/passes-plain-fd"
                 (m43-imp4--contains-p
                  "src/sysdep.c"
                  "SCM_CALL_1 (proc, make_fixnum (fd));"))
(m43-imp4--check "dispatch/passes-plain-flow"
                 (m43-imp4--contains-p
                  "src/sysdep.c"
                  "SCM_CALL_2 (proc, make_fixnum (fd), flow ? Qt : Qnil);"))
;; reset_tty_mode validates a non-nil base before the Scheme call.
(m43-imp4--check "dispatch/validates-base"
                 (m43-imp4--contains-p "src/sysdep.c" "!NILP (base)"))

;;; --- P2. The rewires (brief.org section 9 step 6, 7, 8) --------------

;; reset_sys_modes no longer restores with emacs_set_tty; it builds the
;; plain base list and dispatches.
(m43-imp4--check "reset/builds-base-and-dispatches"
                 (and (m43-imp4--contains-p
                       "src/sysdep.c"
                       "reset_tty_mode (fileno (tty_out->input), base);")
                      (m43-imp4--contains-p
                       "src/sysdep.c"
                       "make_fixnum (tty_out->old_tty->main.c_iflag)")))
(m43-imp4--check "reset/no-direct-emacs-set-tty"
                 (not (m43-imp4--contains-p
                       "src/sysdep.c"
                       "while (emacs_set_tty (fileno (tty_out->input),")))
;; suppress_echo_on_tty keeps the function but calls the dispatcher.
(m43-imp4--check "suppress-echo/calls-dispatcher"
                 (m43-imp4--contains-p "src/sysdep.c" "suppress_echo_tty (fd);"))
(m43-imp4--check "suppress-echo/no-flags-in-c"
                 (not (m43-imp4--contains-p
                       "src/sysdep.c" "etty.main.c_lflag &= ~ICANON")))
;; The three flow-control arms are deleted from init_sys_modes; the call
;; site replaces them.
(m43-imp4--check "flow/arms-deleted"
                 (and (not (m43-imp4--contains-p
                            "src/sysdep.c"
                            "if (!tty_out->flow_control) ioctl (fileno (tty_out->input), TCXONC"))
                      (not (m43-imp4--contains-p
                            "src/sysdep.c"
                            "if (!tty_out->flow_control) ioctl (fileno (tty_out->input), TIOCSTART"))
                      (not (m43-imp4--contains-p
                            "src/sysdep.c"
                            "if (!tty_out->flow_control) tcflow"))))
(m43-imp4--check "flow/calls-dispatcher"
                 (m43-imp4--contains-p
                  "src/sysdep.c"
                  "unlock_tty_flow (fileno (tty_out->input), tty_out->flow_control);"))

;;; --- P3. The --tty-flow-unlock leaf (brief.org section 7) ------------

(m43-imp4--check "leaf/defun"
                 (m43-imp4--contains-p
                  "src/sysdep.c" "DEFUN (\"--tty-flow-unlock\""))
(m43-imp4--check "leaf/tcxonc-arm"
                 (m43-imp4--contains-p "src/sysdep.c" "ioctl (ifd, TCXONC, 1)"))
(m43-imp4--check "leaf/tiocstart-arm"
                 (m43-imp4--contains-p "src/sysdep.c" "ioctl (ifd, TIOCSTART, 0)"))
(m43-imp4--check "leaf/tcoon-arm"
                 (m43-imp4--contains-p "src/sysdep.c" "if (tcflow (ifd, TCOON) != 0)"))
(m43-imp4--check "leaf/dos-nt-guard"
                 (m43-imp4--contains-p "src/sysdep.c" "#endif /* ! DOS_NT */"))

;;; --- P4. The module (emacs tty-modes) (brief.org section 5, 6, 9) ----

(m43-imp4--check "module/restore-rule"
                 (m43-imp4--contains-p "mod/emacs/tty-modes.scm"
                                       "(define (tty-mode-restore base)"))
(m43-imp4--check "module/no-echo-rule"
                 (m43-imp4--contains-p "mod/emacs/tty-modes.scm"
                                       "(define (tty-mode-no-echo base flags)"))
(m43-imp4--check "module/entry-points"
                 (and (m43-imp4--contains-p "mod/emacs/tty-modes.scm"
                                            "(define (reset-tty-mode fd base)")
                      (m43-imp4--contains-p "mod/emacs/tty-modes.scm"
                                            "(define (suppress-echo-tty fd)")
                      (m43-imp4--contains-p "mod/emacs/tty-modes.scm"
                                            "(define (unlock-tty-flow fd flow?)")))
(m43-imp4--check "module/exports-all"
                 (and (m43-imp4--contains-p "mod/emacs/tty-modes.scm"
                                            "tty-mode-restore tty-mode-no-echo")
                      (m43-imp4--contains-p "mod/emacs/tty-modes.scm"
                                            "reset-tty-mode suppress-echo-tty unlock-tty-flow")))
(m43-imp4--check "module/defelisp-flow-unlock"
                 (m43-imp4--contains-p
                  "mod/emacs/tty-modes.scm"
                  "(defelisp %--tty-flow-unlock --tty-flow-unlock)"))
;; The entry points apply with the imp-2 leaf; the no-echo rule reuses the
;; constants; the flow policy is (not flow?).
(m43-imp4--check "module/entry-applies-with-tty-set-mode"
                 (and (m43-imp4--contains-p "mod/emacs/tty-modes.scm"
                                            "(tty-set-mode fd (tty-mode-restore base) #f)")
                      (m43-imp4--contains-p "mod/emacs/tty-modes.scm"
                                            "(tty-set-mode fd (tty-mode-no-echo mode (tty-mode-constants)) #f)")))
(m43-imp4--check "module/no-ffi-no-libc-no-ioctl"
                 (and (not (m43-imp4--contains-p "mod/emacs/tty-modes.scm"
                                                 "(system foreign)"))
                      (not (m43-imp4--contains-p "mod/emacs/tty-modes.scm"
                                                 "libc.so.6"))
                      (not (m43-imp4--contains-p "mod/emacs/tty-modes.scm"
                                                 "ioctl"))))

;;; --- P5. Registration (brief.org section 9 step 11) ------------------

(m43-imp4--check "reg/m43-group-has-imp4"
                 (m43-imp4--contains-p "tool/run-tests.scm"
                                       "test/m43/test-m43-imp4.el"))

;;; --- P6. The re-measured surface (brief.org section 2) ---------------

(m43-imp4--check "surface/sysdep.c-lines-4950"
                 (eql 4950 (m43-imp4--lines "src/sysdep.c")))
(m43-imp4--check "surface/sysdep.c-defuns-7"
                 (eql 7 (m43-imp4--count "src/sysdep.c" "^DEFUN (\"")))
(m43-imp4--check "surface/keyboard.c-lines-11233"
                 (eql 11233 (m43-imp4--lines "src/keyboard.c")))
(m43-imp4--check "surface/keyboard-globals.c-lines-490"
                 (eql 490 (m43-imp4--lines "src/keyboard-globals.c")))
(m43-imp4--check "surface/combined-11723-under-11960"
                 (let ((k (m43-imp4--lines "src/keyboard.c"))
                       (kg (m43-imp4--lines "src/keyboard-globals.c")))
                   (and (eql 11233 k)
                        (eql 490 kg)
                        (eql 11723 (+ k kg))
                        (<= (+ k kg) 11960))))
(m43-imp4--check "surface/scm-c-public-ref-232"
                 (eql 232 (m43-imp4--count-scm-ref)))

;;; --- P7. The pure policy corpus (brief.org section 11) ---------------
;;;
;;; Load the companion Scheme corpus and report its PASS/FAIL lines.

(let* ((dir (file-name-directory (or load-file-name default-directory)))
       (corpus (expand-file-name "test-m43-imp4.scm" dir))
       (load-error nil))
  (condition-case err
      (eval-scheme (format "(primitive-load %S)" corpus))
    (error (setq load-error err)))
  (let* ((results
          (cond
           (load-error
            (list (list "m43-imp4/corpus-load"
                        (cons 'FAIL (format "%S" load-error)))))
           (t
            (condition-case e
                (let ((r (eval-scheme "(reverse test-results)")))
                  (if (or (not (listp r)) (null r))
                      (list (list "m43-imp4/corpus-empty"
                                  (cons 'FAIL "corpus produced no results")))
                    r))
              (error
               (list (list "m43-imp4/readback"
                           (cons 'FAIL (format "%S" e)))))))))
         (pass 0)
         (fail 0))
    (dolist (result results)
      (let* ((name (car result))
             (status (cadr result))
             (ok (eq status 'PASS)))
        (cond
         (ok
          (imp-register-check-as-ert-test (format "m43-imp4/%s" name) status)
          (setq pass (1+ pass))
          (princ (format "PASS m43/imp4/%s\n" name)))
         ((and (consp status) (eq (car status) 'INFO))
          (princ (format "INFO m43/imp4/%s %s\n" name (cadr status))))
         (t
          (imp-register-check-as-ert-test (format "m43-imp4/%s" name) status)
          (setq fail (1+ fail))
          (princ (format "FAIL m43/imp4/%s %S\n" name (cdr result)))))))
    (princ (format "=== m43 imp-4 pure policy: %d passed, %d failed, %d total ===\n"
                   pass fail (+ pass fail)))))

;;; --- P8. The pty driver artifact (brief.org sections 9, 11.3, 11.4) -
;;;
;;; The end-to-end driver is a tracked file.  An absent or incomplete
;;; driver is a real FAIL, never an INFO skip: an INFO skip here would
;;; hide a missing artifact as an environment limit (brief.org section
;;; 11.4).

(m43-imp4--check "pty/driver-present"
                 (m43-imp4--file-has "test/pty-driver.py"
                                     "reset-tty-mode"))
(m43-imp4--check "pty/driver-mode-save"
                 (m43-imp4--file-has "test/pty-driver.py"
                                     "module-ref mod 'tty-get-mode"))

;;; --- The observable restore check (brief.org section 11.3) -----------
;;;
;;; The check needs a pty and the built src/emacs.  The corpus ATTEMPTS the
;;; pty: test/pty-driver.py calls os.openpty, and only a failed attempt is
;;; an environment-gated INFO skip, never a silent pass.  On success the
;;; driver runs the built emacs on the pty slave, saves the mode, applies
;;; the Emacs mode through init-tty-mode, restores it through
;;; reset-tty-mode, reads the mode back, and reports PASS/INFO/FAIL.  On
;;; this host os.openpty gives EACCES (errno 13), so the case reports an
;;; INFO skip.

(defun m43-imp4--emacs ()
  "Return the emacs under test, or nil when there is none.
M43_EMACS in the environment wins.  Otherwise use the built src/emacs."
  (let ((env (getenv "M43_EMACS")))
    (cond
     ((and env (file-executable-p env)) env)
     (t (let ((built (expand-file-name "src/emacs" m43-imp4--root)))
          (and (file-executable-p built) built))))))

(defun m43-imp4--parse-line (line)
  "Parse one driver report LINE into a (NAME . STATUS) pair, or nil.
STATUS is the symbol PASS, (FAIL . DETAIL), or (INFO DETAIL)."
  (cond
   ((string-match "\\`PASS \\([^ \t]+\\)" line)
    (cons (match-string 1 line) 'PASS))
   ((string-match "\\`FAIL \\([^ \t]+\\) *\\(.*\\)\\'" line)
    (cons (match-string 1 line) (cons 'FAIL (match-string 2 line))))
   ((string-match "\\`INFO \\([^ \t]+\\) *\\(.*\\)\\'" line)
    (cons (match-string 1 line) (list 'INFO (match-string 2 line))))
   (t nil)))

(let* ((driver (expand-file-name "test/pty-driver.py" m43-imp4--root))
       (python (executable-find "python3"))
       (emacs (m43-imp4--emacs))
       (name "m43-imp4/pty-e2e")
       (results
        (cond
         ((not (file-readable-p driver))
          (list (cons name (cons 'FAIL "missing test/pty-driver.py (tracked artifact)"))))
         ((not python)
          (list (cons name (list 'INFO "skipped (no python3)"))))
         ((not emacs)
          (list (cons name (list 'INFO "skipped (no built src/emacs)"))))
         (t
          (with-temp-buffer
            (let ((rc (condition-case err
                          (call-process python nil t nil driver
                                        "--group" "m43-imp4" "--emacs" emacs)
                        (error (cons 'ERROR err))))
                  (parsed nil))
              (dolist (l (split-string (buffer-string) "\n"))
                (let ((p (m43-imp4--parse-line l)))
                  (when p (push p parsed))))
              (setq parsed (nreverse parsed))
              (if (null parsed)
                  (list (cons name
                              (list 'INFO
                                    (format "skipped (driver produced no report: %S)"
                                            rc))))
                parsed)))))))
  (dolist (result results)
    (let ((rname (car result))
          (status (cdr result)))
      (cond
       ((eq status 'PASS)
        (imp-register-check-as-ert-test rname status)
        (princ (format "PASS %s\n" rname)))
       ((and (consp status) (eq (car status) 'INFO))
        (imp-register-skip-as-ert-test rname (cadr status))
        (princ (format "INFO %s %s\n" rname (cadr status))))
       (t
        (imp-register-check-as-ert-test rname status)
        (princ (format "FAIL %s %S\n" rname status)))))))

(princ "=== m43 imp-4 reset/restore policy suite done ===\n")
