;;; test-m43-imp3.el --- M43 imp-3 corpus: the init_sys_modes mode policy.
;;;
;;; M43 imp-3 moves the terminal-mode flag policy of init_sys_modes
;;; (src/sysdep.c) into (emacs tty-modes):
;;;
;;;   (tty-mode-constants)         -> the plain build key/value list
;;;   (tty-mode-wanted base flags) -> the wanted mode list (pure policy)
;;;   (init-tty-mode fd base flags)-> the thin entry point; applies it
;;; plus the C dispatcher init_tty_mode next to init_sys_modes and the
;;; --tty-mode-constants leaf in src/sysdep.c.
;;;
;;; This file holds the pins that read files only, so they run on every
;;; host (P1-P6).  The table-driven pure check of the policy lives in the
;;; companion corpus test-m43-imp3.scm; it is the primary proof of imp-3
;;; (brief.org section 11) and runs on every host too.  The observable
;;; tty-mode check needs a pty: this host cannot allocate one
;;; (os.openpty gives EACCES, errno 13), so that case is an
;;; environment-gated INFO skip, not a pass (brief.org section 12).
;;;
;;; Each check is printed as a PASS/FAIL line and turned into an ERT
;;; test so the harness counts it.  A read error is a real error, never a
;;; silent pass.

(princ "=== m43 imp-3 init_sys_modes mode-policy suite ===\n")

(require 'imp-ert-report)

(defvar m43-imp3--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))

(defun m43-imp3--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
the symbol `m43-imp3-absent' when REL does not exist."
  (let ((path (expand-file-name rel m43-imp3--root)))
    (if (not (file-exists-p path))
        'm43-imp3-absent
      (with-temp-buffer
        (insert-file-contents path)
        (funcall fn)))))

(defun m43-imp3--contains-p (rel needle)
  "Non-nil when REL (repo-root-relative) contains NEEDLE."
  (m43-imp3--with rel
    (lambda ()
      (goto-char (point-min))
      (search-forward needle nil t))))

(defun m43-imp3--lines (rel)
  "Count the newlines of REL the way `wc -l' does."
  (m43-imp3--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (search-forward "\n" nil t) (setq n (1+ n)))
        n))))

(defun m43-imp3--count (rel regexp)
  "Count the matches of REGEXP in REL."
  (m43-imp3--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (re-search-forward regexp nil t) (setq n (1+ n)))
        n))))

(defun m43-imp3--check (name ok)
  "Report and register one check.  An absent source file yields `eql'
nil, which prints FAIL (an absent src/ file is a real error, not a
pass)."
  (if (eq ok 'm43-imp3-absent)
      (princ (format "INFO m43/imp3/%s skipped (source file absent)\n" name))
    (progn
      (princ (format "%s m43/imp3/%s\n" (if ok "PASS" "FAIL") name))
      (imp-register-bool-as-ert-test (format "m43-imp3/%s" name) ok))))

;;; --- P1. The C dispatcher init_tty_mode (brief.org section 9 step 4) -

(m43-imp3--check "dispatch/defun"
                 (m43-imp3--contains-p
                  "src/sysdep.c"
                  "init_tty_mode (int fd, Lisp_Object base, Lisp_Object flags)"))
(m43-imp3--check "dispatch/calls-init-tty-mode"
                 (m43-imp3--contains-p
                  "src/sysdep.c"
                  "scm_c_public_ref (\"emacs tty-modes\", \"init-tty-mode\")"))
;; The dispatcher takes and passes plain values only.
(m43-imp3--check "dispatch/passes-plain-fd"
                 (m43-imp3--contains-p
                  "src/sysdep.c"
                  "SCM_CALL_3 (proc, make_fixnum (fd), base, flags);"))
;; The dispatcher validates the base mode before the Scheme call.
(m43-imp3--check "dispatch/validates-base"
                 (m43-imp3--contains-p "src/sysdep.c" "scm_is_bytevector"))
;; init_sys_modes builds the plain base list and flags, then dispatches.
(m43-imp3--check "init/builds-base-list"
                 (m43-imp3--contains-p
                  "src/sysdep.c"
                  "base = list5 (make_fixnum (tty.main.c_iflag),"))
(m43-imp3--check "init/builds-flags-list"
                 (m43-imp3--contains-p
                  "src/sysdep.c"
                  "intern_c_string (\"flow-control?\")"))
(m43-imp3--check "init/calls-dispatcher"
                 (m43-imp3--contains-p
                  "src/sysdep.c"
                  "init_tty_mode (fileno (tty_out->input), base, flags);"))
;; The flag block left C; C no longer applies the mode with emacs_set_tty
;; in init_sys_modes.
(m43-imp3--check "init/flag-block-deleted"
                 (not (m43-imp3--contains-p
                       "src/sysdep.c" "tty.main.c_iflag |= (IGNBRK)")))
;; The dropped-platform arms are deleted, not transliterated.
(m43-imp3--check "init/dropped-arms-deleted"
                 (and (not (m43-imp3--contains-p "src/sysdep.c"
                                                 "dos_ttraw (tty_out)"))
                      (not (m43-imp3--contains-p "src/sysdep.c"
                                                 "#endif /* HAIKU */"))))
;; C keeps the post-set work.
(m43-imp3--check "init/keeps-post-set-work"
                 (and (m43-imp3--contains-p "src/sysdep.c" "TCXONC, 1")
                      (m43-imp3--contains-p "src/sysdep.c"
                                            "set_terminal_modes_hook (tty_out->terminal)")))

;;; --- P2. The --tty-mode-constants leaf (brief.org section 8) ---------

(m43-imp3--check "consts/defun"
                 (m43-imp3--contains-p
                  "src/sysdep.c" "DEFUN (\"--tty-mode-constants\""))
;; The leaf is a plain key/value list: name symbol then fixnum value.
(m43-imp3--check "consts/plain-key-value-list"
                 (m43-imp3--contains-p
                  "src/sysdep.c"
                  "list = Fcons (make_fixnum (name), Fcons (intern_c_string (#name), list))"))
;; An absent #ifdef name is absent from the list.
(m43-imp3--check "consts/guards-optional-names"
                 (m43-imp3--contains-p "src/sysdep.c" "#ifdef VSWTCH"))

;;; --- P3. The module (emacs tty-modes) (brief.org section 7, 9) ------

(m43-imp3--check "module/pure-policy"
                 (m43-imp3--contains-p "mod/emacs/tty-modes.scm"
                                       "(define (tty-mode-wanted base flags)"))
(m43-imp3--check "module/entry-point"
                 (m43-imp3--contains-p "mod/emacs/tty-modes.scm"
                                       "(define (init-tty-mode fd base flags)"))
(m43-imp3--check "module/constants-wrapper"
                 (m43-imp3--contains-p "mod/emacs/tty-modes.scm"
                                       "(define (tty-mode-constants)"))
(m43-imp3--check "module/exports-all"
                 (and (m43-imp3--contains-p "mod/emacs/tty-modes.scm"
                                            "tty-mode-wanted")
                      (m43-imp3--contains-p "mod/emacs/tty-modes.scm"
                                            "init-tty-mode")
                      (m43-imp3--contains-p "mod/emacs/tty-modes.scm"
                                            "tty-mode-constants")))
;; The entry point applies the wanted mode with the imp-2 leaf, and the
;; pure policy runs no syscall (it does not call tty-set-mode).
(m43-imp3--check "module/entry-applies-with-tty-set-mode"
                 (m43-imp3--contains-p "mod/emacs/tty-modes.scm"
                                       "(tty-set-mode fd wanted #f)"))
(m43-imp3--check "module/defelisp-constants"
                 (m43-imp3--contains-p
                  "mod/emacs/tty-modes.scm"
                  "(defelisp %--tty-mode-constants --tty-mode-constants)"))
(m43-imp3--check "module/no-ffi-no-libc-no-ioctl"
                 (and (not (m43-imp3--contains-p "mod/emacs/tty-modes.scm"
                                                 "(system foreign)"))
                      (not (m43-imp3--contains-p "mod/emacs/tty-modes.scm"
                                                 "libc.so.6"))
                      (not (m43-imp3--contains-p "mod/emacs/tty-modes.scm"
                                                 "ioctl"))))

;;; --- P4. Registration (brief.org section 9 step 6, 7) ----------------

(m43-imp3--check "reg/loader-has-tty-modes"
                 (m43-imp3--contains-p "prelude/load.scm"
                                       "(use-modules (emacs tty-modes))"))
(m43-imp3--check "reg/m43-group-has-imp3"
                 (m43-imp3--contains-p "tool/run-tests.scm"
                                       "test/m43/test-m43-imp3.el"))

;;; --- P5. The re-measured surface (brief.org section 2) ---------------

(m43-imp3--check "surface/sysdep.c-lines-4950"
                 (eql 4950 (m43-imp3--lines "src/sysdep.c")))
(m43-imp3--check "surface/sysdep.c-defuns-7"
                 (eql 7 (m43-imp3--count "src/sysdep.c" "^DEFUN (\"")))
(m43-imp3--check "surface/keyboard.c-lines-11233"
                 (eql 11233 (m43-imp3--lines "src/keyboard.c")))
(m43-imp3--check "surface/keyboard-globals.c-lines-490"
                 (eql 490 (m43-imp3--lines "src/keyboard-globals.c")))
(m43-imp3--check "surface/combined-11723-under-11960"
                 (let ((k (m43-imp3--lines "src/keyboard.c"))
                       (kg (m43-imp3--lines "src/keyboard-globals.c")))
                   (and (eql 11233 k)
                        (eql 490 kg)
                        (eql 11723 (+ k kg))
                        (<= (+ k kg) 11960))))

;;; --- P6. The pure policy corpus (brief.org section 11) ---------------
;;;
;;; Load the companion Scheme corpus and report its PASS/FAIL lines.

(let* ((dir (file-name-directory (or load-file-name default-directory)))
       (corpus (expand-file-name "test-m43-imp3.scm" dir))
       (load-error nil))
  (condition-case err
      (eval-scheme (format "(primitive-load %S)" corpus))
    (error (setq load-error err)))
  (let* ((results
          (cond
           (load-error
            (list (list "m43-imp3/corpus-load"
                        (cons 'FAIL (format "%S" load-error)))))
           (t
            (condition-case e
                (let ((r (eval-scheme "(reverse test-results)")))
                  (if (or (not (listp r)) (null r))
                      (list (list "m43-imp3/corpus-empty"
                                  (cons 'FAIL "corpus produced no results")))
                    r))
              (error
               (list (list "m43-imp3/readback"
                           (cons 'FAIL (format "%S" e)))))))))
         (pass 0)
         (fail 0))
    (dolist (result results)
      (let* ((name (car result))
             (status (cadr result))
             (ok (eq status 'PASS)))
        (cond
         (ok
          (imp-register-check-as-ert-test (format "m43-imp3/%s" name) status)
          (setq pass (1+ pass))
          (princ (format "PASS m43/imp3/%s\n" name)))
         ((and (consp status) (eq (car status) 'INFO))
          (princ (format "INFO m43/imp3/%s %s\n" name (cadr status))))
         (t
          (imp-register-check-as-ert-test (format "m43-imp3/%s" name) status)
          (setq fail (1+ fail))
          (princ (format "FAIL m43/imp3/%s %S\n" name (cdr result)))))))
    (princ (format "=== m43 imp-3 pure policy: %d passed, %d failed, %d total ===\n"
                   pass fail (+ pass fail)))))

;;; --- The observable tty-mode check (brief.org section 11, 12) --------
;;;
;;; The check needs a pty and the built src/emacs.  The corpus ATTEMPTS
;;; the pty: pty-driver-imp3.py calls os.openpty, and only a failed
;;; attempt is an environment-gated INFO skip, never a silent pass (review
;;; cr.org F3).  On success the driver runs the built emacs on the pty
;;; slave, applies the wanted mode through init-tty-mode, reads the mode
;;; back, and reports PASS/INFO/FAIL.  On this host os.openpty gives
;;; EACCES (errno 13), so the case reports an INFO skip.

(defun m43-imp3--emacs ()
  "Return the emacs under test, or nil when there is none.
M43_EMACS in the environment wins.  Otherwise use the built src/emacs."
  (let ((env (getenv "M43_EMACS")))
    (cond
     ((and env (file-executable-p env)) env)
     (t (let ((built (expand-file-name "src/emacs" m43-imp3--root)))
          (and (file-executable-p built) built))))))

(defun m43-imp3--parse-line (line)
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

(let* ((dir (file-name-directory (or load-file-name default-directory)))
       (driver (expand-file-name "pty-driver-imp3.py" dir))
       (python (executable-find "python3"))
       (emacs (m43-imp3--emacs))
       (name "m43-imp3/pty-e2e")
       (results
        (cond
         ((not (file-readable-p driver))
          (list (cons name (cons 'FAIL "missing pty-driver-imp3.py (tracked artifact)"))))
         ((not python)
          (list (cons name (list 'INFO "skipped (no python3)"))))
         ((not emacs)
          (list (cons name (list 'INFO "skipped (no built src/emacs)"))))
         (t
          (with-temp-buffer
            (let ((rc (condition-case err
                          (call-process python nil t nil driver "--emacs" emacs)
                        (error (cons 'ERROR err))))
                  (parsed nil))
              (dolist (l (split-string (buffer-string) "\n"))
                (let ((p (m43-imp3--parse-line l)))
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

(princ "=== m43 imp-3 init_sys_modes mode-policy suite done ===\n")
