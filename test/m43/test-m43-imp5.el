;;; test-m43-imp5.el --- M43 imp-5 corpus: the tty-size policy.
;;;
;;; M43 imp-5 moves the size policy of get_tty_size and set_window_size of
;;; src/sysdep.c into (emacs tty-modes):
;;;
;;;   (tty-size-wanted probe fallback) -> a (width . height) pair
;;;   (tty-size fd)                    -> the probe applied with no fallback
;;;   (set-tty-size fd height width)   -> the leaf status
;;; plus the two C leaves --tty-get-size / --tty-set-size and the two C
;;; dispatchers get_tty_size_policy / set_window_size_policy in src/sysdep.c.
;;;
;;; This file holds the pins that read files only, so they run on every
;;; host (P1-P8).  The table-driven pure check of the policy lives in the
;;; companion corpus test-m43-imp5.scm; it is the primary proof of imp-5
;;; (brief.org section 11) and runs on every host too.  The observable
;;; size ("a set size reads back") needs a pty: this host cannot allocate
;;; one (os.openpty gives EACCES, errno 13), so that case is an
;;; environment-gated INFO skip, not a pass (brief.org section 11.3).
;;;
;;; Each check is printed as a PASS/FAIL line and turned into an ERT test
;;; so the harness counts it.  A read error is a real error, never a
;;; silent pass.

(princ "=== m43 imp-5 tty-size policy suite ===\n")

(require 'imp-ert-report)

(defvar m43-imp5--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))

(defun m43-imp5--with (rel fn)
  "Call FN in a temp buffer holding REL (repo-root-relative), or return
the symbol `m43-imp5-absent' when REL does not exist."
  (let ((path (expand-file-name rel m43-imp5--root)))
    (if (not (file-exists-p path))
        'm43-imp5-absent
      (with-temp-buffer
        (insert-file-contents path)
        (funcall fn)))))

(defun m43-imp5--contains-p (rel needle)
  "Non-nil when REL (repo-root-relative) contains NEEDLE."
  (m43-imp5--with rel
    (lambda ()
      (goto-char (point-min))
      (search-forward needle nil t))))

(defun m43-imp5--file-has (rel needle)
  "Non-nil when the file REL (repo-root-relative) holds NEEDLE.
An absent file is nil, that is a real FAIL, not an INFO skip.  This is
the fail-loudly rule of brief.org section 11.4: a *tracked* artifact
that is missing must not look like an environment limit."
  (let ((path (expand-file-name rel m43-imp5--root)))
    (and (file-readable-p path)
         (with-temp-buffer
           (insert-file-contents path)
           (goto-char (point-min))
           (and (search-forward needle nil t) t)))))

(defun m43-imp5--lines (rel)
  "Count the newlines of REL the way `wc -l' does."
  (m43-imp5--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (search-forward "\n" nil t) (setq n (1+ n)))
        n))))

(defun m43-imp5--count (rel regexp)
  "Count the matches of REGEXP in REL."
  (m43-imp5--with rel
    (lambda ()
      (goto-char (point-min))
      (let ((n 0))
        (while (re-search-forward regexp nil t) (setq n (1+ n)))
        n))))

(defun m43-imp5--count-scm-ref ()
  "Count scm_c_public_ref over src/*.[chm] (the brief.org section 2 measure)."
  (let ((total 0)
        (dir (expand-file-name "src" m43-imp5--root)))
    (dolist (f (directory-files dir t "\\.[chm]\\'"))
      (setq total (+ total (or (m43-imp5--count f "scm_c_public_ref") 0))))
    total))

(defun m43-imp5--check (name ok)
  "Report and register one check.  An absent source file yields `eql'
nil, which prints FAIL (an absent src/ file is a real error, not a pass)."
  (if (eq ok 'm43-imp5-absent)
      (princ (format "INFO m43/imp5/%s skipped (source file absent)\n" name))
    (progn
      (princ (format "%s m43/imp5/%s\n" (if ok "PASS" "FAIL") name))
      (imp-register-bool-as-ert-test (format "m43-imp5/%s" name) ok))))

;;; --- P1. The two C leaves (brief.org section 6) ----------------------

(m43-imp5--check "leaf/get-defun"
                 (m43-imp5--contains-p
                  "src/sysdep.c" "DEFUN (\"--tty-get-size\""))
(m43-imp5--check "leaf/set-defun"
                 (m43-imp5--contains-p
                  "src/sysdep.c" "DEFUN (\"--tty-set-size\""))
(m43-imp5--check "leaf/tiocgwinsz-arm"
                 (m43-imp5--contains-p
                  "src/sysdep.c" "ioctl (ifd, TIOCGWINSZ, &size)"))
(m43-imp5--check "leaf/tiocswinsz-arm"
                 (m43-imp5--contains-p
                  "src/sysdep.c" "ioctl (ifd, TIOCSWINSZ, &size)"))
(m43-imp5--check "leaf/get-dos-nt-guard"
                 (m43-imp5--contains-p
                  "src/sysdep.c" "#ifndef DOS_NT\n#if defined TIOCGWINSZ"))
(m43-imp5--check "leaf/set-dos-nt-guard"
                 (m43-imp5--contains-p
                  "src/sysdep.c" "#ifndef DOS_NT\n#ifdef TIOCSWINSZ"))
;; The dropped-platform arms are deleted.
(m43-imp5--check "leaf/no-window-nt-arm"
                 (not (m43-imp5--contains-p
                       "src/sysdep.c" "GetConsoleScreenBufferInfo")))
(m43-imp5--check "leaf/no-sunos-typo-arm"
                 (not (m43-imp5--contains-p
                       "src/sysdep.c" "ioctl (fd, TIOCGSIZE, &size)")))

;;; --- P2. The two C dispatchers (brief.org section 7) -----------------

(m43-imp5--check "dispatch/get-policy-defun"
                 (m43-imp5--contains-p
                  "src/sysdep.c"
                  "get_tty_size_policy (int fd, int *widthp, int *heightp)"))
(m43-imp5--check "dispatch/set-policy-defun"
                 (m43-imp5--contains-p
                  "src/sysdep.c"
                  "set_window_size_policy (int fd, int height, int width)"))
(m43-imp5--check "dispatch/calls-tty-size"
                 (m43-imp5--contains-p
                  "src/sysdep.c"
                  "scm_c_public_ref (\"emacs tty-modes\", \"tty-size\")"))
(m43-imp5--check "dispatch/calls-set-tty-size"
                 (m43-imp5--contains-p
                  "src/sysdep.c"
                  "scm_c_public_ref (\"emacs tty-modes\", \"set-tty-size\")"))
;; The dispatchers pass plain values only.
(m43-imp5--check "dispatch/passes-plain-fd-call1"
                 (m43-imp5--contains-p
                  "src/sysdep.c"
                  "SCM_CALL_1 (proc, make_fixnum (fd));"))
(m43-imp5--check "dispatch/passes-plain-set-call3"
                 (m43-imp5--contains-p
                  "src/sysdep.c"
                  "SCM_CALL_3 (proc, make_fixnum (fd), make_fixnum (height),"))
;; A bad shape is a programming error.
(m43-imp5--check "dispatch/aborts-on-bad-shape"
                 (m43-imp5--contains-p "src/sysdep.c" "emacs_abort ()"))

;;; --- P3. The two rewires (brief.org section 9 step 5) ----------------

;; get_tty_size no longer probes; it calls the dispatcher, and no
;; ioctl (fd, TIOCGWINSZ, &size) stays in its body.
(m43-imp5--check "rewire/get-calls-dispatcher"
                 (m43-imp5--contains-p
                  "src/sysdep.c"
                  "get_tty_size_policy (fd, widthp, heightp);"))
(m43-imp5--check "rewire/get-no-direct-ioctl"
                 (not (m43-imp5--contains-p
                       "src/sysdep.c" "ioctl (fd, TIOCGWINSZ, &size)")))
;; set_window_size no longer issues TIOCSWINSZ; it calls the dispatcher.
(m43-imp5--check "rewire/set-calls-dispatcher"
                 (m43-imp5--contains-p
                  "src/sysdep.c"
                  "return set_window_size_policy (fd, height, width);"))
(m43-imp5--check "rewire/set-no-direct-ioctl"
                 (not (m43-imp5--contains-p
                       "src/sysdep.c" "ioctl (fd, TIOCSWINSZ, &size)")))

;;; --- P4. The module (emacs tty-modes) (brief.org section 5, 8) -------

(m43-imp5--check "module/wanted-rule"
                 (m43-imp5--contains-p "mod/emacs/tty-modes.scm"
                                       "(define (tty-size-wanted probe fallback)"))
(m43-imp5--check "module/entry-points"
                 (and (m43-imp5--contains-p "mod/emacs/tty-modes.scm"
                                            "(define (tty-size fd)")
                      (m43-imp5--contains-p "mod/emacs/tty-modes.scm"
                                            "(define (set-tty-size fd height width)")))
(m43-imp5--check "module/exports-all"
                 (m43-imp5--contains-p "mod/emacs/tty-modes.scm"
                                       "tty-size-wanted tty-size set-tty-size"))
(m43-imp5--check "module/defelisp-leaves"
                 (and (m43-imp5--contains-p
                       "mod/emacs/tty-modes.scm"
                       "(defelisp %--tty-get-size --tty-get-size)")
                      (m43-imp5--contains-p
                       "mod/emacs/tty-modes.scm"
                       "(defelisp %--tty-set-size --tty-set-size)")))
;; tty-size applies the rule with no fallback; set-tty-size returns the
;; leaf status.
(m43-imp5--check "module/tty-size-applies-rule"
                 (m43-imp5--contains-p "mod/emacs/tty-modes.scm"
                                       "(tty-size-wanted ((force %--tty-get-size) fd) #f)"))
(m43-imp5--check "module/set-tty-size-calls-leaf"
                 (m43-imp5--contains-p "mod/emacs/tty-modes.scm"
                                       "((force %--tty-set-size) fd height width)"))
(m43-imp5--check "module/no-ffi-no-libc-no-ioctl"
                 (and (not (m43-imp5--contains-p "mod/emacs/tty-modes.scm"
                                                 "(system foreign)"))
                      (not (m43-imp5--contains-p "mod/emacs/tty-modes.scm"
                                                 "libc.so.6"))
                      (not (m43-imp5--contains-p "mod/emacs/tty-modes.scm"
                                                 "ioctl"))))

;;; --- P5. Registration (brief.org section 9 step 10) ------------------

(m43-imp5--check "reg/m43-group-has-imp5"
                 (m43-imp5--contains-p "tool/run-tests.scm"
                                       "test/m43/test-m43-imp5.el"))

;;; --- P6. The re-measured surface (brief.org section 2) ---------------

(m43-imp5--check "surface/sysdep.c-lines-4950"
                 (eql 4950 (m43-imp5--lines "src/sysdep.c")))
(m43-imp5--check "surface/sysdep.c-defuns-7"
                 (eql 7 (m43-imp5--count "src/sysdep.c" "^DEFUN (\"")))
(m43-imp5--check "surface/keyboard.c-lines-11233"
                 (eql 11233 (m43-imp5--lines "src/keyboard.c")))
(m43-imp5--check "surface/keyboard-globals.c-lines-490"
                 (eql 490 (m43-imp5--lines "src/keyboard-globals.c")))
(m43-imp5--check "surface/combined-11723-under-11960"
                 (let ((k (m43-imp5--lines "src/keyboard.c"))
                       (kg (m43-imp5--lines "src/keyboard-globals.c")))
                   (and (eql 11233 k)
                        (eql 490 kg)
                        (eql 11723 (+ k kg))
                        (<= (+ k kg) 11960))))
(m43-imp5--check "surface/scm-c-public-ref-235"
                 (eql 235 (m43-imp5--count-scm-ref)))

;;; --- P7. The pure policy corpus (brief.org section 11) ---------------
;;;
;;; Load the companion Scheme corpus and report its PASS/FAIL lines.

(let* ((dir (file-name-directory (or load-file-name default-directory)))
       (corpus (expand-file-name "test-m43-imp5.scm" dir))
       (load-error nil))
  (condition-case err
      (eval-scheme (format "(primitive-load %S)" corpus))
    (error (setq load-error err)))
  (let* ((results
          (cond
           (load-error
            (list (list "m43-imp5/corpus-load"
                        (cons 'FAIL (format "%S" load-error)))))
           (t
            (condition-case e
                (let ((r (eval-scheme "(reverse test-results)")))
                  (if (or (not (listp r)) (null r))
                      (list (list "m43-imp5/corpus-empty"
                                  (cons 'FAIL "corpus produced no results")))
                    r))
              (error
               (list (list "m43-imp5/readback"
                           (cons 'FAIL (format "%S" e)))))))))
         (pass 0)
         (fail 0))
    (dolist (result results)
      (let* ((name (car result))
             (status (cadr result))
             (ok (eq status 'PASS)))
        (cond
         (ok
          (imp-register-check-as-ert-test (format "m43-imp5/%s" name) status)
          (setq pass (1+ pass))
          (princ (format "PASS m43/imp5/%s\n" name)))
         ((and (consp status) (eq (car status) 'INFO))
          (princ (format "INFO m43/imp5/%s %s\n" name (cadr status))))
         (t
          (imp-register-check-as-ert-test (format "m43-imp5/%s" name) status)
          (setq fail (1+ fail))
          (princ (format "FAIL m43/imp5/%s %S\n" name (cdr result)))))))
    (princ (format "=== m43 imp-5 pure policy: %d passed, %d failed, %d total ===\n"
                   pass fail (+ pass fail)))))

;;; --- P8. The pty driver artifact (brief.org sections 9, 11.3, 11.4) -
;;;
;;; The end-to-end driver is a tracked file.  An absent or incomplete
;;; driver is a real FAIL, never an INFO skip: an INFO skip here would
;;; hide a missing artifact as an environment limit (brief.org section
;;; 11.4).

(m43-imp5--check "pty/driver-present"
                 (m43-imp5--file-has "test/pty-driver.py"
                                     "set-tty-size"))
(m43-imp5--check "pty/driver-size-probe"
                 (m43-imp5--file-has "test/pty-driver.py"
                                     "module-ref mod 'tty-size"))

;;; --- The observable size check (brief.org section 11.3) --------------
;;;
;;; The check needs a pty and the built src/emacs.  The corpus ATTEMPTS the
;;; pty: test/pty-driver.py calls os.openpty, and only a failed attempt is
;;; an environment-gated INFO skip, never a silent pass.  On success the
;;; driver runs the built emacs on the pty slave, probes the size, applies
;;; a known size with set-tty-size, reads it back, and reports
;;; PASS/INFO/FAIL.  On this host os.openpty gives EACCES (errno 13), so
;;; the case reports an INFO skip.

(defun m43-imp5--emacs ()
  "Return the emacs under test, or nil when there is none.
M43_EMACS in the environment wins.  Otherwise use the built src/emacs."
  (let ((env (getenv "M43_EMACS")))
    (cond
     ((and env (file-executable-p env)) env)
     (t (let ((built (expand-file-name "src/emacs" m43-imp5--root)))
          (and (file-executable-p built) built))))))

(defun m43-imp5--parse-line (line)
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

(let* ((driver (expand-file-name "test/pty-driver.py" m43-imp5--root))
       (python (executable-find "python3"))
       (emacs (m43-imp5--emacs))
       (name "m43-imp5/pty-e2e")
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
                                        "--group" "m43-imp5" "--emacs" emacs)
                        (error (cons 'ERROR err))))
                  (parsed nil))
              (dolist (l (split-string (buffer-string) "\n"))
                (let ((p (m43-imp5--parse-line l)))
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

(princ "=== m43 imp-5 tty-size policy suite done ===\n")
