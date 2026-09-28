;;; pty-runner.el --- M42 imp-3: start the pty driver and read its report.  -*- lexical-binding: t; -*-
;;;
;;; The runner starts test/m42/pty-driver.py on the emacs under test
;;; (src/emacs) and reads the driver's stdout.  The driver prints one
;;; report line per case:
;;;
;;;   PASS <name>
;;;   FAIL <name> <detail>
;;;   INFO <name> skipped (<reason>)
;;;
;;; The runner turns each line into a (NAME . STATUS) pair and returns
;;; the list.  The ERT wrapper (test-m42-imp3.el) registers each pair as
;;; a real ERT test.
;;;
;;; The skip path (brief.org sections 5.3 and 8): when python3 is
;;; missing, when no built src/emacs is present, or when the driver
;;; cannot allocate a pty, the runner returns one INFO pair per case.
;;; An INFO pair is never a PASS and never a FAIL -- the wrapper prints
;;; it and the harness reports it as skipped, not failed.
;;;
;;; The driver owns the pty pair and the child.  This runner does not
;;; use `make-process :connection-type 'pty': the child must be the
;;; emacs under test, not the test runner (brief.org D1).

;; Keep in sync with CASES in test/m42/pty-driver.py.  The runner needs
;; the names only for the skip path, where no driver output exists.
(defconst m42-imp3--cases
  '("m42-imp3/case-1-no-input"
    "m42-imp3/case-2-short-read")
  "The imp-3 case names.  Matches the driver's CASES table.")

(defun m42-imp3--dir ()
  "Return the directory that holds pty-runner.el."
  (file-name-directory (or load-file-name
                           (locate-library "pty-runner")
                           default-directory)))

(defun m42-imp3--repo-root ()
  "Return the repository root (two levels above test/m42/)."
  (file-name-as-directory
   (expand-file-name "../.." (m42-imp3--dir))))

(defun m42-imp3--emacs ()
  "Return the emacs under test, or nil when there is none.
M42_EMACS in the environment wins.  Otherwise use the built src/emacs
at the repository root."
  (let ((env (getenv "M42_EMACS")))
    (cond
     ((and env (file-executable-p env)) env)
     (t (let ((built (expand-file-name "src/emacs" (m42-imp3--repo-root))))
          (and (file-executable-p built) built))))))

(defun m42-imp3--skip (reason)
  "Return one INFO pair per case, all carrying REASON."
  (mapcar (lambda (name) (cons name (list 'INFO (format "skipped (%s)" reason))))
          m42-imp3--cases))

(defun m42-imp3--parse-line (line)
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

(defun m42-imp3--parse (text)
  "Parse the driver's TEXT into a list of (NAME . STATUS) pairs."
  (let (results)
    (dolist (line (split-string text "\n"))
      (let ((pair (m42-imp3--parse-line line)))
        (when pair (push pair results))))
    (nreverse results)))

(defun m42-imp3-run-driver ()
  "Run the pty driver on the emacs under test.
Return a list of (NAME . STATUS) pairs.  STATUS is the symbol PASS, a
(FAIL . DETAIL) pair, or an (INFO DETAIL) list.  Every environment gap
(python3, src/emacs, pty) returns INFO pairs, never FAIL."
  (let ((python (executable-find "python3"))
        (emacs (m42-imp3--emacs))
        (driver (expand-file-name "pty-driver.py" (m42-imp3--dir))))
    (cond
     ((not (file-readable-p driver))
      (m42-imp3--skip "no pty-driver.py"))
     ((not python)
      (m42-imp3--skip "no python3"))
     ((not emacs)
      (m42-imp3--skip "no built src/emacs"))
     (t
      (with-temp-buffer
        (let ((rc (condition-case err
                      (call-process python nil t nil driver "--emacs" emacs)
                    (error (cons 'ERROR err)))))
          (let ((results (m42-imp3--parse (buffer-string))))
            (if (null results)
                (m42-imp3--skip (format "driver produced no report (%S)" rc))
              results))))))))

(provide 'pty-runner)
;;; pty-runner.el ends here
