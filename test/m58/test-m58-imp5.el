;;; test-m58-imp5.el --- M58 imp-5, the CLOSE-OUT: the 3 row verdicts.
;;;
;;; imp-5 CLOSES M58.  It moves no C and no Scheme policy: the C delta
;;; is 0 and the Scheme delta is 0.  It re-measures the surface and
;;; records a measured verdict for each of the 3 open MOVE-candidate
;;; rows of the imp-1 row map (brief.org section 5).
;;;
;;; The 3 verdicts, each MEASURED at HEAD (not copied from brief.org):
;;;
;;;   row A  the calculate_costs TS_repeat test (src/term.c).  STAYS C:
;;;          the block writes tty->RPov only.  RPov has 2 writes and 1
;;;          declaration and NO reader.  A value that no code reads is
;;;          not an observable, and the cost inputs per_line_cost /
;;;          string_cost are C termcap calls (tputs).  No decision
;;;          moves, so this row has NO runtime observable.
;;;   row B  tty-no-underline.  STAYS C: one C struct field write behind
;;;          a C terminal-type test.  The observable DOES exist (after
;;;          the call an underlined face emits no underline start byte;
;;;          TS_enter_underline_mode is the M52_CAP "underline" source),
;;;          but no plain value crosses that C would not compute itself,
;;;          so a Scheme port would be a passthrough, not a port
;;;          (passthrough-leaf-is-not-a-port).
;;;   row C  tty-top-frame.  STAYS C: a pure read of a Lisp_Object
;;;          field of a C struct.  It computes nothing and it needs the
;;;          C struct member itself.
;;;
;;; The row map closes as: 5 MOVEs in Scheme (Group A: tty-face-on-steps,
;;; tty-face-off-steps, tty-capable-p; Group B: tty-color-mode-tag,
;;; tty-color-mode-changed-p), 3 rows STAYS C (this unit), 5 rows NOT
;;; PROVEN (no observable: the 3 Group D ins / del rows and the 2 Group
;;; F tty--output-buffer-size rows), and Group G STAYS C.
;;;
;;; M61 imp-2b and imp-2g removed every SOURCE-INSPECTION assertion of
;;; this corpus (milestone.org finding F2 / F7).  A test proves
;;; BEHAVIOR.  It must not read source text, a source line number, a
;;; source byte count, a source order, or a count pin of another runner.
;;;
;;; What the corpus keeps:
;;;
;;;   V1 -- the 2 row verdicts that HAVE a runtime observable: the 2
;;;         STAYS C entry points still resolve as subrs in the running
;;;         binary.  V1 holds 2 checks.  Row A has no observable, so it
;;;         is recorded in the comment above and holds no check.
;;;   V2 -- the row-map close: the 5 MOVEs resolve as module bindings of
;;;         (emacs tty-output) in a real `guile -L mod' process.  A
;;;         missing guile binary is an explicit INFO skip.  V2 holds 1
;;;         check.
;;;   V3 -- the real path: run the 3 existing PTY groups (m58-imp2,
;;;         m58-imp3, m58-imp4) on the built src/emacs.  One check per
;;;         group.  A missing python3, a missing built src/emacs, or a
;;;         missing PTY is an explicit INFO skip, NEVER a pass.  V3
;;;         holds 3 checks.
;;;   V4 -- the guards: 3 per-group min-count guards plus the in-process
;;;         group total.  V4 holds 3 checks.
;;;
;;; The corpus reads NO source file.  The only inputs are the running
;;; binary, a real `guile' process, and a real PTY run.
;;;
;;; A read error is a real error, never a silent pass.  Every check
;;; registers a real ERT test.

(princ "=== m58 imp-5 close-out suite ===\n")

(require 'imp-ert-report)

(defvar m58-imp5--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))
(defvar m58-imp5--registered 0
  "Total number of checks this corpus has registered.")
(defvar m58-imp5--group nil
  "The group that `m58-imp5--check' counts into: `v1' .. `v4', or nil.")
(defvar m58-imp5--counts nil
  "Alist of (GROUP . COUNT) for the registered checks.")

(defun m58-imp5--group-count (group)
  "Number of checks registered so far in GROUP."
  (or (cdr (assq group m58-imp5--counts)) 0))

(defun m58-imp5--bump-group ()
  "Count one check into `m58-imp5--group'."
  (when m58-imp5--group
    (let ((cell (assq m58-imp5--group m58-imp5--counts)))
      (if cell
          (setcdr cell (1+ (cdr cell)))
        (push (cons m58-imp5--group 1) m58-imp5--counts)))))

(defun m58-imp5--count-in (text needle)
  "Count the non-overlapping occurrences of the literal NEEDLE in TEXT."
  (let ((n 0) (start 0) (re (regexp-quote needle)))
    (while (string-match re text start)
      (setq n (1+ n) start (match-end 0)))
    n))

(defun m58-imp5--run (prog args)
  "Run PROG with ARGS from the repo root and return the combined output,
or the symbol `m58-imp5-prog-absent'."
  (if (not (executable-find prog))
      'm58-imp5-prog-absent
    (let ((buf (get-buffer-create " *m58-imp5-run*"))
          (default-directory m58-imp5--root))
      (unwind-protect
          (progn
            (with-current-buffer buf (erase-buffer))
            (apply #'call-process prog nil buf nil args)
            (with-current-buffer buf
              (buffer-substring-no-properties (point-min) (point-max))))
        (kill-buffer buf)))))

(defun m58-imp5--check (name ok)
  "Report and register one check.  OK is a boolean."
  (let ((pass (and ok t)))
    (princ (format "%s m58/imp5/%s\n" (if pass "PASS" "FAIL") name))
    (setq m58-imp5--registered (1+ m58-imp5--registered))
    (m58-imp5--bump-group)
    (imp-register-bool-as-ert-test (format "m58-imp5/%s" name) pass)))

(defun m58-imp5--info-skip (name reason)
  "Register one explicit INFO skip, counted into the current group."
  (princ (format "INFO m58/imp5/%s %s\n" name reason))
  (setq m58-imp5--registered (1+ m58-imp5--registered))
  (m58-imp5--bump-group)
  (imp-register-skip-as-ert-test (format "m58-imp5/%s" name) reason))

;;; --- V1. The row verdicts that have a runtime observable ------------

;; Row A has NO observable (see the header), so it holds no check.  Row
;; B and row C each keep one real subr in the running binary.  This
;; corpus runs INSIDE the built src/emacs, so the check is the real
;; binary of this tree.
(setq m58-imp5--group 'v1)

(m58-imp5--check "v1/row-b-stays-c"
                 (and (fboundp 'tty-no-underline)
                      (subrp (symbol-function 'tty-no-underline))))

(m58-imp5--check "v1/row-c-stays-c"
                 (and (fboundp 'tty-top-frame)
                      (subrp (symbol-function 'tty-top-frame))))

;;; --- V2. The row-map close ------------------------------------------

;; The 5 MOVE rows are module bindings of (emacs tty-output).  A real
;; `guile -L mod' process that imports all 5 names proves that each one
;; resolves and is exported.  A missing guile binary is an explicit INFO
;; skip, never a pass.
(setq m58-imp5--group 'v2)

(let ((out (m58-imp5--run "guile"
                          (list "-L" (expand-file-name "mod" m58-imp5--root)
                                "-c"
                                (concat "(use-modules ((emacs tty-output) #:select "
                                        "(tty-face-on-steps tty-face-off-steps "
                                        "tty-capable-p tty-color-mode-tag "
                                        "tty-color-mode-changed-p))) "
                                        "(display \"MOVES-OK\")")))))
  (if (eq out 'm58-imp5-prog-absent)
      (m58-imp5--info-skip "v2/five-moves-resolve" "no guile binary on PATH")
    (m58-imp5--check "v2/five-moves-resolve"
                     (and (string-match-p "MOVES-OK" out) t))))

;;; --- V3. The real path ----------------------------------------------

;; Run EACH existing PTY group on the built src/emacs.  "PASS" or an
;; explicit INFO skip, never a pass on a skip.  A bad run retries once
;; (the (m58) PTY cases can intermit -- a timing race).

(defun m58-imp5--pty-verdict (group)
  "Run the PTY GROUP on the built src/emacs.  Answer (STATUS . OUTPUT)
where STATUS is `pass', `info', `fail', `no-emacs', or `no-python3'."
  (let ((emacs (expand-file-name "src/emacs" m58-imp5--root)))
    (cond
     ((not (and (file-exists-p emacs) (file-executable-p emacs)))
      (cons 'no-emacs nil))
     (t
      (let* ((args (list "test/pty-driver.py" "--emacs" emacs
                         "--group" group))
             (out1 (m58-imp5--run "python3" args))
             (needle (concat "PASS " group "/"))
             (done (or (eq out1 'm58-imp5-prog-absent)
                       (string-match-p (regexp-quote needle) out1)
                       (string-match-p (concat "INFO " group "/") out1)))
             (out2 (unless done (m58-imp5--run "python3" args)))
             (out (or out2 out1)))
        (cond
         ((eq out1 'm58-imp5-prog-absent) (cons 'no-python3 nil))
         ((string-match-p (regexp-quote needle) out) (cons 'pass out))
         ((string-match-p (concat "INFO " group "/") out) (cons 'info out))
         (t (cons 'fail (list out1 out2)))))))))

(defun m58-imp5--pty-check (name group units)
  "Register one real-path check for GROUP.  UNITS is the number of PASS
lines that a healthy run prints."
  (let ((verdict (m58-imp5--pty-verdict group)))
    (cond
     ((eq (car verdict) 'no-emacs)
      (m58-imp5--info-skip name "no built src/emacs"))
     ((eq (car verdict) 'no-python3)
      (m58-imp5--info-skip name "no python3 binary on PATH"))
     ((eq (car verdict) 'pass)
      (let ((out (cdr verdict)))
        (m58-imp5--check name
                         (>= (m58-imp5--count-in out (concat "PASS " group "/"))
                             units))))
     ((eq (car verdict) 'info)
      (m58-imp5--info-skip name "no PTY on this host"))
     (t
      (princ (format "m58 imp5 PTY %s run 1:\n%s\n" group
                     (nth 0 (cdr verdict))))
      (princ (format "m58 imp5 PTY %s run 2 (retry):\n%s\n" group
                     (nth 1 (cdr verdict))))
      (m58-imp5--check name nil)))))

(setq m58-imp5--group 'v3)

(m58-imp5--pty-check "v3/pty-m58-imp2" "m58-imp2" 1)
(m58-imp5--pty-check "v3/pty-m58-imp3" "m58-imp3" 5)
(m58-imp5--pty-check "v3/pty-m58-imp4" "m58-imp4" 1)

;;; --- V4. The guards -------------------------------------------------

;; An --filter that matches no group reports exit 0 with 0 tests, so a
;; green m58 gate proves nothing until the corpus really registers.
(setq m58-imp5--group 'v4)

(m58-imp5--check "reg/min-v1-checks-2" (>= (m58-imp5--group-count 'v1) 2))
(m58-imp5--check "reg/min-v2-checks-1" (>= (m58-imp5--group-count 'v2) 1))
(m58-imp5--check "reg/min-v3-checks-3" (>= (m58-imp5--group-count 'v3) 3))

;;; --- The group-total check ------------------------------------------

;; 9 registered checks (V1 2, V2 1, V3 3, V4 3) plus the group-total
;; deftest itself.  A V3 check may fold to a controlled INFO skip on a
;; host with no built src/emacs, no python3, or no PTY, and a controlled
;; skip is still a registered test.

(defvar m58-imp5--gate-total 10
  "The EXACT number of m58-imp5 ERT tests: 9 registered checks (V1 2,
V2 1, V3 3, V4 3) plus the group-total deftest itself.  The guard uses
`equal', not `>=', so a DUPLICATE registration fails too.")

(ert-deftest m58-imp5/gate-m58-total ()
  "The m58-imp5 corpus registers exactly its docs-independent count."
  (should (equal (length (ert-select-tests "^m58-imp5" t))
                 m58-imp5--gate-total)))

(princ (format "=== m58 imp-5 suite done (%d checks; v1 %d, v2 %d, v3 %d, v4 %d) ===\n"
               m58-imp5--registered
               (m58-imp5--group-count 'v1)
               (m58-imp5--group-count 'v2)
               (m58-imp5--group-count 'v3)
               (m58-imp5--group-count 'v4)))
