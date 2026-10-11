;;; test-m52-imp8.el --- M52 imp-8 scroll / window / glyph arithmetic tests.  -*- lexical-binding: t; -*-
;;;
;;; M52 imp-8 moves the DECISION of 4 src/term.c arithmetic hubs into the
;;; module (emacs tty-output): tty_set_terminal_window,
;;; tty_set_scroll_region, tty_delete_glyphs, and tty_ins_del_lines.
;;; Each hub keeps its C state read and write, its FILE * streams, its
;;; tparam, and its OUTPUT / OUTPUT1 / OUTPUTL / OUTPUT_IF padding; only
;;; the step selection and the arithmetic run in Scheme.
;;;
;;; This corpus checks the observable behaviour on every host:
;;;   1. The headless policy table.  It resolves the module through
;;;      `eval-scheme' and calls each of the 4 procedures for every flag
;;;      combination.  It checks the returned step (a KEY string or a
;;;      MARKER list), the ordered step list, the marker shape (a plain
;;;      list), and the #nil case.
;;;   2. The headless #nil rule for tty-ins-del-lines-steps: guard 1
;;;      (scroll-ok 1 and vpos + i >= specified-window), guard 2
;;;      (memory-below 0 and vpos + i >= total-lines), and the live case.
;;;   3. The KEY / MARKER shape pin.  Each capability KEY string is a
;;;      m52_caps key byte for byte; the check names delete-mode and
;;;      end-delete-mode, so a missing table row makes the pty case FAIL
;;;      (m52_cap_string_1 returns NULL on an unknown key, so the hub
;;;      emits nothing).  See the fixture note below.
;;;   4. The module-export check for the 4 new procedures.
;;;   5. One pty case (m52-imp8/policy-key-e2e) that drives the built
;;;      Emacs.
;;;
;;; LIMITATION (brief.org section 5).  No deterministic elisp trigger
;;; reaches the 4 rewired hubs from a hook: the 4 hubs run in the
;;; redisplay path.  So the pty case drives the policy -> key -> bytes
;;; chain: the child calls the 4 policy procedures through `module-ref'
;;; and emits each returned KEY (string) step through --tty-emit-cap.  It
;;; skips the marker steps.  It does NOT prove that the rewired hubs ran.
;;; The hub rewiring is a C source fact; it is not asserted here (this
;;; behaviour corpus holds no source-layout checks, the imp-3 rule).  A
;;; pty allocation failure is an explicit INFO skip, never a PASS.  The
;;; case pins NO provisional byte span (brief.org section 5); a
;;; hard-coded TERM=xterm span is forbidden.
;;;
;;; The 2 KEY steps of this group are the terminfo smdc (enter delete
;;; mode) and rmdc (exit delete mode) strings.  No terminfo entry in a
;;; normal installation defines them: on TERM=xterm --tty-emit-cap
;;; returns 0 bytes for both keys, and a 0 count cannot show whether the
;;; m52_caps row is present.  The pty case therefore runs a controlled
;;; terminfo entry that defines the 2 strings (the TERMINFO fixture in
;;; test/pty-driver.py).  When tic or infocmp is missing, the case
;;; INFO-skips, never a PASS.

(princ "=== m52 imp-8 scroll / window / glyph arithmetic policy suite ===\n")

(require 'imp-ert-report)

(let ((dir (expand-file-name "../m42"
                             (file-name-directory
                              (or load-file-name default-directory)))))
  (add-to-list 'load-path dir)
  (require 'pty-runner))

(defvar m52-imp8--registered 0
  "Number of M52 imp-8 pty cases registered by this corpus.")

(let* ((results
        (condition-case err
            (m52-imp8-run-driver)
          (error (list (cons "m52-imp8/runner" (cons 'FAIL (format "%S" err)))))))
       (wanted m52-imp8--cases))
  (when (null results)
    (setq results (list (cons "m52-imp8/report"
                              (cons 'FAIL "driver produced no case results")))))
  (dolist (name wanted)
    (unless (assoc name results)
      (setq results (append results
                            (list (cons name (cons 'FAIL "driver omitted this case")))))))
  (dolist (result results)
    (let ((name (car result))
          (status (cdr result)))
      (setq m52-imp8--registered (1+ m52-imp8--registered))
      (cond
       ((eq status 'PASS)
        (imp-register-check-as-ert-test name status)
        (princ (format "PASS %s\n" name)))
       ((and (consp status) (eq (car status) 'INFO))
        (imp-register-skip-as-ert-test name (cadr status))
        (princ (format "INFO %s %s\n" name (cadr status))))
       (t
        (imp-register-check-as-ert-test name status)
        (princ (format "FAIL %s %S\n" name (cdr result))))))))

(ert-deftest m52-imp8/gate-has-output-cases ()
  "The M52 group registers the M52 imp-8 pty case."
  (should (>= m52-imp8--registered 1)))

;; The headless policy table.  It proves that the DECISION and the
;; arithmetic run in Scheme: each procedure returns the right step, or
;; #nil, for every flag combination.  Every KEY string is one of the
;; m52_caps keys (delete-mode, end-delete-mode), so a rewrite that
;; returns a key the C table does not hold would FAIL.  The marker steps
;; are plain lists.
(ert-deftest m52-imp8/policy-table ()
  "Each policy procedure selects the right step, or #nil, for its flags."
  (should
   (eql 1
        (eval-scheme
         (concat
          "(let ((m (resolve-module '(emacs tty-output))))"
          " (if (and"
          ;; set-terminal-window: w = size, or total-lines when size is 0;
          ;; the scroll-region marker is present only when scroll-ok holds.
          "  (equal? ((module-ref m 'tty-set-terminal-window-steps) 0 40 0) '((\"set-window\" 40)))"
          "  (equal? ((module-ref m 'tty-set-terminal-window-steps) 0 40 1) '((\"set-window\" 40) (\"scroll-region\" 0 40)))"
          "  (equal? ((module-ref m 'tty-set-terminal-window-steps) 7 40 0) '((\"set-window\" 7)))"
          "  (equal? ((module-ref m 'tty-set-terminal-window-steps) 7 40 1) '((\"set-window\" 7) (\"scroll-region\" 0 7)))"
          ;; set-scroll-region: the 3 forms and their tparam args.
          "  (equal? ((module-ref m 'tty-set-scroll-region-steps) 3 11 40 80 1 0 0) '(\"scroll-region\" 3 10))"
          "  (equal? ((module-ref m 'tty-set-scroll-region-steps) 3 11 40 80 0 1 0) '(\"scroll-region-1\" 40 3 29 40))"
          "  (equal? ((module-ref m 'tty-set-scroll-region-steps) 3 11 40 80 0 0 1) '(\"set-window\" 3 0 11 80))"
          ;; delete-glyphs: the 4 cases of the brief table.
          "  (equal? ((module-ref m 'tty-delete-glyphs-steps) 5 1 1) '((\"on-insert\") (\"del-multi\" 5)))"
          "  (equal? ((module-ref m 'tty-delete-glyphs-steps) 5 1 0) '((\"on-insert\") (\"del-char\" 5)))"
          "  (equal? ((module-ref m 'tty-delete-glyphs-steps) 5 0 1) '((\"off-insert\") \"delete-mode\" (\"del-multi\" 5) \"end-delete-mode\"))"
          "  (equal? ((module-ref m 'tty-delete-glyphs-steps) 5 0 0) '((\"off-insert\") \"delete-mode\" (\"del-char\" 5) \"end-delete-mode\"))"
          ;; ins-del-lines: the multi / single / scroll choice, plus the
          ;; eabs case and the OUTPUTL line count.
          "  (equal? ((module-ref m 'tty-ins-del-lines-steps) 5 3 40 40 1 1 1 0 1) '(\"multi\" 3))"
          "  (equal? ((module-ref m 'tty-ins-del-lines-steps) 5 3 40 40 1 1 0 1 1) '(\"single\" 3))"
          "  (equal? ((module-ref m 'tty-ins-del-lines-steps) 5 3 40 40 1 1 0 0 1) '(\"scroll\" 3 35))"
          "  (equal? ((module-ref m 'tty-ins-del-lines-steps) 10 -2 40 40 1 1 0 1 1) '(\"single\" 2)))"
          " 1 0))")))))

;; The #nil rule.  The ins/del-lines procedure returns #nil when a guard
;; holds, so the hub emits nothing (C tests the whole step with NILP).
;; Two guards: the lines below the edit run into the end of the scroll
;; region, and the lines run out of the bottom of the frame with no
;; memory below.
(ert-deftest m52-imp8/nil-rule ()
  "The ins/del-lines procedure returns #nil on either guard."
  (should
   (eql 1
        (eval-scheme
         (concat
          "(let ((m (resolve-module '(emacs tty-output))))"
          " (if (and"
          ;; guard 1: scroll-ok 1 and vpos + i >= specified-window.
          "  (eq? ((module-ref m 'tty-ins-del-lines-steps) 5 3 5 40 1 1 1 0 1) #nil)"
          "  (eq? ((module-ref m 'tty-ins-del-lines-steps) 5 3 5 40 1 0 1 0 1) #nil)"
          ;; guard 2: memory-below 0 and vpos + i >= total-lines.
          "  (eq? ((module-ref m 'tty-ins-del-lines-steps) 30 11 40 40 0 0 1 0 1) #nil)"
          ;; the live region is never #nil.
          "  (pair? ((module-ref m 'tty-ins-del-lines-steps) 5 3 40 40 1 1 1 0 1))"
          "  (pair? ((module-ref m 'tty-ins-del-lines-steps) 5 3 40 40 1 1 0 1 1)))"
          " 1 0))")))))

;; The key / marker split.  brief.org section 3: a KEY step is a plain
;; string; a MARKER step is a plain list.  The C hub tells them apart
;; with STRINGP.  This check fails if a rewrite returns the wrong kind,
;; and it pins the exact marker tags and the 2 capability keys that the
;; delete-glyphs procedure returns.
(ert-deftest m52-imp8/key-and-marker-shapes ()
  "Each procedure returns string KEYs and list MARKERs, as the brief says."
  (should
   (eql 1
        (eval-scheme
         (concat
          "(let ((m (resolve-module '(emacs tty-output))))"
          " (if (and"
          "  (pair? ((module-ref m 'tty-set-terminal-window-steps) 0 40 1))"
          "  (equal? ((module-ref m 'tty-set-terminal-window-steps) 0 40 1)"
          "          '((\"set-window\" 40) (\"scroll-region\" 0 40)))"
          "  (equal? ((module-ref m 'tty-set-scroll-region-steps) 3 11 40 80 1 0 0)"
          "          '(\"scroll-region\" 3 10))"
          "  (string? (cadr ((module-ref m 'tty-delete-glyphs-steps) 5 0 1)))"
          "  (equal? (cadr ((module-ref m 'tty-delete-glyphs-steps) 5 0 1)) \"delete-mode\")"
          "  (equal? (car (reverse ((module-ref m 'tty-delete-glyphs-steps) 5 0 1))) \"end-delete-mode\")"
          "  (equal? ((module-ref m 'tty-ins-del-lines-steps) 5 3 40 40 1 1 1 0 1)"
          "          '(\"multi\" 3)))"
          " 1 0))")))))

;; The module loads and exports the 4 new procedures.  A missing module
;; or export yields 0, so the check FAILS on any gap.  This keeps the
;; Scheme side covered on every host, with or without pty support.
(ert-deftest m52-imp8/module-exports-policy ()
  "The (emacs tty-output) module exports the 4 imp-8 policy procedures."
  (should
   (eql 1
        (eval-scheme
         (concat
          "(let ((m (resolve-module '(emacs tty-output))))"
          " (if (and (procedure? (module-ref m 'tty-set-terminal-window-steps))"
          "  (procedure? (module-ref m 'tty-set-scroll-region-steps))"
          "  (procedure? (module-ref m 'tty-delete-glyphs-steps))"
          "  (procedure? (module-ref m 'tty-ins-del-lines-steps)))"
          " 1 0))")))))

(princ (format "=== m52 imp-8 policy suite done (%d cases) ===\n"
               m52-imp8--registered))
