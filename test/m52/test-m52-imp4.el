;;; test-m52-imp4.el --- M52 imp-4 insert / highlight cap policy tests.  -*- lexical-binding: t; -*-
;;;
;;; M52 imp-4 moves the DECISION of 5 src/term.c hubs into the module
;;; (emacs tty-output): tty_turn_on_insert, tty_turn_off_insert,
;;; tty_turn_off_highlight, tty_turn_on_highlight, and
;;; tty_toggle_highlight.  Each hub keeps its C state write and its
;;; OUTPUT / OUTPUT_IF call; only the capability-string selection runs
;;; in Scheme.
;;;
;;; This corpus checks the observable behaviour on every host:
;;;   1. The headless policy table.  It resolves the module through
;;;      `eval-scheme' and calls each of the 5 procedures for both flag
;;;      values (0 and 1).  It checks the returned KEY string, or #nil.
;;;   2. The headless #nil rule.  A flag that already holds the wanted
;;;      value returns #nil, so the hub emits nothing.
;;;   3. The module-export check.
;;;   4. One pty case (m52-imp4/policy-key-e2e) that drives the built
;;;      Emacs.
;;;
;;; LIMITATION (brief.org section 7 item 4).  No deterministic elisp
;;; trigger reaches the 5 rewired hubs: tty_turn_on_insert /
;;; tty_turn_off_insert run only inside the glyph insert / delete
;;; redisplay path, and tty_toggle_highlight runs inside the redisplay
;;; highlight path.  So the pty case drives the policy -> key -> bytes
;;; chain: the child calls the 5 policy procedures through `module-ref'
;;; and emits each returned key through --tty-emit-cap.  It does NOT
;;; prove the rewired hubs ran.  The hub rewiring is a C source fact; it
;;; is not asserted here (this behaviour corpus holds no source-layout
;;; checks, the imp-3 rule).  A pty allocation failure is an explicit
;;; INFO skip, never a PASS.

(princ "=== m52 imp-4 insert / highlight cap policy suite ===\n")

(require 'imp-ert-report)

(let ((dir (expand-file-name "../m42"
                             (file-name-directory
                              (or load-file-name default-directory)))))
  (add-to-list 'load-path dir)
  (require 'pty-runner))

(defvar m52-imp4--registered 0
  "Number of M52 imp-4 pty cases registered by this corpus.")

(let* ((results
        (condition-case err
            (m52-imp4-run-driver)
          (error (list (cons "m52-imp4/runner" (cons 'FAIL (format "%S" err)))))))
       (wanted m52-imp4--cases))
  (when (null results)
    (setq results (list (cons "m52-imp4/report"
                              (cons 'FAIL "driver produced no case results")))))
  (dolist (name wanted)
    (unless (assoc name results)
      (setq results (append results
                            (list (cons name (cons 'FAIL "driver omitted this case")))))))
  (dolist (result results)
    (let ((name (car result))
          (status (cdr result)))
      (setq m52-imp4--registered (1+ m52-imp4--registered))
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

(ert-deftest m52-imp4/gate-has-output-cases ()
  "The M52 group registers the M52 imp-4 pty case."
  (should (>= m52-imp4--registered 1)))

;; The headless policy table.  It proves that the DECISION runs in
;; Scheme: each procedure returns the right capability KEY for both flag
;; values.  Every key is one of the m52_caps keys (insert-mode,
;; end-insert-mode, standout-mode, end-standout-mode), so a rewrite that
;; returns a key the C table does not hold would FAIL here.
(ert-deftest m52-imp4/policy-table ()
  "Each policy procedure selects the right KEY, or #nil, for both flags."
  (should
   (eql 1
        (eval-scheme
         (concat
          "(let ((m (resolve-module '(emacs tty-output))))"
          " (if (and"
          "  (equal? ((module-ref m 'tty-turn-on-insert-cap) 0) \"insert-mode\")"
          "  (equal? ((module-ref m 'tty-turn-on-insert-cap) 1) #nil)"
          "  (equal? ((module-ref m 'tty-turn-off-insert-cap) 0) #nil)"
          "  (equal? ((module-ref m 'tty-turn-off-insert-cap) 1) \"end-insert-mode\")"
          "  (equal? ((module-ref m 'tty-turn-off-highlight-cap) 0) #nil)"
          "  (equal? ((module-ref m 'tty-turn-off-highlight-cap) 1) \"end-standout-mode\")"
          "  (equal? ((module-ref m 'tty-turn-on-highlight-cap) 0) \"standout-mode\")"
          "  (equal? ((module-ref m 'tty-turn-on-highlight-cap) 1) #nil)"
          "  (equal? ((module-ref m 'tty-toggle-highlight-cap) 0) \"standout-mode\")"
          "  (equal? ((module-ref m 'tty-toggle-highlight-cap) 1) \"end-standout-mode\"))"
          " 1 0))")))))

;; The #nil rule.  A flag that already holds the wanted value returns
;; #nil, so the hub emits nothing (C tests the KEY with NILP).  The
;; toggle has no #nil case: it always picks one direction.
(ert-deftest m52-imp4/nil-rule ()
  "Each guarded procedure returns #nil when the flag is already set."
  (should
   (eql 1
        (eval-scheme
         (concat
          "(let ((m (resolve-module '(emacs tty-output))))"
          " (if (and"
          "  (eq? ((module-ref m 'tty-turn-on-insert-cap) 1) #nil)"
          "  (eq? ((module-ref m 'tty-turn-off-insert-cap) 0) #nil)"
          "  (eq? ((module-ref m 'tty-turn-off-highlight-cap) 0) #nil)"
          "  (eq? ((module-ref m 'tty-turn-on-highlight-cap) 1) #nil))"
          " 1 0))")))))

;; The module loads and exports the 5 procedures.  A missing module or
;; export yields 0, so the check FAILS on any gap.  This keeps the
;; Scheme side covered on every host, with or without pty support.
(ert-deftest m52-imp4/module-exports-policy ()
  "The (emacs tty-output) module exports the 5 policy procedures."
  (should
   (eql 1
        (eval-scheme
         (concat
          "(let ((m (resolve-module '(emacs tty-output))))"
          " (if (and (procedure? (module-ref m 'tty-turn-on-insert-cap))"
          "  (procedure? (module-ref m 'tty-turn-off-insert-cap))"
          "  (procedure? (module-ref m 'tty-turn-off-highlight-cap))"
          "  (procedure? (module-ref m 'tty-turn-on-highlight-cap))"
          "  (procedure? (module-ref m 'tty-toggle-highlight-cap)))"
          " 1 0))")))))

(princ (format "=== m52 imp-4 policy suite done (%d cases) ===\n"
               m52-imp4--registered))
