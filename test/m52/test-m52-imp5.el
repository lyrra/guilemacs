;;; test-m52-imp5.el --- M52 imp-5 bell / cursor / update-end policy tests.  -*- lexical-binding: t; -*-
;;;
;;; M52 imp-5 moves the DECISION of 6 src/term.c hubs into the module
;;; (emacs tty-output): tty_ring_bell, tty_update_end, tty_hide_cursor,
;;; tty_show_cursor, tty_background_highlight, and tty_highlight_if_desired.
;;; Each hub keeps its C state write and its OUTPUT / OUTPUT_IF call;
;;; only the capability-string / step selection runs in Scheme.
;;;
;;; This corpus checks the observable behaviour on every host:
;;;   1. The headless policy table.  It resolves the module through
;;;      `eval-scheme' and calls each of the 6 procedures for every flag
;;;      combination.  It checks the returned KEY string, the ordered KEY
;;;      list, or #nil.
;;;   2. The headless #nil rule.  A cursor flag that already holds the
;;;      wanted value returns #nil, so the hub emits nothing.
;;;   3. The module-export check.
;;;   4. One pty case (m52-imp5/policy-key-e2e) that drives the built
;;;      Emacs.
;;;
;;; LIMITATION (brief.org section 6 item 3).  No deterministic elisp
;;; trigger reaches the 6 rewired hubs from a hook: tty_ring_bell runs on
;;; the bell path, tty_update_end runs at the end of each redisplay, and
;;; the cursor / highlight hubs run inside the redisplay path.  So the pty
;;; case drives the policy -> key -> bytes chain: the child calls the 6
;;; policy procedures through `module-ref' and emits each returned key
;;; through --tty-emit-cap.  It does NOT prove the rewired hubs ran.  The
;;; hub rewiring is a C source fact; it is not asserted here (this
;;; behaviour corpus holds no source-layout checks, the imp-3 rule).  A
;;; pty allocation failure is an explicit INFO skip, never a PASS.

(princ "=== m52 imp-5 bell / cursor / update-end policy suite ===\n")

(require 'imp-ert-report)

(let ((dir (expand-file-name "../m42"
                             (file-name-directory
                              (or load-file-name default-directory)))))
  (add-to-list 'load-path dir)
  (require 'pty-runner))

(defvar m52-imp5--registered 0
  "Number of M52 imp-5 pty cases registered by this corpus.")

(let* ((results
        (condition-case err
            (m52-imp5-run-driver)
          (error (list (cons "m52-imp5/runner" (cons 'FAIL (format "%S" err)))))))
       (wanted m52-imp5--cases))
  (when (null results)
    (setq results (list (cons "m52-imp5/report"
                              (cons 'FAIL "driver produced no case results")))))
  (dolist (name wanted)
    (unless (assoc name results)
      (setq results (append results
                            (list (cons name (cons 'FAIL "driver omitted this case")))))))
  (dolist (result results)
    (let ((name (car result))
          (status (cdr result)))
      (setq m52-imp5--registered (1+ m52-imp5--registered))
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

(ert-deftest m52-imp5/gate-has-output-cases ()
  "The M52 group registers the M52 imp-5 pty case."
  (should (>= m52-imp5--registered 1)))

;; The headless policy table.  It proves that the DECISION runs in
;; Scheme: each procedure returns the right capability KEY (or ordered KEY
;; list) for every flag combination.  Every key is one of the m52_caps
;; keys (bell, visible-bell, cursor-invisible, cursor-normal,
;; cursor-visible, standout-mode, end-standout-mode), so a rewrite that
;; returns a key the C table does not hold would FAIL here.
(ert-deftest m52-imp5/policy-table ()
  "Each policy procedure selects the right KEY, or #nil, for its flags."
  (should
   (eql 1
        (eval-scheme
         (concat
          "(let ((m (resolve-module '(emacs tty-output))))"
          " (if (and"
          ;; ring-bell: visible-bell only when both flags are true.
          "  (equal? ((module-ref m 'tty-ring-bell-cap) 0 0) \"bell\")"
          "  (equal? ((module-ref m 'tty-ring-bell-cap) 1 0) \"bell\")"
          "  (equal? ((module-ref m 'tty-ring-bell-cap) 0 1) \"bell\")"
          "  (equal? ((module-ref m 'tty-ring-bell-cap) 1 1) \"visible-bell\")"
          ;; hide-cursor: hide only when cursor_hidden is 0.
          "  (equal? ((module-ref m 'tty-hide-cursor-cap) 0) '(\"cursor-invisible\"))"
          "  (eq? ((module-ref m 'tty-hide-cursor-cap) 1) #nil)"
          ;; show-cursor: show only when cursor_hidden is not 0.
          "  (eq? ((module-ref m 'tty-show-cursor-cap) 0 0) #nil)"
          "  (eq? ((module-ref m 'tty-show-cursor-cap) 0 1) #nil)"
          "  (equal? ((module-ref m 'tty-show-cursor-cap) 1 0) '(\"cursor-normal\"))"
          "  (equal? ((module-ref m 'tty-show-cursor-cap) 1 1)"
          "          '(\"cursor-normal\" \"cursor-visible\"))"
          ;; background / highlight-if-desired: the on / off keys.
          "  (equal? ((module-ref m 'tty-background-highlight-cap) 0) \"end-standout-mode\")"
          "  (equal? ((module-ref m 'tty-background-highlight-cap) 1) \"standout-mode\")"
          "  (equal? ((module-ref m 'tty-highlight-if-desired-cap) 0) \"end-standout-mode\")"
          "  (equal? ((module-ref m 'tty-highlight-if-desired-cap) 1) \"standout-mode\")"
          ;; update-end: the ordered step list, with or without show-cursor.
          "  (equal? ((module-ref m 'tty-update-end-steps) 0)"
          "          '(\"show-cursor\" \"off-insert\" \"background\"))"
          "  (equal? ((module-ref m 'tty-update-end-steps) 1)"
          "          '(\"off-insert\" \"background\")))"
          " 1 0))")))))

;; The #nil rule.  A cursor flag that already holds the wanted value
;; returns #nil, so the hub emits nothing (C tests the whole list with
;; NILP).  The ring-bell and update-end procedures have no #nil case.
(ert-deftest m52-imp5/nil-rule ()
  "Each guarded cursor procedure returns #nil when the flag is already set."
  (should
   (eql 1
        (eval-scheme
         (concat
          "(let ((m (resolve-module '(emacs tty-output))))"
          " (if (and"
          "  (eq? ((module-ref m 'tty-hide-cursor-cap) 1) #nil)"
          "  (eq? ((module-ref m 'tty-show-cursor-cap) 0 0) #nil)"
          "  (eq? ((module-ref m 'tty-show-cursor-cap) 0 1) #nil))"
          " 1 0))")))))

;; The module loads and exports the 6 procedures.  A missing module or
;; export yields 0, so the check FAILS on any gap.  This keeps the
;; Scheme side covered on every host, with or without pty support.
(ert-deftest m52-imp5/module-exports-policy ()
  "The (emacs tty-output) module exports the 6 imp-5 policy procedures."
  (should
   (eql 1
        (eval-scheme
         (concat
          "(let ((m (resolve-module '(emacs tty-output))))"
          " (if (and (procedure? (module-ref m 'tty-ring-bell-cap))"
          "  (procedure? (module-ref m 'tty-hide-cursor-cap))"
          "  (procedure? (module-ref m 'tty-show-cursor-cap))"
          "  (procedure? (module-ref m 'tty-background-highlight-cap))"
          "  (procedure? (module-ref m 'tty-highlight-if-desired-cap))"
          "  (procedure? (module-ref m 'tty-update-end-steps)))"
          " 1 0))")))))

(princ (format "=== m52 imp-5 policy suite done (%d cases) ===\n"
               m52-imp5--registered))
