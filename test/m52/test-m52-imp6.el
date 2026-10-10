;;; test-m52-imp6.el --- M52 imp-6 terminal-mode / cursor-motion tests.  -*- lexical-binding: t; -*-
;;;
;;; M52 imp-6 moves the DECISION of 4 src/term.c hubs into the module
;;; (emacs tty-output): tty_set_terminal_modes, tty_reset_terminal_modes,
;;; tty_cursor_to, and tty_raw_cursor_to.  Each hub keeps its C state
;;; write, its FILE * streams, and its OUTPUT / OUTPUT_IF padding; only
;;; the ordered step selection runs in Scheme.
;;;
;;; This corpus checks the observable behaviour on every host:
;;;   1. The headless policy table.  It resolves the module through
;;;      `eval-scheme' and calls each of the 4 procedures for every flag
;;;      combination.  It checks the returned ordered step list, the
;;;      marker shape (a plain list), and the #nil case.
;;;   2. The headless #nil rule for the two cursor procedures: the
;;;      no-move case returns #nil, so the hub emits nothing.  A partial
;;;      coordinate match still moves (the `and` shape, not `or`).
;;;   3. The module-export check for the 4 new procedures.
;;;   4. One pty case (m52-imp6/policy-key-e2e) that drives the built
;;;      Emacs.
;;;
;;; LIMITATION (brief.org section 6).  No deterministic elisp trigger
;;; reaches the 4 rewired hubs from a hook: tty_set_terminal_modes and
;;; tty_reset_terminal_modes run at terminal setup / teardown, and the
;;; two cursor hubs run inside the redisplay path after the costs have
;;; been calculated.  So the pty case drives the policy -> key -> bytes
;;; chain: the child calls the 4 policy procedures through `module-ref'
;;; and emits each returned KEY (string) step through --tty-emit-cap.
;;; It skips the marker steps.  It does NOT prove that the rewired hubs
;;; ran.  The hub rewiring is a C source fact; it is not asserted here
;;; (this behaviour corpus holds no source-layout checks, the imp-3
;;; rule).  A pty allocation failure is an explicit INFO skip, never a
;;; PASS.

(princ "=== m52 imp-6 terminal-mode / cursor-motion policy suite ===\n")

(require 'imp-ert-report)

(let ((dir (expand-file-name "../m42"
                             (file-name-directory
                              (or load-file-name default-directory)))))
  (add-to-list 'load-path dir)
  (require 'pty-runner))

(defvar m52-imp6--registered 0
  "Number of M52 imp-6 pty cases registered by this corpus.")

(let* ((results
        (condition-case err
            (m52-imp6-run-driver)
          (error (list (cons "m52-imp6/runner" (cons 'FAIL (format "%S" err)))))))
       (wanted m52-imp6--cases))
  (when (null results)
    (setq results (list (cons "m52-imp6/report"
                              (cons 'FAIL "driver produced no case results")))))
  (dolist (name wanted)
    (unless (assoc name results)
      (setq results (append results
                            (list (cons name (cons 'FAIL "driver omitted this case")))))))
  (dolist (result results)
    (let ((name (car result))
          (status (cdr result)))
      (setq m52-imp6--registered (1+ m52-imp6--registered))
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

(ert-deftest m52-imp6/gate-has-output-cases ()
  "The M52 group registers the M52 imp-6 pty case."
  (should (>= m52-imp6--registered 1)))

;; The headless policy table.  It proves that the DECISION runs in
;; Scheme: each procedure returns the right ordered step list for every
;; flag combination.  Every KEY string is one of the m52_caps keys
;; (termcap-modes, cursor-normal, cursor-visible, keypad-mode,
;; end-keypad-mode, end-termcap-modes, orig-pair), so a rewrite that
;; returns a key the C table does not hold would FAIL here.  The marker
;; steps ("newlines", "raw-cr", "move") are plain lists.
(ert-deftest m52-imp6/policy-table ()
  "Each policy procedure selects the right step list, or #nil, for its flags."
  (should
   (eql 1
        (eval-scheme
         (concat
          "(let ((m (resolve-module '(emacs tty-output))))"
          " (if (and"
          ;; set-terminal-modes: termcap-modes OR the newlines marker,
          ;; then the cursor key, then the keypad key.
          "  (equal? ((module-ref m 'tty-set-terminal-modes-steps) 1 24 0)"
          "          '(\"termcap-modes\" \"cursor-normal\" \"keypad-mode\"))"
          "  (equal? ((module-ref m 'tty-set-terminal-modes-steps) 1 24 1)"
          "          '(\"termcap-modes\" \"cursor-visible\" \"keypad-mode\"))"
          "  (equal? ((module-ref m 'tty-set-terminal-modes-steps) 0 24 0)"
          "          '((\"newlines\" 24) \"cursor-normal\" \"keypad-mode\"))"
          "  (equal? ((module-ref m 'tty-set-terminal-modes-steps) 0 24 1)"
          "          '((\"newlines\" 24) \"cursor-visible\" \"keypad-mode\"))"
          ;; reset-terminal-modes: the fixed 5-step order.
          "  (equal? ((module-ref m 'tty-reset-terminal-modes-steps))"
          "          '(\"end-keypad-mode\" \"cursor-normal\" \"end-termcap-modes\""
          "            \"orig-pair\" (\"raw-cr\")))"
          ;; cursor-to: #nil on no move, else the conditional resets plus
          ;; the move marker, in order.
          "  (eq? ((module-ref m 'tty-cursor-to-steps) 5 5 5 5 0 0) #nil)"
          "  (equal? ((module-ref m 'tty-cursor-to-steps) 0 0 5 7 1 1)"
          "          '((\"move\" 5 7)))"
          "  (equal? ((module-ref m 'tty-cursor-to-steps) 0 0 5 7 0 1)"
          "          '((\"background\") (\"move\" 5 7)))"
          "  (equal? ((module-ref m 'tty-cursor-to-steps) 0 0 5 7 1 0)"
          "          '((\"off-insert\") (\"move\" 5 7)))"
          "  (equal? ((module-ref m 'tty-cursor-to-steps) 0 0 5 7 0 0)"
          "          '((\"background\") (\"off-insert\") (\"move\" 5 7)))"
          ;; raw-cursor-to: the same shape, with the target row / col.
          "  (eq? ((module-ref m 'tty-raw-cursor-to-steps) 5 5 5 5 0 0) #nil)"
          "  (equal? ((module-ref m 'tty-raw-cursor-to-steps) 0 0 5 7 1 1)"
          "          '((\"move\" 5 7)))"
          "  (equal? ((module-ref m 'tty-raw-cursor-to-steps) 0 0 5 7 0 1)"
          "          '((\"background\") (\"move\" 5 7)))"
          "  (equal? ((module-ref m 'tty-raw-cursor-to-steps) 0 0 5 7 1 0)"
          "          '((\"off-insert\") (\"move\" 5 7)))"
          "  (equal? ((module-ref m 'tty-raw-cursor-to-steps) 0 0 5 7 0 0)"
          "          '((\"background\") (\"off-insert\") (\"move\" 5 7))))"
          " 1 0))")))))

;; The #nil rule.  The two cursor procedures return #nil when the target
;; equals the current cursor, so the hub emits nothing (C tests the whole
;; list with NILP).  The move case is never #nil; it always ends in the
;; "move" marker.
(ert-deftest m52-imp6/nil-rule ()
  "Each cursor procedure returns #nil on no move, and a list otherwise."
  (should
   (eql 1
        (eval-scheme
         (concat
          "(let ((m (resolve-module '(emacs tty-output))))"
          " (if (and"
          "  (eq? ((module-ref m 'tty-cursor-to-steps) 3 4 3 4 0 0) #nil)"
          "  (eq? ((module-ref m 'tty-raw-cursor-to-steps) 3 4 3 4 0 0) #nil)"
          "  (pair? ((module-ref m 'tty-cursor-to-steps) 3 4 3 5 0 0))"
          "  (pair? ((module-ref m 'tty-raw-cursor-to-steps) 3 4 3 5 0 0)))"
          " 1 0))")))))

;; The partial-match rule.  A move is suppressed ONLY when BOTH
;; coordinates match.  If EITHER coordinate differs, the hub moves.  So
;; a wrong `or` (instead of `and`) in the Scheme would wrongly return
;; #nil when just one coordinate matches.  This check pins that shape
;; for both cursor procedures.
(ert-deftest m52-imp6/partial-match-still-moves ()
  "One matching coordinate is not enough to suppress the move."
  (should
   (eql 1
        (eval-scheme
         (concat
          "(let ((m (resolve-module '(emacs tty-output))))"
          " (if (and"
          ;; cur_y == vpos, cur_x != hpos -> move.
          "  (equal? ((module-ref m 'tty-cursor-to-steps) 5 0 5 7 1 1)"
          "          '((\"move\" 5 7)))"
          ;; cur_x == hpos, cur_y != vpos -> move.
          "  (equal? ((module-ref m 'tty-cursor-to-steps) 0 7 5 7 1 1)"
          "          '((\"move\" 5 7)))"
          ;; the same shape for raw-cursor-to: cur_row == row, cur_col != col.
          "  (equal? ((module-ref m 'tty-raw-cursor-to-steps) 5 0 5 7 1 1)"
          "          '((\"move\" 5 7)))"
          ;; cur_col == col, cur_row != row.
          "  (equal? ((module-ref m 'tty-raw-cursor-to-steps) 0 7 5 7 1 1)"
          "          '((\"move\" 5 7))))"
          " 1 0))")))))

;; The module loads and exports the 4 new procedures.  A missing module
;; or export yields 0, so the check FAILS on any gap.  This keeps the
;; Scheme side covered on every host, with or without pty support.
(ert-deftest m52-imp6/module-exports-policy ()
  "The (emacs tty-output) module exports the 4 imp-6 policy procedures."
  (should
   (eql 1
        (eval-scheme
         (concat
          "(let ((m (resolve-module '(emacs tty-output))))"
          " (if (and (procedure? (module-ref m 'tty-set-terminal-modes-steps))"
          "  (procedure? (module-ref m 'tty-reset-terminal-modes-steps))"
          "  (procedure? (module-ref m 'tty-cursor-to-steps))"
          "  (procedure? (module-ref m 'tty-raw-cursor-to-steps)))"
          " 1 0))")))))

;; The marker-only rule for the two cursor procedures.  brief.org
;; section 6 says do NOT add a KEY step to the two cursor hubs: their
;; only output is the conditional resets plus the "move" marker.  This
;; check fails if a rewrite returns a bare KEY string (which the C would
;; then resolve with m52_cap_string_1).  It also pins that the "move"
;; marker carries the target (vpos hpos) for cursor-to and (row col) for
;; raw-cursor-to, in CAR order, last.
(ert-deftest m52-imp6/cursor-hubs-markers-only ()
  "The two cursor procedures return only marker steps, and end with the move marker."
  (should
   (eql 1
        (eval-scheme
         (concat
          "(let ((m (resolve-module '(emacs tty-output))))"
          " (if (and"
          "  (null? (filter string? ((module-ref m 'tty-cursor-to-steps) 0 0 5 7 0 0)))"
          "  (null? (filter string? ((module-ref m 'tty-raw-cursor-to-steps) 0 0 5 7 0 0)))"
          "  (equal? (car (reverse ((module-ref m 'tty-cursor-to-steps) 0 0 5 7 0 0)))"
          "          '(\"move\" 5 7))"
          "  (equal? (car (reverse ((module-ref m 'tty-raw-cursor-to-steps) 2 3 9 4 0 0)))"
          "          '(\"move\" 9 4)))"
          " 1 0))")))))

(princ (format "=== m52 imp-6 policy suite done (%d cases) ===\n"
               m52-imp6--registered))
