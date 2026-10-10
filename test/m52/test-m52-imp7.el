;;; test-m52-imp7.el --- M52 imp-7 clear-selection tests.  -*- lexical-binding: t; -*-
;;;
;;; M52 imp-7 moves the DECISION of 3 src/term.c clear hubs into the
;;; module (emacs tty-output): tty_clear_to_end, tty_clear_frame, and
;;; tty_clear_end_of_line.  Each hub keeps its C state read, its FILE *
;;; streams, and its OUTPUT / OUTPUT1 padding; only the one-step
;;; selection runs in Scheme.
;;;
;;; This corpus checks the observable behaviour on every host:
;;;   1. The headless policy table.  It resolves the module through
;;;      `eval-scheme' and calls each of the 3 procedures for every flag
;;;      combination.  It checks the returned step (a KEY string or a
;;;      MARKER list), the marker shape (a plain list), and the #nil case.
;;;   2. The headless #nil rule for the end-of-line guard: the 0-width
;;;      region case (costs-set 0, and cur-x at or past first-unused-hpos)
;;;      returns #nil, so the hub emits nothing.
;;;   3. The module-export check for the 3 new procedures.
;;;   4. One pty case (m52-imp7/policy-key-e2e) that drives the built
;;;      Emacs.
;;;
;;; LIMITATION (brief.org section 5).  No deterministic elisp trigger
;;; reaches the 3 rewired hubs from a hook: the 3 clear hubs run inside
;;; the redisplay path after the costs have been calculated.  So the pty
;;; case drives the policy -> key -> bytes chain: the child calls the 3
;;; policy procedures through `module-ref' and emits each returned KEY
;;; (string) step through --tty-emit-cap.  It skips the marker steps.  It
;;; does NOT prove that the rewired hubs ran.  The hub rewiring is a C
;;; source fact; it is not asserted here (this behaviour corpus holds no
;;; source-layout checks, the imp-3 rule).  A pty allocation failure is
;;; an explicit INFO skip, never a PASS.  The case pins NO provisional
;;; byte span (brief.org section 5); a hard-coded TERM=xterm span is
;;; forbidden.

(princ "=== m52 imp-7 clear-selection policy suite ===\n")

(require 'imp-ert-report)

(let ((dir (expand-file-name "../m42"
                             (file-name-directory
                              (or load-file-name default-directory)))))
  (add-to-list 'load-path dir)
  (require 'pty-runner))

(defvar m52-imp7--registered 0
  "Number of M52 imp-7 pty cases registered by this corpus.")

(let* ((results
        (condition-case err
            (m52-imp7-run-driver)
          (error (list (cons "m52-imp7/runner" (cons 'FAIL (format "%S" err)))))))
       (wanted m52-imp7--cases))
  (when (null results)
    (setq results (list (cons "m52-imp7/report"
                              (cons 'FAIL "driver produced no case results")))))
  (dolist (name wanted)
    (unless (assoc name results)
      (setq results (append results
                            (list (cons name (cons 'FAIL "driver omitted this case")))))))
  (dolist (result results)
    (let ((name (car result))
          (status (cdr result)))
      (setq m52-imp7--registered (1+ m52-imp7--registered))
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

(ert-deftest m52-imp7/gate-has-output-cases ()
  "The M52 group registers the M52 imp-7 pty case."
  (should (>= m52-imp7--registered 1)))

;; The headless policy table.  It proves that the DECISION runs in
;; Scheme: each procedure returns the right step for every flag
;; combination.  Every KEY string is one of the m52_caps keys
;; (clear-to-bottom, clear-frame, clear-line), so a rewrite that returns
;; a key the C table does not hold would FAIL here.  The marker steps
;; ("clear-loop", "clear-frame-fallback", "clear-line-hard") are plain
;; lists.
(ert-deftest m52-imp7/policy-table ()
  "Each policy procedure selects the right step, or #nil, for its flags."
  (should
   (eql 1
        (eval-scheme
         (concat
          "(let ((m (resolve-module '(emacs tty-output))))"
          " (if (and"
          ;; clear-to-end: the capability KEY when present, else the loop
          ;; MARKER.
          "  (equal? ((module-ref m 'tty-clear-to-end-steps) 1) \"clear-to-bottom\")"
          "  (equal? ((module-ref m 'tty-clear-to-end-steps) 0) '(\"clear-loop\"))"
          ;; clear-frame: the capability KEY when present, else the
          ;; fallback MARKER.
          "  (equal? ((module-ref m 'tty-clear-frame-steps) 1) \"clear-frame\")"
          "  (equal? ((module-ref m 'tty-clear-frame-steps) 0) '(\"clear-frame-fallback\"))"
          ;; clear-end-of-line: the capability KEY when present, else the
          ;; hard-way MARKER.
          "  (equal? ((module-ref m 'tty-clear-end-of-line-steps) 1 3 8 1) \"clear-line\")"
          "  (equal? ((module-ref m 'tty-clear-end-of-line-steps) 1 3 8 0) '(\"clear-line-hard\")))"
          " 1 0))")))))

;; The #nil rule.  The end-of-line procedure returns #nil when a guard
;; holds, so the hub emits nothing (C tests the whole step with NILP).
;; Two guards: the costs have never been calculated (costs-set 0), and
;; the erase region is 0-width (cur-x at or past first-unused-hpos).
(ert-deftest m52-imp7/nil-rule ()
  "The end-of-line procedure returns #nil on either guard."
  (should
   (eql 1
        (eval-scheme
         (concat
          "(let ((m (resolve-module '(emacs tty-output))))"
          " (if (and"
          ;; costs-set 0 -> #nil, whatever the other flags.
          "  (eq? ((module-ref m 'tty-clear-end-of-line-steps) 0 3 8 1) #nil)"
          "  (eq? ((module-ref m 'tty-clear-end-of-line-steps) 0 9 8 0) #nil)"
          ;; cur-x == first-unused-hpos -> #nil (0-width region).
          "  (eq? ((module-ref m 'tty-clear-end-of-line-steps) 1 8 8 1) #nil)"
          ;; cur-x > first-unused-hpos -> #nil.
          "  (eq? ((module-ref m 'tty-clear-end-of-line-steps) 1 9 8 0) #nil)"
          ;; the live region is never #nil.
          "  (string? ((module-ref m 'tty-clear-end-of-line-steps) 1 2 8 1))"
          "  (pair? ((module-ref m 'tty-clear-end-of-line-steps) 1 2 8 0)))"
          " 1 0))")))))

;; The key / marker split.  brief.org section 3: a KEY step is a plain
;; string; a MARKER step is a plain list.  The C hub tells them apart
;; with STRINGP.  This check fails if a rewrite returns the wrong kind,
;; and it pins the exact marker tags.
(ert-deftest m52-imp7/key-and-marker-shapes ()
  "Each procedure returns a string KEY or a list MARKER, as the brief says."
  (should
   (eql 1
        (eval-scheme
         (concat
          "(let ((m (resolve-module '(emacs tty-output))))"
          " (if (and"
          "  (string? ((module-ref m 'tty-clear-to-end-steps) 1))"
          "  (equal? ((module-ref m 'tty-clear-to-end-steps) 0) '(\"clear-loop\"))"
          "  (string? ((module-ref m 'tty-clear-frame-steps) 1))"
          "  (equal? ((module-ref m 'tty-clear-frame-steps) 0) '(\"clear-frame-fallback\"))"
          "  (string? ((module-ref m 'tty-clear-end-of-line-steps) 1 2 8 1))"
          "  (equal? ((module-ref m 'tty-clear-end-of-line-steps) 1 2 8 0)"
          "          '(\"clear-line-hard\")))"
          " 1 0))")))))

;; The module loads and exports the 3 new procedures.  A missing module
;; or export yields 0, so the check FAILS on any gap.  This keeps the
;; Scheme side covered on every host, with or without pty support.
(ert-deftest m52-imp7/module-exports-policy ()
  "The (emacs tty-output) module exports the 3 imp-7 policy procedures."
  (should
   (eql 1
        (eval-scheme
         (concat
          "(let ((m (resolve-module '(emacs tty-output))))"
          " (if (and (procedure? (module-ref m 'tty-clear-to-end-steps))"
          "  (procedure? (module-ref m 'tty-clear-frame-steps))"
          "  (procedure? (module-ref m 'tty-clear-end-of-line-steps)))"
          " 1 0))")))))

(princ (format "=== m52 imp-7 policy suite done (%d cases) ===\n"
               m52-imp7--registered))
