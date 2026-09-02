;;; test-m23-imp3.el --- M23 imp-3 DEFVAR_KBOARD relocation tests.
;;;
;;; imp-3 moves the 8 DEFVAR_KBOARD call sites out of syms_of_keyboard in
;;; src/keyboard.c into src/keyboard-globals.c, mirroring imp-2.  Pure
;;; relocation: each DEFVAR_KBOARD registers a Lisp_Kboard_Objfwd
;;; forwarding into struct kboard (offsetof) that dispatches through
;;; current_kboard, so the call site is not tied to any translation unit
;;; and no struct, macro, or forwarding logic changed.  See brief.org.
;;;
;;; The regression these tests catch is a missing registration at
;;; runtime (void-variable), not a build failure.  Each case asserts the
;;; variable is bound, and reads back its default at load time.
;;;
;;; Value caveat (mirrors imp-2): 5 of the 8 names have no literal
;;; default in syms_of_keyboard and read nil at fresh boot.
;;; local-function-key-map and input-decode-map get their real value (a
;;; keymap) from init_kboard at allocate_kboard time, so they are
;;; asserted via keymapp rather than an exact value (same caveat
;;; test-m23-imp2.el recorded for key-translation-map).
;;; keyboard-translate-table likewise gets a char-table from init_kboard,
;;; so it is asserted via char-table-p.
;;;
;;; Plain-elisp corpus: prints PASS/FAIL lines + a summary, read from the
;;; harness output like the other test/keyboard/test-m2x-*.el corpora.

(princ "=== m23 imp-3 test suite ===\n")

(defvar gm3-pass 0)
(defvar gm3-fail 0)

(defun gm3-report (name ok expected actual)
  (if ok
      (setq gm3-pass (1+ gm3-pass))
    (setq gm3-fail (1+ gm3-fail)))
  (princ (format "%s %s%s\n" (if ok "PASS" "FAIL") name
                 (if ok "" (format " (expected %S, got %S)" expected actual)))))

;; Each case: (elisp-name expected).  expected is:
;;   * nil       -> assert bound and (symbol-value var) is nil
;;   * keymap    -> assert bound and (keymapp (symbol-value var))
;;   * char-table -> assert bound and (char-table-p (symbol-value var))
(defvar gm3-cases
  '((last-command nil)
    (real-last-command nil)
    (last-repeatable-command nil)
    (keyboard-translate-table char-table)
    (overriding-terminal-local-map nil)
    (system-key-alist nil)
    (local-function-key-map keymap)
    (input-decode-map keymap)))

(dolist (case gm3-cases)
  (let ((var (car case))
        (expected (cadr case)))
    (gm3-report (format "m23/imp3/%s/boundp" var)
                (boundp var) 'boundp t)
    (cond
     ((eq expected 'keymap)
      (gm3-report (format "m23/imp3/%s/keymapp" var)
                  (keymapp (symbol-value var)) t nil))
     ((eq expected 'char-table)
      (gm3-report (format "m23/imp3/%s/char-table-p" var)
                  (char-table-p (symbol-value var)) t nil))
     (t
      (gm3-report (format "m23/imp3/%s/default" var)
                  (null (symbol-value var)) nil (symbol-value var))))))

(princ (format "=== %d passed, %d failed, %d total ===\n"
               gm3-pass gm3-fail (+ gm3-pass gm3-fail)))
