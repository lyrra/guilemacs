;;; test-m23-imp2.el --- M23 imp-2 cross-file keyboard globals tests.
;;;
;;; imp-2 moves the 22 cross-file DEFVAR_LISP/_INT/_BOOL call sites out
;;; of syms_of_keyboard into src/keyboard-globals.c (wired into emacs.c
;;; as syms_of_keyboard_globals).  Pure relocation: each variable's doc
;;; string and default-value line moved verbatim.  See brief.org.
;;;
;;; The regression these tests catch is Risk 2 from docs/m23-plan.org: a
;;; missing syms_of_keyboard_globals() call in emacs.c is a *silent*
;;; void-variable at runtime, not a build failure.  Each case therefore
;;; first asserts the variable is bound (not void-variable); most then
;;; assert the default value read back at load time.
;;;
;;; Values were captured live by loading this file under the built emacs.
;;; Exceptions (boundp only, value not asserted):
;;;   * tty-erase-char   - "set up in sysdep.c"; no DEFVAR default, and
;;;                        reading it before a terminal exists segfaults
;;;                        this guilemacs build (pre-existing, unrelated
;;;                        to the relocation).  FIX-20260902-guilemacs.
;;;   * top-level        - DEFVAR default is nil but startup binds it to
;;;                        (normal-top-level) before tests load.
;;;   * key-translation-map - C installs a sparse keymap; asserted via a
;;;                        keymapp predicate rather than an exact value.
;;;
;;; Plain-elisp corpus: prints PASS/FAIL lines + a summary, read from the
;;; harness output like the other test/keyboard/test-m2x-*.el corpora.

(princ "=== m23 imp-2 test suite ===\n")

(defvar gm2-pass 0)
(defvar gm2-fail 0)

(defun gm2-report (name ok expected actual)
  (if ok
      (setq gm2-pass (1+ gm2-pass))
    (setq gm2-fail (1+ gm2-fail)))
  (princ (format "%s %s%s\n" (if ok "PASS" "FAIL") name
                 (if ok "" (format " (expected %S, got %S)" expected actual)))))

;; Each case: (elisp-name expected).  expected is:
;;   * bound-only  -> assert the variable is bound (no value check)
;;   * a value     -> assert (symbol-value var) equals it
;;   * (keymap)    -> assert (keymapp (symbol-value var))
(defvar gm2-cases
  '((last-command-event nil)
    (last-nonmenu-event nil)
    (last-input-event nil)
    (unread-command-events nil)
    (meta-prefix-char ?\e)
    (this-command nil)
    (real-this-command nil)
    (this-original-command nil)
    (double-click-time 500)
    (num-nonmacro-input-events 0)
    (tty-erase-char bound-only)
    (help-form nil)
    (top-level bound-only)
    (extra-keyboard-modifiers 0)
    (deactivate-mark nil)
    (overriding-local-map nil)
    (overriding-local-map-menu-flag nil)
    (track-mouse nil)
    (key-translation-map keymap)
    (delayed-warnings-list nil)
    (throw-on-input nil)
    (mwheel-coalesce-scroll-events t)))

(dolist (case gm2-cases)
  (let ((var (car case))
        (expected (cadr case)))
    (gm2-report (format "m23/imp2/%s/boundp" var)
                (boundp var) 'boundp t)
    (cond
     ((eq expected 'bound-only)
      ;; Existence only.  Do NOT read the value: tty-erase-char segfaults
      ;; this build on read before a terminal exists (see file header).
      nil)
     ((eq expected 'keymap)
      (gm2-report (format "m23/imp2/%s/keymapp" var)
                  (keymapp (symbol-value var)) t nil))
     (t
      (gm2-report (format "m23/imp2/%s/default" var)
                  (equal expected (symbol-value var)) expected (symbol-value var))))))

;; deactivate-mark must stay buffer-local: its DEFVAR and the
;; Fmake_variable_buffer_local call were both moved to keyboard-globals.c
;; in this same order.  If only the DEFVAR had been relocated, the Fmake
;; would have run first and the buffer-local redirect would have been
;; overwritten, silently de-buffer-localizing it.
(gm2-report "m23/imp2/deactivate-mark/buffer-local"
            (local-variable-if-set-p 'deactivate-mark) t nil)

(princ (format "=== %d passed, %d failed, %d total ===\n"
               gm2-pass gm2-fail (+ gm2-pass gm2-fail)))
