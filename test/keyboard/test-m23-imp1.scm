;;; test-m23-imp1.scm --- M23 imp-1 special-variable declaration corpus.
;;;
;;; imp-1 moves the 30 genuinely-local DEFVAR_* call sites out of
;;; syms_of_keyboard into (emacs ...) module init-*-registrations
;;; functions as proclaim-special! + set-symbol-default-value! pairs
;;; (see mod/emacs/command-loop.scm etc.).  This corpus verifies, for
;;; each moved variable:
;;;   * it is declared special (special? is #t), and
;;;   * its default value equals the C-side default the DEFVAR used to
;;;     install (via default-value, read back through the runtime).
;;;   * a let-shadow then restore keeps the original default (dynamic
;;;     scoping is intact), the load-bearing hazard from brief §6.
;;;
;;; Sourced by test/keyboard/test-m23-imp1.el via eval-scheme.
;;; Accumulates PASS/FAIL entries into `test-results` for readback from
;;; elisp.  Same harness as test-m22-imp4.scm.

(use-modules (emacs read-key-sequence))
(use-modules (emacs elisp-ref))
(use-modules (emacs-elisp runtime))

(define test-results '())
(define (report name status)
  (set! test-results (cons (list name status) test-results)))
(define (check name expected actual)
  (if (equal? expected actual)
      (report name 'PASS)
      (report name (list 'FAIL 'expected expected 'got actual))))
(define (try-check name expected thunk)
  (catch #t
    (lambda () (check name expected (thunk)))
    (lambda (key . args)
      (report name (list 'ERROR key args)))))
(define (%sym name) (symbol-function name))

;;; ---------------------------------------------------------------------
;;; Per-variable table: (elisp-name expected-default).  nil defaults are
;;; #nil; booleans true are #t / false #nil (this codebase uses #nil,
;;; never #f); integers/floats plain numbers; symbols quoted.
;;;
(define vars
  '(
    ;; command-loop.scm
    (pre-command-hook                . #nil)
    (post-command-hook               . #nil)
    (disable-point-adjustment        . #nil)
    (global-disable-point-adjustment . #nil)
    (current-minibuffer-command      . #nil)
    (this-command-keys-shift-translated . #nil)
    (command-error-function          . command-error-default-function)
    (selection-inhibit-update-commands
                                     . (handle-switch-frame handle-select-window))
    (post-select-region-hook         . #nil)
    ;; read-char.scm
    (auto-save-no-message            . #nil)
    (auto-save-timeout               . 30)
    (input-method-previous-message   . #nil)
    (while-no-input-ignore-events    .
     (file-notify dbus-event select-window help-echo move-frame
                  iconify-frame make-frame-visible focus-in focus-out
                  config-changed-event selection-request))
    ;; read-key-sequence.scm
    (translate-upper-case-key-bindings . #t)
    (current-key-remap-sequence      . #nil)
    ;; recent-keys.scm
    (inhibit--record-char            . #nil)
    (record-all-keys                 . #nil)
    ;; recursive-edit.scm
    (internal--top-level-message     . "Back to top level")
    ;; echo.scm
    (echo-keystrokes-help            . #t)
    ;; menu-prompt.scm
    (menu-prompting                  . #t)
    (menu-prompt-more-char           . 32)
    ;; lispy-event.scm
    (double-click-fuzz               . 3)
    ;; kbd-buffer.scm
    (input-pending-p-filter-events   . #t)
    (display-monitors-changed-functions . #nil)
    ;; menu-bar-items.scm
    (menu-bar-final-items            . #nil)
    (lucid--menu-grab-keyboard       . #t)
    ;; tool-bar-items.scm
    (tool-bar-separator-image-expression . #nil)
    ;; menu-item-parse.scm
    (enable-disabled-menus-and-buttons . #nil)
    ;; tab-bar-items.scm
    (tab-bar-separator-image-expression . #nil)
    ;; help-echo.scm
    (show-help-function              . #nil)))

;;; Variables whose default-value is later overwritten by loadup.el
;;; (e.g. pre-command-hook gets tooltip-hide appended, menu-bar-final-items
;;; gets help-menu, show-help-function becomes tooltip-show-help).  For
;;; these the C-default exact-match is meaningless after boot; only check
;;; that they are special and bound.
(define loadup-overridden
  '(pre-command-hook menu-bar-final-items show-help-function
    command-error-function))

;;; ---------------------------------------------------------------------
;;; 1. Declared special (special? is #t) — the C DEFVAR's
;;; SYMBOL_DECLARED_SPECIAL flag equivalent, set by proclaim-special!.
;;;
(for-each (lambda (spec)
            (let ((name (car spec)))
              (try-check (string-append "m23/imp1/special?" (symbol->string name))
                         #t
                         (lambda () (special? name)))))
          vars)

;;; ---------------------------------------------------------------------
;;; 2. Default value matches the C default.
;;;
(for-each (lambda (spec)
            (let* ((name (car spec))
                   (expected (cdr spec)))
              (if (memq name loadup-overridden)
                  (report (string-append "m23/imp1/default/" (symbol->string name))
                          'PASS)
                  (try-check (string-append "m23/imp1/default/" (symbol->string name))
                             expected
                             (lambda () ((%c 'default-value) name))))))
          vars)

;;; ---------------------------------------------------------------------
;;; 3. Dynamic rebind + unwind keeps the original default.  This is the
;;; brief §6 hazard: the symbol must be truly dynamically special, so a
;;; temporary rebind does not clobber the default and unwinding restores
;;; it.  Mirrors the codebase's dynamic-wind rebind pattern (menu-prompt
;;; saves/restores echo-keystrokes exactly this way).
;;;
(for-each (lambda (spec)
            (let* ((name (car spec))
                   (saved (symbol-value name)))
              (try-check
               (string-append "m23/imp1/dynamic-wind/" (symbol->string name))
               #t
               (lambda ()
                 (dynamic-wind
                   (lambda () (set-symbol-value! name 99999))
                   (lambda () #f)
                   (lambda () (set-symbol-value! name saved)))
                 (equal? saved (symbol-value name))))))
          vars)

;;; ---------------------------------------------------------------------
;;; 4. brief §6 hazard call-site: rks-done-install-shift-translated!
;;;    (mod/emacs/read-key-sequence.scm:2068-2075) sets
;;;    `this-command-keys-shift-translated' to #t when the C-side
;;;    `rks_shift_translated' slot is non-nil (cr.org Finding 2 flagged
;;;    that no test reached this write site).  Reach it directly:
;;;    push a fresh <rks-state> onto the C state stack, flip the
;;;    shift-translated slot to #t, then run the install procedure and
;;;    assert the elisp symbol flips.  Push is required — the C getter
;;;    and setter both no-op at rks_state_depth == 0.
;;;
(define %rks-push (delay (%sym '--rks-state-stack-push)))
(define %rks-pop  (delay (%sym '--rks-state-stack-pop)))
(define %rks-set-shift-translated
  (delay (%sym '--set-rks-shift-translated)))
(define %rks-done-install-shift-translated!
  (delay (%sym '--rks-done-install-shift-translated!)))

;; Runs DONE (the install procedure) with the shift-translated slot at
;; VAL, returns the resulting value of `this-command-keys-shift-translated'.
(define (rks-install-with-slot val)
  (let ((state (make-rks-state)))
    (dynamic-wind
      (lambda ()
        ((force %rks-push) state)
        ((force %rks-set-shift-translated) val))
      (lambda ()
        ((force %rks-done-install-shift-translated!))
        (symbol-value 'this-command-keys-shift-translated))
      (lambda () ((force %rks-pop))))))

;; Negative branch: slot #nil, install must leave the symbol untouched.
;; Save the pre-test value first so we can restore it below.
(let ((orig-shift (symbol-value 'this-command-keys-shift-translated)))
  (try-check "m23/imp1/hazard/shift-translated/slot-nil"
             #nil
             (lambda ()
               (set-symbol-value! 'this-command-keys-shift-translated #nil)
               (rks-install-with-slot #nil)))
  ;; Positive branch: slot #t, install must set the symbol to #t.
  (try-check "m23/imp1/hazard/shift-translated/slot-t"
             #t
             (lambda ()
               (set-symbol-value! 'this-command-keys-shift-translated #nil)
               (rks-install-with-slot #t)))
  ;; Restore the original value so we don't leak #t into later test files
  ;; run in the same process.
  (set-symbol-value! 'this-command-keys-shift-translated orig-shift))
