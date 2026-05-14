;;; ertest-command-loop.el --- M7a ERT suite for (emacs command-loop)

;; M7a — first slice of the command_loop_1 port.  Tests the prologue
;; that runs at each top-of-loop entry: per-command state reset, the
;; trailing post-command-hook + delayed-warnings-hook for the previous
;; command, and the kboard last-command save.
;;
;; The prologue is exposed via `--command-loop-1-prologue' for direct
;; testing.  Production calls flow through C command_loop_1 →
;; command_loop_1_prologue → Scheme dispatch.
;;
;; See docs/keyboard.org §"M7a — command_loop_1 prologue".

(require 'ert)

;;;; Existence checks

(ert-deftest m7a-prologue/exists ()
  (should (fboundp '--command-loop-1-prologue)))

(ert-deftest m7a-helpers/exist ()
  (should (fboundp '--cancel-echoing))
  (should (fboundp '--safe-run-hooks))
  (should (fboundp '--safe-run-hooks-maybe-narrowed-selected))
  (should (fboundp '--resize-echo-area-exactly))
  (should (fboundp '--echo-area-buffer-0-non-empty-p))
  (should (fboundp '--clear-waiting-for-input)))

;;;; State-reset behavior

(ert-deftest m7a-prologue/clears-this-command-key-count ()
  (set--this-command-keys "abc")
  (should (= 3 (--this-command-key-count)))
  (--command-loop-1-prologue)
  (should (= 0 (--this-command-key-count))))

(ert-deftest m7a-prologue/clears-this-single-command-key-start ()
  ;; Some prior state — call the M5 setter so we have something to reset.
  (--set-this-command-key-count 5)
  (--set-this-single-command-key-start 3)
  (--command-loop-1-prologue)
  (should (= 0 (--this-single-command-key-start))))

(ert-deftest m7a-prologue/clears-kboard-prefix-args ()
  (let ((kb (current-kboard)))
    (set-kboard-prefix-arg      kb '(4))
    (set-kboard-last-prefix-arg kb '(16))
    (--command-loop-1-prologue)
    (should (eq nil (kboard-prefix-arg      kb)))
    (should (eq nil (kboard-last-prefix-arg kb)))))

(ert-deftest m7a-prologue/clears-deactivate-mark ()
  (setq deactivate-mark t)
  (--command-loop-1-prologue)
  (should (eq nil deactivate-mark)))

;;;; last-command save (prev-command transition)

(ert-deftest m7a-prologue/saves-this-command-into-last-command ()
  ;; Set this-command and real-this-command, then run the prologue.
  ;; Afterwards the kboard's last-command should reflect this-command.
  (let ((kb (current-kboard)))
    (setq this-command       'sentinel-cmd-a)
    (setq real-this-command  'sentinel-real-a)
    (--command-loop-1-prologue)
    (should (eq 'sentinel-cmd-a  (kboard-last-command      kb)))
    (should (eq 'sentinel-real-a (kboard-real-last-command kb)))
    ;; Clean up
    (setq this-command nil real-this-command nil)))

(ert-deftest m7a-prologue/saves-last-repeatable-only-when-event-not-cons ()
  ;; If last-command-event is a cons (e.g. a mouse click), last-repeatable
  ;; should NOT be updated.  Otherwise it should be.
  (let ((kb (current-kboard)))
    ;; Case 1: non-cons last-command-event → save fires.
    (setq this-command 'sentinel-real-b
          real-this-command 'sentinel-real-b
          last-command-event ?a)
    (set-kboard-last-repeatable-command kb 'pre-existing)
    (--command-loop-1-prologue)
    (should (eq 'sentinel-real-b (kboard-last-repeatable-command kb)))
    ;; Case 2: cons last-command-event → save skipped.
    (setq this-command 'sentinel-real-c
          real-this-command 'sentinel-real-c
          last-command-event '(mouse-1 0))
    (set-kboard-last-repeatable-command kb 'pre-existing-2)
    (--command-loop-1-prologue)
    (should (eq 'pre-existing-2 (kboard-last-repeatable-command kb)))
    ;; Clean up
    (setq this-command nil real-this-command nil last-command-event nil)
    (set-kboard-last-repeatable-command kb nil)))

;;;; memory-full short-circuit

(ert-deftest m7a-prologue/memory-full-skips-hooks ()
  ;; When memory-full is t, post-command-hook / delayed-warnings-hook
  ;; must NOT run.  We probe by adding a hook that mutates a sentinel
  ;; and checking it's untouched.
  (let ((sentinel nil)
        (hook (lambda () (setq sentinel 'ran))))
    (unwind-protect
        (progn
          (add-hook 'post-command-hook hook)
          (setq memory-full t)
          (--command-loop-1-prologue)
          (should (eq sentinel nil)))
      (remove-hook 'post-command-hook hook)
      (setq memory-full nil))))

(provide 'ertest-command-loop)

;;; ertest-command-loop.el ends here
