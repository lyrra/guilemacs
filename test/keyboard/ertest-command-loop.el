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

;;;; M7b1 — pre-read iteration

(ert-deftest m7b1-iter-pre-read/exists ()
  (should (fboundp '--command-loop-1-iter-pre-read)))

(ert-deftest m7b1-helpers/exist ()
  (should (fboundp '--selected-frame-live-p))
  (should (fboundp '--set-buffer-from-selected-window))
  (should (fboundp '--display-pending-malloc-warnings-loop))
  (should (fboundp '--clear-ignore-mouse-drag))
  (should (fboundp '--minibuf-and-echo-area-aligned-p))
  (should (fboundp '--resize-mini-window-minibuf-non-shrink))
  (should (fboundp '--quit-char))
  (should (fboundp '--set-raw-keybuf-count))
  (should (fboundp '--read-key-sequence))
  (should (fboundp '--inc-num-input-keys)))

(ert-deftest m7b1-helpers/selected-frame-live-p-batch ()
  ;; Batch always has a (selected) terminal frame.
  (should (eq t (--selected-frame-live-p))))

(ert-deftest m7b1-helpers/minibuf-and-echo-aligned-p-batch ()
  ;; No minibuffer active at batch top-level: the predicate must return nil.
  (should (eq nil (--minibuf-and-echo-area-aligned-p))))

(ert-deftest m7b1-helpers/quit-char-default ()
  ;; Default quit-char is C-g = 7.
  (should (= 7 (--quit-char))))

(ert-deftest m7b1-iter-pre-read/resets-this-command-vars ()
  ;; Set the four vars to non-nil, then run a single iteration with
  ;; unread-command-events queued (so we don't block).  After return,
  ;; this-original-command should be nil (the pre-read reset cleared it).
  (setq this-command 'X
        real-this-command 'Y
        this-original-command 'Z
        this-command-keys-shift-translated t)
  (setq unread-command-events (list ?a))
  (let ((outcome (--command-loop-1-iter-pre-read)))
    ;; outcome should be 0 (OK) since we had one key to read.
    (should (= 0 outcome)))
  (should (eq nil this-original-command))
  (should (eq nil this-command-keys-shift-translated))
  ;; Also: deactivate-mark cleared.
  (should (eq nil deactivate-mark))
  ;; Clean up
  (setq this-command nil real-this-command nil
        this-original-command nil
        this-command-keys-shift-translated nil
        unread-command-events nil))

(ert-deftest m7b1-iter-pre-read/sets-last-command-event ()
  ;; Queue a known key; iter-pre-read should set last-command-event.
  (setq unread-command-events (list ?x))
  (--command-loop-1-iter-pre-read)
  (should (= ?x last-command-event))
  (setq unread-command-events nil last-command-event nil))

;; EOF branch (i==0) is not directly testable in batch — read_key_sequence
;; blocks on the kbd_buffer / terminal poll rather than returning 0 when
;; no events are queued.  Real EOF is reached only at the end of a kbd
;; macro replay; tests for that path would need execute-kbd-macro which
;; itself drives command_loop_1.  Coverage there comes via the existing
;; macro-related test suite plus the interactive smoke gate.

;;;; M7b2 — dispatch helpers

(ert-deftest m7b2-iter-dispatch/exists ()
  (should (fboundp '--command-loop-1-iter-dispatch)))

(ert-deftest m7b2-helpers/exist ()
  (should (fboundp '--clear-force-start-and-flush-buffer-unchanged))
  (should (fboundp '--read-key-sequence-cmd))
  (should (fboundp '--read-key-sequence-remapped))
  (should (fboundp '--maybe-quit))
  (should (fboundp '--save-state-for-redisplay-get-pt))
  (should (fboundp '--restore-last-point-position))
  (should (fboundp '--record-recent-keys-cmd-pseudo-event))
  (should (fboundp '--with-hourglass-protection))
  (should (fboundp '--save-point-before-last-command-or-undo))
  (should (fboundp '--reset-redisplay-tick-state))
  (should (fboundp '--clear-display-working-on-window-p)))

(ert-deftest m7b2-helper/save-state-returns-pt ()
  ;; --save-state-for-redisplay-get-pt returns current point as a fixnum.
  ;; Run in a fresh temp buffer so PT is deterministic.
  (with-temp-buffer
    (insert "abc")
    (goto-char 2)
    (should (= 2 (--save-state-for-redisplay-get-pt)))))

(ert-deftest m7b2-helper/with-hourglass-protection-runs-thunk ()
  ;; In batch (no window system), the wrapper just funcalls THUNK.
  (let ((sentinel 'unset))
    (--with-hourglass-protection (lambda () (setq sentinel 'ran)))
    (should (eq sentinel 'ran))))

(ert-deftest m7b2-helper/record-recent-keys-cmd-pushes-pseudo-event ()
  ;; Push a (nil . CMD) pseudo-event into the ring; verify recent-keys
  ;; with INCLUDE-CMDS=t surfaces it.  Clear after to avoid contamination.
  (clear-this-command-keys)
  (--record-recent-keys-cmd-pseudo-event 'm7b2-sentinel-cmd)
  (let ((rk (recent-keys t)))
    (should (or (vectorp rk) (stringp rk)))
    ;; recent-keys returns the chronological view; our event should be
    ;; in there.  Use equal because the cons cell isn't eq across calls.
    (let ((found nil))
      (dotimes (i (length rk))
        (let ((e (aref rk i)))
          (when (and (consp e) (eq (cdr e) 'm7b2-sentinel-cmd))
            (setq found t))))
      (should found)))
  (clear-this-command-keys))

(ert-deftest m7b2-helper/restore-last-point-position ()
  ;; --restore-last-point-position sets the C last_point_position
  ;; global.  We can't directly read it, but --save-state-for-redisplay-get-pt
  ;; also sets it; so the round-trip works.
  (with-temp-buffer
    (insert "abcdef")
    (goto-char 4)
    (--save-state-for-redisplay-get-pt)  ; sets last_point_position to 4
    (goto-char 2)
    (--restore-last-point-position 4)
    ;; No observable change in PT (we restore last_point_position only).
    (should (= 2 (point)))))

;;;; M7b3 — post-dispatch

(ert-deftest m7b3-iter-post-dispatch/exists ()
  (should (fboundp '--command-loop-1-iter-post-dispatch)))

(ert-deftest m7b3-helpers/exist ()
  (should (fboundp '--echo-area-window-eq-selected-frame-minibuf-p))
  (should (fboundp '--current-kboard-immediate-echo-p))
  (should (fboundp '--clear-current-kboard-immediate-echo))
  (should (fboundp '--echo-now)))

(ert-deftest m7b3-helper/current-kboard-immediate-echo-defaults-nil ()
  ;; Default state at batch startup: immediate-echo off.
  (should (eq nil (--current-kboard-immediate-echo-p))))

(ert-deftest m7b3-iter-post-dispatch/saves-last-prefix-arg ()
  ;; The first thing the post-dispatch helper does is save
  ;; Vcurrent_prefix_arg into the kboard's last-prefix-arg slot.
  (let ((kb (current-kboard)))
    (set-kboard-last-prefix-arg kb nil)
    (setq current-prefix-arg '(16))
    (--command-loop-1-iter-post-dispatch)
    (should (equal '(16) (kboard-last-prefix-arg kb)))
    ;; Cleanup
    (set-kboard-last-prefix-arg kb nil)
    (setq current-prefix-arg nil)))

(ert-deftest m7b3-iter-post-dispatch/saves-this-command-into-last-command ()
  ;; Mirrors the M7a save behavior but for the trailing path: after
  ;; dispatch, this-command / real-this-command get committed to the
  ;; kboard.  Use sentinels distinct from the M7a values.
  (let ((kb (current-kboard)))
    (setq this-command       'm7b3-sentinel-tc)
    (setq real-this-command  'm7b3-sentinel-rtc)
    (setq last-command-event ?z)  ; non-cons → last-repeatable updates
    (--command-loop-1-iter-post-dispatch)
    (should (eq 'm7b3-sentinel-tc  (kboard-last-command           kb)))
    (should (eq 'm7b3-sentinel-rtc (kboard-real-last-command      kb)))
    (should (eq 'm7b3-sentinel-rtc (kboard-last-repeatable-command kb)))
    ;; Cleanup
    (setq this-command nil real-this-command nil last-command-event nil)
    (set-kboard-last-command           kb nil)
    (set-kboard-real-last-command      kb nil)
    (set-kboard-last-repeatable-command kb nil)))

(ert-deftest m7b3-iter-post-dispatch/zeros-key-counters ()
  ;; After post-dispatch, both per-command key counters are 0.
  (set--this-command-keys "abcde")
  (should (= 5 (--this-command-key-count)))
  (--command-loop-1-iter-post-dispatch)
  (should (= 0 (--this-command-key-count)))
  (should (= 0 (--this-single-command-key-start))))

;;;; M7b4 — mark/region

(ert-deftest m7b4-iter-mark-region/exists ()
  (should (fboundp '--command-loop-1-iter-mark-region)))

(ert-deftest m7b4-helpers/exist ()
  (should (fboundp '--current-buffer-mark-active-p))
  (should (fboundp '--current-buffer-mark-has-buffer-p))
  (should (fboundp '--cl1-prev-buffer-current-p))
  (should (fboundp '--cl1-prev-modiff-current-p)))

(ert-deftest m7b4-helper/mark-active-default-nil ()
  ;; Default state at batch startup: mark not active.
  (with-temp-buffer
    (should (eq nil (--current-buffer-mark-active-p)))))

(ert-deftest m7b4-iter-mark-region/no-op-when-mark-inactive ()
  ;; The whole block is gated on mark-active.  When mark is not active,
  ;; calling iter-mark-region must NOT touch transient-mark-mode etc.
  (with-temp-buffer
    (let ((saved-tmm transient-mark-mode))
      (setq transient-mark-mode 'identity)
      (--command-loop-1-iter-mark-region)
      ;; The Emacs-22 rotation only fires when mark-active; since it's
      ;; nil here, transient-mark-mode is unchanged.
      (should (eq 'identity transient-mark-mode))
      (setq transient-mark-mode saved-tmm))))

(ert-deftest m7b4-iter-mark-region/rotates-transient-mark-only ()
  ;; When mark is active and transient-mark-mode is `only', rotate it
  ;; to `identity'.
  (with-temp-buffer
    (insert "hello world")
    (push-mark 1)
    (setq transient-mark-mode 'only)
    (--command-loop-1-iter-mark-region)
    (should (eq 'identity transient-mark-mode))
    (setq transient-mark-mode nil)))

(ert-deftest m7b4-iter-mark-region/rotates-transient-mark-identity ()
  ;; When mark is active and transient-mark-mode is `identity', clear it.
  (with-temp-buffer
    (insert "hello world")
    (push-mark 1)
    (setq transient-mark-mode 'identity)
    (--command-loop-1-iter-mark-region)
    (should (eq nil transient-mark-mode))))

;;;; M7c — finalize (point adjustment + kbd-macro chars install)

(ert-deftest m7c-finalize/exists ()
  (should (fboundp '--command-loop-1-finalize)))

(ert-deftest m7c-helpers/exist ()
  (should (fboundp '--selected-window-buffer-current-p))
  (should (fboundp '--last-point-position-ne-pt-p))
  (should (fboundp '--composition-break-at-point-p))
  (should (fboundp '--last-point-position-in-accessible-p))
  (should (fboundp '--pt-in-accessible-p))
  (should (fboundp '--composition-adjust-point-lpp-changes-p))
  (should (fboundp '--composition-adjust-point-pt-changes-p))
  (should (fboundp '--adjust-point-for-property-cl1))
  (should (fboundp '--set-windows-or-buffers-changed))
  (should (fboundp '--finalize-kbd-macro-chars)))

(ert-deftest m7c-helper/composition-break-at-point-defaults-nil ()
  ;; `composition-break-at-point' defaults nil.
  (should (eq nil (--composition-break-at-point-p))))

(ert-deftest m7c-helper/pt-in-accessible-p ()
  ;; In an empty buffer PT == BEGV == ZV, so PT is not strictly between.
  (with-temp-buffer
    (should (eq nil (--pt-in-accessible-p)))
    (insert "hello world")
    (goto-char 3)   ; somewhere in the middle of "hello"
    (should (eq t (--pt-in-accessible-p)))
    (goto-char 1)
    (should (eq nil (--pt-in-accessible-p)))
    (goto-char (point-max))
    (should (eq nil (--pt-in-accessible-p)))))

(ert-deftest m7c-helper/last-point-position-ne-pt-p ()
  ;; After `--save-state-for-redisplay-get-pt' the snapshot equals PT.
  (with-temp-buffer
    (insert "abc")
    (goto-char 2)
    (--save-state-for-redisplay-get-pt)  ; resets last_point_position to PT
    (should (eq nil (--last-point-position-ne-pt-p)))
    (goto-char 3)
    (should (eq t (--last-point-position-ne-pt-p)))))

(ert-deftest m7c-helper/selected-window-buffer-current-p ()
  ;; In batch the selected-window's buffer is *scratch*; sync via
  ;; with-current-buffer to confirm both sides agree.
  (with-current-buffer (window-buffer (selected-window))
    (should (eq t (--selected-window-buffer-current-p)))))

(ert-deftest m7c-helper/set-windows-or-buffers-changed-accepts-fixnum ()
  ;; No reader subr — just verify it does not error on the two values
  ;; the finalize block actually uses.
  (should (eq nil (--set-windows-or-buffers-changed 21)))
  (should (eq nil (--set-windows-or-buffers-changed 39)))
  (should (eq nil (--set-windows-or-buffers-changed 0))))

(ert-deftest m7c-finalize/no-op-when-pt-unchanged ()
  ;; Steady state: no point movement, not defining a kbd-macro.
  ;; --command-loop-1-finalize must run to completion without error.
  (with-current-buffer (window-buffer (selected-window))
    (--save-state-for-redisplay-get-pt)
    (let ((kb (current-kboard)))
      (set-kboard-defining-kbd-macro kb nil)
      (set-kboard-prefix-arg          kb nil)
      (--command-loop-1-finalize)
      (should t))))

;;;; M7d — command_loop_1 entry point in Scheme

(ert-deftest m7d-command-loop-1/exists ()
  ;; The full while-loop is now (emacs command-loop) command-loop-1.
  ;; Exposed to elisp as `--command-loop-1' for symmetry with siblings.
  (should (fboundp '--command-loop-1)))

;;;; M7e — command_loop_2 / top_level_1 outer drivers in Scheme

(ert-deftest m7e-command-loop-2/exists ()
  (should (fboundp '--command-loop-2)))

(ert-deftest m7e-top-level-1/exists ()
  (should (fboundp '--top-level-1)))

(ert-deftest m7e-helpers/exist ()
  ;; --cmd-error wraps the C cmd_error handler; --eval-top-level
  ;; bundles Feval (Vtop_level, Qt).
  (should (fboundp '--cmd-error))
  (should (fboundp '--eval-top-level)))

;;;; M7f — cmd-error in Scheme

(ert-deftest m7f-helpers/exist ()
  (should (fboundp '--executing-kbd-macro-c-p))
  (should (fboundp '--clear-executing-kbd-macro))
  (should (fboundp '--executing-kbd-macro-iterations))
  (should (fboundp '--display-hourglass-p))
  (should (fboundp '--cancel-hourglass))
  (should (fboundp '--cmd-error-internal)))

(ert-deftest m7f-helper/executing-kbd-macro-c-defaults-nil ()
  ;; At batch startup, no kbd-macro is replaying.
  (should (eq nil (--executing-kbd-macro-c-p))))

(ert-deftest m7f-helper/display-hourglass-returns-bool ()
  ;; --display-hourglass-p returns t or nil.  Actual value depends on
  ;; the build (window-system vs. TTY) — defvar default is t.
  (let ((v (--display-hourglass-p)))
    (should (or (eq v t) (eq v nil)))))

(ert-deftest m7f-helper/cancel-hourglass-no-op-in-batch ()
  ;; Must run cleanly even when there's no hourglass to cancel.
  (--cancel-hourglass)
  (should t))

(ert-deftest m7f-cmd-error/returns-fixnum-0 ()
  ;; cmd-error always returns 0 — the loop in command-loop-2 / top-level-1
  ;; treats 0 (non-nil) as "keep iterating".  Synthetic invocation.
  (let ((Vcommand_error_function-saved command-error-function))
    (unwind-protect
        (progn
          ;; Suppress side effects: empty error-function so we don't
          ;; spew "After 0 kbd macro iterations:" into test output.
          (setq command-error-function (lambda (data ctx sig) nil))
          (should (= 0 (--cmd-error (cons 'my-test-error (list "data"))))))
      (setq command-error-function Vcommand_error_function-saved))))

(provide 'ertest-command-loop)

;;; ertest-command-loop.el ends here
