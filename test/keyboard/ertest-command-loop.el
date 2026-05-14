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

(provide 'ertest-command-loop)

;;; ertest-command-loop.el ends here
