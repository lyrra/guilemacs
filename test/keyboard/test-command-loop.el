;;; test-command-loop.el --- M7a SRFI-64 suite

;; Same coverage as ertest-command-loop.el, transcribed for the
;; test-framework.el / SRFI-64 harness.  Keep in sync.

(test-begin "command-loop")

;;;; Existence checks

(test-assert "prologue/exists"             (fboundp '--command-loop-1-prologue))
(test-assert "helpers/cancel-echoing"      (fboundp '--cancel-echoing))
(test-assert "helpers/safe-run-hooks"      (fboundp '--safe-run-hooks))
(test-assert "helpers/safe-run-hooks-maybe-narrowed"
             (fboundp '--safe-run-hooks-maybe-narrowed-selected))
(test-assert "helpers/resize-echo-area"    (fboundp '--resize-echo-area-exactly))
(test-assert "helpers/echo-area-non-empty" (fboundp '--echo-area-buffer-0-non-empty-p))
(test-assert "helpers/clear-waiting"       (fboundp '--clear-waiting-for-input))

;;;; State-reset behavior

(set--this-command-keys "abc")
(--command-loop-1-prologue)
(test-equal "prologue/clears-tck-count" 0 (--this-command-key-count))

(--set-this-command-key-count 5)
(--set-this-single-command-key-start 3)
(--command-loop-1-prologue)
(test-equal "prologue/clears-single-cmd-start" 0 (--this-single-command-key-start))

(let ((kb (current-kboard)))
  (set-kboard-prefix-arg      kb '(4))
  (set-kboard-last-prefix-arg kb '(16))
  (--command-loop-1-prologue)
  (test-eq "prologue/clears-prefix-arg"      nil (kboard-prefix-arg      kb))
  (test-eq "prologue/clears-last-prefix-arg" nil (kboard-last-prefix-arg kb)))

(setq deactivate-mark t)
(--command-loop-1-prologue)
(test-eq "prologue/clears-deactivate-mark" nil deactivate-mark)

;;;; last-command save

(let ((kb (current-kboard)))
  (setq this-command       'sentinel-cmd-a)
  (setq real-this-command  'sentinel-real-a)
  (--command-loop-1-prologue)
  (test-eq "prologue/saves-last-command"      'sentinel-cmd-a  (kboard-last-command      kb))
  (test-eq "prologue/saves-real-last-command" 'sentinel-real-a (kboard-real-last-command kb))
  (setq this-command nil real-this-command nil))

;;;; last-repeatable only when last-command-event not cons

(let ((kb (current-kboard)))
  (setq this-command 'sentinel-rep-b
        real-this-command 'sentinel-rep-b
        last-command-event ?a)
  (set-kboard-last-repeatable-command kb 'pre)
  (--command-loop-1-prologue)
  (test-eq "prologue/saves-repeatable-on-non-cons-event"
           'sentinel-rep-b (kboard-last-repeatable-command kb))

  (setq this-command 'sentinel-rep-c
        real-this-command 'sentinel-rep-c
        last-command-event '(mouse-1 0))
  (set-kboard-last-repeatable-command kb 'pre2)
  (--command-loop-1-prologue)
  (test-eq "prologue/skips-repeatable-on-cons-event"
           'pre2 (kboard-last-repeatable-command kb))

  (setq this-command nil real-this-command nil last-command-event nil)
  (set-kboard-last-repeatable-command kb nil))

;;;; memory-full short-circuits hooks

(let ((sentinel nil)
      (hook (lambda () (setq sentinel 'ran))))
  (add-hook 'post-command-hook hook)
  (setq memory-full t)
  (--command-loop-1-prologue)
  (test-eq "prologue/memory-full-skips-hooks" nil sentinel)
  (remove-hook 'post-command-hook hook)
  (setq memory-full nil))

;;;; M7b1

(test-assert "iter-pre-read/exists" (fboundp '--command-loop-1-iter-pre-read))

(test-assert "m7b1-helper/selected-frame-live-p" (fboundp '--selected-frame-live-p))
(test-assert "m7b1-helper/set-buffer-from-selected-window"
             (fboundp '--set-buffer-from-selected-window))
(test-assert "m7b1-helper/display-pending-malloc"
             (fboundp '--display-pending-malloc-warnings-loop))
(test-assert "m7b1-helper/clear-ignore-mouse-drag"
             (fboundp '--clear-ignore-mouse-drag))
(test-assert "m7b1-helper/minibuf-echo-aligned"
             (fboundp '--minibuf-and-echo-area-aligned-p))
(test-assert "m7b1-helper/resize-mini-window"
             (fboundp '--resize-mini-window-minibuf-non-shrink))
(test-assert "m7b1-helper/quit-char" (fboundp '--quit-char))
(test-assert "m7b1-helper/set-raw-keybuf-count"
             (fboundp '--set-raw-keybuf-count))
(test-assert "m7b1-helper/read-key-sequence" (fboundp '--read-key-sequence))
(test-assert "m7b1-helper/inc-num-input-keys" (fboundp '--inc-num-input-keys))

(test-eq "m7b1-helper/selected-frame-live-p-batch" t (--selected-frame-live-p))
(test-eq "m7b1-helper/minibuf-aligned-batch"     nil (--minibuf-and-echo-area-aligned-p))
(test-equal "m7b1-helper/quit-char-default"        7 (--quit-char))

(setq this-command 'X real-this-command 'Y this-original-command 'Z
      this-command-keys-shift-translated t
      unread-command-events (list ?a))
(let ((outcome (--command-loop-1-iter-pre-read)))
  (test-equal "iter-pre-read/ok-outcome" 0 outcome))
(test-eq "iter-pre-read/clears-this-original-command" nil this-original-command)
(test-eq "iter-pre-read/clears-shift-translated"      nil this-command-keys-shift-translated)
(test-eq "iter-pre-read/clears-deactivate-mark"       nil deactivate-mark)
(setq this-command nil real-this-command nil
      this-original-command nil
      this-command-keys-shift-translated nil
      unread-command-events nil)

(setq unread-command-events (list ?x))
(--command-loop-1-iter-pre-read)
(test-equal "iter-pre-read/sets-last-command-event" ?x last-command-event)
(setq unread-command-events nil last-command-event nil)

;; EOF branch (i==0) is not directly testable in batch — see ERT suite
;; for the reason.  Real EOF is reached only via kbd-macro replay.

;;;; M7b2

(test-assert "iter-dispatch/exists"  (fboundp '--command-loop-1-iter-dispatch))

(test-assert "m7b2-helper/clear-force-start"
             (fboundp '--clear-force-start-and-flush-buffer-unchanged))
(test-assert "m7b2-helper/read-key-sequence-cmd"
             (fboundp '--read-key-sequence-cmd))
(test-assert "m7b2-helper/read-key-sequence-remapped"
             (fboundp '--read-key-sequence-remapped))
(test-assert "m7b2-helper/maybe-quit" (fboundp '--maybe-quit))
(test-assert "m7b2-helper/save-state-for-redisplay"
             (fboundp '--save-state-for-redisplay-get-pt))
(test-assert "m7b2-helper/restore-last-point-position"
             (fboundp '--restore-last-point-position))
(test-assert "m7b2-helper/record-recent-keys-cmd"
             (fboundp '--record-recent-keys-cmd-pseudo-event))
(test-assert "m7b2-helper/with-hourglass" (fboundp '--with-hourglass-protection))
(test-assert "m7b2-helper/save-point-before-last-command"
             (fboundp '--save-point-before-last-command-or-undo))
(test-assert "m7b2-helper/reset-redisplay-tick-state"
             (fboundp '--reset-redisplay-tick-state))
(test-assert "m7b2-helper/clear-display-working-on-window-p"
             (fboundp '--clear-display-working-on-window-p))

(with-temp-buffer
  (insert "abc")
  (goto-char 2)
  (test-equal "save-state/returns-pt" 2 (--save-state-for-redisplay-get-pt)))

(let ((sentinel 'unset))
  (--with-hourglass-protection (lambda () (setq sentinel 'ran)))
  (test-eq "with-hourglass-protection/runs-thunk" 'ran sentinel))

(clear-this-command-keys)
(--record-recent-keys-cmd-pseudo-event 'srfi-sentinel-cmd)
(let ((rk (recent-keys t))
      (found nil))
  (dotimes (i (length rk))
    (let ((e (aref rk i)))
      (when (and (consp e) (eq (cdr e) 'srfi-sentinel-cmd))
        (setq found t))))
  (test-assert "record-recent-keys-cmd-pushes-pseudo-event" found))
(clear-this-command-keys)

;;;; M7b3

(test-assert "iter-post-dispatch/exists" (fboundp '--command-loop-1-iter-post-dispatch))

(test-assert "m7b3-helper/echo-area-window-eq-minibuf"
             (fboundp '--echo-area-window-eq-selected-frame-minibuf-p))
(test-assert "m7b3-helper/current-kboard-immediate-echo-p"
             (fboundp '--current-kboard-immediate-echo-p))
(test-assert "m7b3-helper/clear-current-kboard-immediate-echo"
             (fboundp '--clear-current-kboard-immediate-echo))
(test-assert "m7b3-helper/echo-now" (fboundp '--echo-now))

(test-eq "m7b3/immediate-echo-defaults-nil" nil (--current-kboard-immediate-echo-p))

(let ((kb (current-kboard)))
  (set-kboard-last-prefix-arg kb nil)
  (setq current-prefix-arg '(16))
  (--command-loop-1-iter-post-dispatch)
  (test-equal "m7b3/saves-last-prefix-arg" '(16) (kboard-last-prefix-arg kb))
  (set-kboard-last-prefix-arg kb nil)
  (setq current-prefix-arg nil))

(let ((kb (current-kboard)))
  (setq this-command 'srfi-m7b3-tc real-this-command 'srfi-m7b3-rtc
        last-command-event ?z)
  (--command-loop-1-iter-post-dispatch)
  (test-eq "m7b3/saves-last-command"           'srfi-m7b3-tc  (kboard-last-command           kb))
  (test-eq "m7b3/saves-real-last-command"      'srfi-m7b3-rtc (kboard-real-last-command      kb))
  (test-eq "m7b3/saves-last-repeatable-command" 'srfi-m7b3-rtc (kboard-last-repeatable-command kb))
  (setq this-command nil real-this-command nil last-command-event nil)
  (set-kboard-last-command kb nil)
  (set-kboard-real-last-command kb nil)
  (set-kboard-last-repeatable-command kb nil))

(set--this-command-keys "abcde")
(--command-loop-1-iter-post-dispatch)
(test-equal "m7b3/zeros-this-command-key-count" 0 (--this-command-key-count))
(test-equal "m7b3/zeros-single-key-start"       0 (--this-single-command-key-start))

;;;; M7b4

(test-assert "iter-mark-region/exists" (fboundp '--command-loop-1-iter-mark-region))

(test-assert "m7b4-helper/mark-active-p"     (fboundp '--current-buffer-mark-active-p))
(test-assert "m7b4-helper/mark-has-buffer-p" (fboundp '--current-buffer-mark-has-buffer-p))
(test-assert "m7b4-helper/cl1-prev-buffer-current-p"
             (fboundp '--cl1-prev-buffer-current-p))
(test-assert "m7b4-helper/cl1-prev-modiff-current-p"
             (fboundp '--cl1-prev-modiff-current-p))

(with-temp-buffer
  (test-eq "m7b4/mark-active-default-nil" nil (--current-buffer-mark-active-p)))

(with-temp-buffer
  (let ((saved transient-mark-mode))
    (setq transient-mark-mode 'identity)
    (--command-loop-1-iter-mark-region)
    (test-eq "m7b4/no-op-when-mark-inactive" 'identity transient-mark-mode)
    (setq transient-mark-mode saved)))

(with-temp-buffer
  (insert "hello world")
  (push-mark 1)
  (setq transient-mark-mode 'only)
  (--command-loop-1-iter-mark-region)
  (test-eq "m7b4/rotates-only-to-identity" 'identity transient-mark-mode)
  (setq transient-mark-mode nil))

(with-temp-buffer
  (insert "hello world")
  (push-mark 1)
  (setq transient-mark-mode 'identity)
  (--command-loop-1-iter-mark-region)
  (test-eq "m7b4/rotates-identity-to-nil" nil transient-mark-mode))

(test-end)
