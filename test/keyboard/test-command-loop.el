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

(test-end)
