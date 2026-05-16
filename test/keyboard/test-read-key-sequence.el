;;; test-read-key-sequence.el --- M6a SRFI-64 suite

;; Same coverage as ertest-read-key-sequence.el, transcribed for the
;; test-framework.el / SRFI-64 harness.  Keep in sync.

(test-begin "read-key-sequence")

;;;; Existence checks

(test-assert "wrapper/exists"     (fboundp '--read-key-sequence-vs))
(test-assert "elisp/read-key-sequence-fboundp"
             (fboundp 'read-key-sequence))
(test-assert "elisp/read-key-sequence-vector-fboundp"
             (fboundp 'read-key-sequence-vector))
(test-assert "helper/read-key-sequence-and-vector"
             (fboundp '--read-key-sequence-and-vector))
(test-assert "helper/make-event-array-from-vector"
             (fboundp '--make-event-array-from-vector))

;;;; Wrapper behavior — mocked --read-key-sequence-and-vector

(advice-add '--read-key-sequence-and-vector :around
            (lambda (orig &rest args) [?a ?b ?c]))

(let ((result (--read-key-sequence-vs nil t nil nil nil t nil)))
  (test-assert "wrapper/allow-string-stringp" (stringp result))
  (test-equal  "wrapper/allow-string-value"   "abc" result))

(let ((result (--read-key-sequence-vs nil t nil nil nil nil nil)))
  (test-assert "wrapper/disallow-string-vectorp" (vectorp result))
  (test-equal  "wrapper/disallow-string-length" 3 (length result)))

(advice-remove '--read-key-sequence-and-vector
               (lambda (orig &rest args) [?a ?b ?c]))

;;;; Counter reset behavior

(let (observed)
  (advice-add '--read-key-sequence-and-vector :around
              (lambda (orig &rest args)
                (setq observed (cons (--this-command-key-count)
                                     (--this-single-command-key-start)))
                []))
  (--set-this-command-key-count        5)
  (--set-this-single-command-key-start 3)
  (--read-key-sequence-vs nil nil nil nil nil nil nil)
  (test-equal "wrapper/continue-echo-nil-resets-count" 0 (car observed))
  (test-equal "wrapper/continue-echo-nil-resets-start" 0 (cdr observed))
  (advice-remove '--read-key-sequence-and-vector
                 (lambda (orig &rest args)
                   (setq observed (cons (--this-command-key-count)
                                        (--this-single-command-key-start)))
                   [])))

;;;; M6b

(test-assert "m6b/discard-input-exists" (fboundp 'discard-input))
(test-assert "m6b/dispatch-shim-exists" (fboundp '--discard-input))
(test-assert "m6b-helper/end-kbd-macro" (fboundp '--end-kbd-macro))
(test-assert "m6b-helper/discard-tty-input" (fboundp '--discard-tty-input))
(test-assert "m6b-helper/reset-kbd-ring-and-pending"
             (fboundp '--reset-kbd-ring-and-pending))

(let ((saved unread-command-events))
  (setq unread-command-events '(?a ?b ?c))
  (discard-input)
  (test-eq "m6b/clears-unread-command-events" nil unread-command-events)
  (setq unread-command-events saved))

(test-eq "m6b/returns-nil" nil (discard-input))

;;;; M6c

(test-assert "m6c/current-input-mode-exists" (fboundp 'current-input-mode))
(test-assert "m6c/set-input-mode-exists"     (fboundp 'set-input-mode))
(test-assert "m6c-helper/interrupt-input-p"  (fboundp '--interrupt-input-p))
(test-assert "m6c-helper/selected-frame-tty-p"
             (fboundp '--selected-frame-tty-p))
(test-assert "m6c-helper/selected-frame-tty-flow-control-p"
             (fboundp '--selected-frame-tty-flow-control-p))
(test-assert "m6c-helper/selected-frame-tty-meta-key"
             (fboundp '--selected-frame-tty-meta-key))

(let ((m (current-input-mode)))
  (test-assert "m6c/current-input-mode-is-list" (listp m))
  (test-equal  "m6c/current-input-mode-length"  4 (length m))
  (test-assert "m6c/quit-is-integer" (integerp (nth 3 m))))

;;;; M6d

(test-assert "m6d/posn-at-point-exists" (fboundp 'posn-at-point))

(let ((r (with-current-buffer (window-buffer (selected-window))
           (posn-at-point))))
  (test-assert "m6d/posn-at-point-runs" (or (eq r nil) (consp r))))

;;;; M6e

(test-assert "m6e/input-pending-p-exists" (fboundp 'input-pending-p))
(test-assert "m6e-helper/requeued-events-pending-p"
             (fboundp '--requeued-events-pending-p))
(test-assert "m6e-helper/process-special-events"
             (fboundp '--process-special-events))
(test-assert "m6e-helper/get-input-pending"
             (fboundp '--get-input-pending))

(let ((r (input-pending-p)))
  (test-assert "m6e/input-pending-p-boolean"
               (or (eq r t) (eq r nil))))

;;;; M6f

(test-assert "m6f/active-maps-exists" (fboundp '--active-maps))

(let ((m (--active-maps ?a nil)))
  (test-assert "m6f/active-maps-consp" (consp m))
  (test-eq    "m6f/active-maps-car-keymap" 'keymap (car m)))

;;;; M6g — state-machine record types

(test-assert "m6g/make-keyremap-exists"   (fboundp '--make-keyremap))
(test-assert "m6g/keyremap-empty-p-exists" (fboundp '--keyremap-empty-p))
(test-assert "m6g/keyremap-reset!-exists"  (fboundp '--keyremap-reset!))
(test-assert "m6g/keyremap-rebase!-exists" (fboundp '--keyremap-rebase!))
(test-assert "m6g/make-rks-state-exists"   (fboundp '--make-rks-state))

(let ((kr (--make-keyremap nil)))
  (test-eq "m6g/fresh-keyremap-empty" t (--keyremap-empty-p kr)))

(let ((kr (--make-keyremap 0)))
  (--keyremap-rebase! kr 99)
  (test-eq "m6g/keyremap-rebase-preserves-empty" t (--keyremap-empty-p kr)))

(let ((kr (--make-keyremap 0)))
  (--keyremap-reset! kr)
  (test-eq "m6g/keyremap-reset-preserves-empty" t (--keyremap-empty-p kr)))

(let ((s (--make-rks-state)))
  (test-assert "m6g/make-rks-state-nonnil" (not (null s))))

;;;; M6h

(test-assert "m6h-helper/echo-length"     (fboundp '--echo-length))
(test-assert "m6h-helper/echo-truncate"   (fboundp '--echo-truncate))
(test-assert "m6h-helper/echo-dash"       (fboundp '--echo-dash))
(test-assert "m6h-helper/echo-keystrokes-p" (fboundp '--echo-keystrokes-p))
(test-assert "m6h-helper/cursor-in-echo-area-p"
             (fboundp '--cursor-in-echo-area-p))
(test-assert "m6h-helper/set-current-kboard-immediate-echo"
             (fboundp '--set-current-kboard-immediate-echo))

(let ((n (--echo-length)))
  (test-assert "m6h/echo-length-fixnum" (and (integerp n) (>= n 0))))

(test-assert "m6h/setup-prompt-exists"
             (fboundp '--rks-setup-prompt!))
(--rks-setup-prompt! nil)
(test-assert "m6h/setup-prompt-nil-runs" t)

(test-assert "m6h/setup-initial-keys-exists"
             (fboundp '--rks-setup-initial-keys-state!))

(--set-this-command-key-count        4)
(--set-this-single-command-key-start 2)
(let ((s (--make-rks-state)))
  (--rks-setup-initial-keys-state! s)
  (test-equal "m6h/setup-copies-key-count" 4 (--this-single-command-key-start)))

;;;; M6j

(test-assert "m6j-helper/set-rks-echo-start"   (fboundp '--set-rks-echo-start))
(test-assert "m6j-helper/set-rks-keys-start"   (fboundp '--set-rks-keys-start))
(test-assert "m6j/setup-initial-state-c-exists"
             (fboundp '--rks-setup-initial-state-c!))

(--set-this-command-key-count        6)
(--set-this-single-command-key-start 0)
(--rks-setup-initial-state-c!)
(test-equal "m6j/setup-sets-single-cmd-key-start"
            6 (--this-single-command-key-start))

(test-eq "m6j/set-rks-echo-start-returns-nil"  nil (--set-rks-echo-start 42))
(test-eq "m6j/set-rks-keys-start-returns-nil"  nil (--set-rks-keys-start 7))

;;;; M6k

(test-assert "m6k/replay-entire-sequence-exists"
             (fboundp '--rks-setup-replay-entire-sequence!))
(test-assert "m6k/replay-sequence-exists"
             (fboundp '--rks-setup-replay-sequence!))

(let ((s (--make-rks-state)))
  (--rks-setup-replay-entire-sequence! s)
  (test-assert "m6k/replay-entire-sequence-runs" t))

(let ((s (--make-rks-state)))
  (--rks-setup-replay-sequence! s)
  (test-assert "m6k/replay-sequence-runs" t))

;;;; M6l

(test-assert "m6l-helper/rks-init-keyremaps"
             (fboundp '--rks-init-keyremaps))
(test-assert "m6l/runtime-variant-exists"
             (fboundp '--rks-setup-replay-entire-sequence-c!))

(test-eq "m6l/init-keyremaps-returns-nil"
         nil (--rks-init-keyremaps nil nil nil))

(--rks-setup-replay-entire-sequence-c!)
(test-assert "m6l/runtime-variant-runs" t)

(test-end)
