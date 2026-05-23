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

;;;; M6m

(test-assert "m6m-helper/rks-replay-sequence-init-rest"
             (fboundp '--rks-replay-sequence-init-rest))
(test-assert "m6m/runtime-variant-exists"
             (fboundp '--rks-setup-replay-sequence-c!))

(test-eq "m6m/init-rest-returns-nil"
         nil (--rks-replay-sequence-init-rest nil))

(--rks-setup-replay-sequence-c! nil nil)
(test-assert "m6m/runtime-variant-runs" t)

;;;; M6n

(test-assert "m6n-helper/set-read-key-sequence-remapped"
             (fboundp '--set-read-key-sequence-remapped))
(test-assert "m6n/compute-remapped-exists"
             (fboundp '--rks-done-compute-remapped!))

(test-eq "m6n/set-remapped-returns-nil"
         nil (--set-read-key-sequence-remapped nil))

(--rks-done-compute-remapped!)
(test-assert "m6n/compute-remapped-runs" t)

;;;; M6o

(test-assert "m6o-helper/shift-translated-p"
             (fboundp '--rks-shift-translated-p))
(test-assert "m6o/install-exists"
             (fboundp '--rks-done-install-shift-translated!))

(let ((v (--rks-shift-translated-p)))
  (test-assert "m6o/shift-translated-p-boolean"
               (or (eq v t) (eq v nil))))

(--rks-done-install-shift-translated!)
(test-assert "m6o/install-runs" t)

;;;; M6p

(test-assert "m6p-helper/rks-delayed-switch-frame"
             (fboundp '--rks-delayed-switch-frame))
(test-assert "m6p-helper/set-unread-switch-frame"
             (fboundp '--set-unread-switch-frame))
(test-assert "m6p/install-exists"
             (fboundp '--rks-done-install-unread-switch-frame!))

(test-eq "m6p/set-unread-returns-nil" nil (--set-unread-switch-frame nil))
(--rks-done-install-unread-switch-frame!)
(test-assert "m6p/install-runs" t)
(let ((v (--rks-delayed-switch-frame)))
  (test-assert "m6p/getter-returns-lisp-value"
               (or (eq v nil) v)))

;;;; M6q

(test-assert "m6q-helper/keybuf-depth"      (fboundp '--rks-keybuf-depth))
(test-assert "m6q-helper/keybuf-ref"        (fboundp '--rks-keybuf-ref))
(test-assert "m6q-helper/keybuf-set"        (fboundp '--rks-keybuf-set))

(test-equal "m6q/depth-zero-at-idle" 0 (--rks-keybuf-depth))
(test-eq    "m6q/ref-nil-when-empty"  nil (--rks-keybuf-ref 0))
(test-eq    "m6q/set-no-op-when-empty" nil (--rks-keybuf-set 0 'x))
(test-eq    "m6q/ref-out-of-range" nil (--rks-keybuf-ref 100))

;;;; M6r

(test-assert "m6r-helper/original-uppercase"
             (fboundp '--rks-original-uppercase))
(test-assert "m6r-helper/original-uppercase-position"
             (fboundp '--rks-original-uppercase-position))
(test-assert "m6r-helper/rks-t"             (fboundp '--rks-t))
(test-assert "m6r-helper/rks-current-binding"
             (fboundp '--rks-current-binding))
(test-assert "m6r-helper/set-rks-shift-translated"
             (fboundp '--set-rks-shift-translated))
(test-assert "m6r/downcase-undo-exists"
             (fboundp '--rks-done-downcase-undo!))

(test-assert "m6r/original-uppercase-position-integer"
             (integerp (--rks-original-uppercase-position)))

(--rks-done-downcase-undo! nil)
(--rks-done-downcase-undo! t)
(test-assert "m6r/downcase-undo-runs" t)

;;;; M6s

(test-assert "m6s-helper/rks-mock-input"   (fboundp '--rks-mock-input))
(test-assert "m6s-helper/set-rks-t"        (fboundp '--set-rks-t))
(test-assert "m6s-helper/echo-update"      (fboundp '--echo-update))
(test-assert "m6s/fabricated-events-exists"
             (fboundp '--rks-done-fabricated-events!))

(test-assert "m6s/rks-mock-input-integer" (integerp (--rks-mock-input)))

(let ((saved (--rks-t)))
  (--set-rks-t 0)
  (test-equal "m6s/set-rks-t-roundtrip" 0 (--rks-t))
  (--set-rks-t saved))

(--rks-done-fabricated-events!)
(test-assert "m6s/fabricated-events-runs" t)

;;;; M6t

(test-assert "m6t-helper/fkey-start"      (fboundp '--rks-fkey-start))
(test-assert "m6t-helper/keytran-start"   (fboundp '--rks-keytran-start))
(test-assert "m6t-helper/indec-start"     (fboundp '--rks-indec-start))
(test-assert "m6t-helper/first-unbound"   (fboundp '--rks-first-unbound))
(test-assert "m6t-helper/set-mock-input"  (fboundp '--set-rks-mock-input))
(test-assert "m6t-helper/keybuf-shift-down"
             (fboundp '--rks-keybuf-shift-down))
(test-assert "m6t-helper/keyremaps-shrink-by"
             (fboundp '--rks-keyremaps-shrink-by))
(test-assert "m6t/short-circuit-exists"
             (fboundp '--rks-first-unbound-short-circuit!))

(test-eq "m6t/short-circuit-idle-nil"
         nil (--rks-first-unbound-short-circuit!))
(test-eq "m6t/keyremaps-shrink-returns-nil"
         nil (--rks-keyremaps-shrink-by 0))

;;;; M6u

(test-assert "m6u-helper/try-shift-translation-simple"
             (fboundp '--rks-try-shift-translation-simple))

(test-eq "m6u/lowercase-falls-through"
         nil (--rks-try-shift-translation-simple! 97))
(test-eq "m6u/non-fixnum-falls-through"
         nil (--rks-try-shift-translation-simple! 'up))

;;;; M6v

(test-assert "m6v-helper/try-help-char"
             (fboundp '--rks-try-help-char))
(test-eq "m6v/help-char-nil-at-idle"
         nil (--rks-try-help-char! 8))
(test-eq "m6v/help-char-nil-for-symbol"
         nil (--rks-try-help-char! 'foo))

;;;; M6w

(test-assert "m6w-helper/try-shift-translation-fn-key"
             (fboundp '--rks-try-shift-translation-fn-key))
(test-eq "m6w/fn-key-nil-for-symbol"
         nil (--rks-try-shift-translation-fn-key! 'up))
(test-eq "m6w/fn-key-nil-for-lowercase"
         nil (--rks-try-shift-translation-fn-key! ?a))

;;;; M6x

(test-assert "m6x-helper/walk-translation-maps"
             (fboundp '--rks-walk-translation-maps))
(test-eq "m6x/walk-nil-at-idle"
         nil (--rks-walk-translation-maps! nil))
(test-eq "m6x/walk-nil-with-prompt"
         nil (--rks-walk-translation-maps! "P> "))

;;;; M6y

(test-assert "m6y-helper/iter-setup-capture"
             (fboundp '--rks-iter-setup-capture))
(test-assert "m6y-helper/iter-replay-restore"
             (fboundp '--rks-iter-replay-restore))
(test-assert "m6y-helper/echo-local-start"
             (fboundp '--rks-echo-local-start))
(test-assert "m6y-helper/keys-local-start"
             (fboundp '--rks-keys-local-start))

(let ((saved-e (--rks-echo-local-start))
      (saved-k (--rks-keys-local-start)))
  (--rks-set-echo-local-start 42)
  (--rks-set-keys-local-start 7)
  (test-equal "m6y/echo-local-start-roundtrip" 42 (--rks-echo-local-start))
  (test-equal "m6y/keys-local-start-roundtrip" 7  (--rks-keys-local-start))
  (--rks-set-echo-local-start saved-e)
  (--rks-set-keys-local-start saved-k))

(--rks-iter-setup-capture!)
(test-assert "m6y/setup-capture-runs" t)
(--rks-iter-replay-restore!)
(test-assert "m6y/replay-restore-runs" t)

;;;; M6z

(test-assert "m6z-helper/rks-key"      (fboundp '--rks-key))
(test-assert "m6z-helper/used-mouse-menu-p"
             (fboundp '--rks-used-mouse-menu-p))
(test-assert "m6z-helper/cascade"
             (fboundp '--rks-iter-pre-read-cascade))

(test-eq "m6z/cascade-read-char-at-idle"
         'read-char (--rks-iter-pre-read-cascade!))
(let ((v (--rks-used-mouse-menu-p)))
  (test-assert "m6z/used-mouse-menu-boolean"
               (or (eq v t) (eq v nil))))

(test-end)
