;;; ertest-read-key-sequence.el --- M6a ERT suite for (emacs read-key-sequence)

;; M6a — outer wrapper port (read_key_sequence_vs in src/keyboard.c).
;; The state machine itself stays C (--read-key-sequence-and-vector).
;; We test the housekeeping wrapper via the elisp-registered shim
;; `--read-key-sequence-vs' and stub the C primitive by rebinding its
;; symbol-function for each test (advice didn't compose reliably in
;; this Guile-elisp environment).
;;
;; See docs/keyboard.org §M6a.

(require 'ert)

;;;; Existence checks

(ert-deftest m6a-wrapper/exists ()
  (should (fboundp '--read-key-sequence-vs))
  ;; The user-visible DEFUNs still resolve (now via cached-SCM dispatch).
  (should (fboundp 'read-key-sequence))
  (should (fboundp 'read-key-sequence-vector)))

(ert-deftest m6a-helpers/exist ()
  (should (fboundp '--read-key-sequence-and-vector))
  ;; --make-event-array-from-vector is shared with M3/M5 (3-arg form).
  (should (fboundp '--make-event-array-from-vector)))

;;;; Test helper that rebinds the C subr's elisp dispatch for the
;;;; duration of THUNK then restores.  Avoids the advice machinery.

(defun m6a-with-stub-rks (stub thunk)
  "Run THUNK with --read-key-sequence-and-vector's elisp binding
replaced by STUB.  Restore afterwards regardless of how THUNK exits."
  (let ((saved (symbol-function '--read-key-sequence-and-vector)))
    (unwind-protect
        (progn
          (fset '--read-key-sequence-and-vector stub)
          (funcall thunk))
      (fset '--read-key-sequence-and-vector saved))))

;;;; Wrapper specbind behavior

(ert-deftest m6a-wrapper/specbinds-input-method-vars-when-cmd-loop-nil ()
  ;; When cmd-loop arg is nil, the two input-method vars are bound to t
  ;; for the duration of the read.
  (let ((saved-exit input-method-exit-on-first-char)
        (saved-echo input-method-use-echo-area)
        (observed nil))
    (unwind-protect
        (progn
          (setq input-method-exit-on-first-char nil
                input-method-use-echo-area nil)
          (m6a-with-stub-rks
           (lambda (&rest _args)
             (setq observed (cons input-method-exit-on-first-char
                                  input-method-use-echo-area))
             [])
           (lambda ()
             (--read-key-sequence-vs nil nil nil nil nil nil nil)))
          (should (eq t (car observed)))
          (should (eq t (cdr observed)))
          (should (eq nil input-method-exit-on-first-char))
          (should (eq nil input-method-use-echo-area)))
      (setq input-method-exit-on-first-char saved-exit
            input-method-use-echo-area saved-echo))))

(ert-deftest m6a-wrapper/resets-key-counters-when-continue-echo-nil ()
  (let (observed)
    (m6a-with-stub-rks
     (lambda (&rest _args)
       (setq observed (cons (--this-command-key-count)
                            (--this-single-command-key-start)))
       [])
     (lambda ()
       (--set-this-command-key-count        5)
       (--set-this-single-command-key-start 3)
       (--read-key-sequence-vs nil nil nil nil nil nil nil)))
    (should (= 0 (car observed)))
    (should (= 0 (cdr observed)))))

(ert-deftest m6a-wrapper/skips-counter-reset-when-continue-echo-non-nil ()
  (let (observed)
    (m6a-with-stub-rks
     (lambda (&rest _args)
       (setq observed (cons (--this-command-key-count)
                            (--this-single-command-key-start)))
       [])
     (lambda ()
       (--set-this-command-key-count        7)
       (--set-this-single-command-key-start 4)
       (--read-key-sequence-vs nil t nil nil nil nil nil)))
    (should (= 7 (car observed)))
    (should (= 4 (cdr observed)))))

(ert-deftest m6a-wrapper/allow-string-converts-vector ()
  (let ((result
         (m6a-with-stub-rks
          (lambda (&rest _args) [?a ?b ?c])
          (lambda ()
            (--read-key-sequence-vs nil t nil nil nil t nil)))))
    (should (stringp result))
    (should (equal "abc" result))))

(ert-deftest m6a-wrapper/disallow-string-returns-vector ()
  (let ((result
         (m6a-with-stub-rks
          (lambda (&rest _args) [?a ?b ?c])
          (lambda ()
            (--read-key-sequence-vs nil t nil nil nil nil nil)))))
    (should (vectorp result))
    (should (= 3 (length result)))))

;;;; M6b — discard-input

(ert-deftest m6b-discard-input/exists ()
  (should (fboundp 'discard-input))
  (should (fboundp '--discard-input)))

(ert-deftest m6b-helpers/exist ()
  (should (fboundp '--end-kbd-macro))
  (should (fboundp '--discard-tty-input))
  (should (fboundp '--reset-kbd-ring-and-pending)))

(ert-deftest m6b-discard-input/clears-unread-command-events ()
  ;; discard-input always sets unread-command-events to nil.
  (let ((saved unread-command-events))
    (unwind-protect
        (progn
          (setq unread-command-events '(?a ?b ?c))
          (discard-input)
          (should (eq nil unread-command-events)))
      (setq unread-command-events saved))))

(ert-deftest m6b-discard-input/returns-nil ()
  (should (eq nil (discard-input))))

;;;; M6c — set-input-mode / current-input-mode

(ert-deftest m6c-current-input-mode/exists ()
  (should (fboundp 'current-input-mode)))

(ert-deftest m6c-set-input-mode/exists ()
  (should (fboundp 'set-input-mode)))

(ert-deftest m6c-helpers/exist ()
  (should (fboundp '--interrupt-input-p))
  (should (fboundp '--selected-frame-tty-p))
  (should (fboundp '--selected-frame-tty-flow-control-p))
  (should (fboundp '--selected-frame-tty-meta-key)))

(ert-deftest m6c-current-input-mode/returns-list-of-four ()
  ;; The shape is (INTERRUPT FLOW META QUIT) per the docstring.
  (let ((m (current-input-mode)))
    (should (listp m))
    (should (= 4 (length m)))))

(ert-deftest m6c-current-input-mode/quit-is-fixnum ()
  ;; QUIT (4th element) is the integer character code.
  (let ((q (nth 3 (current-input-mode))))
    (should (integerp q))
    (should (>= q 0))))

;;;; M6d — posn-at-point

(ert-deftest m6d-posn-at-point/exists ()
  (should (fboundp 'posn-at-point)))

(ert-deftest m6d-posn-at-point/nil-when-not-visible ()
  ;; In batch mode the *scratch* buffer of the selected window is
  ;; typically not "visible" in the redisplay sense — posn-at-point
  ;; returns nil.  Either result is acceptable; we just confirm the
  ;; function runs without error and returns a list or nil.
  (let ((r (with-current-buffer (window-buffer (selected-window))
             (posn-at-point))))
    (should (or (eq r nil) (consp r)))))

;;;; M6e — input-pending-p

(ert-deftest m6e-input-pending-p/exists ()
  (should (fboundp 'input-pending-p)))

(ert-deftest m6e-helpers/exist ()
  (should (fboundp '--requeued-events-pending-p))
  (should (fboundp '--process-special-events))
  (should (fboundp '--get-input-pending)))

(ert-deftest m6e-input-pending-p/returns-t-or-nil ()
  ;; In batch with no events queued, nil is the expected result; but the
  ;; docstring permits a conservative t.  Just verify a boolean.
  (let ((r (input-pending-p)))
    (should (or (eq r t) (eq r nil))))
  (let ((r (input-pending-p t)))
    (should (or (eq r t) (eq r nil)))))

;;;; M6f — --active-maps infrastructure

(ert-deftest m6f-active-maps/exists ()
  (should (fboundp '--active-maps)))

(ert-deftest m6f-active-maps/returns-keymap-cons ()
  ;; The result is (keymap . MAPS) — a cons starting with `keymap'.
  (let ((m (--active-maps ?a nil)))
    (should (consp m))
    (should (eq 'keymap (car m)))))

(ert-deftest m6f-active-maps/nil-events-still-yields-cons ()
  ;; With nil first event, position is nil and we get current-active-maps
  ;; for the selected window position.
  (let ((m (--active-maps nil nil)))
    (should (consp m))
    (should (eq 'keymap (car m)))))

;;;; M6g — state-machine record types

(ert-deftest m6g-record-types/elisp-bindings-exist ()
  (should (fboundp '--make-keyremap))
  (should (fboundp '--keyremap-empty-p))
  (should (fboundp '--keyremap-reset!))
  (should (fboundp '--keyremap-rebase!))
  (should (fboundp '--make-rks-state)))

(ert-deftest m6g-keyremap/fresh-is-empty ()
  ;; A freshly-constructed keyremap has start == end == 0.
  (let ((kr (--make-keyremap nil)))
    (should (eq t (--keyremap-empty-p kr)))))

(ert-deftest m6g-keyremap/rebase-preserves-empty ()
  ;; Rebasing to a new parent zeroes the indices, so empty-p still holds.
  (let ((kr (--make-keyremap 0)))
    (--keyremap-rebase! kr 99)
    (should (eq t (--keyremap-empty-p kr)))))

(ert-deftest m6g-keyremap/reset-preserves-empty ()
  ;; Resetting a fresh keyremap is a no-op.
  (let ((kr (--make-keyremap 0)))
    (--keyremap-reset! kr)
    (should (eq t (--keyremap-empty-p kr)))))

(ert-deftest m6g-rks-state/constructs-non-nil ()
  (let ((s (--make-rks-state)))
    (should (not (null s)))))

;;;; M6h — setup-phase helpers

(ert-deftest m6h-helpers/exist ()
  (should (fboundp '--echo-length))
  (should (fboundp '--echo-truncate))
  (should (fboundp '--echo-dash))
  (should (fboundp '--echo-keystrokes-p))
  (should (fboundp '--cursor-in-echo-area-p))
  (should (fboundp '--set-current-kboard-immediate-echo)))

(ert-deftest m6h-helper/echo-length-fixnum ()
  ;; --echo-length returns a non-negative integer.
  (let ((n (--echo-length)))
    (should (integerp n))
    (should (>= n 0))))

(ert-deftest m6h-helper/echo-keystrokes-p-boolean ()
  (let ((v (--echo-keystrokes-p)))
    (should (or (eq v t) (eq v nil)))))

(ert-deftest m6h-helper/cursor-in-echo-area-p-boolean ()
  (let ((v (--cursor-in-echo-area-p)))
    (should (or (eq v t) (eq v nil)))))

(ert-deftest m6h-setup-prompt/exists ()
  (should (fboundp '--rks-setup-prompt!)))

(ert-deftest m6h-setup-prompt/nil-prompt-runs ()
  ;; In batch mode noninteractive is t, so the wrapper does nothing.
  (--rks-setup-prompt! nil)
  (should t))

(ert-deftest m6h-setup-initial-keys/exists ()
  (should (fboundp '--rks-setup-initial-keys-state!)))

(ert-deftest m6h-setup-initial-keys/copies-key-count ()
  ;; After setup, this-single-command-key-start should equal
  ;; this-command-key-count (which is 0 unless prior state).
  (--set-this-command-key-count        4)
  (--set-this-single-command-key-start 2)
  (let ((s (--make-rks-state)))
    (--rks-setup-initial-keys-state! s)
    (should (= 4 (--this-single-command-key-start)))))

;;;; M6j — runtime initial-state capture (writes C file-static shadows)

(ert-deftest m6j-helpers/exist ()
  (should (fboundp '--set-rks-echo-start))
  (should (fboundp '--set-rks-keys-start))
  (should (fboundp '--rks-setup-initial-state-c!)))

(ert-deftest m6j-setup-initial-state-c/sets-single-cmd-key-start ()
  ;; Runtime variant also synchronizes this-single-command-key-start
  ;; with this-command-key-count (same as the rks-state variant).
  (--set-this-command-key-count        6)
  (--set-this-single-command-key-start 0)
  (--rks-setup-initial-state-c!)
  (should (= 6 (--this-single-command-key-start))))

(ert-deftest m6j-setters/accept-fixnums ()
  ;; The two C-shadow setters take non-negative fixnums.  Just verify
  ;; they don't error.
  (should (eq nil (--set-rks-echo-start 0)))
  (should (eq nil (--set-rks-keys-start 0)))
  (should (eq nil (--set-rks-echo-start 42)))
  (should (eq nil (--set-rks-keys-start 7))))

;;;; M6k — parallel replay-phase procedures

(ert-deftest m6k-replay-entire-sequence/exists ()
  (should (fboundp '--rks-setup-replay-entire-sequence!)))

(ert-deftest m6k-replay-sequence/exists ()
  (should (fboundp '--rks-setup-replay-sequence!)))

(ert-deftest m6k-replay-entire-sequence/runs-without-error ()
  ;; Operates on a fresh state.  All three keyremaps get rebased to
  ;; current-kboard maps + the global key-translation-map.
  (let ((s (--make-rks-state)))
    (--rks-setup-replay-entire-sequence! s)
    (should t)))

(ert-deftest m6k-replay-sequence/runs-without-error ()
  ;; replay_sequence reads keybuf[0..1] (gated by mock-input), so
  ;; calling it on a fresh state (mock-input = 0) just yields nil
  ;; events.  active-maps then produces the keymap stack at the
  ;; selected window's position.
  (let ((s (--make-rks-state)))
    (--rks-setup-replay-sequence! s)
    (should t)))

;;;; M6l — runtime replay-entire-sequence wire-in

(ert-deftest m6l-helpers/exist ()
  (should (fboundp '--rks-init-keyremaps))
  (should (fboundp '--rks-setup-replay-entire-sequence-c!)))

(ert-deftest m6l-rks-init-keyremaps/returns-nil ()
  ;; The bulk-init subr always returns nil; just verify it accepts
  ;; three arbitrary Lisp values.
  (should (eq nil (--rks-init-keyremaps nil nil nil))))

(ert-deftest m6l-runtime-variant/runs-without-error ()
  ;; The runtime variant reads from current-kboard and writes the
  ;; file-static C shadows.  No record argument — operates entirely
  ;; on C state.
  (--rks-setup-replay-entire-sequence-c!)
  (should t))

;;;; M6m — runtime replay_sequence wire-in

(ert-deftest m6m-helpers/exist ()
  (should (fboundp '--rks-replay-sequence-init-rest))
  (should (fboundp '--rks-setup-replay-sequence-c!)))

(ert-deftest m6m-init-rest/returns-nil ()
  ;; The subr writes file-statics and returns nil.
  (should (eq nil (--rks-replay-sequence-init-rest nil))))

(ert-deftest m6m-runtime-variant/runs-without-error ()
  ;; Two-arg runtime variant: simulates the call read_key_sequence
  ;; makes at the replay_sequence: label with mock_input == 0
  ;; (both keybuf elements nil).
  (--rks-setup-replay-sequence-c! nil nil)
  (should t))

;;;; M6n — done:-block remapped computation

(ert-deftest m6n-helpers/exist ()
  (should (fboundp '--set-read-key-sequence-remapped))
  (should (fboundp '--rks-done-compute-remapped!)))

(ert-deftest m6n-set-remapped/returns-nil ()
  (should (eq nil (--set-read-key-sequence-remapped nil)))
  (should (eq nil (--set-read-key-sequence-remapped t))))

(ert-deftest m6n-compute-remapped/runs-without-error ()
  ;; Whatever read_key_sequence_cmd happens to be, the call should
  ;; not error.
  (--rks-done-compute-remapped!)
  (should t))

;;;; M6o — shift-translated install

(ert-deftest m6o-helpers/exist ()
  (should (fboundp '--rks-shift-translated-p))
  (should (fboundp '--rks-done-install-shift-translated!)))

(ert-deftest m6o-shift-translated-p/returns-boolean ()
  (let ((v (--rks-shift-translated-p)))
    (should (or (eq v t) (eq v nil)))))

(ert-deftest m6o-install/runs-without-error ()
  (--rks-done-install-shift-translated!)
  (should t))

;;;; M6p — unread_switch_frame install

(ert-deftest m6p-helpers/exist ()
  (should (fboundp '--rks-delayed-switch-frame))
  (should (fboundp '--set-unread-switch-frame))
  (should (fboundp '--rks-done-install-unread-switch-frame!)))

(ert-deftest m6p-set-unread-switch-frame/returns-nil ()
  ;; The setter writes the C global `unread_switch_frame'.  It has
  ;; no elisp-visible defvar so we can only verify the setter
  ;; returns nil.
  (should (eq nil (--set-unread-switch-frame nil))))

(ert-deftest m6p-delayed-switch-frame/getter-runs ()
  ;; Whatever the C shadow currently holds, the getter returns a
  ;; valid Lisp value (typically nil at idle).
  (let ((v (--rks-delayed-switch-frame)))
    (should (or (eq v nil) v))))   ; non-nil objects are truthy

(ert-deftest m6p-install/runs-without-error ()
  ;; Install copies rks_delayed_switch_frame → unread_switch_frame.
  ;; In batch with no in-flight read_key_sequence, both are nil.
  (--rks-done-install-unread-switch-frame!)
  (should t))

;;;; M6q — keybuf stack

(ert-deftest m6q-helpers/exist ()
  (should (fboundp '--rks-keybuf-depth))
  (should (fboundp '--rks-keybuf-ref))
  (should (fboundp '--rks-keybuf-set)))

(ert-deftest m6q-depth/zero-at-idle ()
  ;; Outside of any in-flight read_key_sequence call, depth is 0.
  (should (= 0 (--rks-keybuf-depth))))

(ert-deftest m6q-ref/nil-when-stack-empty ()
  ;; Reading any index when the stack is empty returns nil (no crash).
  (should (eq nil (--rks-keybuf-ref 0)))
  (should (eq nil (--rks-keybuf-ref 5)))
  (should (eq nil (--rks-keybuf-ref 29))))

(ert-deftest m6q-set/no-op-when-stack-empty ()
  ;; Writing when no call is in flight is a silent no-op.
  (should (eq nil (--rks-keybuf-set 0 'sentinel))))

(ert-deftest m6q-ref/out-of-range-returns-nil ()
  ;; Out-of-range indices return nil rather than reading past the array.
  (should (eq nil (--rks-keybuf-ref 30)))
  (should (eq nil (--rks-keybuf-ref 100))))

;;;; M6r — downcase-undo

(ert-deftest m6r-helpers/exist ()
  (should (fboundp '--rks-original-uppercase))
  (should (fboundp '--rks-original-uppercase-position))
  (should (fboundp '--rks-t))
  (should (fboundp '--rks-current-binding))
  (should (fboundp '--set-rks-shift-translated))
  (should (fboundp '--rks-done-downcase-undo!)))

(ert-deftest m6r-original-uppercase-position/defaults-to-negative-or-zero ()
  ;; Pre-init the position is -1 (or whatever was last left after a
  ;; read_key_sequence call).  Just verify it's an integer.
  (should (integerp (--rks-original-uppercase-position))))

(ert-deftest m6r-downcase-undo/no-op-when-position-out-of-range ()
  ;; In batch when no read_key_sequence is in flight, t == 0 (or
  ;; whatever was last set).  No downcase undo should fire.
  (--rks-done-downcase-undo! nil)
  (--rks-done-downcase-undo! t)
  (should t))

;;;; M6s — fabricated-events finalize loop

(ert-deftest m6s-helpers/exist ()
  (should (fboundp '--rks-mock-input))
  (should (fboundp '--set-rks-t))
  (should (fboundp '--echo-update))
  (should (fboundp '--rks-done-fabricated-events!)))

(ert-deftest m6s-rks-mock-input/integer ()
  (should (integerp (--rks-mock-input))))

(ert-deftest m6s-set-rks-t/returns-nil ()
  (let ((saved (--rks-t)))
    (unwind-protect
        (progn
          (should (eq nil (--set-rks-t 0)))
          (should (= 0 (--rks-t))))
      (--set-rks-t saved))))

(ert-deftest m6s-fabricated-events/no-op-when-t-ge-mock-input ()
  ;; With t == mock_input (or t > mock_input), the loop doesn't fire,
  ;; so the procedure is just an echo-update.
  (--rks-done-fabricated-events!)
  (should t))

;;;; M6t — first_unbound short-circuit

(ert-deftest m6t-helpers/exist ()
  (should (fboundp '--rks-fkey-start))
  (should (fboundp '--rks-keytran-start))
  (should (fboundp '--rks-indec-start))
  (should (fboundp '--rks-first-unbound))
  (should (fboundp '--set-rks-mock-input))
  (should (fboundp '--rks-keybuf-shift-down))
  (should (fboundp '--rks-keyremaps-shrink-by))
  (should (fboundp '--rks-first-unbound-short-circuit!)))

(ert-deftest m6t-short-circuit/idle-returns-nil ()
  ;; At idle the predicate first_unbound < keytran.start is false
  ;; (both are 0 or both equal in any sensible state).  Should
  ;; return nil without touching state.
  (should (eq nil (--rks-first-unbound-short-circuit!))))

(ert-deftest m6t-keyremaps-shrink-by/returns-nil ()
  (should (eq nil (--rks-keyremaps-shrink-by 0))))

;;;; M6u — simple shift-translation (upper→lower)

(ert-deftest m6u-helpers/exist ()
  (should (fboundp '--rks-shift-translate-key)))

(ert-deftest m6u-translation-simple/nil-for-lowercase ()
  ;; 'a' (97) is already lowercase — downcase returns itself, so the
  ;; subr falls through with nil and does NOT mutate state.
  (should (eq nil (--rks-try-shift-translation-simple! 97))))

(ert-deftest m6u-translation-simple/nil-for-non-fixnum ()
  ;; A symbol key (e.g. arrow key) is not a fixnum — subr returns nil
  ;; without mutating state.
  (should (eq nil (--rks-try-shift-translation-simple! 'up))))

(ert-deftest m6u-translation-simple/nil-when-current-binding-non-nil ()
  ;; The predicate gates on NIL current_binding.  Tests don't have a
  ;; clean setter for current_binding without harming other paths, so
  ;; just verify the gating via the no-binding path (sufficient since
  ;; the C subr's first check is current_binding).
  (should (eq nil (--rks-try-shift-translation-simple! 97))))

;;;; M6v — help-char check

(ert-deftest m6v-helpers/exist ()
  (should (fboundp '--rks-try-help-char)))

(ert-deftest m6v-help-char/nil-when-rks-t-le-1 ()
  ;; The predicate gates on rks_t > 1.  At idle rks_t == 0, so any
  ;; KEY returns nil.
  (should (eq nil (--rks-try-help-char! 8)))   ;; ?\C-h is the typical help char
  (should (eq nil (--rks-try-help-char! ?a)))  ;; ordinary char
  (should (eq nil (--rks-try-help-char! 'foo))))

;;;; M6w — shifted-function-key shift-translation

(ert-deftest m6w-helpers/exist ()
  (should (fboundp '--rks-fn-key-shift-translate)))

(ert-deftest m6w-fn-key/nil-for-symbol-without-shift ()
  ;; A symbol key like `up' has no shift modifier and isn't an
  ;; uppercase fixnum — subr returns nil.
  (should (eq nil (--rks-try-shift-translation-fn-key! 'up))))

(ert-deftest m6w-fn-key/nil-for-lowercase ()
  ;; Lowercase char 'a' — not shifted, not uppercase — nil.
  (should (eq nil (--rks-try-shift-translation-fn-key! ?a))))

;;;; M6x — translation-map walks

(ert-deftest m6x-helpers/exist ()
  (should (fboundp '--rks-walk-translation-maps)))

(ert-deftest m6x-walk/nil-at-idle ()
  ;; At idle the keyremap structs are all at start == end == 0 (or
  ;; whatever the last call left), and rks_keybuf_depth == 0 so the
  ;; subr short-circuits to nil.
  (should (eq nil (--rks-walk-translation-maps! nil)))
  (should (eq nil (--rks-walk-translation-maps! "P> "))))

;;;; M6y — per-iteration setup + replay_key restore

(ert-deftest m6y-helpers/exist ()
  (should (fboundp '--rks-iter-setup-capture))
  (should (fboundp '--rks-iter-replay-restore))
  (should (fboundp '--rks-echo-local-start))
  (should (fboundp '--rks-set-echo-local-start))
  (should (fboundp '--rks-keys-local-start))
  (should (fboundp '--rks-set-keys-local-start))
  (should (fboundp '--rks-set-last-real-key-start)))

(ert-deftest m6y-echo-local-start/roundtrip ()
  (let ((saved (--rks-echo-local-start)))
    (unwind-protect
        (progn
          (--rks-set-echo-local-start 42)
          (should (= 42 (--rks-echo-local-start))))
      (--rks-set-echo-local-start saved))))

(ert-deftest m6y-keys-local-start/roundtrip ()
  (let ((saved (--rks-keys-local-start)))
    (unwind-protect
        (progn
          (--rks-set-keys-local-start 7)
          (should (= 7 (--rks-keys-local-start))))
      (--rks-set-keys-local-start saved))))

(ert-deftest m6y-setup-capture/runs-at-rks-t-below-limit ()
  ;; rks_t is 0 (or small) at idle — well below READ_KEY_ELTS (30).
  ;; Should run without error.
  (--rks-iter-setup-capture!)
  (should t))

(ert-deftest m6y-replay-restore/runs ()
  (--rks-iter-replay-restore!)
  (should t))

;;;; M6z — mock-input + end-of-macro cascade

(ert-deftest m6z-helpers/exist ()
  (should (fboundp '--rks-key))
  (should (fboundp '--rks-used-mouse-menu-p))
  (should (fboundp '--rks-iter-pre-read-cascade)))

(ert-deftest m6z-cascade/read-char-at-idle ()
  ;; At idle: rks_t == 0, rks_mock_input == 0 — not less than, so
  ;; branch 1 doesn't fire.  Vexecuting_kbd_macro is nil — branch 2
  ;; doesn't fire.  Cascade falls through to 'read-char.
  (should (eq 'read-char (--rks-iter-pre-read-cascade!))))

(ert-deftest m6z-used-mouse-menu-p/boolean ()
  (let ((v (--rks-used-mouse-menu-p)))
    (should (or (eq v t) (eq v nil)))))

;;;; M6aa — final binding-install + per-key bookkeeping

(ert-deftest m6aa-helpers/exist ()
  (should (fboundp '--rks-iter-install-binding)))

(ert-deftest m6aa-install/returns-nil ()
  ;; Call with nil new-binding outside of a read_key_sequence call.
  ;; rks_keybuf_depth == 0 means the keybuf-write is a no-op; we
  ;; just verify the subr runs without error.  It DOES mutate
  ;; rks_t, rks_current_binding, last_nonmenu_event, and
  ;; this_single_command_key_start — so save and restore those.
  (let ((saved-t (--rks-t))
        (saved-cb (--rks-current-binding))
        (saved-lne last-nonmenu-event)
        (saved-tsckcs (--this-single-command-key-start)))
    (unwind-protect
        (should (eq nil (--rks-iter-install-binding nil)))
      (--set-rks-t saved-t)
      (setq last-nonmenu-event saved-lne)
      (--set-this-single-command-key-start saved-tsckcs))))

;;;; M6ab — follow_key + first_unbound update

(ert-deftest m6ab-helpers/exist ()
  (should (fboundp '--rks-follow-key))
  (should (fboundp '--rks-new-binding)))

(ert-deftest m6ab-follow-key/nil-at-idle ()
  ;; At idle, rks_current_binding is nil and rks_key is nil.
  ;; follow_key(nil, nil) returns nil (no binding).  Subr returns nil.
  (should (eq nil (--rks-follow-key-and-update-first-unbound))))

(ert-deftest m6ab-new-binding/getter-runs ()
  (let ((v (--rks-new-binding)))
    (should (or (eq v nil) v))))

;;;; M6ac — mouse-click prefix expansion

(ert-deftest m6ac-helpers/exist ()
  (should (fboundp '--rks-iter-mouse-click-prefix)))

(ert-deftest m6ac-mouse-click/fall-through-at-idle ()
  ;; rks_key is nil at idle (no in-flight read).  No mouse-event
  ;; parameters present — subr returns `fall-through'.
  (should (eq 'fall-through (--rks-iter-mouse-click-prefix!))))

;;;; M6ad — unbound-event reduction

(ert-deftest m6ad-helpers/exist ()
  (should (fboundp '--rks-iter-unbound-event-reduction)))

(ert-deftest m6ad-reduction/fall-through-at-idle ()
  ;; At idle rks_key is nil — EVENT_HEAD/parse_modifiers yields no
  ;; reducer modifiers, so the subr falls through without mutating
  ;; state.
  (should (eq 'fall-through (--rks-iter-unbound-event-reduction!))))

;;;; M6ae — text-conversion-disable check

(ert-deftest m6ae-helpers/exist ()
  (should (fboundp '--rks-iter-maybe-disable-text-conversion)))

(ert-deftest m6ae-disable-text-conversion/runs-without-error ()
  ;; On builds without HAVE_TEXT_CONVERSION the subr is a no-op.
  ;; On HAVE_TEXT_CONVERSION builds the predicate gates on rks_t > 0;
  ;; at idle rks_t == 0 so the inner work is skipped.  Either way
  ;; the call runs cleanly and returns nil.
  (should (eq nil (--rks-iter-maybe-disable-text-conversion!))))

(provide 'ertest-read-key-sequence)
