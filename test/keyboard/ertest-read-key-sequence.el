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

(provide 'ertest-read-key-sequence)
