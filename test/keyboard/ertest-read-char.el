;;; ertest-read-char.el --- M8a ERT suite for (emacs read-char)

;; M8a — foundation only.  Module skeleton + <rc-state> Scheme
;; record type + C-side state-pointer stack with 4 trivial getters.
;; No splices into read_char_1 yet — those start at M8e.
;;
;; See docs/keyboard.org §M8.

(require 'ert)

;;;; <rc-state> Scheme record + factory

(ert-deftest m8a-helpers/exist ()
  (should (fboundp '--make-rc-state))
  (should (fboundp '--rc-state-fresh!)))

(ert-deftest m8a-rc-state/constructs-non-nil ()
  (let ((s (--make-rc-state)))
    (should (not (null s)))))

(ert-deftest m8a-rc-state-fresh/runs-without-error ()
  ;; Resetting a freshly-constructed state is a no-op (defaults =
  ;; defaults) but must not error.
  (let ((s (--make-rc-state)))
    (--rc-state-fresh! s)
    (should t)))

;;;; M8c — prologue drain

(ert-deftest m8c-helpers/exist ()
  (should (fboundp '--rc-prologue-drain-unread)))

(ert-deftest m8c-drain/fall-through-at-idle ()
  ;; Outside any in-flight read_char, the stack is empty and the
  ;; subr early-returns `fall-through' before touching anything.
  (should (eq 'fall-through (--rc-prologue-drain-unread!))))

;;;; M8d — kbd-macro + unread-switch-frame early exits

(ert-deftest m8d-helpers/exist ()
  (should (fboundp '--rc-prologue-macro-or-switch-frame)))

(ert-deftest m8d-macro-sf/fall-through-at-idle ()
  ;; No kbd-macro running and no unread-switch-frame at batch
  ;; startup; subr returns `fall-through'.
  (should (eq 'fall-through (--rc-prologue-macro-or-switch-frame!))))

;;;; M8e — redisplay loop

(ert-deftest m8e-helpers/exist ()
  (should (fboundp '--rc-prologue-redisplay)))

(ert-deftest m8e-redisplay/no-op-when-stack-empty ()
  ;; Outside any in-flight read_char, the subr early-returns nil
  ;; without touching the redisplay machinery.
  (should (eq nil (--rc-prologue-redisplay!))))

;;;; M8f — echo + minibuf-menu

(ert-deftest m8f-helpers/exist ()
  (should (fboundp '--rc-prologue-echo-and-menu)))

(ert-deftest m8f-echo-menu/fall-through-at-idle ()
  ;; Outside any in-flight read_char, the subr early-returns
  ;; `fall-through' before touching anything.
  (should (eq 'fall-through (--rc-prologue-echo-and-menu!))))

;;;; M8g — idle-timer + immediate-echo + auto-save

(ert-deftest m8g-helpers/exist ()
  (should (fboundp '--rc-prologue-idle-echo-autosave)))

(ert-deftest m8g-idle-echo-autosave/no-op-when-stack-empty ()
  ;; Outside any in-flight read_char, the subr early-returns nil.
  (should (eq nil (--rc-prologue-idle-echo-autosave!))))

;;;; M8h — X-menu + auto-save-by-idle-timeout + GC

(ert-deftest m8h-helpers/exist ()
  (should (fboundp '--rc-prologue-xmenu-and-idle-gc)))

(ert-deftest m8h-xmenu-idle-gc/fall-through-at-idle ()
  ;; Outside any in-flight read_char, the subr early-returns
  ;; `fall-through' before touching anything.
  (should (eq 'fall-through (--rc-prologue-xmenu-and-idle-gc!))))

;;;; M8i — wrong-kboard + unread-events + kbd-queue + other-kboard

(ert-deftest m8i-helpers/exist ()
  (should (fboundp '--rc-prologue-kboard-and-queues)))

(ert-deftest m8i-kboard-queues/fall-through-at-idle ()
  ;; Outside any in-flight read_char, the subr early-returns
  ;; `fall-through' without touching kboard or queue state.
  (should (eq 'fall-through (--rc-prologue-kboard-and-queues!))))

;;;; M8j — wrong_kboard + non_reread loop

(ert-deftest m8j-helpers/exist ()
  (should (fboundp '--rc-wrong-kboard-and-non-reread)))

(ert-deftest m8j-wkbd-nr/fall-through-at-idle ()
  ;; Outside any in-flight read_char, the subr early-returns
  ;; `fall-through' before touching read_decoded_event_from_main_queue.
  (should (eq 'fall-through (--rc-wrong-kboard-and-non-reread!))))

;;;; M8k — BUFFERP + special-event-map dispatch

(ert-deftest m8k-helpers/exist ()
  (should (fboundp '--rc-bufferp-and-special-event-map)))

(ert-deftest m8k-bufp-special/fall-through-at-idle ()
  ;; Outside any in-flight read_char, the subr early-returns
  ;; `fall-through' before touching state.
  (should (eq 'fall-through (--rc-bufferp-and-special-event-map!))))

;;;; M8l — translate + menu-bar + record + echo-wipe

(ert-deftest m8l-helpers/exist ()
  (should (fboundp '--rc-event-translate-and-record)))

(ert-deftest m8l-translate-record/fall-through-at-idle ()
  ;; Outside any in-flight read_char, the subr early-returns
  ;; `fall-through' before touching record_char / echo state.
  (should (eq 'fall-through (--rc-event-translate-and-record!))))

;;;; M8m — input-method dispatch + record-if-unread

(ert-deftest m8m-helpers/exist ()
  (should (fboundp '--rc-input-method-dispatch)))

(ert-deftest m8m-input-method/fall-through-at-idle ()
  ;; Outside any in-flight read_char, the subr early-returns
  ;; `fall-through' before touching Vinput_method_function or
  ;; this_command_keys.
  (should (eq 'fall-through (--rc-input-method-dispatch!))))

;;;; M8n — help-echo + this-command-keys + help-form

(ert-deftest m8n-helpers/exist ()
  (should (fboundp '--rc-help-echo-and-help-form)))

(ert-deftest m8n-help-echo-form/fall-through-at-idle ()
  ;; Outside any in-flight read_char, the subr early-returns
  ;; `fall-through' before touching show_help_echo or help_form.
  (should (eq 'fall-through (--rc-help-echo-and-help-form!))))

;;;; M8final — exit tail + hoisted dispatcher

(ert-deftest m8final-helpers/exist ()
  (should (fboundp '--rc-exit))
  (should (fboundp '--read-char-main)))

(ert-deftest m8final-rc-exit/nil-at-idle ()
  ;; --rc-exit returns nil when rc_state_stack is empty (no
  ;; in-flight read_char to read state->c from).
  (should (eq nil (--rc-exit!))))

;;;; Step 1 of state-to-record migration — companion Scheme record

(ert-deftest step1-helpers/exist ()
  (should (fboundp '--rc-record)))

(ert-deftest step1-rc-record/nil-at-idle ()
  ;; Outside any in-flight read_char, no SCM record is allocated.
  (should (eq nil (--rc-record))))

;;;; Step 2-A — sync subrs (C struct <-> Scheme record)

(ert-deftest step2a-helpers/exist ()
  (should (fboundp '--rc-sync-to-record))
  (should (fboundp '--rc-sync-from-record)))

(ert-deftest step2a-sync-to-record/nil-at-idle ()
  ;; With no in-flight read_char, sync-to-record finds no state
  ;; and returns nil (no record to populate).
  (should (eq nil (--rc-sync-to-record))))

(ert-deftest step2a-sync-from-record/nil-at-idle ()
  ;; With no in-flight read_char, sync-from-record is a no-op.
  (should (eq nil (--rc-sync-from-record))))

(provide 'ertest-read-char)
