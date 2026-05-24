;;; ertest-read-char.el --- M8a ERT suite for (emacs read-char)

;; M8a — foundation only.  Module skeleton + <rc-state> Scheme
;; record type + C-side state-pointer stack with 4 trivial getters.
;; No splices into read_char_1 yet — those start at M8e.
;;
;; See docs/keyboard.org §M8.

(require 'ert)

;;;; Existence checks

(ert-deftest m8a-helpers/exist ()
  (should (fboundp '--rc-state-depth))
  (should (fboundp '--rc-commandflag))
  (should (fboundp '--rc-map))
  (should (fboundp '--rc-prev-event))
  (should (fboundp '--rc-reread-p))
  (should (fboundp '--make-rc-state))
  (should (fboundp '--rc-state-fresh!)))

;;;; C-side stack at idle

(ert-deftest m8a-state-depth/zero-at-idle ()
  ;; Outside any in-flight read_char invocation, depth is 0.
  (should (= 0 (--rc-state-depth))))

(ert-deftest m8a-getters/defaults-when-stack-empty ()
  ;; Each accessor returns its struct-default when the stack is
  ;; empty (no crash on dereferencing the empty stack).
  (should (= 0 (--rc-commandflag)))
  (should (eq nil (--rc-map)))
  (should (eq nil (--rc-prev-event)))
  (should (eq nil (--rc-reread-p))))

;;;; Scheme record

(ert-deftest m8a-rc-state/constructs-non-nil ()
  (let ((s (--make-rc-state)))
    (should (not (null s)))))

(ert-deftest m8a-rc-state-fresh/runs-without-error ()
  ;; Resetting a freshly-constructed state is a no-op (defaults =
  ;; defaults) but must not error.
  (let ((s (--make-rc-state)))
    (--rc-state-fresh! s)
    (should t)))

;;;; M8b — extended accessors

(ert-deftest m8b-helpers/exist ()
  (should (fboundp '--rc-c))
  (should (fboundp '--set-rc-c))
  (should (fboundp '--rc-recorded-p))
  (should (fboundp '--set-rc-recorded))
  (should (fboundp '--set-rc-reread))
  (should (fboundp '--rc-set-used-mouse-menu)))

(ert-deftest m8b-setters/no-op-when-stack-empty ()
  ;; Outside any in-flight read_char, setters silently succeed
  ;; (return nil, mutate nothing).
  (should (eq nil (--set-rc-c 'sentinel)))
  (should (eq nil (--set-rc-recorded t)))
  (should (eq nil (--set-rc-reread t)))
  (should (eq nil (--rc-set-used-mouse-menu t))))

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

(provide 'ertest-read-char)
