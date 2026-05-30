;;; ertest-read-char.el --- M8a ERT suite for (emacs read-char)

;; M8a — foundation only.  Module skeleton + <rc-state> Scheme
;; record type + C-side state-pointer stack with 4 trivial getters.
;; No splices into read_char_1 yet — those start at M8e.
;;
;; See docs/keyboard.org §M8.

(require 'ert)

;;;; <rc-state> Scheme record + factory

(defvar m8--test-rec nil)
(defvar m8-test-special-observed nil)

(defun m8-test-state-ref (field)
  (--rc-test-state-ref m8--test-rec field))

(defun m8-with-rc-state (bindings thunk)
  (let ((m8--test-rec (--make-rc-state)))
    (--rc-state-fresh! m8--test-rec)
    (dolist (binding bindings)
      (--rc-test-state-set! m8--test-rec (car binding) (cdr binding)))
    (--rc-test-with-state m8--test-rec thunk)))

(defun m8-test-special-command ()
  (interactive)
  (setq m8-test-special-observed last-input-event))

(defun m8-clear-unread-switch-frame ()
  (--set-unread-switch-frame nil))

(ert-deftest m8a-helpers/exist ()
  (should (fboundp '--make-rc-state))
  (should (fboundp '--rc-state-fresh!))
  (should (fboundp '--rc-test-state-ref))
  (should (fboundp '--rc-test-state-set!))
  (should (fboundp '--rc-test-with-state)))

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

(ert-deftest m8c-drain/unread-post-input-method-first ()
  (let ((unread-post-input-method-events (list ?p))
        (unread-command-events nil)
        (unread-input-method-events nil))
    (m8-with-rc-state
     nil
     (lambda ()
       (should (eq 'reread-first (--rc-prologue-drain-unread!)))
       (should (eq ?p (m8-test-state-ref 'c)))
       (should (eq t (m8-test-state-ref 'reread)))
       (should (null unread-post-input-method-events))))))

(ert-deftest m8c-drain/no-record-command-event ()
  (let ((unread-post-input-method-events nil)
        (unread-command-events (list (cons 'no-record ?n)))
        (unread-input-method-events nil))
    (m8-with-rc-state
     nil
     (lambda ()
       (should (eq 'reread-for-input-method
                   (--rc-prologue-drain-unread!)))
       (should (eq ?n (m8-test-state-ref 'c)))
       (should (eq t (m8-test-state-ref 'recorded)))
       (should (eq t (m8-test-state-ref 'reread)))
       (should (null unread-command-events))))))

(ert-deftest m8c-drain/unread-input-method-peels-popup-cons ()
  (let ((unread-post-input-method-events nil)
        (unread-command-events nil)
        (unread-input-method-events (list (cons ?i nil))))
    (m8-with-rc-state
     nil
     (lambda ()
       (should (eq 'reread-for-input-method
                   (--rc-prologue-drain-unread!)))
       (should (eq ?i (m8-test-state-ref 'c)))
       (should (eq t (m8-test-state-ref 'reread)))
       (should (null unread-input-method-events))))))

(ert-deftest m8c-drain/disabled-command-event-peels-to-head ()
  (let ((unread-post-input-method-events nil)
        (unread-command-events (list (cons 'm8-disabled 'disabled)))
        (unread-input-method-events nil))
    (m8-with-rc-state
     nil
     (lambda ()
       (should (eq 'reread-for-input-method
                   (--rc-prologue-drain-unread!)))
       (should (eq 'm8-disabled (m8-test-state-ref 'c)))
       (should (null (m8-test-state-ref 'recorded)))
       (should (eq t (m8-test-state-ref 'reread)))
       (should (null unread-command-events))))))

;;;; M8d — kbd-macro + unread-switch-frame early exits

(ert-deftest m8d-helpers/exist ()
  (should (fboundp '--rc-prologue-macro-or-switch-frame)))

(ert-deftest m8d-macro-sf/fall-through-at-idle ()
  ;; No kbd-macro running and no unread-switch-frame at batch
  ;; startup; subr returns `fall-through'.
  (should (eq 'fall-through (--rc-prologue-macro-or-switch-frame!))))

(ert-deftest m8d-macro/replays-next-string-event ()
  (let ((executing-kbd-macro "a")
        (executing-kbd-macro-index 0))
    (m8-with-rc-state
     nil
     (lambda ()
       (should (eq 'from-macro (--rc-prologue-macro-or-switch-frame!)))
       (should (eq ?a (m8-test-state-ref 'c)))
       (should (eq 1 executing-kbd-macro-index))))))

(ert-deftest m8d-macro/decodes-meta-bit-from-string ()
  (let ((executing-kbd-macro (string #x80))
        (executing-kbd-macro-index 0))
    (m8-with-rc-state
     nil
     (lambda ()
       (should (eq 'from-macro (--rc-prologue-macro-or-switch-frame!)))
       (should (eq #x8000000 (m8-test-state-ref 'c)))
       (should (eq 1 executing-kbd-macro-index))))))

(ert-deftest m8d-switch-frame/takes-pending-event ()
  (let ((event (list 'switch-frame (selected-frame))))
    (unwind-protect
        (progn
          (--set-unread-switch-frame event)
          (m8-with-rc-state
           nil
           (lambda ()
             (should (eq 'reread-first
                         (--rc-prologue-macro-or-switch-frame!)))
             (should (eq event (m8-test-state-ref 'c)))
             (should (null (--get-unread-switch-frame))))))
      (m8-clear-unread-switch-frame))))

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

(ert-deftest m8f-echo-menu/live-fall-through-clears-c ()
  (m8-with-rc-state
   '((c . ?x))
   (lambda ()
     (should (eq 'fall-through (--rc-prologue-echo-and-menu!)))
     (should (null (m8-test-state-ref 'c))))))

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

(ert-deftest m8i-kboard-queues/wrong-kboard-when-origin-missing ()
  (m8-with-rc-state
   nil
   (lambda ()
     (should (eq 'return-wrong-kboard
                 (--rc-prologue-kboard-and-queues!))))))

(ert-deftest m8i-kboard-queues/drains-no-record-command-event ()
  (let ((unread-command-events (list (cons 'no-record ?u))))
    (m8-with-rc-state
     `((orig-kboard . ,(current-kboard)))
     (lambda ()
       (should (eq 'fall-through (--rc-prologue-kboard-and-queues!)))
       (should (eq ?u (m8-test-state-ref 'c)))
       (should (eq t (m8-test-state-ref 'recorded)))
       (should (eq t (m8-test-state-ref 'reread)))
       (should (null unread-command-events))))))

(ert-deftest m8i-kboard-queues/qt-wrapper-does-not-mark-reread ()
  (let ((unread-command-events (list (cons t ?q))))
    (m8-with-rc-state
     `((orig-kboard . ,(current-kboard)))
     (lambda ()
       (should (eq 'fall-through (--rc-prologue-kboard-and-queues!)))
       (should (eq ?q (m8-test-state-ref 'c)))
       (should (null (m8-test-state-ref 'recorded)))
       (should (null (m8-test-state-ref 'reread)))
       (should (null unread-command-events))))))

;;;; M8j — wrong_kboard + non_reread loop

(ert-deftest m8j-helpers/exist ()
  (should (fboundp '--rc-wrong-kboard-and-non-reread)))

(ert-deftest m8j-wkbd-nr/fall-through-at-idle ()
  ;; Outside any in-flight read_char, the subr early-returns
  ;; `fall-through' before touching read_decoded_event_from_main_queue.
  (should (eq 'fall-through (--rc-wrong-kboard-and-non-reread!))))

(ert-deftest m8j-wkbd-nr/preset-c-falls-through ()
  (m8-with-rc-state
   '((c . ?j))
   (lambda ()
     (should (eq 'fall-through (--rc-wrong-kboard-and-non-reread!)))
     (should (eq ?j (m8-test-state-ref 'c))))))

;;;; M8k — BUFFERP + special-event-map dispatch

(ert-deftest m8k-helpers/exist ()
  (should (fboundp '--rc-bufferp-and-special-event-map)))

(ert-deftest m8k-bufp-special/fall-through-at-idle ()
  ;; Outside any in-flight read_char, the subr early-returns
  ;; `fall-through' before touching state.
  (should (eq 'fall-through (--rc-bufferp-and-special-event-map!))))

(ert-deftest m8k-bufp-special/buffer-event-goes-to-exit ()
  (m8-with-rc-state
   `((c . ,(current-buffer)))
   (lambda ()
     (should (eq 'goto-exit (--rc-bufferp-and-special-event-map!))))))

(ert-deftest m8k-bufp-special/dispatches-special-event ()
  (let ((special-event-map (make-sparse-keymap))
        (while-no-input-ignore-events nil)
        (last-input-event nil)
        (m8-test-special-observed nil))
    (define-key special-event-map [m8-test-special]
      'm8-test-special-command)
    (m8-with-rc-state
     '((c . m8-test-special))
     (lambda ()
       (should (eq 'goto-retry (--rc-bufferp-and-special-event-map!)))
       (should (eq 'm8-test-special m8-test-special-observed))
       (should (eq 'm8-test-special last-input-event))
       (should (eq 'm8-test-special (m8-test-state-ref 'c)))))))

;;;; M8l — translate + menu-bar + record + echo-wipe

(ert-deftest m8l-helpers/exist ()
  (should (fboundp '--rc-event-translate-and-record)))

(ert-deftest m8l-translate-record/fall-through-at-idle ()
  ;; Outside any in-flight read_char, the subr early-returns
  ;; `fall-through' before touching record_char / echo state.
  (should (eq 'fall-through (--rc-event-translate-and-record!))))

(ert-deftest m8l-translate-record/eof-goes-to-exit ()
  (m8-with-rc-state
   '((c . -1))
   (lambda ()
     (should (eq 'goto-exit (--rc-event-translate-and-record!))))))

(ert-deftest m8l-translate-record/records-printable-input-method-event ()
  (let ((input-method-function #'ignore)
        (input-method-previous-message nil))
    (m8-with-rc-state
     '((c . ?z))
     (lambda ()
       (should (eq 'fall-through
                   (--rc-event-translate-and-record!)))
       (should (eq t (m8-test-state-ref 'recorded)))
       (should (eq ?z (m8-test-state-ref 'c)))))))

;;;; M8m — input-method dispatch + record-if-unread

(ert-deftest m8m-helpers/exist ()
  (should (fboundp '--rc-input-method-dispatch)))

(ert-deftest m8m-input-method/fall-through-at-idle ()
  ;; Outside any in-flight read_char, the subr early-returns
  ;; `fall-through' before touching Vinput_method_function or
  ;; this_command_keys.
  (should (eq 'fall-through (--rc-input-method-dispatch!))))

(ert-deftest m8m-input-method/installs-returned-events ()
  (let ((input-method-function (lambda (_c) (list ?x ?y ?z)))
        (unread-post-input-method-events nil))
    (m8-with-rc-state
     '((c . ?a))
     (lambda ()
       (should (eq 'fall-through (--rc-input-method-dispatch!)))
       (should (eq ?x (m8-test-state-ref 'c)))
       (should (equal (list ?y ?z) unread-post-input-method-events))
       (should (eq t (m8-test-state-ref 'recorded)))))))

;;;; M8n — help-echo + this-command-keys + help-form

(ert-deftest m8n-helpers/exist ()
  (should (fboundp '--rc-help-echo-and-help-form)))

(ert-deftest m8n-help-echo-form/fall-through-at-idle ()
  ;; Outside any in-flight read_char, the subr early-returns
  ;; `fall-through' before touching show_help_echo or help_form.
  (should (eq 'fall-through (--rc-help-echo-and-help-form!))))

(ert-deftest m8n-help-echo-form/records-command-key ()
  (let ((help-form nil)
        (last-input-event nil))
    (unwind-protect
        (progn
          (clear-this-command-keys)
          (m8-with-rc-state
           '((c . ?r))
           (lambda ()
             (should (eq 'fall-through
                         (--rc-help-echo-and-help-form!)))
             (should (eq ?r last-input-event))
             (should (equal "r" (this-command-keys-vector))))))
      (clear-this-command-keys))))

;;;; M8final — exit tail + hoisted dispatcher

(ert-deftest m8final-helpers/exist ()
  (should (fboundp '--rc-exit))
  (should (fboundp '--read-char-main)))

(ert-deftest m8final-rc-exit/nil-at-idle ()
  ;; --rc-exit returns nil when rc_state_stack is empty (no
  ;; in-flight read_char to read state->c from).
  (should (eq nil (--rc-exit!))))

(ert-deftest m8final-rc-exit/returns-live-state-c ()
  (m8-with-rc-state
   '((c . ?e))
   (lambda ()
     (should (eq ?e (--rc-exit!))))))

;;;; Hoisted focus-in helper

(ert-deftest focus-in-helpers/exist ()
  (should (fboundp 'internal-handle-focus-in))
  (should (fboundp '--get-internal-last-event-frame))
  (should (fboundp '--set-internal-last-event-frame))
  (should (fboundp '--get-unread-switch-frame))
  (should (fboundp '--set-unread-switch-frame)))

(ert-deftest focus-in/rejects-invalid-event ()
  (should-error (internal-handle-focus-in '(focus-in not-a-frame))))

(ert-deftest focus-in/updates-internal-last-event-frame ()
  (let ((frame (selected-frame)))
    (unwind-protect
        (progn
          (--set-internal-last-event-frame nil)
          (m8-clear-unread-switch-frame)
          (should (null (internal-handle-focus-in (list 'focus-in frame))))
          (should (eq frame (--get-internal-last-event-frame)))
          (should (null (--get-unread-switch-frame))))
      (m8-clear-unread-switch-frame))))

(ert-deftest focus-in/preserves-pending-switch-frame ()
  (let ((frame (selected-frame)))
    (unwind-protect
        (progn
          (--set-internal-last-event-frame frame)
          (--set-unread-switch-frame 'pending-switch)
          (should (null (internal-handle-focus-in (list 'focus-in frame))))
          (let ((event (--get-unread-switch-frame)))
            (should (eq 'switch-frame (car event)))
            (should (eq frame (cadr event)))))
      (m8-clear-unread-switch-frame))))

;;;; Step 1 of state-to-record migration — companion Scheme record

(ert-deftest step1-helpers/exist ()
  (should (fboundp '--rc-record)))

(ert-deftest step1-rc-record/nil-at-idle ()
  ;; Outside any in-flight read_char, no SCM record is allocated.
  (should (eq nil (--rc-record))))

(provide 'ertest-read-char)
