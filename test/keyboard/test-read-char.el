;;; test-read-char.el --- M8a SRFI-64 suite

;; Same coverage as ertest-read-char.el, transcribed for the
;; test-framework.el / SRFI-64 harness.  Keep in sync.

(test-begin "read-char")

(test-assert "helpers/make-rc-state"    (fboundp '--make-rc-state))
(test-assert "helpers/rc-state-fresh!"  (fboundp '--rc-state-fresh!))

(let ((s (--make-rc-state)))
  (test-assert "rc-state/constructs-non-nil" (not (null s)))
  (--rc-state-fresh! s)
  (test-assert "rc-state-fresh/runs" t))

;;;; M8c

(test-assert "helpers/rc-prologue-drain-unread"
             (fboundp '--rc-prologue-drain-unread))
(test-eq "drain/fall-through-at-idle"
         'fall-through (--rc-prologue-drain-unread!))

;;;; M8d

(test-assert "helpers/rc-prologue-macro-or-switch-frame"
             (fboundp '--rc-prologue-macro-or-switch-frame))
(test-eq "macro-sf/fall-through-at-idle"
         'fall-through (--rc-prologue-macro-or-switch-frame!))

;;;; M8e

(test-assert "helpers/rc-prologue-redisplay"
             (fboundp '--rc-prologue-redisplay))
(test-eq "redisplay/no-op-when-stack-empty"
         nil (--rc-prologue-redisplay!))

;;;; M8f

(test-assert "helpers/rc-prologue-echo-and-menu"
             (fboundp '--rc-prologue-echo-and-menu))
(test-eq "echo-menu/fall-through-at-idle"
         'fall-through (--rc-prologue-echo-and-menu!))

;;;; M8g

(test-assert "helpers/rc-prologue-idle-echo-autosave"
             (fboundp '--rc-prologue-idle-echo-autosave))
(test-eq "idle-echo-autosave/no-op-when-stack-empty"
         nil (--rc-prologue-idle-echo-autosave!))

;;;; M8h

(test-assert "helpers/rc-prologue-xmenu-and-idle-gc"
             (fboundp '--rc-prologue-xmenu-and-idle-gc))
(test-eq "xmenu-and-idle-gc/fall-through-at-idle"
         'fall-through (--rc-prologue-xmenu-and-idle-gc!))

;;;; M8i

(test-assert "helpers/rc-prologue-kboard-and-queues"
             (fboundp '--rc-prologue-kboard-and-queues))
(test-eq "kboard-and-queues/fall-through-at-idle"
         'fall-through (--rc-prologue-kboard-and-queues!))

;;;; M8j

(test-assert "helpers/rc-wrong-kboard-and-non-reread"
             (fboundp '--rc-wrong-kboard-and-non-reread))
(test-eq "wkbd-nr/fall-through-at-idle"
         'fall-through (--rc-wrong-kboard-and-non-reread!))

;;;; M8k

(test-assert "helpers/rc-bufferp-and-special-event-map"
             (fboundp '--rc-bufferp-and-special-event-map))
(test-eq "bufp-special/fall-through-at-idle"
         'fall-through (--rc-bufferp-and-special-event-map!))

;;;; M8l

(test-assert "helpers/rc-event-translate-and-record"
             (fboundp '--rc-event-translate-and-record))
(test-eq "translate-record/fall-through-at-idle"
         'fall-through (--rc-event-translate-and-record!))

;;;; M8m

(test-assert "helpers/rc-input-method-dispatch"
             (fboundp '--rc-input-method-dispatch))
(test-eq "input-method/fall-through-at-idle"
         'fall-through (--rc-input-method-dispatch!))

;;;; M8n

(test-assert "helpers/rc-help-echo-and-help-form"
             (fboundp '--rc-help-echo-and-help-form))
(test-eq "help-echo-form/fall-through-at-idle"
         'fall-through (--rc-help-echo-and-help-form!))

;;;; M8final

(test-assert "helpers/rc-exit"         (fboundp '--rc-exit))
(test-assert "helpers/read-char-main"  (fboundp '--read-char-main))
(test-eq "rc-exit/nil-at-idle" nil (--rc-exit!))

;;;; Step 1 of state-to-record migration

(test-assert "helpers/rc-record" (fboundp '--rc-record))
(test-eq "rc-record/nil-at-idle" nil (--rc-record))

(test-end)
