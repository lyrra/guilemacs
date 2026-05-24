;;; test-read-char.el --- M8a SRFI-64 suite

;; Same coverage as ertest-read-char.el, transcribed for the
;; test-framework.el / SRFI-64 harness.  Keep in sync.

(test-begin "read-char")

(test-assert "helpers/rc-state-depth"   (fboundp '--rc-state-depth))
(test-assert "helpers/rc-commandflag"   (fboundp '--rc-commandflag))
(test-assert "helpers/rc-map"           (fboundp '--rc-map))
(test-assert "helpers/rc-prev-event"    (fboundp '--rc-prev-event))
(test-assert "helpers/rc-reread-p"      (fboundp '--rc-reread-p))
(test-assert "helpers/make-rc-state"    (fboundp '--make-rc-state))
(test-assert "helpers/rc-state-fresh!"  (fboundp '--rc-state-fresh!))

(test-equal "state-depth/zero-at-idle"  0   (--rc-state-depth))
(test-equal "commandflag/default"       0   (--rc-commandflag))
(test-eq    "map/default-nil"           nil (--rc-map))
(test-eq    "prev-event/default-nil"    nil (--rc-prev-event))
(test-eq    "reread-p/default-nil"      nil (--rc-reread-p))

(let ((s (--make-rc-state)))
  (test-assert "rc-state/constructs-non-nil" (not (null s)))
  (--rc-state-fresh! s)
  (test-assert "rc-state-fresh/runs" t))

;;;; M8b

(test-assert "helpers/rc-c"              (fboundp '--rc-c))
(test-assert "helpers/set-rc-c"          (fboundp '--set-rc-c))
(test-assert "helpers/rc-recorded-p"     (fboundp '--rc-recorded-p))
(test-assert "helpers/set-rc-recorded"   (fboundp '--set-rc-recorded))
(test-assert "helpers/set-rc-reread"     (fboundp '--set-rc-reread))
(test-assert "helpers/rc-set-used-mouse-menu"
             (fboundp '--rc-set-used-mouse-menu))

(test-eq "setters/no-op-when-stack-empty-c"        nil (--set-rc-c 'x))
(test-eq "setters/no-op-when-stack-empty-recorded" nil (--set-rc-recorded t))
(test-eq "setters/no-op-when-stack-empty-reread"   nil (--set-rc-reread t))
(test-eq "setters/no-op-when-stack-empty-ump"      nil (--rc-set-used-mouse-menu t))

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

(test-end)
