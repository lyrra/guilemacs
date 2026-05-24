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

(test-end)
