;;; test-recent-keys.el --- M3 SRFI-64 suite for (emacs recent-keys)

;; Same coverage as ertest-recent-keys.el, transcribed for the
;; test-framework.el / SRFI-64 harness.  Keep in sync.

(test-begin "recent-keys")

;;;; lossage-size getter

(test-equal "lossage-size/default"   300 (lossage-size))
(test-equal "lossage-size/explicit-nil" 300 (lossage-size nil))

;;;; lossage-size setter + restore

(let ((orig (lossage-size)))
  (test-equal "lossage-size/set-200" 200 (lossage-size 200))
  (test-equal "lossage-size/get-200" 200 (lossage-size))
  (test-equal "lossage-size/set-500" 500 (lossage-size 500))
  (test-equal "lossage-size/get-500" 500 (lossage-size))
  (lossage-size orig)
  (test-equal "lossage-size/restored" orig (lossage-size)))

(let ((cur (lossage-size)))
  (test-equal "lossage-size/set-same-noop" cur (lossage-size cur)))

;;;; boundary signals

(test-assert "lossage-size/below-min-signals"
             (condition-case nil
                 (progn (lossage-size 50) nil)
               (user-error t)))

(test-assert "lossage-size/negative-signals"
             (condition-case nil
                 (progn (lossage-size -1) nil)
               (user-error t)))

(test-assert "lossage-size/non-number-signals"
             (condition-case nil
                 (progn (lossage-size "x") nil)
               (user-error t)))

(let ((orig (lossage-size)))
  (test-equal "lossage-size/at-min-100" 100 (lossage-size 100))
  (lossage-size orig))

;;;; recent-keys

(let ((r (recent-keys)))
  (test-assert "recent-keys/result-is-string-or-vector"
               (or (stringp r) (vectorp r)))
  (test-equal "recent-keys/empty-length-zero" 0 (length r)))

(let ((r (recent-keys t)))
  (test-assert "recent-keys-cmds/result-shape"
               (or (stringp r) (vectorp r)))
  (test-equal "recent-keys-cmds/empty-length-zero" 0 (length r)))

(test-end)
