;;; ertest-recent-keys.el --- M3 ERT suite for (emacs recent-keys)

;; M3 gating tests.  Exercises (recent-keys) and (lossage-size) now
;; that their elisp DEFUN bodies dispatch to mod/emacs/recent-keys.scm.
;; The ring storage itself (recent_keys vector, indices) stays in
;; keyboard.c — these tests exercise the user-facing wrappers, not the
;; ring writer (which is still C-side record_char).
;;
;; See docs/keyboard.org §"M3 — Echo / recent-keys / dribble".

(require 'ert)

;;;; lossage-size — getter

(ert-deftest m3-lossage-size/getter-default ()
  ;; Default ring size is 3 * MIN_NUM_RECENT_KEYS = 300.
  (should (= (lossage-size) 300)))

(ert-deftest m3-lossage-size/getter-with-nil ()
  ;; Explicit nil argument behaves like no argument.
  (should (= (lossage-size nil) 300)))

;;;; lossage-size — setter

(ert-deftest m3-lossage-size/set-and-restore ()
  (let ((orig (lossage-size)))
    (unwind-protect
        (progn
          (should (= (lossage-size 200) 200))
          (should (= (lossage-size) 200))
          (should (= (lossage-size 500) 500))
          (should (= (lossage-size) 500)))
      (lossage-size orig)
      (should (= (lossage-size) orig)))))

(ert-deftest m3-lossage-size/set-same-noop ()
  ;; Setting to the current value short-circuits — should still return
  ;; the current limit.
  (let ((cur (lossage-size)))
    (should (= (lossage-size cur) cur))))

;;;; lossage-size — boundary signals

(ert-deftest m3-lossage-size/below-min-signals ()
  ;; MIN_NUM_RECENT_KEYS = 100; anything smaller must signal user-error.
  (should-error (lossage-size 50)  :type 'user-error)
  (should-error (lossage-size 99)  :type 'user-error)
  (should-error (lossage-size 1)   :type 'user-error))

(ert-deftest m3-lossage-size/at-min-accepted ()
  (let ((orig (lossage-size)))
    (unwind-protect
        (should (= (lossage-size 100) 100))
      (lossage-size orig))))

(ert-deftest m3-lossage-size/negative-signals ()
  (should-error (lossage-size -1) :type 'user-error)
  (should-error (lossage-size "not-a-number") :type 'user-error))

;;;; recent-keys

(ert-deftest m3-recent-keys/empty-returns-empty ()
  ;; Batch startup hasn't recorded any keys — result should be a
  ;; string or vector of length 0.
  (let ((r (recent-keys)))
    (should (or (stringp r) (vectorp r)))
    (should (= (length r) 0))))

(ert-deftest m3-recent-keys/include-cmds-empty ()
  ;; With include-cmds, same shape.
  (let ((r (recent-keys t)))
    (should (or (stringp r) (vectorp r)))
    (should (= (length r) 0))))

(ert-deftest m3-recent-keys/returns-correct-type ()
  ;; The result is either a unibyte string (all events are simple
  ;; chars) or a vector (some events are not chars).  Empty case
  ;; collapses to a string per make_event_array_from_vector.
  (let ((r (recent-keys)))
    (should (or (stringp r) (vectorp r)))))

(provide 'ertest-recent-keys)

;;; ertest-recent-keys.el ends here
