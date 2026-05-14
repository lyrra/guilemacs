;;; ertest-this-command-keys.el --- M5 ERT suite for (emacs this-command-keys)

;; M5 gating tests.  Exercises the five user-facing DEFUNs now ported
;; to mod/emacs/this-command-keys.scm.  Batch mode has no interactive
;; key activity so the vectors stay empty unless we drive them via
;; the C-side accessor subrs.
;;
;; See docs/keyboard.org §"M5 — This-command-keys & predicates".

(require 'ert)

;;;; Empty-state readers

(ert-deftest m5-this-command-keys/empty-shape ()
  (let ((r (this-command-keys)))
    (should (or (stringp r) (vectorp r)))
    (should (= (length r) 0))))

(ert-deftest m5-this-command-keys-vector/empty-shape ()
  (let ((r (this-command-keys-vector)))
    (should (or (stringp r) (vectorp r)))
    (should (= (length r) 0))))

(ert-deftest m5-this-single-command-keys/empty-shape ()
  (let ((r (this-single-command-keys)))
    (should (or (stringp r) (vectorp r)))
    (should (= (length r) 0))))

(ert-deftest m5-this-single-command-raw-keys/empty-shape ()
  (let ((r (this-single-command-raw-keys)))
    (should (or (stringp r) (vectorp r)))
    (should (= (length r) 0))))

;;;; Clear is a no-op on empty state but returns nil

(ert-deftest m5-clear-this-command-keys/empty-with-keep-record ()
  (should (eq (clear-this-command-keys t) nil))
  (should (= (length (this-command-keys)) 0)))

(ert-deftest m5-clear-this-command-keys/empty-no-arg ()
  (should (eq (clear-this-command-keys) nil))
  (should (= (length (this-command-keys)) 0)))

(ert-deftest m5-clear-this-command-keys/clears-recent-keys-when-no-keep-record ()
  ;; Without keep-record, the recent-keys ring should also be cleared
  ;; (recent-keys returns 0 elements after the clear).  This is the
  ;; M3-state cross-interaction baked into Fclear_this_command_keys.
  (clear-this-command-keys)
  (let ((rk (recent-keys)))
    (should (= (length rk) 0))))

;;;; Single-command-keys reads the prefix slice

(ert-deftest m5-this-single-command-keys/respects-prefix-start ()
  ;; --this-single-command-key-start is read from C state; both
  ;; this-command-keys and this-single-command-keys agree at the
  ;; default zero-offset empty state.
  (should (equal (this-single-command-keys)
                 (this-command-keys))))

;;;; Internal accessors are present and consistent

(ert-deftest m5-accessors/exist ()
  (should (fboundp '--this-command-keys))
  (should (fboundp '--this-command-key-count))
  (should (fboundp '--raw-keybuf))
  (should (fboundp '--raw-keybuf-count))
  (should (fboundp '--this-single-command-key-start)))

(ert-deftest m5-accessors/scalars-are-integers ()
  ;; The vector accessors return Guile-side pseudovectors that elisp
  ;; vectorp doesn't recognize; testing their shape from elisp is
  ;; meaningless.  We check just the integer counters, which DO round-trip
  ;; cleanly across the boundary.
  (should (integerp (--this-command-key-count)))
  (should (integerp (--raw-keybuf-count)))
  (should (integerp (--this-single-command-key-start))))

(provide 'ertest-this-command-keys)

;;; ertest-this-command-keys.el ends here
