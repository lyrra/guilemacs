;;; ertest-consolidation.el --- ERT suite for the consolidation milestone

;; Consolidation milestone (between M5 and M6).  Covers two DEFUNs
;; that move user-facing logic into Scheme:
;;
;;   - top-level                  → (emacs recursive-edit)
;;   - set--this-command-keys     → (emacs this-command-keys)
;;
;; The other un-ported keyboard.c DEFUNs (current-idle-time,
;; current-input-mode, input-pending-p, discard-input, plus the M2/M3
;; deferrals) were audited and judged C-natural — see
;; docs/keyboard.org §"Consolidation".

(require 'ert)

;;;; top-level

(ert-deftest cons-top-level/throws-top-level-with-nil ()
  (let ((caught 'unset))
    (catch 'top-level
      (setq caught 'inside-catch)
      (top-level)
      (setq caught 'unreached-after-top-level))
    (should (eq caught 'inside-catch))))

(ert-deftest cons-top-level/returns-via-throw ()
  (should (eq nil (catch 'top-level (top-level) 'unreached))))

;;;; set--this-command-keys

(ert-deftest cons-set-this-command-keys/empty-string ()
  (clear-this-command-keys t)
  (set--this-command-keys "")
  (should (= 0 (--this-command-key-count))))

(ert-deftest cons-set-this-command-keys/ascii-roundtrip ()
  (clear-this-command-keys t)
  (set--this-command-keys "foo")
  (should (= 3 (--this-command-key-count)))
  ;; The vector contains exact ASCII codes.
  (let ((v (--this-command-keys)))
    (should (= ?f (aref v 0)))
    (should (= ?o (aref v 1)))
    (should (= ?o (aref v 2)))))

(ert-deftest cons-set-this-command-keys/m-x-kludge ()
  ;; A leading 248 (\370 = Meta-x in the novice.el form) gets folded
  ;; to (logior ?x meta-modifier) = 134217848 (= 0x08000078) so the
  ;; key sequence inserted matches what M-x actually produces.
  (clear-this-command-keys t)
  (set--this-command-keys "\xf8")
  (should (= 1 (--this-command-key-count)))
  (should (= (logior ?x #x08000000) (aref (--this-command-keys) 0))))

(ert-deftest cons-set-this-command-keys/m-x-kludge-only-on-first ()
  ;; The kludge applies only to position 0.  A trailing 248 is left as-is.
  ;; Use "x\xf8": position 0 is 'x' (not the kludge); position 1 is 248
  ;; and stays as 248.
  (clear-this-command-keys t)
  (set--this-command-keys "x\xf8")
  (should (= 2 (--this-command-key-count)))
  (let ((v (--this-command-keys)))
    (should (= ?x (aref v 0)))
    (should (= 248 (aref v 1)))))

(ert-deftest cons-set-this-command-keys/resets-key-counters ()
  ;; Both this_command_key_count and this_single_command_key_start
  ;; reset to 0 at the start.
  (clear-this-command-keys t)
  (set--this-command-keys "abc")
  (should (= 3 (--this-command-key-count)))
  (should (= 0 (--this-single-command-key-start)))
  (set--this-command-keys "d")
  (should (= 1 (--this-command-key-count)))
  (should (= 0 (--this-single-command-key-start))))

(ert-deftest cons-set-this-command-keys/rejects-non-string ()
  (should-error (set--this-command-keys 42)
                :type 'wrong-type-argument)
  (should-error (set--this-command-keys '(?a ?b))
                :type 'wrong-type-argument))

(provide 'ertest-consolidation)

;;; ertest-consolidation.el ends here
