;;; test-this-command-keys.el --- M5 SRFI-64 suite for (emacs this-command-keys)

;; Same coverage as ertest-this-command-keys.el, transcribed for the
;; test-framework.el / SRFI-64 harness.  Keep in sync.

(test-begin "this-command-keys")

;;;; Empty-state readers

(let ((r (this-command-keys)))
  (test-assert "tck/shape"           (or (stringp r) (vectorp r)))
  (test-equal  "tck/length"          0 (length r)))

(let ((r (this-command-keys-vector)))
  (test-assert "tckv/shape"          (or (stringp r) (vectorp r)))
  (test-equal  "tckv/length"         0 (length r)))

(let ((r (this-single-command-keys)))
  (test-assert "tsck/shape"          (or (stringp r) (vectorp r)))
  (test-equal  "tsck/length"         0 (length r)))

(let ((r (this-single-command-raw-keys)))
  (test-assert "tscrk/shape"         (or (stringp r) (vectorp r)))
  (test-equal  "tscrk/length"        0 (length r)))

;;;; Clear paths

(test-eq    "clear/with-keep-record/return" nil (clear-this-command-keys t))
(test-equal "clear/with-keep-record/empties-tck"
            0 (length (this-command-keys)))

(test-eq    "clear/no-arg/return" nil (clear-this-command-keys))
(test-equal "clear/no-arg/empties-tck"
            0 (length (this-command-keys)))

(clear-this-command-keys)
(test-equal "clear/no-arg/empties-recent-keys"
            0 (length (recent-keys)))

;;;; this-single-command-keys agrees with this-command-keys at zero offset

(test-equal "tsck-matches-tck-at-zero-offset"
            (this-command-keys)
            (this-single-command-keys))

;;;; Internal accessors are present and consistent

(test-assert "accessors/exist--this-command-keys"        (fboundp '--this-command-keys))
(test-assert "accessors/exist--this-command-key-count"   (fboundp '--this-command-key-count))
(test-assert "accessors/exist--raw-keybuf"               (fboundp '--raw-keybuf))
(test-assert "accessors/exist--raw-keybuf-count"         (fboundp '--raw-keybuf-count))
(test-assert "accessors/exist--this-single-command-key-start"
             (fboundp '--this-single-command-key-start))

;; The vector accessors return Guile pseudovectors that elisp vectorp
;; doesn't recognize; only the integer counters round-trip cleanly.
(test-assert "accessors/--this-command-key-count-intp" (integerp (--this-command-key-count)))
(test-assert "accessors/--raw-keybuf-count-intp" (integerp (--raw-keybuf-count)))
(test-assert "accessors/--this-single-command-key-start-intp"
             (integerp (--this-single-command-key-start)))

(test-end)
