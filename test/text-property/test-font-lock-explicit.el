;;; test-font-lock-explicit.el --- Test with explicit font-lock enable

(message "\n=== Font-Lock Explicit Enable Test ===\n")

(with-temp-buffer
  (insert "(defun test () \"doc\" 42)")
  (emacs-lisp-mode)

  (message "Before font-lock-mode:")
  (message "  Font-lock-mode: %S" font-lock-mode)
  (message "  Font-lock-keywords count: %S" (length font-lock-keywords))

  ;; Explicitly turn on font-lock-mode
  (font-lock-mode 1)

  (message "\nAfter (font-lock-mode 1):")
  (message "  Font-lock-mode: %S" font-lock-mode)
  (message "  Font-lock-keywords count: %S" (length font-lock-keywords))

  ;; Now fontify
  (font-lock-fontify-region (point-min) (point-max))

  (message "\nAfter font-lock-fontify-region:")
  (message "  Checking properties:")

  (dotimes (i (buffer-size))
    (let* ((pos (1+ i))
           (char (buffer-substring pos (1+ pos)))
           (face (get-text-property pos 'face)))
      (when face
        (message "    Pos %d '%s': face=%S" pos char face)))))

(message "\n=== Test Complete ===")
