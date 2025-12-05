;;; test-font-lock-debug.el --- Debug font-lock behavior

(message "\n=== Font-Lock Debug ===\n")

(with-temp-buffer
  (emacs-lisp-mode)
  (insert "(defun test () \"doc\" 42)")

  (message "Before font-lock-ensure:")
  (message "  Major mode: %S" major-mode)
  (message "  Font-lock-mode: %S" font-lock-mode)
  (message "  Font-lock-keywords: %S" (length font-lock-keywords))

  (font-lock-ensure)

  (message "\nAfter font-lock-ensure:")
  (message "  Checking all positions:")

  (dotimes (i (buffer-size))
    (let* ((pos (1+ i))
           (char (buffer-substring pos (1+ pos)))
           (face (get-text-property pos 'face))
           (props (text-properties-at pos)))
      (when (or face props)
        (message "    Pos %d '%s': face=%S props=%S" pos char face props))))

  (message "\nChecking specific keywords:")
  (let ((keywords '("defun" "test" "doc" "42")))
    (dolist (kw keywords)
      (let ((pos (string-match kw (buffer-string))))
        (when pos
          (setq pos (1+ pos))
          (message "  '%s' at pos %d: face=%S" kw pos (get-text-property pos 'face)))))))

(message "\n=== Font-Lock Debug Complete ===")
