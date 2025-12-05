;;; test-font-lock.el --- Test font-lock with text properties

(message "\n=== Font-Lock Test ===\n")

;; Test 1: Basic elisp mode font-lock
(message "Test 1: Font-lock in elisp-mode")
(with-temp-buffer
  (emacs-lisp-mode)
  (insert "(defun my-function (arg)
  \"A test function.\"
  (let ((x 42))
    (message \"x is %d\" x)))")

  (message "Buffer content inserted, applying font-lock...")
  (font-lock-ensure)

  (message "After font-lock-ensure:")
  (message "  Buffer size: %d" (buffer-size))

  ;; Check properties at various positions
  (message "\nProperty analysis:")

  ;; Position 1: '(' - should have some face
  (message "  Pos 1 '(': face=%S" (get-text-property 1 'face))

  ;; Position 2: 'd' in 'defun' - should be font-lock-keyword-face
  (message "  Pos 2 'd' (defun): face=%S" (get-text-property 2 'face))

  ;; Position 8: 'm' in 'my-function' - should be font-lock-function-name-face
  (message "  Pos 8 'm' (my-function): face=%S" (get-text-property 8 'face))

  ;; Position 20: 'a' in 'arg' - should be font-lock-variable-name-face
  (message "  Pos 20 'a' (arg): face=%S" (get-text-property 20 'face))

  ;; Position 26: '\"' - string quote
  (let ((pos (string-match "\"" (buffer-string))))
    (when pos
      (setq pos (1+ pos))
      (message "  Pos %d '\"' (string): face=%S" pos (get-text-property pos 'face))))

  ;; Count how many characters have face properties
  (let ((count 0))
    (dotimes (i (buffer-size))
      (when (get-text-property (1+ i) 'face)
        (setq count (1+ count))))
    (message "\nTotal characters with face properties: %d/%d (%.1f%%)"
             count (buffer-size) (* 100.0 (/ count (float (buffer-size)))))))

;; Test 2: Check if font-lock uses text properties correctly
(message "\n\nTest 2: Font-lock property modification")
(with-temp-buffer
  (emacs-lisp-mode)
  (insert "(setq x 10)")
  (font-lock-ensure)

  (message "Initial state:")
  (message "  Pos 2 's' (setq): face=%S" (get-text-property 2 'face))

  ;; Modify buffer
  (goto-char (point-max))
  (insert "\n(setq y 20)")
  (font-lock-ensure)

  (message "After adding second line:")
  (message "  First setq face: %S" (get-text-property 2 'face))
  (message "  Second setq face: %S" (get-text-property 14 'face)))

;; Test 3: Test text-property-any with font-lock
(message "\n\nTest 3: Searching for font-lock faces")
(with-temp-buffer
  (emacs-lisp-mode)
  (insert "(defun test () (let ((x 1)) x))")
  (font-lock-ensure)

  (message "Searching for font-lock-keyword-face:")
  (let ((pos 1)
        (found 0))
    (while (setq pos (text-property-any pos (point-max) 'face 'font-lock-keyword-face (current-buffer)))
      (setq found (1+ found))
      (message "  Found at pos %d: %S" pos (buffer-substring pos (min (+ pos 6) (point-max))))
      (setq pos (1+ pos)))
    (message "Total keyword faces found: %d" found)))

(message "\n=== Font-Lock Test Complete ===")
