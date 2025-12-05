;;; test-manual-fontification.el --- Test text properties like font-lock would use them

(message "\n=== Manual Fontification Test ===\n")

(message "Simulating how font-lock applies faces...")

(with-temp-buffer
  (insert "(defun my-test (arg) \"documentation\" 42)")

  (message "Buffer: %S" (buffer-string))

  ;; Manually apply faces like font-lock would
  (message "\nApplying faces manually:")

  ;; 'defun' keyword at pos 2-6
  (put-text-property 2 7 'face 'font-lock-keyword-face)
  (message "  Applied font-lock-keyword-face to 'defun'")

  ;; 'my-test' function name at pos 8-14
  (put-text-property 8 15 'face 'font-lock-function-name-face)
  (message "  Applied font-lock-function-name-face to 'my-test'")

  ;; 'arg' variable at pos 17-19
  (put-text-property 17 20 'face 'font-lock-variable-name-face)
  (message "  Applied font-lock-variable-name-face to 'arg'")

  ;; "documentation" string at pos 22-36
  (put-text-property 22 37 'face 'font-lock-string-face)
  (message "  Applied font-lock-string-face to string")

  ;; '42' number at pos 38-39
  (put-text-property 38 40 'face 'font-lock-constant-face)
  (message "  Applied font-lock-constant-face to '42'")

  (message "\nVerifying properties were applied:")
  (let ((tests '((2 "defun" font-lock-keyword-face)
                 (8 "my-test" font-lock-function-name-face)
                 (17 "arg" font-lock-variable-name-face)
                 (22 "doc" font-lock-string-face)
                 (38 "42" font-lock-constant-face))))
    (dolist (test tests)
      (let* ((pos (nth 0 test))
             (name (nth 1 test))
             (expected-face (nth 2 test))
             (actual-face (get-text-property pos 'face)))
        (message "  Pos %d (%s): expected=%S actual=%S %s"
                 pos name expected-face actual-face
                 (if (eq expected-face actual-face) "✓" "✗")))))

  (message "\nSearching for specific faces:")

  ;; Test text-property-any with font-lock faces
  (let ((faces '(font-lock-keyword-face
                 font-lock-function-name-face
                 font-lock-variable-name-face
                 font-lock-string-face
                 font-lock-constant-face)))
    (dolist (face faces)
      (let ((pos (text-property-any 1 (point-max) 'face face (current-buffer))))
        (message "  %s: %s" face (if pos (format "found at %d" pos) "NOT FOUND")))))

  (message "\nTesting property removal:")
  (remove-text-properties 8 15 '(face))
  (message "  Removed face from 'my-test'")
  (message "  Face at pos 8 now: %S" (get-text-property 8 'face))

  (message "\nTesting property replacement:")
  (set-text-properties 2 7 '(face font-lock-comment-face))
  (message "  Changed 'defun' to font-lock-comment-face")
  (message "  Face at pos 2 now: %S" (get-text-property 2 'face)))

(message "\n=== Manual Fontification Test Complete ===")
