;;; test-remove-set-debug.el --- Debug remove and set functions

(message "\n=== Remove/Set Debug Test ===\n")

(with-temp-buffer
  (insert "test text here")

  (message "Test 1: remove-text-properties")
  (put-text-property 1 5 'face 'bold)
  (put-text-property 1 5 'invisible t)
  (message "  Before: face=%S invisible=%S"
           (get-text-property 1 'face)
           (get-text-property 1 'invisible))

  (let ((result (remove-text-properties 1 5 '(invisible))))
    (message "  remove-text-properties returned: %S" result))

  (message "  After: face=%S invisible=%S"
           (get-text-property 1 'face)
           (get-text-property 1 'invisible))

  (message "\nTest 2: set-text-properties")
  (message "  Before: face=%S invisible=%S"
           (get-text-property 1 'face)
           (get-text-property 1 'invisible))

  (set-text-properties 1 5 '(underline t))
  (message "  After set-text-properties: face=%S underline=%S"
           (get-text-property 1 'face)
           (get-text-property 1 'underline)))

(message "\n=== Test Complete ===")
