;;; test-buffer-intervals-debug.el --- Debug buffer intervals

(message "\n=== Buffer Intervals Debug ===\n")

(with-temp-buffer
  (insert "abcdefghij")

  (message "Step 1: Add property")
  (put-text-property 3 7 'face 'bold)
  (message "  face at 5: %S" (get-text-property 5 'face))

  (message "\nStep 2: Remove property")
  (let ((result (remove-text-properties 3 7 '(face))))
    (message "  remove returned: %S" result)
    (message "  face at 5 after remove: %S" (get-text-property 5 'face)))

  (message "\nStep 3: Add again and try set")
  (put-text-property 3 7 'face 'bold)
  (message "  face at 5: %S" (get-text-property 5 'face))

  (set-text-properties 3 7 '(underline t))
  (message "  After set, face at 5: %S" (get-text-property 5 'face))
  (message "  After set, underline at 5: %S" (get-text-property 5 'underline)))

(message "\n=== Test Complete ===")
