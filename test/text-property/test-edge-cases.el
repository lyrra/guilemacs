;;; test-edge-cases.el --- Test edge cases and corner scenarios

(test-begin "edge-cases")

;; Test 1: Empty buffer
(with-temp-buffer
  (test-nil "edge-cases/empty-buffer-get-property"
            (get-text-property 1 'face)))

;; Test 2: Empty range
(with-temp-buffer
  (insert "test")
  (put-text-property 3 3 'face 'bold)
  (test-nil "edge-cases/empty-range-no-effect" (get-text-property 3 'face)))

;; Test 3: Adjacent intervals
(with-temp-buffer
  (insert "0123456789")
  (put-text-property 1 5 'face 'bold)
  (put-text-property 5 10 'face 'italic)
  (test-eq "edge-cases/adjacent-first" 'bold (get-text-property 4 'face))
  (test-eq "edge-cases/adjacent-second" 'italic (get-text-property 5 'face)))

;; Test 4: Overlapping properties
(with-temp-buffer
  (insert "0123456789")
  (put-text-property 1 7 'face 'bold)
  (put-text-property 4 10 'underline t)
  (test-eq "edge-cases/overlap-both-present-face" 'bold (get-text-property 5 'face))
  (test-eq "edge-cases/overlap-both-present-underline" t (get-text-property 5 'underline)))

;; Test 5: Multiple properties on same range
(with-temp-buffer
  (insert "test")
  (add-text-properties 1 5 '(face bold invisible t category special mouse-face highlight))
  (test-eq "edge-cases/multiple-face" 'bold (get-text-property 2 'face))
  (test-eq "edge-cases/multiple-invisible" t (get-text-property 2 'invisible))
  (test-eq "edge-cases/multiple-category" 'special (get-text-property 2 'category))
  (test-eq "edge-cases/multiple-mouse-face" 'highlight (get-text-property 2 'mouse-face)))

;; Test 6: Property at buffer boundaries
(with-temp-buffer
  (insert "test")
  (put-text-property 1 (point-max) 'face 'bold)
  (test-eq "edge-cases/boundary-start" 'bold (get-text-property 1 'face))
  (test-eq "edge-cases/boundary-end" 'bold (get-text-property (1- (point-max)) 'face)))

;; Test 7: Propertize with empty string
(let ((str (propertize "" 'face 'bold)))
  (test-equal "edge-cases/propertize-empty-length" 0 (length str)))

;; Test 8: Remove non-existent property
(with-temp-buffer
  (insert "test")
  (put-text-property 1 5 'face 'bold)
  (remove-text-properties 1 5 '(nonexistent))
  (test-eq "edge-cases/remove-nonexistent-preserves-existing" 'bold (get-text-property 2 'face)))

;; Test 9: Set properties to nil (clear)
(with-temp-buffer
  (insert "test")
  (put-text-property 1 5 'face 'bold)
  (set-text-properties 1 5 nil)
  (test-nil "edge-cases/set-nil-clears-properties" (get-text-property 2 'face)))

;; Test 10: Sequential property additions
(with-temp-buffer
  (insert "test")
  (put-text-property 1 5 'prop1 'val1)
  (put-text-property 1 5 'prop2 'val2)
  (put-text-property 1 5 'prop3 'val3)
  (test-eq "edge-cases/sequential-prop1" 'val1 (get-text-property 2 'prop1))
  (test-eq "edge-cases/sequential-prop2" 'val2 (get-text-property 2 'prop2))
  (test-eq "edge-cases/sequential-prop3" 'val3 (get-text-property 2 'prop3)))

(test-end)
