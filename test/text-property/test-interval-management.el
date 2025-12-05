;;; test-interval-management.el --- Test interval splitting, merging, coalescing

(load-file "test/text-property/test-framework.el")

(test-begin "interval-management")

;; Test 1: Adjacent intervals with same properties - do they merge?
(with-temp-buffer
  (insert "0123456789")
  (put-text-property 1 5 'face 'bold)
  (put-text-property 5 10 'face 'bold)
  ;; Check that both regions have the property
  (test-eq "interval-management/adjacent-same-first-region"
           'bold
           (get-text-property 3 'face))
  (test-eq "interval-management/adjacent-same-boundary"
           'bold
           (get-text-property 5 'face))
  (test-eq "interval-management/adjacent-same-second-region"
           'bold
           (get-text-property 7 'face)))

;; Test 2: Adjacent intervals with different properties - separate intervals
(with-temp-buffer
  (insert "0123456789")
  (put-text-property 1 5 'face 'bold)
  (put-text-property 5 10 'face 'italic)
  (test-eq "interval-management/adjacent-different-first"
           'bold
           (get-text-property 4 'face))
  (test-eq "interval-management/adjacent-different-boundary"
           'italic
           (get-text-property 5 'face))
  (test-eq "interval-management/adjacent-different-second"
           'italic
           (get-text-property 7 'face)))

;; Test 3: Splitting an interval - set property in middle
(with-temp-buffer
  (insert "0123456789")
  (put-text-property 1 10 'face 'bold)
  (put-text-property 4 7 'face 'italic)
  (test-eq "interval-management/split-before"
           'bold
           (get-text-property 2 'face))
  (test-eq "interval-management/split-middle"
           'italic
           (get-text-property 5 'face))
  (test-eq "interval-management/split-after"
           'bold
           (get-text-property 8 'face)))

;; Test 4: Removing property from middle - creates split
(with-temp-buffer
  (insert "0123456789")
  (put-text-property 1 10 'face 'bold)
  (remove-text-properties 4 7 '(face))
  (test-eq "interval-management/remove-middle-before"
           'bold
           (get-text-property 2 'face))
  (test-nil "interval-management/remove-middle-gap"
            (get-text-property 5 'face))
  (test-eq "interval-management/remove-middle-after"
           'bold
           (get-text-property 8 'face)))

;; Test 5: Multiple properties - partial removal
(with-temp-buffer
  (insert "0123456789")
  (put-text-property 1 10 'face 'bold)
  (put-text-property 1 10 'invisible t)
  (remove-text-properties 4 7 '(invisible))
  (test-eq "interval-management/multi-before-face"
           'bold
           (get-text-property 2 'face))
  (test-eq "interval-management/multi-before-invisible"
           t
           (get-text-property 2 'invisible))
  (test-eq "interval-management/multi-middle-face"
           'bold
           (get-text-property 5 'face))
  (test-nil "interval-management/multi-middle-invisible"
            (get-text-property 5 'invisible))
  (test-eq "interval-management/multi-after-face"
           'bold
           (get-text-property 8 'face))
  (test-eq "interval-management/multi-after-invisible"
           t
           (get-text-property 8 'invisible)))

;; Test 6: Overlapping property sets - FIXED!
(with-temp-buffer
  (insert "0123456789ABCDEF")
  (put-text-property 1 10 'face 'bold)
  (put-text-property 5 15 'face 'italic)
  (test-eq "interval-management/overlap-first-only"
           'bold
           (get-text-property 3 'face))
  (test-eq "interval-management/overlap-second-overwrites"
           'italic
           (get-text-property 7 'face))
  (test-eq "interval-management/overlap-second-only"
           'italic
           (get-text-property 12 'face)))

;; Test 7: Three-way overlap - FIXED!
(with-temp-buffer
  (insert "0123456789ABCDEF")
  (put-text-property 1 10 'face 'bold)
  (put-text-property 5 15 'face 'italic)
  (put-text-property 3 12 'face 'underline)
  (test-eq "interval-management/3way-first-preserved"
           'bold
           (get-text-property 2 'face))
  (test-eq "interval-management/3way-middle-last-wins"
           'underline
           (get-text-property 7 'face))
  (test-eq "interval-management/3way-last-region"
           'italic
           (get-text-property 13 'face)))

;; Test 8: Add vs Set - overlapping
(with-temp-buffer
  (insert "0123456789")
  (put-text-property 1 10 'face 'bold)
  (add-text-properties 5 10 '(invisible t))
  (test-eq "interval-management/add-preserves-face-before"
           'bold
           (get-text-property 3 'face))
  (test-nil "interval-management/add-no-invisible-before"
            (get-text-property 3 'invisible))
  (test-eq "interval-management/add-preserves-face-after"
           'bold
           (get-text-property 7 'face))
  (test-eq "interval-management/add-adds-invisible-after"
           t
           (get-text-property 7 'invisible)))

;; Test 9: Set properties to nil - clears region
(with-temp-buffer
  (insert "0123456789")
  (put-text-property 1 10 'face 'bold)
  (set-text-properties 4 7 nil)
  (test-eq "interval-management/set-nil-before"
           'bold
           (get-text-property 2 'face))
  (test-nil "interval-management/set-nil-middle"
            (get-text-property 5 'face))
  (test-eq "interval-management/set-nil-after"
           'bold
           (get-text-property 8 'face)))

;; Test 10: Exact boundary behavior - start position
(with-temp-buffer
  (insert "0123456789")
  (put-text-property 5 10 'face 'bold)
  (test-nil "interval-management/boundary-before-start"
            (get-text-property 4 'face))
  (test-eq "interval-management/boundary-at-start"
           'bold
           (get-text-property 5 'face))
  (test-eq "interval-management/boundary-after-start"
           'bold
           (get-text-property 6 'face)))

;; Test 11: Exact boundary behavior - end position
(with-temp-buffer
  (insert "0123456789")
  (put-text-property 1 5 'face 'bold)
  (test-eq "interval-management/boundary-before-end"
           'bold
           (get-text-property 4 'face))
  (test-nil "interval-management/boundary-at-end"
            (get-text-property 5 'face))
  (test-nil "interval-management/boundary-after-end"
            (get-text-property 6 'face)))

;; Test 12: Zero-width interval (start == end)
(with-temp-buffer
  (insert "test")
  (put-text-property 3 3 'face 'bold)
  (test-nil "interval-management/zero-width-before"
            (get-text-property 2 'face))
  (test-nil "interval-management/zero-width-at"
            (get-text-property 3 'face))
  (test-nil "interval-management/zero-width-after"
            (get-text-property 4 'face)))

;; Test 13: Consecutive set operations on same range
(with-temp-buffer
  (insert "test")
  (put-text-property 1 5 'face 'bold)
  (put-text-property 1 5 'face 'italic)
  (put-text-property 1 5 'face 'underline)
  (test-eq "interval-management/consecutive-sets-last-wins"
           'underline
           (get-text-property 2 'face)))

;; Test 14: Property value comparison - symbols vs strings
(with-temp-buffer
  (insert "test")
  (put-text-property 1 5 'face 'bold)
  (let ((pos (text-property-any 1 5 'face 'bold (current-buffer))))
    (test-not-nil "interval-management/symbol-search-finds"
                  pos)))

;; Test 15: Multiple properties - order independence
(with-temp-buffer
  (insert "test")
  (add-text-properties 1 5 '(face bold invisible t category special))
  (let ((props (text-properties-at 2)))
    (test-eq "interval-management/multi-order-face"
             'bold
             (plist-get props 'face))
    (test-eq "interval-management/multi-order-invisible"
             t
             (plist-get props 'invisible))
    (test-eq "interval-management/multi-order-category"
             'special
             (plist-get props 'category))))

(test-end)
