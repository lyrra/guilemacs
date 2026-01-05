;;; test-scheme-storage.el --- Test that properties are stored in Scheme intervals
;;;
;;; These tests verify that text properties are stored in Scheme's interval
;;; data structure rather than C intervals. This is critical for guilemacs
;;; where text properties are managed by Scheme code.

(test-begin "scheme-storage")

;; Test 1: Basic storage and retrieval
(with-temp-buffer
  (insert "Hello World")
  (add-text-properties 1 6 '(face bold))
  (test-eq "scheme-storage/basic-add" 'bold (get-text-property 1 'face))
  (test-nil "scheme-storage/outside-range" (get-text-property 7 'face)))

;; Test 2: put-text-property stores correctly
(with-temp-buffer
  (insert "Hello World")
  (put-text-property 1 6 'test-prop 'test-value)
  (test-eq "scheme-storage/put-stores" 'test-value (get-text-property 1 'test-prop)))

;; Test 3: Multiple properties on same region
(with-temp-buffer
  (insert "Hello World")
  (add-text-properties 1 6 '(face bold mouse-face highlight help-echo "hi"))
  (test-eq "scheme-storage/multi-face" 'bold (get-text-property 1 'face))
  (test-eq "scheme-storage/multi-mouse" 'highlight (get-text-property 1 'mouse-face))
  (test-equal "scheme-storage/multi-help" "hi" (get-text-property 1 'help-echo)))

;; Test 4: Properties survive buffer modifications (insert before)
(with-temp-buffer
  (insert "Hello World")
  (put-text-property 7 12 'test-prop 'test-value)
  (goto-char 1)
  (insert "XXX")
  ;; Property should shift from 7 to 10 (7 + 3)
  (test-eq "scheme-storage/shift-after-insert" 'test-value (get-text-property 10 'test-prop)))

;; Test 5: Properties survive buffer modifications (insert inside)
(with-temp-buffer
  (insert "Hello World")
  (put-text-property 1 12 'test-prop 'test-value)
  (goto-char 6)
  (insert " there")
  ;; Property should still cover the whole range
  (test-eq "scheme-storage/insert-inside-start" 'test-value (get-text-property 1 'test-prop))
  (test-eq "scheme-storage/insert-inside-end" 'test-value (get-text-property 17 'test-prop)))

;; Test 6: Properties survive buffer modifications (delete before)
(with-temp-buffer
  (insert "XXXHello World")
  (put-text-property 4 9 'test-prop 'test-value)  ; "Hello"
  (goto-char 1)
  (delete-char 3)
  ;; Property should shift from 4-9 to 1-6
  (test-eq "scheme-storage/shift-after-delete" 'test-value (get-text-property 1 'test-prop))
  (test-nil "scheme-storage/after-shifted-range" (get-text-property 7 'test-prop)))

;; Test 7: Propertized string insertion preserves properties
(with-temp-buffer
  (let ((propertized (propertize "Hello" 'face 'bold)))
    (insert propertized)
    (test-eq "scheme-storage/propertize-insert" 'bold (get-text-property 1 'face))))

;; Test 8: buffer-substring preserves properties
(with-temp-buffer
  (insert "Hello World")
  (put-text-property 1 6 'myface 'mybold)
  (let ((substr (buffer-substring 1 6)))
    (test-eq "scheme-storage/substring-props" 'mybold (get-text-property 0 'myface substr))))

;; Test 9: buffer-substring-no-properties strips properties
(with-temp-buffer
  (insert "Hello World")
  (put-text-property 1 6 'myface 'mybold)
  (let ((substr (buffer-substring-no-properties 1 6)))
    (test-nil "scheme-storage/substring-no-props" (get-text-property 0 'myface substr))))

;; Test 10: Overlapping property regions merge correctly
(with-temp-buffer
  (insert "ABCDEFGHIJ")
  (put-text-property 1 4 'prop1 'val1)  ; ABC
  (put-text-property 3 7 'prop2 'val2)  ; CDEF
  ;; Position 1-2: only prop1
  (test-eq "scheme-storage/overlap-left-1" 'val1 (get-text-property 1 'prop1))
  (test-nil "scheme-storage/overlap-left-2" (get-text-property 1 'prop2))
  ;; Position 3: both properties
  (test-eq "scheme-storage/overlap-both-1" 'val1 (get-text-property 3 'prop1))
  (test-eq "scheme-storage/overlap-both-2" 'val2 (get-text-property 3 'prop2))
  ;; Position 5: only prop2
  (test-nil "scheme-storage/overlap-right-1" (get-text-property 5 'prop1))
  (test-eq "scheme-storage/overlap-right-2" 'val2 (get-text-property 5 'prop2)))

;; Test 11: remove-text-properties works
(with-temp-buffer
  (insert "Hello World")
  (put-text-property 1 6 'test-prop 'test-value)
  (test-eq "scheme-storage/before-remove" 'test-value (get-text-property 1 'test-prop))
  (remove-text-properties 1 6 '(test-prop nil))
  (test-nil "scheme-storage/after-remove" (get-text-property 1 'test-prop)))

;; Test 12: set-text-properties replaces all
(with-temp-buffer
  (insert "Hello World")
  (put-text-property 1 6 'old-prop 'old-value)
  (set-text-properties 1 6 '(new-prop new-value))
  (test-nil "scheme-storage/set-removes-old" (get-text-property 1 'old-prop))
  (test-eq "scheme-storage/set-adds-new" 'new-value (get-text-property 1 'new-prop)))

;; Test 13: next-property-change works with Scheme intervals
(with-temp-buffer
  (insert "Hello World")
  (put-text-property 1 6 'test-prop 'test-value)
  (let ((next-change (next-property-change 1)))
    (test-eq "scheme-storage/next-prop-change" 6 next-change)))

;; Test 14: Properties on different buffers are independent
(let ((buf1 (generate-new-buffer "*test1*"))
      (buf2 (generate-new-buffer "*test2*")))
  (unwind-protect
      (progn
        (with-current-buffer buf1
          (insert "Buffer 1")
          (put-text-property 1 9 'prop 'val1))
        (with-current-buffer buf2
          (insert "Buffer 2")
          (put-text-property 1 9 'prop 'val2))
        (test-eq "scheme-storage/buf1-prop" 'val1
                 (with-current-buffer buf1 (get-text-property 1 'prop)))
        (test-eq "scheme-storage/buf2-prop" 'val2
                 (with-current-buffer buf2 (get-text-property 1 'prop))))
    (kill-buffer buf1)
    (kill-buffer buf2)))

;; Test 15: text-properties-at returns full plist
(with-temp-buffer
  (insert "Hello")
  (add-text-properties 1 6 '(face bold fontified t))
  (let ((props (text-properties-at 1)))
    (test-eq "scheme-storage/plist-face" 'bold (plist-get props 'face))
    (test-eq "scheme-storage/plist-fontified" t (plist-get props 'fontified))))

;; Test 16: Boundary positions work correctly
(with-temp-buffer
  (insert "ABCDE")
  (put-text-property 2 4 'test 'value)  ; "BC"
  (test-nil "scheme-storage/boundary-before" (get-text-property 1 'test))  ; "A"
  (test-eq "scheme-storage/boundary-start" 'value (get-text-property 2 'test))  ; "B"
  (test-eq "scheme-storage/boundary-inside" 'value (get-text-property 3 'test))  ; "C"
  (test-nil "scheme-storage/boundary-end" (get-text-property 4 'test))  ; "D"
  (test-nil "scheme-storage/boundary-after" (get-text-property 5 'test)))  ; "E"

(test-end)
