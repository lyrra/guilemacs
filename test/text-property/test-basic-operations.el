;;; test-basic-operations.el --- Test basic text property operations

(test-begin "basic-operations")

;; Test 1: put-text-property
(with-temp-buffer
  (insert "abcdefghij")
  (put-text-property 3 7 'face 'bold)
  (test-eq "put-text-property/face-applied" 'bold (get-text-property 5 'face))
  (test-nil "put-text-property/before-range" (get-text-property 1 'face))
  (test-nil "put-text-property/after-range" (get-text-property 8 'face)))

;; Test 2: get-text-property
(with-temp-buffer
  (insert "test")
  (put-text-property 1 5 'category 'special)
  (test-eq "get-text-property/retrieves-value" 'special (get-text-property 2 'category))
  (test-nil "get-text-property/nonexistent-property" (get-text-property 2 'nonexistent)))

;; Test 3: text-properties-at
(with-temp-buffer
  (insert "test")
  (put-text-property 1 5 'face 'bold)
  (put-text-property 1 5 'invisible t)
  (let ((props (text-properties-at 2)))
    (test-equal "text-properties-at/has-face" 'bold (plist-get props 'face))
    (test-equal "text-properties-at/has-invisible" t (plist-get props 'invisible))))

;; Test 4: add-text-properties multiple
(with-temp-buffer
  (insert "test")
  (add-text-properties 1 5 '(face bold invisible t category special))
  (test-eq "add-text-properties/face" 'bold (get-text-property 2 'face))
  (test-eq "add-text-properties/invisible" t (get-text-property 2 'invisible))
  (test-eq "add-text-properties/category" 'special (get-text-property 2 'category)))

;; Test 5: propertize
(let ((str (propertize "test" 'face 'bold)))
  (test-eq "propertize/creates-wrapper" 'bold (get-text-property 0 'face str))
  (test-equal "propertize/preserves-content" "test" (substring str 0)))

(test-end)
