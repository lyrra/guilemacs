;;; test-phase5-operations.el --- Test Phase 5 property operations

(load-file "test/text-property/test-framework.el")

(test-begin "phase5-operations")

;; Test 1: remove-text-properties - selective removal
(with-temp-buffer
  (insert "test text")
  (put-text-property 1 5 'face 'bold)
  (put-text-property 1 5 'invisible t)
  (let ((result (remove-text-properties 1 5 '(invisible))))
    (test-not-nil "remove-text-properties/returns-t-when-removed" result)
    (test-eq "remove-text-properties/face-preserved" 'bold (get-text-property 2 'face))
    (test-nil "remove-text-properties/invisible-removed" (get-text-property 2 'invisible))))

;; Test 2: remove-text-properties - remove all
(with-temp-buffer
  (insert "test text")
  (put-text-property 1 5 'face 'bold)
  (remove-text-properties 1 5 '(face))
  (test-nil "remove-text-properties/all-removed" (get-text-property 2 'face)))

;; Test 3: set-text-properties - complete replacement
(with-temp-buffer
  (insert "test text")
  (put-text-property 1 5 'face 'bold)
  (put-text-property 1 5 'invisible t)
  (set-text-properties 1 5 '(underline t))
  (test-nil "set-text-properties/old-face-removed" (get-text-property 2 'face))
  (test-nil "set-text-properties/old-invisible-removed" (get-text-property 2 'invisible))
  (test-eq "set-text-properties/new-underline-added" t (get-text-property 2 'underline)))

;; Test 4: set-text-properties - partial range
(with-temp-buffer
  (insert "0123456789")
  (put-text-property 1 11 'face 'bold)
  (set-text-properties 3 7 '(underline t))
  (test-eq "set-text-properties/before-range-preserved" 'bold (get-text-property 2 'face))
  (test-nil "set-text-properties/in-range-replaced" (get-text-property 5 'face))
  (test-eq "set-text-properties/in-range-new-prop" t (get-text-property 5 'underline))
  (test-eq "set-text-properties/after-range-preserved" 'bold (get-text-property 8 'face)))

;; Test 5: text-property-any - find matching property
(with-temp-buffer
  (insert "plain ")
  (insert (propertize "bold" 'face 'bold))
  (insert " plain")
  (let ((pos (text-property-any 1 (point-max) 'face 'bold (current-buffer))))
    (test-equal "text-property-any/finds-position" 7 pos)))

;; Test 6: text-property-any - no match
(with-temp-buffer
  (insert "plain text")
  (let ((pos (text-property-any 1 (point-max) 'face 'bold (current-buffer))))
    (test-nil "text-property-any/returns-nil-when-not-found" pos)))

;; Test 7: text-property-not-all - find mismatch
(with-temp-buffer
  (insert (propertize "bold text " 'face 'bold))
  (insert "plain text")
  (let ((pos (text-property-not-all 1 (point-max) 'face 'bold (current-buffer))))
    (test-equal "text-property-not-all/finds-mismatch" 11 pos)))

;; Test 8: text-property-not-all - all match
(with-temp-buffer
  (insert (propertize "all bold" 'face 'bold))
  (let ((pos (text-property-not-all 1 (point-max) 'face 'bold (current-buffer))))
    (test-nil "text-property-not-all/returns-nil-when-all-match" pos)))

;; Test 9: text-property-any - limited range search
(with-temp-buffer
  (insert "plain text ")
  (insert (propertize "bold text" 'face 'bold))
  (insert " more plain")
  ;; Search only first 10 chars (should not find bold at pos 12)
  (let ((pos (text-property-any 1 10 'face 'bold (current-buffer))))
    (test-nil "text-property-any/limited-range-not-found" pos))
  ;; Search starting from bold region
  (let ((pos (text-property-any 12 (point-max) 'face 'bold (current-buffer))))
    (test-equal "text-property-any/limited-range-found" 12 pos)))

;; Test 10: text-property-not-all - limited range search
(with-temp-buffer
  (insert (propertize "bold text " 'face 'bold))
  (insert "plain text")
  ;; Search only bold region (should return nil - all bold)
  (let ((pos (text-property-not-all 1 10 'face 'bold (current-buffer))))
    (test-nil "text-property-not-all/limited-range-all-match" pos))
  ;; Search starting from boundary
  (let ((pos (text-property-not-all 8 (point-max) 'face 'bold (current-buffer))))
    (test-equal "text-property-not-all/limited-range-finds" 11 pos)))

;; Test 11: remove-text-properties - partial range
(with-temp-buffer
  (insert "0123456789")
  (put-text-property 1 11 'face 'bold)
  (put-text-property 1 11 'invisible t)
  ;; Remove invisible from middle portion only
  (remove-text-properties 4 8 '(invisible))
  (test-eq "remove-text-properties/partial-before-unchanged" t (get-text-property 2 'invisible))
  (test-nil "remove-text-properties/partial-middle-removed" (get-text-property 5 'invisible))
  (test-eq "remove-text-properties/partial-after-unchanged" t (get-text-property 9 'invisible))
  (test-eq "remove-text-properties/partial-face-preserved" 'bold (get-text-property 5 'face)))

;; Test 12: set-text-properties - verify complete replacement
(with-temp-buffer
  (insert "test")
  (put-text-property 1 5 'face 'bold)
  (put-text-property 1 5 'invisible t)
  (put-text-property 1 5 'category 'special)
  ;; Replace with completely different properties
  (set-text-properties 1 5 '(underline t mouse-face highlight))
  (test-nil "set-text-properties/replaces-face" (get-text-property 2 'face))
  (test-nil "set-text-properties/replaces-invisible" (get-text-property 2 'invisible))
  (test-nil "set-text-properties/replaces-category" (get-text-property 2 'category))
  (test-eq "set-text-properties/sets-underline" t (get-text-property 2 'underline))
  (test-eq "set-text-properties/sets-mouse-face" 'highlight (get-text-property 2 'mouse-face)))

(test-end)
