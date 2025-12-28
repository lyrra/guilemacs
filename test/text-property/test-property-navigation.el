;;; test-property-navigation.el --- Test next/previous property change functions

(test-begin "property-navigation")

;; Test 1: next-property-change - single interval
(with-temp-buffer
  (insert "aaaaa")
  (insert (propertize "bbbbb" 'face 'bold))
  (insert "ccccc")

  (let ((pos (next-property-change 1 (current-buffer))))
    (test-equal "property-navigation/next-change-finds-start"
                6
                pos))

  (let ((pos (next-property-change 7 (current-buffer))))
    (test-equal "property-navigation/next-change-finds-end"
                11
                pos)))

;; Test 2: next-property-change - no change
(with-temp-buffer
  (insert "plain text")
  (let ((pos (next-property-change 1 (current-buffer))))
    (test-nil "property-navigation/next-change-none"
              pos)))

;; Test 3: next-property-change - at end of buffer
(with-temp-buffer
  (insert (propertize "test" 'face 'bold))
  (let ((pos (next-property-change (point-max) (current-buffer))))
    (test-nil "property-navigation/next-change-at-end"
              pos)))

;; Test 4: previous-property-change - single interval
(with-temp-buffer
  (insert "aaaaa")
  (insert (propertize "bbbbb" 'face 'bold))
  (insert "ccccc")

  (let ((pos (previous-property-change 15 (current-buffer))))
    (test-equal "property-navigation/prev-change-finds-end"
                11
                pos))

  (let ((pos (previous-property-change 10 (current-buffer))))
    (test-equal "property-navigation/prev-change-finds-start"
                6
                pos)))

;; Test 5: previous-property-change - no change
(with-temp-buffer
  (insert "plain text")
  (let ((pos (previous-property-change 10 (current-buffer))))
    (test-nil "property-navigation/prev-change-none"
              pos)))

;; Test 6: previous-property-change - at start
(with-temp-buffer
  (insert (propertize "test" 'face 'bold))
  (let ((pos (previous-property-change 1 (current-buffer))))
    (test-nil "property-navigation/prev-change-at-start"
              pos)))

;; Test 7: next-single-property-change - specific property
(with-temp-buffer
  (insert "aaaaa")
  (insert (propertize "bbbbb" 'face 'bold))
  (insert "ccccc")

  (let ((pos (next-single-property-change 1 'face (current-buffer))))
    (test-equal "property-navigation/next-single-face-start"
                6
                pos))

  (let ((pos (next-single-property-change 7 'face (current-buffer))))
    (test-equal "property-navigation/next-single-face-end"
                11
                pos)))

;; Test 8: next-single-property-change - ignores other properties
(with-temp-buffer
  (insert "aaaaa")
  (insert (propertize "bbbbb" 'invisible t))
  (insert (propertize "ccccc" 'face 'bold))

  ;; Looking for 'face changes, should skip 'invisible
  (let ((pos (next-single-property-change 1 'face (current-buffer))))
    (test-equal "property-navigation/next-single-ignores-other"
                11
                pos)))

;; Test 9: previous-single-property-change - specific property
(with-temp-buffer
  (insert "aaaaa")
  (insert (propertize "bbbbb" 'face 'bold))
  (insert "ccccc")

  (let ((pos (previous-single-property-change 15 'face (current-buffer))))
    (test-equal "property-navigation/prev-single-face-end"
                11
                pos))

  (let ((pos (previous-single-property-change 10 'face (current-buffer))))
    (test-equal "property-navigation/prev-single-face-start"
                6
                pos)))

;; Test 10: Walk through all property changes
(with-temp-buffer
  (insert "plain ")
  (insert (propertize "bold" 'face 'bold))
  (insert " middle ")
  (insert (propertize "italic" 'face 'italic))
  (insert " end")

  (let ((changes '())
        (pos 1))
    (while (setq pos (next-property-change pos (current-buffer)))
      (push pos changes))

    (test-equal "property-navigation/walk-all-count"
                4
                (length changes))
    (test-equal "property-navigation/walk-all-positions"
                '(25 19 11 7)
                changes)))  ; reversed due to push

;; Test 11: Walk backwards through property changes
(with-temp-buffer
  (insert "plain ")
  (insert (propertize "bold" 'face 'bold))
  (insert " middle ")
  (insert (propertize "italic" 'face 'italic))
  (insert " end")

  (let ((changes '())
        (pos (point-max)))
    (while (setq pos (previous-property-change pos (current-buffer)))
      (push pos changes))

    (test-equal "property-navigation/walk-backward-count"
                4
                (length changes))
    (test-equal "property-navigation/walk-backward-positions"
                '(7 11 19 25)
                changes)))

;; Test 12: next-property-change with limit
(with-temp-buffer
  (insert "aaaaa")
  (insert (propertize "bbbbb" 'face 'bold))
  (insert "ccccc")

  ;; Limit search to before the property starts
  (let ((pos (next-property-change 1 (current-buffer) 5)))
    (test-equal "property-navigation/next-change-limit-before"
                5
                pos))

  ;; Limit search to after the property ends
  (let ((pos (next-property-change 7 (current-buffer) 15)))
    (test-equal "property-navigation/next-change-limit-after"
                11
                pos)))

;; Test 13: Multiple properties - next-property-change sees any change
(with-temp-buffer
  (insert "aaaaa")
  (insert (propertize "bbbbb" 'face 'bold 'invisible t))
  (insert "ccccc")
  (put-text-property 11 16 'category 'special)

  (let ((pos 1)
        (changes '()))
    (while (setq pos (next-property-change pos (current-buffer)))
      (push pos changes))

    (test-equal "property-navigation/multiple-props-count"
                3
                (length changes))))

;; Test 14: next-single-property-change - no change for property
(with-temp-buffer
  (insert "plain text")
  (let ((pos (next-single-property-change 1 'face (current-buffer))))
    (test-nil "property-navigation/next-single-no-change"
              pos)))

;; Test 15: Find all regions with specific property value
(with-temp-buffer
  (insert "a")
  (insert (propertize "b" 'type 'special))
  (insert "c")
  (insert (propertize "d" 'type 'special))
  (insert "e")
  (insert (propertize "f" 'type 'special))
  (insert "g")

  (let ((regions '())
        (pos 1))
    (while (setq pos (next-single-property-change pos 'type (current-buffer)))
      ;; Check if we're entering or leaving a 'special region
      (when (eq (get-text-property pos 'type) 'special)
        (let ((end (next-single-property-change pos 'type (current-buffer))))
          (push (cons pos end) regions)))
      (setq pos (1+ pos)))

    (test-equal "property-navigation/find-all-special-count"
                3
                (length regions))))

(test-end)
