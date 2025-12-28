;;; test-narrow-widen.el --- Test text properties in narrowed buffers

(test-begin "narrow-widen")

;; Test 1: Properties visible in narrowed region
(with-temp-buffer
  (insert "AAAAA")
  (insert (propertize "BBBBB" 'face 'bold))
  (insert "CCCCC")

  (narrow-to-region 6 11)  ; Narrow to the bold region

  (test-eq "narrow-widen/narrowed-property-visible"
           'bold
           (get-text-property 6 'face)))

;; Test 2: Set property in narrowed buffer
(with-temp-buffer
  (insert "0123456789ABCDEF")

  (narrow-to-region 5 11)  ; Narrow to "56789A"

  (put-text-property 5 11 'face 'bold)

  (test-eq "narrow-widen/set-in-narrow-region"
           'bold
           (get-text-property 7 'face))

  (widen)

  ;; Check property persists after widening
  (test-eq "narrow-widen/set-persists-after-widen"
           'bold
           (get-text-property 7 'face))

  ;; Check property only in narrowed region
  (test-nil "narrow-widen/set-only-in-narrow-before"
            (get-text-property 3 'face))
  (test-nil "narrow-widen/set-only-in-narrow-after"
            (get-text-property 13 'face)))

;; Test 3: buffer-substring in narrowed buffer
(with-temp-buffer
  (insert "00000")
  (insert (propertize "11111" 'face 'bold))
  (insert "22222")

  (narrow-to-region 6 11)  ; The bold region

  (let ((sub (buffer-substring 6 11)))
    (test-equal "narrow-widen/substring-in-narrow-content"
                "11111"
                sub)
    (test-eq "narrow-widen/substring-in-narrow-props"
             'bold
             (get-text-property 0 'face sub))))

;; Test 4: get-text-property at boundaries of narrowed region
(with-temp-buffer
  (insert (propertize "0123456789" 'face 'bold))

  (narrow-to-region 3 8)  ; "234567" (indices 3-7 in original)

  (test-eq "narrow-widen/boundary-at-narrow-start"
           'bold
           (get-text-property 3 'face))

  (test-eq "narrow-widen/boundary-before-narrow-end"
           'bold
           (get-text-property 7 'face)))

;; Test 5: Insert with properties in narrowed buffer
(with-temp-buffer
  (insert "AAAAAAAAAA")

  (narrow-to-region 3 8)  ; Narrow to middle

  (goto-char 5)
  (insert (propertize "XX" 'face 'bold))

  (test-eq "narrow-widen/insert-in-narrow-has-props"
           'bold
           (get-text-property 5 'face))

  (widen)

  ;; Check insertion is in correct place after widen
  (test-eq "narrow-widen/insert-persists-after-widen"
           'bold
           (get-text-property 5 'face)))

;; Test 6: Delete text with properties in narrowed buffer
(with-temp-buffer
  (insert "AAA")
  (insert (propertize "BBBBB" 'face 'bold))
  (insert "CCC")

  (narrow-to-region 4 9)  ; Narrow to bold region

  (goto-char 6)
  (delete-char 2)  ; Delete some of the bold text

  (test-eq "narrow-widen/delete-in-narrow-props-remain"
           'bold
           (get-text-property 4 'face))

  (widen)

  (test-eq "narrow-widen/delete-persists-after-widen"
           'bold
           (get-text-property 4 'face)))

;; Test 7: text-property-any in narrowed buffer
(with-temp-buffer
  (insert "plain ")
  (insert (propertize "bold" 'face 'bold))
  (insert " middle ")
  (insert (propertize "italic" 'face 'italic))
  (insert " end")

  (narrow-to-region 7 24)  ; From start of "bold" to end of "italic"

  (let ((pos (text-property-any 7 24 'face 'bold (current-buffer))))
    (test-equal "narrow-widen/text-property-any-in-narrow"
                7
                pos))

  (let ((pos (text-property-any 7 24 'face 'italic (current-buffer))))
    (test-equal "narrow-widen/text-property-any-finds-second"
                19 ; FIX: need to be verified
                pos)))

;; Test 8: next-property-change in narrowed buffer
(with-temp-buffer
  (insert "plain ")
  (insert (propertize "bold" 'face 'bold))
  (insert " end")

  (narrow-to-region 1 11)  ; Narrow to "plain bold"

  (let ((pos (next-property-change 1 (current-buffer))))
    (test-equal "narrow-widen/next-change-in-narrow"
                7
                pos))

  (let ((pos (next-property-change 8 (current-buffer))))
    (test-equal "narrow-widen/next-change-at-narrow-end"
                11
                pos)))

;; Test 9: Widen and check properties outside narrow region
(with-temp-buffer
  (insert (propertize "AAA" 'face 'bold))
  (insert "BBB")
  (insert (propertize "CCC" 'face 'italic))

  (narrow-to-region 4 7)  ; Narrow to "BBB"

  (test-nil "narrow-widen/narrow-to-plain-region"
            (get-text-property 5 'face))

  (widen)

  (test-eq "narrow-widen/widen-shows-before"
           'bold
           (get-text-property 2 'face))

  (test-eq "narrow-widen/widen-shows-after"
           'italic
           (get-text-property 8 'face)))

;; Test 10: Multiple narrow/widen cycles
(with-temp-buffer
  (insert (propertize "0123456789" 'face 'bold))

  ;; First narrow
  (narrow-to-region 3 8)
  (test-eq "narrow-widen/cycle-first-narrow"
           'bold
           (get-text-property 5 'face))

  (widen)

  ;; Second narrow - different region
  (narrow-to-region 6 10)
  (test-eq "narrow-widen/cycle-second-narrow"
           'bold
           (get-text-property 7 'face))

  (widen)

  ;; Properties still intact
  (test-eq "narrow-widen/cycle-final-props-intact"
           'bold
           (get-text-property 5 'face)))

;; Test 11: Add properties across narrow boundary (before narrowing)
(with-temp-buffer
  (insert "0123456789ABCDEF")

  (put-text-property 1 17 'face 'bold)

  (narrow-to-region 5 11)

  ;; Should see bold property in narrowed region
  (test-eq "narrow-widen/props-across-boundary-visible"
           'bold
           (get-text-property 7 'face))

  (widen)

  ;; Should see bold everywhere
  (test-eq "narrow-widen/props-across-boundary-before"
           'bold
           (get-text-property 2 'face))
  (test-eq "narrow-widen/props-across-boundary-after"
           'bold
           (get-text-property 14 'face)))

;; Test 12: remove-text-properties in narrowed buffer
(with-temp-buffer
  (insert (propertize "0123456789" 'face 'bold 'invisible t))

  (narrow-to-region 3 8)

  (remove-text-properties 3 8 '(invisible) (current-buffer))

  (test-eq "narrow-widen/remove-in-narrow-face-preserved"
           'bold
           (get-text-property 5 'face))

  (test-nil "narrow-widen/remove-in-narrow-invisible-removed"
            (get-text-property 5 'invisible))

  (widen)

  ;; Check properties outside narrowed region unchanged
  (test-eq "narrow-widen/remove-outside-narrow-before-face"
           'bold
           (get-text-property 2 'face))
  (test-eq "narrow-widen/remove-outside-narrow-before-invisible"
           t
           (get-text-property 2 'invisible))

  (test-eq "narrow-widen/remove-outside-narrow-after-face"
           'bold
           (get-text-property 9 'face))
  (test-eq "narrow-widen/remove-outside-narrow-after-invisible"
           t
           (get-text-property 9 'invisible)))

;; Test 13: point-min and point-max in narrowed buffer
(with-temp-buffer
  (insert "0123456789")

  (put-text-property 1 11 'face 'bold)

  (narrow-to-region 4 8)

  ;; In narrowed buffer, point-min is 4, point-max is 8
  (test-equal "narrow-widen/point-min-in-narrow"
              4
              (point-min))

  (test-equal "narrow-widen/point-max-in-narrow"
              8
              (point-max))

  (test-eq "narrow-widen/props-at-narrow-min"
           'bold
           (get-text-property (point-min) 'face))

  (test-eq "narrow-widen/props-before-narrow-max"
           'bold
           (get-text-property (1- (point-max)) 'face)))

;; Test 14: buffer-string in narrowed buffer
(with-temp-buffer
  (insert "AAA")
  (insert (propertize "BBB" 'face 'bold))
  (insert "CCC")

  (narrow-to-region 4 7)  ; The bold "BBB"

  (let ((str (buffer-string)))
    (test-equal "narrow-widen/buffer-string-narrow-content"
                "BBB"
                str)
    (test-eq "narrow-widen/buffer-string-narrow-props"
             'bold
             (get-text-property 0 'face str))))

;; Test 15: Nested narrow operations
(with-temp-buffer
  (insert (propertize "0123456789ABCDEF" 'face 'bold))

  (save-restriction
    (narrow-to-region 5 15)  ; "56789ABCDE"

    (test-eq "narrow-widen/nested-outer-narrow"
             'bold
             (get-text-property 7 'face))

    (save-restriction
      (narrow-to-region 7 12)  ; "789AB" within the outer narrow

      (test-eq "narrow-widen/nested-inner-narrow"
               'bold
               (get-text-property 9 'face))

      (test-equal "narrow-widen/nested-inner-point-min"
                  7
                  (point-min)))

    ;; Back to outer narrow
    (test-equal "narrow-widen/nested-back-to-outer"
                5
                (point-min)))

  ;; Fully widened
  (test-equal "narrow-widen/nested-fully-widened"
              1
              (point-min)))

(test-end)
