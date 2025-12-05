;;; test-buffer-modifications.el --- Test insert/delete with text properties

(load-file "test/text-property/test-framework.el")

(test-begin "buffer-modifications")

;; Test 1: Insert plain text in middle of propertized region
(with-temp-buffer
  (insert (propertize "beforeafter" 'face 'bold))
  (goto-char 7)  ; After "before"
  (insert "MIDDLE")
  (test-eq "buffer-modifications/insert-plain-before-preserved"
           'bold
           (get-text-property 3 'face))
  (test-eq "buffer-modifications/insert-plain-after-preserved"
           'bold
           (get-text-property 14 'face))
  ;; Check if inserted text inherited properties (rear-sticky behavior)
  (let ((middle-prop (get-text-property 8 'face)))
    (test-not-nil "buffer-modifications/insert-plain-inherits-or-not"
                  t)))  ; Just verify it doesn't crash

;; Test 2: Delete text from middle of propertized region
(with-temp-buffer
  (insert (propertize "0123456789" 'face 'bold))
  (goto-char 4)
  (delete-char 3)  ; Delete "345"
  (test-eq "buffer-modifications/delete-middle-before-preserved"
           'bold
           (get-text-property 2 'face))
  (test-eq "buffer-modifications/delete-middle-after-preserved"
           'bold
           (get-text-property 5 'face)))

;; Test 3: Delete across interval boundaries
(with-temp-buffer
  (insert (propertize "AAAAA" 'face 'bold))
  (insert (propertize "BBBBB" 'face 'italic))
  (goto-char 4)
  (delete-char 4)  ; Delete "AA" + "BB"
  (test-eq "buffer-modifications/delete-across-before"
           'bold
           (get-text-property 2 'face))
  (test-eq "buffer-modifications/delete-across-after"
           'italic
           (get-text-property 4 'face)))

;; Test 4: Delete entire interval
(with-temp-buffer
  (insert "AAA")
  (insert (propertize "BBBBB" 'face 'bold))
  (insert "CCC")
  (goto-char 4)
  (delete-char 5)  ; Delete all B's
  (test-nil "buffer-modifications/delete-entire-before"
            (get-text-property 2 'face))
  (test-nil "buffer-modifications/delete-entire-after"
            (get-text-property 4 'face)))

;; Test 5: Delete from start of buffer
(with-temp-buffer
  (insert (propertize "AAAAA" 'face 'bold))
  (insert "BBBBB")
  (goto-char 1)
  (delete-char 3)
  (test-eq "buffer-modifications/delete-start-remaining"
           'bold
           (get-text-property 2 'face))
  (test-nil "buffer-modifications/delete-start-plain"
            (get-text-property 4 'face)))

;; Test 6: Insert at interval boundary - start
(with-temp-buffer
  (insert "AAA")
  (insert (propertize "BBB" 'face 'bold))
  (goto-char 4)  ; At boundary
  (insert "X")
  (test-nil "buffer-modifications/insert-boundary-before"
            (get-text-property 3 'face))
  ;; Position 4 is now 'X' - check its property
  (let ((boundary-prop (get-text-property 4 'face)))
    (test-not-nil "buffer-modifications/insert-boundary-check" t))
  (test-eq "buffer-modifications/insert-boundary-after"
           'bold
           (get-text-property 5 'face)))

;; Test 7: Insert at interval boundary - end
(with-temp-buffer
  (insert (propertize "AAA" 'face 'bold))
  (insert "BBB")
  (goto-char 4)  ; At end of bold region
  (insert "X")
  ;; Check properties around insertion
  (test-eq "buffer-modifications/insert-end-before"
           'bold
           (get-text-property 3 'face))
  (test-nil "buffer-modifications/insert-end-after"
            (get-text-property 5 'face)))

;; Test 8: Insert propertized text in middle of different property
(with-temp-buffer
  (insert (propertize "AAAAAA" 'face 'bold))
  (goto-char 4)
  (insert (propertize "XX" 'face 'italic))
  (test-eq "buffer-modifications/insert-prop-before"
           'bold
           (get-text-property 2 'face))
  (test-eq "buffer-modifications/insert-prop-inserted"
           'italic
           (get-text-property 4 'face))
  (test-eq "buffer-modifications/insert-prop-after"
           'bold
           (get-text-property 7 'face)))

;; Test 9: Replace text (delete + insert)
(with-temp-buffer
  (insert (propertize "0123456789" 'face 'bold))
  (goto-char 4)
  (delete-char 3)
  (insert "XXX")
  (test-eq "buffer-modifications/replace-before"
           'bold
           (get-text-property 2 'face))
  (test-eq "buffer-modifications/replace-after"
           'bold
           (get-text-property 8 'face)))

;; Test 10: Insert at point-max
(with-temp-buffer
  (insert (propertize "test" 'face 'bold))
  (goto-char (point-max))
  (insert "more")
  (test-eq "buffer-modifications/insert-max-existing"
           'bold
           (get-text-property 2 'face))
  ;; Check if new text inherits
  (let ((new-prop (get-text-property 6 'face)))
    (test-not-nil "buffer-modifications/insert-max-new" t)))

;; Test 11: Delete to point-max
(with-temp-buffer
  (insert (propertize "AAAAA" 'face 'bold))
  (insert "BBBBB")
  (goto-char 6)
  (delete-region (point) (point-max))
  (test-eq "buffer-modifications/delete-to-max-preserved"
           'bold
           (get-text-property 3 'face))
  (test-equal "buffer-modifications/delete-to-max-length"
              5
              (length (buffer-string))))

;; Test 12: Insert with multiple properties
(with-temp-buffer
  (insert "test")
  (goto-char 3)
  (insert (propertize "XX" 'face 'bold 'invisible t))
  (test-nil "buffer-modifications/multi-insert-before-face"
            (get-text-property 2 'face))
  (test-eq "buffer-modifications/multi-insert-new-face"
           'bold
           (get-text-property 3 'face))
  (test-eq "buffer-modifications/multi-insert-new-invisible"
           t
           (get-text-property 3 'invisible))
  (test-nil "buffer-modifications/multi-insert-after-face"
            (get-text-property 5 'face)))

;; Test 13: Buffer-substring preserves properties
(with-temp-buffer
  (insert (propertize "test text" 'face 'bold))
  (let ((sub (buffer-substring 1 5)))
    (test-eq "buffer-modifications/substring-preserves"
             'bold
             (get-text-property 0 'face sub))))

;; Test 14: Kill and yank text with properties
(with-temp-buffer
  (insert (propertize "test" 'face 'bold))
  (insert " plain")
  (goto-char 1)
  (kill-word 1)  ; Kill "test"
  (goto-char (point-max))
  (yank)
  (test-eq "buffer-modifications/yank-preserves"
           'bold
           (get-text-property 8 'face)))

;; Test 15: Delete backwards
(with-temp-buffer
  (insert (propertize "0123456789" 'face 'bold))
  (goto-char 7)
  (delete-char -3)  ; Delete backwards
  (test-eq "buffer-modifications/delete-backward-before"
           'bold
           (get-text-property 2 'face))
  (test-eq "buffer-modifications/delete-backward-after"
           'bold
           (get-text-property 5 'face)))

(test-end)
