;;; test-substring-operations.el --- Test substring and copy operations

(load-file "test/text-property/test-framework.el")

(test-begin "substring-operations")

;; Test 1: buffer-substring preserves properties
(with-temp-buffer
  (insert (propertize "AAAAA" 'face 'bold))
  (insert "BBBBB")
  (insert (propertize "CCCCC" 'face 'italic))
  (let ((sub (buffer-substring 1 6)))
    (test-eq "substring-operations/buffer-substring-preserves"
             'bold
             (get-text-property 0 'face sub))))

;; Test 2: buffer-substring across intervals
(with-temp-buffer
  (insert (propertize "AAA" 'face 'bold))
  (insert (propertize "BBB" 'face 'italic))
  (let ((sub (buffer-substring 1 7)))
    (test-eq "substring-operations/across-first"
             'bold
             (get-text-property 0 'face sub))
    (test-eq "substring-operations/across-second"
             'italic
             (get-text-property 4 'face sub))))

;; Test 3: buffer-substring-no-properties strips properties
(with-temp-buffer
  (insert (propertize "test" 'face 'bold))
  (let ((sub (buffer-substring-no-properties 1 5)))
    (test-nil "substring-operations/no-properties-strips"
              (get-text-property 0 'face sub))))

;; Test 4: substring on propertized string
(let* ((str (propertize "0123456789" 'face 'bold))
       (sub (substring str 3 7)))
  (test-eq "substring-operations/string-substring-preserves"
           'bold
           (get-text-property 0 'face sub))
  (test-equal "substring-operations/string-substring-content"
              "3456"
              sub))

;; Test 5: substring across property boundaries in string
(let* ((str (concat (propertize "AAA" 'face 'bold)
                   (propertize "BBB" 'face 'italic)))
       (sub (substring str 1 5)))
  (test-eq "substring-operations/string-across-first"
           'bold
           (get-text-property 0 'face sub))
  (test-eq "substring-operations/string-across-second"
           'italic
           (get-text-property 3 'face sub)))

;; Test 6: substring of substring
(let* ((str (propertize "0123456789" 'face 'bold))
       (sub1 (substring str 2 8))
       (sub2 (substring sub1 1 4)))
  (test-eq "substring-operations/nested-substring-preserves"
           'bold
           (get-text-property 0 'face sub2))
  (test-equal "substring-operations/nested-substring-content"
              "345"
              sub2))

;; Test 7: buffer-substring with multiple properties
(with-temp-buffer
  (insert (propertize "test" 'face 'bold 'invisible t 'category 'special))
  (let ((sub (buffer-substring 1 5)))
    (test-eq "substring-operations/multi-face"
             'bold
             (get-text-property 0 'face sub))
    (test-eq "substring-operations/multi-invisible"
             t
             (get-text-property 0 'invisible sub))
    (test-eq "substring-operations/multi-category"
             'special
             (get-text-property 0 'category sub))))

;; Test 8: substring from start
(let* ((str (propertize "test" 'face 'bold))
       (sub (substring str 0 2)))
  (test-eq "substring-operations/from-start"
           'bold
           (get-text-property 0 'face sub)))

;; Test 9: substring to end
(let* ((str (propertize "test" 'face 'bold))
       (sub (substring str 2)))
  (test-eq "substring-operations/to-end"
           'bold
           (get-text-property 0 'face sub))
  (test-equal "substring-operations/to-end-content"
              "st"
              sub))

;; Test 10: Empty substring
(let* ((str (propertize "test" 'face 'bold))
       (sub (substring str 2 2)))
  (test-equal "substring-operations/empty-length"
              0
              (length sub)))

;; Test 11: Copy whole buffer with properties
(with-temp-buffer
  (insert (propertize "line1\n" 'face 'bold))
  (insert (propertize "line2\n" 'face 'italic))
  (let ((copy (buffer-substring 1 (point-max))))
    (test-eq "substring-operations/whole-buffer-first"
             'bold
             (get-text-property 0 'face copy))
    (test-eq "substring-operations/whole-buffer-second"
             'italic
             (get-text-property 7 'face copy))))

;; Test 12: buffer-string preserves properties
(with-temp-buffer
  (insert (propertize "test" 'face 'bold))
  (let ((str (buffer-string)))
    (test-eq "substring-operations/buffer-string-preserves"
             'bold
             (get-text-property 0 'face str))))

;; Test 13: Modification doesn't affect substring
(with-temp-buffer
  (insert (propertize "test" 'face 'bold))
  (let ((sub (buffer-substring 1 5)))
    (goto-char 1)
    (insert "X")
    (test-eq "substring-operations/independent-after-modify"
             'bold
             (get-text-property 0 'face sub))))

;; Test 14: substring with partial property coverage
(let* ((str (concat "AAA" (propertize "BBB" 'face 'bold) "CCC"))
       (sub (substring str 2 7)))
  (test-nil "substring-operations/partial-before"
            (get-text-property 0 'face sub))
  (test-eq "substring-operations/partial-middle"
           'bold
           (get-text-property 2 'face sub))
  (test-nil "substring-operations/partial-after"
            (get-text-property 4 'face sub)))

(test-end)
