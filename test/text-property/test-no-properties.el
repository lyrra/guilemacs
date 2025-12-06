;;; test-no-properties.el --- Test *-no-properties variants

(load-file "test/text-property/test-framework.el")

(test-begin "no-properties")

;; Test 1: buffer-substring-no-properties strips properties
(with-temp-buffer
  (insert (propertize "test text" 'face 'bold 'invisible t))

  (let ((sub (buffer-substring-no-properties 1 6)))
    (test-equal "no-properties/buffer-substring-no-props-content"
                "test "
                sub)
    (test-nil "no-properties/buffer-substring-no-props-face"
              (get-text-property 0 'face sub))
    (test-nil "no-properties/buffer-substring-no-props-invisible"
              (get-text-property 0 'invisible sub))))

;; Test 2: buffer-substring-no-properties vs buffer-substring
(with-temp-buffer
  (insert (propertize "propertized" 'face 'bold))

  (let ((with-props (buffer-substring 1 12))
        (without-props (buffer-substring-no-properties 1 12)))

    (test-equal "no-properties/compare-content-same"
                "propertized"
                without-props)

    (test-eq "no-properties/with-props-has-face"
             'bold
             (get-text-property 0 'face with-props))

    (test-nil "no-properties/without-props-no-face"
              (get-text-property 0 'face without-props))))

;; Test 3: buffer-substring-no-properties on plain text
(with-temp-buffer
  (insert "plain text")

  (let ((sub (buffer-substring-no-properties 1 11)))
    (test-equal "no-properties/plain-text-content"
                "plain text"
                sub)))

;; Test 4: buffer-substring-no-properties partial range
(with-temp-buffer
  (insert (propertize "0123456789" 'face 'bold))

  (let ((sub (buffer-substring-no-properties 3 7)))
    (test-equal "no-properties/partial-range-content"
                "2345"
                sub)
    (test-nil "no-properties/partial-range-no-props"
              (get-text-property 0 'face sub))))

;; Test 5: buffer-substring-no-properties with multiple properties
(with-temp-buffer
  (insert (propertize "text" 'face 'bold 'invisible t 'category 'special 'mouse-face 'highlight))

  (let ((sub (buffer-substring-no-properties 1 5)))
    (test-equal "no-properties/multi-props-content"
                "text"
                sub)
    (test-nil "no-properties/multi-props-no-face"
              (get-text-property 0 'face sub))
    (test-nil "no-properties/multi-props-no-invisible"
              (get-text-property 0 'invisible sub))
    (test-nil "no-properties/multi-props-no-category"
              (get-text-property 0 'category sub))
    (test-nil "no-properties/multi-props-no-mouse-face"
              (get-text-property 0 'mouse-face sub))))

;; Test 6: buffer-substring-no-properties across interval boundaries
(with-temp-buffer
  (insert (propertize "AAAAA" 'face 'bold))
  (insert (propertize "BBBBB" 'face 'italic))
  (insert "CCCCC")

  (let ((sub (buffer-substring-no-properties 3 13)))
    (test-equal "no-properties/across-boundaries-content"
                "AAABBBBBC"
                sub)
    (test-nil "no-properties/across-boundaries-no-props"
              (get-text-property 0 'face sub))))

;; Test 7: buffer-string-no-properties on entire buffer
(with-temp-buffer
  (insert (propertize "Title" 'face 'bold))
  (insert "\n")
  (insert (propertize "Body" 'face 'italic))

  (let ((str (buffer-string-no-properties)))
    (test-equal "no-properties/buffer-string-content"
                "Title\nBody"
                str)
    (test-nil "no-properties/buffer-string-no-props"
              (get-text-property 0 'face str))))

;; Test 8: buffer-string vs buffer-string-no-properties
(with-temp-buffer
  (insert (propertize "test" 'face 'bold))

  (let ((with-props (buffer-string))
        (without-props (buffer-string-no-properties)))

    (test-equal "no-properties/buffer-string-compare-content"
                "test"
                without-props)

    (test-eq "no-properties/buffer-string-with-has-props"
             'bold
             (get-text-property 0 'face with-props))

    (test-nil "no-properties/buffer-string-without-no-props"
              (get-text-property 0 'face without-props))))

;; Test 9: insert-buffer-substring-no-properties
(with-temp-buffer
  (let ((source-buf (current-buffer)))
    (insert (propertize "source text" 'face 'bold))

    (with-temp-buffer
      (insert "Before ")
      (insert-buffer-substring-no-properties source-buf 1 12)
      (insert " After")

      (test-equal "no-properties/insert-buffer-substring-content"
                  "Before source text After"
                  (buffer-string))

      (test-nil "no-properties/insert-buffer-substring-before-no-props"
                (get-text-property 8 'face))

      (test-nil "no-properties/insert-buffer-substring-inserted-no-props"
                (get-text-property 10 'face)))))

;; Test 10: filter-buffer-substring with delete-flag and no-properties
(with-temp-buffer
  (insert "plain ")
  (insert (propertize "bold" 'face 'bold))
  (insert " text")

  ;; filter-buffer-substring can strip properties
  (let ((filtered (filter-buffer-substring 7 11 nil)))
    ;; By default it preserves properties
    (test-eq "no-properties/filter-preserves-by-default"
             'bold
             (get-text-property 0 'face filtered)))

  ;; buffer-substring-no-properties explicitly strips them
  (let ((no-props (buffer-substring-no-properties 7 11)))
    (test-nil "no-properties/explicit-strip"
              (get-text-property 0 'face no-props))))

;; Test 11: Empty range
(with-temp-buffer
  (insert (propertize "test" 'face 'bold))

  (let ((sub (buffer-substring-no-properties 3 3)))
    (test-equal "no-properties/empty-range-content"
                ""
                sub)))

;; Test 12: Entire propertized buffer
(with-temp-buffer
  (insert (propertize "Everything is bold!" 'face 'bold))

  (let ((sub (buffer-substring-no-properties 1 (point-max))))
    (test-equal "no-properties/entire-buffer-content"
                "Everything is bold!"
                sub)
    (test-nil "no-properties/entire-buffer-no-props"
              (get-text-property 0 'face sub))))

;; Test 13: substring-no-properties on strings
(let* ((str (propertize "test string" 'face 'bold 'invisible t))
       (sub (substring-no-properties str)))

  (test-equal "no-properties/substring-no-props-content"
              "test string"
              sub)
  (test-nil "no-properties/substring-no-props-face"
            (get-text-property 0 'face sub))
  (test-nil "no-properties/substring-no-props-invisible"
            (get-text-property 0 'invisible sub)))

;; Test 14: substring-no-properties with indices
(let* ((str (propertize "0123456789" 'face 'bold))
       (sub (substring-no-properties str 3 7)))

  (test-equal "no-properties/substring-no-props-partial"
              "3456"
              sub)
  (test-nil "no-properties/substring-no-props-partial-face"
            (get-text-property 0 'face sub)))

;; Test 15: substring-no-properties vs substring
(let* ((str (propertize "test" 'face 'bold))
       (with-props (substring str))
       (without-props (substring-no-properties str)))

  (test-equal "no-properties/substring-compare-content"
              "test"
              without-props)

  (test-eq "no-properties/substring-with-has-props"
           'bold
           (get-text-property 0 'face with-props))

  (test-nil "no-properties/substring-without-no-props"
            (get-text-property 0 'face without-props)))

(test-end)
