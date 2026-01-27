;;; test-equal-including-properties.el --- Test equal-including-properties migration

(test-begin "equal-including-properties")

;;; --- equal-including-properties: non-string types ---

;; Non-string objects behave like equal
(test-assert "eip/identical-symbols"
             (equal-including-properties 'foo 'foo))
(test-nil "eip/different-symbols"
          (equal-including-properties 'foo 'bar))
(test-assert "eip/identical-numbers"
             (equal-including-properties 42 42))
(test-nil "eip/different-numbers"
          (equal-including-properties 42 43))
(test-nil "eip/t-vs-nil"
          (equal-including-properties t nil))
(test-assert "eip/nil-nil"
             (equal-including-properties nil nil))
(test-assert "eip/t-t"
             (equal-including-properties t t))
(test-assert "eip/equal-lists"
             (equal-including-properties '(1 2 3) '(1 2 3)))
(test-nil "eip/different-lists"
          (equal-including-properties '(1 2 3) '(1 2 4)))
(test-assert "eip/equal-vectors"
             (equal-including-properties [1 2 3] [1 2 3]))
(test-nil "eip/different-vectors"
          (equal-including-properties [1 2 3] [1 2 4]))

;;; --- equal-including-properties: plain strings ---

;; Plain strings with no properties
(test-assert "eip/plain-strings-equal"
             (equal-including-properties "hello" "hello"))
(test-nil "eip/plain-strings-differ"
          (equal-including-properties "hello" "world"))

;;; --- equal-including-properties: propertized strings ---

;; Same content, same properties
(test-assert "eip/same-props"
             (equal-including-properties
              (propertize "test" 'face 'bold)
              (propertize "test" 'face 'bold)))

;; Same content, different properties
(test-nil "eip/different-props"
          (equal-including-properties
           (propertize "test" 'face 'bold)
           (propertize "test" 'face 'italic)))

;; Same content, one has properties one doesn't
(test-nil "eip/props-vs-no-props"
          (equal-including-properties
           (propertize "test" 'face 'bold)
           "test"))

;; Same content, different property keys
(test-nil "eip/different-prop-keys"
          (equal-including-properties
           (propertize "test" 'face 'bold)
           (propertize "test" 'invisible t)))

;; Multiple properties, same on both
(test-assert "eip/multi-props-same"
             (equal-including-properties
              (propertize "test" 'face 'bold 'invisible t)
              (propertize "test" 'face 'bold 'invisible t)))

;; Multiple properties, one differs
(test-nil "eip/multi-props-one-differs"
          (equal-including-properties
           (propertize "test" 'face 'bold 'invisible t)
           (propertize "test" 'face 'bold 'invisible nil)))

;; Partial property ranges
(let ((a (concat (propertize "ab" 'face 'bold) "cd"))
      (b (concat (propertize "ab" 'face 'bold) "cd")))
  (test-assert "eip/partial-range-same"
               (equal-including-properties a b)))

(let ((a (concat (propertize "ab" 'face 'bold) "cd"))
      (b (concat "ab" (propertize "cd" 'face 'bold))))
  (test-nil "eip/partial-range-different-positions"
            (equal-including-properties a b)))

;;; --- equal vs equal-including-properties contrast ---

;; equal ignores properties, equal-including-properties does not
(let ((plain "test")
      (propped (propertize "test" 'face 'bold)))
  (test-assert "eip/equal-ignores-props"
               (equal plain propped))
  (test-nil "eip/eip-checks-props"
            (equal-including-properties plain propped)))

;;; --- equal-including-properties: lists containing strings ---

(test-assert "eip/list-plain-strings"
             (equal-including-properties
              '("a" "b" "c")
              '("a" "b" "c")))

(let ((a (list (propertize "x" 'face 'bold)))
      (b (list (propertize "x" 'face 'bold))))
  (test-assert "eip/list-with-propped-strings-same"
               (equal-including-properties a b)))

(let ((a (list (propertize "x" 'face 'bold)))
      (b (list (propertize "x" 'face 'italic))))
  (test-nil "eip/list-with-propped-strings-differ"
            (equal-including-properties a b)))

(let ((a (list (propertize "x" 'face 'bold)))
      (b (list "x")))
  (test-nil "eip/list-propped-vs-plain"
            (equal-including-properties a b)))

;;; --- equal-including-properties: vectors containing strings ---

(let ((a (vector (propertize "x" 'face 'bold)))
      (b (vector (propertize "x" 'face 'bold))))
  (test-assert "eip/vector-with-propped-strings-same"
               (equal-including-properties a b)))

(let ((a (vector (propertize "x" 'face 'bold)))
      (b (vector "x")))
  (test-nil "eip/vector-propped-vs-plain"
            (equal-including-properties a b)))

;;; --- text-properties-at on strings ---

(let ((str (propertize "hello" 'face 'bold 'invisible t)))
  (let ((props (text-properties-at 0 str)))
    (test-eq "tpa/string-face" 'bold (plist-get props 'face))
    (test-eq "tpa/string-invisible" t (plist-get props 'invisible))))

(test-nil "tpa/plain-string-no-props"
          (text-properties-at 0 "hello"))

;; Partial property range
(let ((str (concat (propertize "ab" 'face 'bold) "cd")))
  (test-eq "tpa/in-propped-range" 'bold
           (plist-get (text-properties-at 0 str) 'face))
  (test-nil "tpa/outside-propped-range"
            (plist-get (text-properties-at 3 str) 'face)))

;;; --- substring-no-properties ---

(let ((str (propertize "hello world" 'face 'bold)))
  (test-equal "snp/full-string" "hello world"
              (substring-no-properties str))
  (test-equal "snp/substring" "hello"
              (substring-no-properties str 0 5))
  (test-equal "snp/middle" "lo wo"
              (substring-no-properties str 3 8))
  ;; result should have no properties
  (test-nil "snp/result-no-props"
            (text-properties-at 0 (substring-no-properties str 0 5))))

;; Partial property ranges
(let ((str (concat (propertize "ab" 'face 'bold) "cd")))
  (test-equal "snp/strips-partial" "abcd"
              (substring-no-properties str))
  (test-nil "snp/strips-partial-no-props"
            (text-properties-at 0 (substring-no-properties str))))

;; Single character extraction
(let ((str (propertize "abc" 'face 'bold)))
  (test-equal "snp/single-char" "b"
              (substring-no-properties str 1 2))
  (test-nil "snp/single-char-no-props"
            (text-properties-at 0 (substring-no-properties str 1 2))))

(test-end)
