;;; test-string-operations.el --- Test text property operations on strings

(test-begin "string-operations")

;; Test 1: remove-text-properties on string - selective removal
(let ((str (propertize "test text" 'face 'bold 'invisible t)))
  (remove-text-properties 0 9 '(invisible) str)
  (test-eq "string-operations/remove-selective-face-preserved"
           'bold
           (get-text-property 0 'face str))
  (test-nil "string-operations/remove-selective-invisible-removed"
            (get-text-property 0 'invisible str)))

;; Test 2: remove-text-properties on string - remove all
(let ((str (propertize "test" 'face 'bold)))
  (remove-text-properties 0 4 '(face) str)
  (test-nil "string-operations/remove-all-properties"
            (get-text-property 0 'face str)))

;; Test 3: set-text-properties on string - replace properties
(let ((str (propertize "test text" 'face 'bold 'invisible t)))
  (set-text-properties 0 4 '(underline t) str)
  (test-nil "string-operations/set-replaces-face"
            (get-text-property 0 'face str))
  (test-nil "string-operations/set-replaces-invisible"
            (get-text-property 0 'invisible str))
  (test-eq "string-operations/set-adds-underline"
           t
           (get-text-property 0 'underline str))
  (test-eq "string-operations/set-partial-range-preserves"
           'bold
           (get-text-property 5 'face str)))

;; Test 4: text-property-any on string
(let ((str (concat "plain " (propertize "bold" 'face 'bold) " plain")))
  (let ((pos (text-property-any 0 (length str) 'face 'bold str)))
    (test-equal "string-operations/text-property-any-finds"
                6
                pos))
  (let ((pos (text-property-any 0 5 'face 'bold str)))
    (test-nil "string-operations/text-property-any-range-not-found"
              pos)))

;; Test 5: text-property-not-all on string
(let ((str (concat (propertize "bold" 'face 'bold) " plain")))
  (let ((pos (text-property-not-all 0 (length str) 'face 'bold str)))
    (test-equal "string-operations/text-property-not-all-finds"
                4
                pos))
  (let ((pos (text-property-not-all 0 4 'face 'bold str)))
    (test-nil "string-operations/text-property-not-all-all-match"
              pos)))

;; Test 6: add-text-properties on string
(let ((str (propertize "test" 'face 'bold)))
  (add-text-properties 0 4 '(underline t) str)
  (test-eq "string-operations/add-preserves-existing"
           'bold
           (get-text-property 0 'face str))
  (test-eq "string-operations/add-adds-new"
           t
           (get-text-property 0 'underline str)))

;; Test 7: put-text-property on emacs-string
(let ((str (propertize "test" 'dummy nil)))  ; Create emacs-string first
  (put-text-property 0 4 'face 'bold str)
  (test-eq "string-operations/put-on-emacs-string"
           'bold
           (get-text-property 0 'face str)))

;; Test 8: text-properties-at on string
(let ((str (propertize "test" 'face 'bold 'invisible t 'category 'special)))
  (let ((props (text-properties-at 0 str)))
    (test-not-nil "string-operations/text-properties-at-returns-list"
                  props)
    (test-eq "string-operations/text-properties-at-has-face"
             'bold
             (plist-get props 'face))
    (test-eq "string-operations/text-properties-at-has-invisible"
             t
             (plist-get props 'invisible))
    (test-eq "string-operations/text-properties-at-has-category"
             'special
             (plist-get props 'category))))

;; Test 9: Propertize with multiple properties
(let ((str (propertize "text" 'face 'bold 'invisible t 'mouse-face 'highlight)))
  (test-eq "string-operations/propertize-multi-face"
           'bold
           (get-text-property 0 'face str))
  (test-eq "string-operations/propertize-multi-invisible"
           t
           (get-text-property 0 'invisible str))
  (test-eq "string-operations/propertize-multi-mouse-face"
           'highlight
           (get-text-property 0 'mouse-face str)))

;; Test 10: String concatenation preserves properties
(let* ((str1 (propertize "bold" 'face 'bold))
       (str2 (propertize "italic" 'face 'italic))
       (result (concat str1 " " str2)))
  (test-eq "string-operations/concat-preserves-first"
           'bold
           (get-text-property 0 'face result))
  (test-nil "string-operations/concat-middle-no-props"
            (get-text-property 4 'face result))
  (test-eq "string-operations/concat-preserves-second"
           'italic
           (get-text-property 5 'face result)))

;; Test 11: Partial range operations on strings
(let ((str (propertize "0123456789" 'face 'bold)))
  (set-text-properties 3 7 '(underline t) str)
  (test-eq "string-operations/partial-before-range"
           'bold
           (get-text-property 2 'face str))
  (test-nil "string-operations/partial-in-range"
            (get-text-property 5 'face str))
  (test-eq "string-operations/partial-in-range-new"
           t
           (get-text-property 5 'underline str))
  (test-eq "string-operations/partial-after-range"
           'bold
           (get-text-property 8 'face str)))

(test-end)
